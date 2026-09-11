"""Diagnostic extraction probes, not a proof-validation gate. Run through lake env."""

import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[3]
REPORTS = ROOT / 'aeneas-lean/.lake/compiler-workaround-probes'
OUT = None
SOURCE = Path(__file__).with_name('source.rs')
COMPILER = ROOT / 'aeneas-lean/.lake/aeneas'
ENV = os.environ.copy()
ENV.update(CARGO_TARGET_DIR=str(ROOT / 'aeneas-lean/.lake/sept7-cargo-target'),
           CARGO_PROFILE_DEV_DEBUG='0', CARGO_PROFILE_TEST_DEBUG='0', CARGO_INCREMENTAL='0')
RESULTS = []
VERSIONS = {}

def run(directory, label, cmd, cwd=None, env=ENV):
    with (directory / (label + '.log')).open('w') as log:
        result = subprocess.run([str(x) for x in cmd], cwd=cwd or directory, env=env,
                                stdout=log, stderr=subprocess.STDOUT, timeout=600)
    text = (directory / (label + '.log')).read_text()
    if "falling back to rustc's default sysroot" in text:
        raise RuntimeError('full MIR sysroot unavailable')
    return result.returncode

def probe(name, charon_args, filtered=False):
    directory = OUT / name
    directory.mkdir(exist_ok=True)
    llbc = directory / 'probe.llbc'
    kind, flags, rust = charon_args
    cmd = [COMPILER / 'charon', kind, '--preset=aeneas', *flags, '--dest-file', llbc, '--', *rust]
    result = {'case': name, 'charon': run(directory, 'charon', cmd)}
    if 'Type error after transformations' in (directory / 'charon.log').read_text():
        result['charonTypeError'] = True
    if result['charon'] == 0:
        result['llbcHasErrors'] = json.loads(llbc.read_text()).get('has_errors')
        cmd = [COMPILER / 'aeneas', '-backend', 'lean', '-namespace', 'Probe', '-split-files',
               '-no-progress-bar', '-print-error-emitters', '-print-error-diagnostics',
               '-dest', directory / 'Probe', *(['-filter-trait-methods'] if filtered else []), llbc]
        result['aeneas'] = run(directory, 'aeneas', cmd)
        if result['aeneas'] == 0:
            files = sorted((directory / 'Probe').glob('*.lean'))
            result['templates'] = [p.name for p in files if 'Template' in p.name]
            if not result['templates']:
                env = ENV.copy()
                env['LEAN_PATH'] = str(directory) + os.pathsep + ENV.get('LEAN_PATH', '')
                result['lean'] = {}
                for part in ['Types', 'Funs']:
                    result['lean'][part] = run(directory, 'lean-' + part,
                        ['lean', '-o', 'Probe/' + part + '.olean', 'Probe/' + part + '.lean'], env=env)
                    if result['lean'][part]:
                        break
    RESULTS.append(result)
    (REPORTS / 'report.json').write_text(json.dumps({
        'diagnosticOnly': True, 'output': str(OUT),
        'toolchainPin': json.loads((ROOT / 'aeneas-toolchain.json').read_text()),
        'versions': VERSIONS,
        'sourceHashes': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in [SOURCE, Path(__file__),
                ROOT / 'aeneas-lean/reproducers/option_models/source.rs',
                ROOT / 'aeneas-lean/reproducers/cow_regions/src/lib.rs',
                ROOT / 'aeneas-lean/reproducers/cow_regions/Cargo.lock',
                ROOT / 'aeneas-lean/reproducers/vec_map_models/source.rs',
                ROOT / 'aeneas-lean/reproducers/vec_map_models/Cargo.lock']},
        'results': RESULTS,
    }, indent=2) + '\n')
    print(json.dumps(result), flush=True)

def main():
    global OUT
    REPORTS.mkdir(parents=True, exist_ok=True)
    (REPORTS / 'report.json').unlink(missing_ok=True)
    OUT = Path(tempfile.mkdtemp(prefix='run-', dir=REPORTS))
    pin = json.loads((ROOT / 'aeneas-toolchain.json').read_text())
    for name, command, expected in [
        ('aeneas-version', [COMPILER / 'aeneas', '-version'], pin['aeneasVersion']),
        ('charon-version', [COMPILER / 'charon', 'version'], pin['charonVersion']),
        ('rustc-version', ['rustc', '+' + pin['rustToolchain'], '--version', '--verbose'], pin['rustcCommit']),
        ('lean-version', ['lean', '--version'], pin['leanToolchain'].split(':v')[1]),
    ]:
        if run(OUT, name, command):
            raise RuntimeError('Could not check ' + name)
        VERSIONS[name] = (OUT / (name + '.log')).read_text().strip()
        if expected not in VERSIONS[name]:
            raise RuntimeError('Unexpected ' + name + ': ' + VERSIONS[name])
    source_args = ['--edition=2024', '--crate-type', 'lib', '--crate-name', 'simplification_probe', SOURCE]
    for root in ['record_insert', 'take', 'borrowed_try', 'fallback', 'use_cloned', 'into_iter', 'fnmut']:
        qualified = 'simplification_probe::_::record_insert' if root == 'record_insert' else 'simplification_probe::' + root
        flags = ['--start-from', qualified]
        if root == 'use_cloned':
            flags += ['--start-from', '{impl core::iter::traits::iterator::Iterator for simplification_probe::Counter}']
        probe(root, ('rustc', flags, source_args))
    probe('cloned-source', ('rustc', ['--include', 'core::option', '--start-from', 'option_source::cloned'],
          ['--edition=2024', '--crate-type', 'lib', '--crate-name', 'option_source',
           ROOT / 'aeneas-lean/reproducers/option_models/source.rs']))
    probe('cow-readers', ('cargo', ['--start-from', 'milhouse_cow_regions_probe'],
          ['--locked', '--offline', '--manifest-path', ROOT / 'aeneas-lean/reproducers/cow_regions/Cargo.toml']))
    vec = ('cargo', ['--include', 'vec_map', '--include', 'core::iter::traits::iterator::Iterator::map',
            '--include', 'core::iter::adapters::map', '--include', 'alloc::vec::_::extend',
            '--start-from', 'vec_map_source::insert'],
           ['--locked', '--offline', '--manifest-path', ROOT / 'aeneas-lean/reproducers/vec_map_models/Cargo.toml'])
    probe('vecmap-insert', vec)
    probe('vecmap-insert-filtered', vec, True)

if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        print(f'{type(error).__name__}: {error}', file=sys.stderr)
        sys.exit(1)
