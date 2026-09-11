#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
autoloop="$repo_root/autoloop.sh"
test_root="$(mktemp -d)"
fake_bin="$test_root/bin"

cleanup() {
    rm -rf -- "$test_root"
}
trap cleanup EXIT

mkdir -p "$fake_bin"

cat >"$fake_bin/nono" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail

if [[ "${FAKE_NONO_FAIL:-0}" == "1" ]]; then
    echo "fake nono failure" >&2
    exit 23
fi

while (($# > 0)); do
    if [[ "$1" == "--" ]]; then
        shift
        exec "$@"
    fi
    shift
done

echo "fake nono did not receive a command" >&2
exit 64
EOF

cat >"$fake_bin/codex" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail

sleep "${FAKE_WORKER_SLEEP:-0}"
prompt="${!#}"
progress="${prompt#*write a markdown summary to }"
if [[ "$progress" == "$prompt" ]]; then
    echo "could not find progress path in worker prompt" >&2
    exit 65
fi
progress="${progress%% covering:*}"
printf '# Fake worker progress\n' >"$progress"
echo "fake worker complete"
EOF

cat >"$fake_bin/claude" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail

prompt="${!#}"
feedback="${prompt#*Write your feedback to }"
if [[ "$feedback" == "$prompt" ]]; then
    echo "could not find feedback path in judge prompt" >&2
    exit 65
fi
feedback="${feedback%%. It is addressed*}"
printf 'STATUS: %s\n\n# Fake judge feedback\n' \
    "${FAKE_JUDGE_STATUS:-complete}" >"$feedback"
echo "fake judge complete"
EOF

chmod +x "$fake_bin/nono" "$fake_bin/codex" "$fake_bin/claude"

make_case() {
    local name="$1"
    local case_dir="$test_root/$name"

    mkdir -p "$case_dir/output"
    printf 'Do the test task\n' >"$case_dir/spec.md"
    printf '%s\n' "$case_dir"
}

success_dir="$(make_case success)"
(
    cd "$success_dir"
    PATH="$fake_bin:$PATH" "$autoloop" spec.md 1 output \
        >stdout.log 2>stderr.log
)
[[ "$(head -n 1 "$success_dir/output/feedback-1.md")" == "STATUS: complete" ]]

failure_dir="$(make_case stale-failure)"
printf 'STATUS: complete\n\nThis verdict is stale.\n' \
    >"$failure_dir/output/feedback-1.md"
set +e
(
    cd "$failure_dir"
    PATH="$fake_bin:$PATH" FAKE_NONO_FAIL=1 \
        "$autoloop" spec.md 1 output >stdout.log 2>stderr.log
)
failure_status=$?
set -e
[[ "$failure_status" == "1" ]]
[[ "$(head -n 1 "$failure_dir/output/feedback-1.md")" == "STATUS: continue" ]]
grep -q 'with agent errors' "$failure_dir/stderr.log"

timeout_dir="$(make_case timeout)"
set +e
(
    cd "$timeout_dir"
    PATH="$fake_bin:$PATH" FAKE_WORKER_SLEEP=5 FAKE_JUDGE_STATUS=continue \
        WORKER_TIMEOUT_SECS=1 "$autoloop" spec.md 1 output \
        >stdout.log 2>stderr.log
)
timeout_status=$?
set -e
[[ "$timeout_status" == "1" ]]
grep -q 'worker timed out after 1s' "$timeout_dir/stderr.log"

echo "autoloop tests passed"
