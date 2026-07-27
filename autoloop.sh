#!/usr/bin/env bash
# autoloop.sh — autonomous spec-implementation loop.
#
# Each iteration:
#   1. A codex (Sol) worker reads the spec + previous iteration's feedback and
#      makes progress, writing a summary to <outdir>/progress-<i>.md.
#   2. A claude (Fable) judge inspects the summary and the repo state and writes
#      feedback to <outdir>/feedback-<i>.md, which the next worker reads.
#
# Both agents run under nono (codex-lighthouse / claude-lighthouse profiles),
# so their internal sandboxes/approvals are disabled — nono is the sandbox.
#
# Usage: ./autoloop.sh <spec.md> <iterations> [outdir]
#   CODEX_MODEL  (default: gpt-5.6-sol)
#   CLAUDE_MODEL (default: claude-fable-5)

set -uo pipefail

usage() {
    echo "usage: $0 <spec.md> <iterations> [outdir]" >&2
    exit 1
}

SPEC="${1:-}"
ITERS="${2:-}"
OUTDIR="${3:-autoloop}"

[[ -f "$SPEC" ]] || usage
[[ "$ITERS" =~ ^[1-9][0-9]*$ ]] || usage

CODEX_MODEL="${CODEX_MODEL:-gpt-5.6-sol}"
CLAUDE_MODEL="${CLAUDE_MODEL:-claude-fable-5}"

mkdir -p "$OUTDIR"
SPEC_ABS="$(realpath "$SPEC")"
OUTDIR_ABS="$(realpath "$OUTDIR")"

for ((i = 1; i <= ITERS; i++)); do
    progress="$OUTDIR_ABS/progress-$i.md"
    feedback="$OUTDIR_ABS/feedback-$i.md"
    prev_feedback="$OUTDIR_ABS/feedback-$((i - 1)).md"

    echo "=== iteration $i/$ITERS: worker (codex $CODEX_MODEL) ==="

    worker_prompt="You are iteration $i of an autonomous loop implementing a spec.

The spec is at: $SPEC_ABS
"
    if [[ -f "$prev_feedback" ]]; then
        worker_prompt+="A reviewer left feedback on the previous iteration at: $prev_feedback
Read the spec and the feedback first, and address the feedback.
"
    else
        worker_prompt+="This is the first iteration; there is no feedback yet. Read the spec first.
"
    fi
    worker_prompt+="
Make as much concrete, verified progress toward the spec's goal as you can in this session.

Before exiting, write a markdown summary to $progress covering:
what you did, the current state of the work, what remains, and anything the
next iteration should know. Writing this file is mandatory."

    if ! nono run -s --allow-cwd --profile codex-lighthouse -- \
        codex exec -m "$CODEX_MODEL" --dangerously-bypass-approvals-and-sandbox \
        "$worker_prompt" 2>&1 | tee "$OUTDIR_ABS/worker-$i.log"; then
        echo "warning: worker exited non-zero (see worker-$i.log)" >&2
    fi

    if [[ ! -f "$progress" ]]; then
        {
            echo "# Iteration $i summary (auto-generated)"
            echo
            echo "The worker did not write its summary file. Tail of its transcript:"
            echo
            echo '```'
            tail -n 60 "$OUTDIR_ABS/worker-$i.log"
            echo '```'
        } >"$progress"
    fi

    echo "=== iteration $i/$ITERS: judge (claude $CLAUDE_MODEL) ==="

    judge_prompt="You are reviewing iteration $i of an autonomous loop in which a codex worker
is implementing a spec.

The spec is at: $SPEC_ABS
The worker's summary of this iteration is at: $progress

Read both, then inspect the actual state of the codebase (git status, git diff,
git log, read the relevant files, run builds/tests where cheap) and judge
whether the worker did the right thing — do not take the summary at its word.

Write your feedback to $feedback. It is addressed to the next iteration's
worker, so make it concrete and actionable: what was done correctly, what is
wrong or off-track and must be fixed or reverted, and what to do next.

The very first line of the feedback file must be exactly 'STATUS: complete' if
the spec is fully and correctly implemented, or 'STATUS: continue' otherwise.
Writing this file is mandatory."

    if ! nono run -s --allow-cwd --profile claude-lighthouse -- \
        claude -p --model "$CLAUDE_MODEL" --dangerously-skip-permissions \
        "$judge_prompt" 2>&1 | tee "$OUTDIR_ABS/judge-$i.log"; then
        echo "warning: judge exited non-zero (see judge-$i.log)" >&2
    fi

    if [[ ! -f "$feedback" ]]; then
        {
            echo "STATUS: continue"
            echo
            echo "# Iteration $i feedback (auto-generated)"
            echo
            echo "The judge did not write its feedback file. Tail of its transcript:"
            echo
            echo '```'
            tail -n 60 "$OUTDIR_ABS/judge-$i.log"
            echo '```'
        } >"$feedback"
    fi

    if [[ "$(head -n 1 "$feedback")" == "STATUS: complete" ]]; then
        echo "=== judge declared the spec complete after iteration $i — stopping ==="
        exit 0
    fi
done

echo "=== reached iteration limit ($ITERS) without completion ==="
