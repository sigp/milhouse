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
#   CODEX_MODEL          (default: gpt-5.6-sol)
#   CLAUDE_MODEL         (default: claude-fable-5)
#   WORKER_TIMEOUT_SECS  (default: 1800)
#   JUDGE_TIMEOUT_SECS   (default: 900)

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
WORKER_TIMEOUT_SECS="${WORKER_TIMEOUT_SECS:-1800}"
JUDGE_TIMEOUT_SECS="${JUDGE_TIMEOUT_SECS:-900}"

if [[ ! "$WORKER_TIMEOUT_SECS" =~ ^[1-9][0-9]*$ ]]; then
    echo "error: WORKER_TIMEOUT_SECS must be a positive integer" >&2
    exit 1
fi
if [[ ! "$JUDGE_TIMEOUT_SECS" =~ ^[1-9][0-9]*$ ]]; then
    echo "error: JUDGE_TIMEOUT_SECS must be a positive integer" >&2
    exit 1
fi
if ! command -v timeout >/dev/null 2>&1; then
    echo "error: GNU timeout is required" >&2
    exit 1
fi

if [[ -n "${NONO_CAP_FILE:-}" ]]; then
    echo "warning: autoloop is already running inside a nono sandbox." >&2
    echo "warning: nested profiles cannot grant access denied by the outer sandbox." >&2
fi

if ! mkdir -p "$OUTDIR"; then
    echo "error: could not create output directory: $OUTDIR" >&2
    exit 1
fi
SPEC_ABS="$(realpath "$SPEC")" || exit 1
OUTDIR_ABS="$(realpath "$OUTDIR")" || exit 1
run_failed=0

for ((i = 1; i <= ITERS; i++)); do
    progress="$OUTDIR_ABS/progress-$i.md"
    feedback="$OUTDIR_ABS/feedback-$i.md"
    prev_feedback="$OUTDIR_ABS/feedback-$((i - 1)).md"
    worker_log="$OUTDIR_ABS/worker-$i.log"
    judge_log="$OUTDIR_ABS/judge-$i.log"

    # The output directory is reusable. Never let a failed agent leave a prior
    # run's summary or verdict looking current.
    if ! rm -f -- "$progress" "$feedback" "$worker_log" "$judge_log"; then
        echo "error: could not clear generated artifacts for iteration $i" >&2
        exit 1
    fi

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

    timeout --kill-after=10s "${WORKER_TIMEOUT_SECS}s" \
        nono run -s --allow-cwd --profile codex-lighthouse -- \
        codex exec -m "$CODEX_MODEL" --dangerously-bypass-approvals-and-sandbox \
        "$worker_prompt" 2>&1 | tee "$worker_log"
    worker_pipe_status=("${PIPESTATUS[@]}")
    worker_status=${worker_pipe_status[0]}
    worker_tee_status=${worker_pipe_status[1]}
    if ((worker_status != 0 || worker_tee_status != 0)); then
        run_failed=1
        if ((worker_status == 124 || worker_status == 137)); then
            echo "warning: worker timed out after ${WORKER_TIMEOUT_SECS}s (see worker-$i.log)" >&2
        else
            echo "warning: worker exited with status $worker_status (see worker-$i.log)" >&2
        fi
        if ((worker_tee_status != 0)); then
            echo "warning: tee exited with status $worker_tee_status while recording worker-$i.log" >&2
        fi
    fi

    if [[ ! -f "$progress" ]]; then
        {
            echo "# Iteration $i summary (auto-generated)"
            echo
            echo "The worker did not write its summary file. Tail of its transcript:"
            echo
            echo '```'
            tail -n 60 "$worker_log"
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

    timeout --kill-after=10s "${JUDGE_TIMEOUT_SECS}s" \
        nono run -s --allow-cwd --profile claude-lighthouse -- \
        claude -p --model "$CLAUDE_MODEL" --dangerously-skip-permissions \
        "$judge_prompt" 2>&1 | tee "$judge_log"
    judge_pipe_status=("${PIPESTATUS[@]}")
    judge_status=${judge_pipe_status[0]}
    judge_tee_status=${judge_pipe_status[1]}
    if ((judge_status != 0 || judge_tee_status != 0)); then
        run_failed=1
        if ((judge_status == 124 || judge_status == 137)); then
            echo "warning: judge timed out after ${JUDGE_TIMEOUT_SECS}s (see judge-$i.log)" >&2
        else
            echo "warning: judge exited with status $judge_status (see judge-$i.log)" >&2
        fi
        if ((judge_tee_status != 0)); then
            echo "warning: tee exited with status $judge_tee_status while recording judge-$i.log" >&2
        fi
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
            tail -n 60 "$judge_log"
            echo '```'
        } >"$feedback"
    fi

    feedback_status="$(head -n 1 "$feedback")"
    case "$feedback_status" in
    "STATUS: complete")
        if ((judge_status == 0 && judge_tee_status == 0)); then
            echo "=== judge declared the spec complete after iteration $i — stopping ==="
            exit 0
        fi
        echo "warning: ignoring completion verdict from failed judge" >&2
        ;;
    "STATUS: continue")
        ;;
    *)
        run_failed=1
        echo "warning: invalid feedback status: $feedback_status" >&2
        ;;
    esac
done

if ((run_failed != 0)); then
    echo "=== reached iteration limit ($ITERS) with agent errors ===" >&2
    exit 1
fi

echo "=== reached iteration limit ($ITERS) without completion ==="
