# Proof sessions

The proof work behind this collection, taken from the agent sessions that did
it. Each `.jsonl` file is one session: the gnatprove runs and the source edits
between them, in order. Together they show the proofs that failed and the
changes that fixed them, which the finished units in `src/` do not.

The files are numbered in the order the sessions started, from 27 August to
30 September 2026. There are 29 sessions, with 419 gnatprove runs, 415 edits and 948 unproved-check
messages.

## Format

Each line is one event:

| `kind`       | Fields               | Meaning                                              |
|--------------|----------------------|------------------------------------------------------|
| `prove`      | `cmd`, `output`      | A gnatprove run and the diagnostic lines of its output |
| `edit`       | `file`, `old`, `new` | A string replacement in a source file                |
| `write`      | `file`, `content`    | A whole source file written                          |
| `shell_edit` | `cmd`                | A shell, `sed` or Python command that edits sources  |
| `patch`      | `patch`              | An `apply_patch` body, limited to repository sources |

Paths are relative to the repository root. `<toolchain>` stands for the
installation directory of the tools and `<scratch>` for a temporary directory.

## Limitations

- Only the proof runs and the edits are kept. The conversation and the
  reasoning behind each change are not. The matching sections of
  [PROOF.md](../PROOF.md) explain the fixes.
- `shell_edit` events are commands, not diffs, and a session may start from a
  state between two commits. The sessions show what was tried, but they cannot
  be replayed on a checkout without some work.
- A few units have little or no trace here. Examples are the skew heap and the
  early work on the binary heap.
- When a long proof run was polled for output, that output is attached to the
  last `prove` event of the session.
