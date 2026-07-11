# Reference Material Scripts

This repo commits the official Clay Mathematics Institute PDFs under `Problems/**/references/clay/`.

Use this script to (re)download PDFs or verify their PDF headers and pinned SHA-256 checksums:

- `python scripts/clay_refs.py download`
- `python scripts/clay_refs.py verify`

To see the URL → local path mapping:

- `python scripts/clay_refs.py list`

Problem-specific commands accept either placement of `--problem`:

- `python scripts/clay_refs.py verify --problem Hodge`
- `python scripts/clay_refs.py --problem Hodge verify`
