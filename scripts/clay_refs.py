#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable
from urllib.request import Request, urlopen


@dataclass(frozen=True)
class ClayPdf:
    url: str
    out_path: Path
    sha256: str


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[1]

def _download(url: str, out_path: Path) -> None:
    out_path.parent.mkdir(parents=True, exist_ok=True)
    req = Request(url, headers={"User-Agent": "LeanMillenniumPrizeProblems/refs-fetcher"})
    with urlopen(req, timeout=120) as r, out_path.open("wb") as w:
        w.write(r.read())


def _pdf_specification() -> dict[str, list[ClayPdf]]:
    root = _repo_root()
    return {
        "BirchSwinnertonDyer": [
            ClayPdf(
                url="https://www.claymath.org/wp-content/uploads/2022/05/birchswin.pdf",
                out_path=root / "Problems/BirchSwinnertonDyer/references/clay/birchswin.pdf",
                sha256="c25dc966dd0051a60ac04593aef344d8aa89a51abedccbedadc5dc42099ddc6a",
            )
        ],
        "Hodge": [
            ClayPdf(
                url="https://www.claymath.org/wp-content/uploads/2022/06/hodge.pdf",
                out_path=root / "Problems/Hodge/references/clay/hodge.pdf",
                sha256="e308d945ea3cf5dad8b187a06509013712c467b589039eb41b365cc4c988f0c8",
            )
        ],
        "NavierStokes": [
            ClayPdf(
                url="https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf",
                out_path=root / "Problems/NavierStokes/references/clay/navierstokes.pdf",
                sha256="c1b5f27b1a64705cfaf1afceea513db5deedca8a18ca56ab32e7f86445a06d0c",
            )
        ],
        "PVersusNP": [
            ClayPdf(
                url="https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf",
                out_path=root / "Problems/PVersusNP/references/clay/pvsnp.pdf",
                sha256="018f3d473d16c35e807e8cdfbd0bed3ccf7a56452e3e10c6b1d84b56eaf2cf59",
            )
        ],
        "Poincare": [
            ClayPdf(
                url="https://www.claymath.org/wp-content/uploads/2022/06/poincare.pdf",
                out_path=root / "Problems/Poincare/references/clay/poincare.pdf",
                sha256="909f35c9020280d8b5a2301231bb203613b7e7868f9312fd7824c0a521b6229c",
            ),
        ],
        "RiemannHypothesis": [
            ClayPdf(
                url="https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf",
                out_path=root / "Problems/RiemannHypothesis/references/clay/riemann.pdf",
                sha256="1454b2909f99271726ffb68b056aef45b7d3e6893a66282cad596339d69bafa9",
            )
        ],
        "YangMills": [
            ClayPdf(
                url="https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf",
                out_path=root / "Problems/YangMills/references/clay/yangmills.pdf",
                sha256="3558403ca14c11e382f73a09e548222708540bfdf478cf96aa11c52d43e23e09",
            )
        ],
    }


def _iter_pdfs(problem: str | None) -> Iterable[ClayPdf]:
    pdf_specification = _pdf_specification()
    if problem is None:
        for pdfs in pdf_specification.values():
            yield from pdfs
        return
    if problem not in pdf_specification:
        raise SystemExit(f"Unknown problem '{problem}'. Known: {', '.join(sorted(pdf_specification.keys()))}")
    yield from pdf_specification[problem]


def cmd_list() -> int:
    pdf_specification = _pdf_specification()
    out = {
        k: [{"url": p.url, "out_path": str(p.out_path), "sha256": p.sha256} for p in v]
        for k, v in sorted(pdf_specification.items())
    }
    print(json.dumps(out, indent=2, sort_keys=True))
    return 0


def cmd_download(problem: str | None, force: bool) -> int:
    for pdf in _iter_pdfs(problem):
        pdf_path = pdf.out_path
        if pdf_path.exists() and not force:
            continue
        _download(pdf.url, pdf_path)
    return 0


def cmd_verify(problem: str | None) -> int:
    ok = True
    for pdf in _iter_pdfs(problem):
        pdf_path = pdf.out_path
        if not pdf_path.exists():
            print(f"missing: {pdf_path}")
            ok = False
            continue
        data = pdf_path.read_bytes()
        if not data.startswith(b"%PDF-"):
            print(f"invalid PDF header: {pdf_path}")
            ok = False
        actual = hashlib.sha256(data).hexdigest()
        if actual != pdf.sha256:
            print(f"checksum mismatch: {pdf_path}\n  expected: {pdf.sha256}\n  actual:   {actual}")
            ok = False
    return 0 if ok else 1


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Download/verify Clay Mathematics Institute Millennium Problem PDFs into "
            "`Problems/**/references/clay/`."
        )
    )
    parser.add_argument("--problem", default=None, help="One of: BirchSwinnertonDyer, Hodge, NavierStokes, PVersusNP, Poincare, RiemannHypothesis, YangMills")
    sub = parser.add_subparsers(dest="cmd", required=True)
    sub.add_parser("list", help="Print the PDF URL → local path mapping as JSON.")
    p_dl = sub.add_parser("download", help="Download PDFs into the repo.")
    p_dl.add_argument("--problem", default=argparse.SUPPRESS)
    p_dl.add_argument("--force", action="store_true", help="Redownload even if the PDF exists.")
    p_verify = sub.add_parser("verify", help="Check PDF headers and pinned SHA-256 checksums.")
    p_verify.add_argument("--problem", default=argparse.SUPPRESS)

    args = parser.parse_args()
    if args.cmd == "list":
        return cmd_list()
    if args.cmd == "download":
        return cmd_download(args.problem, args.force)
    if args.cmd == "verify":
        return cmd_verify(args.problem)
    raise SystemExit(f"Unknown command: {args.cmd}")


if __name__ == "__main__":
    raise SystemExit(main())
