#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable
from urllib.request import Request, urlopen


@dataclass(frozen=True)
class ClayPdf:
    url: str
    out_path: Path


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[1]

def _download(url: str, out_path: Path) -> None:
    out_path.parent.mkdir(parents=True, exist_ok=True)
    req = Request(url, headers={"User-Agent": "LeanMillenniumPrizeProblems/refs-fetcher"})
    with urlopen(req, timeout=120) as r, out_path.open("wb") as w:
        w.write(r.read())


def _spec() -> dict[str, list[ClayPdf]]:
    root = _repo_root()
    return {
        "BirchSwinnertonDyer": [
            ClayPdf(
                url="https://www.claymath.org/wp-content/uploads/2022/05/birchswin.pdf",
                out_path=root / "Problems/BirchSwinnertonDyer/references/clay/birchswin.pdf",
            )
        ],
        "Hodge": [
            ClayPdf(
                url="https://www.claymath.org/wp-content/uploads/2022/06/hodge.pdf",
                out_path=root / "Problems/Hodge/references/clay/hodge.pdf",
            )
        ],
        "NavierStokes": [
            ClayPdf(
                url="https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf",
                out_path=root / "Problems/NavierStokes/references/clay/navierstokes.pdf",
            )
        ],
        "PvsNP": [
            ClayPdf(
                url="https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf",
                out_path=root / "Problems/PvsNP/references/clay/pvsnp.pdf",
            )
        ],
        "Poincare": [
            ClayPdf(
                url="https://www.claymath.org/wp-content/uploads/2022/06/poincare.pdf",
                out_path=root / "Problems/Poincare/references/clay/poincare.pdf",
            ),
            ClayPdf(
                url="https://www.claymath.org/wp-content/uploads/2022/03/cmip19.pdf",
                out_path=root / "Problems/Poincare/references/clay/cmip19.pdf",
            ),
            ClayPdf(
                url="https://www.claymath.org/wp-content/uploads/2022/03/Ricci-pdf.pdf",
                out_path=root / "Problems/Poincare/references/clay/Ricci-pdf.pdf",
            ),
            ClayPdf(
                url="https://www.claymath.org/wp-content/uploads/2022/06/Poincare-press-release.pdf",
                out_path=root / "Problems/Poincare/references/clay/Poincare-press-release.pdf",
            ),
        ],
        "RiemannHypothesis": [
            ClayPdf(
                url="https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf",
                out_path=root / "Problems/RiemannHypothesis/references/clay/riemann.pdf",
            )
        ],
        "YangMills": [
            ClayPdf(
                url="https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf",
                out_path=root / "Problems/YangMills/references/clay/yangmills.pdf",
            )
        ],
    }


def _iter_pdfs(problem: str | None) -> Iterable[ClayPdf]:
    spec = _spec()
    if problem is None:
        for pdfs in spec.values():
            yield from pdfs
        return
    if problem not in spec:
        raise SystemExit(f"Unknown problem '{problem}'. Known: {', '.join(sorted(spec.keys()))}")
    yield from spec[problem]


def cmd_list() -> int:
    spec = _spec()
    out = {
        k: [{"url": p.url, "out_path": str(p.out_path)} for p in v] for k, v in sorted(spec.items())
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
    return 0 if ok else 1


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Download/verify Clay Mathematics Institute Millennium Problem PDFs into "
            "`Problems/**/references/clay/`."
        )
    )
    parser.add_argument("--problem", default=None, help="One of: BirchSwinnertonDyer, Hodge, NavierStokes, PvsNP, Poincare, RiemannHypothesis, YangMills")
    sub = parser.add_subparsers(dest="cmd", required=True)
    sub.add_parser("list", help="Print the PDF URL → local path mapping as JSON.")
    p_dl = sub.add_parser("download", help="Download PDFs into the repo.")
    p_dl.add_argument("--force", action="store_true", help="Redownload even if the PDF exists.")
    sub.add_parser("verify", help="Check that the expected PDFs exist locally.")

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
