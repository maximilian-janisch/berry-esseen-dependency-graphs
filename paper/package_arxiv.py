"""Build the arXiv upload from the paper sources and the standalone Lean project."""

from pathlib import Path
from tempfile import TemporaryDirectory
from zipfile import ZIP_DEFLATED, ZipFile, ZipInfo


def main() -> None:
    paper = Path(__file__).resolve().parent
    project = paper.parent
    files = {
        "janisch-lehericy-proof.tex": paper / "janisch-lehericy-proof.tex",
        "introduction.tex": paper / "introduction.tex",
        "anc/lean/README.md": project / "VERIFY.md",
    }
    for name in (
        "JanischLehericy.lean",
        "Audit.lean",
        "Replay.lean",
        "lean-toolchain",
        "lakefile.toml",
        "lake-manifest.json",
    ):
        files[f"anc/lean/{name}"] = project / name
    for module in (project / "JanischLehericy").rglob("*.lean"):
        relative = module.relative_to(project).as_posix()
        files[f"anc/lean/{relative}"] = module

    with TemporaryDirectory(dir=paper) as staging:
        archive = Path(staging) / "arxiv-submission.zip"
        with ZipFile(archive, "w") as bundle:
            for name, source in sorted(files.items()):
                # Fixed ZIP metadata keeps consecutive builds byte-identical.
                entry = ZipInfo(name)
                entry.create_system = 3
                entry.external_attr = 0o100644 << 16
                bundle.writestr(entry, source.read_bytes(), compress_type=ZIP_DEFLATED)
        archive.replace(paper / archive.name)


if __name__ == "__main__":
    main()
