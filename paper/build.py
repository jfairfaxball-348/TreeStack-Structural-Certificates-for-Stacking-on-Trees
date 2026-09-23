#!/usr/bin/env python3
"""Compile the canonical article and verify its self-contained arXiv bundle."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile


PAPER = Path(__file__).resolve().parent
BUILD = PAPER / ".build"
PALOMAR = "PALOMAR_VERIFICATION_URL_PLACEHOLDER"
FIELDS = (
    "Title", "Authors", "Abstract", "Comments", "Primary category", "Cross-list",
    "MSC-class", "Report-no", "Journal-ref", "DOI", "Palomar verification", "Repository",
)


class PreflightError(Exception):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise PreflightError(message)


def command(args: list[str], cwd: Path) -> str:
    env = os.environ.copy()
    # Keep parsable tool messages (notably pdfinfo's Pages field) locale-independent.
    env["LC_ALL"] = "C"
    # The extracted upload must not find source files through local search paths.
    for key in ("TEXINPUTS", "BIBINPUTS", "BSTINPUTS"):
        env.pop(key, None)
    result = subprocess.run(args, cwd=cwd, env=env, text=True,
                            encoding="utf-8", errors="replace",
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    require(result.returncode == 0,
            f"Command failed in {cwd}: {' '.join(args)}\n{result.stdout[-16000:]}")
    return result.stdout


def tool(name: str) -> str:
    path = shutil.which(name)
    require(path is not None, f"Required command not found on PATH: {name}")
    return str(path)


def without_comments(text: str) -> str:
    return re.sub(r"(?<!\\)%[^\n]*", "", text)


def check_text(text: str, label: str) -> None:
    require(not re.search(r"\b(?:TODO|FIXME|TBD)\b|\\todo\b|\?\?", text),
            f"Unresolved editorial marker in {label}")
    # URL line breaks in extracted PDF text must not turn the one permitted
    # marker into an apparently different placeholder.
    remainder = re.sub(r"\s*".join(re.escape(char) for char in PALOMAR), "", text)
    require(not re.search(r"\b[A-Z_]*PLACEHOLDER[A-Z_]*\b", remainder),
            f"Unexpected placeholder in {label}")


def case_correct(path: Path) -> bool:
    current = PAPER
    for part in path.parts:
        if part not in {item.name for item in current.iterdir()}:
            return False
        current /= part
    return current.is_file()


def source_files() -> list[Path]:
    """Follow the article's explicit local inputs, excluding unrelated files."""
    files: set[Path] = set()
    pending = [Path("main.tex"), Path("references.bib")]
    while pending:
        relative = pending.pop()
        require(not relative.is_absolute() and ".." not in relative.parts,
                f"Source dependency escapes paper/: {relative}")
        require(all(re.fullmatch(r"[A-Za-z0-9_+.,=-]+", part)
                    and not part.startswith(".") for part in relative.parts),
                f"Nonportable source filename: {relative}")
        require(case_correct(relative), f"Missing or case-mismatched source: {relative}")
        require(not (PAPER / relative).is_symlink(), f"Symlink input: {relative}")
        if relative in files:
            continue
        files.add(relative)
        if relative.suffix not in {".tex", ".sty", ".cls", ".bib", ".bst"}:
            continue
        text = without_comments((PAPER / relative).read_text(encoding="utf-8"))
        check_text(text, str(relative))
        for name in re.findall(r"\\(?:input|include)\s*\{([^}]+)\}", text):
            path = Path(name)
            path = path if path.suffix else path.with_suffix(".tex")
            # pdfTeX supplies this mapping file in its standard installation;
            # it is deliberately not copied into the upload bundle.
            if path == Path("glyphtounicode.tex") and not (PAPER / path).exists():
                continue
            pending.append(path)
        for names in re.findall(r"\\bibliography\s*\{([^}]+)\}", text):
            pending.extend(Path(name.strip()).with_suffix(".bib") for name in names.split(","))
        # Include a local class/style only if this article actually loads it.
        for kind, names in re.findall(
                r"\\(usepackage|documentclass|bibliographystyle)(?:\[[^]]*\])?\s*\{([^}]+)\}", text):
            suffix = {"usepackage": ".sty", "documentclass": ".cls", "bibliographystyle": ".bst"}[kind]
            for name in names.split(","):
                path = Path(name.strip()).with_suffix(suffix)
                if (PAPER / path).exists():
                    pending.append(path)
        for name in re.findall(r"\\includegraphics(?:\[[^]]*\])?\s*\{([^}]+)\}", text):
            path = Path(name)
            choices = [path] if path.suffix else [path.with_suffix(ext) for ext in (".pdf", ".png", ".jpg", ".jpeg")]
            matches = [candidate for candidate in choices if (PAPER / candidate).is_file()]
            require(len(matches) == 1, f"Missing or ambiguous figure: {name}")
            require(matches[0].parts[0] == "figures", "Figure inputs must be under figures/")
            pending.extend(matches)
    return sorted(files)


def metadata() -> dict[str, str]:
    raw = (PAPER / "arxiv-metadata.txt").read_text(encoding="utf-8")
    fields: dict[str, str] = {}
    key = None
    for line in raw.splitlines():
        candidate, separator, value = line.partition(":")
        if separator and candidate in FIELDS:
            require(candidate not in fields, f"Duplicate metadata field: {candidate}")
            key = candidate
            fields[key] = value.strip()
        elif key is not None and line.strip():
            fields[key] += (" " if fields[key] else "") + line.strip()
    require(set(fields) == set(FIELDS), f"Missing metadata fields: {set(FIELDS) - set(fields)}")
    for key in ("Title", "Authors", "Abstract", "Comments", "Primary category", "MSC-class", "Repository"):
        require(bool(fields[key]), f"Empty required metadata field: {key}")
    for key in ("Title", "Abstract"):
        require(fields[key].isascii(), f"Use portable TeX accents, not Unicode, in metadata {key}")
        require(not re.search(r"\\(?:stack|estim|TreeStack|cite|ref|eqref|newcommand)\b", fields[key]),
                f"Expand local macros/references in metadata {key}")
    require(len(fields["Abstract"]) <= 1920, "Metadata abstract exceeds 1920 characters")
    check_text(raw, "arxiv-metadata.txt")
    return fields


def compile_paper(directory: Path, pdflatex: str, bibtex: str, *, bibliography: bool) -> str:
    args = [pdflatex, "-no-shell-escape", "-interaction=nonstopmode", "-halt-on-error", "-file-line-error", "main.tex"]
    command(args, directory)
    if bibliography:
        output = command([bibtex, "main"], directory)
        require("Warning--" not in output, f"BibTeX warning:\n{output}")
    for _ in range(4):
        command(args, directory)
        log = (directory / "main.log").read_text(encoding="utf-8", errors="replace")
        if not re.search(r"Rerun to get|Label\(s\) may have changed|rerunfilecheck Warning", log):
            break
    return log


def check_log(log: str, label: str) -> None:
    problems = [line for line in log.splitlines() if re.search(
        r"^!|LaTeX Error|undefined|multiply defined|Overfull \\[hv]box|"
        r"Rerun to get|Label\(s\) may have changed|rerunfilecheck Warning|Missing character:", line)]
    require(not problems, f"{label} failed:\n" + "\n".join(problems))


def pdf_details(directory: Path, pdfinfo: str, pdftotext: str) -> tuple[int, str]:
    info = command([pdfinfo, "main.pdf"], directory)
    count = re.search(r"^Pages:\s+(\d+)", info, re.MULTILINE)
    require(count is not None, "Cannot determine PDF page count")
    command([pdftotext, "-layout", "main.pdf", "main.txt"], directory)
    text = (directory / "main.txt").read_text(encoding="utf-8")
    require(len(text.strip()) > 1000, "PDF text extraction is empty or unexpectedly short")
    require("\ufffd" not in text, "Replacement character in PDF text extraction")
    check_text(text, "extracted PDF text")
    return int(count.group(1)), text


def archive(files: list[Path], bbl: Path, target: Path) -> None:
    target.parent.mkdir(exist_ok=True)
    with target.open("wb") as output:
        with gzip.GzipFile(filename="", mode="wb", fileobj=output, mtime=0) as compressed:
            with tarfile.open(fileobj=compressed, mode="w", format=tarfile.USTAR_FORMAT) as bundle:
                inputs = {str(path): PAPER / path for path in files}
                inputs["main.bbl"] = bbl
                for name, path in sorted(inputs.items()):
                    data = path.read_bytes()
                    entry = tarfile.TarInfo(name)
                    entry.size = len(data)
                    entry.mode = 0o644
                    bundle.addfile(entry, io.BytesIO(data))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--draft", action="store_true", help="Compile for inspection; do not preflight or package")
    args = parser.parse_args()
    report_path = BUILD / "preflight.json"
    if report_path.exists():
        report_path.unlink()
    pdflatex, bibtex = tool("pdflatex"), tool("bibtex")
    files = source_files()
    local = BUILD / "local"
    if local.exists():
        shutil.rmtree(local)
    local.mkdir(parents=True)
    for relative in files:
        (local / relative).parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(PAPER / relative, local / relative)
    log = compile_paper(local, pdflatex, bibtex, bibliography=True)
    if args.draft:
        shutil.copyfile(local / "main.pdf", PAPER / "TreeStack.pdf")
        print(f"Draft compiled: {PAPER / 'TreeStack.pdf'}; inspect {local / 'main.log'}")
        return
    check_log(log, "Canonical compilation")
    fields = metadata()
    pdfinfo, pdftotext = tool("pdfinfo"), tool("pdftotext")
    pages, text = pdf_details(local, pdfinfo, pdftotext)
    page_comment = re.search(r"\b(\d+) pages?\b", fields["Comments"])
    require(page_comment is not None and int(page_comment.group(1)) == pages,
            f"Metadata Comments must give the actual page count: {pages} pages")
    figures = sum(len(re.findall(r"\\begin\{figure\*?\}", without_comments((PAPER / p).read_text())))
                  for p in files if p.suffix == ".tex")
    figure_comment = re.search(r"\b(\d+) figures?\b", fields["Comments"])
    require(figure_comment is not None and int(figure_comment.group(1)) == figures,
            f"Metadata Comments must give the actual figure count: {figures} figures")
    target = PAPER / "arxiv" / "TreeStack-arxiv.tar.gz"
    candidate = BUILD / "TreeStack-arxiv.tar.gz"
    archive(files, local / "main.bbl", candidate)
    extracted = BUILD / "arxiv-extracted"
    if extracted.exists():
        shutil.rmtree(extracted)
    extracted.mkdir()
    with tarfile.open(candidate, "r:gz") as bundle:
        # Read our allowlisted members individually; do not trust tar paths or links.
        expected = {str(path) for path in files} | {"main.bbl"}
        require(set(bundle.getnames()) == expected, "Unexpected file in arXiv archive")
        for item in bundle:
            require(item.isfile() and item.name in expected, f"Unsafe archive member: {item.name}")
            destination = extracted / item.name
            destination.parent.mkdir(parents=True, exist_ok=True)
            stream = bundle.extractfile(item)
            require(stream is not None, f"Missing archive content: {item.name}")
            destination.write_bytes(stream.read())
    check_log(compile_paper(extracted, pdflatex, bibtex, bibliography=False), "Extracted-bundle compilation")
    bundle_pages, bundle_text = pdf_details(extracted, pdfinfo, pdftotext)
    require((pages, text) == (bundle_pages, bundle_text), "Extracted upload PDF differs from canonical PDF")
    target.parent.mkdir(exist_ok=True)
    shutil.copyfile(candidate, target)
    shutil.copyfile(local / "main.pdf", PAPER / "TreeStack.pdf")
    report = {
        "status": "passed",
        "engine": command([pdflatex, "--version"], PAPER).splitlines()[0],
        "pages": pages,
        "figures": figures,
        "abstract_characters": len(fields["Abstract"]),
        "source_files": [str(path) for path in files],
        "source_sha256": {str(path): hashlib.sha256((PAPER / path).read_bytes()).hexdigest() for path in files},
        "bundle_sha256": hashlib.sha256(target.read_bytes()).hexdigest(),
        "bundled_bibliography": "main.bbl",
        "extracted_bundle_compiles_without_bibtex": True,
        "canonical_and_bundle_pdf_text_identical": True,
        "unresolved_references_citations_or_overfull_boxes": 0,
        "permitted_placeholder": PALOMAR if PALOMAR in re.sub(r"\s+", "", text) else None,
    }
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    print(f"PDF: {PAPER / 'TreeStack.pdf'}\nUpload bundle: {target}")


if __name__ == "__main__":
    try:
        main()
    except (PreflightError, OSError) as error:
        print(f"Paper preflight failed: {error}", file=sys.stderr)
        sys.exit(1)
