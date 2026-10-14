#!/usr/bin/env python3
"""Build paper/refs.bib from verified metadata only (Claude's code).

    build_bib.py

arXiv entries come from the arXiv API (title, authors, year are taken from the API response, never typed), DOI
entries from doi.org content negotiation (Crossref BibTeX). A missing or mismatching record aborts the build.
Web resources (software, datasets, a blog post) are listed by hand with the URL that was checked to resolve.
"""
import re, subprocess, sys, xml.etree.ElementTree as ET
from pathlib import Path

OUT = Path(__file__).resolve().parent.parent / "paper/refs.bib"
ARXIV = {
    "du2023debate": "2305.14325", "li2024moreagents": "2402.05120", "wang2023selfconsistency": "2203.11171",
    "hong2023metagpt": "2308.00352", "wu2023autogen": "2308.08155", "qian2023chatdev": "2307.07924",
    "cemri2025fail": "2503.13657", "brown2024monkeys": "2407.21787", "zheng2021minif2f": "2109.00110",
    "tsoukalas2024putnambench": "2407.11214", "ren2025deepseekprover": "2504.21801", "novikov2025alphaevolve": "2506.13131",
    "wang2026horizonmath": "2603.15617", "white2024livebench": "2406.19314", "jain2024livecodebench": "2403.07974",
    "bondarenko2025specgaming": "2502.13295", "glm2025glm45": "2508.06471", "kim2025scaling": "2512.08296",
    "lin2025goedel": "2502.07640", "adamczewski2026oeisopen": "2608.11941", "zhang2025rlm": "2512.24601",
}
DOI = {
    "demoura2021lean4": "10.1007/978-3-030-79876-5_37", "mathlib2020": "10.1145/3372885.3373824",
    "mcnemar1947": "10.1007/BF02295996", "clopper1934": "10.1093/biomet/26.4.404",
    "tango1998": "10.1002/(SICI)1097-0258(19980430)17:8<891::AID-SIM780>3.0.CO;2-B", "nosek2018": "10.1073/pnas.1708274114",
}
MISC = r"""
@misc{anthropic2025multiagent,
  author = {{Anthropic}},
  title = {How we built our multi-agent research system},
  year = {2025},
  howpublished = {\url{https://www.anthropic.com/engineering/multi-agent-research-system}},
  note = {Engineering blog post}
}
@misc{formalconjectures,
  author = {{Google DeepMind}},
  title = {{Formal Conjectures}: a collection of formalised statements of conjectures in {Lean}},
  year = {2026},
  howpublished = {\url{https://github.com/google-deepmind/formal-conjectures}},
  note = {Commit 79222608 (October 2026), Apache-2.0}
}
@misc{oeis,
  author = {{OEIS Foundation Inc.}},
  title = {The {On-Line Encyclopedia of Integer Sequences}},
  year = {2026},
  howpublished = {\url{https://oeis.org}}
}
@misc{primeagent,
  author = {{Prime Intellect}},
  title = {{Prime Agent}: a self-improving {RLM} harness},
  year = {2026},
  howpublished = {\url{https://github.com/PrimeIntellect-ai/prime-agent}},
  note = {Version 0.10.0, commit e6ebebe}
}
@misc{glm53,
  author = {{Z.ai}},
  title = {{GLM-5.3}},
  year = {2026},
  note = {Proprietary model served through the Z.ai API; accessed October 2026}
}
"""


def bibtex_escape(s):
    return s.replace("&", r"\&").replace("%", r"\%").replace("#", r"\#").replace("_", r"\_")


def arxiv_entries():
    ids = ",".join(ARXIV.values())
    xml = subprocess.run(["curl", "-sS", "-L", "--max-time", "120", f"https://export.arxiv.org/api/query?id_list={ids}&max_results=50"],
                         capture_output=True, text=True, check=True).stdout
    ns = {"a": "http://www.w3.org/2005/Atom", "x": "http://arxiv.org/schemas/atom"}
    got = {}
    for e in ET.fromstring(xml).findall("a:entry", ns):
        aid = re.sub(r"v\d+$", "", e.find("a:id", ns).text.split("/abs/")[-1])
        title = " ".join(e.find("a:title", ns).text.split())
        authors = [a.find("a:name", ns).text for a in e.findall("a:author", ns)]
        year = e.find("a:published", ns).text[:4]
        prim = e.find("x:primary_category", ns)
        got[aid] = (title, authors, year, prim.get("term") if prim is not None else "")
    out = []
    for key, aid in ARXIV.items():
        if aid not in got:
            sys.exit(f"arXiv {aid} ({key}) not returned by the API")
        title, authors, year, cat = got[aid]
        # formatting only: drop punctuation-only "authors" and brace collective names (e.g. "GLM-4. 5 Team")
        authors = [a for a in authors if re.search(r"[A-Za-z]", a)]
        authors = ["{" + re.sub(r"(\d)\. (\d)", r"\1.\2", a) + "}" if a.endswith(" Team") else a for a in authors]
        au = " and ".join(authors[:10]) + (" and others" if len(authors) > 10 else "")
        out.append(f"@misc{{{key},\n  author = {{{bibtex_escape(au)}}},\n  title = {{{{{bibtex_escape(title)}}}}},\n  year = {{{year}}},\n"
                   f"  eprint = {{{aid}}},\n  archivePrefix = {{arXiv}},\n  primaryClass = {{{cat}}},\n  howpublished = {{arXiv:{aid}}}\n}}")
    return out


def doi_entries():
    out = []
    for key, doi in DOI.items():
        r = subprocess.run(["curl", "-sS", "-L", "--max-time", "60", "-H", "Accept: application/x-bibtex", f"https://doi.org/{doi}"],
                           capture_output=True, text=True)
        b = r.stdout.strip()
        if not b.startswith("@"):
            sys.exit(f"DOI {doi} ({key}) did not resolve to BibTeX: {b[:120]!r}")
        b = re.sub(r"^@(\w+)\{[^,]*,", lambda m: f"@{m.group(1)}{{{key},", b, count=1)
        # some publishers deposit titles and surnames in capitals; normalise case only (the words are unchanged)
        small = {"a", "an", "and", "in", "of", "on", "or", "the", "to", "for"}
        b = re.sub(r"title=\{([^{}]*)\}", lambda m: "title={" + (" ".join(
            w.lower() if i and w.lower() in small else w.capitalize() for i, w in enumerate(m.group(1).split()))
            if m.group(1).isupper() else m.group(1)) + "}", b, count=1)
        b = re.sub(r"author=\{([^{}]*)\}", lambda m: "author={" + re.sub(r"\b([A-Z]{2,})\b", lambda w: w.group(1).capitalize(), m.group(1)) + "}", b, count=1)
        b = b.replace("title={The lean mathematical library}", "title={The {L}ean Mathematical Library}")
        out.append(b)
    return out


entries = arxiv_entries() + doi_entries()
OUT.write_text("% generated by scripts/build_bib.py from the arXiv API and doi.org -- do not edit\n\n" + "\n\n".join(entries) + "\n" + MISC)
print(f"{len(entries)} verified entries + {MISC.count('@misc')} web resources -> {OUT}")
