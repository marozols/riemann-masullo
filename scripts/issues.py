#!/usr/bin/env python3
"""Keep `proof` issues in step with the `sorry`s in RiemannMasullo/.

    scripts/issues.py            show what would change
    scripts/issues.py --apply    open an issue per new sorry, close issues whose sorry is gone,
                                 and unblock section issues whose prerequisites are closed

Run from an up-to-date `main`. Lean itself reports the sorries (`lake build` warnings), so this
never misreads the source. An issue is tied to its declaration by a hidden marker in the body.
A section issue lists the issues it waits for in a marker `<!-- needs: 12 15 -->`; when all of
them are closed, its `blocked` label is removed.
"""
import json, pathlib, re, subprocess, sys, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
WARN = re.compile(r"warning: (RiemannMasullo/\S+?\.lean):(\d+):(\d+): declaration uses `sorry`")
MARK = re.compile(r"<!-- sorry: (\S+) -->")


def run(cmd, **kw):
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, **kw)


def list_issues(state, label):
    """All issues with a label, through the REST listing. `gh issue list` with a label goes
    through GitHub's search, which stops at 1,000 results, and a truncated list of open proof
    issues makes this script open duplicates."""
    out = run(["gh", "api", "--paginate",
               f"repos/{{owner}}/{{repo}}/issues?state={state}&labels={label}&per_page=100",
               "--jq", ".[] | select(.pull_request | not) | {number, state, title, body} | tojson"])
    if out.returncode:
        sys.exit(out.stderr)
    return [json.loads(line) for line in out.stdout.splitlines() if line.strip()]


def sorries():
    out = run(["lake", "build", "RiemannMasullo"])
    if out.returncode:
        sys.exit("lake build failed; fix the build first\n" + (out.stdout + out.stderr)[-3000:])
    found = {}
    for path, line, col in WARN.findall(out.stdout + out.stderr):
        lines = (ROOT / path).read_text().splitlines()
        i = int(line) - 1
        name = re.match(r"[^\s:({\[]+", lines[i][int(col):])
        name = name.group(0) if name else f"line{line}"
        top = i
        while top > 0 and lines[top - 1].lstrip().startswith("@["):
            top -= 1
        if top > 0 and lines[top - 1].rstrip().endswith("-/"):
            top -= 1
            while top > 0 and "/--" not in lines[top]:
                top -= 1
        end = i
        while end < len(lines) - 1 and "sorry" not in lines[end] and end - i < 80:
            end += 1
        block = "\n".join(lines[top:end + 1])
        paper = re.search(r"Paper:\s*(.*?\bpp?\.\s*\d+(?:[-–]\d+)?)", block)
        found[f"{path}::{name}"] = dict(path=path, line=int(line), name=name, block=block,
                                        paper=paper.group(1) if paper else "")
    return found


def chapter_label(path):
    m = re.match(r"RiemannMasullo/(Ch\d+|App[A-E])", path)
    return m.group(1)[0].lower() + m.group(1)[1:] if m else None


def main():
    apply = "--apply" in sys.argv
    branch = run(["git", "rev-parse", "--abbrev-ref", "HEAD"]).stdout.strip()
    if branch != "main":
        print(f"note: on branch {branch}, not main", file=sys.stderr)
    sha = run(["git", "rev-parse", "--short", "HEAD"]).stdout.strip()
    full_sha = run(["git", "rev-parse", "HEAD"]).stdout.strip()
    url = run(["gh", "repo", "view", "--json", "url", "--jq", ".url"]).stdout.strip()
    current = sorries()
    open_issues = {}
    for issue in sorted(list_issues("open", "proof"), key=lambda i: -i["number"]):
        m = MARK.search(issue["body"] or "")
        if m:
            open_issues[m.group(1)] = issue["number"]      # the oldest issue wins

    new = [k for k in current if k not in open_issues]
    stale = [k for k in open_issues if k not in current]
    print(f"{len(current)} sorries at {sha}; {len(open_issues)} open proof issues; "
          f"{len(new)} to open, {len(stale)} to close")
    for key in new:
        s = current[key]
        title = f"Prove `{s['name']}`" + (f" ({s['paper']})" if s["paper"] else "")
        body = (f"[`{s['path']}`, line {s['line']}]({url}/blob/{full_sha}/{s['path']}#L{s['line']})\n\n"
                f"```lean\n{s['block']}\n```\n\n"
                "Replace the `sorry` with a proof, or split it into smaller lemmas, without changing "
                "the statement. If the statement looks wrong, say so here instead.\n\n"
                "**To take this issue**, comment `Claiming`, then follow "
                f"[CONTRIBUTING.md]({url}/blob/main/CONTRIBUTING.md). The paper is in "
                f"[`paper/`]({url}/tree/main/paper).\n\n"
                f"<!-- sorry: {key} -->\n")
        print(f"  open   {title}")
        if apply:
            cmd = ["gh", "issue", "create", "--title", title, "--body", body, "--label", "proof"]
            if chapter_label(s["path"]):
                cmd += ["--label", chapter_label(s["path"])]
            r = run(cmd)
            print("        ", (r.stdout or r.stderr).strip())
            time.sleep(1.5)   # stay under GitHub's limit on creating content
    for key in stale:
        print(f"  close  #{open_issues[key]}  {key}")
        if apply:
            run(["gh", "issue", "close", str(open_issues[key]), "--comment",
                 f"`{key.split('::')[1]}` is no longer a `sorry` on main at {sha}."])
    ready = unblock(apply)
    if not apply and (new or stale or ready):
        print("dry run; pass --apply to make these changes")


def unblock(apply):
    """Remove `blocked` from open issues whose `<!-- needs: ... -->` issues are all closed."""
    states = {i["number"]: i["state"] for i in list_issues("all", "section")}
    blocked = list_issues("open", "blocked")
    ready = []
    for issue in sorted(blocked, key=lambda i: i["number"]):
        m = re.search(r"<!-- needs:([\d\s]*)-->", issue["body"] or "")
        if m and all(states.get(int(n)) == "closed" for n in m.group(1).split()):
            ready.append(issue["number"])
            print(f"  unblock #{issue['number']}  {issue['title']}")
            if apply:
                run(["gh", "issue", "edit", str(issue["number"]), "--remove-label", "blocked"])
    return ready


if __name__ == "__main__":
    main()
