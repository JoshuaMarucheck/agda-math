"""Not very clean, just checks if the name appears in the whole file (ignoring scope)"""

from pathlib import Path
import glob

agda_dir = Path(__file__).parent / "Plasmaduck"
targets = list(map(lambda p: agda_dir / p, glob.glob("*/**/*.agda", root_dir=agda_dir)))
assert (
    Path(
        "/home/joshuascardboardbox/Desktop/Agda/classical/Plasmaduck/Relation/DecStrictPartialOrder/Trees.agda"
    )
    in targets
)
# Known bugs:
# probably doesn't handle multiline imports well (which is especially bad if it deletes public
# doesn't seek through all subdirectories somehow??? I added a star to the glob,
#   but I don't think that's the right fix since now it just searches one directory lower,
#   and it needs to search one down, meaning it won't find top-level files.
# deletes modules if they're used for qualified imports (like import Function, and then Function.id appears somewhere (esp open import Function using (flip), and then Function.id is used somewhere))


def min_existing(*idx: int) -> int:
    """Takes indices from find function (which return -1 if not found), and returns the minimum of those that are not -1.
    If all inputs are -1, returns -1."""
    r: int | None = None
    for i in idx:
        if i == -1:
            continue
        if r is None:
            r = i
        else:
            r = min(r, i)
    if r is None:
        return -1
    return r


def clean_file(target: Path) -> None:
    output_lines: list[str] = []
    with open(target, "r") as f:
        lines = f.readlines()

    for line in lines:
        if line.strip().startswith("open") and not line.strip().endswith(" public"):
            using_imports: list[str] = []
            renaming_imports: list[tuple[str, str]] = []

            i = line.find("using")
            if i != -1:
                i = 1 + line.find("(", i)

                end = line.find(")", i)
                while i < end:
                    j = line.find(";", i, end)
                    if j == -1:
                        j = end

                    item = line[i:j].strip()
                    using_imports.append(item)
                    i = j + 1

            i = line.find("renaming")
            if i != -1:
                i = 1 + line.find("(", i)
                end = line.find(")", i)

                while i < end:
                    j1 = line.find("to", i, end)
                    if j1 == -1:
                        break
                    j2 = line.find(";", j1, end)
                    if j2 == -1:
                        j2 = end

                    item1 = line[i:j1].strip()
                    item2 = line[j1 + 2 : j2].strip()
                    renaming_imports.append((item1, item2))
                    i = j2 + 1

            using_imports1: list[str] = []
            for name in using_imports:
                names = list(
                    filter(lambda s: s != "", name.removeprefix("module ").split("_"))
                )
                for l in lines:
                    if l != line and (
                        (
                            name.startswith("module ")
                            and ("open " + name.removeprefix("module ")) in l
                        )
                        or any(n in l for n in names)
                    ):
                        using_imports1.append(name)
                        break

            renaming_imports1: list[tuple[str, str]] = []
            for name1, name2 in renaming_imports:
                names = list(filter(lambda s: s != "", name2.split("_")))
                for l in lines:
                    if l != line and (
                        ("open " + name2) in l or any(n in l for n in names)
                    ):
                        renaming_imports1.append((name1, name2))
                        break

            if len(using_imports1) == 0 and len(renaming_imports1) == 0:
                if "using" not in line and "renaming" not in line:
                    output_lines.append(line)

            else:
                idx = min_existing(line.find("using"), line.find("renaming"))
                if idx != -1:
                    s: str = line[: idx - 1]

                    if "using" in line:
                        # Even if there are no imports, we want this to prevent importing all names in the module
                        s += " using ("
                        s += "; ".join(using_imports1)
                        s += ")"
                    if len(renaming_imports1) > 0:
                        s += " renaming ("
                        s += "; ".join(
                            map(
                                lambda pair: pair[0] + " to " + pair[1],
                                renaming_imports1,
                            )
                        )
                        s += ")"

                    s += "\n"
                    output_lines.append(s)
                else:
                    # print nothing
                    pass
        else:
            output_lines.append(line)

    with open(target, "w") as f:
        f.writelines(output_lines)


for target in targets:
    clean_file(target)
