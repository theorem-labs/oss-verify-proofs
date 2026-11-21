# Contributing

Proofs go in `projects/<project>/<harness>/proofs/<statement>/` and
counterexamples in `projects/<project>/<harness>/counterexamples/<statement>/`
([docs/proving.md](docs/proving.md)); what a proof must meet to enter a
release, and how a maintainer checks it, is in
[docs/adding-a-proof.md](docs/adding-a-proof.md). An agent that adds a proof
follows [the adding-a-proof skill](.claude/skills/adding-a-proof/SKILL.md).
Its licence step holds for every proof: a file made from a proof library here
keeps the licence lines of its case (requirement 7 of docs/adding-a-proof.md).
Run `./oft generate --skip-shared` and commit what it renders with your change,
since a new proof changes your fuzz target's page; the shared pages and the
index are rendered after the merge, so your pull request carries none of them.
Before you open the pull request, run the commands of step 3 of
[docs/adding-a-proof.md](docs/adding-a-proof.md#steps): they lint the change
from its merge base, with the kind that CI gives the pull request (step 3
says which kind), and check the proofs in the checker image. Corrections to
a harness summary, a check or a reason are welcome as issues. Your own work is
under the MIT licence, with a DCO sign-off (`git commit -s`). A pull request
from outside may touch only a harness's `proofs/` and `counterexamples/`
folders (under `projects/<project>/<harness>/`), `docs/` and the rendered files
that follow from them. New projects are enrolled in
[theorem-labs/oss-verify](https://github.com/theorem-labs/oss-verify), not here.
