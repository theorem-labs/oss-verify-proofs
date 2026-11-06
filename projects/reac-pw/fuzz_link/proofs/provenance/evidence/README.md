# What the files in this directory are

These are **verbatim run records**: the output of the tools that produced this
unit's tables, kept as the tools wrote it. They are evidence, not prose, and
they are not rewritten — editing them would make the record disagree with the
run it records.

Because they are verbatim, some of them quote commit identifiers of **internal
working commits** of the lanes that produced the tables. Those commits are not
published, so a reader of the release cannot resolve them from this repository.
They are preserved, with the files they name, in this unit's records ref so that
the record stays checkable:

- A-side records: `records/reac-pw-fuzz_link-asan` on the project's internal
  remote, whose `MANIFEST` lists each preserved file with its `sha256`.

Where a claim in these records needs to be checked, check it against the
`sha256` of the file the record names, not against the commit identifier: the
hash identifies the bytes and does not depend on which branches have been
published.

Nothing in this file cites a commit. Every prose claim this unit makes outside
this directory names files by content hash in the form
`<path> (file sha256 <12>; donor not released)` for a donor file and
`<basename> (sha256 <12>; internal record)` for a lane file.
