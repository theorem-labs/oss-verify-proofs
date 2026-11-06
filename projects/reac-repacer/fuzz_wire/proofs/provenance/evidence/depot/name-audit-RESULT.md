# Lane-name audit at 4483a8de6e6f (the publication owner via the unit owner's ruling, 00:33Z) — read only
Greps over *.v (provenance/ excluded) for the start-up generators' own header markers (the af0m tool path and the start-up collector's generated-by markers), the
collector-header text of every start-up generator, and lane / worker / branch tokens. Every hit classified.
Counts: (a) Modified-by notice 71 (49 brief-marker + 22 extra), (b) registered KEEP line 2, (c) ordinary comment 83
(48 + 35). No (b) KEEP line carries a lane / worker / branch name.
Registry gaps (for the registry owner): lib/Reusable/DepotCfg.v:12, :14 are KEEP lines under registry row DC1 (status TOOL, not
SCRUB-NAMES), naming tools/startup/af0m.py, no lane token; a gap only if af0m.py is not a tool of record.
K list: 10 (a) notices were missing and are now in postship (d3): A/AB01:4 AB03:4 AB05:4 AB12:4 AD1k:4 AD2i:4 AD2j:4
AE37:5 AE3i:4 AF0m:9 (tool-written, no lane name). The 9 AD3* line-3 comments (d2) stay open and span long (AD3c to
line 100); licence-lines --apply would remove the span whole, which is already comment text in Rocq.
(c): 72 name-carrying comment lines remain in files the lane scrub lists (58 in AD3*): knock's inherited comment text.
The per-row tables (file:line, lane name, class, +SCRUB) name the lanes they locate, so they are kept out of the shipped evidence (they would fail the ship lint); they are held with the worker record for the scrub pass.
