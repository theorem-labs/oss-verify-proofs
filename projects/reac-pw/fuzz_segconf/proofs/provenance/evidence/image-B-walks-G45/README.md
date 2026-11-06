# Step plans of the image-B program walks, groups G4 + G5 (fuzz_segconf.asan-ubsan)

The step plans of the 21 image-B walks of groups G4 and G5 (one plan-<F>.md per walked function: the image-A to
image-B instruction map, the instrumented checks, the UBSan trap branches and the premise that refutes each, the
calls and their callee contracts, the abort arms, the stack window, the segment split) are records, not shipped
files. They are kept byte for byte in the unit's internal record at commit c83b0c95cf3bdf93055fd8ee791581efc9ad8acf,
directory Bwalks-G45-plans/, with the sha256 of each file in that commit's MANIFEST.

Some walk files cite a plan in a comment as "the unit record's Bwalks-G45-plans/plan-<F>.md"; that is the file in the
table below. The citing files: lib/B/Prog/check_address.v, check_declared.v, check_ignore.v, check_segments_s1.v,
name_ok.v, name_ok_s1.v, reac_declared_vlan_add.v, reac_segconf_find.v, reac_segconf_find_lem.v, reac_segconf_init.v.
(reac_segconf_find.v, reac_segconf_find_lem.v and reac_segconf_ignored.v also cite image A's plan of the same
function, marked "image A's walk record"; that is image A's record, not one of these.)

| record path (commit c83b0c95cf3b) | sha256 |
|---|---|
| Bwalks-G45-plans/plan-check_absent.md | a051e153dc7f80882f1eff120f712bd8356e4a106b4725cbc20a6aef88eef23d |
| Bwalks-G45-plans/plan-check_address.md | 4ca788db00349f09c06bb396d5029a7422711af700189b9f31dd30abb3096260 |
| Bwalks-G45-plans/plan-check_declared.md | e02333362b10174e99456064c8e8a732e6f2a7d0fe5f8328bb16ea46c0ca9176 |
| Bwalks-G45-plans/plan-check_ignore.md | 04868191f3ae925bfe31779eed548b9ba63f2c72c37fc27dd85d6313707eab0f |
| Bwalks-G45-plans/plan-check_knock_refused.md | 1f79c5521789be6821acfb04e4315359d714d39ef3143ca3ecc2d7506749e769 |
| Bwalks-G45-plans/plan-check_model.md | 23e8c34f526b9d89ef60eee9877382e1061dd5a15537609b4af5660a48ca4401 |
| Bwalks-G45-plans/plan-check_provenance.md | a8377d61532048d4972e41e2e00a816eaab94e41713176696cc9ff2fe5c5de30 |
| Bwalks-G45-plans/plan-check_refusals.md | 6168404f7bea1ad066179a3f8838185179c46c0d32080e3770f5801372d685b7 |
| Bwalks-G45-plans/plan-check_role.md | e1efad7bc3951298102ab001b2b8def8f2061dc62551739c8024e6a38b811a78 |
| Bwalks-G45-plans/plan-check_segments.md | bb22fc5e41a44cc8e6c0b64ba4807ec45bccbb8bc12da7ce9e844cbf5cd695f4 |
| Bwalks-G45-plans/plan-name_ok.md | 06c106c1159908627107542b1bc46db908c6210546207ded107c24e1bd2a594c |
| Bwalks-G45-plans/plan-reac_declared_vlan_add.md | e1d4e75954fe8a2ea9bdf9425179bb20f3a59a184728bf1e0270812ddd76d371 |
| Bwalks-G45-plans/plan-reac_declared_vlan_split.md | 413663ceb0600eba7905a5f4f18605bba43465cfc497426b1c7ca91de6e9f746 |
| Bwalks-G45-plans/plan-reac_segconf_declared.md | 2c665be610679e07fb4947dca610d704bd83056c69b8966a4867d0a057b5d72c |
| Bwalks-G45-plans/plan-reac_segconf_find.md | a2d1c3fb78e89276eced85c01254873fb4f6f513890683bc63231249345cd3e6 |
| Bwalks-G45-plans/plan-reac_segconf_ignore_file.md | 2a4b2ad30510cb38edca0dc0b572d4e1ffc1ef0de2e40b32d14ff67eb2d33868 |
| Bwalks-G45-plans/plan-reac_segconf_ignored.md | e753db61e62351fa5dc46e567ff7140aa90f83e4de54ff5b47984a8b4afc2b9d |
| Bwalks-G45-plans/plan-reac_segconf_init.md | 464fbe338859fe79a93a2c0ac85d055e5390024d5ebf30a413d64c78001ee496 |
| Bwalks-G45-plans/plan-reac_segconf_model.md | 33bd1ce9aaf15965ad2149ade29aa05261eed7b5ed20c0f9fce8e4e5be572db2 |
| Bwalks-G45-plans/plan-reac_segconf_role.md | 669824b651717c146f0400762afbed451f9c4f790fc596a937bbc43ed4eb064b |
| Bwalks-G45-plans/plan-reac_segconf_role_file.md | 509e6af5337e5403ed2c0224db8c12446f6a35b6af6873069ff271bd1f8fe5d0 |
