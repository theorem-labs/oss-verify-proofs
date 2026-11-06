# kit-rerun-86da41d3ef68: the code-equality claims of plugin-hostd/fuzz_command measured again with cmpkit 86da41d3ef68

Each file below is part of one record (RECORD.md). It measures again, with the comparison kit of record, every comment in this unit that says two copies of code are the same. One claim is false as written (lib/B/Prog/send_message_k.v:5, after 0x86e48), one gives a wrong address in a true claim, four could not be measured, and every other claim is the same.

| file | sha256 | role |
|---|---|---|
| RECORD.md | dbb9926ab786d63bc10a11f51e6a09d0e57aac3b61c87309c616da6f4db3fafa | the record: why, the inventory, the images, the commands, the verdicts (one changed), the scans, the hand traces of the kit's known fail-opens, the citation changes |
| amb-AB.tsv | ff3299a695e89f96cf670a7df9cd0027fbc51a7a24442079164570bf3e7e0f58 | ambiscan over the earlier fuzz_command.asan / asan-ubsan compare outputs: 0 ambiguous hits |
| amb-grant.tsv | b3f2063716d5bbb955897481363845e16b3136085b7d089e3c88f39777b5142a | ambiscan over the earlier fuzz_grant / fuzz_command compare outputs: 0 by-name compares read, 0 hits |
| amb-intrin.tsv | dce65e054bf5f203f587001af66c43483ca093458f3114d9832e96365243e145 | ambiscan over the earlier cgif / fuzz_command compare output: 0 ambiguous hits |
| claims.tsv | 3e99dfa5a539370612d9a52a8f880e7f105ed8ff4d400f9d7cc0324c05498154 | the 73 code-equality claims: maker class, what the re-run compares, the kit rows, the kit verdict, the settled verdict, the citation change |
| fail-open-traces.tsv | 71a32a6e5d9f7c39c283a70a877fe365e3b1db3af46d2438b4ebaac91cba760c | the kit's known fail-opens: every site in the functions behind the 62 EQUAL* / same claims (207 site pairs) and the 7 other claims (42), each with the trace that names its target on both sides; 0 targets differ |
| failopen.py | 1c4ca02b446dcb3c36107f754c1fa4b1798ca2ae427dc51710392160fda48413 | the may-dataflow scan, the .got-slot traces and the hand traces that write fail-open-traces.tsv from the kit, the images and the compare outputs (--selftest: one planted function per shape) |
| g1-strcmp-grant.cmp.tsv | 152849ab0a33f130666ae3f0990ec1b9550ec5127ed12c7fd22b58427b445184 | strictcmp3 cmp: fuzz_grant.asan vs fuzz_command.asan and fuzz_command.asan-ubsan, the strcmp interceptor and its callees |
| g2-answer-settle.kitrange.tsv | f6b7bb97588b20e0498fad174b712dbd03791bc7c03e3c8d7321b39ae249baf5 | kitrange.py output for g2-answer-settle.spec.tsv |
| g2-answer-settle.spec.tsv | ffc25a45bd400a33aebcc8fccf86e54f8027ee23376182ea011e299a46d42161 | kitrange.py input: the answer entry range with and without its end word |
| g2-prog-ranges.kitrange.tsv | a23ad42f44fb681b35d17fb5a22813653908321df769d028dee34073af3f2409 | kitrange.py output for g2-prog-ranges.spec.tsv (real words listed) |
| g2-prog-ranges.spec.tsv | d4ddd8328dedd3ae9544bdd05759e7902385bdb9992a2cda02fc05ea2a470a3c | kitrange.py input: the ranges, parts and same-image pairs |
| g2-prog.cmp.tsv | 1dccee6057b50056f055a2eb72e10be69fa6e8e196451f88b6a1321170018ab6 | strictcmp3 cmp: fuzz_command.asan-ubsan vs fuzz_command.asan, the program functions of the lib/B/Prog claims |
| g2-rt.cmp.tsv | 5d25913edabf9441e7614d581164505804a7dcf7a31de6ce14699cb5d590f8a7 | strictcmp3 cmp: fuzz_command.asan-ubsan vs fuzz_command.asan, the runtime functions of the lib/B/Rt claims |
| g2-verbs-receive.kitrange.tsv | 0d2e5f1a102e2c91f663324209e66608554b247e5da4430a27377cc4cefe510a | kitrange.py output for g2-verbs-receive.spec.tsv |
| g2-verbs-receive.spec.tsv | a63c5272ee1b7f5dea3637aad8fd81647f395c7e4495c774a62931d3521aeaff | kitrange.py input: the verbs_receive prologue and side-stack call |
| g3-sm3-disco.cmp.tsv | a28430146b107417f3dc2fe2f1598d8e30d4961c0ee6f57d557baeff17ade3a6 | strictcmp3 cmp: fuzz_disco.asan vs fuzz_command.asan, __asan_stack_malloc_3 and its walked callees |
| g4-cgif.cmp.tsv | 6a57b2c539bfa43c323adbca4f68f8c6eb78bd42f17064ad9ae672260431fabe | strictcmp3 cmp: cgif_file_fuzzer asan / asan-ubsan vs fuzz_command, the memcpy / memset closures |
| g5-printf-common.cmp.tsv | 00ff009d0b5276ad1935012a296d1d51f7c9d8d29439aa2a8ffe8035a3d1ed6a | strictcmp3 cmp: fuzz_reply vs fuzz_command, printf_common |
| g9-memchr.cmp.tsv | a559eff62dc366a0f83f3cb94956c55627b1d1849203906997d64c52e269476a | strictcmp3 cmp: fuzz_command.asan-ubsan vs fuzz_command.asan, musl memchr and its constants |
| images.tsv | 5da52ab4756735400d69fd00f329c61cae58f18f550dc67c4d95333604e05de0 | the eight images: the pinned image sha256 and its unstripped twin sha256 |
| kitrange.py | 3d9c07e8cd0c354a4787c0b7b12b97d99b71b211c4adad93b1e36fe7f73b9491 | the by-address driver of the kit's own compare (strictcmp3.tcmp / strictcmp3.verdict) |
| lui-checks.tsv | a1ad9302bf190d1e68cc3beb1834974288fdd2ca59f42dc28520dc687b7b3d41 | every lui word of the compared functions, its uses and the hand check (the lui fail-open limit does not apply) |
| lui-pairs-sides.tsv | f9f50431211f1db7c665f75c24662cfba6fb6eeb2241c48c272a8e4c385efe38 | per compared pair, the base sites of each side and whether the two sides agree (82 pairs, all equal) |
| lui-pairs.tsv | 19173b1d0864d1cdc6083e475a69666300897e9b0bd7a7bdebc7b2e0459488db | the kit's combined-lui fail-open: every load / store / jalr / AMO base of the compared functions that carries a lui value, with its chain and the hand check (0 bases carry two or more) |
| luipairs.py | 9534aad7d923121a6ec70cfd49ac378237419e09b91d91eb1fa95fd9a3e3a921 | the may-dataflow driver that writes lui-pairs.tsv and lui-pairs-sides.tsv from the kit, the images and the compare outputs |
| luiscan-cgif_file_fuzzer.asan-ubsan.tsv | 22d1a2855298a9fb4bb442ce317de94216703c0e707edc17564d493064234380 | luiscan --all --fns for cgif_file_fuzzer.asan-ubsan: exposure 0 in every compared function |
| luiscan-cgif_file_fuzzer.asan.tsv | ba66989741a9bc39bb800bc6ec1bc65b0aa1d4314041272f2be7cf7a171468a4 | luiscan --all --fns for cgif_file_fuzzer.asan: exposure 0 in every compared function |
| luiscan-fuzz_command.asan-ubsan.tsv | a92b1272f3ecd3d51c139e3067b5b09b97b8f877fefc03051baaa6b7ebfe64c4 | luiscan --all --fns for fuzz_command.asan-ubsan: exposure 0 in every compared function |
| luiscan-fuzz_command.asan.tsv | 196562f25050d0fa5411891e438951bf57cff7eb1b145f629ae5ac67415a7cab | luiscan --all --fns for fuzz_command.asan: exposure 0 in every compared function |
| luiscan-fuzz_disco.asan.tsv | b7e47a49132bb240dd598b52168b1962069db45579c18129400e0bd59eecab1d | luiscan --all --fns for fuzz_disco.asan: exposure 0 in every compared function |
| luiscan-fuzz_grant.asan.tsv | c318f64b3c607e1a00f041fecdb8c1fe21d7f0303aa177e4727f646bc8c44372 | luiscan --all --fns for fuzz_grant.asan: exposure 0 in every compared function |
| luiscan-fuzz_reply.asan-ubsan.tsv | 73274affe19512abbb4d75a29520025c21df44169737eacde1a9ca3ff87d8b25 | luiscan --all --fns for fuzz_reply.asan-ubsan: exposure 0 in every compared function |
| luiscan-fuzz_reply.asan.tsv | 1417d250804e58c9e6660902c1df7eac1afd5dfcf820cc527ad798eb08e80329 | luiscan --all --fns for fuzz_reply.asan: exposure 0 in every compared function |
| measured-rows.tsv | 556cff0dc54f72572b002f7f1a3125e413d7ac662ff3a12c4c3f1c16a513ca9f | the 57 citation changes for measured-rows (lines at the series base): 52 for the class-F claims, 5 for the not-certified claims |
| names.tsv | 3965a645a88e1e52ab2491bd87e8dffd891b815980bc7105c3264ceadf0fbf5a | per image, the copies of each compared function name (only MemToShadow has several; compared by its file) |
| send_message-byuse.tsv | 11fa7ffb4b26dfe14dabe46dea96ea5a2d5dc3ab4dda7eaa1a262c6f1f45d7e5 | every address literal and entry offset in lib/B/Prog/send_message*.v (none after 0x86e48 outside the comment that names the unimp) |
| settled.tsv | 033370ae9f0a4af11fa214d532aef08d2e8e0ae08a2211f6cf7f9e5bdcf63927 | the settled rows S1 to S8, each beside the kit verdict, with the measurement that settles it |
| twins.out | 43f40fea483edd346dd6de7d112455734dea001004e7800d687c411ae32fb098 | drvcmp.py twins output for the eight pin / twin pairs |
