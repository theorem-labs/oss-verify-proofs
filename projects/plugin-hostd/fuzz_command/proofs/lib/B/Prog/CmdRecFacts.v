(* The per-binary facts of fuzz_command.asan-ubsan that the program contracts and their walks use (the B twin of
   lib/A/Prog/CmdRecFacts.v), from the allocator record (CmdBSyms, lib/B/YF0m.v) and the
   image's segments. One import for the walks; the
   facts are in small files so that each compiles on its own:
   - CmdRecBase: the definitions, the record cmd_img_facts, and the shadow lemmas (cmd_addressable_chk,
     cmd_hull_vis_chk, cmd_aread_ok_chk, cmd_word_chk, cmd_stk_above);
   - CmdRecCells: PALib's fields over any instance, check_words_add's facts, REC_CELLS, PROG_WRITABLE;
   - CmdRecRo: M3 (cmd_ro_ok_of_aro), CMD_RO_IN, the relro range (relro_img, RELRO_IMG, RRO), RPG, string tails;
   - CmdRecImg (+ CmdRecImgChk): cmd_heap_tail_vis, cmd_prog_unowned, cmd_rom_view_on, cmd_img_facts_tfib;
   - CmdRecCover: the image's shadow coverage, cmd_ro_rd, cmd_ro_hull_vis, cmd_ro_addr_kept;
   - CmdRecRest: cmd_aread_ok_img, cmd_ro_prog_apart, cmd_prog_img, cmd_ro_kept, cmd_atail_kept, cmd_rodata_kept,
     val_mem_of_aval, cmd_palib and CmdObj.v's bridges for PB_cmd. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Export
CmdChk CmdRecBase CmdRecCells CmdRecRo CmdRecImgChk CmdRecImg CmdRecCover CmdRecRest.
