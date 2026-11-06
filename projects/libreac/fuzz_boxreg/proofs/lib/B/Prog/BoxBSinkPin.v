(* The pin of the ASan+UBSan sink head (walks/PLAN.md 0.6, item 5): lib/B/Prog/BoxBClose.v's boxb_sink_head has
   sk_ofl_head = 0x5f4a48. boxb_RO does not catch a wrong head on B (B's read-only range ends at 0x9a000, below the
   ASan build's head 0x5f4608 as well), so this equality is the check that the B closing uses B's own head.
   Measured on the ORIGINAL unstripped image (image root
   the release's unstripped fuzz_boxreg.asan-ubsan, sha256
   1d548458eac37ae17f9e8dfb06a5dfef3c606ec9e03eca8ef291d5fec9dce495), pyelftools 0.33 + capstone 5.0.7:
   - .symtab: `ofl_head` = 0x5f4a48 (8 bytes, STT_OBJECT, STB_LOCAL, .bss [0x9dd00, 0x5f5c30)); `ofl_lock` = 0x5f4a40;
     `__ofl_lock` = 0x8ec68 (48 bytes, .text).
   - __ofl_lock's code: 0x8ec74 auipc a0,0x566; 0x8ec78 addi s0,a0,-0x234 (s0 = 0x5f4a40 = &ofl_lock); 0x8ec84 addi
     a0,s0,8 (a0 = 0x5f4a48 = &ofl_head, the return value).
   - The image the proofs load (projects/libreac/bin/fuzz_boxreg/fuzz_boxreg.asan-ubsan, sha256 7620eb05...0d85) has
     the same four PT_LOADs; .text is byte-identical.
   The ASan build's head is 0x5f4608 (lib/A/Prog/BoxClose.v BOX_OFL_HEAD) and the plain build's is 0x4ed20
   (Reusable/YH03.v src0_D_ofl_head); this lemma holds for neither. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YI16.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require BoxBClose.
Local Open Scope Z_scope.
Lemma boxb_sink_head_val : @YI16.sk_ofl_head BoxBClose.boxb_sink_head = 0x5f4a48.
Proof. reflexivity. Qed.
