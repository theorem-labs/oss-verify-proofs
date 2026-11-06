(* The pin of the ASan sink head, beside lib/B/Prog/BoxBSinkPin.v: lib/A/Prog/BoxClose.v's box_sink_head has
   sk_ofl_head = 0x5f4608, fuzz_boxreg.asan's own `ofl_head`.
   Measured on the ORIGINAL images (the release's libreac bin/fuzz_boxreg/
   fuzz_boxreg.asan, sha256 eacfa205..., ET_EXEC, no PT_DYNAMIC; symbols from the unstripped twin's nm):
   - `ofl_head` = 0x5f4608 (8 bytes, .bss [0x9d8c0, 0x5f57f0) of the original); `ofl_lock` = 0x5f4600.
   - Every non-writable PT_LOAD ([0x10000, 0x2ef58), [0x2ff58, 0x9791c)) and the read-only range of PI_box
     ([0x98958, 0x99bb0)) end below it (BoxClose.v box_RO).
   The ASan+UBSan build's head is 0x5f4a48 (BoxBSinkPin.v) and the plain build's is 0x4ed20 (Reusable/YH03.v
   src0_D_ofl_head); this lemma holds for neither. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YI16.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require BoxClose.
Local Open Scope Z_scope.
Lemma box_sink_head_val : @YI16.sk_ofl_head BoxClose.box_sink_head = 0x5f4608.
Proof. reflexivity. Qed.
