(* reac-pw/fuzz_segconf, image B: the allocator events of one call of LLVMFuzzerTestOneInput are at most 16, the
   bound the close's bridge (lib/B/Prog/SegLibX.v) needs against the program interface's EV_LIB (the role of
   plugin-hostd/fuzz_command's lib/A/Prog/HarnessArgsEv.v, origin/ossv/recipes 501c0d516c69).

   EV_LTOI pl = 8 + 2 * seg_spec.seg_nfiles pl (lib/B/Prog/LLVMFuzzerTestOneInput_c.v): malloc(c), calloc(m),
   calloc(tab), calloc(mt) and the four frees, and a malloc / free pair per file turn. The payload decodes to 1 + b2 mod 4
   files (the plain build's walk lemma Prog/Seg/L03.v l03_nfiles: 1 <= seg_nfiles inp <= 4), so EV_LTOI pl <= 16.
   proves no function (kind: arithmetic bound over the contract's event count). *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require L03.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require LLVMFuzzerTestOneInput_c.
Local Open Scope Z_scope.

Definition EV_LTOI_MAX : Z := 16.

Lemma ev_ltoi_max : forall pl, LLVMFuzzerTestOneInput_c.EV_LTOI pl <= EV_LTOI_MAX.
Proof.
intros pl. unfold LLVMFuzzerTestOneInput_c.EV_LTOI, EV_LTOI_MAX. pose proof (L03.l03_nfiles pl) as H. lia.
Qed.

Print Assumptions ev_ltoi_max.
