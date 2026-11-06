(* reac-pw/fuzz_link, PLAIN build: the heap arms of printf_core's location premises hold at link's FILE.

   lib/CJ/RL/GX/G_printf_core_common.v `printf_core_stmt` lets the FILE (Fp, 232 bytes) and its buffer
   (B, BS bytes) lie on the heap: below printf_core's frame (`+ 232 <= lo`, `B + BS <= lo`) and outside the
   image (wholly below 65536, with the format string at or above 65536, or at or above GLOBALS_TOP).
   This lemma takes those two premises, word for word as printf_core_stmt states them (A is the format
   string's address, `bv_unsigned a1` there; AP and VA are free: the heap arm does not use them), and shows
   them at link's memory FILE (lib/MemFile.v, lib/Prog/memfile_c.v): Fp = f, B = f + MF_BUF (280),
   BS = MF_BUFSIZ (1024), on link's plain image N_img (GLOBALS_TOP = sym 0x35000 = 0x97000), when the
   1304-byte block lies outside the image (`mf_place_ok f`, part of `memfile_k`) and below the frame,
   and the format string is in .rodata (RO_LO = 0x10000 <= A). *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.I Require IImgP.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX Require G_printf_core_common.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require memfile_c.
Local Open Scope Z_scope.

#[local] Existing Instance IImgP.N_img.

Module PI := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.

Lemma printf_core_heap_arm_ok : forall (f A AP VA lo : Z),
  0 < f -> memfile_c.RO_LO <= A -> memfile_c.mf_place_ok f -> f + MemFile.MF_BLOCK <= lo ->
  let Fp := f in let B := f + MemFile.MF_BUF in let BS := MemFile.MF_BUFSIZ in
  (((sym 0x22e18 + 8) <= Fp /\ Fp + 232 <= (sym 0x34288)) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA)
     \/ (0 < Fp /\ Fp + 232 <= lo /\ ((Fp + 232 <= 65536 /\ 65536 <= A) \/ PI.GLOBALS_TOP <= Fp)))
  /\ ((AP + 8 <= B /\ B + BS <= VA) \/ (0 < B /\ B + BS <= lo /\ ((B + BS <= 65536 /\ 65536 <= A) \/ PI.GLOBALS_TOP <= B))).
Proof.
  intros f A AP VA lo H0 HA HP HL. cbv zeta.
  assert (T : PI.GLOBALS_TOP = 0x97000) by (vm_compute; reflexivity).
  rewrite T.
  unfold memfile_c.mf_place_ok, memfile_c.IMG_LO, memfile_c.IMG_TOP, memfile_c.RO_LO,
         MemFile.MF_BLOCK, MemFile.MF_BUF, MemFile.MF_BUFSIZ in *.
  split; [right; right | right]; lia.
Qed.
