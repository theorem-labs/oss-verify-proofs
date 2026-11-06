From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import put_utf8_c parse_string_loops.
Import ListNotations.
Open Scope Z_scope.

Lemma ps_putback : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o cp p st en : Z),
  put_utf8_contract ->
  s2 = Z_to_bv 64 o -> a1 = Z_to_bv 64 cp -> s9 = Z_to_bv 64 p -> s0 = Z_to_bv 64 st ->
  o <> 0 -> 0 < cp <= 0x10FFFF -> wr_at rsegs m o (Z.of_nat (length (utf8 cp))) ->
  o + Z.of_nat (length (utf8 cp)) < 2 ^ 64 ->
  bytes_at rsegs m (st + 8) (le8 (Z_to_bv 64 en)) ->
  (o + Z.of_nat (length (utf8 cp)) <= st + 8 \/ st + 16 <= o) ->
  0 <= p < 2 ^ 64 -> 0 <= en < 2 ^ 64 ->
  evt rsegs
    (fun ms' => exists (ra' t0' t1' t2' a1' a2' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 en) a1' a2' (Z_to_bv 64 91) (Z_to_bv 64 114) a5' a6' a7'
                     (Z_to_bv 64 (o + Z.of_nat (length (utf8 cp)))) (Z_to_bv 64 p) s4 s5 s6 s7 s8 (Z_to_bv 64 p) s10 s11
                     t3' t4' t5' t6')
                F (if p <? en then Z_to_bv 64 0x170e4 else Z_to_bv 64 0x1718c) fc None m' (seg_rom rsegs) /\
       bytes_at rsegs m' o (utf8 cp) /\
       bytes_at rsegs m' (st + 8) (le8 (Z_to_bv 64 en)) /\
       munch [(o, o + Z.of_nat (length (utf8 cp)))] m m' /\
       wmono rsegs m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x172b4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m o cp p st en
    PU E2 E1 E9 E0 HO Hcp HW HOn HE HD HP HN.
  subst s2 a1 s9 s0.
  pose proof (bytes_at_bound rsegs m (st + 8) _ HE) as HB. rewrite length_le8 in HB.
  pose proof HW as (Ho0 & _).
  step. step.
  eapply evt_cut.
  { eapply PU; [reflexivity | reflexivity | exact HO | exact HW | exact Hcp]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & HU & MU & WM).
  replace (ret_pc (Z_to_bv 64 0x172bc)) with (Z_to_bv 64 0x172bc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (HE' : bytes_at rsegs m' (st + 8) (le8 (Z_to_bv 64 en))).
  { apply (bytes_at_transport rsegs _ m m' (st + 8) _ HE MU). cbn [disjoint_from]. rewrite length_le8. split; [lia | exact I]. }
  assert (RD : ov_read_bytes rsegs m' (wa (st + 8)) 8 = Some (le8 (Z_to_bv 64 en))).
  { replace (wa (st + 8)) with (wa (st + 8 + 0)) by (f_equal; lia).
    rewrite (bytes_at_read rsegs m' (st + 8) _ 0 8 HE') by (rewrite ?length_le8; lia). reflexivity. }
  pose proof (Nat2Z.is_nonneg (length (utf8 cp))) as Hn0.
  step. step. step. step.
  rewrite (unsigned_lit o), psl_not by lia.
  rewrite (psl_ltu (2 ^ 64 - 1 - o)) by lia.
  rewrite (proj2 (Z.ltb_ge (2 ^ 64 - 1 - o) (Z.of_nat (length (utf8 cp))))) by lia. cbv iota.
  step. step. step. step. step.
  rewrite (psl_ltu p en) by lia.
  apply evt_done. cbv beta. do 13 eexists. exists m'.
  split; [destruct (p <? en); reflexivity|]. split; [exact HU|]. split; [exact HE'|]. split; [exact MU | exact WM].
Qed.
