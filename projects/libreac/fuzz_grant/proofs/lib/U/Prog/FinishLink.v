From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import RcModel RcFin.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import ctrl_finish_c GrantSweepModel RgLemmas RgNeeds_c.
Import ListNotations.
Open Scope Z_scope.

Lemma fin_eq : forall blk, length blk = 32%nat -> fin 2 16 6 blk = finish_bytes blk.
Proof.
  intros blk Hl.
  do 32 (destruct blk as [|? blk]; [discriminate|]).
  destruct blk; [|discriminate]. clear Hl.
  unfold fin, finish_bytes, finish_z, stamp32, rstamp, rsum, zsum, upd_bytes, bl.
  try change (Z.to_nat (16 + 6 - 1)) with 21%nat.
  try change (Z.to_nat 16) with 16%nat.
  try change (Z.to_nat (6 - 1)) with 5%nat.
  cbn -[Z_to_bv bv_unsigned Z.modulo].
  repeat match goal with |- cons _ _ = cons _ _ => apply f_equal2 end.
  all: try reflexivity.
  all: try (symmetry; apply stdpp.bitvector.definitions.Z_to_bv_bv_unsigned).
  all: match goal with |- Z_to_bv _ _ = Z_to_bv _ _ => apply (f_equal (Z_to_bv 8)) end.
  all: rewrite ?Z_to_bv_unsigned; try unfold bv_wrap; try change (bv_modulus 8) with 256.
  all: Z.div_mod_to_equations; lia.
Qed.

Theorem ctrl_finish_link : ctrl_finish_contract -> ctrl_finish_need.
Proof.
  intros FC. unfold ctrl_finish_need, CTRL_FINISH_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m f lo blk -> -> Hf Hf50 HRW HMI ST LO HD HROW HROWD HRD.
  pose proof (proj1 (proj1 HRW)) as Hwf. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hlen _].
  destruct (stk_split rsegs m lo (bv_unsigned sp - 16) (bv_unsigned sp) ST ltac:(lia)) as [STlo ST16].
  eapply evt_mono.
  { apply (FC ra sp gp tp t0 t1 t2 s0 s1 _ _ a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             f CTRL_ROW 2 16 6 CTRL_ROW_BYTES blk).
    - reflexivity.
    - reflexivity.
    - exact ST16.
    - lia.
    - lia.
    - reflexivity.
    - unfold CTRL_ROW. lia.
    - reflexivity.
    - exact HROW.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - intros _. lia.
    - exact Hf.
    - exact Hf50.
    - intros _. exact HRW. }
  intros ms' (a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & -> & MU & WM & MI & ST' & HB).
  destruct (HB (or_intror eq_refl)) as (HR' & _ & _).
  change (fin_w 2 16 6 f) with [(f + 18 + 16 + 6 - 1, f + 18 + 16 + 6); (f + 49, f + 50)] in MU.
  exists t0, t1, t2, a0', a1', a2', a3', a4', a5', a6', a7', t3, t4, t5, t6, m'.
  split; [reflexivity|].
  split.
  { eapply munch_weaken; [|exact MU].
    intros x [Hx1 [Hx2 _]]. split; [exact Hx1|]. split; [intro; lia|]. split; [intro; lia|]. exact I. }
  split; [exact WM|].
  split; [exact (MI HMI)|].
  split.
  { apply (stk_merge rsegs m' lo (bv_unsigned sp - 16) (bv_unsigned sp)); [|exact ST'|lia].
    apply (stk_transport_disjoint rsegs _ m m' lo (bv_unsigned sp - 16) STlo MU WM).
    cbn [disjoint_from]. repeat split; lia. }
  split; [eapply row_keep; [exact HROW | exact MU | cbn [disjoint_from]; repeat split; lia]|].
  rewrite <- (fin_eq blk Hlen). exact HR'.
Qed.
