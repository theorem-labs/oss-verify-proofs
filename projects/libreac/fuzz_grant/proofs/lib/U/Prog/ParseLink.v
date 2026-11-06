From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import RcParse.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel GrantSweepModel GroupaModel
  reac_ctrl_parse_c GroupaNeeds_c.
Import ListNotations.
Open Scope Z_scope.

Lemma parse_F50 : forall ch p v,
  fst (ctrlparse 50 (F50 ch p v)) = 6 /\
  snd (ctrlparse 50 (F50 ch p v)) =
    firstn 30 (snd (ctrlparse 50 (F50 ch p v))) ++ [Z_to_bv 8 ch; Z_to_bv 8 p; Z_to_bv 8 v] ++
    skipn 33 (snd (ctrlparse 50 (F50 ch p v))).
Proof.
  intros ch p v. split; [reflexivity|].
  set (X := snd (ctrlparse 50 (F50 ch p v))).
  assert (E : firstn 3 (skipn 30 X) = [Z_to_bv 8 ch; Z_to_bv 8 p; Z_to_bv 8 v]) by reflexivity.
  rewrite <- E.
  rewrite <- (firstn_skipn 30 X) at 1. f_equal.
Qed.

Lemma rw_cells_cb36 : forall segs m A b1 x y z b2, length b1 = 30%nat -> length b2 = 3%nat ->
  rw_cells segs m A [CB 36 (b1 ++ [x; y; z] ++ b2)] ->
  rw_cells segs m A [CB 30 b1; C1 x; C1 y; C1 z; CB 3 b2].
Proof.
  intros segs m A b1 x y z b2 L1 L2 [[_ Hb] Hw]. unfold rw_cells, cells_at.
  cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize] in *. rewrite app_nil_r in Hb.
  split; [split|].
  - repeat split; assumption.
  - rewrite app_nil_r. cbn [app] in Hb |- *. exact Hb.
  - exact Hw.
Qed.

Theorem parse_link : reac_ctrl_parse_contract -> reac_ctrl_parse_need.
Proof.
  intros PC.
  unfold reac_ctrl_parse_contract, reac_ctrl_parse_c.REAC_CTRL_PARSE, REAC_CTRL_PARSE_K in PC.
  unfold reac_ctrl_parse_need, GroupaNeeds_c.REAC_CTRL_PARSE, REAC_CTRL_PARSE_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m f o lo ch p v junk -> -> -> SP16 Hf Hf50 Ho Ho4 Ho36 HCH HP HV HB HO DOF DF DO ST LO HMI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with 18446744073709551616 in Rsp.
  change (2 ^ 64) with 18446744073709551616 in Hf50, Ho36.
  pose proof ST as (Hlo0 & _ & _).
  destruct (stk_split rsegs m lo (bv_unsigned sp - 80) (bv_unsigned sp) ST ltac:(lia)) as [STL STH].
  pose proof (length_F50 ch p v) as HL.
  destruct (parse_F50 ch p v) as [K6 BS].
  eapply evt_mono; [ eapply PC with (S := bv_unsigned sp) (n := 50) (fr := F50 ch p v) (junk := junk);
    [ reflexivity | reflexivity | reflexivity | symmetry; apply Z_to_bv_lit_self
    | lia | lia | lia | lia | exact SP16 | lia | exact STH | exact HMI | exact HL
    | intros _; split; [lia | split; [lia | exact DF]]
    | intros i Hi; pose proof (cp_rd_lt39 50 (F50 ch p v) i Hi) as Hi39;
      destruct HB as (_ & _ & HB); apply HB; rewrite HL; lia
    | intros _; split; [exact Ho4 | split; [lia | split; [exact HO | split; [right; exact DO | intros _; exact DOF]]]] ] | ].
  intros ms' (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m' & -> & MU & WM & MI & STH' & RO).
  specialize (RO ltac:(lia)). rewrite BS in RO.
  apply rw_cells_cb36 in RO; [| rewrite length_firstn, ctrlparse_length; reflexivity
                             | rewrite length_skipn, ctrlparse_length; reflexivity].
  unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K in MU. rewrite (proj2 (Z.eqb_neq o 0)) in MU by lia. cbn [app] in MU.
  exists x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, m',
    (firstn 30 (snd (ctrlparse 50 (F50 ch p v)))), (skipn 33 (snd (ctrlparse 50 (F50 ch p v)))).
  rewrite K6. split; [reflexivity|].
  split.
  { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros x (H1 & H2 & _). repeat split; assumption. }
  split; [exact WM|]. split; [exact MI|]. split; [|exact RO].
  eapply stk_merge; [| exact STH' | lia].
  eapply stk_transport_disjoint; [exact STL | exact MU | exact WM |].
  cbn [disjoint_from]. repeat split; try exact I; lia.
Qed.
