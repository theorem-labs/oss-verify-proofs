(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module names changed; 85 of its 151 lines of code are new or changed and 3787 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match_lib.v, with its module paths and module names changed; 717 of its 758 lines of code are new or changed and 110 lines of the source are left out. *)
(* Segment F31 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): the range 0x82798-0x827d4 (the classify branch,
   three not-taken instrumented checks and the bcmp wrapper call at 0x827d4).  rule 24: no function proved.
   v1.9 STATUS (2026-10-28): UNVERIFIED.  No build without probes has checked this file on v1.9.0.  It closed only
   in an ITERATION-ONLY build on the v1.9 bytes (FACTS 0bfe9aa0d452) with probes in Seg/Tac_slot.v and
   Seg/Tac_fsfree.v.  It waits for Seg/Tac_slot.v / Tac_fsfree.v re-fit to the regenerated Contract.v and FrameAPI.v.

   Entry Inv_A82798_at (SlotInv.v), exits Inv_A827d8_at (the bcmp wrapper returned) and Inv_A82800_at (the target of
   `bnez a0` at 0x82798).  The three cuts carry FLSI /\ LK /\ FLS /\ LT; this file defines no cut and no bundle.
     classify = None  (a0 = -1): `bnez a0` is taken to 0x82800; no memory changes (f31n_evt).
     classify = Some e (a0 = 0): the source field of the classify output is 00 40 ab c9 c10 c11, so the three byte
       checks fall through, and the bcmp wrapper compares those 6 bytes with our[] (f31c_evt).  The wrapper asks
       mem_inv; FRA carries ro_agree only, so the run is made on the normalized memory (f31c_norm,
       MemNorm.evt_normalize).  It writes only its stack window W = [sp - 4560, sp): FRA moves by
       Tac_b5.sl_callee_keep, ENT by Tac_slot.ent_store / ent_mat, and FLSI / LK / FLS / LT by f31_keep (the spill
       area, the frame, the turn's block and the harness block are all apart from W; W is app memory, so every
       addressable range stays addressable). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI RoAdapt BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse RcClassify RcClassifyLib RcIdentModel RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require memcmp_c bcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5.
Import ListNotations.
(* The plain lib/Prog files also load lib/Reusable/YK11, so the short name YK11 may name the plain one; the slot's
   cuts are stated with the image-A one, which this alias names. *)
Module AYK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Import AYK.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module BW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_c.
Module SF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec.StrFun.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module RP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcParse.
Module RC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcClassify.
Module RCL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcClassifyLib.
Module RIM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.
Module RF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFrag.

(* The bcmp wrapper's and memcmp's constants, the v1.9.0 values of Prog/bcmp_wrap_c.v and Prog/memcmp_c.v
   (a Theorem Labs lane 3eade53eef2). *)
Local Definition BCMP_WRAP_K := 4560.
Local Definition BCMP := 0x97b0c.
Local Definition REAL_BCMP := 0xa17f0.
Local Definition REAL_MEMCMP := 0xa17e8.
Local Definition GOT_CF := 0x9fac0.
Local Definition CF := 0x13a3a8.
Local Definition MEMCMP := 0x97bdc.
Local Notation memcmp_model := SF.memcmp_model.

(* ---- Model facts: the classify result (C1.8 of the classify contract's model). *)
Lemma f31_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. exact H.
Qed.

Lemma f31_cls_r : forall c, RC.cl_r c = 0 \/ RC.cl_r c = -1.
Proof. intros [e|]; [left | right]; reflexivity. Qed.

Lemma f31_cls_some : forall c, RC.cl_r c = 0 -> exists e, c = Some e.
Proof. intros [e|] H; [exists e; reflexivity | unfold RC.cl_r in H; discriminate H]. Qed.

Lemma f31_cls_B : forall inp j e, t_cls inp j = Some e -> t_B inp j = RP.cp_struct (t_g inp j) (t_k inp j).
Proof.
  intros inp j e H. unfold t_cls in H.
  destruct (RCL.classify_some _ _ _ _ H) as (K & _).
  destruct (RCL.cl_hdr _ _ K) as [_ HB]. exact HB.
Qed.

Lemma f31_cls_oui : forall inp j e, t_cls inp j = Some e ->
  RP.cp_v (t_g inp j) 6 = 0 /\ RP.cp_v (t_g inp j) 7 = 64 /\ RP.cp_v (t_g inp j) 8 = 171.
Proof.
  intros inp j e H. unfold t_cls in H.
  destruct (RCL.classify_some _ _ _ _ H) as (_ & _ & OUI & _).
  unfold RC.cl_oui in OUI. apply andb_prop in OUI as [OUI O8]. apply andb_prop in OUI as [O6 O7].
  apply Z.eqb_eq in O6, O7, O8. split; [exact O6|]. split; [exact O7 | exact O8].
Qed.

Lemma f31_cp_b : forall fr i v, RP.cp_v fr i = v -> 0 <= v < 256 -> RP.cp_b fr i = Z_to_bv 8 v.
Proof.
  intros fr i v E Hv. apply bv_eq. unfold RP.cp_v in E. rewrite E. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small; lia.
Qed.

Lemma f31_struct_src : forall fr k,
  firstn 6 (skipn 4 (RP.cp_struct fr k)) =
  [RP.cp_b fr 6; RP.cp_b fr 7; RP.cp_b fr 8; RP.cp_b fr 9; RP.cp_b fr 10; RP.cp_b fr 11].
Proof. intros fr k. unfold RP.cp_struct. destruct (RP.cp_rec fr), (k =? 6); reflexivity. Qed.

(* classify = Some e: the source field of the classify output (bytes 4..9 of t_B) begins 00 40 ab. *)
Lemma f31_B_src : forall inp j e, t_cls inp j = Some e ->
  firstn 6 (skipn 4 (t_B inp j)) =
  [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; RP.cp_b (t_g inp j) 9; RP.cp_b (t_g inp j) 10; RP.cp_b (t_g inp j) 11].
Proof.
  intros inp j e H. rewrite (f31_cls_B inp j e H), f31_struct_src.
  destruct (f31_cls_oui inp j e H) as (O6 & O7 & O8).
  rewrite (f31_cp_b _ 6 0 O6), (f31_cp_b _ 7 64 O7), (f31_cp_b _ 8 171 O8) by lia. reflexivity.
Qed.

Lemma f31_B_length : forall inp j, length (t_B inp j) = 36%nat.
Proof. intros inp j. apply RP.ctrlparse_length. Qed.

Lemma f31_mm_spec : forall n l r v, length l = n -> length r = n -> memcmp_model l r n = Some v ->
  (v = 0 <-> l = r) /\ -256 < v < 256.
Proof.
  induction n as [|n IH]; intros l r v Hl Hr H.
  - destruct l; [|discriminate]. destruct r; [|discriminate]. cbn in H. inversion H. split; [tauto|lia].
  - destruct l as [|a l]; [discriminate|]. destruct r as [|b r]; [discriminate|]. cbn in Hl, Hr, H.
    pose proof (f31_byte_range a) as Ra. pose proof (f31_byte_range b) as Rb.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
    + destruct (IH l r v ltac:(lia) ltac:(lia) H) as [I1 I2]. split; [|exact I2].
      apply bv_eq in E. subst b. split.
      * intros Hv. f_equal. apply I1. exact Hv.
      * intros Hq. apply I1. injection Hq as Hq. exact Hq.
    + inversion H; subst v. split; [|lia]. split; [lia|]. intros Hq. injection Hq as Hab _. subst b. contradiction.
Qed.

Lemma f31_lit0 : forall v, -256 < v < 256 -> (Z_to_bv 64 v = Z_to_bv 64 0 <-> v = 0).
Proof.
  intros v Hv. split; intros E; [|subst; reflexivity].
  apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit_wrap in E. change (0 mod 2 ^ 64) with 0 in E.
  Z.div_mod_to_equations. lia.
Qed.

Lemma f31_ba_sub : forall m A bs k jj, bytes_at rsegs m A bs -> (k + jj <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn jj (skipn k bs)).
Proof.
  intros m A bs k jj (HA & HL & H) Hkj.
  assert (Lf : length (firstn jj (skipn k bs)) = jj) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite Lf; lia|].
  intros i Hi. rewrite Lf in Hi.
  replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia.
  rewrite H by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i jj) as [_|C]; [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

(* A spilled word at s1 + off read at the FRA spill base A (the existential base of `spill` is A). *)
Lemma f31_spill : forall regs m off v A, spill regs m off v -> rg regs 9 A ->
  0 <= A -> A + 416 <= 2 ^ 64 -> 0 <= off <= 400 -> q64 m (A + off) v.
Proof.
  intros regs m off v A (A' & HA' & Hq) HA H0 H1 Hoff.
  unfold rg in HA, HA'. rewrite HA in HA'.
  pose proof Hq as (Hq0 & Hq1 & _). rewrite length_le8 in Hq1.
  assert (E : A' = A).
  { apply (f_equal bv_unsigned) in HA'. rewrite !unsigned_lit_wrap in HA'.
    rewrite (Z.mod_small A) in HA' by lia. Z.div_mod_to_equations. lia. }
  subst A'. exact Hq.
Qed.

(* ---- The sizes of the frame records of LT = IFS g fr (S j): the identity record is ID_SIZE = 38 bytes (ING keeps
   it) and the fragment state 72 bytes (fg_first / fg_join / fg_clear keep it under fg_fr's 1 <= n <= 22 and
   fg_keep's T <= 64), so both lie in [fr + 2688, fr + 2840).  (a Theorem Labs lane's F36 f36_tID_len / f36_tFG_len.) *)
Lemma f31_tID_len : forall inp j, length (t_ID inp j) = RIM.ID_SIZE.
Proof.
  intros inp j. unfold t_ID. induction j as [|j IH].
  - cbn [fst_at fs0 fs_id]. unfold RIM.ID0. apply repeat_length.
  - rewrite fst_at_S. set (s := fst_at inp j) in *.
    assert (E : fs_id (turn s (t_len inp j) (t_g inp j)) =
                fg_id (rp_id (fs_id s) (t_len inp j) (t_g inp j)) (t_len inp j) (fs_fg s) (t_g inp j))
      by (unfold turn; destruct (f_opens (t_len inp j) (t_g inp j)); reflexivity).
    rewrite E.
    assert (E1 : length (rp_id (fs_id s) (t_len inp j) (t_g inp j)) = RIM.ID_SIZE).
    { unfold rp_id. match goal with |- context [if ?b then _ else _] => destruct b end;
        [apply RIM.ING_length; exact IH | exact IH]. }
    unfold fg_id. match goal with |- context [if ?b then _ else _] => destruct b end;
      [apply RIM.ING_length; exact E1 | exact E1].
Qed.

Lemma f31_fg_st_len : forall len st g, length st = 72%nat -> length g = 50%nat ->
  length (fg_st len st g) = 72%nat.
Proof.
  intros len st g Hs Hg.
  assert (Hlf : 0 <= RF.fg_lf st).
  { unfold RF.fg_lf, RF.bat. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat 7) st (Z_to_bv 8 0))) as R. lia. }
  assert (Hnn : forall len', RF.fg_fr len' g = true -> 1 <= RF.fg_n g <= 22).
  { intros len' Ef. unfold RF.fg_fr in Ef. apply andb_prop in Ef as [Ef _]. apply andb_prop in Ef as [Ef E2].
    apply andb_prop in Ef as [_ E1]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia. }
  assert (HJ : 1 <= RF.fg_n g <= 22 -> RF.fg_T st g <= 64 -> length (RF.fg_join st g) = 72%nat).
  { intros Hn HT. unfold RF.fg_T in HT. unfold RF.fg_join, RF.fg_body, RF.bsl.
    rewrite !length_app, !length_firstn, !length_skipn. rewrite Hs, Hg. unfold RF.fg_T. lia. }
  assert (HC : forall l, length l = 72%nat -> length (RF.fg_clear l) = 72%nat).
  { intros l Hl. unfold RF.fg_clear. rewrite !length_app, length_firstn, length_skipn. cbn [length]. lia. }
  unfold fg_st. destruct (fcls len st g) eqn:Ec; cbn [fg_next].
  - exact Hs.
  - exact Hs.
  - unfold fcls, RF.fg_class in Ec. cbn [Z.eqb orb] in Ec.
    destruct (RF.fg_fr len g) eqn:Ef; cbn [negb] in Ec; [|discriminate Ec].
    pose proof (Hnn len Ef) as Hn.
    unfold RF.fg_first, RF.fg_body, RF.bsl. rewrite !length_app, !length_firstn, !length_skipn. cbn [length].
    rewrite Hs, Hg. lia.
  - exact (HC st Hs).
  - unfold fcls, RF.fg_class in Ec. cbn [Z.eqb orb] in Ec.
    destruct (RF.fg_fr len g) eqn:Ef; cbn [negb] in Ec; [|discriminate Ec].
    destruct (RF.bat g 19 =? 1); [discriminate Ec|].
    destruct (RF.fg_keep st g) eqn:Ek; cbn [negb] in Ec; [|discriminate Ec].
    unfold RF.fg_keep in Ek. apply andb_prop in Ek as [_ E3]. apply Z.leb_le in E3.
    exact (HC _ (HJ (Hnn len Ef) E3)).
  - unfold fcls, RF.fg_class in Ec. cbn [Z.eqb orb] in Ec.
    destruct (RF.fg_fr len g) eqn:Ef; cbn [negb] in Ec; [|discriminate Ec].
    destruct (RF.bat g 19 =? 1); [discriminate Ec|].
    destruct (RF.fg_keep st g) eqn:Ek; cbn [negb] in Ec; [|discriminate Ec].
    unfold RF.fg_keep in Ek. apply andb_prop in Ek as [_ E3]. apply Z.leb_le in E3.
    exact (HC _ (HJ (Hnn len Ef) E3)).
Qed.

Lemma f31_tFG_len : forall inp j, length (t_FG inp j) = 72%nat.
Proof.
  intros inp j. unfold t_FG. induction j as [|j IH].
  - cbn [fst_at fs0 fs_fg]. exact z72_length.
  - rewrite fst_at_S. set (s := fst_at inp j) in *.
    assert (E : fs_fg (turn s (t_len inp j) (t_g inp j)) = fg_st (t_len inp j) (fs_fg s) (t_g inp j))
      by (unfold turn; destruct (f_opens (t_len inp j) (t_g inp j)); reflexivity).
    rewrite E. apply f31_fg_st_len; [exact IH | unfold t_g; apply fr50_length].
Qed.

(* v1.9 FSb: the first fragment's body is at most the 23 bytes block[9 ..] of a 50-byte record (fs0's is empty),
   so it lies in [fr + 2880, fr + 2903), inside the frame.  (F29's fs_body_len.) *)
Lemma f31_fs_body_len : forall inp j, (length (fs_body (fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - cbn [fst_at fs0 fs_body length]. lia.
  - rewrite fst_at_S. unfold turn.
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_body]; [|exact IH].
    rewrite length_firstn, length_skipn. unfold t_g. rewrite fr50_length. lia.
Qed.

(* ---- FLSI, LK, FLS and LT (SlotInv's official bundles) across a run that writes only W and keeps the registers
   they read (s1 9, s2 18, s5 21, s6 22, s7 23, s8 24, s9 25): W misses the spill area [A, A + 416), the frame
   [fr, fr + 3136), the turn's block (on the long arm, where FLS speaks of its bytes) and the harness block; every
   addressable range stays addressable (HAD). *)
Lemma f31_keep : forall g j phi fr regs regs' m m' W A,
  FLSI g j fr regs m -> LK g fr j regs m -> FLS g j phi fr regs m -> LT g fr j regs m ->
  munch W m m' -> wmono rsegs m m' ->
  (forall p n, addressable m p n -> addressable m' p n) ->
  getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 21 = getr regs 21 ->
  getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 -> getr regs' 24 = getr regs 24 ->
  getr regs' 25 = getr regs 25 ->
  rg regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 ->
  (forall x, A <= x < A + 416 -> outside W x) ->
  (forall x, fr <= x < fr + 3136 -> outside W x) ->
  (50 <= flen g j -> forall x, phi <= x < phi + flen g j -> outside W x) ->
  (0 < g_n g -> forall x, g_p g <= x < g_p g + g_n g -> outside W x) ->
  FLSI g j fr regs' m' /\ LK g fr j regs' m' /\ FLS g j phi fr regs' m' /\ LT g fr j regs' m'.
Proof.
  intros g j phi fr regs regs' m m' W A HI HLK HS HLT MU WM HAD E9 E18 E21 E22 E23 E24 E25 Hr9 HA0 HA1
    HWA HWF HWB HWP.
  assert (SP : forall off v, 0 <= off <= 400 -> spill regs m off v -> spill regs' m' off v).
  { intros off v Ho Hs. pose proof (f31_spill regs m off v A Hs Hr9 HA0 HA1 Ho) as Hq.
    exists A. split; [unfold rg in Hr9 |- *; rewrite E9; exact Hr9|].
    unfold q64 in Hq |- *. apply (fl_bytes W m m' _ _ Hq MU). rewrite length_le8.
    intros x Hx. apply HWA. lia. }
  destruct HI as (((H40 & H120 & H136 & H160 & H168 & H176 & H208 & H248p & HadO & _ & _ & P184 & P256 & P264 &
                    P272 & P32) & H128 & Hstk & H144 & Had2691) & H216 & H224 & H248 & (Hin & Hadp & Hbyp) &
                  (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & CadF & CadI & C72 & C64 & C56 & C48)).
  destruct HLK as (Hj & H21 & HOUR).
  destruct HS as (_ & H18 & H22 & H23 & H24 & H25 & Hrec & H152 & H280).
  destruct HLT as ((HIDB & Hidok) & (HFGB & Hfgok) & (H104 & H112 & Hbody & Hadbody & HFI)).
  assert (HI' : FLSI g j fr regs' m').
  { split.
    - split.
      + split; [apply SP; [lia | exact H40]|].
        split; [apply SP; [lia | exact H120]|].
        split; [apply SP; [lia | exact H136]|].
        split; [apply SP; [lia | exact H160]|].
        split; [apply SP; [lia | exact H168]|].
        split; [apply SP; [lia | exact H176]|].
        split; [apply SP; [lia | exact H208]|].
        split; [apply SP; [lia | exact H248p]|].
        split; [exact (HAD _ _ HadO)|].
        split.
        * apply (fl_bytes W m m' _ _ Hbyp MU). intros x Hx. apply HWP; unfold g_n, nlen; lia.
        * split; [intros Hn; split; [exact (Hin Hn) | exact (HAD _ _ Hadp)]|].
          split; [apply SP; [lia | exact P184]|].
          split; [apply SP; [lia | exact P256]|].
          split; [apply SP; [lia | exact P264]|].
          split; [apply SP; [lia | exact P272] | apply SP; [lia | exact P32]].
      + split; [apply SP; [lia | exact H128]|].
        split.
        * apply (stk_transport rsegs W m m' fr (fr + 3136) Hstk MU WM). intros x Hx. left. exact (HWF x Hx).
        * split; [apply SP; [lia | exact H144] | exact (HAD _ _ Had2691)].
    - split; [apply SP; [lia | exact H216]|].
      split; [apply SP; [lia | exact H224]|].
      split; [apply SP; [lia | exact H248]|].
      split.
      + split; [exact Hin|]. split; [exact (HAD _ _ Hadp)|].
        apply (fl_bytes W m m' _ _ Hbyp MU). intros x Hx. apply HWP; unfold g_n, nlen; lia.
      + split; [apply SP; [lia | exact C256]|].
        split; [apply SP; [lia | exact C184]|].
        split; [apply SP; [lia | exact C192]|].
        split; [apply SP; [lia | exact C80]|].
        split; [apply SP; [lia | exact C88]|].
        split; [apply SP; [lia | exact C96]|].
        split; [apply SP; [lia | exact C272]|].
        split; [apply SP; [lia | exact C264]|].
        split; [exact (HAD _ _ CadF)|]. split; [exact (HAD _ _ CadI)|].
        split; [apply SP; [lia | exact C72]|]. split; [apply SP; [lia | exact C64]|].
        split; [apply SP; [lia | exact C56] | apply SP; [lia | exact C48]]. }
  assert (HLK' : LK g fr j regs' m').
  { split; [exact Hj|]. split; [unfold rg in H21 |- *; rewrite E21; exact H21|].
    unfold OURb in HOUR |- *. apply (fl_bytes W m m' _ _ HOUR MU). rewrite OUR_length.
    intros x Hx. apply HWF. lia. }
  assert (HS' : FLS g j phi fr regs' m').
  { split; [exact HI'|].
    split; [unfold rg in H18 |- *; rewrite E18; exact H18|].
    split; [unfold rg in H22 |- *; rewrite E22; exact H22|].
    split; [unfold rg in H23 |- *; rewrite E23; exact H23|].
    split; [unfold rg in H24 |- *; rewrite E24; exact H24|].
    split; [unfold rg in H25 |- *; rewrite E25; exact H25|].
    split.
    - intros H50. destruct (Hrec H50) as (Hp0 & Hp1 & Hg & Hpb & Hpl).
      split; [exact Hp0|]. split; [exact Hp1|].
      split.
      + apply (fl_bytes W m m' _ _ Hg MU). unfold t_g. rewrite fr50_length.
        intros x Hx. apply (HWB H50). lia.
      + split; [|exact Hpl]. apply (fl_bytes W m m' _ _ Hpb MU).
        intros x Hx. apply (HWB H50). lia.
    - split; [apply SP; [lia | exact H152] | apply SP; [lia | exact H280]]. }
  assert (HLT' : LT g fr j regs' m').
  { split; [|split].
    - split; [|exact Hidok]. unfold IDBe in HIDB |- *. apply (fl_bytes W m m' _ _ HIDB MU).
      rewrite f31_tID_len. unfold RIM.ID_SIZE. intros x Hx. apply HWF. lia.
    - split; [|exact Hfgok]. unfold FGBe in HFGB |- *. apply (fl_bytes W m m' _ _ HFGB MU).
      rewrite f31_tFG_len. intros x Hx. apply HWF. lia.
    - split; [apply SP; [lia | exact H104]|]. split; [apply SP; [lia | exact H112]|].
      split.
      + apply (fl_bytes W m m' _ _ Hbody MU). pose proof (f31_fs_body_len (g_in g) (S j)) as Hl.
        intros x Hx. apply HWF. lia.
      + split; [exact (HAD _ _ Hadbody) | exact HFI]. }
  exact (conj HI' (conj HLK' (conj HS' HLT'))).
Qed.

(* 0x82798 with a0 = -1 (classify = None): bnez a0 is taken to 0x82800. *)
Lemma f31n_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = Z_to_bv 64 (-1) ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                              t3 t4 t5 t6) Fr (Z_to_bv 64 0x82800) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82798) fc None m (seg_rom rsegs)).
Proof.
  intros. subst a0. step. try if_true. apply evt_done. reflexivity.
Qed.

Section F31.
Context {fx : AYK.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis HBC : BW.bcmp_wrap_contract.

(* 0x82798 with a0 = 0: the three byte checks of the source field (00 40 ab) are not taken, then the bcmp wrapper
   compares the 6 bytes at O+4 with the 6 bytes at R.  Frame variables: [A+208] = fr+448 = O, the classify output
   (36 bytes = t_B j); [A+128] = fr+452 = O+4, its source field; [A+168] = fr+2624 = R = our[]. *)
Lemma f31c_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A O R : Z) (c9 c10 c11 : byte) (rs : list byte) (vcmp lo : Z),
    s1v = Z_to_bv 64 A -> a0 = Z_to_bv 64 0 ->
    0 <= O /\ O + 16 <= 2 ^ 64 -> 0 <= R < 2 ^ 64 ->
    bytes_at rsegs m (A + 128) (le8 (Z_to_bv 64 (O + 4))) ->
    bytes_at rsegs m (A + 208) (le8 (Z_to_bv 64 O)) ->
    bytes_at rsegs m (A + 168) (le8 (Z_to_bv 64 R)) ->
    bytes_at rsegs m (O + 4) [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11] ->
    bytes_at rsegs m R rs -> length rs = 6%nat ->
    memcmp_model [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11] rs 6 = Some vcmp ->
    mem_inv rsegs m -> addressable m (O + 4) 6 -> addressable m R 6 ->
    app_mem (O + 4 + 6) -> app_mem (R + 6) -> app_mem (O + 4 + 7) -> app_mem (R + 7) ->
    (O + 4 + 6 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= O + 4) ->
    (R + 6 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    LE.evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 vcmp) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x827d8) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
         /\ asan_cells m' /\ shadow_rw m')
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82798) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A O R c9 c10 c11 rs vcmp lo -> -> [HO0 HO1] HR0 H128 H200 H168 HBL HBR HLrs Hmm HMI HADL HADR
    HaL6 HaR6 HaL7 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC HSW HRB HRM HGC HC254 HC255.
  assert (HL128 : ov_read_bytes rsegs m (wa (A + 128)) 8 = Some (le8 (Z_to_bv 64 (O + 4)))).
  { pose proof (bytes_at_ov_read rsegs m (A + 128) _ 0 8 H128 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HL200 : ov_read_bytes rsegs m (wa (A + 208)) 8 = Some (le8 (Z_to_bv 64 O))).
  { pose proof (bytes_at_ov_read rsegs m (A + 208) _ 0 8 H200 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HL168 : ov_read_bytes rsegs m (wa (A + 168)) 8 = Some (le8 (Z_to_bv 64 R))).
  { pose proof (bytes_at_ov_read rsegs m (A + 168) _ 0 8 H168 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HB4 : ov_read_bytes rsegs m (wa (O + 4)) 1 = Some [Z_to_bv 8 0]).
  { pose proof (bytes_at_ov_read rsegs m (O + 4) _ 0 1 HBL ltac:(cbn; lia)) as HH.
    cbn [firstn skipn] in HH. replace (O + 4 + Z.of_nat 0) with (O + 4) in HH by lia. exact HH. }
  assert (HB5 : ov_read_bytes rsegs m (wa (O + 5)) 1 = Some [Z_to_bv 8 64]).
  { pose proof (bytes_at_ov_read rsegs m (O + 4) _ 1 1 HBL ltac:(cbn; lia)) as HH.
    cbn [firstn skipn] in HH. replace (O + 4 + Z.of_nat 1) with (O + 5) in HH by lia. exact HH. }
  assert (HB6 : ov_read_bytes rsegs m (wa (O + 6)) 1 = Some [Z_to_bv 8 171]).
  { pose proof (bytes_at_ov_read rsegs m (O + 4) _ 2 1 HBL ltac:(cbn; lia)) as HH.
    cbn [firstn skipn] in HH. replace (O + 4 + Z.of_nat 2) with (O + 6) in HH by lia. exact HH. }
  (* 0x82798 bnez a0 (a0 = 0): not taken *)
  step. try if_false.
  (* 0x8279c ld a0,128(s1); lbu a0,0(a0) = 0x00; bnez a0 (to 0x82bf4): not taken *)
  step. step. step. try if_false.
  (* 0x827a8 ld a0,208(s1); lbu a0,5(a0) = 0x40; li a1,64; bne a0,a1 (to 0x82bf4): not taken *)
  step. step. step. step. try if_false.
  (* 0x827b8 ld a0,208(s1); lbu a0,6(a0) = 0xab; li a1,171; bne a0,a1 (to 0x82bf4): not taken *)
  step. step. step. step. try if_false.
  (* 0x827c8 li a2,6; ld a0,128(s1); ld a1,168(s1); jal wrapper_bcmp *)
  step. step. step. step.
  pose proof HBC as HB. unfold BW.bcmp_wrap_contract, BW.BCMP_WRAP_K in HB. cbv zeta in HB.
  assert (EL : bv_unsigned (Z_to_bv 64 (O + 4)) = O + 4) by (apply unsigned_lit; lia).
  assert (ER : bv_unsigned (Z_to_bv 64 R) = R) by (apply unsigned_lit; lia).
  assert (E6 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
  eapply evt_cut.
  { eapply HB with (ls := [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11]) (rs := rs) (v := vcmp) (lo := lo).
    all: rewrite ?EL, ?ER, ?E6.
    - exact HBL.
    - exact HBR.
    - change (Z.to_nat 6) with 6%nat; exact Hmm.
    - exact HMI.
    - clear; lia.
    - exact HADL.
    - exact HADR.
    - right; exact HaL6.
    - right; exact HaR6.
    - right; exact HaL7.
    - right; exact HaR7.
    - exact HdjL.
    - exact HdjR.
    - exact HST.
    - exact Hlo1.
    - exact Hlo2.
    - exact Hspa.
    - exact HAC.
    - exact HSW.
    - exact HRB.
    - exact HRM.
    - exact HGC.
    - exact HC254.
    - exact HC255. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m'
              & E & MU & WM & MI' & ST' & AC' & SW' & _ & _).
  subst ms'.
  match goal with
  | |- context [ret_pc (Z_to_bv 64 ?z)] =>
      replace (ret_pc (Z_to_bv 64 z)) with (Z_to_bv 64 z) by (symmetry; apply ret_pc_even; [clear; lia | reflexivity])
  end.
  apply evt_done.
  eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split; [exact AC' | exact SW'].
Qed.

(* The same run from a memory that agrees with the image on its read-only bytes (a cut carries ro_agree, not
   mem_inv): f31c_evt on the normalized memory (MemNorm.evt_normalize), every premise moved to it and the post moved
   back across mem_rel (RoAdapt; the stack window and the shadow have no read-only byte). *)
Lemma f31c_norm :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A O R : Z) (c9 c10 c11 : byte) (rs : list byte) (vcmp lo : Z),
    s1v = Z_to_bv 64 A -> a0 = Z_to_bv 64 0 ->
    0 <= O /\ O + 16 <= 2 ^ 64 -> 0 <= R < 2 ^ 64 ->
    bytes_at rsegs m (A + 128) (le8 (Z_to_bv 64 (O + 4))) ->
    bytes_at rsegs m (A + 208) (le8 (Z_to_bv 64 O)) ->
    bytes_at rsegs m (A + 168) (le8 (Z_to_bv 64 R)) ->
    bytes_at rsegs m (O + 4) [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11] ->
    bytes_at rsegs m R rs -> length rs = 6%nat ->
    memcmp_model [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11] rs 6 = Some vcmp ->
    ro_agree rsegs m -> addressable m (O + 4) 6 -> addressable m R 6 ->
    app_mem (O + 4 + 6) -> app_mem (R + 6) -> app_mem (O + 4 + 7) -> app_mem (R + 7) ->
    (O + 4 + 6 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= O + 4) ->
    (R + 6 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    LE.evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 vcmp) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x827d8) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82798) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A O R c9 c10 c11 rs vcmp lo Es1 Ea0 HO HR0 H128 H200 H168 HBL HBR HLrs Hmm HRO HADL HADR
    HaL6 HaR6 HaL7 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC HSW HRB HRM HGC HC254 HC255.
  pose proof (mem_rel_normalize rsegs m HRO) as REL0.
  assert (BR : forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs (normalize rsegs m) a bs)
    by (intros a bs Hb; exact (proj1 (bytes_at_rel rsegs m (normalize rsegs m) a bs REL0) Hb)).
  assert (HST0 : stk rsegs (normalize rsegs m) lo (bv_unsigned sp)).
  { apply (RoAdapt.rel_stk_norm m _ _ _ REL0); [|exact HST].
    intros x Hx. apply RoAdapt.ro_addr_false_hi. unfold HIGHMEM_BEG, APPMEM_END in *. lia. }
  eapply LE.evt_mono.
  { eapply (evt_normalize rsegs _ _ Fr _ fc None m (seg_rom rsegs) BzBridge.wx_apart_asan HRO).
    exact (f31c_evt ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 Fr fc (normalize rsegs m) A O R c9 c10 c11 rs vcmp lo Es1 Ea0 HO HR0
             (BR _ _ H128) (BR _ _ H200) (BR _ _ H168) (BR _ _ HBL) (BR _ _ HBR) HLrs Hmm
             (mem_inv_normalize rsegs m)
             (RoAdapt.rel_addr_norm m _ _ _ REL0 HADL) (RoAdapt.rel_addr_norm m _ _ _ REL0 HADR)
             HaL6 HaR6 HaL7 HaR7 HdjL HdjR HST0 Hlo1 Hlo2 Hspa
             (RoAdapt.rel_ac_norm m _ REL0 HAC) (RoAdapt.rel_sw_norm m _ REL0 HSW)
             (BR _ _ HRB) (BR _ _ HRM) (BR _ _ HGC) (BR _ _ HC254) (BR _ _ HC255)). }
  intros s (s0' & HQ & REL & SAME).
  destruct HQ as (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m0' &
                  E0 & MU & WM & _ & ST & _ & _).
  subst s0'.
  destruct s as [R' F' pc' sv' rv' fc' m' ro'].
  unfold ms_rel, MS in REL.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in REL, SAME.
  destruct REL as (ER & EF & Epc & Esv & Erv & Efc & Erom & RM).
  subst R' F' pc' sv' rv' fc' ro'.
  exists ra', a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) m' m0' REL0 RM SAME MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) m' m0' REL0 RM SAME WM)|].
  exact (RoAdapt.rel_stk_back m' m0' _ _ RM ST).
Qed.

Lemma seg_F31 : forall j, Hat B APIf ra (Inv_A827d8_at B APIf ra) j -> Hat B APIf ra (Inv_A82800_at B APIf ra) j ->
  Hat B APIf ra (Inv_A82798_at B APIf ra) j.
Proof.
  intros j H72c H754 g c HInv.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HLK & HFLS &
    H10 & HBo & HadL & Hev & HLT).
  subst c. rewrite SEGS.
  pose proof (fra_frame B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA) as (Hplace & _ & _ & _).
  pose proof (fra_app B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA) as (HGT & Hfapp).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAGf & HWAf & HSHI1 & HSHI2 &
    HSHI3 & Hhb & Hlive).
  pose proof HFLSI as (((Hs40 & Hs120 & Hs136 & Hs160 & Hs168 & Hs176 & Hs200 & _ & HadR & _ & _) & Hs128 & Hfstk &
    Hs144 & Had2691) & Hs216 & Hs224 & Hs248 & Hf1 & _).
  pose proof HLK as (Hj255 & Hr21 & HOUR).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HKK : BCMP_WRAP_K = 4560) by reflexivity.
  assert (HHM : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HAE : APPMEM_END = 140737488355328) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HwinB : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64) by (destruct Hwin as (W0 & W1 & _); lia).
  assert (HA64 : 0 <= A /\ A + 416 <= 2 ^ 64) by lia.
  assert (Hfr0 : 0 <= fr) by (unfold AC.GT in HGT; lia).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH) as Hstkhi.
  destruct (f31_cls_r (t_cls (g_in g) j)) as [Er|Er]; rewrite Er in H10.
  2: {
    (* classify = None (a0 = -1): bnez a0 at 0x82798 is taken to 0x82800; nothing else changes. *)
    apply (sl_run_lib regs (Z_to_bv 64 0x82798) mem md
      (fun R0 pc' mem' => pc' = Z_to_bv 64 0x82800 /\ mem' = mem /\
         getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
         getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
         getr R0 19 = getr regs 19 /\ getr R0 21 = getr regs 21 /\ getr R0 23 = getr regs 23 /\
         getr R0 24 = getr regs 24 /\ getr R0 25 = getr regs 25 /\ getr R0 22 = getr regs 22 /\
         getr R0 26 = getr regs 26)
      (Post B APIf ra g)).
    - exact Hhalt.
    - eapply LE.evt_mono.
      { unfold Regs6ss.mkR_of. apply f31n_evt. unfold rg in H10. exact H10. }
      { intros ms' E. eexists _, _, _. split; [exact E|].
        split; [reflexivity|]. split; [reflexivity|]. repeat split; reflexivity. }
    - intros R0 pc' mem' regs' md'
        (Hpc & Hmem & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E21 & E23 & E24 & E25 & E22 & E26)
        Hreg Hmat.
      subst pc' mem'.
      assert (F2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact E2).
      assert (F3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact E3).
      assert (F4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact E4).
      assert (F8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact E8).
      assert (F9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact E9).
      assert (F18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact E18).
      assert (F19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact E19).
      assert (F21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact E21).
      assert (F22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact E22).
      assert (F23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact E23).
      assert (F24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact E24).
      assert (F25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact E25).
      assert (F26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact E26).
      destruct (f31_keep g j phi fr regs regs' mem mem [] A HFLSI HLK HFLS HLT (munch_refl [] mem)
                  (wmono_refl rsegs mem) (fun p n H => H) F9 F18 F21 F22 F23 F24 F25 Hr9
                  (proj1 HA64) (proj2 HA64) (fun x _ => I) (fun x _ => I) (fun _ x _ => I) (fun _ x _ => I))
        as (HI' & HLK' & HS' & HLT').
      assert (HIexit : Inv_A82800_at B APIf ra g j
                         (mkCfg (mkst regs' (Z_to_bv 64 0x82800) mem (seg_rom rsegs)) md')).
      { exists phi, regs', mem, md', fr. rewrite SEGS. split; [reflexivity|].
        split; [exact (sl_fra_move B APIf ra g fr _ regs regs' mem md md' HFRA F2 F3 F4 F8 F9 F19 F26 Hmat)|].
        split; [exact (ent_mat APIf g _ mem md md' HENT Hmat)|].
        split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|]. split; [exact HI'|].
        split; [exact HLK'|]. split; [exact HS' | exact HLT']. }
      pose proof (H754 g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR. }
  (* classify = Some e (a0 = 0): the source field is 00 40 ab c9 c10 c11; the three checks fall through and the
     bcmp wrapper compares it with our[]. *)
  destruct (f31_cls_some _ Er) as (e & Ecl).
  pose proof (f31_B_src (g_in g) j e Ecl) as Esrc.
  set (c9 := RP.cp_b (t_g (g_in g) j) 9) in *.
  set (c10 := RP.cp_b (t_g (g_in g) j) 10) in *.
  set (c11 := RP.cp_b (t_g (g_in g) j) 11) in *.
  set (lsc := [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11]) in *.
  assert (HLs : bytes_at rsegs mem (fr + 448 + 4) lsc).
  { rewrite <- Esrc. change (fr + 448 + 4) with (fr + 448 + Z.of_nat 4).
    apply f31_ba_sub; [exact HBo | rewrite f31_B_length; lia]. }
  destruct (SF.memcmp_model_total lsc (OUR (g_in g)) 6 ltac:(cbn; lia) ltac:(rewrite OUR_length; lia))
    as (v & Hv).
  destruct (f31_mm_spec 6 lsc (OUR (g_in g)) v eq_refl (OUR_length _) Hv) as [Hiff Hvr].
  pose proof HRT as HRT2.
  destruct HRT2 as (HAC0 & HSW0 & _ & HCF0 & _ & HREAL0 & _).
  destruct HCF0 as (HGOTCF & _ & _ & _ & _ & _ & HCF240 & _).
  assert (HGC : bytes_at rsegs mem GOT_CF (le8 (wa CF))) by exact HGOTCF.
  assert (HRBc : bytes_at rsegs mem REAL_BCMP (le8 (wa BCMP)))
    by (apply (real_cell_of mem REAL_BCMP BCMP HREAL0); vm_compute; reflexivity).
  assert (HRMc : bytes_at rsegs mem REAL_MEMCMP (le8 (wa MEMCMP)))
    by (apply (real_cell_of mem REAL_MEMCMP MEMCMP HREAL0); vm_compute; reflexivity).
  assert (HC254 : bytes_at rsegs mem (CF + 254) [Z_to_bv 8 1]).
  { pose proof (f31_ba_sub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 14 1 HCF240
      ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 14) with (CF + 254) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 14 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
  assert (HC255 : bytes_at rsegs mem (CF + 255) [Z_to_bv 8 1]).
  { pose proof (f31_ba_sub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 15 1 HCF240
      ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 15) with (CF + 255) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 15 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
  assert (Q128 : q64 mem (A + 128) (fr + 452)) by (apply (f31_spill regs mem 128 _ A Hs128 Hr9); lia).
  assert (Q168 : q64 mem (A + 168) (fr + 2624)) by (apply (f31_spill regs mem 168 _ A Hs168 Hr9); lia).
  assert (Q200 : q64 mem (A + 208) (fr + 448)) by (apply (f31_spill regs mem 208 _ A Hs200 Hr9); lia).
  assert (HstkW : stk rsegs mem (g_S g - AF.SLOT_STACK) (AC.aspZ regs)).
  { destruct (stk_split rsegs mem (g_S g - AF.SLOT_STACK) (AC.aspZ regs) (g_S g) Hwin ltac:(lia)) as [HS _].
    exact HS. }
  set (W := [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)]).
  apply (sl_run_lib regs (Z_to_bv 64 0x82798) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x827d8 /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 21 = getr regs 21 /\ getr R0 23 = getr regs 23 /\
       getr R0 24 = getr regs 24 /\ getr R0 25 = getr regs 25 /\ getr R0 22 = getr regs 22 /\
       getr R0 26 = getr regs 26 /\ getr R0 10 = Z_to_bv 64 v /\
       munch W mem mem' /\ wmono rsegs mem mem' /\
       stk rsegs mem' (g_S g - AF.SLOT_STACK) (AC.aspZ regs))
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply LE.evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply f31c_norm with (A := A) (O := fr + 448) (R := fr + 2624) (c9 := c9) (c10 := c10) (c11 := c11)
        (rs := OUR (g_in g)) (vcmp := v) (lo := g_S g - AF.SLOT_STACK).
      - unfold rg in Hr9; exact Hr9.
      - unfold rg in H10; exact H10.
      - lia.
      - lia.
      - replace (fr + 448 + 4) with (fr + 452) by lia. exact Q128.
      - exact Q200.
      - exact Q168.
      - exact HLs.
      - exact HOUR.
      - apply OUR_length.
      - exact Hv.
      - exact Hro.
      - replace (fr + 448 + 4) with (fr + 452) by lia. exact HadL.
      - exact HadR.
      - apply Hfapp; lia.
      - apply Hfapp; lia.
      - apply Hfapp; lia.
      - apply Hfapp; lia.
      - assert (HdjL : fr + 448 + 4 + 6 <= AC.aspZ regs - BCMP_WRAP_K \/ AC.aspZ regs <= fr + 448 + 4).
        { destruct (Hplace BCMP_WRAP_K ltac:(lia)) as [HD|HD]; [left | right]; lia. }
        exact HdjL.
      - assert (HdjR : fr + 2624 + 6 <= AC.aspZ regs - BCMP_WRAP_K \/ AC.aspZ regs <= fr + 2624).
        { destruct (Hplace BCMP_WRAP_K ltac:(lia)) as [HD|HD]; [left | right]; lia. }
        exact HdjR.
      - exact HstkW.
      - assert (HloK : g_S g - AF.SLOT_STACK + BCMP_WRAP_K <= AC.aspZ regs) by lia.
        exact HloK.
      - lia.
      - assert (HaspB : AC.aspZ regs <= APPMEM_END) by lia.
        exact HaspB.
      - exact HAC0.
      - exact HSW0.
      - exact HRBc.
      - exact HRMc.
      - exact HGC.
      - exact HC254.
      - exact HC255. }
    { intros ms' (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m'
                  & E & MU & WM & ST').
      eexists _, (Z_to_bv 64 0x827d8), m'. split; [exact E|].
      split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [unfold rg in Hr9; rewrite Hr9; reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. exact ST'. }
  - intros R0 pc' mem' regs' md'
      (Hpc & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E21 & E23 & E24 & E25 & E22 & E26 & E10 & MU & WM & ST')
      Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact E2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact E3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact E4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact E8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact E9).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact E18).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact E19).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact E21).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact E22).
    assert (Fr23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact E23).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact E24).
    assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact E25).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact E26).
    assert (Fr10 : getr regs' 10 = Z_to_bv 64 v) by (rewrite Hreg; exact E10).
    (* the wrapper's window W = [sp - 4560, sp) is app memory, above stklo (so a_store_ok), below S *)
    assert (Hallapp : all_app W).
    { subst W. cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right. lia. }
    assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.a_store_ok (hb1 phi (AC.a_size (flen g j)) ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hns. apply MU. rewrite unsigned_lit by lia. subst W.
      cbn [ULFr.outside LibFr.outside]. split; [|exact I]. intros [HH1 HH2]. apply Hns.
      unfold AC.a_store_ok. right; left. split; lia. }
    assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
      by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
    destruct (AC.a_laws_store _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem mem' md HAH HstoreC HwmL)
      as (_ & HOWN & HSTKeq & HSTKHI).
    (* the entry-anchored window [S - SLOT_STACK, S) of mem': the wrapper's own post below sp, kept above it *)
    assert (HWINg : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
    { destruct (stk_split rsegs mem (g_S g - AF.SLOT_STACK) (AC.aspZ regs) (g_S g) Hwin ltac:(lia))
        as [_ Hhigh].
      apply (stk_merge rsegs mem' (g_S g - AF.SLOT_STACK) (AC.aspZ regs) (g_S g)); [exact ST' | | lia].
      apply (stk_transport_disjoint rsegs W mem mem' _ _ Hhigh MU WM).
      subst W. cbn [disjoint_from]. split; [|exact I]. right. lia. }
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem' md').
    { apply (sl_callee_keep B APIf ra empty FF g fr _ regs regs' mem mem' md md' BCMP_WRAP_K HFRA MU WM HWINg).
      - lia.
      - lia.
      - destruct (Hplace BCMP_WRAP_K ltac:(lia)) as [HD|HD]; [right | left]; lia.
      - lia.
      - exact Fr2.
      - exact Fr3.
      - exact Fr4.
      - exact Fr8.
      - exact Fr9.
      - exact Fr19.
      - exact Fr26.
      - exact Hmat. }
    (* ENT across the wrapper's write (W lies in the slot window below the entry sp S), then across the run's
       lazy-page materialization *)
    assert (HENTm : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md).
    { apply (ent_store B APIf ra g fr _ regs mem mem' md W HENT HFRA MU).
      - intros x Hx. destruct (Z_lt_le_dec x (AC.aspZ regs - BCMP_WRAP_K)) as [Hlt|Hge].
        + left. subst W. cbn [ULFr.outside LibFr.outside]. split; [|exact I]. lia.
        + destruct (Z_lt_le_dec x (AC.aspZ regs)) as [Hlt2|Hge2].
          * right. left. lia.
          * left. subst W. cbn [ULFr.outside LibFr.outside]. split; [|exact I]. lia.
      - exact HSTKeq.
      - exact HSTKHI.
      - intros a _ Hown. exact (proj2 (HOWN a) Hown). }
    assert (HENT' : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md')
      by exact (ent_mat APIf g _ mem' md md' HENTm Hmat).
    (* what W misses: the spill area (at or above sp), the frame (fra_frame), the turn's block and the harness
       block (both live blocks, so below stklo <= S - SLOT_STACK < sp - 4560) *)
    assert (HWA : forall x, A <= x < A + 416 -> outside W x).
    { intros x Hx. subst W. cbn [ULFr.outside LibFr.outside]. split; [|exact I]. lia. }
    assert (HWfr : forall x, fr <= x < fr + 3136 -> outside W x).
    { intros x Hx. subst W. cbn [ULFr.outside LibFr.outside]. split; [|exact I].
      destruct (Hplace BCMP_WRAP_K ltac:(lia)); lia. }
    assert (HWB : 50 <= flen g j -> forall x, phi <= x < phi + flen g j -> outside W x).
    { intros _ x Hx.
      destruct (AC.a_laws_blocks _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md phi
                  (AC.a_size (flen g j)) HAH) as (_ & _ & Hle & _).
      + apply in_or_app. left. unfold hb1. left. reflexivity.
      + unfold AC.a_size in Hle. subst W. cbn [ULFr.outside LibFr.outside]. split; [|exact I]. lia. }
    assert (HWP : 0 < g_n g -> forall x, g_p g <= x < g_p g + g_n g -> outside W x).
    { intros Hn x Hx. pose proof Hf1 as (Hin & _ & _).
      destruct (AC.a_laws_blocks _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md (g_p g) (g_n g)
                  HAH) as (_ & _ & Hle & _).
      + apply in_or_app. right. exact (Hin Hn).
      + subst W. cbn [ULFr.outside LibFr.outside]. split; [|exact I]. lia. }
    destruct (f31_keep g j phi fr regs regs' mem mem' W A HFLSI HLK HFLS HLT MU WM
                (fun p n H => sl_addr_keep mem mem' W p n H MU Hallapp)
                Fr9 Fr18 Fr21 Fr22 Fr23 Fr24 Fr25 Hr9 (proj1 HA64) (proj2 HA64) HWA HWfr HWB HWP)
      as (HI' & HLK' & HS' & HLT').
    assert (Hiff' : getr regs' 10 = Z_to_bv 64 0 <-> firstn 6 (skipn 4 (t_B (g_in g) j)) = OUR (g_in g)).
    { rewrite Fr10, (f31_lit0 v Hvr), Esrc. exact Hiff. }
    assert (HIexit : Inv_A827d8_at B APIf ra g j
                       (mkCfg (mkst regs' (Z_to_bv 64 0x827d8) mem' (seg_rom rsegs)) md')).
    { exists phi, regs', mem', md', fr. rewrite SEGS. split; [reflexivity|].
      split; [exact HFRA'|]. split; [exact HENT'|].
      split; [exact Hgn|]. split; [exact Hj|].
      split; [split; [exact (proj1 HHB) | exact (sl_addr_keep mem mem' W _ _ (proj2 HHB) MU Hallapp)]|].
      split; [exact HI'|]. split; [exact HLK'|]. split; [exact HS'|].
      split; [rewrite Ecl; discriminate|].
      split; [exact Hiff'|].
      split; [|exact HLT'].
      intros e0 He0. pose proof (Hev e0 He0) as Hq. unfold u32 in Hq |- *.
      apply (fl_bytes W mem mem' _ _ Hq MU). rewrite length_le4. intros x Hx. apply HWfr. lia. }
    pose proof (H72c g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End F31.
(* b8refit: applied map b8refit-v190.tsv sha256=7153b913f625df27 kinds=frame,pc,slot. Do not apply it again. *)
