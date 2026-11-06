(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatSim StoreOk ShapeSet RealizesCfg AsanAcct AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxPlan FxFrame FxDrv FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_put AXG_put3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put3 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp.AXG_uw.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcHand.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFixNew.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcDenW AcHand AcHand0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp AcTbl.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt.AcShift OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.AcMrg OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand.AcMrg0 OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFixNew.AcComm OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDenW OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp.AcPutApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcTbl OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp.AcTblOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma mrg_reg0 : forall E L S ms r l, sden0 SEGS E (mrg L S) ms -> rget (s_regs L) (rkey r) = l -> getr (ms_regs ms) r = lden E l.
Proof. intros E L S ms r l Hd Hl. destruct Hd as (_ & _ & _ & HR & _). rewrite (HR r). cbn [mrg s_regs]. rewrite Hl. reflexivity. Qed.
Lemma mrg_rg0 : forall E L S ms i R, sden0 SEGS E (mrg L S) ms -> nth_error (s_rgs L) i = Some R -> rg_ok SEGS E (ms_mem ms) R.
Proof.
  intros E L S ms i R Hd Hi. destruct Hd as (_ & _ & _ & _ & HG & _). cbn [mrg s_rgs] in HG.
  apply Forall_app in HG as [HG _]. rewrite Forall_forall in HG. exact (HG R (nth_error_In _ _ Hi)).
Qed.
Lemma mrg_fact0 : forall E L S ms f, sden0 SEGS E (mrg L S) ms -> In f (s_facts L) -> fact_ok E f.
Proof.
  intros E L S ms f Hd Hf. destruct Hd as (_ & _ & _ & _ & _ & _ & HF & _). cbn [mrg s_facts] in HF.
  apply Forall_app in HF as [HF _]. rewrite Forall_forall in HF. exact (HF f Hf).
Qed.
Lemma reg_off0 : forall E L S ms k spl c SPv, sden0 SEGS E (mrg L S) ms -> rget (s_regs L) (rk k) = laddc spl c ->
  bv_unsigned (lden E spl) = SPv -> 0 <= SPv + c < two64 -> getr (ms_regs ms) (Z_to_bv 5 k) = wa (SPv + c).
Proof.
  intros E L S ms k spl c SPv Hd Hl HS Hr. rewrite (mrg_reg0 E L S ms (Z_to_bv 5 k) _ Hd Hl). unfold wa. apply bv_eq.
  rewrite lden_laddc, HS. reflexivity.
Qed.
Lemma reg_lin20 : forall E L S ms k c x1 k1 x2 k2 v, sden0 SEGS E (mrg L S) ms -> rget (s_regs L) (rk k) = LIN c [(x1, k1); (x2, k2)] ->
  eqm (c + k1 * bv_unsigned (E x1) + k2 * bv_unsigned (E x2)) v -> getr (ms_regs ms) (Z_to_bv 5 k) = wa v.
Proof.
  intros E L S ms k c x1 k1 x2 k2 v Hd Hl Hv. rewrite (mrg_reg0 E L S ms (Z_to_bv 5 k) _ Hd Hl). unfold lden, lz. cbn [l_c l_t tsum]. unfold vz, wa.
  apply Z_to_bv_eqm. replace (c + (k1 * bv_unsigned (E x1) + (k2 * bv_unsigned (E x2) + 0))) with
    (c + k1 * bv_unsigned (E x1) + k2 * bv_unsigned (E x2)) by ring. exact Hv.
Qed.
Lemma stk_rw0 : forall E m spl b z c SPv x, rg_ok SEGS E m (RG (laddc spl b) (lconst z) RW c) -> bv_unsigned (lden E spl) = SPv ->
  8192 <= SPv <= 2^47 -> -8192 <= b -> 0 <= z -> b + z <= 0 -> SPv + b <= x < SPv + b + z ->
  rd1 SEGS m (Z_to_bv 64 x) <> None /\ wview SEGS m (Z_to_bv 64 x) <> None.
Proof.
  intros E m spl b z c SPv x HR HS HSr Hb Hz Hbz Hx. apply (rg_rw_pt _ _ _ x HR eq_refl). cbn [rg_base].
  rewrite lden_laddc, HS, u_small64 by (unfold two64; lia). unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_small64 by (unfold two64; lia). lia.
Qed.
Lemma stk_in0 : forall E spl b z c SPv x, bv_unsigned (lden E spl) = SPv ->
  8192 <= SPv <= 2^47 -> -8192 <= b -> 0 <= z -> b + z <= 0 -> SPv + b <= bv_unsigned x < SPv + b + z ->
  in_rg E (RG (laddc spl b) (lconst z) RW c) x.
Proof.
  intros E spl b z c SPv x HS HSr Hb Hz Hbz Hx. unfold in_rg. cbn [rg_base].
  rewrite lden_laddc, HS, u_small64 by (unfold two64; lia). unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_small64 by (unfold two64; lia). lia.
Qed.
Lemma unw_wr0 : forall E m spl SPv osp obuf blo zlo bhi zhi clo cf cs ct chi, bv_unsigned (lden E spl) = SPv -> 8192 <= SPv <= 2^47 ->
  osp <= obuf -> obuf + 2056 <= 0 -> -8192 <= blo -> blo <= osp - 1024 -> osp - 64 <= blo + zlo -> 0 <= zlo -> blo + zlo <= 0 ->
  -8192 <= bhi -> bhi <= obuf + 256 -> obuf + 2056 <= bhi + zhi -> 0 <= zhi -> bhi + zhi <= 0 -> -8192 <= osp - 1024 ->
  rg_ok SEGS E m (RG (laddc spl blo) (lconst zlo) RW clo) ->
  rg_ok SEGS E m (RG (laddc spl (osp - 64)) (lconst 64) RW cf) ->
  rg_ok SEGS E m (RG (laddc spl (obuf + 8)) (lconst 8) RW cs) ->
  rg_ok SEGS E m (RG (laddc spl (obuf + 16)) (lconst 240) RW ct) ->
  rg_ok SEGS E m (RG (laddc spl bhi) (lconst zhi) RW chi) ->
  forall x, (SPv + osp - 1024 <= x < SPv + osp) \/ (SPv + obuf + 8 <= x < SPv + obuf + 2056) ->
  rd1 SEGS m (Z_to_bv 64 x) <> None /\ wview SEGS m (Z_to_bv 64 x) <> None.
Proof.
  intros E m spl SPv osp obuf blo zlo bhi zhi clo cf cs ct chi HS HSr N5 N6 N7 N8 N9 N10 N16 N17 N11 N12 N13 N14 N15 Rlo Rf Rs Rt Rhi x Hx.
  destruct (Z_lt_ge_dec x (SPv + osp - 64)) as [H1|H1]; [apply (stk_rw0 E m spl blo zlo clo SPv x Rlo HS); lia|].
  destruct (Z_lt_ge_dec x (SPv + osp)) as [H2|H2]; [apply (stk_rw0 E m spl (osp - 64) 64 cf SPv x Rf HS); lia|].
  destruct (Z_lt_ge_dec x (SPv + obuf + 16)) as [H3|H3]; [apply (stk_rw0 E m spl (obuf + 8) 8 cs SPv x Rs HS); lia|].
  destruct (Z_lt_ge_dec x (SPv + obuf + 256)) as [H4|H4]; [apply (stk_rw0 E m spl (obuf + 16) 240 ct SPv x Rt HS); lia|].
  apply (stk_rw0 E m spl bhi zhi chi SPv x Rhi HS); lia.
Qed.
Lemma nth_bvs8 : forall x j b, nth_error (bvs_of (lvar x) 8) j = Some b -> (j < 8)%nat /\ b = BV (lvar x) (Z.of_nat j).
Proof.
  intros x j b H. destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; cbn in H; try (injection H as <-; split; [lia | reflexivity]).
  rewrite nth_error_nil in H. discriminate.
Qed.
Lemma put_rg_mrg0 : forall L S i o bvs, (i < length (s_rgs L))%nat -> put_rg (mrg L S) i o bvs = mrg (put_rg L i o bvs) S.
Proof.
  intros L S i o bvs Hi. unfold put_rg. cbn [mrg s_rgs]. rewrite nth_error_app1 by exact Hi.
  destruct (nth_error (s_rgs L) i) as [R|] eqn:HR; [|exfalso; apply nth_error_None in HR; lia].
  unfold mrg. cbn [s_pc s_regs s_rgs s_facts s_next s_resv]. rewrite upd_nth_app by exact Hi. reflexivity.
Qed.
Lemma unw_res_mrg0 : forall L S W iS, (iS < length (s_rgs L))%nat ->
  mrg (unw_res L W iS) S =
  add_fact (put_rg (bump (mrg (hand_post L 0x82a28 KALLk W) S) (Pos.succ (s_next L + 33))) iS 0 (bvs_of (lvar (s_next L + 33)) 8))
           (FRange (lvar (s_next L + 33)) 1 30).
Proof.
  intros L S W iS Hi. unfold unw_res. cbn [hand_post s_next].
  change (mrg (add_fact ?X ?f) S) with (add_fact (mrg X S) f). f_equal.
  change (bump (mrg ?X S) ?k) with (mrg (bump X k) S).
  rewrite put_rg_mrg0; [reflexivity|]. cbn [bump hand_post s_rgs]. rewrite length_empty_at. exact Hi.
Qed.

Lemma ro_none_z : forall E m z, 77824 <= z < 2^32 -> rg_ok SEGS E m (RG (lconst 65536) (lconst z) RO TEmpty) ->
  forall i, 65536 <= i < 143360 -> m (Z_to_bv 64 i) = None.
Proof.
  intros E m z Hz Rro i Hi. destruct Rro as (_ & _ & Hb & _). cbn [rg_base rg_kind rg_size] in Hb. unfold rsz in Hb. cbn [rg_size] in Hb.
  rewrite lden_lconst, u_small64 in Hb by (unfold two64; lia). specialize (Hb (i - 65536) ltac:(lia)).
  rewrite lden_lconst, u_small64 in Hb by (unfold two64; lia). replace (65536 + (i - 65536)) with i in Hb by lia. exact (proj1 Hb).
Qed.


(* [comment removed for export] *)
Lemma unw_uch10 : forall m E spl SPv TOP c b, rg_ok SEGS E m (RG (laddc spl (-56)) (lconst 56) RW c) -> bv_unsigned (lden E spl) = SPv ->
  8192 <= SPv <= 2^47 -> TOP <= 2^47 -> tget (Pos.of_succ_nat 40) c = Some (BK b) -> 0 <= b < 256 ->
  (forall j, (1 <= j < 8)%nat -> tget (Pos.of_succ_nat (40 + j)) c = Some (BK 0)) -> b <= SPv -> uch m TOP SPv.
Proof.
  intros m E spl SPv TOP c b HR HS HSr HTr Hb0 Hb Hbj Hle.
  assert (Hrw : forall x, SPv - 56 <= x < SPv -> rd1 SEGS m (Z_to_bv 64 x) <> None).
  { intros x Hx. exact (proj1 (stk_rw0 E m spl (-56) 56 c SPv x HR HS ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))). }
  apply uch_mk.
  - apply (rdn_some m (SPv - 8) 8); [lia | cbn; unfold two64; lia |]. intros i Hi. apply Hrw. cbn in Hi. lia.
  - apply (rdn_some m (SPv - 16) 8); [lia | cbn; unfold two64; lia |]. intros i Hi. apply Hrw. cbn in Hi. lia.
  - intros nb Hrd H1 H2 H3. exfalso.
    assert (Hrd8 : rd m (SPv - 16) 8 b).
    { unfold rd, word_to_le_bytes. rewrite u_wa_small by lia.
      assert (Hl : length (Z_to_le_bytes 8 b) = 8%nat) by apply length_Z_to_le_bytes. rewrite <- Hl.
      unfold wa. apply rdn_of_rd1; [lia | rewrite Hl; unfold two64; lia |]. rewrite Hl. intros j Hj.
      rewrite nth_Z_to_le_bytes by exact Hj.
      assert (HA : bv_unsigned (lden E (rg_base (RG (laddc spl (-56)) (lconst 56) RW c))) = SPv - 56).
      { cbn [rg_base]. rewrite lden_laddc, HS, u_small64; unfold two64; lia. }
      destruct HR as (_ & _ & _ & HT).
      assert (Hv : tget (Pos.of_succ_nat (40 + j)) c = Some (BK (if Nat.eqb j 0 then b else 0))).
      { destruct (Nat.eqb j 0) eqn:Ej; [apply Nat.eqb_eq in Ej; subst j; rewrite Nat.add_0_r; exact Hb0 | apply Nat.eqb_neq in Ej; apply Hbj; lia]. }
      destruct (HT _ _ Hv) as [_ X]. rewrite HA in X.
      rewrite Zpos_P_of_succ_nat, Nat2Z.inj_add in X. replace (SPv - 56 + (Z.succ (Z.of_nat 40 + Z.of_nat j) - 1)) with (SPv - 16 + Z.of_nat j) in X by lia.
      rewrite X. cbn [bden]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. f_equal.
      destruct (Nat.eqb j 0) eqn:Ej.
      - apply Nat.eqb_eq in Ej. subst j. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
      - apply Nat.eqb_neq in Ej. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small; [reflexivity|]. split; [lia|].
        apply (Z.lt_le_trans _ 256); [lia|]. change 256 with (2 ^ 8). apply Z.pow_le_mono_r; lia. }
    assert (Hnb : nb = b).
    { apply (rd_inj m (SPv - 16) 8 nb b); [lia | | | exact Hrd | exact Hrd8].
      - change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). lia.
      - change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). lia. }
    subst nb. lia.
Qed.

Record unw_shape0 (L : sst) (spl : lin) (osp obuf blo zlo bhi zhi : Z) (iLo iF iS iT iHi iRO iGOT iPSZ : nat) (xt1 xt2 : positive) (lo hi : Z) : Prop := {
  u0_pc  : s_pc L = 0x82908 ;
  u0_rsv : s_resv L = RNone ;
  u0_sp  : rget (s_regs L) (rk 2) = laddc spl osp ;
  u0_buf : rget (s_regs L) (rk 10) = laddc spl obuf ;
  u0_bp  : rget (s_regs L) (rk 12) = spl ;
  u0_top : rget (s_regs L) (rk 13) = TOPL xt1 xt2 ;
  u0_bot : rget (s_regs L) (rk 14) = BOTL xt1 xt2 ;
  u0_max : rget (s_regs L) (rk 15) = lconst 30 ;
  u0_rlo : exists c, nth_error (s_rgs L) iLo = Some (RG (laddc spl blo) (lconst zlo) RW c) ;
  u0_rf  : exists c, nth_error (s_rgs L) iF = Some (RG (laddc spl (osp - 64)) (lconst 64) RW c) ;
  u0_rs  : exists c, nth_error (s_rgs L) iS = Some (RG (laddc spl (obuf + 8)) (lconst 8) RW c) /\
           forall j, (4 <= j < 8)%nat -> tget (Pos.of_succ_nat j) c = Some (BK 0) ;
  u0_rt  : exists c, nth_error (s_rgs L) iT = Some (RG (laddc spl (obuf + 16)) (lconst 240) RW c) ;
  u0_rhi : exists c, nth_error (s_rgs L) iHi = Some (RG (laddc spl bhi) (lconst zhi) RW c) ;
  u0_ro  : exists zro, 77824 <= zro < 2^32 /\ nth_error (s_rgs L) iRO = Some (RG (lconst 65536) (lconst zro) RO TEmpty) ;
  u0_got : exists k b z, (k = RI \/ k = RO) /\ 0 <= b <= 910448 /\ 910456 <= b + z <= 2^47 /\ nth_error (s_rgs L) iGOT = Some (RG (lconst b) (lconst z) k TEmpty) ;
  u0_psz : exists b z c, nth_error (s_rgs L) iPSZ = Some (RG (lconst b) (lconst z) RZ c) /\ 0 <= b <= 1532192 /\ 1532192 + 8 <= b + z /\
           b + z < two64 /\ psz_ok c (1532192 - b) = true ;
  u0_fal : In (FMod spl 4 0) (s_facts L) ;
  u0_frg : In (FRange spl lo hi) (s_facts L) ;
  u0_ft1 : In (FRange (lvar xt1) 4294901759 4294967295) (s_facts L) ;
  u0_ft2 : In (FRange (lvar xt2) 0 7) (s_facts L) ;
  u0_nx  : lwf (s_next L) spl = true ;
  u0_num : 2^46 + 8192 <= lo /\ hi <= 2^47 /\ osp mod 16 = 0 /\ obuf mod 8 = 0 /\ osp <= obuf /\ obuf + 2056 <= 0 /\
           -8192 <= blo /\ blo <= osp - 1024 /\ osp - 64 <= blo + zlo /\ 0 <= zlo /\ bhi <= obuf + 256 /\ obuf + 2056 <= bhi + zhi /\
           0 <= zhi /\ bhi + zhi <= 0 /\ -8192 <= osp - 1024 /\ blo + zlo <= 0 /\ -8192 <= bhi
}.

Section UnwMain0.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap SEGS.

#[using="Hwx"] Theorem den_unw_app0 : forall mem0 L S E M ms model T spl osp obuf blo zlo bhi zhi iLo iF iS iT iHi iRO iGOT iPSZ xt1 xt2 lo hi,
  DEN SEGS LIMIT model0 mem0 E (mrg L S) M ms model ->
  state_wf L = true ->
  unw_shape0 L spl osp obuf blo zlo bhi zhi iLo iF iS iT iHi iRO iGOT iPSZ xt1 xt2 lo hi ->
  (* [comment removed for export] *)
  uch (ms_mem (restrict (Hof E M model) ms)) (4096 + 32768 * bv_unsigned (E xt1) + 4096 * bv_unsigned (E xt2))
      (bv_unsigned (lden E spl)) ->
  (forall E' ms' model', DEN SEGS LIMIT model0 mem0 E' (mrg (unw_res L [iF; iS; iT] iS) S) M ms' model' ->
     agree (s_next L) E E' -> realizes_cfg SEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg SEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros mem0 L S E M ms model T spl osp obuf blo zlo bhi zhi iLo iF iS iT iHi iRO iGOT iPSZ xt1 xt2 lo hi Hd HwL US HUCH Hk.
  destruct US as [Ppc Prsv Psp Pbuf Pbp Ptop Pbot Pmax (clo & Plo) (cf & Pf) (cs & Ps & Ptag) (ct & Pt) (chi & Phi) (zro & Hzro & Pro) (kg & gb & gz & Hkg & Hgb & Hgz & Pgot) (pb & pz & pc & Ppsz & Ppb & Ppz & Ppz64 & Ppok)
                  Pfal Pfrg Pft1 Pft2 Pnx Pnum].
  pose proof (dn_sden _ _ _ _ _ _ _ _ _ Hd) as Hsd.
  pose proof (dn_own _ _ _ _ _ _ _ _ _ Hd) as Hown.
  set (H := Hof E M model) in *. set (msr := restrict H ms) in *.
  pose proof (sden_0 _ _ _ _ Hsd) as Hd0.
  assert (Hsvc : ms_svc_pending ms = None) by (destruct Hd0 as (_ & X & _); exact X).
  assert (Hrv : ms_resv ms = None).
  { destruct Hd0 as (_ & _ & X & _). cbn [mrg s_resv] in X. rewrite Prsv in X. cbn [rsv_ok] in X. exact X. }
  set (SPv := bv_unsigned (lden E spl)) in *.
  assert (Hal : SPv mod 16 = 0) by (pose proof (mrg_fact0 E L S msr _ Hd0 Pfal) as X; cbn [fact_ok] in X; exact X).
  assert (Hrg : lo <= SPv <= hi) by (pose proof (mrg_fact0 E L S msr _ Hd0 Pfrg) as X; cbn [fact_ok] in X; exact X).
  set (V1 := bv_unsigned (E xt1)) in *. set (V2 := bv_unsigned (E xt2)) in *.
  assert (HV1 : 4294901759 <= V1 <= 4294967295) by (pose proof (mrg_fact0 E L S msr _ Hd0 Pft1) as X; cbn [fact_ok] in X; rewrite lden_lvar in X; exact X).
  assert (HV2 : 0 <= V2 <= 7) by (pose proof (mrg_fact0 E L S msr _ Hd0 Pft2) as X; cbn [fact_ok] in X; rewrite lden_lvar in X; exact X).
  destruct Pnum as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16 & N17).
  set (TOP := 4096 + 32768 * V1 + 4096 * V2) in *.
  set (SP := SPv + osp). set (BUF := SPv + obuf).
  assert (HSPr0 : 2^46 + 8192 <= SPv <= 2^47) by lia.
  assert (HT : 2^47 - 2^32 <= TOP <= 2^47) by (unfold TOP; lia).
  (* [comment removed for export] *)
  assert (ES : bv_unsigned (lden E spl) = SPv) by reflexivity.
  assert (R2 : getr (ms_regs ms) (Z_to_bv 5 2) = wa SP) by exact (reg_off0 E L S msr 2 spl osp SPv Hd0 Psp ES ltac:(unfold two64; lia)).
  assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = wa BUF) by exact (reg_off0 E L S msr 10 spl obuf SPv Hd0 Pbuf ES ltac:(unfold two64; lia)).
  assert (R12 : getr (ms_regs ms) (Z_to_bv 5 12) = wa SPv).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E L S msr (Z_to_bv 5 12) _ Hd0 Pbp). unfold SPv. rewrite wa_u. reflexivity. }
  assert (R13 : getr (ms_regs ms) (Z_to_bv 5 13) = wa TOP) by (apply (reg_lin20 E L S msr 13 _ _ _ _ _ _ Hd0 Ptop); reflexivity).
  assert (R14 : getr (ms_regs ms) (Z_to_bv 5 14) = wa (TOP - 8388608)).
  { apply (reg_lin20 E L S msr 14 _ _ _ _ _ _ Hd0 Pbot). fold V1 V2. unfold eqm.
    replace (18446744073701167104 + 32768 * V1 + 4096 * V2) with ((TOP - 8388608) + 1 * two64) by (unfold TOP, two64; lia).
    rewrite Z_mod_plus_full. reflexivity. }
  assert (R15 : getr (ms_regs ms) (Z_to_bv 5 15) = wa 30).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E L S msr (Z_to_bv 5 15) _ Hd0 Pmax). rewrite lden_lconst. reflexivity. }
  set (PCv := bv_unsigned (getr (ms_regs ms) (Z_to_bv 5 11))).
  assert (R11 : getr (ms_regs ms) (Z_to_bv 5 11) = wa PCv) by (unfold PCv; rewrite wa_u; reflexivity).
  assert (HPC : 0 <= PCv < 2^64) by (unfold PCv; apply bv_unsigned_in_range).
  (* [comment removed for export] *)
  pose proof (mrg_rg0 E L S msr iLo _ Hd0 Plo) as Rlo. pose proof (mrg_rg0 E L S msr iF _ Hd0 Pf) as Rf.
  pose proof (mrg_rg0 E L S msr iS _ Hd0 Ps) as Rs. pose proof (mrg_rg0 E L S msr iT _ Hd0 Pt) as Rt.
  pose proof (mrg_rg0 E L S msr iHi _ Hd0 Phi) as Rhi. pose proof (mrg_rg0 E L S msr iRO _ Hd0 Pro) as Rro.
  pose proof (mrg_rg0 E L S msr iGOT _ Hd0 Pgot) as Rgot. pose proof (mrg_rg0 E L S msr iPSZ _ Hd0 Ppsz) as Rpsz.
  assert (Ebase2 : forall b, -8192 <= b <= 0 -> bv_unsigned (lden E (laddc spl b)) = SPv + b).
  { clear - ES HSPr0. intros b Hb. rewrite lden_laddc, ES, u_small64; unfold two64; lia. }
  pose proof (unw_wr0 E (ms_mem msr) spl SPv osp obuf blo zlo bhi zhi clo cf cs ct chi ES ltac:(lia) N5 N6 N7 N8 N9 N10 N16 N17 N11 N12 N13 N14 N15
                Rlo Rf Rs Rt Rhi) as Wst.
  pose proof (ro_none_z _ _ _ Hzro Rro) as Bro. pose proof (got_word_g _ _ _ _ _ Hkg Hgb Hgz Rgot) as HGOT. pose proof (psz_word _ _ _ _ _ Rpsz Ppb Ppz Ppz64 Ppok) as HPSZ.
  assert (HSPr : 2^46 + 8192 <= SPv <= 2^47) by lia.
  assert (Hstk : stk_ok SEGS (ms_mem msr) (wa SP) 1024).
  { clear - Wst HSPr N3 N5 N6 N15. intros a k Ha Hk'. rewrite u_wa_small in Ha, Hk' by (unfold SP; lia).
    apply store_ok_of_all; [pose proof (bv_unsigned_in_range _ a); unfold SP in *; lia|].
    intros x Hx. pose proof (bv_unsigned_in_range _ x) as Rx. destruct (Wst (bv_unsigned x) ltac:(left; unfold SP in *; lia)) as [_ W].
    rewrite Z_to_bv_bv_unsigned in W. exact W. }
  assert (HWB : forall d k, 0 <= d -> d + Z.of_nat k <= 2048 -> store_ok SEGS (ms_mem msr) (wa (BUF + 8 + d)) k = true).
  { clear - Wst HSPr N3 N5 N6 N15. intros d k Hd' Hk'. apply store_ok_of_all; [rewrite u_wa_small by (unfold BUF; lia); unfold BUF; lia|].
    intros x Hx. rewrite u_wa_small in Hx by (unfold BUF; lia). pose proof (bv_unsigned_in_range _ x) as Rx.
    destruct (Wst (bv_unsigned x) ltac:(right; unfold BUF in *; lia)) as [_ W]. rewrite Z_to_bv_bv_unsigned in W. exact W. }
  assert (HBAND : TOP - 8388608 < SPv -> uch (ms_mem msr) TOP SPv) by (intros _; exact HUCH).
  set (fx1 := mkFP (ms_fregs ms) (ms_fcsr ms)).
  destruct (@uw_contract fx1 (ms_rom ms) (ms_mem msr) (ms_regs ms) SP BUF PCv SPv TOP (TOP - 8388608))
    as (R & m' & sz & Hms & HK & Hsz & Hrd & Hfr & Hgr).
  all: try (replace (2%bv : reg) with (Z_to_bv 5 2) by (apply bv_eq; reflexivity); exact R2).
  all: try (replace (10%bv : reg) with (Z_to_bv 5 10) by (apply bv_eq; reflexivity); exact R10).
  all: try (replace (11%bv : reg) with (Z_to_bv 5 11) by (apply bv_eq; reflexivity); exact R11).
  all: try (replace (12%bv : reg) with (Z_to_bv 5 12) by (apply bv_eq; reflexivity); exact R12).
  all: try (replace (13%bv : reg) with (Z_to_bv 5 13) by (apply bv_eq; reflexivity); exact R13).
  all: try (replace (14%bv : reg) with (Z_to_bv 5 14) by (apply bv_eq; reflexivity); exact R14).
  all: try (replace (15%bv : reg) with (Z_to_bv 5 15) by (apply bv_eq; reflexivity); exact R15).
  all: try exact Hstk.
  all: try exact HWB.
  all: try exact HGOT.
  all: try exact HPSZ.
  all: try exact Bro.
  all: try exact HBAND.
  all: try exact HPC.
  all: match goal with |- realizes_cfg _ _ _ _ => idtac | |- _ => unfold SP, BUF; clear - HSPr HT Hal N3 N4 N5 N6 N15; try lia end.
  all: match goal with |- realizes_cfg _ _ _ _ => idtac | |- ?G => idtac "REMAIN" G; fail end.
  set (msr' := @mkst fx1 R (wa 0x82a28) m' (ms_rom ms)).
  assert (Hpc0 : ms_pc_val ms = wa 0x82908) by (destruct Hd0 as (X & _); cbn [mrg s_pc] in X; rewrite Ppc in X; exact X).
  assert (Hst : isteps SEGS msr msr').
  { unfold msr. rewrite (restrict_mkst H ms Hsvc Hrv), Hpc0. apply isteps_of_msteps. exact Hms. }
  (* [comment removed for export] *)
  assert (HinW : forall x, WUW SP BUF (bv_unsigned x) -> exists i R0, In i [iF; iS; iT] /\ nth_error (s_rgs L) i = Some R0 /\ in_rg E R0 x).
  { intros x Hw. unfold WUW, SP, BUF in Hw. destruct Hw as [Hw|[Hw|Hw]].
    - exists iF, (RG (laddc spl (osp - 64)) (lconst 64) RW cf). split; [left; reflexivity|]. split; [exact Pf|].
      apply (stk_in0 E spl _ _ _ SPv x ES); clear - Hw HSPr0 N3 N5 N6 N15; lia.
    - exists iS, (RG (laddc spl (obuf + 8)) (lconst 8) RW cs). split; [right; left; reflexivity|]. split; [exact Ps|].
      apply (stk_in0 E spl _ _ _ SPv x ES); clear - Hw HSPr0 N3 N5 N6 N15; lia.
    - exists iT, (RG (laddc spl (obuf + 16)) (lconst 240) RW ct). split; [right; right; left; reflexivity|]. split; [exact Pt|].
      apply (stk_in0 E spl _ _ _ SPv x ES); clear - Hw HSPr0 N3 N5 N6 N15; lia. }
  assert (Hm_other : forall x, ~ WUW SP BUF (bv_unsigned x) -> ms_mem msr' x = ms_mem msr x).
  { intros x H1. cbn [msr' mkst ms_mem]. rewrite <- (wa_u x). apply Hfr; [apply bv_unsigned_in_range | exact H1]. }
  assert (Hout_W : forall x, outside E (s_rgs (mrg L S)) x -> ~ WUW SP BUF (bv_unsigned x)).
  { intros x Hout Hw. destruct (HinW x Hw) as (i & R0 & Hi & HR0 & Hin). unfold outside in Hout. rewrite Forall_forall in Hout.
    cbn [mrg s_rgs] in Hout. specialize (Hout R0 ltac:(apply in_or_app; left; exact (nth_error_In _ _ HR0))).
    unfold in_rg in Hin. lia. }
  apply (den_hand_w0 SEGS cfg LIMIT model0 Hwx mem0 L S E M ms model T 0x82a28 KALLk [iF; iS; iT]
           (fun mr => rd mr (BUF + 8) 4 sz /\ (forall j, 4 <= j < 8 -> rd1 SEGS mr (Z_to_bv 64 (BUF + 8 + j)) = Some (Z_to_bv 8 0)) /\
              (forall w, outside E (s_rgs (mrg L S)) (Z_to_bv 64 w) -> own_pt E M w -> mr (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w))) Hd HwL).
  { intros i R0 Hi HR0. destruct Hi as [<-|[<-|[<-|[]]]]; [rewrite Pf in HR0 | rewrite Ps in HR0 | rewrite Pt in HR0]; injection HR0 as <-; discriminate. }
  { exists msr'. split; [exact Hst|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [|split; [|split; [|split; [|split]]]].
    - intros r Hr. destruct (kall_cases r Hr) as (k & Hk' & ->). change (ms_regs msr') with R. exact (HK k Hk').
    - intros x Hx _. apply Hm_other. intros Hw. apply Hx. exact (HinW x Hw).
    - intros w _ Hout _. apply Hm_other. apply Hout_W. exact Hout.
    - intros w Hfz. pose proof (dn_frz _ _ _ _ _ _ _ _ _ Hd) as Hfrz.
      destruct Hfz as (p & Hp & Hw). destruct (Hfrz p Hp w Hw) as (_ & Hout & _).
      apply Hm_other. apply Hout_W. exact Hout.
    - intros i R0 j Hi HR0 Hj. destruct Hi as [<-|[<-|[<-|[]]]].
      + rewrite Pf in HR0. injection HR0 as <-. unfold rsz in Hj. cbn [rg_size rg_base] in Hj |- *. rewrite lden_lconst, u_small64 in Hj by (unfold two64; lia).
        rewrite (Ebase2 (osp - 64) ltac:(clear - N15 N5 N6; lia)). destruct (Wst (SPv + (osp - 64) + j) ltac:(left; clear - Hj N15 N5 N6; lia)) as [B1' B2'].
        destruct (grows_rw SEGS (ms_mem msr) m' _ Hgr B1' B2') as [C1 C2]. split; [exact C1 | intros _; exact C2].
      + rewrite Ps in HR0. injection HR0 as <-. unfold rsz in Hj. cbn [rg_size rg_base] in Hj |- *. rewrite lden_lconst, u_small64 in Hj by (unfold two64; lia).
        rewrite (Ebase2 (obuf + 8) ltac:(clear - N15 N5 N6; lia)). destruct (Wst (SPv + (obuf + 8) + j) ltac:(right; clear - Hj N15 N5 N6; lia)) as [B1' B2'].
        destruct (grows_rw SEGS (ms_mem msr) m' _ Hgr B1' B2') as [C1 C2]. split; [exact C1 | intros _; exact C2].
      + rewrite Pt in HR0. injection HR0 as <-. unfold rsz in Hj. cbn [rg_size rg_base] in Hj |- *. rewrite lden_lconst, u_small64 in Hj by (unfold two64; lia).
        rewrite (Ebase2 (obuf + 16) ltac:(clear - N15 N5 N6; lia)). destruct (Wst (SPv + (obuf + 16) + j) ltac:(right; clear - Hj N15 N5 N6; lia)) as [B1' B2'].
        destruct (grows_rw SEGS (ms_mem msr) m' _ Hgr B1' B2') as [C1 C2]. split; [exact C1 | intros _; exact C2].
    - split; [exact Hrd|]. split.
      { intros j Hj. assert (Hnw : ~ WUW SP BUF (bv_unsigned (Z_to_bv 64 (BUF + 8 + j)))).
        { rewrite u_small64 by (unfold BUF, two64; clear - Hj HSPr0 N15 N5 N6; lia). unfold WUW, SP, BUF. clear - Hj N5; lia. }
        unfold rd1. rewrite (Hm_other _ Hnw). fold (rd1 SEGS (ms_mem msr) (Z_to_bv 64 (BUF + 8 + j))).
        pose proof Rs as Rs'. destruct Rs' as (_ & _ & _ & HTr). specialize (HTr (Pos.of_succ_nat (Z.to_nat j)) (BK 0) (Ptag (Z.to_nat j) ltac:(lia))) as [_ X].
        rewrite Zpos_P_of_succ_nat, Z2Nat.id in X by lia. cbn [rg_base] in X. rewrite (Ebase2 (obuf + 8) ltac:(clear - N15 N5 N6; lia)) in X.
        replace (SPv + (obuf + 8) + (Z.succ j - 1)) with (BUF + 8 + j) in X by (unfold BUF; lia). exact X. }
      intros w Hout Hown'. cbn [msr' mkst ms_mem]. rewrite <- (wa_u (Z_to_bv 64 w)).
      rewrite Hfr; [|apply bv_unsigned_in_range | apply Hout_W; exact Hout]. rewrite wa_u.
      destruct Hown' as (p & Hp & Hw). destruct (Hown p Hp w Hw) as [Hv Hm]. fold H in Hv. cbn [msr restrict ms_mem]. unfold mrestrict. rewrite Hv. exact (Hm Hout). }
  (* [comment removed for export] *)
  intros E' ms' model' HD' Ha' Hfz' (mr & (Hrd' & Htag' & Hom) & Hvis).
  set (Lh := hand_post L 0x82a28 KALLk [iF; iS; iT]) in *.
  assert (HwfM : sm_wf (s_next L) M = true) by exact (dn_wf _ _ _ _ _ _ _ _ _ Hd).
  assert (HbwS : bases_wf (s_next L) (s_rgs (mrg L S)) = true) by exact (dn_bases _ _ _ _ _ _ _ _ _ Hd).
  assert (Hsh : shape (s_rgs (mrg Lh S)) = shape (s_rgs (mrg L S))).
  { cbn [mrg s_rgs]. unfold Lh, hand_post. cbn [s_rgs]. unfold shape. rewrite !map_app. f_equal.
    pose proof (empty_at_shape [iF; iS; iT] (s_rgs L) 0) as Hs. unfold shape in Hs. exact Hs. }
  assert (HD2 : DEN SEGS LIMIT model0 mem0 E' (mrg Lh S) M ms' model').
  { apply (den_snap SEGS LIMIT model0 (ms_mem ms') mem0 E' _ M ms' model' HD').
    - intros w Hw. symmetry. apply Hfz'. exact (proj1 (frz_pt_agree (s_next L) E E' M w HwfM Ha') Hw).
    - intros w Hw Hout. symmetry.
      assert (Hw0 : own_pt E M w) by exact (proj1 (own_pt_agree (s_next L) E E' M w HwfM Ha') Hw).
      assert (Hout0 : outside E (s_rgs (mrg L S)) (Z_to_bv 64 w)) by exact (outside_agree_shape _ E E' _ _ _ HbwS Ha' Hsh Hout).
      rewrite (Hvis (Z_to_bv 64 w)); [exact (Hom w Hout0 Hw0)|].
      destruct Hw0 as (p & Hp & Hpw). exact (proj1 (Hown p Hp w Hpw)). }
  set (x := (s_next L + 33)%positive).
  assert (Px2 : (x < Pos.succ x)%positive) by (clear; lia).
  assert (Px3 : (s_next L < x)%positive) by (unfold x; clear; lia).
  set (E2 := upd E' x (Z_to_bv 64 sz)).
  assert (Ha2 : agree x E' E2) by apply agree_upd.
  assert (HE2x : E2 x = Z_to_bv 64 sz) by (unfold E2, upd; rewrite Pos.eqb_refl; reflexivity).
  pose proof (den_agree SEGS LIMIT model0 mem0 E' E2 _ M ms' model' HD2 Ha2) as HD3.
  pose proof (den_bump SEGS LIMIT model0 mem0 E2 _ M ms' model' (Pos.succ x) HD3 (Pos.lt_le_incl _ _ Px2)) as HD4.
  assert (HiS : (iS < length (s_rgs L))%nat) by (apply nth_error_Some; rewrite Ps; discriminate).
  set (RS := RG (laddc spl (obuf + 8)) (lconst 8) RW TEmpty).
  assert (HnS0 : nth_error (s_rgs (bump Lh (Pos.succ x))) iS = Some RS).
  { unfold Lh, hand_post. cbn [bump s_rgs]. rewrite (empty_at_nth_fwd _ _ 0 iS _ Ps). cbn [Nat.add]. rewrite existsb_mid. reflexivity. }
  assert (HnS : nth_error (s_rgs (bump (mrg Lh S) (Pos.succ x))) iS = Some RS).
  { change (bump (mrg Lh S) (Pos.succ x)) with (mrg (bump Lh (Pos.succ x)) S).
    cbn [mrg s_rgs]. rewrite nth_error_app1 by (apply nth_error_Some; rewrite HnS0; discriminate). exact HnS0. }
  assert (E2n2 : forall E'', agree (Pos.succ x) E2 E'' -> lden E'' spl = lden E spl).
  { intros E'' Ha''. assert (Hag : agree (s_next L) E E'').
    { intros y Hy. rewrite (Ha' y Hy), (Ha2 y ltac:(clear - Hy Px3; lia)). apply Ha''. clear - Hy Px3 Px2; lia. }
    exact (lden_agree_wf (s_next L) E E'' spl Pnx Hag). }
  (* [comment removed for export] *)
  assert (HvisS : forall j, (j < 8)%nat -> H (Z_to_bv 64 (BUF + 8 + Z.of_nat j)) = false).
  { intros j Hj. apply (vis_of_rd1 H (ms_mem ms)).
    - destruct (Wst (BUF + 8 + Z.of_nat j) ltac:(right; unfold BUF; clear - Hj N15 N5 N6; lia)) as [W1 _]. exact W1.
    - apply seg_rom_stack. rewrite u_small64 by (unfold BUF, two64; clear - Hj HSPr0 N15 N5 N6; lia). unfold BUF. clear - Hj HSPr0 N15 N5 N6; lia. }
  assert (HD5 : DEN SEGS LIMIT model0 mem0 E2 (put_rg (bump (mrg Lh S) (Pos.succ x)) iS 0 (bvs_of (lvar x) 8)) M ms' model').
  { apply (den_put SEGS LIMIT mem0 model0 E2 _ M ms' model' iS RS 0 _ HD4 HnS); [discriminate | lia | |].
    - intros E'' _. unfold RS, rsz. cbn [rg_size]. rewrite lden_lconst, u_small64 by (unfold two64; lia). cbn. lia.
    - intros E'' Ha'' j b Hj. destruct (nth_bvs8 x j b Hj) as (Hj4 & ->).
      assert (Eu : uE E'' (rg_base RS) = BUF + 8).
      { unfold uE, RS. cbn [rg_base]. rewrite lden_laddc, (E2n2 E'' Ha''). fold SPv. rewrite u_small64 by (unfold two64; clear - HSPr0 N15 N5 N6; lia).
        unfold BUF. clear; lia. }
      rewrite Eu, Z.add_0_r. cbn [bden]. rewrite lden_lvar, <- (Ha'' x Px2), HE2x.
      rewrite u_small64 by (unfold two64; clear - Hsz; lia).
      (* [comment removed for export] *)
      pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ HD4)) as Hd4.
      change (bump (mrg Lh S) (Pos.succ x)) with (mrg (bump Lh (Pos.succ x)) S) in Hd4.
      pose proof (mrg_rg0 E2 (bump Lh (Pos.succ x)) S _ iS RS Hd4 HnS0) as RS4.
      assert (HE2sp : bv_unsigned (lden E2 spl) = SPv) by (rewrite (E2n2 E2 (agree_refl _ _)); reflexivity).
      destruct (stk_rw0 E2 _ spl (obuf + 8) 8 TEmpty SPv (BUF + 8 + Z.of_nat j) RS4 HE2sp ltac:(clear - HSPr0; lia) ltac:(clear - N15 N5 N6; lia) ltac:(lia)
                  ltac:(clear - N15 N5 N6; lia) ltac:(unfold BUF; clear - Hj4; lia)) as [V4 _].
      cbn [restrict ms_mem] in V4.
      assert (Hv2 : Hof E2 M model' (Z_to_bv 64 (BUF + 8 + Z.of_nat j)) = false).
      { apply (vis_of_rd1 _ (ms_mem ms') _ V4). apply seg_rom_stack. rewrite u_small64 by (unfold BUF, two64; clear - Hj4 HSPr0 N15 N5 N6; lia).
        unfold BUF. clear - Hj4 HSPr0 N15 N5 N6; lia. }
      rewrite (rd1_mrestrict_vis _ _ _ Hv2).
      assert (Em : rd1 SEGS (ms_mem ms') (Z_to_bv 64 (BUF + 8 + Z.of_nat j)) = rd1 SEGS mr (Z_to_bv 64 (BUF + 8 + Z.of_nat j))).
      { unfold rd1. rewrite (Hvis _ (HvisS j Hj4)). reflexivity. }
      rewrite Em. destruct (Nat.lt_ge_cases j 4) as [Hj3|Hj3].
      + rewrite (rdn_rd1 mr (BUF + 8) 4 _ j ltac:(unfold BUF; clear - HSPr0 N15 N5 N6; lia) ltac:(unfold BUF; cbn; clear - HSPr0 N15 N5 N6; lia) Hrd' Hj3).
        unfold word_to_le_bytes. rewrite nth_Z_to_le_bytes by exact Hj3. rewrite u_wa_small by (clear - Hsz; lia). reflexivity.
      + rewrite (Htag' (Z.of_nat j) ltac:(lia)). f_equal. rewrite Z.shiftr_eq_0; [reflexivity | clear - Hsz; lia |].
        apply (Z.le_lt_trans _ (Z.log2 30)); [apply Z.log2_le_mono; lia | cbn; lia]. }
  assert (HD6 : DEN SEGS LIMIT model0 mem0 E2 (add_fact (put_rg (bump (mrg Lh S) (Pos.succ x)) iS 0 (bvs_of (lvar x) 8)) (FRange (lvar x) 1 30)) M ms' model').
  { apply (den_addfact SEGS LIMIT model0 mem0 E2 _ M ms' model' _ HD5). intros E'' Ha''. cbn [fact_ok].
    rewrite lden_lvar. rewrite put_rg_next0 in Ha''. cbn [bump s_next] in Ha''.
    rewrite <- (Ha'' x Px2), HE2x, u_small64 by (unfold two64; clear - Hsz; lia). clear - Hsz; lia. }
  apply (Hk E2 ms' model').
  - rewrite unw_res_mrg0 by exact HiS. exact HD6.
  - intros y Hy. rewrite (Ha' y Hy). apply Ha2. clear - Hy Px3; lia.
Qed.
End UnwMain0.
(* [comment removed for export] *)
