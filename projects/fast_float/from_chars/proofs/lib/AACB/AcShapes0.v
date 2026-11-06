(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem FxSubst FxEnt FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst AcSteps.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp.

Module AcShapes.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem FxSubst FxEnt FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst AcSteps.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcSteps OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp.AcPutApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition rg_hdr_b (o : option region) (b z : lin) (k : rkind) : bool :=
  match o with Some R => (lin_eqb (rg_base R) b && lin_eqb (rg_size R) z && rkind_eqb (rg_kind R) k)%bool | None => false end.
Lemma rg_hdr_b_sound : forall o b z k, rg_hdr_b o b z k = true -> exists c, o = Some (RG b z k c).
Proof.
  intros [[b0 z0 k0 c0]|] b z k H; [|discriminate]. cbn in H. apply andb_prop in H as [H Hk]. apply andb_prop in H as [Hb Hz].
  apply lin_eqb_eq in Hb, Hz. apply rkind_eqb_eq in Hk. subst. exists c0. reflexivity.
Qed.
Definition rg_is_b (o : option region) (R : region) : bool := match o with Some R' => rg_eqb R' R | None => false end.
Lemma rg_is_b_sound : forall o R, rg_is_b o R = true -> o = Some R.
Proof. intros [R'|] R H; [|discriminate]. cbn in H. rewrite (rg_eqb_eq _ _ H). reflexivity. Qed.
Definition infact_b (f : fact) (fs : list fact) : bool := existsb (fact_eqb f) fs.
Lemma infact_b_sound : forall f fs, infact_b f fs = true -> In f fs.
Proof. intros f fs H. apply existsb_exists in H as (g & Hg & He). apply fact_eqb_eq in He. subst. exact Hg. Qed.
Definition rsv_none_b (r : rsv) : bool := match r with RNone => true | _ => false end.
Lemma rsv_none_b_sound : forall r, rsv_none_b r = true -> r = RNone. Proof. intros [| |] H; try discriminate; reflexivity. Qed.

(* [comment removed for export] *)
Definition psz_b (o : option region) : bool :=
  match o with
  | Some (RG b z RZ c) => match is_const b, is_const z with
                          | Some b', Some z' =>
                              (* [comment removed for export] *)
                              if Z.leb 0 b' then if Z.leb b' 1532192 then if Z.leb (1532192 + 8) (b' + z') then if Z.ltb (b' + z') two64 then
                              if lin_eqb b (lconst b') then if lin_eqb z (lconst z') then psz_ok c (1532192 - b') else false else false
                              else false else false else false else false
                          | _, _ => false
                          end
  | _ => false
  end.
Lemma psz_b_sound : forall o, psz_b o = true -> exists b z c, o = Some (RG (lconst b) (lconst z) RZ c) /\ 0 <= b <= 1532192 /\
  1532192 + 8 <= b + z /\ b + z < two64 /\ psz_ok c (1532192 - b) = true.
Proof.
  intros [[b z k c]|] H; [|discriminate]. unfold psz_b in H. destruct k; try discriminate.
  destruct (is_const b) as [b'|]; [|discriminate]. destruct (is_const z) as [z'|]; [|discriminate].
  repeat match type of H with (if ?t then _ else false) = true => let Et := fresh "Et" in destruct t eqn:Et; [|discriminate H] end.
  repeat match goal with H : lin_eqb _ _ = true |- _ => apply lin_eqb_eq in H | H : Z.leb _ _ = true |- _ => apply Z.leb_le in H
                      | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H end. subst.
  exists b', z', c. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia | assumption].
Qed.

Definition tag0_b (o : option region) : bool :=
  match o with Some R => forallb (fun j => match tget (Pos.of_succ_nat j) (rg_cont R) with Some (BK 0) => true | _ => false end) [4;5;6;7]%nat | None => false end.
Lemma tag0_b_sound : forall o b z k c, o = Some (RG b z k c) -> tag0_b o = true -> forall j, (4 <= j < 8)%nat -> tget (Pos.of_succ_nat j) c = Some (BK 0).
Proof.
  intros o b z k c -> H j Hj. unfold tag0_b in H. rewrite forallb_forall in H. cbn [rg_cont] in H.
  assert (Hin : In j [4;5;6;7]%nat) by (cbn; lia). specialize (H j Hin).
  destruct (tget (Pos.of_succ_nat j) c) as [[v|l jj]|]; try discriminate. destruct v; try discriminate; reflexivity.
Qed.
Definition unw_shape_b (L : sst) (osp obuf blo zlo bhi zhi : Z) (iLo iF iS iT iHi iRO iGOT iPSZ : nat) (xt1 xt2 : positive) (lo hi : Z) : bool :=
  let R := s_regs L in let G := s_rgs L in let F := s_facts L in
  (Z.eqb (s_pc L) 0x82908 && rsv_none_b (s_resv L) &&
   lin_eqb (rget R (rk 2)) (laddc (lvar 2) osp) && lin_eqb (rget R (rk 10)) (laddc (lvar 2) obuf) && lin_eqb (rget R (rk 12)) (lvar 2) &&
   lin_eqb (rget R (rk 13)) (TOPL xt1 xt2) && lin_eqb (rget R (rk 14)) (BOTL xt1 xt2) && lin_eqb (rget R (rk 15)) (lconst 30) &&
   rg_hdr_b (nth_error G iLo) (laddc (lvar 2) blo) (lconst zlo) RW && rg_hdr_b (nth_error G iF) (laddc (lvar 2) (osp - 64)) (lconst 64) RW &&
   rg_hdr_b (nth_error G iS) (laddc (lvar 2) (obuf + 8)) (lconst 8) RW && tag0_b (nth_error G iS) &&
   rg_hdr_b (nth_error G iT) (laddc (lvar 2) (obuf + 16)) (lconst 240) RW &&
   rg_hdr_b (nth_error G iHi) (laddc (lvar 2) bhi) (lconst zhi) RW &&
   rg_is_b (nth_error G iRO) (RG (lconst 65536) (lconst 77824) RO TEmpty) && rg_is_b (nth_error G iGOT) (RG (lconst 907848) (lconst 8192) RI TEmpty) &&
   psz_b (nth_error G iPSZ) &&
   infact_b (FMod (lvar 2) 4 0) F && infact_b (FRange (lvar 2) lo hi) F && infact_b (FRange (lvar xt1) 4294901759 4294967295) F &&
   infact_b (FRange (lvar xt2) 0 7) F && Pos.ltb 2 (s_next L) &&
   Z.leb (2^46 + 8192) lo && Z.leb hi (2^47) && Z.eqb (osp mod 16) 0 && Z.eqb (obuf mod 8) 0 && Z.leb osp obuf && Z.leb (obuf + 2056) 0 &&
   Z.leb (-8192) blo && Z.leb blo (osp - 1024) && Z.leb (osp - 64) (blo + zlo) && Z.leb 0 zlo && Z.leb bhi (obuf + 256) &&
   Z.leb (obuf + 2056) (bhi + zhi) && Z.leb 0 zhi && Z.leb (bhi + zhi) 0 && Z.leb (-8192) (osp - 1024) && Z.leb (blo + zlo) 0 && Z.leb (-8192) bhi)%bool.

Lemma unw_shape_b_sound : forall L osp obuf blo zlo bhi zhi iLo iF iS iT iHi iRO iGOT iPSZ xt1 xt2 lo hi,
  unw_shape_b L osp obuf blo zlo bhi zhi iLo iF iS iT iHi iRO iGOT iPSZ xt1 xt2 lo hi = true ->
  unw_shape L osp obuf blo zlo bhi zhi iLo iF iS iT iHi iRO iGOT iPSZ xt1 xt2 lo hi.
Proof.
  intros L osp obuf blo zlo bhi zhi iLo iF iS iT iHi iRO iGOT iPSZ xt1 xt2 lo hi H. unfold unw_shape_b in H.
  repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?] end.
  repeat match goal with H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H | H : Z.leb _ _ = true |- _ => apply Z.leb_le in H
                      | H : Pos.ltb _ _ = true |- _ => apply Pos.ltb_lt in H | H : lin_eqb _ _ = true |- _ => apply lin_eqb_eq in H
                      | H : rsv_none_b _ = true |- _ => apply rsv_none_b_sound in H | H : infact_b _ _ = true |- _ => apply infact_b_sound in H
                      | H : rg_is_b _ _ = true |- _ => apply rg_is_b_sound in H | H : rg_hdr_b _ _ _ _ = true |- _ => apply rg_hdr_b_sound in H
                      | H : psz_b _ = true |- _ => apply psz_b_sound in H end.
  constructor; try assumption.
  - match goal with H : exists c, nth_error (s_rgs L) iS = Some _ |- _ => destruct H as (c & Hc) end. exists c. split; [exact Hc|].
    apply (tag0_b_sound _ _ _ _ _ Hc). assumption.
  - repeat split; assumption.
Qed.

Definition put_shape_b (L : sst) (xsz : positive) (iA1 iFt iRO : nat) (lo hi : Z) : bool :=
  let R := s_regs L in let G := s_rgs L in let F := s_facts L in
  (Z.eqb (s_pc L) 0x81f7c && rsv_none_b (s_resv L) &&
   lin_eqb (rget R (rk 2)) (laddc (lvar 2) (-2272)) && lin_eqb (rget R (rk 10)) (laddc (lvar 2) (-2112)) && lin_eqb (rget R (rk 11)) (lvar xsz) &&
   rg_hdr_b (nth_error G iA1) (laddc (lvar 2) (-4320)) (lconst 2048) RW && rg_hdr_b (nth_error G iFt) (laddc (lvar 2) (-2112)) (lconst 240) RW &&
   rg_is_b (nth_error G iRO) (RG (lconst 65536) (lconst 77824) RO TEmpty) &&
   infact_b (FRange (lvar xsz) 1 30) F && infact_b (FMod (lvar 2) 4 0) F && infact_b (FRange (lvar 2) lo hi) F &&
   Z.leb (2^46 + 8192) lo && Z.leb hi (2^47))%bool.
Lemma put_shape_b_sound : forall L xsz iA1 iFt iRO lo hi, put_shape_b L xsz iA1 iFt iRO lo hi = true -> put_shape L xsz iA1 iFt iRO lo hi.
Proof.
  intros L xsz iA1 iFt iRO lo hi H. unfold put_shape_b in H.
  repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?] end.
  repeat match goal with H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H | H : Z.leb _ _ = true |- _ => apply Z.leb_le in H
                      | H : lin_eqb _ _ = true |- _ => apply lin_eqb_eq in H
                      | H : rsv_none_b _ = true |- _ => apply rsv_none_b_sound in H | H : infact_b _ _ = true |- _ => apply infact_b_sound in H
                      | H : rg_is_b _ _ = true |- _ => apply rg_is_b_sound in H | H : rg_hdr_b _ _ _ _ = true |- _ => apply rg_hdr_b_sound in H end.
  constructor; try assumption. split; assumption.
Qed.
(* [comment removed for export] *)
End AcShapes.

From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp0.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcSteps OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp.AcPutApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcShapes0.AcShapes OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp0.

Module AcPutAppG.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatSim StoreOk ShapeSet RealizesCfg AsanAcct AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxPlan FxFrame FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_put AXG_put3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put3 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp.AXG_put5.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcHand.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcDenW AcHand AcHand0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp0.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt.AcShift OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.AcMrg OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand.AcMrg0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDenW OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp.AcPutApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section PutMainG.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap SEGS.

(* [comment removed for export] *)
Record put_shapeG (L : sst) (spl : lin) (otr : Z) (xsz : positive) (iA1 iFt iRO : nat) (lo hi : Z) : Prop := {
  pg_pc   : s_pc L = 0x81f7c ;
  pg_rsv  : s_resv L = RNone ;
  pg_sp   : rget (s_regs L) (rk 2) = spl ;
  pg_tr   : rget (s_regs L) (rk 10) = laddc spl otr ;
  pg_sz   : rget (s_regs L) (rk 11) = lvar xsz ;
  pg_a1   : exists c, nth_error (s_rgs L) iA1 = Some (RG (laddc spl (-2048)) (lconst 2048) RW c) ;
  pg_f    : exists c, nth_error (s_rgs L) iFt = Some (RG (laddc spl otr) (lconst 240) RW c) ;
  pg_ro   : exists zro, 77824 <= zro < 2^32 /\ nth_error (s_rgs L) iRO = Some (RG (lconst 65536) (lconst zro) RO TEmpty) ;
  pg_fsz  : In (FRange (lvar xsz) 1 30) (s_facts L) ;
  pg_fal  : In (FMod spl 4 0) (s_facts L) ;
  pg_frg  : In (FRange spl lo hi) (s_facts L) ;
  pg_rng  : 2^46 + 8192 <= lo /\ hi + otr + 240 <= 2^47 /\ 0 <= otr <= 8192
}.

#[using="Hwx"] Theorem den_put_appG : forall mem0 L S E M ms model T spl otr xsz iA1 iFt iRO lo hi D1 B1 nd F st,
  DEN SEGS LIMIT model0 mem0 E (mrg L S) M ms model ->
  state_wf L = true -> put_shapeG L spl otr xsz iA1 iFt iRO lo hi ->
  INV_D mem0 D1 B1 nd F st -> nd <= 65532 -> F + 31 <= 1048000 ->
  (forall x, 0 <= x < 2^64 -> downed D1 B1 x -> own_pt E M x /\ outside E (s_rgs (mrg L S)) (wa x) /\ ~ frz_pt E M x) ->
  D1 + 1048576 + 2048 <= bv_unsigned (lden E spl) -> B1 + 8388608 + 2048 <= bv_unsigned (lden E spl) ->
  (forall E' ms' model', DEN SEGS LIMIT model0 (ms_mem ms') E' (mrg (hand_post L 0x821f0 KALLk [iA1]) S) M ms' model' ->
     agree (s_next L) E E' -> (forall w, frz_pt E M w -> ms_mem ms' (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)) ->
     (exists nd' F' st', INV_D (ms_mem ms') D1 B1 nd' F' st' /\ nd <= nd' <= nd + 1 /\ F <= F' <= F + 31) ->
     (forall x, 0 <= x < 2^64 -> Hof E M model (wa x) = false -> ~ (bv_unsigned (lden E spl) - 2048 <= x < bv_unsigned (lden E spl)) -> ~ downed D1 B1 x ->
        ms_mem ms' (wa x) = ms_mem ms (wa x)) ->
     realizes_cfg SEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg SEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros mem0 L S E M ms model T spl otr xsz iA1 iFt iRO lo hi D1 B1 nd F st Hd HwL PS HI Hnd HF HDN HD1 HB1 Hk.
  destruct PS as [Ppc Prsv Psp Ptr Psz (c1 & Pa1) (c6 & Pf) (zro & Hzro & Pro) Pfsz Pfal Pfrg Prng].
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
  set (SZv := bv_unsigned (E xsz)) in *.
  assert (Hsz : 1 <= SZv <= 30) by (pose proof (mrg_fact0 E L S msr _ Hd0 Pfsz) as X; cbn [fact_ok] in X; rewrite lden_lvar in X; exact X).
  assert (HSPr : 0 <= SPv < two64) by (pose proof (bv_unsigned_in_range _ (lden E spl)) as X; exact X).
  set (SP := SPv). set (TR := SPv + otr).
  assert (R2 : getr (ms_regs ms) (Z_to_bv 5 2) = wa SP).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E L S msr (Z_to_bv 5 2) _ Hd0 Psp). unfold wa, SP, SPv. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = wa TR).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E L S msr (Z_to_bv 5 10) _ Hd0 Ptr). unfold wa. apply bv_eq. rewrite lden_laddc; fold SPv. reflexivity. }
  assert (R11 : getr (ms_regs ms) (Z_to_bv 5 11) = wa SZv).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E L S msr (Z_to_bv 5 11) _ Hd0 Psz). rewrite lden_lvar. unfold SZv. rewrite wa_u. reflexivity. }
  (* [comment removed for export] *)
  pose proof (mrg_rg0 E L S msr iA1 _ Hd0 Pa1) as Ra1. pose proof (mrg_rg0 E L S msr iFt _ Hd0 Pf) as Rf. pose proof (mrg_rg0 E L S msr iRO _ Hd0 Pro) as Rro.
  assert (Ba1 : forall x, SP - 2048 <= x < SP -> rd1 SEGS (ms_mem msr) (Z_to_bv 64 x) <> None /\ wview SEGS (ms_mem msr) (Z_to_bv 64 x) <> None).
  { intros x Hx. apply (rg_rw_pt _ _ _ x Ra1 eq_refl). cbn [rg_base].
    assert (Eb : bv_unsigned (lden E (laddc spl (-2048))) = SPv - 2048) by (rewrite lden_laddc; fold SPv; rewrite u_small64; unfold two64 in *; lia).
    rewrite Eb. unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_small64 by (unfold two64; lia). unfold SP in Hx. lia. }
  assert (Bf : forall x, TR <= x < TR + 240 -> rd1 SEGS (ms_mem msr) (Z_to_bv 64 x) <> None /\ wview SEGS (ms_mem msr) (Z_to_bv 64 x) <> None).
  { intros x Hx. apply (rg_rw_pt _ _ _ x Rf eq_refl). cbn [rg_base].
    assert (Eb : bv_unsigned (lden E (laddc spl otr)) = SPv + otr) by (rewrite lden_laddc; fold SPv; rewrite u_small64; unfold two64 in *; lia).
    rewrite Eb. unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_small64 by (unfold two64; lia). unfold TR in Hx. lia. }
  assert (Bro : forall i, 65536 <= i < 143360 -> ms_mem msr (Z_to_bv 64 i) = None).
  { exact (ro_none_z _ _ _ Hzro Rro). }
  (* [comment removed for export] *)
  assert (Hdep : forall x, 0 <= x < 2^64 -> downed D1 B1 x -> ms_mem msr (wa x) = mem0 (wa x) /\ H (wa x) = false).
  { intros x Hx Hdw. destruct (HDN x Hx Hdw) as ((p & Hp & Hpw) & Hout & _). pose proof (Hown p Hp x Hpw) as [Hv Hm].
    fold H in Hv. unfold wa. split; [|exact Hv]. cbn [msr restrict ms_mem]. unfold mrestrict. rewrite Hv. apply Hm. exact Hout. }
  assert (HI' : INV_D (ms_mem msr) D1 B1 nd F st).
  { apply (INV_D_frame mem0); [exact HI|]. intros x Hx Hdw. exact (proj1 (Hdep x Hx Hdw)). }
  assert (Hstk : stk_ok SEGS (ms_mem msr) (wa SP) 2048).
  { intros a k Ha Hk'. rewrite u_wa_small in Ha, Hk' by (unfold SP; lia). apply store_ok_of_all; [pose proof (bv_unsigned_in_range _ a); unfold SP in *; lia|].
    intros x Hx. pose proof (bv_unsigned_in_range _ x) as Rx. destruct (Ba1 (bv_unsigned x) ltac:(lia)) as [_ W]. rewrite Z_to_bv_bv_unsigned in W. exact W. }
  assert (Hwords : forall i, 0 <= i < SZv -> exists w, 0 <= w < 2^64 /\ rd (ms_mem msr) (TR + 8 * i) 8 w).
  { intros i Hi. destruct (rdn_some (ms_mem msr) (TR + 8 * i) 8 ltac:(unfold TR; lia) ltac:(cbn; unfold TR, two64; lia)) as (bs & Hbs).
    { intros j Hj. cbn in Hj. exact (proj1 (Bf (TR + 8 * i + j) ltac:(lia))). }
    destruct (rd_exists (ms_mem msr) (TR + 8 * i) 8 bs ltac:(lia) Hbs) as (v & Hv1 & Hv2 & Hrd). exists v. split; [lia | exact Hrd]. }
  destruct (@put_contract (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_rom ms) (ms_mem msr) (ms_regs ms) D1 B1 nd F st TR SZv SP HI' Hnd HF)
    as (R & m' & nd' & F' & st' & Hms & HRs & HK & HI2 & Hnd' & HF' & Hfr & Hgr).
  all: try (unfold SP, TR in *; lia).
  all: try exact Hstk.
  all: try exact Hwords.
  all: try exact Bro.
  all: try (replace (2%bv : reg) with (Z_to_bv 5 2) by (apply bv_eq; reflexivity); exact R2).
  all: try (replace (10%bv : reg) with (Z_to_bv 5 10) by (apply bv_eq; reflexivity); exact R10).
  all: try (replace (11%bv : reg) with (Z_to_bv 5 11) by (apply bv_eq; reflexivity); exact R11).
  all: match goal with |- realizes_cfg _ _ _ _ => idtac | |- ?G => idtac "REMAIN" G; fail end.
  set (fx1 := mkFP (ms_fregs ms) (ms_fcsr ms)).
  set (msr' := @mkst fx1 R (wa 0x821f0) m' (ms_rom ms)).
  assert (Hpc0 : ms_pc_val ms = wa 0x81f7c) by (destruct Hd0 as (X & _); cbn [mrg s_pc] in X; rewrite Ppc in X; exact X).
  assert (Hst : isteps SEGS msr msr').
  { unfold msr. rewrite (restrict_mkst H ms Hsvc Hrv), Hpc0. apply isteps_of_msteps. exact Hms. }
  apply (den_hand_w0 SEGS cfg LIMIT model0 Hwx mem0 L S E M ms model T 0x821f0 KALLk [iA1]
           (fun mr => (exists nd' F' st', INV_D mr D1 B1 nd' F' st' /\ nd <= nd' <= nd + 1 /\ F <= F' <= F + 31) /\
                      (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ downed D1 B1 x -> mr (wa x) = ms_mem msr (wa x))) Hd HwL).
  { intros i R0 Hi HR0. destruct Hi as [<-|[]]. rewrite Pa1 in HR0. injection HR0 as <-. discriminate. }
  { exists msr'. split; [exact Hst|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    assert (Ha1 : forall x, (exists i R0, In i [iA1] /\ nth_error (s_rgs L) i = Some R0 /\ in_rg E R0 x) -> SP - 2048 <= bv_unsigned x < SP).
    { intros x (i & R0 & Hi & HR0 & Hin). destruct Hi as [<-|[]]. rewrite Pa1 in HR0. injection HR0 as <-. unfold in_rg in Hin. cbn [rg_base] in Hin.
      assert (Eb : bv_unsigned (lden E (laddc spl (-2048))) = SPv - 2048) by (rewrite lden_laddc; fold SPv; rewrite u_small64; unfold two64 in *; lia).
      rewrite Eb in Hin. unfold rsz in Hin. cbn [rg_size] in Hin. rewrite lden_lconst, u_small64 in Hin by (unfold two64; lia). unfold SP. lia. }
    assert (HinA1 : forall x, SP - 2048 <= bv_unsigned x < SP -> exists i R0, In i [iA1] /\ nth_error (s_rgs L) i = Some R0 /\ in_rg E R0 x).
    { intros x Hx. exists iA1, (RG (laddc spl (-2048)) (lconst 2048) RW c1). split; [left; reflexivity|]. split; [exact Pa1|].
      unfold in_rg. cbn [rg_base].
      assert (Eb : bv_unsigned (lden E (laddc spl (-2048))) = SPv - 2048) by (rewrite lden_laddc; fold SPv; rewrite u_small64; unfold two64 in *; lia).
      rewrite Eb. unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_small64 by (unfold two64; lia). unfold SP in Hx. lia. }
    (* [comment removed for export] *)
    assert (Hnd_rg : forall x, (exists R0, In R0 (s_rgs (mrg L S)) /\ in_rg E R0 x) -> ~ downed D1 B1 (bv_unsigned x)).
    { intros x (R0 & HR0 & Hin) Hdw. destruct (HDN (bv_unsigned x) (bv_unsigned_in_range _ x) Hdw) as (_ & Hout & _).
      rewrite wa_u in Hout. unfold outside in Hout. rewrite Forall_forall in Hout. specialize (Hout R0 HR0). unfold in_rg in Hin. lia. }
    assert (Hm_other : forall x, ~ (SP - 2048 <= bv_unsigned x < SP) -> ~ downed D1 B1 (bv_unsigned x) -> ms_mem msr' x = ms_mem msr x).
    { intros x H1 H2. cbn [msr' mkst ms_mem]. rewrite <- (wa_u x). apply Hfr; [apply bv_unsigned_in_range | exact H1 | exact H2]. }
    split; [|split; [|split; [|split; [|split]]]].
    - intros r Hr. destruct (kall_cases r Hr) as (k & Hk' & ->). change (ms_regs msr') with R.
      destruct (Nat.eq_dec k 2) as [->|Hk2].
      + change (Z.of_nat 2) with 2. rewrite R2. exact HRs.
      + exact (HK k (kall_other k Hk' Hk2)).
    - intros x Hx Hrg'. apply Hm_other; [intros Hc; apply Hx; exact (HinA1 x Hc) | exact (Hnd_rg x Hrg')].
    - intros w Hw Hout Hno. apply Hm_other.
      + intros Hc. rewrite u_small64 in Hc by exact Hw. destruct (HinA1 (Z_to_bv 64 w) ltac:(rewrite u_small64 by exact Hw; exact Hc)) as (i & R0 & Hi & HR0 & Hin).
        unfold outside in Hout. rewrite Forall_forall in Hout. cbn [mrg s_rgs] in Hout.
        specialize (Hout R0 ltac:(apply in_or_app; left; exact (nth_error_In _ _ HR0))).
        unfold in_rg in Hin. lia.
      + rewrite u_small64 by exact Hw. intros Hdw. apply Hno. exact (proj1 (HDN w ltac:(unfold two64 in Hw; lia) Hdw)).
    - intros w Hfz. pose proof (dn_frz _ _ _ _ _ _ _ _ _ Hd) as Hfrz. pose proof (dn_spok _ _ _ _ _ _ _ _ _ Hd) as Hspok.
      pose proof (alloc_top_lo _ (proj1 Hspok)) as Htop.
      destruct Hfz as (p & Hp & Hw). destruct (Hfrz p Hp w Hw) as (Hwr & Hout & _).
      assert (Hw64 : 0 <= w < two64) by (unfold two64; lia).
      apply Hm_other.
      + intros Hc. rewrite u_small64 in Hc by exact Hw64. destruct (HinA1 (Z_to_bv 64 w) ltac:(rewrite u_small64 by exact Hw64; exact Hc)) as (i & R0 & Hi & HR0 & Hin).
        unfold outside in Hout. rewrite Forall_forall in Hout. cbn [mrg s_rgs] in Hout.
        specialize (Hout R0 ltac:(apply in_or_app; left; exact (nth_error_In _ _ HR0))).
        unfold in_rg in Hin. lia.
      + rewrite u_small64 by exact Hw64. intros Hdw. apply (proj2 (proj2 (HDN w ltac:(unfold two64 in Hw64; lia) Hdw))).
        exists p. split; [exact Hp | exact Hw].
    - intros i R0 j Hi HR0 Hj. destruct Hi as [<-|[]]. rewrite Pa1 in HR0. injection HR0 as <-.
      unfold rsz in Hj. cbn [rg_size rg_base] in Hj |- *. rewrite lden_lconst, u_small64 in Hj by (unfold two64; lia).
      assert (Eb : bv_unsigned (lden E (laddc spl (-2048))) = SPv - 2048) by (rewrite lden_laddc; fold SPv; rewrite u_small64; unfold two64 in *; lia).
      rewrite Eb. destruct (Ba1 (SPv - 2048 + j) ltac:(unfold SP; lia)) as [B1' B2'].
      destruct (grows_rw SEGS (ms_mem msr) m' (Z_to_bv 64 (SPv - 2048 + j)) Hgr B1' B2') as [C1 C2].
      split; [exact C1 | intros _; exact C2].
    - split; [exists nd', F', st'; split; [exact HI2|]; split; [lia | lia]|].
      intros x Hx H1 H2. apply (Hm_other (wa x)); rewrite u_wa_small by exact Hx; assumption. }
  intros E' ms' model' HD' Ha' Hfz' (mr & ((nd2 & F2 & st2 & HI3 & Hb1 & Hb2) & Hfr2) & Hvis).
  apply (Hk E' ms' model' HD' Ha' Hfz').
  - exists nd2, F2, st2. split; [|split; assumption].
    apply (INV_D_frame mr); [exact HI3|]. intros x Hx Hdw. apply Hvis. exact (proj2 (Hdep x Hx Hdw)).
  - intros x Hx Hv H1 H2. rewrite (Hvis (wa x) Hv). rewrite (Hfr2 x Hx H1 H2). cbn [msr restrict ms_mem]. unfold mrestrict. fold H. rewrite Hv. reflexivity.
Qed.
End PutMainG.
(* [comment removed for export] *)
End AcPutAppG.

Module AcStateWf.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec FxLin FxCore FxSound FxMem FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChSep FxChFix.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcCarve AcHand.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma regs_wf_n_get : forall n R m, regs_wf_n n R m = true -> forall j, (1 <= j <= m)%nat -> lwf n (rget R (Pos.of_succ_nat j)) = true.
Proof.
  intros n R m. induction m as [|m IH]; intros H j Hj; [lia|]. cbn [regs_wf_n] in H. apply andb_prop in H as [H1 H2].
  destruct (Nat.eq_dec j (Datatypes.S m)) as [->|Hne]; [exact H1 | apply (IH H2); lia].
Qed.
Lemma regs_wf_n_intro : forall n R m, (forall j, (1 <= j <= m)%nat -> lwf n (rget R (Pos.of_succ_nat j)) = true) -> regs_wf_n n R m = true.
Proof.
  intros n R m. induction m as [|m IH]; intros H; [reflexivity|]. cbn [regs_wf_n]. rewrite (H (Datatypes.S m)) by lia. cbn [andb].
  apply IH. intros j Hj. apply H. lia.
Qed.
Lemma regs_wf_n_mono' : forall n n' R k, (n <= n')%positive -> regs_wf_n n R k = true -> regs_wf_n n' R k = true.
Proof.
  intros n n' R k Hn. induction k as [|k IH]; intros H; [reflexivity|]. cbn [regs_wf_n] in *. apply andb_prop in H as [H1 H2].
  rewrite (lwf_mono' n n' _ Hn H1), (IH H2). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma regs_wf_rset : forall n R k l m, k <> xH -> regs_wf_n n R m = true -> lwf n l = true -> regs_wf_n n (rset R k l) m = true.
Proof.
  intros n R k l m Hk H Hl. apply regs_wf_n_intro. intros j Hj.
  destruct (Pos.eq_dec (Pos.of_succ_nat j) k) as [<-|Hne]; [rewrite rget_rset_same by exact Hk; exact Hl|].
  rewrite rget_rset_other by exact Hne. exact (regs_wf_n_get n R m H j Hj).
Qed.
Lemma with_reg_wf : forall S k l, k <> xH -> state_wf S = true -> lwf (s_next S) l = true -> state_wf (with_reg S k l) = true.
Proof.
  intros S k l Hk H Hl. unfold state_wf, with_reg in *. cbn [s_next s_regs s_rgs s_facts s_resv] in *.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  rewrite (regs_wf_rset _ _ k l 31 Hk H1 Hl), H2, H3, H4. reflexivity.
Qed.
Lemma fix_post_wf : forall L a, state_wf L = true -> lwf (s_next L) a = true -> state_wf (fix_post L a) = true.
Proof.
  intros L a H Hl. unfold state_wf, fix_post in *. cbn [s_next s_regs s_rgs s_facts s_resv] in *.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  assert (Hk : rkey a0r <> xH) by (intros Hc; vm_compute in Hc; discriminate Hc).
  rewrite (regs_wf_rset _ _ (rkey a0r) a 31 Hk H1 Hl), H2, H3, H4. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma empty_rg_wf : forall n R, rwf n R = true -> rwf n (empty_rg R) = true.
Proof.
  intros n R H. unfold rwf, empty_rg in *. cbn [rg_base rg_size rg_cont]. apply andb_prop in H as [H _]. rewrite H. reflexivity.
Qed.
Lemma empty_at_wf : forall n W rgs i, forallb (rwf n) rgs = true -> forallb (rwf n) (empty_at W i rgs) = true.
Proof.
  intros n W rgs. induction rgs as [|R rs IH]; intros i H; [reflexivity|]. cbn [empty_at forallb] in *. apply andb_prop in H as [H1 H2].
  rewrite (IH (Datatypes.S i) H2), andb_true_r. destruct (existsb (Nat.eqb i) W); [exact (empty_rg_wf n R H1) | exact H1].
Qed.
Lemma hand_post_wf : forall L q K W, state_wf L = true -> state_wf (hand_post L q K W) = true.
Proof.
  intros L q K W H. unfold state_wf, hand_post in *. cbn [s_next s_regs s_rgs s_facts s_resv] in *.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  assert (Hn : (s_next L <= s_next L + 33)%positive) by lia.
  assert (HR : regs_wf_n (s_next L + 33) (hregs (s_regs L) K (s_next L) 31 TEmpty) 31 = true).
  { apply regs_wf_n_intro. intros j Hj.
    assert (Hkey : Pos.to_nat (Pos.of_succ_nat j) = Datatypes.S j) by apply SuccNat2Pos.id_succ.
    rewrite hregs_get; [| rewrite Hkey; lia | intros Hc; rewrite Hc in Hkey; cbn in Hkey; lia].
    destruct (existsb (Pos.eqb (Pos.of_succ_nat j)) K).
    - exact (lwf_mono' _ _ _ Hn (regs_wf_n_get _ _ 31 H1 j Hj)).
    - apply lwf_lvar. lia. }
  assert (HG : forallb (rwf (s_next L + 33)) (empty_at W 0 (s_rgs L)) = true).
  { apply empty_at_wf. apply forallb_forall. intros R HR0. rewrite forallb_forall in H2. exact (rwf_mono _ _ R Hn (H2 R HR0)). }
  assert (HFc : forallb (fwf (s_next L + 33)) (s_facts L) = true).
  { apply forallb_forall. intros f Hf. rewrite forallb_forall in H3. exact (fwf_mono _ _ f Hn (H3 f Hf)). }
  rewrite HR, HG, HFc. reflexivity.
Qed.
(* [comment removed for export] *)
End AcStateWf.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ro_b (o : option region) : bool :=
  match o with
  | Some (RG b z RO TEmpty) => match is_const z with Some zz => (lin_eqb b (lconst 65536) && lin_eqb z (lconst zz) && Z.leb 77824 zz && Z.ltb zz (2^32))%bool | None => false end
  | _ => false
  end.
Lemma ro_b_sound : forall o, ro_b o = true -> exists zro, 77824 <= zro < 2^32 /\ o = Some (RG (lconst 65536) (lconst zro) RO TEmpty).
Proof.
  intros [[b z [] c]|] H; cbn [ro_b] in H; try discriminate. destruct c; [|discriminate].
  destruct (is_const z) as [zz|]; [|discriminate].
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply lin_eqb_eq in H1, H2. apply Z.leb_le in H3. apply Z.ltb_lt in H4. subst. exists zz. split; [lia|reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition got_rg_b (o : option region) : bool :=
  match o with
  | Some (RG bb zz k TEmpty) =>
      match is_const bb, is_const zz with
      | Some b, Some z => ((match k with RI | RO => true | _ => false end) && lin_eqb bb (lconst b) && lin_eqb zz (lconst z) &&
                           Z.leb 0 b && Z.leb b 910448 && Z.leb 910456 (b + z) && Z.leb (b + z) (2^47))%bool
      | _, _ => false
      end
  | _ => false
  end.
Lemma got_rg_b_sound : forall o, got_rg_b o = true -> exists k b z, (k = RI \/ k = RO) /\ 0 <= b <= 910448 /\ 910456 <= b + z <= 2^47 /\
  o = Some (RG (lconst b) (lconst z) k TEmpty).
Proof.
  intros o H. unfold got_rg_b in H. destruct o as [[bb zz k c]|]; [|discriminate]. destruct c; [|discriminate].
  destruct (is_const bb) as [b|] eqn:Hb; [|discriminate]. destruct (is_const zz) as [z|] eqn:Hz; [|discriminate].
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?] end.
  repeat match goal with
         | X : Z.leb _ _ = true |- _ => apply Z.leb_le in X
         | X : lin_eqb _ _ = true |- _ => apply lin_eqb_eq in X
         end.
  exists k, b, z. split; [destruct k; try discriminate; first [left; reflexivity | right; reflexivity]|]. split; [lia|]. split; [lia|]. subst. reflexivity.
Qed.

Definition unw_shape0_b (L : sst) (spl : lin) (osp obuf blo zlo bhi zhi : Z) (iLo iF iS iT iHi iRO iGOT iPSZ : nat) (xt1 xt2 : positive) (lo hi : Z) : bool :=
  let R := s_regs L in let G := s_rgs L in let F := s_facts L in
  (Z.eqb (s_pc L) 0x82908 && rsv_none_b (s_resv L) &&
   lin_eqb (rget R (rk 2)) (laddc spl osp) && lin_eqb (rget R (rk 10)) (laddc spl obuf) && lin_eqb (rget R (rk 12)) spl &&
   lin_eqb (rget R (rk 13)) (TOPL xt1 xt2) && lin_eqb (rget R (rk 14)) (BOTL xt1 xt2) && lin_eqb (rget R (rk 15)) (lconst 30) &&
   rg_hdr_b (nth_error G iLo) (laddc spl blo) (lconst zlo) RW && rg_hdr_b (nth_error G iF) (laddc spl (osp - 64)) (lconst 64) RW &&
   rg_hdr_b (nth_error G iS) (laddc spl (obuf + 8)) (lconst 8) RW && tag0_b (nth_error G iS) &&
   rg_hdr_b (nth_error G iT) (laddc spl (obuf + 16)) (lconst 240) RW &&
   rg_hdr_b (nth_error G iHi) (laddc spl bhi) (lconst zhi) RW &&
   ro_b (nth_error G iRO) && got_rg_b (nth_error G iGOT) &&
   psz_b (nth_error G iPSZ) &&
   infact_b (FMod spl 4 0) F && infact_b (FRange spl lo hi) F && infact_b (FRange (lvar xt1) 4294901759 4294967295) F &&
   infact_b (FRange (lvar xt2) 0 7) F && lwf (s_next L) spl &&
   Z.leb (2^46 + 8192) lo && Z.leb hi (2^47) && Z.eqb (osp mod 16) 0 && Z.eqb (obuf mod 8) 0 && Z.leb osp obuf && Z.leb (obuf + 2056) 0 &&
   Z.leb (-8192) blo && Z.leb blo (osp - 1024) && Z.leb (osp - 64) (blo + zlo) && Z.leb 0 zlo && Z.leb bhi (obuf + 256) &&
   Z.leb (obuf + 2056) (bhi + zhi) && Z.leb 0 zhi && Z.leb (bhi + zhi) 0 && Z.leb (-8192) (osp - 1024) && Z.leb (blo + zlo) 0 && Z.leb (-8192) bhi)%bool.

Lemma unw_shape0_b_sound : forall L spl osp obuf blo zlo bhi zhi iLo iF iS iT iHi iRO iGOT iPSZ xt1 xt2 lo hi,
  unw_shape0_b L spl osp obuf blo zlo bhi zhi iLo iF iS iT iHi iRO iGOT iPSZ xt1 xt2 lo hi = true ->
  unw_shape0 L spl osp obuf blo zlo bhi zhi iLo iF iS iT iHi iRO iGOT iPSZ xt1 xt2 lo hi.
Proof.
  intros L spl osp obuf blo zlo bhi zhi iLo iF iS iT iHi iRO iGOT iPSZ xt1 xt2 lo hi H. unfold unw_shape0_b in H.
  repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?] end.
  repeat match goal with H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H | H : Z.leb _ _ = true |- _ => apply Z.leb_le in H
                      | H : Pos.ltb _ _ = true |- _ => apply Pos.ltb_lt in H | H : lin_eqb _ _ = true |- _ => apply lin_eqb_eq in H
                      | H : rsv_none_b _ = true |- _ => apply rsv_none_b_sound in H | H : infact_b _ _ = true |- _ => apply infact_b_sound in H
                      | H : rg_is_b _ _ = true |- _ => apply rg_is_b_sound in H | H : rg_hdr_b _ _ _ _ = true |- _ => apply rg_hdr_b_sound in H
                      | H : ro_b _ = true |- _ => apply ro_b_sound in H
                      | H : got_rg_b _ = true |- _ => apply got_rg_b_sound in H
                      | H : psz_b _ = true |- _ => apply psz_b_sound in H end.
  constructor; try assumption.
  - match goal with H : exists c, nth_error (s_rgs L) iS = Some _ |- _ => destruct H as (c & Hc) end. exists c. split; [exact Hc|].
    apply (tag0_b_sound _ _ _ _ _ Hc). assumption.
  - repeat split; assumption.
Qed.
(* [comment removed for export] *)
