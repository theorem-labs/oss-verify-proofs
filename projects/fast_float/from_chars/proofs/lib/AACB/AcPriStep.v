(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec StoreOk FxLin FxCore FxSound FxMem FxSubst FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChSep FxWvC.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AXG_put AXG_np AXG_nf1 AXG_npf.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst AcPri AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk AcConvA AcNPop.

Module AXG_gpf.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AXG_put AXG_np AXG_npf AXG_gp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma INV_G_o : forall m CA SB c sz nc newc j, INV_G m CA SB c sz nc newc j -> INV_Co m CA SB c sz nc newc j.
Proof. intros m CA SB c sz nc newc j [A B C D E F G H I J K L M N O]. constructor; assumption. Qed.
Lemma INV_Co_G : forall m CA SB c sz nc newc j, INV_Co m CA SB c sz nc newc j -> rd m 929848 8 SB -> rd m 929864 8 (SB + 137438953472) ->
  STATS m CA -> INV_G m CA SB c sz nc newc j.
Proof. intros m CA SB c sz nc newc j [A D E F G H I J K M N] B C (L & _ & O). constructor; assumption. Qed.
(* [comment removed for export] *)
End AXG_gpf.

Module AcNPopApp.
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
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_put AXG_put3 AXG_np AXG_np3 AXG_nf1 AXG_npf AXG_gp AXG_gp4.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put3 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np3 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_npf OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp4 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep.AXG_gpf.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcHand.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcDenW AcHand AcHand0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp0 AcDenX.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt.AcShift OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.AcMrg OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand.AcMrg0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDenW OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp.AcPutApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDenX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition ncell (CA SB c newc x : Z) : Prop := foot_Co CA SB c newc x \/ CA + 2560 <= x < CA + 2592.

(* [comment removed for export] *)
Lemma rd_vis : forall (H : word -> bool) (m : word -> option byte) a w v, H_off_segments SEGS H -> 0 <= a -> a + Z.of_nat w <= 2^64 ->
  rd (mrestrict H m) a w v -> forall x, a <= x < a + Z.of_nat w -> H (wa x) = false.
Proof.
  intros H m a w v Hoff Ha Hw R x Hx. destruct (H (wa x)) eqn:Hh; [|reflexivity]. exfalso.
  destruct (rd_byte (mrestrict H m) a w v (Z.to_nat (x - a)) Ha Hw R ltac:(lia)) as (b & _ & Xb). rewrite Z2Nat.id in Xb by lia.
  replace (a + (x - a)) with x in Xb by lia. unfold rd in Xb. cbn [rdn] in Xb. unfold mrestrict in Xb at 1. rewrite Hh in Xb.
  pose proof (Hoff (wa x) Hh) as Hns. unfold seg_rom, memory_read in Xb. change (Z.of_N 1%N) with 1%Z in Xb. rewrite Hns in Xb. discriminate.
Qed.

Section NPopApp.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap SEGS.

(* [comment removed for export] *)
Record np_shape (L : sst) (spl cal ndl : lin) (iW iRO iST : nat) : Prop := {
  ns_pc   : s_pc L = 0x44004 ;
  ns_rsv  : s_resv L = RNone ;
  ns_sp   : rget (s_regs L) (rk 2) = spl ;
  ns_a0   : rget (s_regs L) (rk 10) = lconst 929816 ;
  ns_a1   : rget (s_regs L) (rk 11) = cal ;
  ns_a2   : rget (s_regs L) (rk 12) = ndl ;
  ns_a3   : rget (s_regs L) (rk 13) = lconst 8 ;
  ns_w    : exists cw, nth_error (s_rgs L) iW = Some (RG (laddc spl (-2048)) (lconst 2048) RW cw) ;
  ns_ro   : exists zro, 77824 <= zro < 2^32 /\ nth_error (s_rgs L) iRO = Some (RG (lconst 65536) (lconst zro) RO TEmpty) ;
  ns_st   : exists stl cs, nth_error (s_rgs L) iST = Some (RG stl (lconst 16) RW cs)   (* [comment removed for export] *)
}.

#[using="Hwx"] Theorem den_npop_app : forall mem0 L S E M ms model T spl cal ndl iW iRO iST c SB sz nc newc j,
  DEN SEGS LIMIT model0 mem0 E (mrg L S) M ms model ->
  state_wf L = true -> np_shape L spl cal ndl iW iRO iST ->
  let CA := uE E cal in let ND := uE E ndl in let SP := uE E spl in
  c = cls_of ND -> 1 <= ND <= 65536 ->
  2^46 + 8192 <= SP <= 2^47 -> SP mod 16 = 0 ->
  INV_Co mem0 CA SB c sz nc newc j -> STATS mem0 CA -> j + 1 + nc <= newc ->
  rd (ms_mem (restrict (Hof E M model) ms)) 929848 8 SB -> rd (ms_mem (restrict (Hof E M model) ms)) 929864 8 (SB + 137438953472) ->
  (forall x, 0 <= x < 2^64 -> ncell CA SB c newc x -> own_pt E M x /\ outside E (s_rgs (mrg L S)) (wa x) /\ ~ frz_pt E M x) ->
  ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6537424 <= CA) /\ CA mod 16 = 0 /\ CA + 2592 <= SP - 2048 ->
  4194304 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048 ->
  (CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA) ->
  (forall E' ms' model', DEN SEGS LIMIT model0 (ms_mem ms') E' (mrg (hand_post L 0x44224 KALLk [iW; iST]) S) M ms' model' ->
     agree (s_next L) E E' -> (forall w, frz_pt E M w -> ms_mem ms' (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)) ->
     INV_G (ms_mem ms') CA SB c sz nc newc (j + 1) -> STATS (ms_mem ms') CA ->
     getr (ms_regs ms') (Z_to_bv 5 10) = wa (SB + c * 4294967296 + j * sz) ->
     (forall x, 0 <= x < 2^64 -> Hof E M model (wa x) = false -> ~ (SP - 2048 <= x < SP) -> ~ owned_C CA SB c x ->
        ms_mem ms' (wa x) = ms_mem ms (wa x)) ->
     realizes_cfg SEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg SEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros mem0 L S E M ms model T spl cal ndl iW iRO iST c SB sz nc newc j Hd HwL PS CA ND SP Hc HND HSP Hal HI HST Hj RSB RRIB HCELL HCA HSB HSEP Hk.
  destruct PS as [Ppc Prsv Psp Pa0 Pa1 Pa2 Pa3 (cw & Pw) (zro & Hzro & Pro) (stl & cs & Pst)].
  pose proof (dn_sden _ _ _ _ _ _ _ _ _ Hd) as Hsd.
  pose proof (dn_own _ _ _ _ _ _ _ _ _ Hd) as Hown.
  set (H := Hof E M model) in *. set (msr := restrict H ms) in *.
  pose proof (sden_0 _ _ _ _ Hsd) as Hd0.
  assert (Hsvc : ms_svc_pending ms = None) by (destruct Hd0 as (_ & X & _); exact X).
  assert (Hrv : ms_resv ms = None).
  { destruct Hd0 as (_ & _ & X & _). cbn [mrg s_resv] in X. rewrite Prsv in X. cbn [rsv_ok] in X. exact X. }
  assert (HSPr : 0 <= SP < two64) by (unfold SP, uE; pose proof (bv_unsigned_in_range _ (lden E spl)) as X; exact X).
  assert (R2 : getr (ms_regs ms) (Z_to_bv 5 2) = wa SP).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E L S msr (Z_to_bv 5 2) _ Hd0 Psp). unfold wa, SP, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = wa 929816).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E L S msr (Z_to_bv 5 10) _ Hd0 Pa0). rewrite lden_lconst. reflexivity. }
  assert (R11 : getr (ms_regs ms) (Z_to_bv 5 11) = wa CA).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E L S msr (Z_to_bv 5 11) _ Hd0 Pa1). unfold wa, CA, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R12 : getr (ms_regs ms) (Z_to_bv 5 12) = wa ND).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E L S msr (Z_to_bv 5 12) _ Hd0 Pa2). unfold wa, ND, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R13 : getr (ms_regs ms) (Z_to_bv 5 13) = wa 8).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E L S msr (Z_to_bv 5 13) _ Hd0 Pa3). rewrite lden_lconst. reflexivity. }
  (* [comment removed for export] *)
  pose proof (mrg_rg0 E L S msr iW _ Hd0 Pw) as Rw. pose proof (mrg_rg0 E L S msr iRO _ Hd0 Pro) as Rro. pose proof (mrg_rg0 E L S msr iST _ Hd0 Pst) as Rst0.
  assert (Ebw : bv_unsigned (lden E (laddc spl (-2048))) = SP - 2048) by (rewrite lden_laddc; fold (uE E spl); fold SP; rewrite u_small64; unfold two64 in *; lia).
  assert (Bw : forall x, SP - 2048 <= x < SP -> rd1 SEGS (ms_mem msr) (Z_to_bv 64 x) <> None /\ wview SEGS (ms_mem msr) (Z_to_bv 64 x) <> None).
  { intros x Hx. apply (rg_rw_pt _ _ _ x Rw eq_refl). cbn [rg_base]. rewrite Ebw. unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_small64 by (unfold two64; lia). lia. }
  assert (Bro : forall i, 65536 <= i < 143360 -> ms_mem msr (Z_to_bv 64 i) = None) by exact (ro_none_z _ _ _ Hzro Rro).
  (* [comment removed for export] *)
  assert (Hcell : forall x, 0 <= x < 2^64 -> ncell CA SB c newc x -> ms_mem msr (wa x) = mem0 (wa x) /\ H (wa x) = false).
  { intros x Hx Hc0. destruct (HCELL x Hx Hc0) as ((p & Hp & Hpw) & Hout & _). pose proof (Hown p Hp x Hpw) as [Hv Hm].
    fold H in Hv. unfold wa. split; [|exact Hv]. cbn [msr restrict ms_mem]. unfold mrestrict. rewrite Hv. apply Hm. exact Hout. }
  pose proof HI as HI0. destruct HI0 as [Igeo _ _ _ _ _ _ _ _ _ _].
  assert (HIo : INV_Co (ms_mem msr) CA SB c sz nc newc j).
  { apply (INV_Co_frame mem0); [lia | lia | lia | lia | | exact HI]. intros x Hf.
    assert (Hx : 0 <= x < 2^64) by (unfold foot_Co in Hf; lia). exact (proj1 (Hcell x Hx (or_introl Hf))). }
  assert (HSTr : STATS (ms_mem msr) CA).
  { destruct HST as ((st & Hst & Rst) & (st2 & Hst2 & Rst2) & Wst). split; [|split].
    - exists st. split; [exact Hst|]. apply (rd_frame mem0); [lia | cbn; lia | intros x Hx; cbn in Hx; apply (Hcell x); [lia | right; lia] | exact Rst].
    - exists st2. split; [exact Hst2|]. apply (rd_frame mem0); [lia | cbn; lia | intros x Hx; cbn in Hx; apply (Hcell x); [lia | right; lia] | exact Rst2].
    - apply (wr_frame mem0); [lia | lia | intros x Hx; apply (Hcell x); [lia | right; lia] | exact Wst]. }
  pose proof (INV_Co_G _ _ _ _ _ _ _ _ HIo RSB RRIB HSTr) as HIC.
  assert (Hstk : stk_ok SEGS (ms_mem msr) (wa SP) 2048).
  { intros a k Ha Hk'. rewrite u_wa_small in Ha, Hk' by lia. apply store_ok_of_all; [pose proof (bv_unsigned_in_range _ a); lia|].
    intros x Hx. pose proof (bv_unsigned_in_range _ x) as Rx. destruct (Bw (bv_unsigned x) ltac:(lia)) as [_ W]. rewrite Z_to_bv_bv_unsigned in W. exact W. }
  destruct (@gpop_contract (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_rom ms) (ms_mem msr) (ms_regs ms) CA ND c SB sz nc newc j SP Hc HIC Hj HND)
    as (R & m' & Hms & HRs & HK & HR10 & HI2 & Hfr & Hgr).
  all: try (replace (2%bv : reg) with (Z_to_bv 5 2) by (apply bv_eq; reflexivity); exact R2).
  all: try (replace (10%bv : reg) with (Z_to_bv 5 10) by (apply bv_eq; reflexivity); exact R10).
  all: try (replace (11%bv : reg) with (Z_to_bv 5 11) by (apply bv_eq; reflexivity); exact R11).
  all: try (replace (12%bv : reg) with (Z_to_bv 5 12) by (apply bv_eq; reflexivity); exact R12).
  all: try (replace (13%bv : reg) with (Z_to_bv 5 13) by (apply bv_eq; reflexivity); exact R13).
  all: try exact Hstk. all: try exact Bro. all: try exact HCA. all: try exact HSB. all: try exact HSEP.
  all: try (split; [lia | exact Hal]).
  all: match goal with |- realizes_cfg _ _ _ _ => idtac | |- ?G => idtac "REMAIN" G; fail end.
  set (fx1 := mkFP (ms_fregs ms) (ms_fcsr ms)).
  set (msr' := @mkst fx1 R (wa 0x44224) m' (ms_rom ms)).
  assert (Hpc0 : ms_pc_val ms = wa 0x44004) by (destruct Hd0 as (X & _); cbn [mrg s_pc] in X; rewrite Ppc in X; exact X).
  assert (Hst : isteps SEGS msr msr').
  { unfold msr. rewrite (restrict_mkst H ms Hsvc Hrv), Hpc0. apply isteps_of_msteps. exact Hms. }
  apply (den_hand_x0 SEGS cfg LIMIT model0 Hwx mem0 L S E M ms model T 0x44224 KALLk [iW; iST]
           (fun rr mr => INV_G mr CA SB c sz nc newc (j + 1) /\ getr rr (Z_to_bv 5 10) = wa (SB + c * 4294967296 + j * sz) /\
                         (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ owned_C CA SB c x -> mr (wa x) = ms_mem msr (wa x)) /\
                         exists st2, 0 <= st2 < 2^64 /\ rd mr (CA + 2584) 8 st2) Hd HwL).
  { intros i R0 Hi HR0. destruct Hi as [<-|[<-|[]]]; [rewrite Pw in HR0 | rewrite Pst in HR0]; injection HR0 as <-; discriminate. }
  { exists msr'. split; [exact Hst|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    assert (HinW : forall x, SP - 2048 <= bv_unsigned x < SP -> exists i R0, In i [iW; iST] /\ nth_error (s_rgs L) i = Some R0 /\ in_rg E R0 x).
    { intros x Hx. exists iW, (RG (laddc spl (-2048)) (lconst 2048) RW cw). split; [left; reflexivity|]. split; [exact Pw|].
      unfold in_rg. cbn [rg_base]. rewrite Ebw. unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_small64 by (unfold two64; lia). lia. }
    assert (Hown_c : forall x, 0 <= x < 2^64 -> owned_C CA SB c x -> ncell CA SB c newc x).
    { intros x Hx Ho. unfold owned_C in Ho. unfold ncell, foot_Co. lia. }
    assert (Hno_rg : forall x, (exists R0, In R0 (s_rgs (mrg L S)) /\ in_rg E R0 x) -> ~ owned_C CA SB c (bv_unsigned x)).
    { intros x (R0 & HR0 & Hin) Ho. destruct (HCELL (bv_unsigned x) (bv_unsigned_in_range _ x) (Hown_c _ (bv_unsigned_in_range _ x) Ho)) as (_ & Hout & _).
      rewrite wa_u in Hout. unfold outside in Hout. rewrite Forall_forall in Hout. specialize (Hout R0 HR0). unfold in_rg in Hin. lia. }
    assert (Hm_other : forall x, ~ (SP - 2048 <= bv_unsigned x < SP) -> ~ owned_C CA SB c (bv_unsigned x) -> ms_mem msr' x = ms_mem msr x).
    { intros x H1 H2. cbn [msr' mkst ms_mem]. rewrite <- (wa_u x). apply Hfr; [apply bv_unsigned_in_range | exact H1 | exact H2]. }
    split; [|split; [|split; [|split; [|split]]]].
    - intros r Hr. destruct (kall_cases r Hr) as (k & Hk' & ->). change (ms_regs msr') with R.
      destruct (Nat.eq_dec k 2) as [->|Hk2].
      + change (Z.of_nat 2) with 2. rewrite R2. exact HRs.
      + apply HK. clear - Hk' Hk2. cbn [In] in Hk'. unfold KCALLEE. cbn [In]. repeat (destruct Hk' as [<-|Hk']; [first [congruence | tauto]|]). destruct Hk'.
    - intros x Hx Hrg'. apply Hm_other; [intros Hc0; apply Hx; exact (HinW x Hc0) | exact (Hno_rg x Hrg')].
    - intros w Hw Hout Hno. apply Hm_other.
      + intros Hc0. rewrite u_small64 in Hc0 by exact Hw. destruct (HinW (Z_to_bv 64 w) ltac:(rewrite u_small64 by exact Hw; exact Hc0)) as (i & R0 & Hi & HR0 & Hin).
        unfold outside in Hout. rewrite Forall_forall in Hout. cbn [mrg s_rgs] in Hout.
        specialize (Hout R0 ltac:(apply in_or_app; left; exact (nth_error_In _ _ HR0))).
        unfold in_rg in Hin. lia.
      + rewrite u_small64 by exact Hw. intros Ho. apply Hno. exact (proj1 (HCELL w ltac:(unfold two64 in Hw; lia) (Hown_c w ltac:(unfold two64 in Hw; lia) Ho))).
    - intros w Hfz. pose proof (dn_frz _ _ _ _ _ _ _ _ _ Hd) as Hfrz.
      destruct Hfz as (p & Hp & Hw). destruct (Hfrz p Hp w Hw) as (Hwr & Hout & _).
      pose proof (dn_spok _ _ _ _ _ _ _ _ _ Hd) as Hspok. pose proof (alloc_top_lo _ (proj1 Hspok)) as Htop.
      assert (Hw64 : 0 <= w < two64) by (unfold two64; lia).
      apply Hm_other.
      + intros Hc0. rewrite u_small64 in Hc0 by exact Hw64. destruct (HinW (Z_to_bv 64 w) ltac:(rewrite u_small64 by exact Hw64; exact Hc0)) as (i & R0 & Hi & HR0 & Hin).
        unfold outside in Hout. rewrite Forall_forall in Hout. cbn [mrg s_rgs] in Hout.
        specialize (Hout R0 ltac:(apply in_or_app; left; exact (nth_error_In _ _ HR0))).
        unfold in_rg in Hin. lia.
      + rewrite u_small64 by exact Hw64. intros Ho. apply (proj2 (proj2 (HCELL w ltac:(unfold two64 in Hw64; lia) (Hown_c w ltac:(unfold two64 in Hw64; lia) Ho)))).
        exists p. split; [exact Hp | exact Hw].
    - intros i R0 j0 Hi HR0 Hj0. destruct Hi as [<-|[<-|[]]].
      + rewrite Pw in HR0. injection HR0 as <-.
        unfold rsz in Hj0. cbn [rg_size rg_base] in Hj0 |- *. rewrite lden_lconst, u_small64 in Hj0 by (unfold two64; lia).
        rewrite Ebw. destruct (Bw (SP - 2048 + j0) ltac:(lia)) as [B1' B2'].
        destruct (grows_rw SEGS (ms_mem msr) m' (Z_to_bv 64 (SP - 2048 + j0)) Hgr B1' B2') as [C1 C2].
        split; [exact C1 | intros _; exact C2].
      + rewrite Pst in HR0. injection HR0 as <-.
        destruct (rg_rw_pt _ _ _ (bv_unsigned (lden E (rg_base (RG stl (lconst 16) RW cs))) + j0) Rst0 eq_refl ltac:(lia)) as [B1' B2'].
        destruct (grows_rw SEGS (ms_mem msr) m' _ Hgr B1' B2') as [C1 C2].
        split; [exact C1 | intros _; exact C2].
    - split; [exact HI2|]. split; [replace (Z_to_bv 5 10) with (10%bv : reg) by (apply bv_eq; reflexivity); exact HR10|]. split; [exact Hfr|].
      destruct HSTr as (_ & (st2 & Hst2 & Rst2) & Wst).
      destruct (rdn_some m' (CA + 2584) 8 ltac:(lia) ltac:(cbn; unfold two64; lia)) as (bs & Hbs).
      { intros i Hi. cbn in Hi.
        destruct (rd_byte (ms_mem msr) (CA + 2584) 8 st2 (Z.to_nat i) ltac:(lia) ltac:(cbn; lia) Rst2 ltac:(lia)) as (b & _ & Xb). rewrite Z2Nat.id in Xb by lia.
        assert (X1 : rd1 SEGS (ms_mem msr) (Z_to_bv 64 (CA + 2584 + i)) <> None).
        { unfold rd in Xb. cbn [rdn] in Xb. unfold rd1. unfold wa in Xb. destruct (ms_mem msr (Z_to_bv 64 (CA + 2584 + i))); [discriminate|].
          destruct (seg_rom SEGS (Z_to_bv 64 (CA + 2584 + i))); [discriminate | discriminate]. }
        assert (X2 : wview SEGS (ms_mem msr) (Z_to_bv 64 (CA + 2584 + i)) <> None).
        { pose proof (Wst (24 + i) 1%nat ltac:(lia) ltac:(cbn; lia)) as W. replace (CA + 2560 + (24 + i)) with (CA + 2584 + i) in W by ring.
          cbn [store_ok] in W. unfold wa in W. destruct (wview SEGS (ms_mem msr) (Z_to_bv 64 (CA + 2584 + i))); [discriminate | discriminate]. }
        exact (proj1 (grows_rw SEGS (ms_mem msr) m' _ Hgr X1 X2)). }
      destruct (rd_exists m' (CA + 2584) 8 bs ltac:(lia) Hbs) as (v & Hv1 & Hv2 & Hrd). exists v. split; [lia | exact Hrd]. }
  intros E' ms' model' HD' Ha' Hfz' (rr & mr & (HI3 & HR3 & Hfr3 & (st2' & Hst2' & Rst2')) & Hrr & Hvis).
  assert (HST3 : STATS (ms_mem ms') CA).
  { destruct HI3 as [_ _ _ _ _ _ _ _ _ _ _ (st & Hst3 & Rst) _ _ Wst]. split; [|split].
    * exists st. split; [exact Hst3|]. apply (rd_frame mr); [lia | cbn; lia | intros x Hx; cbn in Hx; apply Hvis; apply (Hcell x); [lia | right; lia] | exact Rst].
    * exists st2'. split; [exact Hst2'|].
      apply (rd_frame mr); [lia | cbn; lia | intros x Hx; cbn in Hx; apply Hvis; apply (Hcell x); [lia | right; lia] | exact Rst2'].
    * apply (wr_frame mr); [lia | lia | intros x Hx; apply Hvis; apply (Hcell x); [lia | right; lia] | exact Wst]. }
  apply (Hk E' ms' model' HD' Ha' Hfz').
  - (* [comment removed for export] *)
    pose proof HI3 as HI4. destruct HI4 as [Ig ISB IRIB _ _ _ _ _ _ _ _ _ _ _ _].
    assert (HIo3 : INV_Co (ms_mem ms') CA SB c sz nc newc (j + 1)).
    { apply (INV_Co_frame mr); [lia | lia | lia | lia | | exact (INV_G_o _ _ _ _ _ _ _ _ HI3)]. intros x Hf.
      assert (Hx : 0 <= x < 2^64) by (unfold foot_Co in Hf; lia). apply Hvis. exact (proj2 (Hcell x Hx (or_introl Hf))). }
    apply (INV_Co_G _ _ _ _ _ _ _ _ HIo3).
    + apply (rd_frame mr); [lia | cbn; lia | | exact ISB]. intros x Hx. cbn in Hx. apply Hvis.
      exact (rd_vis H (ms_mem ms) 929848 8 _ (dn_hoff _ _ _ _ _ _ _ _ _ Hd) ltac:(lia) ltac:(cbn; lia) RSB x Hx).
    + apply (rd_frame mr); [lia | cbn; lia | | exact IRIB]. intros x Hx. cbn in Hx. apply Hvis.
      exact (rd_vis H (ms_mem ms) 929864 8 _ (dn_hoff _ _ _ _ _ _ _ _ _ Hd) ltac:(lia) ltac:(cbn; lia) RRIB x Hx).
    + exact HST3.
  - exact HST3.
  - rewrite Hrr. exact HR3.
  - intros x Hx Hv Hw Ho. rewrite (Hvis (wa x) Hv). rewrite (Hfr3 x Hx Hw Ho). cbn [msr restrict ms_mem]. unfold mrestrict. rewrite Hv. reflexivity.
Qed.
End NPopApp.
(* [comment removed for export] *)
End AcNPopApp.

Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep.AcNPopApp.

Module AcRunApp.
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
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AXG_put AXG_put3.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcHand.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcDenW AcHand AcHand0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp0 AcDenX.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt.AcShift OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.AcMrg OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand.AcMrg0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDenW OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp.AcPutApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDenX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section RunApp.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap SEGS.

#[using="Hwx"] Theorem den_run_app_x : forall mem0 L S E M ms model T spl stl iW iST cw cst q (K : list positive) (Kn : list nat) R' m' (OWN : Z -> Prop) (WS : Z),
  0 < WS <= 65536 ->
  DEN SEGS LIMIT model0 mem0 E (mrg L S) M ms model ->
  state_wf L = true -> s_resv L = RNone ->
  nth_error (s_rgs L) iW = Some (RG (laddc spl (- WS)) (lconst WS) RW cw) ->
  nth_error (s_rgs L) iST = Some (RG stl (lconst 16) RW cst) ->
  let SP := uE E spl in let ST := uE E stl in
  WS <= SP <= 2^47 -> ST + 16 <= 2^47 ->
  (forall r, existsb (Pos.eqb (rkey r)) K = true -> exists k : nat, In k Kn /\ r = Z_to_bv 5 (Z.of_nat k)) ->
  msteps SEGS (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (ms_pc_val ms) (ms_mem (restrict (Hof E M model) ms)) (ms_rom ms))
              (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) R' (wa q) m' (ms_rom ms)) ->
  (forall k, In k Kn -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat k))) ->
  (forall x, 0 <= x < 2^64 -> OWN x -> own_pt E M x /\ outside E (s_rgs (mrg L S)) (wa x) /\ ~ frz_pt E M x) ->
  (forall x, 0 <= x < 2^64 -> ~ (SP - WS <= x < SP) -> ~ (ST <= x < ST + 16) -> ~ OWN x ->
     m' (wa x) = ms_mem (restrict (Hof E M model) ms) (wa x)) ->
  mem_grows (ms_mem (restrict (Hof E M model) ms)) m' ->
  (forall E' ms' model', DEN SEGS LIMIT model0 (ms_mem ms') E' (mrg (hand_post L q K [iW; iST]) S) M ms' model' ->
     agree (s_next L) E E' -> (forall w, frz_pt E M w -> ms_mem ms' (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)) ->
     ms_regs ms' = R' -> (forall x, Hof E M model x = false -> ms_mem ms' x = m' x) ->
     (* [comment removed for export] *)
     Hof E' M model' = Hof E M model -> ms_mem (restrict (Hof E M model) ms') = m' ->
     realizes_cfg SEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg SEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros mem0 L S E M ms model T spl stl iW iST cw cst q K Kn R' m' OWN WS HWS Hd HwL Prsv Pw Pst SP ST HSP HST HK Hms HKR HOWN Hfr Hgr Hk.
  pose proof (dn_sden _ _ _ _ _ _ _ _ _ Hd) as Hsd.
  set (H := Hof E M model) in *. set (msr := restrict H ms) in *.
  pose proof (sden_0 _ _ _ _ Hsd) as Hd0.
  assert (Hsvc : ms_svc_pending ms = None) by (destruct Hd0 as (_ & X & _); exact X).
  assert (Hrv : ms_resv ms = None).
  { destruct Hd0 as (_ & _ & X & _). cbn [mrg s_resv] in X. rewrite Prsv in X. cbn [rsv_ok] in X. exact X. }
  pose proof (mrg_rg0 E L S msr iW _ Hd0 Pw) as Rw. pose proof (mrg_rg0 E L S msr iST _ Hd0 Pst) as Rst.
  assert (Ebw : bv_unsigned (lden E (laddc spl (- WS))) = SP - WS) by (rewrite lden_laddc; fold (uE E spl); fold SP; rewrite u_small64; unfold two64 in *; lia).
  assert (Bw : forall x, SP - WS <= x < SP -> rd1 SEGS (ms_mem msr) (Z_to_bv 64 x) <> None /\ wview SEGS (ms_mem msr) (Z_to_bv 64 x) <> None).
  { intros x Hx. apply (rg_rw_pt _ _ _ x Rw eq_refl). cbn [rg_base]. rewrite Ebw. unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_small64 by (unfold two64; lia). lia. }
  assert (Bs : forall x, ST <= x < ST + 16 -> rd1 SEGS (ms_mem msr) (Z_to_bv 64 x) <> None /\ wview SEGS (ms_mem msr) (Z_to_bv 64 x) <> None).
  { intros x Hx. apply (rg_rw_pt _ _ _ x Rst eq_refl). cbn [rg_base]. fold (uE E stl). fold ST. unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_small64 by (unfold two64; lia). lia. }
  set (fx1 := mkFP (ms_fregs ms) (ms_fcsr ms)) in *.
  set (msr' := @mkst fx1 R' (wa q) m' (ms_rom ms)).
  assert (Hst : isteps SEGS msr msr').
  { unfold msr. rewrite (restrict_mkst H ms Hsvc Hrv). apply isteps_of_msteps. exact Hms. }
  apply (den_hand_x1 SEGS cfg LIMIT model0 Hwx mem0 L S E M ms model T q K [iW; iST] (fun rr mr => rr = R' /\ mr = m') Hd HwL).
  { intros i R0 Hi HR0. destruct Hi as [<-|[<-|[]]]; [rewrite Pw in HR0 | rewrite Pst in HR0]; injection HR0 as <-; discriminate. }
  { exists msr'. split; [exact Hst|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    assert (HinW : forall x, SP - WS <= bv_unsigned x < SP \/ ST <= bv_unsigned x < ST + 16 ->
                     exists i R0, In i [iW; iST] /\ nth_error (s_rgs L) i = Some R0 /\ in_rg E R0 x).
    { intros x [Hx|Hx].
      - exists iW, (RG (laddc spl (- WS)) (lconst WS) RW cw). split; [left; reflexivity|]. split; [exact Pw|].
        unfold in_rg. cbn [rg_base]. rewrite Ebw. unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_small64 by (unfold two64; lia). lia.
      - exists iST, (RG stl (lconst 16) RW cst). split; [right; left; reflexivity|]. split; [exact Pst|].
        unfold in_rg. cbn [rg_base]. fold (uE E stl). fold ST. unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_small64 by (unfold two64; lia). lia. }
    assert (Hno_rg : forall x, (exists R0, In R0 (s_rgs (mrg L S)) /\ in_rg E R0 x) -> ~ OWN (bv_unsigned x)).
    { intros x (R0 & HR0 & Hin) Ho. destruct (HOWN (bv_unsigned x) (bv_unsigned_in_range _ x) Ho) as (_ & Hout & _).
      rewrite wa_u in Hout. unfold outside in Hout. rewrite Forall_forall in Hout. specialize (Hout R0 HR0). unfold in_rg in Hin. lia. }
    assert (Hm_other : forall x, ~ (SP - WS <= bv_unsigned x < SP) -> ~ (ST <= bv_unsigned x < ST + 16) -> ~ OWN (bv_unsigned x) -> ms_mem msr' x = ms_mem msr x).
    { intros x H1 H2 H3. cbn [msr' mkst ms_mem]. rewrite <- (wa_u x). apply Hfr; [apply bv_unsigned_in_range | exact H1 | exact H2 | exact H3]. }
    split; [|split; [|split; [|split; [|split]]]].
    - intros r Hr. destruct (HK r Hr) as (k & Hk' & ->). change (ms_regs msr') with R'. exact (HKR k Hk').
    - intros x Hx Hrg'. apply Hm_other; [intros Hc0; apply Hx; exact (HinW x (or_introl Hc0)) | intros Hc0; apply Hx; exact (HinW x (or_intror Hc0)) | exact (Hno_rg x Hrg')].
    - intros w Hw Hout Hno.
      assert (Houtw : forall i R0, In i [iW; iST] -> nth_error (s_rgs L) i = Some R0 -> ~ in_rg E R0 (Z_to_bv 64 w)).
      { intros i R0 Hi HR0 Hin. unfold outside in Hout. rewrite Forall_forall in Hout. cbn [mrg s_rgs] in Hout.
        specialize (Hout R0 ltac:(apply in_or_app; left; exact (nth_error_In _ _ HR0))). unfold in_rg in Hin. lia. }
      apply Hm_other.
      + intros Hc0. destruct (HinW (Z_to_bv 64 w) (or_introl Hc0)) as (i & R0 & Hi & HR0 & Hin). exact (Houtw i R0 Hi HR0 Hin).
      + intros Hc0. destruct (HinW (Z_to_bv 64 w) (or_intror Hc0)) as (i & R0 & Hi & HR0 & Hin). exact (Houtw i R0 Hi HR0 Hin).
      + rewrite u_small64 by exact Hw. intros Ho. apply Hno. exact (proj1 (HOWN w ltac:(unfold two64 in Hw; lia) Ho)).
    - intros w Hfz. pose proof (dn_frz _ _ _ _ _ _ _ _ _ Hd) as Hfrz.
      destruct Hfz as (p & Hp & Hw). destruct (Hfrz p Hp w Hw) as (Hwr & Hout & _).
      pose proof (dn_spok _ _ _ _ _ _ _ _ _ Hd) as Hspok. pose proof (alloc_top_lo _ (proj1 Hspok)) as Htop.
      assert (Hw64 : 0 <= w < two64) by (unfold two64; lia).
      assert (Houtw : forall i R0, In i [iW; iST] -> nth_error (s_rgs L) i = Some R0 -> ~ in_rg E R0 (Z_to_bv 64 w)).
      { intros i R0 Hi HR0 Hin. unfold outside in Hout. rewrite Forall_forall in Hout. cbn [mrg s_rgs] in Hout.
        specialize (Hout R0 ltac:(apply in_or_app; left; exact (nth_error_In _ _ HR0))). unfold in_rg in Hin. lia. }
      apply Hm_other.
      + intros Hc0. destruct (HinW (Z_to_bv 64 w) (or_introl Hc0)) as (i & R0 & Hi & HR0 & Hin). exact (Houtw i R0 Hi HR0 Hin).
      + intros Hc0. destruct (HinW (Z_to_bv 64 w) (or_intror Hc0)) as (i & R0 & Hi & HR0 & Hin). exact (Houtw i R0 Hi HR0 Hin).
      + rewrite u_small64 by exact Hw64. intros Ho. apply (proj2 (proj2 (HOWN w ltac:(unfold two64 in Hw64; lia) Ho))).
        exists p. split; [exact Hp | exact Hw].
    - intros i R0 j0 Hi HR0 Hj0. destruct Hi as [<-|[<-|[]]]; [rewrite Pw in HR0 | rewrite Pst in HR0]; injection HR0 as <-;
        unfold rsz in Hj0; cbn [rg_size rg_base] in Hj0 |- *; rewrite lden_lconst, u_small64 in Hj0 by (unfold two64; lia).
      + rewrite Ebw. destruct (Bw (SP - WS + j0) ltac:(lia)) as [B1' B2'].
        destruct (grows_rw SEGS (ms_mem msr) m' (Z_to_bv 64 (SP - WS + j0)) Hgr B1' B2') as [C1 C2]. split; [exact C1 | intros _; exact C2].
      + fold (uE E stl). fold ST. destruct (Bs (ST + j0) ltac:(lia)) as [B1' B2'].
        destruct (grows_rw SEGS (ms_mem msr) m' (Z_to_bv 64 (ST + j0)) Hgr B1' B2') as [C1 C2]. split; [exact C1 | intros _; exact C2].
    - split; reflexivity. }
  intros E' ms' model' HD' Ha' Hfz' (rr & mr & (-> & ->) & Hrr & Hvis & HH & Hrm).
  exact (Hk E' ms' model' HD' Ha' Hfz' Hrr Hvis HH Hrm).
Qed.
#[using="Hwx"] Theorem den_run_app : forall mem0 L S E M ms model T spl stl iW iST cw cst q (K : list positive) (Kn : list nat) R' m' (OWN : Z -> Prop) (WS : Z),
  0 < WS <= 65536 ->
  DEN SEGS LIMIT model0 mem0 E (mrg L S) M ms model ->
  state_wf L = true -> s_resv L = RNone ->
  nth_error (s_rgs L) iW = Some (RG (laddc spl (- WS)) (lconst WS) RW cw) ->
  nth_error (s_rgs L) iST = Some (RG stl (lconst 16) RW cst) ->
  let SP := uE E spl in let ST := uE E stl in
  WS <= SP <= 2^47 -> ST + 16 <= 2^47 ->
  (forall r, existsb (Pos.eqb (rkey r)) K = true -> exists k : nat, In k Kn /\ r = Z_to_bv 5 (Z.of_nat k)) ->
  msteps SEGS (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (ms_pc_val ms) (ms_mem (restrict (Hof E M model) ms)) (ms_rom ms))
              (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) R' (wa q) m' (ms_rom ms)) ->
  (forall k, In k Kn -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat k))) ->
  (forall x, 0 <= x < 2^64 -> OWN x -> own_pt E M x /\ outside E (s_rgs (mrg L S)) (wa x) /\ ~ frz_pt E M x) ->
  (forall x, 0 <= x < 2^64 -> ~ (SP - WS <= x < SP) -> ~ (ST <= x < ST + 16) -> ~ OWN x ->
     m' (wa x) = ms_mem (restrict (Hof E M model) ms) (wa x)) ->
  mem_grows (ms_mem (restrict (Hof E M model) ms)) m' ->
  (forall E' ms' model', DEN SEGS LIMIT model0 (ms_mem ms') E' (mrg (hand_post L q K [iW; iST]) S) M ms' model' ->
     agree (s_next L) E E' -> (forall w, frz_pt E M w -> ms_mem ms' (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)) ->
     ms_regs ms' = R' -> (forall x, Hof E M model x = false -> ms_mem ms' x = m' x) ->
     realizes_cfg SEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg SEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros mem0 L S E M ms model T spl stl iW iST cw cst q K Kn R' m' OWN WS HWS Hd HwL Prsv Pw Pst SP ST HSP HST HK Hms HKR HOWN Hfr Hgr Hk.
  apply (den_run_app_x mem0 L S E M ms model T spl stl iW iST cw cst q K Kn R' m' OWN WS HWS Hd HwL Prsv Pw Pst HSP HST HK Hms HKR HOWN Hfr Hgr).
  intros E' ms' model' HD' Ha' Hfz' Hrr Hvis _ _. exact (Hk E' ms' model' HD' Ha' Hfz' Hrr Hvis).
Qed.
End RunApp.
(* [comment removed for export] *)
End AcRunApp.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma set_nth_length : forall {A} i (x : A) l, List.length (set_nth i x l) = List.length l.
Proof. induction i as [|i IH]; intros x [|y r]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma nth_set_nth : forall {A} i k (x d : A) l, (i < List.length l)%nat -> nth k (set_nth i x l) d = if Nat.eqb k i then x else nth k l d.
Proof.
  induction i as [|i IH]; intros k x d [|y r] Hl; cbn in Hl; try lia.
  - destruct k; reflexivity.
  - destruct k as [|k]; [reflexivity|]. cbn [set_nth nth]. rewrite IH by lia. reflexivity.
Qed.
Lemma map_set_nth : forall {A B} (f : A -> B) i x l, List.map f (set_nth i x l) = set_nth i (f x) (List.map f l).
Proof. induction i as [|i IH]; intros x [|y r]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
Definition pz_step (pz : list Z) (c : Z) : list Z :=
  set_nth (6 + 2 * cidx c) 262144 (set_nth (5 + 2 * cidx c) (z_j pz c + 1) pz).
Lemma cidx_rng : forall c, 1 <= c <= 30 -> (cidx c <= 29)%nat.
Proof. intros c H. unfold cidx. lia. Qed.
Lemma cidx_inj : forall c c', 1 <= c <= 30 -> 1 <= c' <= 30 -> cidx c = cidx c' -> c = c'.
Proof. intros c c' H H' He. unfold cidx in He. lia. Qed.

Section Step.
Variable pz : list Z.
Variable c : Z.
Hypothesis Hlen : List.length pz = PRI_LEN.
Hypothesis Hc : 1 <= c <= 30.

#[using="Hlen Hc"] Lemma zn_step : forall k, zn (pz_step pz c) k =
  if Nat.eqb k (6 + 2 * cidx c) then 262144 else if Nat.eqb k (5 + 2 * cidx c) then z_j pz c + 1 else zn pz k.
Proof. LiaFast.lf_pins (fun (Hlen Hc : LiaFast.U) => LiaFast.u0).
  intros k. pose proof (cidx_rng c Hc) as Hi. unfold zn, pz_step.
  rewrite nth_set_nth by (rewrite set_nth_length, Hlen; unfold PRI_LEN; lia).
  destruct (Nat.eqb k (6 + 2 * cidx c)); [reflexivity|].
  rewrite nth_set_nth by (rewrite Hlen; unfold PRI_LEN; lia). reflexivity.
Qed.
#[using="Hlen"] Lemma step_len : List.length (pz_step pz c) = PRI_LEN.
Proof. LiaFast.lf_pins (fun (Hlen : LiaFast.U) => LiaFast.u0). unfold pz_step. rewrite !set_nth_length. exact Hlen. Qed.
#[using="Hlen Hc"] Lemma step_sb : z_sb (pz_step pz c) = z_sb pz. Proof. LiaFast.lf_pins (fun (Hlen Hc : LiaFast.U) => LiaFast.u0). unfold z_sb. rewrite zn_step. reflexivity. Qed.
#[using="Hlen Hc"] Lemma step_sh : z_sh (pz_step pz c) = z_sh pz. Proof. LiaFast.lf_pins (fun (Hlen Hc : LiaFast.U) => LiaFast.u0). unfold z_sh. rewrite zn_step. reflexivity. Qed.
#[using="Hlen Hc"] Lemma step_ca : z_ca (pz_step pz c) = z_ca pz. Proof. LiaFast.lf_pins (fun (Hlen Hc : LiaFast.U) => LiaFast.u0). unfold z_ca. rewrite zn_step. reflexivity. Qed.
#[using="Hlen Hc"] Lemma step_pg : z_pg (pz_step pz c) = z_pg pz. Proof. LiaFast.lf_pins (fun (Hlen Hc : LiaFast.U) => LiaFast.u0). unfold z_pg. rewrite zn_step. reflexivity. Qed.
#[using="Hlen Hc"] Lemma step_tg : z_tg (pz_step pz c) = z_tg pz. Proof. LiaFast.lf_pins (fun (Hlen Hc : LiaFast.U) => LiaFast.u0). unfold z_tg. rewrite zn_step. reflexivity. Qed.
#[using="Hlen Hc"] Lemma step_qj : z_qj (pz_step pz c) = z_qj pz.
Proof. LiaFast.lf_pins (fun (Hlen Hc : LiaFast.U) => LiaFast.u0). pose proof (cidx_rng c Hc). unfold z_qj. rewrite zn_step. replace (Nat.eqb 65 (6 + 2 * cidx c)) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb 65 (5 + 2 * cidx c)) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity. Qed.
#[using="Hlen Hc"] Lemma step_qn : z_qn (pz_step pz c) = z_qn pz.
Proof. LiaFast.lf_pins (fun (Hlen Hc : LiaFast.U) => LiaFast.u0). pose proof (cidx_rng c Hc). unfold z_qn. rewrite zn_step. replace (Nat.eqb 66 (6 + 2 * cidx c)) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb 66 (5 + 2 * cidx c)) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity. Qed.
#[using="Hlen Hc"] Lemma step_qb : z_qb (pz_step pz c) = z_qb pz.
Proof. LiaFast.lf_pins (fun (Hlen Hc : LiaFast.U) => LiaFast.u0). pose proof (cidx_rng c Hc). unfold z_qb. rewrite zn_step. replace (Nat.eqb 67 (6 + 2 * cidx c)) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb 67 (5 + 2 * cidx c)) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity. Qed.
#[using="Hlen Hc"] Lemma step_gn : z_gn (pz_step pz c) = z_gn pz.
Proof. LiaFast.lf_pins (fun (Hlen Hc : LiaFast.U) => LiaFast.u0). pose proof (cidx_rng c Hc). unfold z_gn. rewrite zn_step. replace (Nat.eqb 68 (6 + 2 * cidx c)) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb 68 (5 + 2 * cidx c)) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity. Qed.
#[using="Hlen Hc"] Lemma step_gl : z_gl (pz_step pz c) = z_gl pz.
Proof. LiaFast.lf_pins (fun (Hlen Hc : LiaFast.U) => LiaFast.u0). pose proof (cidx_rng c Hc). unfold z_gl. rewrite zn_step. replace (Nat.eqb 69 (6 + 2 * cidx c)) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb 69 (5 + 2 * cidx c)) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity. Qed.
#[using="Hlen Hc"] Lemma step_gb : z_gb (pz_step pz c) = z_gb pz.
Proof. LiaFast.lf_pins (fun (Hlen Hc : LiaFast.U) => LiaFast.u0). pose proof (cidx_rng c Hc). unfold z_gb. rewrite zn_step. replace (Nat.eqb 70 (6 + 2 * cidx c)) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb 70 (5 + 2 * cidx c)) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity. Qed.
#[using="Hlen Hc"] Lemma step_j_same : z_j (pz_step pz c) c = z_j pz c + 1.
Proof. LiaFast.lf_pins (fun (Hlen Hc : LiaFast.U) => LiaFast.u0). unfold z_j at 1. rewrite zn_step. replace (Nat.eqb (5 + 2 * cidx c) (6 + 2 * cidx c)) with false by (symmetry; apply Nat.eqb_neq; lia).
  rewrite Nat.eqb_refl. reflexivity. Qed.
#[using="Hlen Hc"] Lemma step_z_same : z_z (pz_step pz c) c = 262144.
Proof. LiaFast.lf_pins (fun (Hlen Hc : LiaFast.U) => LiaFast.u0). unfold z_z. rewrite zn_step. rewrite Nat.eqb_refl. reflexivity. Qed.
#[using="Hlen Hc"] Lemma step_j_other : forall c', 1 <= c' <= 30 -> c' <> c -> z_j (pz_step pz c) c' = z_j pz c'.
Proof. LiaFast.lf_pins (fun (Hlen Hc : LiaFast.U) => LiaFast.u0).
  intros c' Hc' Hne. unfold z_j at 1. rewrite zn_step. assert (cidx c' <> cidx c) by (intros He; apply Hne; exact (cidx_inj c' c Hc' Hc He)).
  replace (Nat.eqb (5 + 2 * cidx c') (6 + 2 * cidx c)) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb (5 + 2 * cidx c') (5 + 2 * cidx c)) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
Qed.
#[using="Hlen Hc"] Lemma step_z_other : forall c', 1 <= c' <= 30 -> c' <> c -> z_z (pz_step pz c) c' = z_z pz c'.
Proof. LiaFast.lf_pins (fun (Hlen Hc : LiaFast.U) => LiaFast.u0).
  intros c' Hc' Hne. unfold z_z at 1. rewrite zn_step. assert (cidx c' <> cidx c) by (intros He; apply Hne; exact (cidx_inj c' c Hc' Hc He)).
  replace (Nat.eqb (6 + 2 * cidx c') (6 + 2 * cidx c)) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb (6 + 2 * cidx c') (5 + 2 * cidx c)) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
Qed.
End Step.

(* [comment removed for export] *)
Lemma pden_step : forall E a c, 0 <= z_j (pden E a) c + 1 < two64 ->
  pden E (with_pri a (a_own (a_step a c)) (pri_step a c)) = pz_step (pden E a) c.
Proof.
  intros E a c Hj. unfold pden. cbn [with_pri a_pri]. unfold pri_step, pz_step. rewrite !map_set_nth. fold (pden E a).
  assert (Ej : uE E (p_j a c) = z_j (pden E a) c) by (symmetry; apply zn_pden).
  rewrite uE_laddc_z by (rewrite Ej; exact Hj). rewrite Ej. rewrite uE_lc by lia. reflexivity.
Qed.
Lemma a_step_pri : forall a c, a_pri (a_step a c) = pri_step a c.
Proof. reflexivity. Qed.
Lemma a_step_eq : forall a c, a_step a c = with_pri a (a_own (a_step a c)) (pri_step a c).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Section Foot.
Variable pz : list Z.
Variable m0 : word -> option byte.
Hypothesis HI : INV_Az pz m0.
(* [comment removed for export] *)
Hypothesis Hdisj : z_tg pz + 4096 <= z_pg pz \/ z_pg pz + PG_SIZE <= z_tg pz.

#[using="m0 HI"] Lemma az_geo : z_pg pz <= z_sb pz /\ z_sb pz + 137438953472 + 4096 <= z_pg pz + 137439023104 /\ z_pg pz + 137439023104 <= 2^47 /\
  17594333495296 <= z_pg pz /\ 17594333495296 <= z_sb pz /\ z_sb pz mod 8 = 0 /\ z_sh pz = z_sb pz / 8 + 2147450880 /\
  2199291686912 <= z_sb pz / 8 /\ z_sb pz / 8 <= 17592186044416 - 17179869184 /\
  z_ca pz = z_tg pz + 208 /\ 4096 <= z_tg pz /\ z_ca pz + 3888 <= 2^47 /\
  (z_tg pz + 4096 <= 2147446784 \/ 17594333495296 <= z_tg pz).
Proof. LiaFast.lf_pins (fun (m0 HI : LiaFast.U) => LiaFast.u0).
  destruct HI as [Hlen Hsb Hsh Hca Hpg Htg Hnsh Hst Hwc Hq Hgq Hcls]. unfold PG_SIZE in Hpg.
  assert (Hm8 : z_sb pz mod 8 = 0).
  { destruct Hsb as [_ Hm]. pose proof (Z.div_mod (z_sb pz) 4096 ltac:(lia)) as Ed. rewrite Hm, Z.add_0_r in Ed. rewrite Ed.
    replace (4096 * (z_sb pz / 4096)) with (512 * (z_sb pz / 4096) * 8) by ring. apply Z.mod_mul. lia. }
  assert (Hd1 : 2199291686912 <= z_sb pz / 8) by (apply Z.div_le_lower_bound; lia).
  assert (Hd2 : z_sb pz / 8 <= 17592186044416 - 17179869184) by (apply Z.div_le_upper_bound; lia).
  repeat split; try lia.
Qed.
(* [comment removed for export] *)
#[using="m0 HI"] Lemma cls_jb : forall c, In c CLS -> 0 <= z_j pz c /\ sz_tbl c * z_j pz c <= 262144 /\ sz_tbl c / 8 * z_j pz c <= 32768 /\
  (z_z pz c = 0 \/ z_z pz c = 262144).
Proof. LiaFast.lf_pins (fun (m0 HI : LiaFast.U) => LiaFast.u0).
  intros c Hc. destruct (cls_tbl c Hc) as (Hszp & Hs8 & Hsz8 & Hnw & Hnm & Hmc). destruct HI as [_ _ _ _ _ _ _ _ _ _ _ Hcls].
  destruct (Hcls c Hc) as [(J0 & Z0 & _)|(J1 & Z1 & Jb & _)]; [rewrite J0; lia|].
  split; [lia|]. split; [nia|]. split; [nia | right; exact Z1].
Qed.
(* [comment removed for export] *)
#[using="m0 HI"] Lemma ext_sem_pt : forall b z x, ext_sem pz b z -> b <= x < b + z ->
  0 <= x < 2^47 /\ alloc_part pz x /\
  (exists c, In c CLS /\ 1 <= z_j pz c /\ z_sb pz + 4294967296 * c <= x < z_sb pz + 4294967296 * c + sz_tbl c * z_j pz c) /\
  (1 <= z_qn pz -> ~ (z_sb pz + 103079215104 + 8192 * z_qj pz <= x < z_sb pz + 103079215104 + 8192 * z_qj pz + 8192)) /\
  (1 <= z_gn pz -> ~ (z_sb pz + 103079215104 + 8192 * z_gl pz <= x < z_sb pz + 103079215104 + 8192 * z_gl pz + 8192)).
Proof. LiaFast.lf_pins (fun (m0 HI : LiaFast.U) => LiaFast.u0).
  intros b z x ((c & Hc & H1 & H2 & _) & HB & HG) Hx. pose proof az_geo as G. pose proof (in_cls_rng c Hc) as Hcr.
  destruct (cls_jb c Hc) as (J0 & J1 & _). destruct (cls_tbl c Hc) as (Hszp & _).
  assert (Hin : z_sb pz + 4294967296 * c <= x < z_sb pz + 4294967296 * c + sz_tbl c * z_j pz c) by lia.
  split; [lia|]. split; [exists c; split; [exact Hc | left; exact Hin]|]. split.
  - exists c. split; [exact Hc|]. split; [|exact Hin]. destruct (Z_le_gt_dec 1 (z_j pz c)) as [Y|Y]; [exact Y|]. exfalso. assert (z_j pz c = 0) by lia. rewrite H in Hin. lia.
  - split; [intros Hq X; destruct (HB Hq) as [Y|Y]; lia | intros Hg X; destruct (HG Hg) as [Y|Y]; lia].
Qed.
(* [comment removed for export] *)
#[using="m0 HI Hdisj"] Lemma ncell_fp : forall c x, In c CLS -> z_z pz c = 262144 -> ncell (z_ca pz) (z_sb pz) c (262144 / sz_tbl c) x ->
  pri_foot_z pz x /\ FPmax pz x /\ ~ alloc_part pz x /\ 0 <= x < 2^47.
Proof. LiaFast.lf_pins (fun (m0 HI Hdisj : LiaFast.U) => LiaFast.u0).
  intros c x Hc Hz Hn. pose proof az_geo as G. pose proof (in_cls_rng c Hc) as Hcr.
  destruct (cls_tbl c Hc) as (Hszp & Hs8 & Hsz8 & Hnw & Hnm & Hmc).
  assert (Hna : forall y, (z_ca pz - 128 <= y < z_ca pz + 2592 \/ z_sb pz + 137438953472 <= y < z_sb pz + 137438953472 + 4096 \/
                           z_sb pz + 4294967296 * c + 3758096384 <= y < z_sb pz + 4294967296 * c + 3758096384 + 262144) -> ~ alloc_part pz y).
  { intros y Hy (c' & Hc' & Ha). pose proof (in_cls_rng c' Hc') as Hcr'. destruct (cls_jb c' Hc') as (J0 & J1 & J2 & _). destruct Ha as [Ha|Ha].
    - destruct Hy as [Hy|[Hy|Hy]]; [| lia |].
      + (* [comment removed for export] *)
        unfold PG_SIZE in Hdisj. lia.
      + assert (c' = c \/ c' <= c - 1 \/ c + 1 <= c') by lia. lia.
    - lia. }
  unfold ncell, foot_Co in Hn. destruct Hn as [[Hn|[Hn|Hn]]|Hn].
  - split; [left; lia|]. split; [right; left; lia|]. split; [apply Hna; left; lia | lia].
  - split; [right; left; lia|]. split; [left; unfold PG_SIZE; lia|]. split; [apply Hna; right; left; lia | lia].
  - split; [right; right; right; exists c; split; [exact Hc|]; right; left; rewrite Hz; lia|]. split; [left; unfold PG_SIZE; lia|]. split; [apply Hna; right; right; lia | lia].
  - split; [left; lia|]. split; [right; left; lia|]. split; [apply Hna; left; lia | lia].
Qed.
(* [comment removed for export] *)
#[using="m0 HI"] Lemma chunk_fp : forall c x, In c CLS -> z_z pz c = 262144 -> z_j pz c + 1 <= 262144 / sz_tbl c ->
  z_sb pz + 4294967296 * c + sz_tbl c * z_j pz c <= x < z_sb pz + 4294967296 * c + sz_tbl c * z_j pz c + sz_tbl c ->
  pri_foot_z pz x /\ FPmax pz x /\ ~ alloc_part pz x /\ 0 <= x < 2^47 /\ x < z_sb pz + 4294967296 * c + 262144.
Proof. LiaFast.lf_pins (fun (m0 HI : LiaFast.U) => LiaFast.u0).
  intros c x Hc Hz Hjb Hx. pose proof az_geo as G. pose proof (in_cls_rng c Hc) as Hcr.
  destruct (cls_tbl c Hc) as (Hszp & Hs8 & Hsz8 & Hnw & Hnm & Hmc). destruct (cls_jb c Hc) as (J0 & J1 & J2 & _).
  assert (Hin : x < z_sb pz + 4294967296 * c + 262144).
  { pose proof (Z.mul_le_mono_nonneg_l (z_j pz c + 1) (262144 / sz_tbl c) (sz_tbl c) ltac:(lia) Hjb) as M1. clear - Hx M1 Hnm. lia. }
  split; [right; right; right; exists c; split; [exact Hc|]; left; rewrite Hz; lia|]. split; [left; unfold PG_SIZE; lia|].
  split; [|lia]. intros (c' & Hc' & Ha). pose proof (in_cls_rng c' Hc') as Hcr'. destruct (cls_jb c' Hc') as (K0 & K1 & K2 & _).
  destruct Ha as [Ha|Ha]; [|lia].
  assert (D : c' = c \/ c' <= c - 1 \/ c + 1 <= c') by lia. destruct D as [->|D]; lia.
Qed.
#[using="m0 HI"] Lemma chsh_fp : forall c x, In c CLS -> z_j pz c + 1 <= 262144 / sz_tbl c ->
  z_sh pz + 536870912 * c + sz_tbl c / 8 * z_j pz c <= x < z_sh pz + 536870912 * c + sz_tbl c / 8 * z_j pz c + sz_tbl c / 8 ->
  pri_foot_z pz x /\ FPmax pz x /\ ~ alloc_part pz x /\ 0 <= x < 2^47 /\ x < z_sh pz + 536870912 * c + 32768.
Proof. LiaFast.lf_pins (fun (m0 HI : LiaFast.U) => LiaFast.u0).
  intros c x Hc Hjb Hx. pose proof az_geo as G. pose proof (in_cls_rng c Hc) as Hcr.
  destruct (cls_tbl c Hc) as (Hszp & Hs8 & Hsz8 & Hnw & Hnm & Hmc). destruct (cls_jb c Hc) as (J0 & J1 & J2 & _).
  assert (Hin : x < z_sh pz + 536870912 * c + 32768).
  { pose proof (Z.mul_le_mono_nonneg_l (z_j pz c + 1) (262144 / sz_tbl c) (sz_tbl c / 8) ltac:(lia) Hjb) as M1.
    assert (M2 : sz_tbl c / 8 * (262144 / sz_tbl c) <= 32768) by (clear - Hnm Hs8 Hsz8; lia). clear - Hx M1 M2. lia. }
  split; [right; right; right; exists c; split; [exact Hc|]; right; right; left; lia|]. split; [right; right; left; lia|].
  split; [|lia]. intros (c' & Hc' & Ha). pose proof (in_cls_rng c' Hc') as Hcr'. destruct (cls_jb c' Hc') as (K0 & K1 & K2 & _).
  destruct Ha as [Ha|Ha]; [lia|].
  assert (D : c' = c \/ c' <= c - 1 \/ c + 1 <= c') by lia. destruct D as [->|D]; lia.
Qed.
(* [comment removed for export] *)
#[using="m0 HI Hdisj"] Lemma virgin_fp : forall c x, In c CLS -> z_j pz c = 0 ->
  (z_ca pz - 128 <= x < z_ca pz + 2592 \/ z_sb pz + 137438953472 <= x < z_sb pz + 137438953472 + 4096 \/
   z_sb pz + 4294967296 * c <= x < z_sb pz + 4294967296 * c + 262144 \/
   z_sb pz + 4294967296 * c + 3758096384 <= x < z_sb pz + 4294967296 * c + 3758096384 + 262144 \/
   z_sh pz + 536870912 * c <= x < z_sh pz + 536870912 * c + 32768 \/
   z_sh pz + 536870912 * c + 469762048 <= x < z_sh pz + 536870912 * c + 469762048 + 32768) ->
  FPmax pz x /\ ~ alloc_part pz x /\ 0 <= x < 2^47.
Proof. LiaFast.lf_pins (fun (m0 HI Hdisj : LiaFast.U) => LiaFast.u0).
  intros c x Hc Hj0 Hx. pose proof az_geo as G. pose proof (in_cls_rng c Hc) as Hcr.
  assert (T1 : z_ca pz + 2592 <= z_pg pz \/ z_pg pz + 137439023104 <= z_ca pz - 128) by (clear - Hdisj G; unfold PG_SIZE in Hdisj; lia).
  assert (S1 : 2199291686912 + 2147450880 <= z_sh pz /\ z_sh pz + 17179869184 <= z_pg pz) by (clear - G; lia).
  assert (S2 : z_ca pz + 2592 <= z_sh pz \/ z_sh pz + 17179869184 <= z_ca pz - 128) by (clear - G S1; lia).
  assert (B0 : 4096 <= z_ca pz - 208 /\ z_ca pz + 3888 <= 2^47 /\ z_pg pz <= z_sb pz /\ z_sb pz + 137438953472 + 4096 <= z_pg pz + 137439023104 /\
               z_pg pz + 137439023104 <= 2^47 /\ 17594333495296 <= z_pg pz) by (clear - G; lia).
  clear G.
  split; [|split].
  - unfold FPmax, PG_SIZE. clear - Hx B0 S1 Hcr. lia.
  - intros (c' & Hc' & Ha). pose proof (in_cls_rng c' Hc') as Hcr'. destruct (cls_jb c' Hc') as (K0 & K1 & K2 & _).
    assert (D : c' = c \/ c' <= c - 1 \/ c + 1 <= c') by lia. destruct D as [->|D].
    + rewrite Hj0 in Ha. rewrite !Z.mul_0_r, !Z.add_0_r in Ha. clear - Ha. lia.
    + destruct Ha as [Ha|Ha].
      * clear - Hx Ha D T1 S1 B0 Hcr Hcr' K0 K1. lia.
      * clear - Hx Ha D S1 S2 B0 Hcr Hcr' K0 K2. lia.
  - clear - Hx B0 S1 Hcr. lia.
Qed.
End Foot.

(* [comment removed for export] *)
Lemma wr_bytes : forall m a n, 0 <= a -> a + n <= 2^64 -> (forall x, a <= x < a + n -> wview SEGS m (wa x) <> None) -> wr m a n.
Proof.
  intros m a n Ha Hn H d k Hd Hk. destruct k as [|k]; [reflexivity|]. rewrite Nat2Z.inj_succ in Hk.
  apply store_ok_of_all; [rewrite u_wa_small by lia; rewrite Nat2Z.inj_succ; lia|].
  intros x Hx. rewrite u_wa_small in Hx by lia. rewrite Nat2Z.inj_succ in Hx. rewrite <- (wa_u x). apply H. lia.
Qed.
Lemma wr_byte : forall m a n x, 0 <= a -> a + n <= 2^64 -> wr m a n -> a <= x < a + n -> wview SEGS m (wa x) <> None.
Proof.
  intros m a n x Ha Hn W Hx. pose proof (W (x - a) 1%nat ltac:(lia) ltac:(lia)) as S1. replace (a + (x - a)) with x in S1 by lia.
  cbn [store_ok] in S1. destruct (wview SEGS m (wa x)); [discriminate | discriminate].
Qed.
Lemma wview_same : forall (m m' : word -> option byte) x, m' x = m x -> wview SEGS m' x = wview SEGS m x.
Proof. intros m m' x H. unfold wview. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma pri_foot_own : forall E a m0, INV_A E a m0 -> forall x, pri_foot E a x ->
  exists p, In p (pri_own a) /\ uE E (fst p) <= x < uE E (fst p) + uE E (snd p).
Proof.
  intros E a m0 HI x Hx. pose proof HI as HI0. destruct HI0 as [Hlen Hsb Hsh Hca Hpg Htg Hnsh Hst Hwc Hq Hgq Hcls]. unfold PG_SIZE in Hpg.
  assert (Zsb : uE E (p_sb a) = z_sb (pden E a)) by (symmetry; apply zn_pden).
  assert (Zsh : uE E (p_sh a) = z_sh (pden E a)) by (symmetry; apply zn_pden).
  assert (Zca : uE E (p_ca a) = z_ca (pden E a)) by (symmetry; apply zn_pden).
  assert (Hshb : 0 <= z_sb (pden E a) / 8 <= 2^44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  unfold pri_foot, pri_foot_z in Hx. unfold pri_own. destruct Hx as [Hx|[Hx|[Hx|(c & Hc & Hx)]]];
    [| | exists (lconst 930696, lconst 40); split; [right; right; left; reflexivity|]; cbn [fst snd]; rewrite !uE_lc by lia; lia |].
  - exists (l_cb a, lconst CB_SIZE). split; [left; reflexivity|]. cbn [fst snd]. unfold CB_SIZE. rewrite uE_lc by lia.
    unfold l_cb. rewrite uE_laddc_z by (rewrite Zca; unfold two64; lia). rewrite Zca. lia.
  - exists (l_rip a, lconst 4096). split; [right; left; reflexivity|]. cbn [fst snd]. rewrite uE_lc by lia.
    unfold l_rip. rewrite uE_laddc2 by (rewrite ?Zsb; unfold two64; lia). rewrite Zsb. lia.
  - pose proof (in_cls_rng c Hc) as Hcr. assert (Zz : uE E (p_z a c) = z_z (pden E a) c) by (symmetry; apply zn_pden).
    assert (Hin : forall p, In p (cls_own a c) -> In p ((l_cb a, lconst CB_SIZE) :: (l_rip a, lconst 4096) :: (lconst 930696, lconst 40) :: flat_map (cls_own a) CLS)).
    { intros p Hp. right. right. right. apply in_flat_map. exists c. split; [exact Hc | exact Hp]. }
    destruct Hx as [Hx|[Hx|[Hx|Hx]]].
    + exists (l_rb a c, p_z a c). split; [apply Hin; left; reflexivity|]. cbn [fst snd]. unfold l_rb.
      rewrite uE_laddc2 by (rewrite ?Zsb; unfold two64; lia). rewrite Zsb, Zz. lia.
    + exists (l_fa a c, p_z a c). split; [apply Hin; right; left; reflexivity|]. cbn [fst snd]. unfold l_fa.
      rewrite uE_laddc2 by (rewrite ?Zsb; unfold two64; lia). rewrite Zsb, Zz. lia.
    + exists (l_shu a c, lconst 32768). split; [apply Hin; right; right; left; reflexivity|]. cbn [fst snd]. unfold l_shu. rewrite uE_lc by lia.
      rewrite uE_laddc2 by (rewrite ?Zsh, ?Hsh; unfold two64; lia). rewrite Zsh. lia.
    + exists (l_shf a c, lconst 32768). split; [apply Hin; right; right; right; left; reflexivity|]. cbn [fst snd]. unfold l_shf. rewrite uE_lc by lia.
      rewrite uE_laddc2 by (rewrite ?Zsh, ?Hsh; unfold two64; lia). rewrite Zsh. lia.
Qed.

(* [comment removed for export] *)
Definition cls_foot (CA SB SH c z x : Z) : Prop :=
  CA + 80 * c <= x < CA + 80 * c + 80 \/ SB + 137438953472 + 128 * c <= x < SB + 137438953472 + 128 * c + 128 \/
  SB + 4294967296 * c <= x < SB + 4294967296 * c + z \/
  SB + 4294967296 * c + 3758096384 <= x < SB + 4294967296 * c + 3758096384 + z \/
  SH + 536870912 * c <= x < SH + 536870912 * c + 32768 \/
  SH + 536870912 * c + 469762048 <= x < SH + 536870912 * c + 469762048 + 32768.
Lemma cls_inv_frame : forall (m0 m0' : word -> option byte) CA SB SH c j z, In c CLS ->
  0 <= CA -> CA + 4096 <= 2^63 -> 0 <= SB -> SB + 137438953472 + 4096 <= 2^63 -> 0 <= SH -> SH + 17179869184 <= 2^63 -> 0 <= j ->
  (forall x, cls_foot CA SB SH c z x -> m0' (wa x) = m0 (wa x)) -> cls_inv m0 CA SB SH c j z -> cls_inv m0' CA SB SH c j z.
Proof.
  intros m0 m0' CA SB SH c j z Hc H1 H2 H3 H4 H5 H6 Hj0 HF Hcl. pose proof (in_cls_rng c Hc) as Hcr.
  destruct (cls_tbl c Hc) as (Hsz & Hs8 & Hs8r & Hnw & Hnm & Hmc).
  destruct Hcl as [(J0 & Z0 & HV & HSW)|(J1 & Z1 & Jb & HI & HP)]; [left | right].
  - split; [exact J0|]. split; [exact Z0|]. split.
    + apply (VIRG_C_frame m0); [lia | lia | lia | lia | lia | | exact HV].
      intros x Hx. apply HF. unfold foot_V in Hx. unfold cls_foot. lia.
    + destruct HSW as [W1 W2]. split.
      * apply (wr_frame m0); [lia | lia | | exact W1]. intros x Hx. apply HF. unfold cls_foot. lia.
      * apply (wr_frame m0); [lia | lia | | exact W2]. intros x Hx. apply HF. unfold cls_foot. lia.
  - split; [exact J1|]. split; [exact Z1|]. split; [exact Jb|]. split.
    + apply (INV_Co_frame m0); [lia | lia | lia | lia | | exact HI].
      intros x Hx. apply HF. unfold foot_Co in Hx. unfold cls_foot. rewrite Z1. lia.
    + apply (POP_C_frame m0); [| nia | exact HP].
      intros x Hx. apply HF. unfold RBX, SHX in Hx. unfold cls_foot. rewrite Z1.
      assert (0 <= sz_tbl c * j) by nia. assert (0 <= sz_tbl c / 8 * j) by nia. lia.
Qed.

Lemma INV_Az_step : forall pz m0 m0' c, INV_Az pz m0 -> (z_tg pz + 4096 <= z_pg pz \/ z_pg pz + PG_SIZE <= z_tg pz) -> In c CLS ->
  z_j pz c + 1 + mc_tbl c / 2 <= 262144 / sz_tbl c ->
  INV_Co m0' (z_ca pz) (z_sb pz) c (sz_tbl c) (mc_tbl c / 2) (262144 / sz_tbl c) (z_j pz c + 1) ->
  POP_C m0' (z_sb pz) (z_sh pz) c (sz_tbl c) (z_j pz c + 1) -> STATS m0' (z_ca pz) ->
  (forall x, pri_foot_z pz x -> ~ owned_C (z_ca pz) (z_sb pz) c x -> m0' (wa x) = m0 (wa x)) ->
  INV_Az (pz_step pz c) m0'.
Proof.
  intros pz m0 m0' c HI Hdisj Hc Hjb HIo HPo HSt HF. pose proof (az_geo pz m0 HI) as G. pose proof (in_cls_rng c Hc) as Hcr.
  pose proof HI as HI0. destruct HI0 as [Hlen Hsb Hsh Hca Hpg Htg Hnsh Hst Hwc Hq Hgq Hcls].
  destruct (cls_jb pz m0 HI c Hc) as (J0 & _).
  unfold PG_SIZE in Hpg, Hdisj.
  (* [comment removed for export] *)
  assert (T1 : z_ca pz + 2592 <= z_pg pz \/ z_pg pz + 137439023104 <= z_ca pz - 128) by (clear - Hdisj Htg; lia).
  assert (S1 : 2199291686912 + 2147450880 <= z_sh pz /\ z_sh pz + 17179869184 <= z_pg pz) by (clear - G; lia).
  assert (S2 : z_ca pz + 2592 <= z_sh pz \/ z_sh pz + 17179869184 <= z_ca pz - 128) by (clear - G S1 Htg; lia).
  assert (B0 : 4096 <= z_ca pz - 208 /\ z_ca pz + 3888 <= 2^47 /\ z_pg pz <= z_sb pz /\ z_sb pz + 137438953472 + 4096 <= z_pg pz + 137439023104 /\
               z_pg pz + 137439023104 <= 2^47 /\ 17594333495296 <= z_pg pz) by (clear - G; lia).
  assert (P0 : z_ca pz + 3888 <= 65536 \/ 6537424 <= z_ca pz) by (clear - Hca; lia).
  clear G Hsb Hsh Hca Hpg Htg Hnsh Hdisj.
  (* [comment removed for export] *)
  assert (HFcb : forall x, z_ca pz - 128 <= x < z_ca pz + 2592 -> ~ (z_ca pz + 80 * c <= x < z_ca pz + 80 * c + 80) -> ~ (z_ca pz + 2560 <= x) -> m0' (wa x) = m0 (wa x)).
  { intros x Hx N1 N2. apply HF; [left; exact Hx|]. unfold owned_C. clear - Hx N1 N2 T1 B0 Hcr. lia. }
  constructor; rewrite ?(step_sb pz c Hlen Hcr), ?(step_sh pz c Hlen Hcr), ?(step_ca pz c Hlen Hcr), ?(step_pg pz c Hlen Hcr), ?(step_tg pz c Hlen Hcr),
    ?(step_qj pz c Hlen Hcr), ?(step_qn pz c Hlen Hcr), ?(step_qb pz c Hlen Hcr), ?(step_gn pz c Hlen Hcr), ?(step_gl pz c Hlen Hcr), ?(step_gb pz c Hlen Hcr); try assumption.
  - exact (step_len pz c Hlen).
  - exact (proj1 (iz_sb _ _ HI), proj2 (iz_sb _ _ HI)) || exact (iz_sb _ _ HI).
  - exact (iz_sh _ _ HI).
  - exact (iz_ca _ _ HI).
  - exact (iz_pg _ _ HI).
  - exact (iz_tg _ _ HI).
  - exact (iz_nsh _ _ HI).
  - (* [comment removed for export] *)
    apply wr_bytes; [clear - B0; lia | clear - B0; lia |]. intros x Hx.
    destruct (Z_lt_le_dec x (z_ca pz + 80 * c)) as [L1|L1]; [|destruct (Z_lt_le_dec x (z_ca pz + 80 * c + 80)) as [L2|L2];
      [|destruct (Z_lt_le_dec x (z_ca pz + 2560)) as [L3|L3]]].
    + rewrite (wview_same m0 m0'); [exact (wr_byte m0 (z_ca pz - 128) 2720 x ltac:(clear - B0; lia) ltac:(clear - B0; lia) Hwc ltac:(clear - Hx; lia))|].
      apply HFcb; clear - Hx L1 Hcr; lia.
    + destruct HIo as [_ _ _ _ _ _ _ _ _ W _]. exact (wr_byte m0' (z_ca pz + 80 * c) 80 x ltac:(clear - B0 Hcr; lia) ltac:(clear - B0 Hcr; lia) W ltac:(clear - L1 L2; lia)).
    + rewrite (wview_same m0 m0'); [exact (wr_byte m0 (z_ca pz - 128) 2720 x ltac:(clear - B0; lia) ltac:(clear - B0; lia) Hwc ltac:(clear - Hx; lia))|].
      apply HFcb; clear - Hx L2 L3 Hcr; lia.
    + destruct HSt as (_ & _ & W). exact (wr_byte m0' (z_ca pz + 2560) 32 x ltac:(clear - B0; lia) ltac:(clear - B0; lia) W ltac:(clear - L3 Hx; lia)).
  - (* [comment removed for export] *)
    assert (HQC : forall x, z_ca pz - 128 <= x < z_ca pz - 96 -> m0' (wa x) = m0 (wa x)).
    { intros x Hx. apply HFcb; clear - Hx Hcr; lia. }
    destruct Hq as [(Hqb & Rqb & Hq) Hqj]. split.
    + split; [exact Hqb|]. split.
      { apply (rd_frame m0); [clear - B0; lia | cbn; clear - B0; lia | intros x Hx; cbn in Hx; apply HQC; clear - Hx; lia | exact Rqb]. }
      destruct Hq as [(Q0 & Qb0 & R0)|(Q1 & Q2 & R1 & R1b & R2 & R3 & R4 & W1)]; [left | right].
      * split; [exact Q0|]. split; [exact Qb0|]. apply (rd_frame m0); [clear - B0; lia | cbn; clear - B0; lia | intros x Hx; cbn in Hx; apply HQC; clear - Hx; lia | exact R0].
      * assert (Z24 : z_z pz 24 = 262144).
        { destruct (Hcls 24 in_cls_24) as [(J24 & _)|(_ & Z1 & _)]; [specialize (Hqj ltac:(clear - Q1; lia)); clear - Hqj J24 Q2; lia | exact Z1]. }
        assert (HB : forall x, z_sb pz + 103079215104 + 8192 * z_qj pz <= x < z_sb pz + 103079215104 + 8192 * z_qj pz + 8192 -> m0' (wa x) = m0 (wa x)).
        { intros x Hx. apply HF; [right; right; right; exists 24; split; [exact in_cls_24|]; left; rewrite Z24; clear - Hx Q2; lia | unfold owned_C; clear - Hx Q2 T1 B0 Hcr; lia]. }
        split; [exact Q1|]. split; [exact Q2|]. split; [|split; [|split; [|split; [|split]]]].
        -- apply (rd_frame m0); [clear - B0; lia | cbn; clear - B0; lia | intros x Hx; cbn in Hx; apply HQC; clear - Hx; lia | exact R1].
        -- apply (rd_frame m0); [clear - B0; lia | cbn; clear - B0; lia | intros x Hx; cbn in Hx; apply HQC; clear - Hx; lia | exact R1b].
        -- apply (rd_frame m0); [clear - B0; lia | cbn; clear - B0; lia | intros x Hx; cbn in Hx; apply HQC; clear - Hx; lia | exact R2].
        -- apply (rd_frame m0); [clear - B0 Q2; lia | cbn; clear - B0 Q2; lia | intros x Hx; cbn in Hx; apply HB; clear - Hx; lia | exact R3].
        -- apply (rd_frame m0); [clear - B0 Q2; lia | cbn; clear - B0 Q2; lia | intros x Hx; cbn in Hx; apply HB; clear - Hx; lia | exact R4].
        -- apply (wr_frame m0); [clear - B0 Q2; lia | clear - B0 Q2; lia | intros x Hx; apply HB; clear - Hx; lia | exact W1].
    + intros Hqn. specialize (Hqj Hqn). destruct (Z.eq_dec c 24) as [->|Hne].
      * rewrite (step_j_same pz 24 Hlen ltac:(lia)). clear - Hqj. lia.
      * rewrite (step_j_other pz c Hlen Hcr 24 ltac:(lia) ltac:(congruence)). exact Hqj.
  - (* [comment removed for export] *)
    destruct Hgq as [Hg Hgl]. split.
    + apply (gq_inv_o_frame m0 m0' (z_sb pz) (z_gn pz) (z_gl pz) (z_gb pz) ltac:(clear - B0; lia) ltac:(clear - B0; lia)); [|exact Hg].
      intros x [Hx|(Hg1 & Hx)].
      * apply HF; [right; right; left; exact Hx | unfold owned_C; clear - Hx P0 B0 Hcr; lia].
      * assert (Z24 : z_z pz 24 = 262144).
        { destruct (Hcls 24 in_cls_24) as [(J24 & _)|(_ & Z1 & _)]; [specialize (Hgl Hg1); destruct Hg as (_ & _ & _ & _ & _ & _ & _ & _ & [(G0 & _)|(_ & G1 & _)]); [clear - G0 Hg1; lia | clear - Hgl J24 G1; lia] | exact Z1]. }
        assert (Gl : 0 <= z_gl pz < 32) by (destruct Hg as (_ & _ & _ & _ & _ & _ & _ & _ & [(G0 & _)|(_ & G1 & _)]); [clear - G0 Hg1; lia | exact G1]).
        apply HF; [right; right; right; exists 24; split; [exact in_cls_24|]; left; rewrite Z24; clear - Hx Gl; lia | unfold owned_C; clear - Hx Gl T1 B0 Hcr; lia].
    + intros Hgn. specialize (Hgl Hgn). destruct (Z.eq_dec c 24) as [->|Hne].
      * rewrite (step_j_same pz 24 Hlen ltac:(lia)). clear - Hgl. lia.
      * rewrite (step_j_other pz c Hlen Hcr 24 ltac:(lia) ltac:(congruence)). exact Hgl.
  - (* [comment removed for export] *)
    intros c' Hc'. pose proof (in_cls_rng c' Hc') as Hcr'. destruct (Z.eq_dec c' c) as [->|Hne].
    + rewrite (step_j_same pz c Hlen Hcr), (step_z_same pz c Hlen Hcr). right.
      split; [clear - J0; lia|]. split; [reflexivity|]. split; [clear - Hjb; lia|]. split; [exact HIo | exact HPo].
    + rewrite (step_j_other pz c Hlen Hcr c' Hcr' Hne), (step_z_other pz c Hlen Hcr c' Hcr' Hne).
      destruct (cls_jb pz m0 HI c' Hc') as (K0 & _ & _ & Kz).
      apply (cls_inv_frame m0 m0' _ _ _ c' _ _ Hc'); [clear - B0; lia | clear - B0; lia | clear - B0; lia | clear - B0; lia | clear - S1; lia | clear - S1 B0; lia | exact K0 | | exact (Hcls c' Hc')].
      intros x Hx. unfold cls_foot in Hx.
      assert (D : c' <= c - 1 \/ c + 1 <= c') by (clear - Hne; lia).
      assert (Kz' : 0 <= z_z pz c' <= 262144) by (clear - Kz; lia).
      destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]].
      * apply HF; [left; clear - Hx Hcr'; lia | unfold owned_C; clear - Hx D T1 B0 Hcr Hcr'; lia].
      * apply HF; [right; left; clear - Hx Hcr'; lia | unfold owned_C; clear - Hx D T1 B0 Hcr Hcr'; lia].
      * apply HF; [right; right; right; exists c'; split; [exact Hc'|]; left; exact Hx | unfold owned_C; clear - Hx Kz' T1 B0 Hcr Hcr'; lia].
      * apply HF; [right; right; right; exists c'; split; [exact Hc'|]; right; left; exact Hx | unfold owned_C; clear - Hx Kz' T1 B0 Hcr Hcr'; lia].
      * apply HF; [right; right; right; exists c'; split; [exact Hc'|]; right; right; left; exact Hx | unfold owned_C; clear - Hx S1 S2 B0 Hcr Hcr'; lia].
      * apply HF; [right; right; right; exists c'; split; [exact Hc'|]; right; right; right; exact Hx | unfold owned_C; clear - Hx S1 S2 B0 Hcr Hcr'; lia].
Qed.

(* [comment removed for export] *)
Lemma lwf_p_nth : forall n a k, forallb (lwf n) (a_pri a) = true -> lwf n (p_nth a k) = true.
Proof.
  intros n a k H. unfold p_nth. destruct (nth_in_or_default k (a_pri a) lc0) as [Hin|He]; [|rewrite He; reflexivity].
  rewrite forallb_forall in H. exact (H _ Hin).
Qed.
Lemma lwf_chunk_lin : forall n a c, forallb (lwf n) (a_pri a) = true -> lwf n (chunk_lin a c) = true /\ lwf n (chsh_lin a c) = true.
Proof.
  intros n a c H. unfold chunk_lin, chsh_lin, p_sb, p_sh, p_j.
  split; apply lwf_laddc, lwf_ladd; first [apply lwf_lscale|idtac]; apply lwf_p_nth; exact H.
Qed.
Lemma u_lin3 : forall E b j k s, 0 <= s -> 0 <= k -> uE E b + s * uE E j + k < two64 ->
  uE E (laddc (ladd b (lscale s j)) k) = uE E b + s * uE E j + k.
Proof.
  intros E b j k s Hs Hk H. pose proof (uE_range E b) as Rb. pose proof (uE_range E j) as Rj.
  assert (Hm : 0 <= s * uE E j) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Esc : uE E (lscale s j) = s * uE E j) by (unfold uE in *; rewrite lden_lscale; apply u_small64; lia).
  assert (Ead : uE E (ladd b (lscale s j)) = uE E b + s * uE E j).
  { unfold uE in *. rewrite ladd_u2 by (rewrite Esc; lia). rewrite Esc. reflexivity. }
  rewrite uE_laddc2 by (rewrite ?Ead; lia). rewrite Ead. reflexivity.
Qed.

(* [comment removed for export] *)
Definition ncell_b (CA SB c newc x : Z) : bool :=
  ((CA + 80 * c <=? x) && (x <? CA + 80 * c + 80) || (SB + 137438953472 + 128 * c <=? x) && (x <? SB + 137438953472 + 128 * c + 128) ||
   (SB + c * 4294967296 + 3758096384 <=? x) && (x <? SB + c * 4294967296 + 3758096384 + 4 * newc) || (CA + 2560 <=? x) && (x <? CA + 2592))%bool.
Lemma ncell_b_spec : forall CA SB c newc x, ncell_b CA SB c newc x = true <-> ncell CA SB c newc x.
Proof.
  intros CA SB c newc x. unfold ncell_b, ncell, foot_Co. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le, !Z.ltb_lt. tauto.
Qed.
Definition hyb_p (P : Z -> bool) (m' m0 : word -> option byte) : word -> option byte :=
  fun x => if P (bv_unsigned x) then m' x else m0 x.

(* [comment removed for export] *)
Lemma fa_cont_get : forall k acc p v, tget p (fa_cont k acc) = Some v -> (v = BK 250 /\ Zpos p - 1 < Z.of_nat k) \/ tget p acc = Some v.
Proof.
  induction k as [|k IH]; intros acc p v H; cbn [fa_cont] in H; [right; exact H|].
  destruct (IH _ p v H) as [[H1 H2]|H1]; [left; split; [exact H1 | lia]|].
  destruct (Pos.eq_dec p (Pos.of_succ_nat k)) as [->|Hne].
  - rewrite tget_tset_same in H1. injection H1 as <-. left. split; [reflexivity|]. rewrite Zpos_P_of_succ_nat. lia.
  - rewrite tget_tset_other in H1 by (intros Hc; apply Hne; symmetry; exact Hc). right. exact H1.
Qed.
(* [comment removed for export] *)
