(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit FPSteps FPStepsV.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptRoom LeptExec LeptExecW LeptExecFP.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptBase.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL7a.
Import V15CL7a.V15LeptErr.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL8a.
Import V15CL8a.V15LeptPixHdr.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptPixCreate.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL9a.
Import V15CL9a.V15LeptPixDestroy.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL10a.
Import V15CL10a.V15LeptCmapValid. Import V15CL10a.V15LeptPixCreateS.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptCmap2 V15LeptPixCopyA V15LeptPixCopy V15LeptPixHdrS V15LeptPixDestroyK.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL14a.
Import V15CL14a.V15LeptThrLeaf. Import V15CL14a.V15LeptDither_iface. Import V15CL14a.V15LeptDithBinW.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL15a.
Import V15CL15a.V15LeptPixDestroyRc2.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import LeptExecT LeptArith LeptRoomPC LeptRoom14.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Chain.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
(* [comment removed for export] *)
#[local] Existing Instance exf_fxd | 100.

Definition STOPS : list Z := [93000; 95132; 95788; 106268; 166172; 112988; 166484; 94372]%Z.
Definition FDEF : list (nat * nat) := [(8%nat, 33%nat)].
Definition PC_PIXCREATE : word := 93000%bv.
Lemma PC_PIXCREATE_eq : Z_to_bv 64 93000 = PC_PIXCREATE. Proof. apply bv_eq; reflexivity. Qed.
Definition PC_DESTROY : word := 94372%bv.
Lemma PC_DESTROY_eq : Z_to_bv 64 94372 = PC_DESTROY. Proof. apply bv_eq; reflexivity. Qed.
Definition ex_r14 : reg := 14%bv. Definition ex_r15 : reg := 15%bv. Definition ex_r16 : reg := 16%bv. Definition ex_r17 : reg := 17%bv. Definition ex_r28 : reg := 28%bv. Definition ex_r29 : reg := 29%bv.

Lemma cmf_keep : forall (fx : FPState) (A A' : AS) (m m' : word -> option byte) (cm : Z) (cv : cmapv), cm_facts A m cm cv -> sub_live A A' -> LIVK A m m' -> cm_facts A' m' cm cv.
Proof.
  intros fx A A' m m' cm cv [->|(CM & OK & L1 & L2)] SUB LK; [left; reflexivity | right].
  split; [exact (exT_cmap_livk A m m' cm cv CM LK L1) | split; [exact OK | split; [exact (SUB _ _ L1) | exact (SUB _ _ L2)]]].
Qed.
Lemma fresh_sub : forall (Ar A : AS) (q : word), sub_live Ar A -> live A q = None -> live Ar q = None.
Proof. intros Ar A q SUB F. destruct (live Ar q) as [k|] eqn:EE; [|reflexivity]. rewrite (SUB _ _ EE) in F. discriminate F. Qed.
Lemma ne_live : forall (A : AS) (p q : word) (k : Z), live A p = Some k -> live A q = None -> p <> q.
Proof. intros A p q k L F ->. rewrite F in L. discriminate L. Qed.
Lemma hdr_ok_8_1 : forall w h, hdr_ok w h 8 -> (1 <= w)%Z -> (1 <= h)%Z -> hdr_ok w h 1.
Proof.
  intros w h HOK Hw Hh. destruct (dith_wpl_facts w h HOK Hw Hh) as (_ & _ & _ & _ & _ & _ & P1 & _). destruct HOK as (_ & X & Y & _).
  split; [unfold dval; tauto|]. split; [exact X|]. split; [exact Y|]. lia.
Qed.
(* [comment removed for export] *)
Lemma pix_keepb : forall (A : AS) (M m' : word -> option byte) (p : Z) (v : pixv) (d b1 b2 : word), PIXat M p v -> live A (Z_to_bv 64 p) = Some 64%Z ->
  Z_to_bv 64 p <> d -> Z_to_bv 64 p <> b1 -> Z_to_bv 64 p <> b2 ->
  (forall (q : word) k, live A q = Some k -> q <> d -> q <> b1 -> q <> b2 -> forall i, (0 <= i < k)%Z -> m' (at_ q i) = M (at_ q i)) -> PIXat m' p v.
Proof.
  intros A M m' p v d b1 b2 PX L N1 N2 N3 KB. pose proof PX as (Hp0 & Hp64 & _). apply (PIXat_frame M); [exact PX|]. intros x Hx.
  pose proof (KB _ _ L N1 N2 N3 (u x - p)%Z ltac:(lia)) as EE.
  replace (at_ (Z_to_bv 64 p) (u x - p)) with x in EE by (unfold at_; apply bv_eq; rewrite !u_Z2bv; rewrite ?u_Z2bv; pose proof (u64_range x); lia).
  exact EE.
Qed.

Section Spec.
Hypothesis HRMC : pixRemoveColormap_gray8_contract.

Theorem pixDitherToBinary_W : pixDitherToBinary_contract.
Proof.
  unfold pixDitherToBinary_contract, PC_pixDitherToBinary, TP15.
  intros fx C A0 m0 md r0 s pixs w h cm data cv ret S FZ CK HW0 H2 Hs16 Hlo0 Hhi H1 Hret H4 H10 PXs HOK Hw1 Hh1 Lpixs_a0 F0pixs Ldata_a0 CMF kR bR RM0 HkR HbR HC.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  assert (HTP : ex_keep (getr r0 ex_r4 = Z_to_bv 64 284096)) by exact H4.
  assert (Hlo : (c_top C - LSTK + 256 <= s)%Z) by (unfold DBIN_STACK, RMC_STACK, LSF in Hlo0; lia).
  assert (Hlo1 : (c_top C - LSTK + 4000 <= s)%Z) by (unfold DBIN_STACK, RMC_STACK, LSF in Hlo0; lia). clear Hlo0.
  assert (HkR' : (RK_pix + RK_rmc + 2 <= kR)%Z) by (unfold RK_dbin in HkR; lia).
  assert (HbR' : (RB_pix14 + RB_rmc + 2 * 2 ^ 21 <= bR)%Z) by (unfold RB_dbin in HbR; lia). clear HkR HbR.
  destruct fx as [fr cs]. cbn [fp_csr] in FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 256)%Z) by lia.
  assert (GLO2 : (s - 256 + Z.of_nat (Z.to_nat 256) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (256 <= s)%Z) by lia.
  pose proof (hdr_ok_8_1 w h HOK Hw1 Hh1) as HOK1.
  destruct (dith_wpl_facts w h HOK Hw1 Hh1) as (Gwpls & Gwpld & _ & _ & _ & Psh & Pdh & Psh1 & Pdh1).
  assert (Rw : (0 <= w < 2 ^ 31)%Z) by (destruct HOK as (_ & X & _); lia). assert (Rh : (0 <= h < 2 ^ 31)%Z) by (destruct HOK as (_ & _ & X & _); lia).
  assert (Rnd : (0 < 4 * (wpl_of w 1 * h))%Z) by lia. assert (Rns : (0 < 4 * (wpl_of w 8 * h))%Z) by lia. assert (Rnb : (0 < 4 * wpl_of w 8)%Z) by lia.
  assert (MGB : (alloc_margin (wpl_of w 8 * 4) <= 2 ^ 21)%Z) by (pose proof (alloc_margin_big (wpl_of w 8 * 4) ltac:(lia)); lia).
  assert (RBpos : (0 <= RB_pix14 /\ 0 <= RB_rmc)%Z) by (unfold RB_rmc, RB_pix14, RB_hdr; lia).
  assert (Hs8 : (s mod 8 = 0)%Z).
  { apply Z.mod_divide in Hs16; [|lia]. destruct Hs16 as [q0 Eq0]. rewrite Eq0. replace (q0 * 16)%Z with (q0 * 2 * 8)%Z by lia. apply Z_mod_mult. }
  pose proof PXs as (Hps0 & Hps64 & _). assert (RRpixs : (0 <= pixs < 2 ^ 64)%Z) by lia.
  pose proof (ai_live_hull A0 m0 (m_vmmaps md) _ _ (w_inv _ _ _ _ HW0) Lpixs_a0) as (_ & ALpixs & _). rewrite u_Z2bv in ALpixs by lia.
  pose proof (exW_win_blk_apart_h C A0 m0 _ s 256 pixs 64 CK HW0 Lpixs_a0 ltac:(lia) RRpixs ltac:(lia)) as WAPpixs.
  assert (Rpixs2 : (4096 <= pixs)%Z /\ (pixs + 64 <= alloc_top (c_vm C))%Z).
  { destruct (blk_range C A0 m0 _ (Z_to_bv 64 pixs) 64 CK HW0 Lpixs_a0 ltac:(lia)) as [G1 G2]. rewrite u_Z2bv in G1, G2 by lia. split; [exact G1 | lia]. }
  pose proof (PIX_rd_w SEGS _ _ _ PXs) as Cw. rewrite <- (Z.add_0_r pixs) in Cw. cbn [p_w hdv] in Cw.
  pose proof (PIX_rd_h SEGS _ _ _ PXs) as Ch. cbn [p_h hdv] in Ch.
  pose proof (PIX_rd_d SEGS _ _ _ PXs) as Cd. cbn [p_d hdv] in Cd.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 256) (Z.to_nat 256) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; exW_canary SEGS 415784 m0]) (EVar 37) (EVar 32) (exW_canary SEGS 415784 m0) s 256 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 430336 (2 ^ 63); KAlign (EVar 32) 16; KRange (EVar 34) 1 (2 ^ 47); KAlign (EVar 34) 16; KDisj (SA (EVar 32) (-256)) 256 (SA (EVar 34) 0) 64; KWord (SA (EVar 34) 0) 4 (EVar 35); KWord (SA (EVar 34) 4) 4 (EVar 36); KWord (SA (EVar 34) 8) 4 (ELit 8); KRange (EVar 35) 0 (2 ^ 31 - 1); KRange (EVar 36) 0 (2 ^ 31 - 1)]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 HKf0)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 256 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  pose proof (exW_win_only E0 m0 log0 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs0. change (mem_denot E0 m0 log0) with M0 in FRs0.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r12 Q12_0. exW_regfactB BS0 HR ex_r1 Q1_0. exW_regfactB BS0 HR ex_r2 Q2_0. exW_regfactB BS0 HR ex_r4 Q4_0.
  clear BS0.
  lazymatch type of Q2_0 with _ = Z_to_bv 64 (s + ?off) => pose (OFF0 := off) end.
  (* [comment removed for export] *)
  rewrite PC_PIXCREATE_eq.
  lazymatch type of Q1_0 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixCreate_sure_W (fx := fxk) C A0 M0 _ Rc0 (s + OFF0) w h 1 (Z_to_bv 64 ra) S CK HWs0 Q2_0
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF0, LSF; lia) ltac:(unfold OFF0; lia) Q1_0 ltac:(red; apply bv_eq; reflexivity) Q4_0 Q10_0 Q11_0 Q12_0 Hw1 Hh1 HOK1 kR bR
             ltac:(rewrite with_vmmaps_vmmaps; exact RM0) ltac:(clear - HkR'; unfold RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' RBpos; lia)) end end.
  intros A1 m1 vm1 r1 pixd datad HW1 CSx0 PMc0 A10_0 PXN RM1.
  pose proof CSx0 as CS0. clear CSx0.
  rewrite with_vmmaps_twice in HW1 |- *.
  destruct PXN as (Gpd1 & Gpd2 & ALpixd & Gdd1 & Gdd2 & ALdatad & NEpd & Fpixd & Fdatad & F0pixd & F0datad & Lpixd_a1 & Ldatad_a1 & LEQ0 & PXd1 & _).
  change (p_wpl (set_data (pix_hdr w h 1) datad)) with (wpl_of w 1) in Gdd2, Ldatad_a1. change (p_h (set_data (pix_hdr w h 1) datad)) with h in Gdd2, Ldatad_a1.
  assert (RRpixd : (0 <= pixd < 2 ^ 64)%Z) by lia. assert (RRdatad : (0 <= datad < 2 ^ 64)%Z) by lia.
  assert (SUB1 : sub_live A0 A1).
  { intros q0 kq Lq. rewrite (LEQ0 q0 (ne_live A0 q0 _ kq Lq Fpixd) (ne_live A0 q0 _ kq Lq Fdatad)). exact Lq. }
  pose proof (SUB1 _ _ Lpixs_a0) as Lpixs_a1. pose proof (SUB1 _ _ Ldata_a0) as Ldata_a1.
  pose proof (ne_live A0 _ _ _ Lpixs_a0 Fpixd) as NE_pixs_pixd. pose proof (ne_live A0 _ _ _ Lpixs_a0 Fdatad) as NE_pixs_datad.
  pose proof (ne_live A0 _ _ _ Ldata_a0 Fpixd) as NE_data_pixd. pose proof (ne_live A0 _ _ _ Ldata_a0 Fdatad) as NE_data_datad.
  assert (NE_pixd_datad : Z_to_bv 64 pixd <> Z_to_bv 64 datad) by (intros EE; apply NEpd; apply (f_equal bv_unsigned) in EE; rewrite !u_Z2bv in EE by lia; exact EE).
  assert (LDEL1 : forall q0 : word, ~ In q0 [Z_to_bv 64 pixd; Z_to_bv 64 datad] -> live A1 q0 = live A0 q0).
  { intros q0 Hq. apply (LEQ0 q0 (fun EE => Hq (or_introl (eq_sym EE))) (fun EE => Hq (or_intror (or_introl (eq_sym EE))))). }
  assert (PM1 : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|]. apply (POSTM_mono C A0 (s + OFF0) s); [unfold OFF0; lia | exact PMc0]. }
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, OFF0, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF0 256 M0 m1 E0 (EVar 32) CK (proj1 PMc0) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E0 m1 kk') in HKk0 end.
  pose proof (regs_ok_agree 38%nat E0 (ex_envL vals0 r1 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m1] 38%nat ltac:(vm_cast_no_check (eq_refl 38%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m1]) m1 _) by (exact (know_ok_agree SEGS 38%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  rewrite (fr_denot_agree 38%nat E0 (ex_envL vals0 r1 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r1 ex_r10 (EVar 70) HRn1 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_0)) as HRx1. clear HRn1. rename HRx1 into HRn1.
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q11_0 Q12_0 Q1_0 Q2_0 Q4_0 PM0 HW0 FRs0 PMc0 CS0 OFF0 LEQ0 RM0 A10_0.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  pose proof (exT_kn_pix SEGS C A1 m1 _ (ex_envL vals0 r1 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m1]) (EVar 70) (EVar 32) (EVar 71) (EVar 72) pixd s 256 _ CK HW1 Lpixd_a1 PXd1 eq_refl eq_refl RS GLO1 eq_refl eq_refl) as HKp1.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m1 _ (s - 256) (Z.to_nat 256) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 415784 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m1]).
  pose proof (exW_kn_fixed SEGS C A1 m1 _ (ex_envL vals0 r1 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m1]) (EVar 73) (EVar 32) (exW_canary SEGS 415784 m1) s 256 415784 65536 212992 213416 213568 213416 213568
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKp1 (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKp1 HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc1 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A1 M1 (with_vmmaps vm1 md) /\ POSTM C A0 s m1 M1).
  { subst M1. apply (exW_win_blks C A1 A0 m1 _ E1 log1 (EVar 32) s 256 [] CK HW1 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP1 as [HWs1 PMs1].
  pose proof (exW_win_only E1 m1 log1 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs1. change (mem_denot E1 m1 log1) with M1 in FRs1.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log1 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC1 : carry log1 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc1 : know_ok SEGS E1 M1 kn1) by (apply (carry_after SEGS E1 m1 log1 kn0 [] kn1 scs hs HC1 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose (BS1 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 1)]).
  exW_regfactB BS1 HR ex_r10 Q10_1. exW_regfactB BS1 HR ex_r11 Q11_1. exW_regfactB BS1 HR ex_r1 Q1_1. exW_regfactB BS1 HR ex_r2 Q2_1.
  clear BS1.
  lazymatch type of Q2_1 with _ = Z_to_bv 64 (s + ?off) => pose (OFF1 := off) end.
  (* [comment removed for export] *)
  assert (PXsM1 : PIXat M1 pixs (hdv w h 8 cm data)) by exact (exT_pix_livk A0 m0 M1 pixs _ PXs (proj2 (POSTM_trans _ _ _ _ _ _ PM1 PMs1)) Lpixs_a0).
  assert (PXdM1 : PIXat M1 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_sess C A1 m1 M1 _ s 256 pixd _ CK HW1 GLO1 Lpixd_a1 PXd1 FRs1).
  lazymatch type of Q1_1 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixCopyRes0_W fxk C A0 A1 M1 _ Rc1 (s + OFF1) pixd pixs _ _ (Z_to_bv 64 ra) S CK HWs1 SUB1 Q2_1
             ltac:(unfold OFF1; lia) ltac:(unfold OFF1; lia) Q1_1 ltac:(red; apply bv_eq; reflexivity) Q10_1 Q11_1 PXsM1 PXdM1 eq_refl eq_refl eq_refl eq_refl 
             Lpixs_a1 Lpixd_a1 Fpixd F0pixd NE_pixs_pixd) end end.
  intros m2 r2 HW2 CSx1 PMc1 PXd2 A10_1.
  pose proof CSx1 as CS1. clear CSx1.
  assert (PM2 : POSTM C A0 s m0 m2).
  { eapply POSTM_trans; [exact PM1|]. eapply POSTM_trans; [exact PMs1|]. apply (POSTM_mono C A0 (s + OFF1) s); [unfold OFF1; lia | exact PMc1]. }
  assert (KEPT1 : Forall (ex_region_kept E1 M1 m2) [(EVar 32, OFF1, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF1 256 M1 m2 E1 (EVar 32) CK (proj1 PMc1) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E1 M1 m2 _ [] _ HKc1 KEPT1) as HKk1.
  match type of HKk1 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E1 m2 kk') in HKk1 end.
  pose proof (regs_ok_agree 74%nat E1 (ex_envL vals1 r2 [exW_canary SEGS 415784 m2]) _ _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa1.
  pose proof (exW_regs_call _ _ _ _ _ HRa1 (ex_regs_ok_junk vals1 r2 [exW_canary SEGS 415784 m2] 74%nat ltac:(vm_cast_no_check (eq_refl 74%nat))) CS1) as HRn2.
  clear HRa1.
  assert (HKa2 : know_ok SEGS (ex_envL vals1 r2 [exW_canary SEGS 415784 m2]) m2 _) by (exact (know_ok_agree SEGS 74%nat E1 _ m2 _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk1)).
  rewrite (fr_denot_agree 74%nat E1 (ex_envL vals1 r2 [exW_canary SEGS 415784 m2]) _ fr (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc1 HKk1 KEPT1 HC1 HWs1 PMs1 Q10_1 Q11_1 Q1_1 Q2_1 PM1 HW1 FRs1 PMc1 CS1 OFF1 A10_1 PXsM1 PXdM1 PXd1.
  subst M1. clear log1. clear E1. try clear Rc1. clear KN1.
  lazymatch type of HRn2 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn2 end.
  pose proof (exT_kn_cells SEGS m2 (ex_envL vals1 r2 [exW_canary SEGS 415784 m2]) (EVar 70) (EVar 71) (EVar 72) pixd _ PXd2 eq_refl eq_refl eq_refl) as HKg2.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m2 _ (s - 256) (Z.to_nat 256) CK HW2 GLO1 GLO2) as SOK2.
  pose proof (exW_canary_ok SEGS 415784 m2 (canary_any m2)) as CANOK2.
  pose (vals2 := vals1 ++ map (getr r2) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m2]).
  pose proof (exW_kn_fixed SEGS C A1 m2 _ (ex_envL vals1 r2 [exW_canary SEGS 415784 m2]) (EVar 106) (EVar 32) (exW_canary SEGS 415784 m2) s 256 415784 65536 212992 213416 213568 213416 213568
                HW2 eq_refl (proj1 CANOK2) (proj2 CANOK2) eq_refl eq_refl eq_refl SOK2 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf2.
  pose proof (proj2 (Forall_app _ _ _) (conj HKg2 (proj2 (Forall_app _ _ _) (conj HKf2 HKa2)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn2 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN2 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKg2 HKf2 HKa2 SOK2 CANOK2.
  repeat match goal with H : getr r2 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc2 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E2 := EEx) in HR, Hlf, HK, Hms |- *; set (log2 := LLx) in Hms, Hlf; set (M2 := mem_denot E2 m2 log2) in Hms end.
  assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A0 s m2 M2).
  { subst M2. apply (exW_win_blks C A1 A0 m2 _ E2 log2 (EVar 32) s 256 [] CK HW2 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP2 as [HWs2 PMs2].
  pose proof (exW_win_only E2 m2 log2 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs2. change (mem_denot E2 m2 log2) with M2 in FRs2.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log2 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC2 : carry log2 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc2 : know_ok SEGS E2 M2 kn1) by (apply (carry_after SEGS E2 m2 log2 kn0 [] kn1 scs hs HC2 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact Hms |].
  pose (BS2 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 1)]).
  exW_regfactB BS2 HR ex_r10 Q10_2. exW_regfactB BS2 HR ex_r11 Q11_2. exW_regfactB BS2 HR ex_r1 Q1_2. exW_regfactB BS2 HR ex_r2 Q2_2.
  clear BS2.
  lazymatch type of Q2_2 with _ = Z_to_bv 64 (s + ?off) => pose (OFF2 := off) end.
  (* [comment removed for export] *)
  assert (PXsM2 : PIXat M2 pixs (hdv w h 8 cm data)) by exact (exT_pix_livk A0 m0 M2 pixs _ PXs (proj2 (POSTM_trans _ _ _ _ _ _ PM2 PMs2)) Lpixs_a0).
  assert (PXdM2 : PIXat M2 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_sess C A1 m2 M2 _ s 256 pixd _ CK HW2 GLO1 Lpixd_a1 PXd2 FRs2).
  lazymatch type of Q1_2 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixCopyFmt0_W fxk C A0 A1 M2 _ Rc2 (s + OFF2) pixd pixs _ _ (Z_to_bv 64 ra) S CK HWs2 SUB1 Q2_2
             ltac:(unfold OFF2; lia) ltac:(unfold OFF2; lia) Q1_2 ltac:(red; apply bv_eq; reflexivity) Q10_2 Q11_2 PXsM2 PXdM2 eq_refl eq_refl 
             Lpixs_a1 Lpixd_a1 Fpixd F0pixd NE_pixs_pixd) end end.
  intros m3 r3 HW3 CSx2 PMc2 PXd3 A10_2.
  pose proof CSx2 as CS2. clear CSx2.
  assert (PM3 : POSTM C A0 s m0 m3).
  { eapply POSTM_trans; [exact PM2|]. eapply POSTM_trans; [exact PMs2|]. apply (POSTM_mono C A0 (s + OFF2) s); [unfold OFF2; lia | exact PMc2]. }
  assert (KEPT2 : Forall (ex_region_kept E2 M2 m3) [(EVar 32, OFF2, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF2 256 M2 m3 E2 (EVar 32) CK (proj1 PMc2) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E2 M2 m3 _ [] _ HKc2 KEPT2) as HKk2.
  match type of HKk2 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E2 m3 kk') in HKk2 end.
  pose proof (regs_ok_agree 107%nat E2 (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) _ _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa2.
  pose proof (exW_regs_call _ _ _ _ _ HRa2 (ex_regs_ok_junk vals2 r3 [exW_canary SEGS 415784 m3] 107%nat ltac:(vm_cast_no_check (eq_refl 107%nat))) CS2) as HRn3.
  clear HRa2.
  assert (HKa3 : know_ok SEGS (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) m3 _) by (exact (know_ok_agree SEGS 107%nat E2 _ m3 _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk2)).
  rewrite (fr_denot_agree 107%nat E2 (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) _ fr (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc2 HKk2 KEPT2 HC2 HWs2 PMs2 Q10_2 Q11_2 Q1_2 Q2_2 PM2 HW2 FRs2 PMc2 CS2 OFF2 A10_2 PXsM2 PXdM2 PXd2.
  subst M2. clear log2. clear E2. try clear Rc2. clear KN2.
  lazymatch type of HRn3 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn3 end.
  pose proof (exT_kn_cells SEGS m3 (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) (EVar 70) (EVar 71) (EVar 72) pixd _ PXd3 eq_refl eq_refl eq_refl) as HKg3.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m3 _ (s - 256) (Z.to_nat 256) CK HW3 GLO1 GLO2) as SOK3.
  pose proof (exW_canary_ok SEGS 415784 m3 (canary_any m3)) as CANOK3.
  pose (vals3 := vals2 ++ map (getr r3) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m3]).
  pose proof (exW_kn_fixed SEGS C A1 m3 _ (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) (EVar 139) (EVar 32) (exW_canary SEGS 415784 m3) s 256 415784 65536 212992 213416 213568 213416 213568
                HW3 eq_refl (proj1 CANOK3) (proj2 CANOK3) eq_refl eq_refl eq_refl SOK3 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf3.
  pose proof (proj2 (Forall_app _ _ _) (conj HKg3 (proj2 (Forall_app _ _ _) (conj HKf3 HKa3)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn3 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN3 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKg3 HKf3 HKa3 SOK3 CANOK3.
  repeat match goal with H : getr r3 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc3 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E3 := EEx) in HR, Hlf, HK, Hms |- *; set (log3 := LLx) in Hms, Hlf; set (M3 := mem_denot E3 m3 log3) in Hms end.
  assert (WP3 : W C A1 M3 (with_vmmaps vm1 md) /\ POSTM C A0 s m3 M3).
  { subst M3. apply (exW_win_blks C A1 A0 m3 _ E3 log3 (EVar 32) s 256 [] CK HW3 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP3 as [HWs3 PMs3].
  pose proof (exW_win_only E3 m3 log3 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs3. change (mem_denot E3 m3 log3) with M3 in FRs3.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log3 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC3 : carry log3 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc3 : know_ok SEGS E3 M3 kn1) by (apply (carry_after SEGS E3 m3 log3 kn0 [] kn1 scs hs HC3 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact Hms |].
  pose (BS3 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 1)]).
  exW_regfactB BS3 HR ex_r10 Q10_3. exW_regfactB BS3 HR ex_r11 Q11_3. exW_regfactB BS3 HR ex_r1 Q1_3. exW_regfactB BS3 HR ex_r2 Q2_3. exW_regfactB BS3 HR ex_r4 Q4_3.
  clear BS3.
  lazymatch type of Q2_3 with _ = Z_to_bv 64 (s + ?off) => pose (OFF3 := off) end.
  (* [comment removed for export] *)
  assert (PXsM3 : PIXat M3 pixs (hdv w h 8 cm data)) by exact (exT_pix_livk A0 m0 M3 pixs _ PXs (proj2 (POSTM_trans _ _ _ _ _ _ PM3 PMs3)) Lpixs_a0).
  assert (PXdM3 : PIXat M3 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_sess C A1 m3 M3 _ s 256 pixd _ CK HW3 GLO1 Lpixd_a1 PXd3 FRs3).
  assert (CMF3 : cm_facts A1 M3 cm cv) by exact (cmf_keep _ A0 A1 m0 M3 cm cv CMF SUB1 (proj2 (POSTM_trans _ _ _ _ _ _ PM3 PMs3))).
  assert (PMB : POSTM C A0 s m0 M3) by exact (POSTM_trans _ _ _ _ _ _ PM3 PMs3).
  lazymatch type of Q1_3 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (HRMC fxk C A1 M3 _ Rc3 (s + OFF3)%Z pixs w h cm data cv (Z_to_bv 64 ra) S FZ CK HWs3 Q2_3
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF3, RMC_STACK, LSF; lia) ltac:(unfold OFF3; lia) Q1_3 ltac:(red; apply bv_eq; reflexivity) Q4_3 Q10_3 Q11_3
             PXsM3 HOK Hw1 Hh1 Lpixs_a1 F0pixs Ldata_a1 CMF3 (kR - RK_pix)%Z (bR - RB_pix14)%Z
             ltac:(rewrite with_vmmaps_vmmaps; exact RM1) ltac:(clear - HkR'; lia) ltac:(clear - HbR'; lia)) end end.
  intros fx2 A2 m4 vm2 r4 FZ2 HW4 CSx3 OUT RM2.
  destruct fx2 as [fr2 cs2]. cbn [fp_csr] in FZ2. clear FZ. rename FZ2 into FZ.
  pose proof CSx3 as CS3. clear CSx3.
  rewrite with_vmmaps_twice in HW4 |- *.
  destruct OUT as [(Ecm & A10_3 & LEQ3 & PMc3) | (NEcm & PMc3 & pixt & datat & A10_3 & PTN)].
  - (* [comment removed for export] *)
    subst cm.
    assert (PMR : POSTM C A1 s (wbytes M3 (Z_to_bv 64 (pixs + 20)) (Z_to_le_bytes 4 2)) m4) by (apply (POSTM_mono C A1 (s + OFF3) s); [unfold OFF3; lia | exact PMc3]).
    assert (CLONEK : forall (Ax : AS) (mx my : word -> option byte) (mdx : Model) (pp : Z), W C Ax mx mdx -> sub_live A0 Ax -> (0 <= pp)%Z -> (c_top C - LSTK <= pp)%Z -> (pp + 8 <= s)%Z ->
               POSTM C A0 s m4 mx -> POSTM C Ax (pp + 8) (wbytes (wbytes mx (Z_to_bv 64 (pixs + 20)) (Z_to_le_bytes 4 1)) (Z_to_bv 64 pp) (Z_to_le_bytes 8 0)) my -> POSTM C A0 s m0 my).
    { intros Ax mx my mdx pp HWx SUBx P0 P1 P2 PM23 PM34. eapply POSTM_trans; [exact PMB|].
      exact (exT_postm_clone C A0 A1 Ax M3 m4 mx my _ mdx s pp pixs (hdv w h 8 0 data) CK HWs3 HWx SUB1 SUBx PXsM3 eq_refl Lpixs_a0 P0 P1 P2 Hhi PMR PM23 PM34). }
    assert (PXt4 : PIXat m4 pixs (set_rc (hdv w h 8 0 data) 2)).
    { apply (exT_pix_livk A1 (wbytes M3 (Z_to_bv 64 (pixs + 20)) (Z_to_le_bytes 4 2)) m4 pixs _); [|exact (proj2 PMc3) | exact Lpixs_a1]. exact (PIX_wr_rc M3 pixs _ 2 PXsM3 ltac:(lia)). }
    assert (NE_pixd_pixs : Z_to_bv 64 pixd <> Z_to_bv 64 pixs) by (intros EE; exact (NE_pixs_pixd (eq_sym EE))).
    assert (PXd4 : PIXat m4 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_patch C A1 A1 M3 m4 _ pixd pixs 64 (pixs + 20) (Z_to_le_bytes 4 2) _ CK HWs3 Lpixd_a1 Lpixs_a1 NE_pixd_pixs RRpixs ltac:(lia) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) PXdM3 (proj2 PMc3) Lpixd_a1).
    pose proof (eq_trans (LEQ3 _) Lpixs_a1) as Lpixs_a2. pose proof (eq_trans (LEQ3 _) Ldata_a1) as Ldata_a2.
    pose proof (eq_trans (LEQ3 _) Lpixd_a1) as Lpixd_a2. pose proof (eq_trans (LEQ3 _) Ldatad_a1) as Ldatad_a2.
    assert (SUB2 : sub_live A0 A2) by (intros q0 kq Lq; rewrite LEQ3; exact (SUB1 _ _ Lq)).
    assert (LDEL2 : forall q0 : word, ~ In q0 [Z_to_bv 64 pixd; Z_to_bv 64 datad] -> live A2 q0 = live A0 q0) by (intros q0 Hq; rewrite LEQ3; exact (LDEL1 q0 Hq)).
    assert (NE_datad_data : Z_to_bv 64 datad <> Z_to_bv 64 data) by (intros EE; exact (NE_data_datad (eq_sym EE))).
    assert (RRdata : (0 <= data < 2 ^ 64)%Z) by (destruct PXs as (_ & _ & WFs & _); exact (wf_data _ WFs)).
    pose proof (POSTM_refl C A0 s m4) as PM4.
  assert (KEPT3 : Forall (ex_region_kept E3 M3 m4) [(EVar 32, OFF3, 0%Z)]).
  { constructor; [exact (exT_kept_patch1 C A1 _ s OFF3 256 M3 m4 E3 (EVar 32) pixs 64 (pixs + 20) (Z_to_le_bytes 4 2) CK HWs3 Lpixs_a1 RRpixs ltac:(lia) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) (proj1 PMc3) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E3 M3 m4 _ [] _ HKc3 KEPT3) as HKk3.
  match type of HKk3 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E3 m4 kk') in HKk3 end.
  pose proof (regs_ok_agree 140%nat E3 (ex_envL vals3 r4 [data; wpl_of w 8; exW_canary SEGS 415784 m4]) _ _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa3.
  pose proof (exW_regs_call _ _ _ _ _ HRa3 (ex_regs_ok_junk vals3 r4 [data; wpl_of w 8; exW_canary SEGS 415784 m4] 140%nat ltac:(vm_cast_no_check (eq_refl 140%nat))) CS3) as HRn4.
  clear HRa3.
  assert (HKa4 : know_ok SEGS (ex_envL vals3 r4 [data; wpl_of w 8; exW_canary SEGS 415784 m4]) m4 _) by (exact (know_ok_agree SEGS 140%nat E3 _ m4 _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk3)).
  pose proof (ex_regs_ok_reexpr _ _ r4 ex_r10 (EVar 34) HRn4 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_3)) as HRx4. clear HRn4. rename HRx4 into HRn4.
  clear HR HK Hlf Hms HKc3 HKk3 KEPT3 HC3 HWs3 PMs3 Q10_3 Q11_3 Q1_3 Q2_3 Q4_3 PM3 HW3 FRs3 PMc3 CS3 OFF3 A10_3 RM1 PMR PXsM3 PXdM3 CMF3 PMB LEQ3 LDEL1 PXd3.
  subst M3. clear log3. clear E3. try clear Rc3. clear KN3.
  lazymatch type of HRn4 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn4 end.
  pose proof (exT_kn_pix SEGS C A2 m4 _ (ex_envL vals3 r4 [data; wpl_of w 8; exW_canary SEGS 415784 m4]) (EVar 34) (EVar 32) (EVar 172) (EVar 173) pixs s 256 _ CK HW4 Lpixs_a2 PXt4 eq_refl eq_refl RS GLO1 eq_refl eq_refl) as HKp4.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A2 m4 _ (s - 256) (Z.to_nat 256) CK HW4 GLO1 GLO2) as SOK4.
  pose proof (exW_canary_ok SEGS 415784 m4 (canary_any m4)) as CANOK4.
  pose (vals4 := vals3 ++ map (getr r4) ex_regs_list ++ map (Z_to_bv 64) [data; wpl_of w 8; exW_canary SEGS 415784 m4]).
  pose proof (exW_kn_fixed SEGS C A2 m4 _ (ex_envL vals3 r4 [data; wpl_of w 8; exW_canary SEGS 415784 m4]) (EVar 174) (EVar 32) (exW_canary SEGS 415784 m4) s 256 415784 65536 212992 213416 213568 213416 213568
                HW4 eq_refl (proj1 CANOK4) (proj2 CANOK4) eq_refl eq_refl eq_refl SOK4 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf4.
  pose proof (proj2 (Forall_app _ _ _) (conj HKp4 (proj2 (Forall_app _ _ _) (conj HKf4 HKa4)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn4 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN4 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKp4 HKf4 HKa4 SOK4 CANOK4.
  repeat match goal with H : getr r4 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc4 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E4 := EEx) in HR, Hlf, HK, Hms |- *; set (log4 := LLx) in Hms, Hlf; set (M4 := mem_denot E4 m4 log4) in Hms end.
  assert (WP4 : W C A2 M4 (with_vmmaps vm2 md) /\ POSTM C A0 s m4 M4).
  { subst M4. apply (exW_win_blks C A2 A0 m4 _ E4 log4 (EVar 32) s 256 [] CK HW4 SUB2 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP4 as [HWs4 PMs4].
  pose proof (exW_win_only E4 m4 log4 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs4. change (mem_denot E4 m4 log4) with M4 in FRs4.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log4 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC4 : carry log4 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc4 : know_ok SEGS E4 M4 kn1) by (apply (carry_after SEGS E4 m4 log4 kn0 [] kn1 scs hs HC4 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact Hms |].
  pose (BS4 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 1); (172%nat, data); (173%nat, wpl_of w 8)]).
  exW_regfactB BS4 HR ex_r10 Q10_4. exW_regfactB BS4 HR ex_r11 Q11_4. exW_regfactB BS4 HR ex_r1 Q1_4. exW_regfactB BS4 HR ex_r2 Q2_4. exW_regfactB BS4 HR ex_r4 Q4_4.
  clear BS4.
  lazymatch type of Q2_4 with _ = Z_to_bv 64 (s + ?off) => pose (OFF4 := off) end.
  (* [comment removed for export] *)
  assert (PXdM4 : PIXat M4 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_sess C A2 m4 M4 _ s 256 pixd _ CK HW4 GLO1 Lpixd_a2 PXd4 FRs4).
  assert (PXtM4 : PIXat M4 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_sess C A2 m4 M4 _ s 256 pixs _ CK HW4 GLO1 Lpixs_a2 PXt4 FRs4).
  lazymatch type of Q1_4 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_4 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A2 M4 _ Rc4 (wpl_of w 8) 4 (kR - RK_pix - RK_rmc) (bR - RB_pix14 - RB_rmc) (Z_to_bv 64 ret) sp' S CK HWs4 Q10_4 Q11_4 ltac:(clear - Gwpls; lia) ltac:(lia) ltac:(clear - Gwpls; lia)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM2) ltac:(clear - HkR'; unfold RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB RBpos; lia) ltac:(unfold ROOM_NMAX; clear - Gwpls; lia) Q1_4
             ltac:(red; apply bv_eq; reflexivity) Q4_4 Q2_4 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF4, CALLOC_STACK, ALLOC_STACK; lia) ltac:(unfold OFF4; lia)) end end end.
  intros A3 m5 vm3 r5 res4 HW5 Hres4 CSx4 Hnz4 Fbufs1x Lo4 F0bufs1 LEQ4 ZERO4 ALbufs1 TOP4 PMc4 RM3.
  pose proof CSx4 as CS4. clear CSx4.
  rewrite with_vmmaps_twice in HW5 |- *.
  assert (Eres4 : res4 = Z_to_bv 64 (u res4)) by (symmetry; apply zbv_self).
  pose proof (u64_range res4) as RRbufs1. set (bufs1 := u res4) in *. clearbody bufs1. rewrite Eres4 in Hres4, Fbufs1x, Lo4, F0bufs1, LEQ4. clear Eres4 ZERO4 TOP4 Hnz4.
  rewrite (Z.mul_comm (wpl_of w 8) 4) in Lo4.
  assert (Gbufs1 : (4096 <= bufs1)%Z /\ (bufs1 + 4 * wpl_of w 8 <= alloc_top (c_vm C))%Z).
  { destruct (blk_range C A3 m5 _ (Z_to_bv 64 bufs1) (4 * wpl_of w 8) CK HW5 Lo4 Rnb) as [G1 G2]. rewrite u_Z2bv in G1, G2 by (clear - RRbufs1; lia). split; assumption. }
  pose proof (fresh_sub A0 A2 _ SUB2 Fbufs1x) as Fbufs1.
  pose proof Lo4 as Lbufs1_a3.
  assert (SUB3 : sub_live A0 A3).
  { intros q0 kq Lq. rewrite (LEQ4 q0 (ne_live A0 q0 _ kq Lq Fbufs1)). exact (SUB2 q0 kq Lq). }
  pose proof (fun (q0 : word) (Hq : ~ In q0 (Z_to_bv 64 bufs1 :: [Z_to_bv 64 pixd; Z_to_bv 64 datad])) => eq_trans (LEQ4 q0 (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL2 q0 (fun XX => Hq (or_intror XX)))) as LDEL3.
  pose proof (ne_live A2 _ _ _ Lpixs_a2 Fbufs1x) as NE_pixs_bufs1.
  pose proof (eq_trans (LEQ4 _ NE_pixs_bufs1) Lpixs_a2) as Lpixs_a3.
  pose proof (ne_live A2 _ _ _ Ldata_a2 Fbufs1x) as NE_data_bufs1.
  pose proof (eq_trans (LEQ4 _ NE_data_bufs1) Ldata_a2) as Ldata_a3.
  pose proof (ne_live A2 _ _ _ Lpixd_a2 Fbufs1x) as NE_pixd_bufs1.
  pose proof (eq_trans (LEQ4 _ NE_pixd_bufs1) Lpixd_a2) as Lpixd_a3.
  pose proof (ne_live A2 _ _ _ Ldatad_a2 Fbufs1x) as NE_datad_bufs1.
  pose proof (eq_trans (LEQ4 _ NE_datad_bufs1) Ldatad_a2) as Ldatad_a3.
  assert (PXd5 : PIXat m5 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_livk A2 M4 m5 pixd _ PXdM4 (proj2 PMc4) Lpixd_a2).
  assert (PXt5 : PIXat m5 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_livk A2 M4 m5 pixs _ PXtM4 (proj2 PMc4) Lpixs_a2).
  assert (PM5 : POSTM C A0 s m4 m5).
  { eapply POSTM_trans; [exact PM4|]. eapply POSTM_trans; [exact PMs4|]. apply (POSTM_sub C A0 A2 _ _ _ SUB2). apply (POSTM_mono C A2 (s + OFF4) s); [unfold OFF4; lia | exact PMc4]. }
  assert (KEPT4 : Forall (ex_region_kept E4 M4 m5) [(EVar 32, OFF4, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF4 256 M4 m5 E4 (EVar 32) CK (proj1 PMc4) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E4 M4 m5 _ [] _ HKc4 KEPT4) as HKk4.
  match type of HKk4 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E4 m5 kk') in HKk4 end.
  pose proof (regs_ok_agree 175%nat E4 (ex_envL vals4 r5 [bufs1; exW_canary SEGS 415784 m5]) _ _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa4.
  pose proof (exW_regs_call _ _ _ _ _ HRa4 (ex_regs_ok_junk vals4 r5 [bufs1; exW_canary SEGS 415784 m5] 175%nat ltac:(vm_cast_no_check (eq_refl 175%nat))) CS4) as HRn5.
  clear HRa4.
  assert (HKa5 : know_ok SEGS (ex_envL vals4 r5 [bufs1; exW_canary SEGS 415784 m5]) m5 _) by (exact (know_ok_agree SEGS 175%nat E4 _ m5 _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk4)).
  rewrite (fr_denot_agree 175%nat E4 (ex_envL vals4 r5 [bufs1; exW_canary SEGS 415784 m5]) _ fr2 (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r5 ex_r10 (EVar 207) HRn5 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres4)) as HRx5. clear HRn5. rename HRx5 into HRn5.
  clear HR HK Hlf Hms HKc4 HKk4 KEPT4 HC4 HWs4 PMs4 Q10_4 Q11_4 Q1_4 Q2_4 Q4_4 PM4 HW4 FRs4 PMc4 CS4 SUB2 RM2 LEQ4 Fbufs1x Lo4 OFF4 LDEL2 Hres4 Lpixs_a2 Ldata_a2 Lpixd_a2 Ldatad_a2 PXdM4 PXd4 PXtM4 PXt4.
  subst M4. clear log4. clear E4. try clear Rc4. clear KN4.
  lazymatch type of HRn5 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn5 end.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [bufs1; exW_canary SEGS 415784 m5]) m5) _ _ (ex_krange SEGS (ex_envL vals4 r5 [bufs1; exW_canary SEGS 415784 m5]) m5 (EVar 207) bufs1 4096 (2 ^ 47) eq_refl RRbufs1 ltac:(clear - Gbufs1 T1 T2 T3 LV Rnb; lia)) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals4 r5 [bufs1; exW_canary SEGS 415784 m5]) m5))) as HKb5.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A3 m5 _ (s - 256) (Z.to_nat 256) CK HW5 GLO1 GLO2) as SOK5.
  pose proof (exW_canary_ok SEGS 415784 m5 (canary_any m5)) as CANOK5.
  pose (vals5 := vals4 ++ map (getr r5) ex_regs_list ++ map (Z_to_bv 64) [bufs1; exW_canary SEGS 415784 m5]).
  pose proof (exW_kn_fixed SEGS C A3 m5 _ (ex_envL vals4 r5 [bufs1; exW_canary SEGS 415784 m5]) (EVar 208) (EVar 32) (exW_canary SEGS 415784 m5) s 256 415784 65536 212992 213416 213568 213416 213568
                HW5 eq_refl (proj1 CANOK5) (proj2 CANOK5) eq_refl eq_refl eq_refl SOK5 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf5.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb5 (proj2 (Forall_app _ _ _) (conj HKf5 HKa5)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn5 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN5 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb5 HKf5 HKa5 SOK5 CANOK5.
  repeat match goal with H : getr r5 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc5 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E5 := EEx) in HR, Hlf, HK, Hms |- *; set (log5 := LLx) in Hms, Hlf; set (M5 := mem_denot E5 m5 log5) in Hms end.
  assert (WP5 : W C A3 M5 (with_vmmaps vm3 md) /\ POSTM C A0 s m5 M5).
  { subst M5. apply (exW_win_blks C A3 A0 m5 _ E5 log5 (EVar 32) s 256 [] CK HW5 SUB3 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP5 as [HWs5 PMs5].
  pose proof (exW_win_only E5 m5 log5 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs5. change (mem_denot E5 m5 log5) with M5 in FRs5.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log5 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC5 : carry log5 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc5 : know_ok SEGS E5 M5 kn1) by (apply (carry_after SEGS E5 m5 log5 kn0 [] kn1 scs hs HC5 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact Hms |].
  pose (BS5 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 1); (172%nat, data); (173%nat, wpl_of w 8); (207%nat, bufs1)]).
  exW_regfactB BS5 HR ex_r10 Q10_5. exW_regfactB BS5 HR ex_r11 Q11_5. exW_regfactB BS5 HR ex_r1 Q1_5. exW_regfactB BS5 HR ex_r2 Q2_5. exW_regfactB BS5 HR ex_r4 Q4_5.
  clear BS5.
  lazymatch type of Q2_5 with _ = Z_to_bv 64 (s + ?off) => pose (OFF5 := off) end.
  (* [comment removed for export] *)
  assert (PXdM5 : PIXat M5 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_sess C A3 m5 M5 _ s 256 pixd _ CK HW5 GLO1 Lpixd_a3 PXd5 FRs5).
  assert (PXtM5 : PIXat M5 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_sess C A3 m5 M5 _ s 256 pixs _ CK HW5 GLO1 Lpixs_a3 PXt5 FRs5).
  lazymatch type of Q1_5 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_5 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A3 M5 _ Rc5 (wpl_of w 8) 4 (kR - RK_pix - RK_rmc - 1) (bR - RB_pix14 - RB_rmc - alloc_margin (wpl_of w 8 * 4)) (Z_to_bv 64 ret) sp' S CK HWs5 Q10_5 Q11_5 ltac:(clear - Gwpls; lia) ltac:(lia) ltac:(clear - Gwpls; lia)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM3) ltac:(clear - HkR'; unfold RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB RBpos; lia) ltac:(unfold ROOM_NMAX; clear - Gwpls; lia) Q1_5
             ltac:(red; apply bv_eq; reflexivity) Q4_5 Q2_5 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF5, CALLOC_STACK, ALLOC_STACK; lia) ltac:(unfold OFF5; lia)) end end end.
  intros A4 m6 vm4 r6 res5 HW6 Hres5 CSx5 Hnz5 Fbufs2x Lo5 F0bufs2 LEQ5 ZERO5 ALbufs2 TOP5 PMc5 RM4.
  pose proof CSx5 as CS5. clear CSx5.
  rewrite with_vmmaps_twice in HW6 |- *.
  assert (Eres5 : res5 = Z_to_bv 64 (u res5)) by (symmetry; apply zbv_self).
  pose proof (u64_range res5) as RRbufs2. set (bufs2 := u res5) in *. clearbody bufs2. rewrite Eres5 in Hres5, Fbufs2x, Lo5, F0bufs2, LEQ5. clear Eres5 ZERO5 TOP5 Hnz5.
  rewrite (Z.mul_comm (wpl_of w 8) 4) in Lo5.
  assert (Gbufs2 : (4096 <= bufs2)%Z /\ (bufs2 + 4 * wpl_of w 8 <= alloc_top (c_vm C))%Z).
  { destruct (blk_range C A4 m6 _ (Z_to_bv 64 bufs2) (4 * wpl_of w 8) CK HW6 Lo5 Rnb) as [G1 G2]. rewrite u_Z2bv in G1, G2 by (clear - RRbufs2; lia). split; assumption. }
  pose proof (fresh_sub A0 A3 _ SUB3 Fbufs2x) as Fbufs2.
  pose proof Lo5 as Lbufs2_a4.
  assert (SUB4 : sub_live A0 A4).
  { intros q0 kq Lq. rewrite (LEQ5 q0 (ne_live A0 q0 _ kq Lq Fbufs2)). exact (SUB3 q0 kq Lq). }
  pose proof (fun (q0 : word) (Hq : ~ In q0 (Z_to_bv 64 bufs2 :: [Z_to_bv 64 bufs1; Z_to_bv 64 pixd; Z_to_bv 64 datad])) => eq_trans (LEQ5 q0 (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL3 q0 (fun XX => Hq (or_intror XX)))) as LDEL4.
  pose proof (ne_live A3 _ _ _ Lpixs_a3 Fbufs2x) as NE_pixs_bufs2.
  pose proof (eq_trans (LEQ5 _ NE_pixs_bufs2) Lpixs_a3) as Lpixs_a4.
  pose proof (ne_live A3 _ _ _ Ldata_a3 Fbufs2x) as NE_data_bufs2.
  pose proof (eq_trans (LEQ5 _ NE_data_bufs2) Ldata_a3) as Ldata_a4.
  pose proof (ne_live A3 _ _ _ Lpixd_a3 Fbufs2x) as NE_pixd_bufs2.
  pose proof (eq_trans (LEQ5 _ NE_pixd_bufs2) Lpixd_a3) as Lpixd_a4.
  pose proof (ne_live A3 _ _ _ Ldatad_a3 Fbufs2x) as NE_datad_bufs2.
  pose proof (eq_trans (LEQ5 _ NE_datad_bufs2) Ldatad_a3) as Ldatad_a4.
  pose proof (ne_live A3 _ _ _ Lbufs1_a3 Fbufs2x) as NE_bufs1_bufs2.
  pose proof (eq_trans (LEQ5 _ NE_bufs1_bufs2) Lbufs1_a3) as Lbufs1_a4.
  assert (PXd6 : PIXat m6 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_livk A3 M5 m6 pixd _ PXdM5 (proj2 PMc5) Lpixd_a3).
  assert (PXt6 : PIXat m6 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_livk A3 M5 m6 pixs _ PXtM5 (proj2 PMc5) Lpixs_a3).
  assert (PM6 : POSTM C A0 s m4 m6).
  { eapply POSTM_trans; [exact PM5|]. eapply POSTM_trans; [exact PMs5|]. apply (POSTM_sub C A0 A3 _ _ _ SUB3). apply (POSTM_mono C A3 (s + OFF5) s); [unfold OFF5; lia | exact PMc5]. }
  assert (KEPT5 : Forall (ex_region_kept E5 M5 m6) [(EVar 32, OFF5, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF5 256 M5 m6 E5 (EVar 32) CK (proj1 PMc5) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E5 M5 m6 _ [] _ HKc5 KEPT5) as HKk5.
  match type of HKk5 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E5 m6 kk') in HKk5 end.
  pose proof (regs_ok_agree 209%nat E5 (ex_envL vals5 r6 [bufs2; exW_canary SEGS 415784 m6]) _ _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa5.
  pose proof (exW_regs_call _ _ _ _ _ HRa5 (ex_regs_ok_junk vals5 r6 [bufs2; exW_canary SEGS 415784 m6] 209%nat ltac:(vm_cast_no_check (eq_refl 209%nat))) CS5) as HRn6.
  clear HRa5.
  assert (HKa6 : know_ok SEGS (ex_envL vals5 r6 [bufs2; exW_canary SEGS 415784 m6]) m6 _) by (exact (know_ok_agree SEGS 209%nat E5 _ m6 _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk5)).
  rewrite (fr_denot_agree 209%nat E5 (ex_envL vals5 r6 [bufs2; exW_canary SEGS 415784 m6]) _ fr2 (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r6 ex_r10 (EVar 241) HRn6 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres5)) as HRx6. clear HRn6. rename HRx6 into HRn6.
  clear HR HK Hlf Hms HKc5 HKk5 KEPT5 HC5 HWs5 PMs5 Q10_5 Q11_5 Q1_5 Q2_5 Q4_5 PM5 HW5 FRs5 PMc5 CS5 SUB3 RM3 LEQ5 Fbufs2x Lo5 OFF5 LDEL3 Hres5 Lpixs_a3 Ldata_a3 Lpixd_a3 Ldatad_a3 Lbufs1_a3 PXdM5 PXd5 PXtM5 PXt5.
  subst M5. clear log5. clear E5. try clear Rc5. clear KN5.
  lazymatch type of HRn6 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn6 end.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [bufs2; exW_canary SEGS 415784 m6]) m6) _ _ (ex_krange SEGS (ex_envL vals5 r6 [bufs2; exW_canary SEGS 415784 m6]) m6 (EVar 241) bufs2 4096 (2 ^ 47) eq_refl RRbufs2 ltac:(clear - Gbufs2 T1 T2 T3 LV Rnb; lia)) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals5 r6 [bufs2; exW_canary SEGS 415784 m6]) m6))) as HKb6.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A4 m6 _ (s - 256) (Z.to_nat 256) CK HW6 GLO1 GLO2) as SOK6.
  pose proof (exW_canary_ok SEGS 415784 m6 (canary_any m6)) as CANOK6.
  pose (vals6 := vals5 ++ map (getr r6) ex_regs_list ++ map (Z_to_bv 64) [bufs2; exW_canary SEGS 415784 m6]).
  pose proof (exW_kn_fixed SEGS C A4 m6 _ (ex_envL vals5 r6 [bufs2; exW_canary SEGS 415784 m6]) (EVar 242) (EVar 32) (exW_canary SEGS 415784 m6) s 256 415784 65536 212992 213416 213568 213416 213568
                HW6 eq_refl (proj1 CANOK6) (proj2 CANOK6) eq_refl eq_refl eq_refl SOK6 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf6.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb6 (proj2 (Forall_app _ _ _) (conj HKf6 HKa6)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn6 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN6 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb6 HKf6 HKa6 SOK6 CANOK6.
  repeat match goal with H : getr r6 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc6 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E6 := EEx) in HR, Hlf, HK, Hms |- *; set (log6 := LLx) in Hms, Hlf; set (M6 := mem_denot E6 m6 log6) in Hms end.
  assert (WP6 : W C A4 M6 (with_vmmaps vm4 md) /\ POSTM C A0 s m6 M6).
  { subst M6. apply (exW_win_blks C A4 A0 m6 _ E6 log6 (EVar 32) s 256 [] CK HW6 SUB4 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP6 as [HWs6 PMs6].
  pose proof (exW_win_only E6 m6 log6 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs6. change (mem_denot E6 m6 log6) with M6 in FRs6.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log6 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC6 : carry log6 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc6 : know_ok SEGS E6 M6 kn1) by (apply (carry_after SEGS E6 m6 log6 kn0 [] kn1 scs hs HC6 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact Hms |].
  pose (BS6 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 1); (172%nat, data); (173%nat, wpl_of w 8); (207%nat, bufs1); (241%nat, bufs2)]).
  exW_regfactB BS6 HR ex_r1 Q1_6. exW_regfactB BS6 HR ex_r2 Q2_6. exW_regfactB BS6 HR ex_r10 Q10_6. exW_regfactB BS6 HR ex_r11 Q11_6. exW_regfactB BS6 HR ex_r12 Q12_6. exW_regfactB BS6 HR ex_r13 Q13_6. exW_regfactB BS6 HR ex_r14 Q14_6. exW_regfactB BS6 HR ex_r15 Q15_6. exW_regfactB BS6 HR ex_r16 Q16_6. exW_regfactB BS6 HR ex_r17 Q17_6. exW_regfactB BS6 HR ex_r28 Q28_6. exW_regfactB BS6 HR ex_r29 Q29_6.
  clear BS6.
  lazymatch type of Q2_6 with _ = Z_to_bv 64 (s + ?off) => pose (OFF6 := off) end.
  (* [comment removed for export] *)
  assert (PXdM6 : PIXat M6 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_sess C A4 m6 M6 _ s 256 pixd _ CK HW6 GLO1 Lpixd_a4 PXd6 FRs6).
  assert (PXtM6 : PIXat M6 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_sess C A4 m6 M6 _ s 256 pixs _ CK HW6 GLO1 Lpixs_a4 PXt6 FRs6).
  lazymatch type of Q1_6 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (dbl_call_W fxk C A4 A0 M6 _ Rc6 (s + OFF6) w h datad data bufs1 bufs2 10 10 (Z_to_bv 64 ra) S CK HWs6 SUB4
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF6; clear - Hlo1; lia) ltac:(unfold OFF6; clear - Hhi; lia) HOK Hw1 Hh1 ltac:(lia) ltac:(lia)
             Ldatad_a4 Fdatad F0datad Ldata_a4 Lbufs1_a4 Fbufs1 F0bufs1 Lbufs2_a4 Fbufs2 F0bufs2 RRdatad RRdata RRbufs1 RRbufs2
             NE_datad_data NE_datad_bufs1 NE_datad_bufs2 NE_data_bufs1 NE_data_bufs2 NE_bufs1_bufs2 Q1_6 ltac:(red; apply bv_eq; reflexivity) Q2_6
             Q10_6 Q11_6 Q12_6 Q13_6 Q14_6 Q15_6 Q16_6 Q17_6 Q28_6 Q29_6) end end.
  intros r7 m7 HW7 PMc6 CSx6 KEEPB6.
  pose proof CSx6 as CS6. clear CSx6.
  assert (PXd7 : PIXat m7 pixd (set_data (pix_hdr w h 1) datad)) by exact (pix_keepb A4 M6 m7 pixd _ _ _ _ PXdM6 Lpixd_a4 NE_pixd_datad NE_pixd_bufs1 NE_pixd_bufs2 KEEPB6).
  assert (PXt7 : PIXat m7 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (pix_keepb A4 M6 m7 pixs _ _ _ _ PXtM6 Lpixs_a4 NE_pixs_datad NE_pixs_bufs1 NE_pixs_bufs2 KEEPB6).
  assert (PM7 : POSTM C A0 s m4 m7).
  { eapply POSTM_trans; [exact PM6|]. eapply POSTM_trans; [exact PMs6|]. apply (POSTM_mono C A0 (s + OFF6) s); [unfold OFF6; lia | exact PMc6]. }
  assert (KEPT6 : Forall (ex_region_kept E6 M6 m7) [(EVar 32, OFF6, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF6 256 M6 m7 E6 (EVar 32) CK (proj1 PMc6) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E6 M6 m7 _ [] _ HKc6 KEPT6) as HKk6.
  match type of HKk6 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E6 m7 kk') in HKk6 end.
  pose proof (regs_ok_agree 243%nat E6 (ex_envL vals6 r7 [exW_canary SEGS 415784 m7]) _ _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa6.
  pose proof (exW_regs_call _ _ _ _ _ HRa6 (ex_regs_ok_junk vals6 r7 [exW_canary SEGS 415784 m7] 243%nat ltac:(vm_cast_no_check (eq_refl 243%nat))) CS6) as HRn7.
  clear HRa6.
  assert (HKa7 : know_ok SEGS (ex_envL vals6 r7 [exW_canary SEGS 415784 m7]) m7 _) by (exact (know_ok_agree SEGS 243%nat E6 _ m7 _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk6)).
  rewrite (fr_denot_agree 243%nat E6 (ex_envL vals6 r7 [exW_canary SEGS 415784 m7]) _ fr2 (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc6 HKk6 KEPT6 HC6 HWs6 PMs6 Q1_6 Q2_6 Q10_6 Q11_6 Q12_6 Q13_6 Q14_6 Q15_6 Q16_6 Q17_6 Q28_6 Q29_6 PM6 HW6 FRs6 PMc6 CS6 OFF6 KEEPB6 PXdM6 PXd6 PXtM6 PXt6.
  subst M6. clear log6. clear E6. try clear Rc6. clear KN6.
  lazymatch type of HRn7 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn7 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A4 m7 _ (s - 256) (Z.to_nat 256) CK HW7 GLO1 GLO2) as SOK7.
  pose proof (exW_canary_ok SEGS 415784 m7 (canary_any m7)) as CANOK7.
  pose (vals7 := vals6 ++ map (getr r7) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m7]).
  pose proof (exW_kn_fixed SEGS C A4 m7 _ (ex_envL vals6 r7 [exW_canary SEGS 415784 m7]) (EVar 275) (EVar 32) (exW_canary SEGS 415784 m7) s 256 415784 65536 212992 213416 213568 213416 213568
                HW7 eq_refl (proj1 CANOK7) (proj2 CANOK7) eq_refl eq_refl eq_refl SOK7 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf7.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf7 HKa7)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn7 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN7 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf7 HKa7 SOK7 CANOK7.
  repeat match goal with H : getr r7 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc7 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E7 := EEx) in HR, Hlf, HK, Hms |- *; set (log7 := LLx) in Hms, Hlf; set (M7 := mem_denot E7 m7 log7) in Hms end.
  assert (WP7 : W C A4 M7 (with_vmmaps vm4 md) /\ POSTM C A0 s m7 M7).
  { subst M7. apply (exW_win_blks C A4 A0 m7 _ E7 log7 (EVar 32) s 256 [] CK HW7 SUB4 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP7 as [HWs7 PMs7].
  pose proof (exW_win_only E7 m7 log7 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs7. change (mem_denot E7 m7 log7) with M7 in FRs7.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log7 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC7 : carry log7 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc7 : know_ok SEGS E7 M7 kn1) by (apply (carry_after SEGS E7 m7 log7 kn0 [] kn1 scs hs HC7 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact Hms |].
  pose (BS7 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 1); (172%nat, data); (173%nat, wpl_of w 8); (207%nat, bufs1); (241%nat, bufs2)]).
  exW_regfactB BS7 HR ex_r10 Q10_7. exW_regfactB BS7 HR ex_r1 Q1_7. exW_regfactB BS7 HR ex_r2 Q2_7. exW_regfactB BS7 HR ex_r4 Q4_7.
  clear BS7.
  lazymatch type of Q2_7 with _ = Z_to_bv 64 (s + ?off) => pose (OFF7 := off) end.
  (* [comment removed for export] *)
  assert (PXdM7 : PIXat M7 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_sess C A4 m7 M7 _ s 256 pixd _ CK HW7 GLO1 Lpixd_a4 PXd7 FRs7).
  assert (PXtM7 : PIXat M7 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_sess C A4 m7 M7 _ s 256 pixs _ CK HW7 GLO1 Lpixs_a4 PXt7 FRs7).
  lazymatch type of Q1_7 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_7 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A4 M7 _ Rc7 (Z_to_bv 64 bufs1) (Z_to_bv 64 ret) (4 * wpl_of w 8) sp' S CK HWs7 Q10_7 Lbufs1_a4 F0bufs1 Q1_7
             ltac:(red; apply bv_eq; reflexivity) Q4_7 Q2_7 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF7, ALLOC_STACK; clear - Hlo1; lia) ltac:(unfold OFF7; clear - Hhi; lia)) end end end.
  intros A5 m8 vm5 r8 HW8 CSx7 Ldead7 LEQ7 PMc7 RTR7.
  pose proof CSx7 as CS7. clear CSx7.
  rewrite with_vmmaps_twice in HW8 |- *.
  assert (SUB5 : sub_live A0 A5).
  { intros q0 kq Lq. rewrite (LEQ7 q0 (ne_live A0 q0 _ kq Lq Fbufs1)). exact (SUB4 q0 kq Lq). }
  assert (LDEL5 : forall q0 : word, ~ In q0 [Z_to_bv 64 bufs2; Z_to_bv 64 pixd; Z_to_bv 64 datad] -> live A5 q0 = live A0 q0).
  { intros q0 Hq. destruct (decide (Z_to_bv 64 bufs1 = q0)) as [<-|NEq]; [rewrite Ldead7, Fbufs1; reflexivity|]. rewrite (LEQ7 q0 (fun EE => NEq (eq_sym EE))). apply LDEL4. clear - Hq NEq. cbn [In] in *. tauto. }
  pose proof (eq_trans (LEQ7 _ NE_pixs_bufs1) Lpixs_a4) as Lpixs_a5.
  pose proof (eq_trans (LEQ7 _ NE_data_bufs1) Ldata_a4) as Ldata_a5.
  pose proof (eq_trans (LEQ7 _ NE_pixd_bufs1) Lpixd_a4) as Lpixd_a5.
  pose proof (eq_trans (LEQ7 _ NE_datad_bufs1) Ldatad_a4) as Ldatad_a5.
  pose proof (eq_trans (LEQ7 _ (fun EE => NE_bufs1_bufs2 (eq_sym EE))) Lbufs2_a4) as Lbufs2_a5.
  assert (PXd8 : PIXat m8 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_livk A5 M7 m8 pixd _ PXdM7 (proj2 PMc7) Lpixd_a5).
  assert (PXt8 : PIXat m8 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_livk A5 M7 m8 pixs _ PXtM7 (proj2 PMc7) Lpixs_a5).
  assert (PM8 : POSTM C A0 s m4 m8).
  { eapply POSTM_trans; [exact PM7|]. eapply POSTM_trans; [exact PMs7|]. apply (POSTM_sub C A0 A5 _ _ _ SUB5). apply (POSTM_mono C A5 (s + OFF7) s); [unfold OFF7; lia | exact PMc7]. }
  pose proof (RTR7 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM4) ltac:(clear - HkR'; unfold RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB RBpos; lia)) as RM5. rewrite !Z.sub_0_r in RM5.
  assert (KEPT7 : Forall (ex_region_kept E7 M7 m8) [(EVar 32, OFF7, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF7 256 M7 m8 E7 (EVar 32) CK (proj1 PMc7) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E7 M7 m8 _ [] _ HKc7 KEPT7) as HKk7.
  match type of HKk7 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E7 m8 kk') in HKk7 end.
  pose proof (regs_ok_agree 276%nat E7 (ex_envL vals7 r8 [exW_canary SEGS 415784 m8]) _ _ (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa7.
  pose proof (exW_regs_call _ _ _ _ _ HRa7 (ex_regs_ok_junk vals7 r8 [exW_canary SEGS 415784 m8] 276%nat ltac:(vm_cast_no_check (eq_refl 276%nat))) CS7) as HRn8.
  clear HRa7.
  assert (HKa8 : know_ok SEGS (ex_envL vals7 r8 [exW_canary SEGS 415784 m8]) m8 _) by (exact (know_ok_agree SEGS 276%nat E7 _ m8 _ (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk7)).
  rewrite (fr_denot_agree 276%nat E7 (ex_envL vals7 r8 [exW_canary SEGS 415784 m8]) _ fr2 (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc7 HKk7 KEPT7 HC7 HWs7 PMs7 Q10_7 Q1_7 Q2_7 Q4_7 PM7 HW7 FRs7 PMc7 CS7 SUB4 RM4 Ldead7 LEQ7 RTR7 Lbufs1_a4 OFF7 LDEL4 Lpixs_a4 Ldata_a4 Lpixd_a4 Ldatad_a4 Lbufs2_a4 PXdM7 PXd7 PXtM7 PXt7.
  subst M7. clear log7. clear E7. try clear Rc7. clear KN7.
  lazymatch type of HRn8 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn8 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A5 m8 _ (s - 256) (Z.to_nat 256) CK HW8 GLO1 GLO2) as SOK8.
  pose proof (exW_canary_ok SEGS 415784 m8 (canary_any m8)) as CANOK8.
  pose (vals8 := vals7 ++ map (getr r8) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m8]).
  pose proof (exW_kn_fixed SEGS C A5 m8 _ (ex_envL vals7 r8 [exW_canary SEGS 415784 m8]) (EVar 308) (EVar 32) (exW_canary SEGS 415784 m8) s 256 415784 65536 212992 213416 213568 213416 213568
                HW8 eq_refl (proj1 CANOK8) (proj2 CANOK8) eq_refl eq_refl eq_refl SOK8 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf8.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf8 HKa8)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn8 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN8 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf8 HKa8 SOK8 CANOK8.
  repeat match goal with H : getr r8 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc8 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E8 := EEx) in HR, Hlf, HK, Hms |- *; set (log8 := LLx) in Hms, Hlf; set (M8 := mem_denot E8 m8 log8) in Hms end.
  assert (WP8 : W C A5 M8 (with_vmmaps vm5 md) /\ POSTM C A0 s m8 M8).
  { subst M8. apply (exW_win_blks C A5 A0 m8 _ E8 log8 (EVar 32) s 256 [] CK HW8 SUB5 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP8 as [HWs8 PMs8].
  pose proof (exW_win_only E8 m8 log8 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs8. change (mem_denot E8 m8 log8) with M8 in FRs8.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log8 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC8 : carry log8 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc8 : know_ok SEGS E8 M8 kn1) by (apply (carry_after SEGS E8 m8 log8 kn0 [] kn1 scs hs HC8 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW8)) | exact (mp_lazy _ (w_pure _ _ _ _ HW8)) | exact Hms |].
  pose (BS8 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 1); (172%nat, data); (173%nat, wpl_of w 8); (207%nat, bufs1); (241%nat, bufs2)]).
  exW_regfactB BS8 HR ex_r10 Q10_8. exW_regfactB BS8 HR ex_r1 Q1_8. exW_regfactB BS8 HR ex_r2 Q2_8. exW_regfactB BS8 HR ex_r4 Q4_8.
  clear BS8.
  lazymatch type of Q2_8 with _ = Z_to_bv 64 (s + ?off) => pose (OFF8 := off) end.
  (* [comment removed for export] *)
  assert (PXdM8 : PIXat M8 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_sess C A5 m8 M8 _ s 256 pixd _ CK HW8 GLO1 Lpixd_a5 PXd8 FRs8).
  assert (PXtM8 : PIXat M8 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_sess C A5 m8 M8 _ s 256 pixs _ CK HW8 GLO1 Lpixs_a5 PXt8 FRs8).
  lazymatch type of Q1_8 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_8 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A5 M8 _ Rc8 (Z_to_bv 64 bufs2) (Z_to_bv 64 ret) (4 * wpl_of w 8) sp' S CK HWs8 Q10_8 Lbufs2_a5 F0bufs2 Q1_8
             ltac:(red; apply bv_eq; reflexivity) Q4_8 Q2_8 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF8, ALLOC_STACK; clear - Hlo1; lia) ltac:(unfold OFF8; clear - Hhi; lia)) end end end.
  intros A6 m9 vm6 r9 HW9 CSx8 Ldead8 LEQ8 PMc8 RTR8.
  pose proof CSx8 as CS8. clear CSx8.
  rewrite with_vmmaps_twice in HW9 |- *.
  assert (SUB6 : sub_live A0 A6).
  { intros q0 kq Lq. rewrite (LEQ8 q0 (ne_live A0 q0 _ kq Lq Fbufs2)). exact (SUB5 q0 kq Lq). }
  assert (LDEL6 : forall q0 : word, ~ In q0 [Z_to_bv 64 pixd; Z_to_bv 64 datad] -> live A6 q0 = live A0 q0).
  { intros q0 Hq. destruct (decide (Z_to_bv 64 bufs2 = q0)) as [<-|NEq]; [rewrite Ldead8, Fbufs2; reflexivity|]. rewrite (LEQ8 q0 (fun EE => NEq (eq_sym EE))). apply LDEL5. clear - Hq NEq. cbn [In] in *. tauto. }
  pose proof (eq_trans (LEQ8 _ NE_pixs_bufs2) Lpixs_a5) as Lpixs_a6.
  pose proof (eq_trans (LEQ8 _ NE_data_bufs2) Ldata_a5) as Ldata_a6.
  pose proof (eq_trans (LEQ8 _ NE_pixd_bufs2) Lpixd_a5) as Lpixd_a6.
  pose proof (eq_trans (LEQ8 _ NE_datad_bufs2) Ldatad_a5) as Ldatad_a6.
  assert (PXd9 : PIXat m9 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_livk A6 M8 m9 pixd _ PXdM8 (proj2 PMc8) Lpixd_a6).
  assert (PXt9 : PIXat m9 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_livk A6 M8 m9 pixs _ PXtM8 (proj2 PMc8) Lpixs_a6).
  assert (PM9 : POSTM C A0 s m4 m9).
  { eapply POSTM_trans; [exact PM8|]. eapply POSTM_trans; [exact PMs8|]. apply (POSTM_sub C A0 A6 _ _ _ SUB6). apply (POSTM_mono C A6 (s + OFF8) s); [unfold OFF8; lia | exact PMc8]. }
  pose proof (RTR8 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM5) ltac:(clear - HkR'; unfold RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB RBpos; lia)) as RM6. rewrite !Z.sub_0_r in RM6.
  assert (KEPT8 : Forall (ex_region_kept E8 M8 m9) [(EVar 32, OFF8, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF8 256 M8 m9 E8 (EVar 32) CK (proj1 PMc8) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E8 M8 m9 _ [] _ HKc8 KEPT8) as HKk8.
  match type of HKk8 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E8 m9 kk') in HKk8 end.
  pose proof (regs_ok_agree 309%nat E8 (ex_envL vals8 r9 [exW_canary SEGS 415784 m9]) _ _ (vals_app_agree vals8 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa8.
  pose proof (exW_regs_call _ _ _ _ _ HRa8 (ex_regs_ok_junk vals8 r9 [exW_canary SEGS 415784 m9] 309%nat ltac:(vm_cast_no_check (eq_refl 309%nat))) CS8) as HRn9.
  clear HRa8.
  assert (HKa9 : know_ok SEGS (ex_envL vals8 r9 [exW_canary SEGS 415784 m9]) m9 _) by (exact (know_ok_agree SEGS 309%nat E8 _ m9 _ (vals_app_agree vals8 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk8)).
  rewrite (fr_denot_agree 309%nat E8 (ex_envL vals8 r9 [exW_canary SEGS 415784 m9]) _ fr2 (vals_app_agree vals8 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc8 HKk8 KEPT8 HC8 HWs8 PMs8 Q10_8 Q1_8 Q2_8 Q4_8 PM8 HW8 FRs8 PMc8 CS8 SUB5 RM5 Ldead8 LEQ8 RTR8 Lbufs2_a5 OFF8 LDEL5 Lpixs_a5 Ldata_a5 Lpixd_a5 Ldatad_a5 PXdM8 PXd8 PXtM8 PXt8.
  subst M8. clear log8. clear E8. try clear Rc8. clear KN8.
  lazymatch type of HRn9 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn9 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A6 m9 _ (s - 256) (Z.to_nat 256) CK HW9 GLO1 GLO2) as SOK9.
  pose proof (exW_canary_ok SEGS 415784 m9 (canary_any m9)) as CANOK9.
  pose (vals9 := vals8 ++ map (getr r9) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m9]).
  pose proof (exW_kn_fixed SEGS C A6 m9 _ (ex_envL vals8 r9 [exW_canary SEGS 415784 m9]) (EVar 341) (EVar 32) (exW_canary SEGS 415784 m9) s 256 415784 65536 212992 213416 213568 213416 213568
                HW9 eq_refl (proj1 CANOK9) (proj2 CANOK9) eq_refl eq_refl eq_refl SOK9 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf9.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf9 HKa9)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn9 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN9 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf9 HKa9 SOK9 CANOK9.
  repeat match goal with H : getr r9 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc9 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E9 := EEx) in HR, Hlf, HK, Hms |- *; set (log9 := LLx) in Hms, Hlf; set (M9 := mem_denot E9 m9 log9) in Hms end.
  assert (WP9 : W C A6 M9 (with_vmmaps vm6 md) /\ POSTM C A0 s m9 M9).
  { subst M9. apply (exW_win_blks C A6 A0 m9 _ E9 log9 (EVar 32) s 256 [] CK HW9 SUB6 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP9 as [HWs9 PMs9].
  pose proof (exW_win_only E9 m9 log9 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs9. change (mem_denot E9 m9 log9) with M9 in FRs9.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log9 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC9 : carry log9 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc9 : know_ok SEGS E9 M9 kn1) by (apply (carry_after SEGS E9 m9 log9 kn0 [] kn1 scs hs HC9 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW9)) | exact (mp_lazy _ (w_pure _ _ _ _ HW9)) | exact Hms |].
  pose (BS9 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 1); (172%nat, data); (173%nat, wpl_of w 8); (207%nat, bufs1); (241%nat, bufs2)]).
  exW_regfactB BS9 HR ex_r10 Q10_9. exW_regfactB BS9 HR ex_r1 Q1_9. exW_regfactB BS9 HR ex_r2 Q2_9. exW_regfactB BS9 HR ex_r4 Q4_9.
  clear BS9.
  lazymatch type of Q2_9 with _ = Z_to_bv 64 (s + ?off) => pose (OFF9 := off) end.
  (* [comment removed for export] *)
  pose (BSx9 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 1); (172%nat, data); (173%nat, wpl_of w 8); (207%nat, bufs1); (241%nat, bufs2)]).
  exW_cellB HK Hlf r0 BSx9 (EVar 32) s (-96)%Z 8%nat CELLpp.
  clear BSx9.
  assert (PXdM9 : PIXat M9 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_sess C A6 m9 M9 _ s 256 pixd _ CK HW9 GLO1 Lpixd_a6 PXd9 FRs9).
  assert (PXtM9 : PIXat M9 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_sess C A6 m9 M9 _ s 256 pixs _ CK HW9 GLO1 Lpixs_a6 PXt9 FRs9).
  assert (PPlo : (s + OFF9 <= s + -96)%Z) by (unfold OFF9; lia). assert (PPhi : (s + -96 + 8 <= c_top C)%Z) by lia.
  lazymatch type of Q1_9 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixDestroy_rc2s_W fxk C A6 M9 _ Rc9 (s + OFF9)%Z (s + -96)%Z pixs (set_rc (hdv w h 8 0 data) 2) (Z_to_bv 64 ra) S CK HWs9 Q2_9
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF9, PXD2_STACK, ALLOC_STACK; clear - Hlo1; lia) PPlo PPhi ltac:(rewrite <- Zplus_mod_idemp_l, Hs8; reflexivity) Q1_9 ltac:(red; apply bv_eq; reflexivity) Q10_9 CELLpp
             PXtM9 eq_refl Lpixs_a6 F0pixs) end end.
  intros m10 r10 HW10 CSx9 PMD FRMs9.
  pose proof CSx9 as CS9. clear CSx9.
  assert (PMB10 : POSTM C A0 s m0 m10).
  { apply (CLONEK A6 M9 m10 _ (s + -96)%Z HWs9 SUB6 ltac:(lia) ltac:(lia) ltac:(lia) (POSTM_trans _ _ _ _ _ _ PM9 PMs9) PMD). }
  assert (PXd10 : PIXat m10 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_patch2 C A6 A6 M9 m10 _ pixd pixs 64 (pixs + 20) (s + -96) (Z_to_le_bytes 4 1) (Z_to_le_bytes 8 0) _ CK HWs9 Lpixd_a6 Lpixs_a6 NE_pixd_pixs RRpixs ltac:(lia) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) PXdM9 (proj2 PMD) Lpixd_a6).
  assert (FRMx9 : FRM C (s + -88) (wbytes (wbytes M9 (Z_to_bv 64 (pixs + 20)) (Z_to_le_bytes 4 1)) (Z_to_bv 64 (s + -96)) (Z_to_le_bytes 8 0)) m10).
  { replace (s + -88)%Z with (s + -96 + 8)%Z by lia. exact (proj1 PMD). }
  pose proof (POSTM_refl C A0 s m10) as PM10.
  assert (KEPT9 : Forall (ex_region_kept E9 M9 m10) [(EVar 32, (-88)%Z, 0%Z); (EVar 32, OFF9, (-96)%Z)]).
  { constructor; [exact (exT_kept_patch2 C A6 _ s (-88) 256 M9 m10 E9 (EVar 32) pixs 64 (pixs + 20) (s + -96) (Z_to_le_bytes 4 1) (Z_to_le_bytes 8 0) CK HWs9 Lpixs_a6 RRpixs ltac:(lia) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) FRMx9 Hlo Hhi eq_refl eq_refl eq_refl ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia))|]. constructor; [exact (exT_kept_in E9 M9 m10 (EVar 32) s OFF9 (-96) (s + OFF9) (s + -96) FRMs9 eq_refl RS (Z.le_refl _) (Z.le_refl _))|]. constructor. }
  pose proof (ex_know_keepD SEGS E9 M9 m10 _ [] _ HKc9 KEPT9) as HKk9.
  match type of HKk9 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E9 m10 kk') in HKk9 end.
  pose proof (regs_ok_agree 342%nat E9 (ex_envL vals9 r10 [exW_canary SEGS 415784 m10]) _ _ (vals_app_agree vals9 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa9.
  pose proof (exW_regs_call _ _ _ _ _ HRa9 (ex_regs_ok_junk vals9 r10 [exW_canary SEGS 415784 m10] 342%nat ltac:(vm_cast_no_check (eq_refl 342%nat))) CS9) as HRn10.
  clear HRa9.
  assert (HKa10 : know_ok SEGS (ex_envL vals9 r10 [exW_canary SEGS 415784 m10]) m10 _) by (exact (know_ok_agree SEGS 342%nat E9 _ m10 _ (vals_app_agree vals9 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk9)).
  rewrite (fr_denot_agree 342%nat E9 (ex_envL vals9 r10 [exW_canary SEGS 415784 m10]) _ fr2 (vals_app_agree vals9 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc9 HKk9 KEPT9 HC9 HWs9 PMs9 Q10_9 Q1_9 Q2_9 Q4_9 PM9 HW9 FRs9 CS9 OFF9 CELLpp PXdM9 PXtM9 PPlo PPhi PXd9 PXt9 PMD FRMx9 CLONEK FRMs9.
  subst M9. clear log9. clear E9. try clear Rc9. clear KN9.
  lazymatch type of HRn10 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn10 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A6 m10 _ (s - 256) (Z.to_nat 256) CK HW10 GLO1 GLO2) as SOK10.
  pose proof (exW_canary_ok SEGS 415784 m10 (canary_any m10)) as CANOK10.
  pose (vals10 := vals9 ++ map (getr r10) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m10]).
  pose proof (exW_kn_fixed SEGS C A6 m10 _ (ex_envL vals9 r10 [exW_canary SEGS 415784 m10]) (EVar 374) (EVar 32) (exW_canary SEGS 415784 m10) s 256 415784 65536 212992 213416 213568 213416 213568
                HW10 eq_refl (proj1 CANOK10) (proj2 CANOK10) eq_refl eq_refl eq_refl SOK10 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf10.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf10 HKa10)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn10 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN10 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf10 HKa10 SOK10 CANOK10.
  repeat match goal with H : getr r10 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E10 := EEx) in HR, Hlf, HK, Hms |- *; set (log10 := LLx) in Hms, Hlf; set (M10 := mem_denot E10 m10 log10) in Hms end.
  assert (WP10 : W C A6 M10 (with_vmmaps vm6 md) /\ POSTM C A0 s m10 M10).
  { subst M10. apply (exW_win_blks C A6 A0 m10 _ E10 log10 (EVar 32) s 256 [] CK HW10 SUB6 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP10 as [HWs10 PMs10].
  pose proof (exW_win_only E10 m10 log10 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs10. change (mem_denot E10 m10 log10) with M10 in FRs10.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW10)) | exact (mp_lazy _ (w_pure _ _ _ _ HW10)) | exact Hms |].
  pose (BSF := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 1); (172%nat, data); (173%nat, wpl_of w 8); (207%nat, bufs1); (241%nat, bufs2)]).
  exW_regfactB BSF HR ex_r10 G10.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ => apply (HC fxk A6 M10 vm6 RcF FZ HWs10) end.
  + lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 RcF [(2%nat, EVar 32); (4%nat, ELit 284096)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor; [symmetry; exact HTP | constructor]] | vm_compute; reflexivity] end.
  + exact (POSTM_trans _ _ _ _ _ _ PMB10 PMs10).
  + right. exists pixd, datad, 0%Z, cv. split; [exact G10|]. split; [|reflexivity].
    refine (conj Gpd1 (conj Gpd2 (conj ALpixd (conj Gdd1 (conj Gdd2 (conj ALdatad (conj NEpd (conj Fpixd (conj Fdatad (conj F0pixd (conj F0datad (conj Lpixd_a6 (conj Ldatad_a6 (conj _ _)))))))))))))).
    * exact (exT_pix_sess C A6 m10 M10 _ s 256 pixd _ CK HW10 GLO1 Lpixd_a6 PXd10 FRs10).
    * left. split; [reflexivity|]. intros q0 N1 N2. apply LDEL6. clear - N1 N2. cbn [In]. intros [EE|[EE|[]]]; [apply N1 | apply N2]; symmetry; exact EE.
  + apply (aroom_mono _ _ _ _ _ _ RM6); [unfold RK_dbin; clear - HkR'; lia | unfold RB_dbin; clear - HbR' MGB; lia].
  - (* [comment removed for export] *)
    destruct PTN as (Gpt1 & Gpt2 & ALpixt & Gdt1 & Gdt2 & ALdatat & NEptdt & Fpixtx & Fdatatx & F0pixt & F0datat & Lpixt_a2 & Ldatat_a2 & PXt4 & CMR).
    destruct CMR as [(_ & LEQ3) | (ad & _ & XX & _)]; [|exfalso; apply XX; reflexivity].
    assert (RRpixt : (0 <= pixt < 2 ^ 64)%Z) by lia. assert (RRdatat : (0 <= datat < 2 ^ 64)%Z) by lia.
    assert (PMB4 : POSTM C A0 s m0 m4).
    { eapply POSTM_trans; [exact PMB|]. apply (POSTM_sub C A0 A1 _ _ _ SUB1). apply (POSTM_mono C A1 (s + OFF3) s); [unfold OFF3; lia | exact PMc3]. }
    assert (PXd4 : PIXat m4 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_livk A1 M3 m4 pixd _ PXdM3 (proj2 PMc3) Lpixd_a1).
    pose proof (eq_trans (LEQ3 _ (ne_live A1 _ _ _ Lpixs_a1 Fpixtx) (ne_live A1 _ _ _ Lpixs_a1 Fdatatx)) Lpixs_a1) as Lpixs_a2.
    pose proof (eq_trans (LEQ3 _ (ne_live A1 _ _ _ Ldata_a1 Fpixtx) (ne_live A1 _ _ _ Ldata_a1 Fdatatx)) Ldata_a1) as Ldata_a2.
    pose proof (eq_trans (LEQ3 _ (ne_live A1 _ _ _ Lpixd_a1 Fpixtx) (ne_live A1 _ _ _ Lpixd_a1 Fdatatx)) Lpixd_a1) as Lpixd_a2.
    pose proof (eq_trans (LEQ3 _ (ne_live A1 _ _ _ Ldatad_a1 Fpixtx) (ne_live A1 _ _ _ Ldatad_a1 Fdatatx)) Ldatad_a1) as Ldatad_a2.
    assert (SUB2 : sub_live A0 A2).
    { intros q0 kq Lq. pose proof (SUB1 _ _ Lq) as L1. rewrite (LEQ3 q0 (ne_live A1 q0 _ kq L1 Fpixtx) (ne_live A1 q0 _ kq L1 Fdatatx)). exact L1. }
    pose proof (fresh_sub A0 A1 _ SUB1 Fpixtx) as Fpixt. pose proof (fresh_sub A0 A1 _ SUB1 Fdatatx) as Fdatat.
    assert (LDEL2 : forall q0 : word, ~ In q0 [Z_to_bv 64 pixt; Z_to_bv 64 datat; Z_to_bv 64 pixd; Z_to_bv 64 datad] -> live A2 q0 = live A0 q0).
    { intros q0 Hq. rewrite (LEQ3 q0 (fun EE => Hq (or_introl (eq_sym EE))) (fun EE => Hq (or_intror (or_introl (eq_sym EE))))). apply LDEL1. intros XX. apply Hq. right; right; exact XX. }
    assert (NE_pixd_pixt : Z_to_bv 64 pixd <> Z_to_bv 64 pixt) by exact (ne_live A1 _ _ _ Lpixd_a1 Fpixtx).
    assert (NE_pixd_datat : Z_to_bv 64 pixd <> Z_to_bv 64 datat) by exact (ne_live A1 _ _ _ Lpixd_a1 Fdatatx).
    assert (NE_datad_pixt : Z_to_bv 64 datad <> Z_to_bv 64 pixt) by exact (ne_live A1 _ _ _ Ldatad_a1 Fpixtx).
    assert (NE_datad_datat : Z_to_bv 64 datad <> Z_to_bv 64 datat) by exact (ne_live A1 _ _ _ Ldatad_a1 Fdatatx).
    assert (NE_pixt_datad : Z_to_bv 64 pixt <> Z_to_bv 64 datad) by (intros EE; exact (NE_datad_pixt (eq_sym EE))).
    assert (NE_pixt_datat : Z_to_bv 64 pixt <> Z_to_bv 64 datat) by (intros EE; apply NEptdt; apply (f_equal bv_unsigned) in EE; rewrite !u_Z2bv in EE by lia; exact EE).
    pose proof (POSTM_refl C A0 s m4) as PM4.
  assert (KEPT3 : Forall (ex_region_kept E3 M3 m4) [(EVar 32, OFF3, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF3 256 M3 m4 E3 (EVar 32) CK (proj1 PMc3) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E3 M3 m4 _ [] _ HKc3 KEPT3) as HKk3.
  match type of HKk3 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E3 m4 kk') in HKk3 end.
  pose proof (regs_ok_agree 140%nat E3 (ex_envL vals3 r4 [pixt; datat; wpl_of w 8; exW_canary SEGS 415784 m4]) _ _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa3.
  pose proof (exW_regs_call _ _ _ _ _ HRa3 (ex_regs_ok_junk vals3 r4 [pixt; datat; wpl_of w 8; exW_canary SEGS 415784 m4] 140%nat ltac:(vm_cast_no_check (eq_refl 140%nat))) CS3) as HRn4.
  clear HRa3.
  assert (HKa4 : know_ok SEGS (ex_envL vals3 r4 [pixt; datat; wpl_of w 8; exW_canary SEGS 415784 m4]) m4 _) by (exact (know_ok_agree SEGS 140%nat E3 _ m4 _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk3)).
  pose proof (ex_regs_ok_reexpr _ _ r4 ex_r10 (EVar 172) HRn4 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_3)) as HRx4. clear HRn4. rename HRx4 into HRn4.
  clear HR HK Hlf Hms HKc3 HKk3 KEPT3 HC3 HWs3 PMs3 Q10_3 Q11_3 Q1_3 Q2_3 Q4_3 PM3 HW3 FRs3 PMc3 CS3 OFF3 A10_3 RM1 PXsM3 PXdM3 CMF3 PMB LEQ3 LDEL1 PXd3.
  subst M3. clear log3. clear E3. try clear Rc3. clear KN3.
  lazymatch type of HRn4 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn4 end.
  pose proof (exT_kn_pix SEGS C A2 m4 _ (ex_envL vals3 r4 [pixt; datat; wpl_of w 8; exW_canary SEGS 415784 m4]) (EVar 172) (EVar 32) (EVar 173) (EVar 174) pixt s 256 _ CK HW4 Lpixt_a2 PXt4 eq_refl eq_refl RS GLO1 eq_refl eq_refl) as HKp4.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A2 m4 _ (s - 256) (Z.to_nat 256) CK HW4 GLO1 GLO2) as SOK4.
  pose proof (exW_canary_ok SEGS 415784 m4 (canary_any m4)) as CANOK4.
  pose (vals4 := vals3 ++ map (getr r4) ex_regs_list ++ map (Z_to_bv 64) [pixt; datat; wpl_of w 8; exW_canary SEGS 415784 m4]).
  pose proof (exW_kn_fixed SEGS C A2 m4 _ (ex_envL vals3 r4 [pixt; datat; wpl_of w 8; exW_canary SEGS 415784 m4]) (EVar 175) (EVar 32) (exW_canary SEGS 415784 m4) s 256 415784 65536 212992 213416 213568 213416 213568
                HW4 eq_refl (proj1 CANOK4) (proj2 CANOK4) eq_refl eq_refl eq_refl SOK4 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf4.
  pose proof (proj2 (Forall_app _ _ _) (conj HKp4 (proj2 (Forall_app _ _ _) (conj HKf4 HKa4)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn4 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN4 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKp4 HKf4 HKa4 SOK4 CANOK4.
  repeat match goal with H : getr r4 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc4 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E4 := EEx) in HR, Hlf, HK, Hms |- *; set (log4 := LLx) in Hms, Hlf; set (M4 := mem_denot E4 m4 log4) in Hms end.
  assert (WP4 : W C A2 M4 (with_vmmaps vm2 md) /\ POSTM C A0 s m4 M4).
  { subst M4. apply (exW_win_blks C A2 A0 m4 _ E4 log4 (EVar 32) s 256 [] CK HW4 SUB2 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP4 as [HWs4 PMs4].
  pose proof (exW_win_only E4 m4 log4 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs4. change (mem_denot E4 m4 log4) with M4 in FRs4.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log4 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC4 : carry log4 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc4 : know_ok SEGS E4 M4 kn1) by (apply (carry_after SEGS E4 m4 log4 kn0 [] kn1 scs hs HC4 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact Hms |].
  pose (BS4 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 1); (172%nat, pixt); (173%nat, datat); (174%nat, wpl_of w 8)]).
  exW_regfactB BS4 HR ex_r10 Q10_4. exW_regfactB BS4 HR ex_r11 Q11_4. exW_regfactB BS4 HR ex_r1 Q1_4. exW_regfactB BS4 HR ex_r2 Q2_4. exW_regfactB BS4 HR ex_r4 Q4_4.
  clear BS4.
  lazymatch type of Q2_4 with _ = Z_to_bv 64 (s + ?off) => pose (OFF4 := off) end.
  (* [comment removed for export] *)
  assert (PXdM4 : PIXat M4 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_sess C A2 m4 M4 _ s 256 pixd _ CK HW4 GLO1 Lpixd_a2 PXd4 FRs4).
  assert (PXtM4 : PIXat M4 pixt (hdv w h 8 0 datat)) by exact (exT_pix_sess C A2 m4 M4 _ s 256 pixt _ CK HW4 GLO1 Lpixt_a2 PXt4 FRs4).
  lazymatch type of Q1_4 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_4 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A2 M4 _ Rc4 (wpl_of w 8) 4 (kR - RK_pix - RK_rmc) (bR - RB_pix14 - RB_rmc) (Z_to_bv 64 ret) sp' S CK HWs4 Q10_4 Q11_4 ltac:(clear - Gwpls; lia) ltac:(lia) ltac:(clear - Gwpls; lia)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM2) ltac:(clear - HkR'; unfold RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB RBpos; lia) ltac:(unfold ROOM_NMAX; clear - Gwpls; lia) Q1_4
             ltac:(red; apply bv_eq; reflexivity) Q4_4 Q2_4 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF4, CALLOC_STACK, ALLOC_STACK; lia) ltac:(unfold OFF4; lia)) end end end.
  intros A3 m5 vm3 r5 res4 HW5 Hres4 CSx4 Hnz4 Fbufs1x Lo4 F0bufs1 LEQ4 ZERO4 ALbufs1 TOP4 PMc4 RM3.
  pose proof CSx4 as CS4. clear CSx4.
  rewrite with_vmmaps_twice in HW5 |- *.
  assert (Eres4 : res4 = Z_to_bv 64 (u res4)) by (symmetry; apply zbv_self).
  pose proof (u64_range res4) as RRbufs1. set (bufs1 := u res4) in *. clearbody bufs1. rewrite Eres4 in Hres4, Fbufs1x, Lo4, F0bufs1, LEQ4. clear Eres4 ZERO4 TOP4 Hnz4.
  rewrite (Z.mul_comm (wpl_of w 8) 4) in Lo4.
  assert (Gbufs1 : (4096 <= bufs1)%Z /\ (bufs1 + 4 * wpl_of w 8 <= alloc_top (c_vm C))%Z).
  { destruct (blk_range C A3 m5 _ (Z_to_bv 64 bufs1) (4 * wpl_of w 8) CK HW5 Lo4 Rnb) as [G1 G2]. rewrite u_Z2bv in G1, G2 by (clear - RRbufs1; lia). split; assumption. }
  pose proof (fresh_sub A0 A2 _ SUB2 Fbufs1x) as Fbufs1.
  pose proof Lo4 as Lbufs1_a3.
  assert (SUB3 : sub_live A0 A3).
  { intros q0 kq Lq. rewrite (LEQ4 q0 (ne_live A0 q0 _ kq Lq Fbufs1)). exact (SUB2 q0 kq Lq). }
  pose proof (fun (q0 : word) (Hq : ~ In q0 (Z_to_bv 64 bufs1 :: [Z_to_bv 64 pixt; Z_to_bv 64 datat; Z_to_bv 64 pixd; Z_to_bv 64 datad])) => eq_trans (LEQ4 q0 (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL2 q0 (fun XX => Hq (or_intror XX)))) as LDEL3.
  pose proof (ne_live A2 _ _ _ Lpixs_a2 Fbufs1x) as NE_pixs_bufs1.
  pose proof (eq_trans (LEQ4 _ NE_pixs_bufs1) Lpixs_a2) as Lpixs_a3.
  pose proof (ne_live A2 _ _ _ Ldata_a2 Fbufs1x) as NE_data_bufs1.
  pose proof (eq_trans (LEQ4 _ NE_data_bufs1) Ldata_a2) as Ldata_a3.
  pose proof (ne_live A2 _ _ _ Lpixd_a2 Fbufs1x) as NE_pixd_bufs1.
  pose proof (eq_trans (LEQ4 _ NE_pixd_bufs1) Lpixd_a2) as Lpixd_a3.
  pose proof (ne_live A2 _ _ _ Ldatad_a2 Fbufs1x) as NE_datad_bufs1.
  pose proof (eq_trans (LEQ4 _ NE_datad_bufs1) Ldatad_a2) as Ldatad_a3.
  pose proof (ne_live A2 _ _ _ Lpixt_a2 Fbufs1x) as NE_pixt_bufs1.
  pose proof (eq_trans (LEQ4 _ NE_pixt_bufs1) Lpixt_a2) as Lpixt_a3.
  pose proof (ne_live A2 _ _ _ Ldatat_a2 Fbufs1x) as NE_datat_bufs1.
  pose proof (eq_trans (LEQ4 _ NE_datat_bufs1) Ldatat_a2) as Ldatat_a3.
  assert (PXd5 : PIXat m5 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_livk A2 M4 m5 pixd _ PXdM4 (proj2 PMc4) Lpixd_a2).
  assert (PXt5 : PIXat m5 pixt (hdv w h 8 0 datat)) by exact (exT_pix_livk A2 M4 m5 pixt _ PXtM4 (proj2 PMc4) Lpixt_a2).
  assert (PM5 : POSTM C A0 s m4 m5).
  { eapply POSTM_trans; [exact PM4|]. eapply POSTM_trans; [exact PMs4|]. apply (POSTM_sub C A0 A2 _ _ _ SUB2). apply (POSTM_mono C A2 (s + OFF4) s); [unfold OFF4; lia | exact PMc4]. }
  assert (KEPT4 : Forall (ex_region_kept E4 M4 m5) [(EVar 32, OFF4, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF4 256 M4 m5 E4 (EVar 32) CK (proj1 PMc4) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E4 M4 m5 _ [] _ HKc4 KEPT4) as HKk4.
  match type of HKk4 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E4 m5 kk') in HKk4 end.
  pose proof (regs_ok_agree 176%nat E4 (ex_envL vals4 r5 [bufs1; exW_canary SEGS 415784 m5]) _ _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa4.
  pose proof (exW_regs_call _ _ _ _ _ HRa4 (ex_regs_ok_junk vals4 r5 [bufs1; exW_canary SEGS 415784 m5] 176%nat ltac:(vm_cast_no_check (eq_refl 176%nat))) CS4) as HRn5.
  clear HRa4.
  assert (HKa5 : know_ok SEGS (ex_envL vals4 r5 [bufs1; exW_canary SEGS 415784 m5]) m5 _) by (exact (know_ok_agree SEGS 176%nat E4 _ m5 _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk4)).
  rewrite (fr_denot_agree 176%nat E4 (ex_envL vals4 r5 [bufs1; exW_canary SEGS 415784 m5]) _ fr2 (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r5 ex_r10 (EVar 208) HRn5 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres4)) as HRx5. clear HRn5. rename HRx5 into HRn5.
  clear HR HK Hlf Hms HKc4 HKk4 KEPT4 HC4 HWs4 PMs4 Q10_4 Q11_4 Q1_4 Q2_4 Q4_4 PM4 HW4 FRs4 PMc4 CS4 SUB2 RM2 LEQ4 Fbufs1x Lo4 OFF4 LDEL2 Hres4 Lpixs_a2 Ldata_a2 Lpixd_a2 Ldatad_a2 Lpixt_a2 Ldatat_a2 PXdM4 PXd4 PXtM4 PXt4.
  subst M4. clear log4. clear E4. try clear Rc4. clear KN4.
  lazymatch type of HRn5 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn5 end.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [bufs1; exW_canary SEGS 415784 m5]) m5) _ _ (ex_krange SEGS (ex_envL vals4 r5 [bufs1; exW_canary SEGS 415784 m5]) m5 (EVar 208) bufs1 4096 (2 ^ 47) eq_refl RRbufs1 ltac:(clear - Gbufs1 T1 T2 T3 LV Rnb; lia)) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals4 r5 [bufs1; exW_canary SEGS 415784 m5]) m5))) as HKb5.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A3 m5 _ (s - 256) (Z.to_nat 256) CK HW5 GLO1 GLO2) as SOK5.
  pose proof (exW_canary_ok SEGS 415784 m5 (canary_any m5)) as CANOK5.
  pose (vals5 := vals4 ++ map (getr r5) ex_regs_list ++ map (Z_to_bv 64) [bufs1; exW_canary SEGS 415784 m5]).
  pose proof (exW_kn_fixed SEGS C A3 m5 _ (ex_envL vals4 r5 [bufs1; exW_canary SEGS 415784 m5]) (EVar 209) (EVar 32) (exW_canary SEGS 415784 m5) s 256 415784 65536 212992 213416 213568 213416 213568
                HW5 eq_refl (proj1 CANOK5) (proj2 CANOK5) eq_refl eq_refl eq_refl SOK5 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf5.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb5 (proj2 (Forall_app _ _ _) (conj HKf5 HKa5)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn5 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN5 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb5 HKf5 HKa5 SOK5 CANOK5.
  repeat match goal with H : getr r5 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc5 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E5 := EEx) in HR, Hlf, HK, Hms |- *; set (log5 := LLx) in Hms, Hlf; set (M5 := mem_denot E5 m5 log5) in Hms end.
  assert (WP5 : W C A3 M5 (with_vmmaps vm3 md) /\ POSTM C A0 s m5 M5).
  { subst M5. apply (exW_win_blks C A3 A0 m5 _ E5 log5 (EVar 32) s 256 [] CK HW5 SUB3 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP5 as [HWs5 PMs5].
  pose proof (exW_win_only E5 m5 log5 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs5. change (mem_denot E5 m5 log5) with M5 in FRs5.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log5 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC5 : carry log5 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc5 : know_ok SEGS E5 M5 kn1) by (apply (carry_after SEGS E5 m5 log5 kn0 [] kn1 scs hs HC5 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact Hms |].
  pose (BS5 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 1); (172%nat, pixt); (173%nat, datat); (174%nat, wpl_of w 8); (208%nat, bufs1)]).
  exW_regfactB BS5 HR ex_r10 Q10_5. exW_regfactB BS5 HR ex_r11 Q11_5. exW_regfactB BS5 HR ex_r1 Q1_5. exW_regfactB BS5 HR ex_r2 Q2_5. exW_regfactB BS5 HR ex_r4 Q4_5.
  clear BS5.
  lazymatch type of Q2_5 with _ = Z_to_bv 64 (s + ?off) => pose (OFF5 := off) end.
  (* [comment removed for export] *)
  assert (PXdM5 : PIXat M5 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_sess C A3 m5 M5 _ s 256 pixd _ CK HW5 GLO1 Lpixd_a3 PXd5 FRs5).
  assert (PXtM5 : PIXat M5 pixt (hdv w h 8 0 datat)) by exact (exT_pix_sess C A3 m5 M5 _ s 256 pixt _ CK HW5 GLO1 Lpixt_a3 PXt5 FRs5).
  lazymatch type of Q1_5 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_5 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A3 M5 _ Rc5 (wpl_of w 8) 4 (kR - RK_pix - RK_rmc - 1) (bR - RB_pix14 - RB_rmc - alloc_margin (wpl_of w 8 * 4)) (Z_to_bv 64 ret) sp' S CK HWs5 Q10_5 Q11_5 ltac:(clear - Gwpls; lia) ltac:(lia) ltac:(clear - Gwpls; lia)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM3) ltac:(clear - HkR'; unfold RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB RBpos; lia) ltac:(unfold ROOM_NMAX; clear - Gwpls; lia) Q1_5
             ltac:(red; apply bv_eq; reflexivity) Q4_5 Q2_5 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF5, CALLOC_STACK, ALLOC_STACK; lia) ltac:(unfold OFF5; lia)) end end end.
  intros A4 m6 vm4 r6 res5 HW6 Hres5 CSx5 Hnz5 Fbufs2x Lo5 F0bufs2 LEQ5 ZERO5 ALbufs2 TOP5 PMc5 RM4.
  pose proof CSx5 as CS5. clear CSx5.
  rewrite with_vmmaps_twice in HW6 |- *.
  assert (Eres5 : res5 = Z_to_bv 64 (u res5)) by (symmetry; apply zbv_self).
  pose proof (u64_range res5) as RRbufs2. set (bufs2 := u res5) in *. clearbody bufs2. rewrite Eres5 in Hres5, Fbufs2x, Lo5, F0bufs2, LEQ5. clear Eres5 ZERO5 TOP5 Hnz5.
  rewrite (Z.mul_comm (wpl_of w 8) 4) in Lo5.
  assert (Gbufs2 : (4096 <= bufs2)%Z /\ (bufs2 + 4 * wpl_of w 8 <= alloc_top (c_vm C))%Z).
  { destruct (blk_range C A4 m6 _ (Z_to_bv 64 bufs2) (4 * wpl_of w 8) CK HW6 Lo5 Rnb) as [G1 G2]. rewrite u_Z2bv in G1, G2 by (clear - RRbufs2; lia). split; assumption. }
  pose proof (fresh_sub A0 A3 _ SUB3 Fbufs2x) as Fbufs2.
  pose proof Lo5 as Lbufs2_a4.
  assert (SUB4 : sub_live A0 A4).
  { intros q0 kq Lq. rewrite (LEQ5 q0 (ne_live A0 q0 _ kq Lq Fbufs2)). exact (SUB3 q0 kq Lq). }
  pose proof (fun (q0 : word) (Hq : ~ In q0 (Z_to_bv 64 bufs2 :: [Z_to_bv 64 bufs1; Z_to_bv 64 pixt; Z_to_bv 64 datat; Z_to_bv 64 pixd; Z_to_bv 64 datad])) => eq_trans (LEQ5 q0 (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL3 q0 (fun XX => Hq (or_intror XX)))) as LDEL4.
  pose proof (ne_live A3 _ _ _ Lpixs_a3 Fbufs2x) as NE_pixs_bufs2.
  pose proof (eq_trans (LEQ5 _ NE_pixs_bufs2) Lpixs_a3) as Lpixs_a4.
  pose proof (ne_live A3 _ _ _ Ldata_a3 Fbufs2x) as NE_data_bufs2.
  pose proof (eq_trans (LEQ5 _ NE_data_bufs2) Ldata_a3) as Ldata_a4.
  pose proof (ne_live A3 _ _ _ Lpixd_a3 Fbufs2x) as NE_pixd_bufs2.
  pose proof (eq_trans (LEQ5 _ NE_pixd_bufs2) Lpixd_a3) as Lpixd_a4.
  pose proof (ne_live A3 _ _ _ Ldatad_a3 Fbufs2x) as NE_datad_bufs2.
  pose proof (eq_trans (LEQ5 _ NE_datad_bufs2) Ldatad_a3) as Ldatad_a4.
  pose proof (ne_live A3 _ _ _ Lpixt_a3 Fbufs2x) as NE_pixt_bufs2.
  pose proof (eq_trans (LEQ5 _ NE_pixt_bufs2) Lpixt_a3) as Lpixt_a4.
  pose proof (ne_live A3 _ _ _ Ldatat_a3 Fbufs2x) as NE_datat_bufs2.
  pose proof (eq_trans (LEQ5 _ NE_datat_bufs2) Ldatat_a3) as Ldatat_a4.
  pose proof (ne_live A3 _ _ _ Lbufs1_a3 Fbufs2x) as NE_bufs1_bufs2.
  pose proof (eq_trans (LEQ5 _ NE_bufs1_bufs2) Lbufs1_a3) as Lbufs1_a4.
  assert (PXd6 : PIXat m6 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_livk A3 M5 m6 pixd _ PXdM5 (proj2 PMc5) Lpixd_a3).
  assert (PXt6 : PIXat m6 pixt (hdv w h 8 0 datat)) by exact (exT_pix_livk A3 M5 m6 pixt _ PXtM5 (proj2 PMc5) Lpixt_a3).
  assert (PM6 : POSTM C A0 s m4 m6).
  { eapply POSTM_trans; [exact PM5|]. eapply POSTM_trans; [exact PMs5|]. apply (POSTM_sub C A0 A3 _ _ _ SUB3). apply (POSTM_mono C A3 (s + OFF5) s); [unfold OFF5; lia | exact PMc5]. }
  assert (KEPT5 : Forall (ex_region_kept E5 M5 m6) [(EVar 32, OFF5, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF5 256 M5 m6 E5 (EVar 32) CK (proj1 PMc5) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E5 M5 m6 _ [] _ HKc5 KEPT5) as HKk5.
  match type of HKk5 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E5 m6 kk') in HKk5 end.
  pose proof (regs_ok_agree 210%nat E5 (ex_envL vals5 r6 [bufs2; exW_canary SEGS 415784 m6]) _ _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa5.
  pose proof (exW_regs_call _ _ _ _ _ HRa5 (ex_regs_ok_junk vals5 r6 [bufs2; exW_canary SEGS 415784 m6] 210%nat ltac:(vm_cast_no_check (eq_refl 210%nat))) CS5) as HRn6.
  clear HRa5.
  assert (HKa6 : know_ok SEGS (ex_envL vals5 r6 [bufs2; exW_canary SEGS 415784 m6]) m6 _) by (exact (know_ok_agree SEGS 210%nat E5 _ m6 _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk5)).
  rewrite (fr_denot_agree 210%nat E5 (ex_envL vals5 r6 [bufs2; exW_canary SEGS 415784 m6]) _ fr2 (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r6 ex_r10 (EVar 242) HRn6 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres5)) as HRx6. clear HRn6. rename HRx6 into HRn6.
  clear HR HK Hlf Hms HKc5 HKk5 KEPT5 HC5 HWs5 PMs5 Q10_5 Q11_5 Q1_5 Q2_5 Q4_5 PM5 HW5 FRs5 PMc5 CS5 SUB3 RM3 LEQ5 Fbufs2x Lo5 OFF5 LDEL3 Hres5 Lpixs_a3 Ldata_a3 Lpixd_a3 Ldatad_a3 Lpixt_a3 Ldatat_a3 Lbufs1_a3 PXdM5 PXd5 PXtM5 PXt5.
  subst M5. clear log5. clear E5. try clear Rc5. clear KN5.
  lazymatch type of HRn6 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn6 end.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [bufs2; exW_canary SEGS 415784 m6]) m6) _ _ (ex_krange SEGS (ex_envL vals5 r6 [bufs2; exW_canary SEGS 415784 m6]) m6 (EVar 242) bufs2 4096 (2 ^ 47) eq_refl RRbufs2 ltac:(clear - Gbufs2 T1 T2 T3 LV Rnb; lia)) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals5 r6 [bufs2; exW_canary SEGS 415784 m6]) m6))) as HKb6.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A4 m6 _ (s - 256) (Z.to_nat 256) CK HW6 GLO1 GLO2) as SOK6.
  pose proof (exW_canary_ok SEGS 415784 m6 (canary_any m6)) as CANOK6.
  pose (vals6 := vals5 ++ map (getr r6) ex_regs_list ++ map (Z_to_bv 64) [bufs2; exW_canary SEGS 415784 m6]).
  pose proof (exW_kn_fixed SEGS C A4 m6 _ (ex_envL vals5 r6 [bufs2; exW_canary SEGS 415784 m6]) (EVar 243) (EVar 32) (exW_canary SEGS 415784 m6) s 256 415784 65536 212992 213416 213568 213416 213568
                HW6 eq_refl (proj1 CANOK6) (proj2 CANOK6) eq_refl eq_refl eq_refl SOK6 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf6.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb6 (proj2 (Forall_app _ _ _) (conj HKf6 HKa6)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn6 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN6 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb6 HKf6 HKa6 SOK6 CANOK6.
  repeat match goal with H : getr r6 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc6 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E6 := EEx) in HR, Hlf, HK, Hms |- *; set (log6 := LLx) in Hms, Hlf; set (M6 := mem_denot E6 m6 log6) in Hms end.
  assert (WP6 : W C A4 M6 (with_vmmaps vm4 md) /\ POSTM C A0 s m6 M6).
  { subst M6. apply (exW_win_blks C A4 A0 m6 _ E6 log6 (EVar 32) s 256 [] CK HW6 SUB4 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP6 as [HWs6 PMs6].
  pose proof (exW_win_only E6 m6 log6 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs6. change (mem_denot E6 m6 log6) with M6 in FRs6.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log6 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC6 : carry log6 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc6 : know_ok SEGS E6 M6 kn1) by (apply (carry_after SEGS E6 m6 log6 kn0 [] kn1 scs hs HC6 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact Hms |].
  pose (BS6 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 1); (172%nat, pixt); (173%nat, datat); (174%nat, wpl_of w 8); (208%nat, bufs1); (242%nat, bufs2)]).
  exW_regfactB BS6 HR ex_r1 Q1_6. exW_regfactB BS6 HR ex_r2 Q2_6. exW_regfactB BS6 HR ex_r10 Q10_6. exW_regfactB BS6 HR ex_r11 Q11_6. exW_regfactB BS6 HR ex_r12 Q12_6. exW_regfactB BS6 HR ex_r13 Q13_6. exW_regfactB BS6 HR ex_r14 Q14_6. exW_regfactB BS6 HR ex_r15 Q15_6. exW_regfactB BS6 HR ex_r16 Q16_6. exW_regfactB BS6 HR ex_r17 Q17_6. exW_regfactB BS6 HR ex_r28 Q28_6. exW_regfactB BS6 HR ex_r29 Q29_6.
  clear BS6.
  lazymatch type of Q2_6 with _ = Z_to_bv 64 (s + ?off) => pose (OFF6 := off) end.
  (* [comment removed for export] *)
  assert (PXdM6 : PIXat M6 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_sess C A4 m6 M6 _ s 256 pixd _ CK HW6 GLO1 Lpixd_a4 PXd6 FRs6).
  assert (PXtM6 : PIXat M6 pixt (hdv w h 8 0 datat)) by exact (exT_pix_sess C A4 m6 M6 _ s 256 pixt _ CK HW6 GLO1 Lpixt_a4 PXt6 FRs6).
  lazymatch type of Q1_6 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (dbl_call_W fxk C A4 A0 M6 _ Rc6 (s + OFF6) w h datad datat bufs1 bufs2 10 10 (Z_to_bv 64 ra) S CK HWs6 SUB4
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF6; clear - Hlo1; lia) ltac:(unfold OFF6; clear - Hhi; lia) HOK Hw1 Hh1 ltac:(lia) ltac:(lia)
             Ldatad_a4 Fdatad F0datad Ldatat_a4 Lbufs1_a4 Fbufs1 F0bufs1 Lbufs2_a4 Fbufs2 F0bufs2 RRdatad RRdatat RRbufs1 RRbufs2
             NE_datad_datat NE_datad_bufs1 NE_datad_bufs2 NE_datat_bufs1 NE_datat_bufs2 NE_bufs1_bufs2 Q1_6 ltac:(red; apply bv_eq; reflexivity) Q2_6
             Q10_6 Q11_6 Q12_6 Q13_6 Q14_6 Q15_6 Q16_6 Q17_6 Q28_6 Q29_6) end end.
  intros r7 m7 HW7 PMc6 CSx6 KEEPB6.
  pose proof CSx6 as CS6. clear CSx6.
  assert (PXd7 : PIXat m7 pixd (set_data (pix_hdr w h 1) datad)) by exact (pix_keepb A4 M6 m7 pixd _ _ _ _ PXdM6 Lpixd_a4 NE_pixd_datad NE_pixd_bufs1 NE_pixd_bufs2 KEEPB6).
  assert (PXt7 : PIXat m7 pixt (hdv w h 8 0 datat)) by exact (pix_keepb A4 M6 m7 pixt _ _ _ _ PXtM6 Lpixt_a4 NE_pixt_datad NE_pixt_bufs1 NE_pixt_bufs2 KEEPB6).
  assert (PM7 : POSTM C A0 s m4 m7).
  { eapply POSTM_trans; [exact PM6|]. eapply POSTM_trans; [exact PMs6|]. apply (POSTM_mono C A0 (s + OFF6) s); [unfold OFF6; lia | exact PMc6]. }
  assert (KEPT6 : Forall (ex_region_kept E6 M6 m7) [(EVar 32, OFF6, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF6 256 M6 m7 E6 (EVar 32) CK (proj1 PMc6) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E6 M6 m7 _ [] _ HKc6 KEPT6) as HKk6.
  match type of HKk6 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E6 m7 kk') in HKk6 end.
  pose proof (regs_ok_agree 244%nat E6 (ex_envL vals6 r7 [exW_canary SEGS 415784 m7]) _ _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa6.
  pose proof (exW_regs_call _ _ _ _ _ HRa6 (ex_regs_ok_junk vals6 r7 [exW_canary SEGS 415784 m7] 244%nat ltac:(vm_cast_no_check (eq_refl 244%nat))) CS6) as HRn7.
  clear HRa6.
  assert (HKa7 : know_ok SEGS (ex_envL vals6 r7 [exW_canary SEGS 415784 m7]) m7 _) by (exact (know_ok_agree SEGS 244%nat E6 _ m7 _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk6)).
  rewrite (fr_denot_agree 244%nat E6 (ex_envL vals6 r7 [exW_canary SEGS 415784 m7]) _ fr2 (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc6 HKk6 KEPT6 HC6 HWs6 PMs6 Q1_6 Q2_6 Q10_6 Q11_6 Q12_6 Q13_6 Q14_6 Q15_6 Q16_6 Q17_6 Q28_6 Q29_6 PM6 HW6 FRs6 PMc6 CS6 OFF6 KEEPB6 PXdM6 PXd6 PXtM6 PXt6.
  subst M6. clear log6. clear E6. try clear Rc6. clear KN6.
  lazymatch type of HRn7 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn7 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A4 m7 _ (s - 256) (Z.to_nat 256) CK HW7 GLO1 GLO2) as SOK7.
  pose proof (exW_canary_ok SEGS 415784 m7 (canary_any m7)) as CANOK7.
  pose (vals7 := vals6 ++ map (getr r7) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m7]).
  pose proof (exW_kn_fixed SEGS C A4 m7 _ (ex_envL vals6 r7 [exW_canary SEGS 415784 m7]) (EVar 276) (EVar 32) (exW_canary SEGS 415784 m7) s 256 415784 65536 212992 213416 213568 213416 213568
                HW7 eq_refl (proj1 CANOK7) (proj2 CANOK7) eq_refl eq_refl eq_refl SOK7 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf7.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf7 HKa7)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn7 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN7 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf7 HKa7 SOK7 CANOK7.
  repeat match goal with H : getr r7 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc7 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E7 := EEx) in HR, Hlf, HK, Hms |- *; set (log7 := LLx) in Hms, Hlf; set (M7 := mem_denot E7 m7 log7) in Hms end.
  assert (WP7 : W C A4 M7 (with_vmmaps vm4 md) /\ POSTM C A0 s m7 M7).
  { subst M7. apply (exW_win_blks C A4 A0 m7 _ E7 log7 (EVar 32) s 256 [] CK HW7 SUB4 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP7 as [HWs7 PMs7].
  pose proof (exW_win_only E7 m7 log7 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs7. change (mem_denot E7 m7 log7) with M7 in FRs7.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log7 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC7 : carry log7 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc7 : know_ok SEGS E7 M7 kn1) by (apply (carry_after SEGS E7 m7 log7 kn0 [] kn1 scs hs HC7 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact Hms |].
  pose (BS7 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 1); (172%nat, pixt); (173%nat, datat); (174%nat, wpl_of w 8); (208%nat, bufs1); (242%nat, bufs2)]).
  exW_regfactB BS7 HR ex_r10 Q10_7. exW_regfactB BS7 HR ex_r1 Q1_7. exW_regfactB BS7 HR ex_r2 Q2_7. exW_regfactB BS7 HR ex_r4 Q4_7.
  clear BS7.
  lazymatch type of Q2_7 with _ = Z_to_bv 64 (s + ?off) => pose (OFF7 := off) end.
  (* [comment removed for export] *)
  assert (PXdM7 : PIXat M7 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_sess C A4 m7 M7 _ s 256 pixd _ CK HW7 GLO1 Lpixd_a4 PXd7 FRs7).
  assert (PXtM7 : PIXat M7 pixt (hdv w h 8 0 datat)) by exact (exT_pix_sess C A4 m7 M7 _ s 256 pixt _ CK HW7 GLO1 Lpixt_a4 PXt7 FRs7).
  lazymatch type of Q1_7 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_7 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A4 M7 _ Rc7 (Z_to_bv 64 bufs1) (Z_to_bv 64 ret) (4 * wpl_of w 8) sp' S CK HWs7 Q10_7 Lbufs1_a4 F0bufs1 Q1_7
             ltac:(red; apply bv_eq; reflexivity) Q4_7 Q2_7 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF7, ALLOC_STACK; clear - Hlo1; lia) ltac:(unfold OFF7; clear - Hhi; lia)) end end end.
  intros A5 m8 vm5 r8 HW8 CSx7 Ldead7 LEQ7 PMc7 RTR7.
  pose proof CSx7 as CS7. clear CSx7.
  rewrite with_vmmaps_twice in HW8 |- *.
  assert (SUB5 : sub_live A0 A5).
  { intros q0 kq Lq. rewrite (LEQ7 q0 (ne_live A0 q0 _ kq Lq Fbufs1)). exact (SUB4 q0 kq Lq). }
  assert (LDEL5 : forall q0 : word, ~ In q0 [Z_to_bv 64 bufs2; Z_to_bv 64 pixt; Z_to_bv 64 datat; Z_to_bv 64 pixd; Z_to_bv 64 datad] -> live A5 q0 = live A0 q0).
  { intros q0 Hq. destruct (decide (Z_to_bv 64 bufs1 = q0)) as [<-|NEq]; [rewrite Ldead7, Fbufs1; reflexivity|]. rewrite (LEQ7 q0 (fun EE => NEq (eq_sym EE))). apply LDEL4. clear - Hq NEq. cbn [In] in *. tauto. }
  pose proof (eq_trans (LEQ7 _ NE_pixs_bufs1) Lpixs_a4) as Lpixs_a5.
  pose proof (eq_trans (LEQ7 _ NE_data_bufs1) Ldata_a4) as Ldata_a5.
  pose proof (eq_trans (LEQ7 _ NE_pixd_bufs1) Lpixd_a4) as Lpixd_a5.
  pose proof (eq_trans (LEQ7 _ NE_datad_bufs1) Ldatad_a4) as Ldatad_a5.
  pose proof (eq_trans (LEQ7 _ NE_pixt_bufs1) Lpixt_a4) as Lpixt_a5.
  pose proof (eq_trans (LEQ7 _ NE_datat_bufs1) Ldatat_a4) as Ldatat_a5.
  pose proof (eq_trans (LEQ7 _ (fun EE => NE_bufs1_bufs2 (eq_sym EE))) Lbufs2_a4) as Lbufs2_a5.
  assert (PXd8 : PIXat m8 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_livk A5 M7 m8 pixd _ PXdM7 (proj2 PMc7) Lpixd_a5).
  assert (PXt8 : PIXat m8 pixt (hdv w h 8 0 datat)) by exact (exT_pix_livk A5 M7 m8 pixt _ PXtM7 (proj2 PMc7) Lpixt_a5).
  assert (PM8 : POSTM C A0 s m4 m8).
  { eapply POSTM_trans; [exact PM7|]. eapply POSTM_trans; [exact PMs7|]. apply (POSTM_sub C A0 A5 _ _ _ SUB5). apply (POSTM_mono C A5 (s + OFF7) s); [unfold OFF7; lia | exact PMc7]. }
  pose proof (RTR7 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM4) ltac:(clear - HkR'; unfold RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB RBpos; lia)) as RM5. rewrite !Z.sub_0_r in RM5.
  assert (KEPT7 : Forall (ex_region_kept E7 M7 m8) [(EVar 32, OFF7, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF7 256 M7 m8 E7 (EVar 32) CK (proj1 PMc7) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E7 M7 m8 _ [] _ HKc7 KEPT7) as HKk7.
  match type of HKk7 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E7 m8 kk') in HKk7 end.
  pose proof (regs_ok_agree 277%nat E7 (ex_envL vals7 r8 [exW_canary SEGS 415784 m8]) _ _ (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa7.
  pose proof (exW_regs_call _ _ _ _ _ HRa7 (ex_regs_ok_junk vals7 r8 [exW_canary SEGS 415784 m8] 277%nat ltac:(vm_cast_no_check (eq_refl 277%nat))) CS7) as HRn8.
  clear HRa7.
  assert (HKa8 : know_ok SEGS (ex_envL vals7 r8 [exW_canary SEGS 415784 m8]) m8 _) by (exact (know_ok_agree SEGS 277%nat E7 _ m8 _ (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk7)).
  rewrite (fr_denot_agree 277%nat E7 (ex_envL vals7 r8 [exW_canary SEGS 415784 m8]) _ fr2 (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc7 HKk7 KEPT7 HC7 HWs7 PMs7 Q10_7 Q1_7 Q2_7 Q4_7 PM7 HW7 FRs7 PMc7 CS7 SUB4 RM4 Ldead7 LEQ7 RTR7 Lbufs1_a4 OFF7 LDEL4 Lpixs_a4 Ldata_a4 Lpixd_a4 Ldatad_a4 Lpixt_a4 Ldatat_a4 Lbufs2_a4 PXdM7 PXd7 PXtM7 PXt7.
  subst M7. clear log7. clear E7. try clear Rc7. clear KN7.
  lazymatch type of HRn8 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn8 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A5 m8 _ (s - 256) (Z.to_nat 256) CK HW8 GLO1 GLO2) as SOK8.
  pose proof (exW_canary_ok SEGS 415784 m8 (canary_any m8)) as CANOK8.
  pose (vals8 := vals7 ++ map (getr r8) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m8]).
  pose proof (exW_kn_fixed SEGS C A5 m8 _ (ex_envL vals7 r8 [exW_canary SEGS 415784 m8]) (EVar 309) (EVar 32) (exW_canary SEGS 415784 m8) s 256 415784 65536 212992 213416 213568 213416 213568
                HW8 eq_refl (proj1 CANOK8) (proj2 CANOK8) eq_refl eq_refl eq_refl SOK8 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf8.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf8 HKa8)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn8 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN8 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf8 HKa8 SOK8 CANOK8.
  repeat match goal with H : getr r8 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc8 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E8 := EEx) in HR, Hlf, HK, Hms |- *; set (log8 := LLx) in Hms, Hlf; set (M8 := mem_denot E8 m8 log8) in Hms end.
  assert (WP8 : W C A5 M8 (with_vmmaps vm5 md) /\ POSTM C A0 s m8 M8).
  { subst M8. apply (exW_win_blks C A5 A0 m8 _ E8 log8 (EVar 32) s 256 [] CK HW8 SUB5 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP8 as [HWs8 PMs8].
  pose proof (exW_win_only E8 m8 log8 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs8. change (mem_denot E8 m8 log8) with M8 in FRs8.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log8 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC8 : carry log8 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc8 : know_ok SEGS E8 M8 kn1) by (apply (carry_after SEGS E8 m8 log8 kn0 [] kn1 scs hs HC8 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW8)) | exact (mp_lazy _ (w_pure _ _ _ _ HW8)) | exact Hms |].
  pose (BS8 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 1); (172%nat, pixt); (173%nat, datat); (174%nat, wpl_of w 8); (208%nat, bufs1); (242%nat, bufs2)]).
  exW_regfactB BS8 HR ex_r10 Q10_8. exW_regfactB BS8 HR ex_r1 Q1_8. exW_regfactB BS8 HR ex_r2 Q2_8. exW_regfactB BS8 HR ex_r4 Q4_8.
  clear BS8.
  lazymatch type of Q2_8 with _ = Z_to_bv 64 (s + ?off) => pose (OFF8 := off) end.
  (* [comment removed for export] *)
  assert (PXdM8 : PIXat M8 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_sess C A5 m8 M8 _ s 256 pixd _ CK HW8 GLO1 Lpixd_a5 PXd8 FRs8).
  assert (PXtM8 : PIXat M8 pixt (hdv w h 8 0 datat)) by exact (exT_pix_sess C A5 m8 M8 _ s 256 pixt _ CK HW8 GLO1 Lpixt_a5 PXt8 FRs8).
  lazymatch type of Q1_8 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_8 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A5 M8 _ Rc8 (Z_to_bv 64 bufs2) (Z_to_bv 64 ret) (4 * wpl_of w 8) sp' S CK HWs8 Q10_8 Lbufs2_a5 F0bufs2 Q1_8
             ltac:(red; apply bv_eq; reflexivity) Q4_8 Q2_8 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF8, ALLOC_STACK; clear - Hlo1; lia) ltac:(unfold OFF8; clear - Hhi; lia)) end end end.
  intros A6 m9 vm6 r9 HW9 CSx8 Ldead8 LEQ8 PMc8 RTR8.
  pose proof CSx8 as CS8. clear CSx8.
  rewrite with_vmmaps_twice in HW9 |- *.
  assert (SUB6 : sub_live A0 A6).
  { intros q0 kq Lq. rewrite (LEQ8 q0 (ne_live A0 q0 _ kq Lq Fbufs2)). exact (SUB5 q0 kq Lq). }
  assert (LDEL6 : forall q0 : word, ~ In q0 [Z_to_bv 64 pixt; Z_to_bv 64 datat; Z_to_bv 64 pixd; Z_to_bv 64 datad] -> live A6 q0 = live A0 q0).
  { intros q0 Hq. destruct (decide (Z_to_bv 64 bufs2 = q0)) as [<-|NEq]; [rewrite Ldead8, Fbufs2; reflexivity|]. rewrite (LEQ8 q0 (fun EE => NEq (eq_sym EE))). apply LDEL5. clear - Hq NEq. cbn [In] in *. tauto. }
  pose proof (eq_trans (LEQ8 _ NE_pixs_bufs2) Lpixs_a5) as Lpixs_a6.
  pose proof (eq_trans (LEQ8 _ NE_data_bufs2) Ldata_a5) as Ldata_a6.
  pose proof (eq_trans (LEQ8 _ NE_pixd_bufs2) Lpixd_a5) as Lpixd_a6.
  pose proof (eq_trans (LEQ8 _ NE_datad_bufs2) Ldatad_a5) as Ldatad_a6.
  pose proof (eq_trans (LEQ8 _ NE_pixt_bufs2) Lpixt_a5) as Lpixt_a6.
  pose proof (eq_trans (LEQ8 _ NE_datat_bufs2) Ldatat_a5) as Ldatat_a6.
  assert (PXd9 : PIXat m9 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_livk A6 M8 m9 pixd _ PXdM8 (proj2 PMc8) Lpixd_a6).
  assert (PXt9 : PIXat m9 pixt (hdv w h 8 0 datat)) by exact (exT_pix_livk A6 M8 m9 pixt _ PXtM8 (proj2 PMc8) Lpixt_a6).
  assert (PM9 : POSTM C A0 s m4 m9).
  { eapply POSTM_trans; [exact PM8|]. eapply POSTM_trans; [exact PMs8|]. apply (POSTM_sub C A0 A6 _ _ _ SUB6). apply (POSTM_mono C A6 (s + OFF8) s); [unfold OFF8; lia | exact PMc8]. }
  pose proof (RTR8 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM5) ltac:(clear - HkR'; unfold RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB RBpos; lia)) as RM6. rewrite !Z.sub_0_r in RM6.
  assert (KEPT8 : Forall (ex_region_kept E8 M8 m9) [(EVar 32, OFF8, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF8 256 M8 m9 E8 (EVar 32) CK (proj1 PMc8) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E8 M8 m9 _ [] _ HKc8 KEPT8) as HKk8.
  match type of HKk8 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E8 m9 kk') in HKk8 end.
  pose proof (regs_ok_agree 310%nat E8 (ex_envL vals8 r9 [exW_canary SEGS 415784 m9]) _ _ (vals_app_agree vals8 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa8.
  pose proof (exW_regs_call _ _ _ _ _ HRa8 (ex_regs_ok_junk vals8 r9 [exW_canary SEGS 415784 m9] 310%nat ltac:(vm_cast_no_check (eq_refl 310%nat))) CS8) as HRn9.
  clear HRa8.
  assert (HKa9 : know_ok SEGS (ex_envL vals8 r9 [exW_canary SEGS 415784 m9]) m9 _) by (exact (know_ok_agree SEGS 310%nat E8 _ m9 _ (vals_app_agree vals8 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk8)).
  rewrite (fr_denot_agree 310%nat E8 (ex_envL vals8 r9 [exW_canary SEGS 415784 m9]) _ fr2 (vals_app_agree vals8 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc8 HKk8 KEPT8 HC8 HWs8 PMs8 Q10_8 Q1_8 Q2_8 Q4_8 PM8 HW8 FRs8 PMc8 CS8 SUB5 RM5 Ldead8 LEQ8 RTR8 Lbufs2_a5 OFF8 LDEL5 Lpixs_a5 Ldata_a5 Lpixd_a5 Ldatad_a5 Lpixt_a5 Ldatat_a5 PXdM8 PXd8 PXtM8 PXt8.
  subst M8. clear log8. clear E8. try clear Rc8. clear KN8.
  lazymatch type of HRn9 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn9 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A6 m9 _ (s - 256) (Z.to_nat 256) CK HW9 GLO1 GLO2) as SOK9.
  pose proof (exW_canary_ok SEGS 415784 m9 (canary_any m9)) as CANOK9.
  pose (vals9 := vals8 ++ map (getr r9) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m9]).
  pose proof (exW_kn_fixed SEGS C A6 m9 _ (ex_envL vals8 r9 [exW_canary SEGS 415784 m9]) (EVar 342) (EVar 32) (exW_canary SEGS 415784 m9) s 256 415784 65536 212992 213416 213568 213416 213568
                HW9 eq_refl (proj1 CANOK9) (proj2 CANOK9) eq_refl eq_refl eq_refl SOK9 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf9.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf9 HKa9)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn9 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN9 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf9 HKa9 SOK9 CANOK9.
  repeat match goal with H : getr r9 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc9 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E9 := EEx) in HR, Hlf, HK, Hms |- *; set (log9 := LLx) in Hms, Hlf; set (M9 := mem_denot E9 m9 log9) in Hms end.
  assert (WP9 : W C A6 M9 (with_vmmaps vm6 md) /\ POSTM C A0 s m9 M9).
  { subst M9. apply (exW_win_blks C A6 A0 m9 _ E9 log9 (EVar 32) s 256 [] CK HW9 SUB6 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP9 as [HWs9 PMs9].
  pose proof (exW_win_only E9 m9 log9 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs9. change (mem_denot E9 m9 log9) with M9 in FRs9.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log9 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC9 : carry log9 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc9 : know_ok SEGS E9 M9 kn1) by (apply (carry_after SEGS E9 m9 log9 kn0 [] kn1 scs hs HC9 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW9)) | exact (mp_lazy _ (w_pure _ _ _ _ HW9)) | exact Hms |].
  pose (BS9 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 1); (172%nat, pixt); (173%nat, datat); (174%nat, wpl_of w 8); (208%nat, bufs1); (242%nat, bufs2)]).
  exW_regfactB BS9 HR ex_r10 Q10_9. exW_regfactB BS9 HR ex_r1 Q1_9. exW_regfactB BS9 HR ex_r2 Q2_9. exW_regfactB BS9 HR ex_r4 Q4_9.
  clear BS9.
  lazymatch type of Q2_9 with _ = Z_to_bv 64 (s + ?off) => pose (OFF9 := off) end.
  (* [comment removed for export] *)
  pose (BSx9 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 1); (172%nat, pixt); (173%nat, datat); (174%nat, wpl_of w 8); (208%nat, bufs1); (242%nat, bufs2)]).
  exW_cellB HK Hlf r0 BSx9 (EVar 32) s (-96)%Z 8%nat CELLpp.
  clear BSx9.
  assert (PXdM9 : PIXat M9 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_sess C A6 m9 M9 _ s 256 pixd _ CK HW9 GLO1 Lpixd_a6 PXd9 FRs9).
  assert (PXtM9 : PIXat M9 pixt (hdv w h 8 0 datat)) by exact (exT_pix_sess C A6 m9 M9 _ s 256 pixt _ CK HW9 GLO1 Lpixt_a6 PXt9 FRs9).
  assert (PPlo : (s + OFF9 <= s + -96)%Z) by (unfold OFF9; lia). assert (PPhi : (s + -96 + 8 <= c_top C)%Z) by lia.
  rewrite PC_DESTROY_eq.
  lazymatch type of Q1_9 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixDestroy_keep_W (fx := fxk) C A6 M9 _ Rc9 (s + OFF9) (s + -96) pixt 0 0 (4 * (wpl_of w 8 * h)) (hdv w h 8 0 datat) cv (Z_to_bv 64 ra) S CK HWs9 Q2_9
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF9, ALLOC_STACK; clear - Hlo1; lia) PPlo PPhi Q1_9 ltac:(red; apply bv_eq; reflexivity) Q4_9 ltac:(rewrite <- Zplus_mod_idemp_l, Hs8; reflexivity) Q10_9 CELLpp
             PXtM9 eq_refl eq_refl eq_refl Lpixt_a6 F0pixt Ldatat_a6 F0datat Rns (fun EE => NEptdt (eq_sym EE)) (or_introl eq_refl)) end end.
  intros A7 m10 vm7 r10 HW10 CSx9 PDP PMc9 CELL0 FRMs9 RTR9.
  pose proof CSx9 as CS9. clear CSx9.
  rewrite with_vmmaps_twice in HW10 |- *.
  destruct PDP as (Dpixt & Ddatat & _ & LEQ9). change (p_data (hdv w h 8 0 datat)) with datat in Ddatat, LEQ9.
  assert (NZdatat : datat <> 0%Z) by lia.
  pose proof (fun (q0 : word) (N1 : q0 <> Z_to_bv 64 pixt) (N2 : q0 <> Z_to_bv 64 datat) => LEQ9 q0 N1 (fun _ => N2) (fun XX : 0%Z <> 0%Z => False_ind _ (XX eq_refl))) as LEQx9.
  pose proof (eq_trans (LEQx9 _ NE_pixd_pixt NE_pixd_datat) Lpixd_a6) as Lpixd_a7.
  pose proof (eq_trans (LEQx9 _ NE_datad_pixt NE_datad_datat) Ldatad_a6) as Ldatad_a7.
  assert (SUB7 : sub_live A0 A7).
  { intros q0 kq Lq. rewrite (LEQx9 q0 (ne_live A0 q0 _ kq Lq Fpixt) (ne_live A0 q0 _ kq Lq Fdatat)). exact (SUB6 _ _ Lq). }
  assert (LDEL7 : forall q0 : word, ~ In q0 [Z_to_bv 64 pixd; Z_to_bv 64 datad] -> live A7 q0 = live A0 q0).
  { intros q0 Hq. destruct (decide (Z_to_bv 64 pixt = q0)) as [<-|NEq1]; [rewrite Dpixt, Fpixt; reflexivity|].
    destruct (decide (Z_to_bv 64 datat = q0)) as [<-|NEq2]; [rewrite (Ddatat NZdatat), Fdatat; reflexivity|].
    rewrite (LEQx9 q0 (fun EE => NEq1 (eq_sym EE)) (fun EE => NEq2 (eq_sym EE))). apply LDEL6. clear - Hq NEq1 NEq2. cbn [In] in *. tauto. }
  pose proof (RTR9 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM6) ltac:(clear - HkR'; unfold RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB RBpos; lia)) as RM7. rewrite !Z.sub_0_r in RM7.
  assert (PMB10 : POSTM C A0 s m0 m10).
  { eapply POSTM_trans; [exact PMB4|]. eapply POSTM_trans; [exact (POSTM_trans _ _ _ _ _ _ PM9 PMs9)|]. apply (POSTM_sub C A0 A7 _ _ _ SUB7). apply (POSTM_mono C A7 (s + -96 + 8) s); [lia | exact PMc9]. }
  assert (PXd10 : PIXat m10 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_livk A7 M9 m10 pixd _ PXdM9 (proj2 PMc9) Lpixd_a7).
  assert (FRMx9 : FRM C (s + -88) M9 m10).
  { replace (s + -88)%Z with (s + -96 + 8)%Z by lia. exact (proj1 PMc9). }
  pose proof (POSTM_refl C A0 s m10) as PM10.
  assert (KEPT9 : Forall (ex_region_kept E9 M9 m10) [(EVar 32, (-88)%Z, 0%Z); (EVar 32, OFF9, (-96)%Z)]).
  { constructor; [exact (exW_kept_stack2 C s (-88) 256 M9 m10 E9 (EVar 32) CK FRMx9 Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exT_kept_in E9 M9 m10 (EVar 32) s OFF9 (-96) (s + OFF9) (s + -96) FRMs9 eq_refl RS (Z.le_refl _) (Z.le_refl _))|]. constructor. }
  pose proof (ex_know_keepD SEGS E9 M9 m10 _ [] _ HKc9 KEPT9) as HKk9.
  match type of HKk9 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E9 m10 kk') in HKk9 end.
  pose proof (regs_ok_agree 343%nat E9 (ex_envL vals9 r10 [exW_canary SEGS 415784 m10]) _ _ (vals_app_agree vals9 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa9.
  pose proof (exW_regs_call _ _ _ _ _ HRa9 (ex_regs_ok_junk vals9 r10 [exW_canary SEGS 415784 m10] 343%nat ltac:(vm_cast_no_check (eq_refl 343%nat))) CS9) as HRn10.
  clear HRa9.
  assert (HKa10 : know_ok SEGS (ex_envL vals9 r10 [exW_canary SEGS 415784 m10]) m10 _) by (exact (know_ok_agree SEGS 343%nat E9 _ m10 _ (vals_app_agree vals9 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk9)).
  rewrite (fr_denot_agree 343%nat E9 (ex_envL vals9 r10 [exW_canary SEGS 415784 m10]) _ fr2 (vals_app_agree vals9 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc9 HKk9 KEPT9 HC9 HWs9 PMs9 Q10_9 Q1_9 Q2_9 Q4_9 PM9 HW9 FRs9 CS9 OFF9 CELLpp PXdM9 PXtM9 PPlo PPhi PXd9 PXt9 PMc9 FRMx9 CELL0 FRMs9 RTR9 LEQ9 LEQx9 LDEL6 PMB4 RM6.
  subst M9. clear log9. clear E9. try clear Rc9. clear KN9.
  lazymatch type of HRn10 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn10 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A7 m10 _ (s - 256) (Z.to_nat 256) CK HW10 GLO1 GLO2) as SOK10.
  pose proof (exW_canary_ok SEGS 415784 m10 (canary_any m10)) as CANOK10.
  pose (vals10 := vals9 ++ map (getr r10) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m10]).
  pose proof (exW_kn_fixed SEGS C A7 m10 _ (ex_envL vals9 r10 [exW_canary SEGS 415784 m10]) (EVar 375) (EVar 32) (exW_canary SEGS 415784 m10) s 256 415784 65536 212992 213416 213568 213416 213568
                HW10 eq_refl (proj1 CANOK10) (proj2 CANOK10) eq_refl eq_refl eq_refl SOK10 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf10.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf10 HKa10)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn10 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN10 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf10 HKa10 SOK10 CANOK10.
  repeat match goal with H : getr r10 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E10 := EEx) in HR, Hlf, HK, Hms |- *; set (log10 := LLx) in Hms, Hlf; set (M10 := mem_denot E10 m10 log10) in Hms end.
  assert (WP10 : W C A7 M10 (with_vmmaps vm7 md) /\ POSTM C A0 s m10 M10).
  { subst M10. apply (exW_win_blks C A7 A0 m10 _ E10 log10 (EVar 32) s 256 [] CK HW10 SUB7 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP10 as [HWs10 PMs10].
  pose proof (exW_win_only E10 m10 log10 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs10. change (mem_denot E10 m10 log10) with M10 in FRs10.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW10)) | exact (mp_lazy _ (w_pure _ _ _ _ HW10)) | exact Hms |].
  pose (BSF := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 1); (172%nat, pixt); (173%nat, datat); (174%nat, wpl_of w 8); (208%nat, bufs1); (242%nat, bufs2)]).
  exW_regfactB BSF HR ex_r10 G10.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ => apply (HC fxk A7 M10 vm7 RcF FZ HWs10) end.
  + lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 RcF [(2%nat, EVar 32); (4%nat, ELit 284096)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor; [symmetry; exact HTP | constructor]] | vm_compute; reflexivity] end.
  + exact (POSTM_trans _ _ _ _ _ _ PMB10 PMs10).
  + right. exists pixd, datad, 0%Z, cv. split; [exact G10|]. split; [|reflexivity].
    refine (conj Gpd1 (conj Gpd2 (conj ALpixd (conj Gdd1 (conj Gdd2 (conj ALdatad (conj NEpd (conj Fpixd (conj Fdatad (conj F0pixd (conj F0datad (conj Lpixd_a7 (conj Ldatad_a7 (conj _ _)))))))))))))).
    * exact (exT_pix_sess C A7 m10 M10 _ s 256 pixd _ CK HW10 GLO1 Lpixd_a7 PXd10 FRs10).
    * left. split; [reflexivity|]. intros q0 N1 N2. apply LDEL7. clear - N1 N2. cbn [In]. intros [EE|[EE|[]]]; [apply N1 | apply N2]; symmetry; exact EE.
  + apply (aroom_mono _ _ _ _ _ _ RM7); [unfold RK_dbin; clear - HkR'; lia | unfold RB_dbin; clear - HbR' MGB; lia].
Qed.
End Spec.
End Chain.
