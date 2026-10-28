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
Import V15CL14a.V15LeptThrLeaf. Import V15CL14a.V15LeptDither_iface.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL15a.
Import V15CL15a.V15LeptPixDestroyRc2.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptCmapLin.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL11a.
Import V15CL11a.V15LeptSetCmapS.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptDith2W.
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

Definition STOPS : list Z := [93000; 95132; 95788; 106268; 166172; 116832; 99744; 95932; 166484; 94372]%Z.
Definition FDEF : list (nat * nat) := [(8%nat, 33%nat)].
Definition PC_PIXCREATE : word := 93000%bv.
Lemma PC_PIXCREATE_eq : Z_to_bv 64 93000 = PC_PIXCREATE. Proof. apply bv_eq; reflexivity. Qed.
Definition PC_SETCMAP : word := 95932%bv.
Lemma PC_SETCMAP_eq : Z_to_bv 64 95932 = PC_SETCMAP. Proof. apply bv_eq; reflexivity. Qed.
Definition PC_DESTROY : word := 94372%bv.
Lemma PC_DESTROY_eq : Z_to_bv 64 94372 = PC_DESTROY. Proof. apply bv_eq; reflexivity. Qed.
Definition ex_r18 : reg := 18%bv. Definition ex_r19 : reg := 19%bv. Definition ex_r20 : reg := 20%bv. Definition ex_r21 : reg := 21%bv. Definition ex_r22 : reg := 22%bv. Definition ex_r25 : reg := 25%bv.

Lemma cmf_keep : forall (fx : FPState) (A A' : AS) (m m' : word -> option byte) (cm : Z) (cv : cmapv), cm_facts A m cm cv -> sub_live A A' -> LIVK A m m' -> cm_facts A' m' cm cv.
Proof.
  intros fx A A' m m' cm cv [->|(CM & OK & L1 & L2)] SUB LK; [left; reflexivity | right].
  split; [exact (exT_cmap_livk A m m' cm cv CM LK L1) | split; [exact OK | split; [exact (SUB _ _ L1) | exact (SUB _ _ L2)]]].
Qed.
Lemma fresh_sub : forall (Ar A : AS) (q : word), sub_live Ar A -> live A q = None -> live Ar q = None.
Proof. intros Ar A q SUB F. destruct (live Ar q) as [k|] eqn:EE; [|reflexivity]. rewrite (SUB _ _ EE) in F. discriminate F. Qed.
Lemma ne_live : forall (A : AS) (p q : word) (k : Z), live A p = Some k -> live A q = None -> p <> q.
Proof. intros A p q k L F ->. rewrite F in L. discriminate L. Qed.
(* [comment removed for export] *)
Lemma pix_keepl : forall (A : AS) (M m' : word -> option byte) (p : Z) (v : pixv) (l : list word), PIXat M p v -> live A (Z_to_bv 64 p) = Some 64%Z ->
  ~ List.In (Z_to_bv 64 p) l ->
  (forall (q : word) k, live A q = Some k -> ~ List.In q l -> forall i, (0 <= i < k)%Z -> m' (at_ q i) = M (at_ q i)) -> PIXat m' p v.
Proof.
  intros A M m' p v l PX L NI KB. pose proof PX as (Hp0 & Hp64 & _). apply (PIXat_frame M); [exact PX|]. intros x Hx.
  pose proof (KB _ _ L NI (u x - p)%Z ltac:(lia)) as EE.
  replace (at_ (Z_to_bv 64 p) (u x - p)) with x in EE by (unfold at_; apply bv_eq; rewrite !u_Z2bv; rewrite ?u_Z2bv; pose proof (u64_range x); lia).
  exact EE.
Qed.
Lemma pix_keep1 : forall (A : AS) (M m' : word -> option byte) (p : Z) (v : pixv) (d : word), PIXat M p v -> live A (Z_to_bv 64 p) = Some 64%Z -> Z_to_bv 64 p <> d ->
  (forall (q : word) k, live A q = Some k -> q <> d -> forall i, (0 <= i < k)%Z -> m' (at_ q i) = M (at_ q i)) -> PIXat m' p v.
Proof.
  intros A M m' p v d PX L NE KB. pose proof PX as (Hp0 & Hp64 & _). apply (PIXat_frame M); [exact PX|]. intros x Hx.
  pose proof (KB _ _ L NE (u x - p)%Z ltac:(lia)) as EE.
  replace (at_ (Z_to_bv 64 p) (u x - p)) with x in EE by (unfold at_; apply bv_eq; rewrite !u_Z2bv; rewrite ?u_Z2bv; pose proof (u64_range x); lia).
  exact EE.
Qed.
Lemma zero_livk : forall (A : AS) (M m' : word -> option byte) (p : word) (n : Z), LIVK A M m' -> live A p = Some n ->
  (forall i, (0 <= i < n)%Z -> M (at_ p i) = Some (Z_to_bv 8 0)) -> (forall i, (0 <= i < n)%Z -> m' (at_ p i) = Some (Z_to_bv 8 0)).
Proof. intros A M m' p n LK L Z i Hi. rewrite (LK p n i L Hi). exact (Z i Hi). Qed.

Section Spec.
Hypothesis HRMC : pixRemoveColormap_gray8_contract.

Theorem pixDitherTo2bpp_W : pixDitherTo2bpp_contract.
Proof.
  unfold pixDitherTo2bpp_contract, PC_pixDitherTo2bpp, TP15.
  intros fx C A0 m0 md r0 s pixs w h cm data cv ret S FZ CK HW0 H2 Hs16 Hlo0 Hhi H1 Hret H4 H10 H11 PXs HOK Hw1 Hh1 Lpixs_a0 F0pixs Ldata_a0 CMF kR bR RM0 HkR HbR HC.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  assert (HTP : ex_keep (getr r0 ex_r4 = Z_to_bv 64 284096)) by exact H4.
  assert (Hlo : (c_top C - LSTK + 256 <= s)%Z) by (unfold D2BPP_STACK, RMC_STACK, LSF in Hlo0; lia).
  assert (Hlo1 : (c_top C - LSTK + 4096 <= s)%Z) by (unfold D2BPP_STACK, RMC_STACK, LSF in Hlo0; lia). clear Hlo0.
  assert (HkR' : (RK_pix + RK_rmc + 5 + 2 <= kR)%Z) by (unfold RK_d2bpp, RK_cml in HkR; lia).
  assert (HbR' : (RB_pix14 + RB_rmc + 2 * 2 ^ 21 + 3 * 2 ^ 17 + RB_cml <= bR)%Z) by (unfold RB_d2bpp in HbR; lia). clear HkR HbR.
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
  pose proof (hdr_ok_8_2 w h HOK Hw1 Hh1) as HOK1.
  destruct (dith_wpl_facts2 w h HOK Hw1 Hh1) as (Gwpls & Gwpld & _ & _ & _ & Psh & Pdh & Psh1 & Pdh1).
  assert (Rw : (0 <= w < 2 ^ 31)%Z) by (destruct HOK as (_ & X & _); lia). assert (Rh : (0 <= h < 2 ^ 31)%Z) by (destruct HOK as (_ & _ & X & _); lia).
  assert (Rnd : (0 < 4 * (wpl_of w 2 * h))%Z) by lia. assert (Rns : (0 < 4 * (wpl_of w 8 * h))%Z) by lia. assert (Rnb : (0 < 4 * wpl_of w 8)%Z) by lia.
  assert (MGB : (alloc_margin (wpl_of w 8 * 4) <= 2 ^ 21)%Z) by (pose proof (alloc_margin_big (wpl_of w 8 * 4) ltac:(lia)); lia).
  assert (RBpos : (0 <= RB_pix14 /\ 0 <= RB_rmc /\ RB_cml = 2 * 2 ^ 17)%Z) by (unfold RB_rmc, RB_pix14, RB_hdr, RB_cml; lia).
  pose proof (alloc_margin_small (256 * 4) ltac:(lia)) as MG17.
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
    apply (pixCreate_sure_W (fx := fxk) C A0 M0 _ Rc0 (s + OFF0) w h 2 (Z_to_bv 64 ra) S CK HWs0 Q2_0
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF0, LSF; lia) ltac:(unfold OFF0; lia) Q1_0 ltac:(red; apply bv_eq; reflexivity) Q4_0 Q10_0 Q11_0 Q12_0 Hw1 Hh1 HOK1 kR bR
             ltac:(rewrite with_vmmaps_vmmaps; exact RM0) ltac:(clear - HkR'; unfold RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' RBpos; lia)) end end.
  intros A1 m1 vm1 r1 pixd datad HW1 CSx0 PMc0 A10_0 PXN RM1.
  pose proof CSx0 as CS0. clear CSx0.
  rewrite with_vmmaps_twice in HW1 |- *.
  destruct PXN as (Gpd1 & Gpd2 & ALpixd & Gdd1 & Gdd2 & ALdatad & NEpd & Fpixd & Fdatad & F0pixd & F0datad & Lpixd_a1 & Ldatad_a1 & LEQ0 & PXd1 & _).
  change (p_wpl (set_data (pix_hdr w h 2) datad)) with (wpl_of w 2) in Gdd2, Ldatad_a1. change (p_h (set_data (pix_hdr w h 2) datad)) with h in Gdd2, Ldatad_a1.
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
  pose proof (regs_ok_agree 38%nat E0 (ex_envL vals0 r1 [pixd; datad; wpl_of w 2; exW_canary SEGS 415784 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [pixd; datad; wpl_of w 2; exW_canary SEGS 415784 m1] 38%nat ltac:(vm_cast_no_check (eq_refl 38%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [pixd; datad; wpl_of w 2; exW_canary SEGS 415784 m1]) m1 _) by (exact (know_ok_agree SEGS 38%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  rewrite (fr_denot_agree 38%nat E0 (ex_envL vals0 r1 [pixd; datad; wpl_of w 2; exW_canary SEGS 415784 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r1 ex_r10 (EVar 70) HRn1 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_0)) as HRx1. clear HRn1. rename HRx1 into HRn1.
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q11_0 Q12_0 Q1_0 Q2_0 Q4_0 PM0 HW0 FRs0 PMc0 CS0 OFF0 LEQ0 RM0 A10_0.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  pose proof (exT_kn_pix SEGS C A1 m1 _ (ex_envL vals0 r1 [pixd; datad; wpl_of w 2; exW_canary SEGS 415784 m1]) (EVar 70) (EVar 32) (EVar 71) (EVar 72) pixd s 256 _ CK HW1 Lpixd_a1 PXd1 eq_refl eq_refl RS GLO1 eq_refl eq_refl) as HKp1.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m1 _ (s - 256) (Z.to_nat 256) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 415784 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [pixd; datad; wpl_of w 2; exW_canary SEGS 415784 m1]).
  pose proof (exW_kn_fixed SEGS C A1 m1 _ (ex_envL vals0 r1 [pixd; datad; wpl_of w 2; exW_canary SEGS 415784 m1]) (EVar 73) (EVar 32) (exW_canary SEGS 415784 m1) s 256 415784 65536 212992 213416 213568 213416 213568
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
  pose (BS1 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2)]).
  exW_regfactB BS1 HR ex_r10 Q10_1. exW_regfactB BS1 HR ex_r11 Q11_1. exW_regfactB BS1 HR ex_r1 Q1_1. exW_regfactB BS1 HR ex_r2 Q2_1.
  clear BS1.
  lazymatch type of Q2_1 with _ = Z_to_bv 64 (s + ?off) => pose (OFF1 := off) end.
  (* [comment removed for export] *)
  assert (PXsM1 : PIXat M1 pixs (hdv w h 8 cm data)) by exact (exT_pix_livk A0 m0 M1 pixs _ PXs (proj2 (POSTM_trans _ _ _ _ _ _ PM1 PMs1)) Lpixs_a0).
  assert (PXdM1 : PIXat M1 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_sess C A1 m1 M1 _ s 256 pixd _ CK HW1 GLO1 Lpixd_a1 PXd1 FRs1).
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
  pose (BS2 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2)]).
  exW_regfactB BS2 HR ex_r10 Q10_2. exW_regfactB BS2 HR ex_r11 Q11_2. exW_regfactB BS2 HR ex_r1 Q1_2. exW_regfactB BS2 HR ex_r2 Q2_2.
  clear BS2.
  lazymatch type of Q2_2 with _ = Z_to_bv 64 (s + ?off) => pose (OFF2 := off) end.
  (* [comment removed for export] *)
  assert (PXsM2 : PIXat M2 pixs (hdv w h 8 cm data)) by exact (exT_pix_livk A0 m0 M2 pixs _ PXs (proj2 (POSTM_trans _ _ _ _ _ _ PM2 PMs2)) Lpixs_a0).
  assert (PXdM2 : PIXat M2 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_sess C A1 m2 M2 _ s 256 pixd _ CK HW2 GLO1 Lpixd_a1 PXd2 FRs2).
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
  pose (BS3 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2)]).
  exW_regfactB BS3 HR ex_r10 Q10_3. exW_regfactB BS3 HR ex_r11 Q11_3. exW_regfactB BS3 HR ex_r1 Q1_3. exW_regfactB BS3 HR ex_r2 Q2_3. exW_regfactB BS3 HR ex_r4 Q4_3.
  clear BS3.
  lazymatch type of Q2_3 with _ = Z_to_bv 64 (s + ?off) => pose (OFF3 := off) end.
  (* [comment removed for export] *)
  assert (PXsM3 : PIXat M3 pixs (hdv w h 8 cm data)) by exact (exT_pix_livk A0 m0 M3 pixs _ PXs (proj2 (POSTM_trans _ _ _ _ _ _ PM3 PMs3)) Lpixs_a0).
  assert (PXdM3 : PIXat M3 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_sess C A1 m3 M3 _ s 256 pixd _ CK HW3 GLO1 Lpixd_a1 PXd3 FRs3).
  assert (CMF3 : cm_facts A1 M3 cm cv) by exact (cmf_keep _ A0 A1 m0 M3 cm cv CMF SUB1 (proj2 (POSTM_trans _ _ _ _ _ _ PM3 PMs3))).
  assert (PMB : POSTM C A0 s m0 M3) by exact (POSTM_trans _ _ _ _ _ _ PM3 PMs3).
  lazymatch type of Q1_3 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (HRMC fxk C A1 M3 _ Rc3 (s + OFF3)%Z pixs w h cm data cv (Z_to_bv 64 ra) S FZ CK HWs3 Q2_3
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF3, RMC_STACK, LSF; lia) ltac:(unfold OFF3; lia) Q1_3 ltac:(red; apply bv_eq; reflexivity) Q4_3 Q10_3 Q11_3
             PXsM3 HOK Hw1 Hh1 Lpixs_a1 F0pixs Ldata_a1 CMF3 (kR - RK_pix)%Z (bR - RB_pix14)%Z
             ltac:(rewrite with_vmmaps_vmmaps; exact RM1) ltac:(clear - HkR'; lia) ltac:(clear - HbR' RBpos; lia)) end end.
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
    assert (PXd4 : PIXat m4 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_patch C A1 A1 M3 m4 _ pixd pixs 64 (pixs + 20) (Z_to_le_bytes 4 2) _ CK HWs3 Lpixd_a1 Lpixs_a1 NE_pixd_pixs RRpixs ltac:(lia) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) PXdM3 (proj2 PMc3) Lpixd_a1).
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
  pose (BS4 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, data); (173%nat, wpl_of w 8)]).
  exW_regfactB BS4 HR ex_r10 Q10_4. exW_regfactB BS4 HR ex_r11 Q11_4. exW_regfactB BS4 HR ex_r1 Q1_4. exW_regfactB BS4 HR ex_r2 Q2_4. exW_regfactB BS4 HR ex_r4 Q4_4.
  clear BS4.
  lazymatch type of Q2_4 with _ = Z_to_bv 64 (s + ?off) => pose (OFF4 := off) end.
  (* [comment removed for export] *)
  assert (PXdM4 : PIXat M4 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_sess C A2 m4 M4 _ s 256 pixd _ CK HW4 GLO1 Lpixd_a2 PXd4 FRs4).
  assert (PXtM4 : PIXat M4 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_sess C A2 m4 M4 _ s 256 pixs _ CK HW4 GLO1 Lpixs_a2 PXt4 FRs4).
  lazymatch type of Q1_4 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_4 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A2 M4 _ Rc4 (wpl_of w 8) 4 (kR - RK_pix - RK_rmc) (bR - RB_pix14 - RB_rmc) (Z_to_bv 64 ret) sp' S CK HWs4 Q10_4 Q11_4 ltac:(clear - Gwpls; lia) ltac:(lia) ltac:(clear - Gwpls; lia)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM2) ltac:(clear - HkR'; unfold RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB MG17 RBpos; lia) ltac:(unfold ROOM_NMAX; clear - Gwpls; lia) Q1_4
             ltac:(red; apply bv_eq; reflexivity) Q4_4 Q2_4 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF4, CALLOC_STACK, ALLOC_STACK; clear - Hlo1; lia) ltac:(unfold OFF4; clear - Hhi; lia)) end end end.
  intros A3 m5 vm3 r5 res4 HW5 Hres4 CSx4 Hnz4 Fbufs1x Lo4 F0bufs1 LEQ4 ZERO4 ALbufs1 TOP4 PMc4 RM3.
  pose proof CSx4 as CS4. clear CSx4.
  rewrite with_vmmaps_twice in HW5 |- *.
  assert (Eres4 : res4 = Z_to_bv 64 (u res4)) by (symmetry; apply zbv_self).
  pose proof (u64_range res4) as RRbufs1. set (bufs1 := u res4) in *. clearbody bufs1. rewrite Eres4 in Hres4, Fbufs1x, Lo4, F0bufs1, LEQ4, ZERO4. clear Eres4 TOP4 Hnz4.
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
  assert (PXd5 : PIXat m5 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_livk A2 M4 m5 pixd _ PXdM4 (proj2 PMc4) Lpixd_a2).
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
  clear HR HK Hlf Hms HKc4 HKk4 KEPT4 HC4 HWs4 PMs4 Q10_4 Q11_4 Q1_4 Q2_4 Q4_4 PM4 HW4 FRs4 PMc4 CS4 SUB2 RM2 LEQ4 Fbufs1x Lo4 OFF4 LDEL2 Hres4 ZERO4 Lpixs_a2 Ldata_a2 Lpixd_a2 Ldatad_a2 PXdM4 PXd4 PXtM4 PXt4.
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
  pose (BS5 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, data); (173%nat, wpl_of w 8); (207%nat, bufs1)]).
  exW_regfactB BS5 HR ex_r10 Q10_5. exW_regfactB BS5 HR ex_r11 Q11_5. exW_regfactB BS5 HR ex_r1 Q1_5. exW_regfactB BS5 HR ex_r2 Q2_5. exW_regfactB BS5 HR ex_r4 Q4_5.
  clear BS5.
  lazymatch type of Q2_5 with _ = Z_to_bv 64 (s + ?off) => pose (OFF5 := off) end.
  (* [comment removed for export] *)
  assert (PXdM5 : PIXat M5 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_sess C A3 m5 M5 _ s 256 pixd _ CK HW5 GLO1 Lpixd_a3 PXd5 FRs5).
  assert (PXtM5 : PIXat M5 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_sess C A3 m5 M5 _ s 256 pixs _ CK HW5 GLO1 Lpixs_a3 PXt5 FRs5).
  lazymatch type of Q1_5 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_5 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A3 M5 _ Rc5 (wpl_of w 8) 4 (kR - RK_pix - RK_rmc - 1) (bR - RB_pix14 - RB_rmc - alloc_margin (wpl_of w 8 * 4)) (Z_to_bv 64 ret) sp' S CK HWs5 Q10_5 Q11_5 ltac:(clear - Gwpls; lia) ltac:(lia) ltac:(clear - Gwpls; lia)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM3) ltac:(clear - HkR'; unfold RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB MG17 RBpos; lia) ltac:(unfold ROOM_NMAX; clear - Gwpls; lia) Q1_5
             ltac:(red; apply bv_eq; reflexivity) Q4_5 Q2_5 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF5, CALLOC_STACK, ALLOC_STACK; clear - Hlo1; lia) ltac:(unfold OFF5; clear - Hhi; lia)) end end end.
  intros A4 m6 vm4 r6 res5 HW6 Hres5 CSx5 Hnz5 Fbufs2x Lo5 F0bufs2 LEQ5 ZERO5 ALbufs2 TOP5 PMc5 RM4.
  pose proof CSx5 as CS5. clear CSx5.
  rewrite with_vmmaps_twice in HW6 |- *.
  assert (Eres5 : res5 = Z_to_bv 64 (u res5)) by (symmetry; apply zbv_self).
  pose proof (u64_range res5) as RRbufs2. set (bufs2 := u res5) in *. clearbody bufs2. rewrite Eres5 in Hres5, Fbufs2x, Lo5, F0bufs2, LEQ5, ZERO5. clear Eres5 TOP5 Hnz5.
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
  assert (PXd6 : PIXat m6 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_livk A3 M5 m6 pixd _ PXdM5 (proj2 PMc5) Lpixd_a3).
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
  clear HR HK Hlf Hms HKc5 HKk5 KEPT5 HC5 HWs5 PMs5 Q10_5 Q11_5 Q1_5 Q2_5 Q4_5 PM5 HW5 FRs5 PMc5 CS5 SUB3 RM3 LEQ5 Fbufs2x Lo5 OFF5 LDEL3 Hres5 ZERO5 Lpixs_a3 Ldata_a3 Lpixd_a3 Ldatad_a3 Lbufs1_a3 PXdM5 PXd5 PXtM5 PXt5.
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
  pose (BS6 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, data); (173%nat, wpl_of w 8); (207%nat, bufs1); (241%nat, bufs2)]).
  exW_regfactB BS6 HR ex_r10 Q10_6. exW_regfactB BS6 HR ex_r11 Q11_6. exW_regfactB BS6 HR ex_r1 Q1_6. exW_regfactB BS6 HR ex_r2 Q2_6. exW_regfactB BS6 HR ex_r4 Q4_6.
  clear BS6.
  lazymatch type of Q2_6 with _ = Z_to_bv 64 (s + ?off) => pose (OFF6 := off) end.
  (* [comment removed for export] *)
  assert (PXdM6 : PIXat M6 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_sess C A4 m6 M6 _ s 256 pixd _ CK HW6 GLO1 Lpixd_a4 PXd6 FRs6).
  assert (PXtM6 : PIXat M6 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_sess C A4 m6 M6 _ s 256 pixs _ CK HW6 GLO1 Lpixs_a4 PXt6 FRs6).
  lazymatch type of Q1_6 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_6 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A4 M6 _ Rc6 (256) 4 (kR - RK_pix - RK_rmc - 1 - 1) (bR - RB_pix14 - RB_rmc - alloc_margin (wpl_of w 8 * 4) - alloc_margin (wpl_of w 8 * 4)) (Z_to_bv 64 ret) sp' S CK HWs6 Q10_6 Q11_6 ltac:(lia) ltac:(lia) ltac:(lia)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM4) ltac:(clear - HkR'; unfold RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB MG17 RBpos; lia) ltac:(unfold ROOM_NMAX; lia) Q1_6
             ltac:(red; apply bv_eq; reflexivity) Q4_6 Q2_6 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF6, CALLOC_STACK, ALLOC_STACK; clear - Hlo1; lia) ltac:(unfold OFF6; clear - Hhi; lia)) end end end.
  intros A5 m7 vm5 r7 res6 HW7 Hres6 CSx6 Hnz6 Ftabvalx Lo6 F0tabval LEQ6 ZERO6 ALtabval TOP6 PMc6 RM5.
  pose proof CSx6 as CS6. clear CSx6.
  rewrite with_vmmaps_twice in HW7 |- *.
  assert (Eres6 : res6 = Z_to_bv 64 (u res6)) by (symmetry; apply zbv_self).
  pose proof (u64_range res6) as RRtabval. set (tabval := u res6) in *. clearbody tabval. rewrite Eres6 in Hres6, Ftabvalx, Lo6, F0tabval, LEQ6, ZERO6. clear Eres6 TOP6 Hnz6.
  change (256 * 4)%Z with 1024%Z in Lo6, ZERO6.
  assert (Gtabval : (4096 <= tabval)%Z /\ (tabval + 1024 <= alloc_top (c_vm C))%Z).
  { destruct (blk_range C A5 m7 _ (Z_to_bv 64 tabval) (1024) CK HW7 Lo6 ltac:(lia)) as [G1 G2]. rewrite u_Z2bv in G1, G2 by (clear - RRtabval; lia). split; assumption. }
  pose proof (fresh_sub A0 A4 _ SUB4 Ftabvalx) as Ftabval.
  pose proof Lo6 as Ltabval_a5.
  assert (SUB5 : sub_live A0 A5).
  { intros q0 kq Lq. rewrite (LEQ6 q0 (ne_live A0 q0 _ kq Lq Ftabval)). exact (SUB4 q0 kq Lq). }
  pose proof (fun (q0 : word) (Hq : ~ In q0 (Z_to_bv 64 tabval :: [Z_to_bv 64 bufs2; Z_to_bv 64 bufs1; Z_to_bv 64 pixd; Z_to_bv 64 datad])) => eq_trans (LEQ6 q0 (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL4 q0 (fun XX => Hq (or_intror XX)))) as LDEL5.
  pose proof (ne_live A4 _ _ _ Lpixs_a4 Ftabvalx) as NE_pixs_tabval.
  pose proof (eq_trans (LEQ6 _ NE_pixs_tabval) Lpixs_a4) as Lpixs_a5.
  pose proof (ne_live A4 _ _ _ Ldata_a4 Ftabvalx) as NE_data_tabval.
  pose proof (eq_trans (LEQ6 _ NE_data_tabval) Ldata_a4) as Ldata_a5.
  pose proof (ne_live A4 _ _ _ Lpixd_a4 Ftabvalx) as NE_pixd_tabval.
  pose proof (eq_trans (LEQ6 _ NE_pixd_tabval) Lpixd_a4) as Lpixd_a5.
  pose proof (ne_live A4 _ _ _ Ldatad_a4 Ftabvalx) as NE_datad_tabval.
  pose proof (eq_trans (LEQ6 _ NE_datad_tabval) Ldatad_a4) as Ldatad_a5.
  pose proof (ne_live A4 _ _ _ Lbufs1_a4 Ftabvalx) as NE_bufs1_tabval.
  pose proof (eq_trans (LEQ6 _ NE_bufs1_tabval) Lbufs1_a4) as Lbufs1_a5.
  pose proof (ne_live A4 _ _ _ Lbufs2_a4 Ftabvalx) as NE_bufs2_tabval.
  pose proof (eq_trans (LEQ6 _ NE_bufs2_tabval) Lbufs2_a4) as Lbufs2_a5.
  assert (PXd7 : PIXat m7 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_livk A4 M6 m7 pixd _ PXdM6 (proj2 PMc6) Lpixd_a4).
  assert (PXt7 : PIXat m7 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_livk A4 M6 m7 pixs _ PXtM6 (proj2 PMc6) Lpixs_a4).
  assert (PM7 : POSTM C A0 s m4 m7).
  { eapply POSTM_trans; [exact PM6|]. eapply POSTM_trans; [exact PMs6|]. apply (POSTM_sub C A0 A4 _ _ _ SUB4). apply (POSTM_mono C A4 (s + OFF6) s); [unfold OFF6; lia | exact PMc6]. }
  assert (KEPT6 : Forall (ex_region_kept E6 M6 m7) [(EVar 32, OFF6, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF6 256 M6 m7 E6 (EVar 32) CK (proj1 PMc6) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E6 M6 m7 _ [] _ HKc6 KEPT6) as HKk6.
  match type of HKk6 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E6 m7 kk') in HKk6 end.
  pose proof (regs_ok_agree 243%nat E6 (ex_envL vals6 r7 [tabval; exW_canary SEGS 415784 m7]) _ _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa6.
  pose proof (exW_regs_call _ _ _ _ _ HRa6 (ex_regs_ok_junk vals6 r7 [tabval; exW_canary SEGS 415784 m7] 243%nat ltac:(vm_cast_no_check (eq_refl 243%nat))) CS6) as HRn7.
  clear HRa6.
  assert (HKa7 : know_ok SEGS (ex_envL vals6 r7 [tabval; exW_canary SEGS 415784 m7]) m7 _) by (exact (know_ok_agree SEGS 243%nat E6 _ m7 _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk6)).
  rewrite (fr_denot_agree 243%nat E6 (ex_envL vals6 r7 [tabval; exW_canary SEGS 415784 m7]) _ fr2 (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r7 ex_r10 (EVar 275) HRn7 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres6)) as HRx7. clear HRn7. rename HRx7 into HRn7.
  clear HR HK Hlf Hms HKc6 HKk6 KEPT6 HC6 HWs6 PMs6 Q10_6 Q11_6 Q1_6 Q2_6 Q4_6 PM6 HW6 FRs6 PMc6 CS6 SUB4 RM4 LEQ6 Ftabvalx Lo6 OFF6 LDEL4 Hres6 ZERO6 Lpixs_a4 Ldata_a4 Lpixd_a4 Ldatad_a4 Lbufs1_a4 Lbufs2_a4 PXdM6 PXd6 PXtM6 PXt6.
  subst M6. clear log6. clear E6. try clear Rc6. clear KN6.
  lazymatch type of HRn7 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn7 end.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [tabval; exW_canary SEGS 415784 m7]) m7) _ _ (ex_krange SEGS (ex_envL vals6 r7 [tabval; exW_canary SEGS 415784 m7]) m7 (EVar 275) tabval 4096 (2 ^ 47) eq_refl RRtabval ltac:(clear - Gtabval T1 T2 T3 LV Rnb; lia)) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals6 r7 [tabval; exW_canary SEGS 415784 m7]) m7))) as HKb7.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A5 m7 _ (s - 256) (Z.to_nat 256) CK HW7 GLO1 GLO2) as SOK7.
  pose proof (exW_canary_ok SEGS 415784 m7 (canary_any m7)) as CANOK7.
  pose (vals7 := vals6 ++ map (getr r7) ex_regs_list ++ map (Z_to_bv 64) [tabval; exW_canary SEGS 415784 m7]).
  pose proof (exW_kn_fixed SEGS C A5 m7 _ (ex_envL vals6 r7 [tabval; exW_canary SEGS 415784 m7]) (EVar 276) (EVar 32) (exW_canary SEGS 415784 m7) s 256 415784 65536 212992 213416 213568 213416 213568
                HW7 eq_refl (proj1 CANOK7) (proj2 CANOK7) eq_refl eq_refl eq_refl SOK7 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf7.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb7 (proj2 (Forall_app _ _ _) (conj HKf7 HKa7)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn7 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN7 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb7 HKf7 HKa7 SOK7 CANOK7.
  repeat match goal with H : getr r7 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc7 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E7 := EEx) in HR, Hlf, HK, Hms |- *; set (log7 := LLx) in Hms, Hlf; set (M7 := mem_denot E7 m7 log7) in Hms end.
  assert (WP7 : W C A5 M7 (with_vmmaps vm5 md) /\ POSTM C A0 s m7 M7).
  { subst M7. apply (exW_win_blks C A5 A0 m7 _ E7 log7 (EVar 32) s 256 [] CK HW7 SUB5 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP7 as [HWs7 PMs7].
  pose proof (exW_win_only E7 m7 log7 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs7. change (mem_denot E7 m7 log7) with M7 in FRs7.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log7 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC7 : carry log7 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc7 : know_ok SEGS E7 M7 kn1) by (apply (carry_after SEGS E7 m7 log7 kn0 [] kn1 scs hs HC7 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact Hms |].
  pose (BS7 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, data); (173%nat, wpl_of w 8); (207%nat, bufs1); (241%nat, bufs2); (275%nat, tabval)]).
  exW_regfactB BS7 HR ex_r10 Q10_7. exW_regfactB BS7 HR ex_r11 Q11_7. exW_regfactB BS7 HR ex_r1 Q1_7. exW_regfactB BS7 HR ex_r2 Q2_7. exW_regfactB BS7 HR ex_r4 Q4_7.
  clear BS7.
  lazymatch type of Q2_7 with _ = Z_to_bv 64 (s + ?off) => pose (OFF7 := off) end.
  (* [comment removed for export] *)
  assert (PXdM7 : PIXat M7 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_sess C A5 m7 M7 _ s 256 pixd _ CK HW7 GLO1 Lpixd_a5 PXd7 FRs7).
  assert (PXtM7 : PIXat M7 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_sess C A5 m7 M7 _ s 256 pixs _ CK HW7 GLO1 Lpixs_a5 PXt7 FRs7).
  lazymatch type of Q1_7 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_7 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A5 M7 _ Rc7 (256) 4 (kR - RK_pix - RK_rmc - 1 - 1 - 1) (bR - RB_pix14 - RB_rmc - alloc_margin (wpl_of w 8 * 4) - alloc_margin (wpl_of w 8 * 4) - alloc_margin (256 * 4)) (Z_to_bv 64 ret) sp' S CK HWs7 Q10_7 Q11_7 ltac:(lia) ltac:(lia) ltac:(lia)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM5) ltac:(clear - HkR'; unfold RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB MG17 RBpos; lia) ltac:(unfold ROOM_NMAX; lia) Q1_7
             ltac:(red; apply bv_eq; reflexivity) Q4_7 Q2_7 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF7, CALLOC_STACK, ALLOC_STACK; clear - Hlo1; lia) ltac:(unfold OFF7; clear - Hhi; lia)) end end end.
  intros A6 m8 vm6 r8 res7 HW8 Hres7 CSx7 Hnz7 Ftab38x Lo7 F0tab38 LEQ7 ZERO7 ALtab38 TOP7 PMc7 RM6.
  pose proof CSx7 as CS7. clear CSx7.
  rewrite with_vmmaps_twice in HW8 |- *.
  assert (Eres7 : res7 = Z_to_bv 64 (u res7)) by (symmetry; apply zbv_self).
  pose proof (u64_range res7) as RRtab38. set (tab38 := u res7) in *. clearbody tab38. rewrite Eres7 in Hres7, Ftab38x, Lo7, F0tab38, LEQ7, ZERO7. clear Eres7 TOP7 Hnz7.
  change (256 * 4)%Z with 1024%Z in Lo7, ZERO7.
  assert (Gtab38 : (4096 <= tab38)%Z /\ (tab38 + 1024 <= alloc_top (c_vm C))%Z).
  { destruct (blk_range C A6 m8 _ (Z_to_bv 64 tab38) (1024) CK HW8 Lo7 ltac:(lia)) as [G1 G2]. rewrite u_Z2bv in G1, G2 by (clear - RRtab38; lia). split; assumption. }
  pose proof (fresh_sub A0 A5 _ SUB5 Ftab38x) as Ftab38.
  pose proof Lo7 as Ltab38_a6.
  assert (SUB6 : sub_live A0 A6).
  { intros q0 kq Lq. rewrite (LEQ7 q0 (ne_live A0 q0 _ kq Lq Ftab38)). exact (SUB5 q0 kq Lq). }
  pose proof (fun (q0 : word) (Hq : ~ In q0 (Z_to_bv 64 tab38 :: [Z_to_bv 64 tabval; Z_to_bv 64 bufs2; Z_to_bv 64 bufs1; Z_to_bv 64 pixd; Z_to_bv 64 datad])) => eq_trans (LEQ7 q0 (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL5 q0 (fun XX => Hq (or_intror XX)))) as LDEL6.
  pose proof (ne_live A5 _ _ _ Lpixs_a5 Ftab38x) as NE_pixs_tab38.
  pose proof (eq_trans (LEQ7 _ NE_pixs_tab38) Lpixs_a5) as Lpixs_a6.
  pose proof (ne_live A5 _ _ _ Ldata_a5 Ftab38x) as NE_data_tab38.
  pose proof (eq_trans (LEQ7 _ NE_data_tab38) Ldata_a5) as Ldata_a6.
  pose proof (ne_live A5 _ _ _ Lpixd_a5 Ftab38x) as NE_pixd_tab38.
  pose proof (eq_trans (LEQ7 _ NE_pixd_tab38) Lpixd_a5) as Lpixd_a6.
  pose proof (ne_live A5 _ _ _ Ldatad_a5 Ftab38x) as NE_datad_tab38.
  pose proof (eq_trans (LEQ7 _ NE_datad_tab38) Ldatad_a5) as Ldatad_a6.
  pose proof (ne_live A5 _ _ _ Lbufs1_a5 Ftab38x) as NE_bufs1_tab38.
  pose proof (eq_trans (LEQ7 _ NE_bufs1_tab38) Lbufs1_a5) as Lbufs1_a6.
  pose proof (ne_live A5 _ _ _ Lbufs2_a5 Ftab38x) as NE_bufs2_tab38.
  pose proof (eq_trans (LEQ7 _ NE_bufs2_tab38) Lbufs2_a5) as Lbufs2_a6.
  pose proof (ne_live A5 _ _ _ Ltabval_a5 Ftab38x) as NE_tabval_tab38.
  pose proof (eq_trans (LEQ7 _ NE_tabval_tab38) Ltabval_a5) as Ltabval_a6.
  assert (PXd8 : PIXat m8 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_livk A5 M7 m8 pixd _ PXdM7 (proj2 PMc7) Lpixd_a5).
  assert (PXt8 : PIXat m8 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_livk A5 M7 m8 pixs _ PXtM7 (proj2 PMc7) Lpixs_a5).
  pose proof ZERO7 as Ztab38_8.
  assert (PM8 : POSTM C A0 s m4 m8).
  { eapply POSTM_trans; [exact PM7|]. eapply POSTM_trans; [exact PMs7|]. apply (POSTM_sub C A0 A5 _ _ _ SUB5). apply (POSTM_mono C A5 (s + OFF7) s); [unfold OFF7; lia | exact PMc7]. }
  assert (KEPT7 : Forall (ex_region_kept E7 M7 m8) [(EVar 32, OFF7, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF7 256 M7 m8 E7 (EVar 32) CK (proj1 PMc7) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E7 M7 m8 _ [] _ HKc7 KEPT7) as HKk7.
  match type of HKk7 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E7 m8 kk') in HKk7 end.
  pose proof (regs_ok_agree 277%nat E7 (ex_envL vals7 r8 [tab38; exW_canary SEGS 415784 m8]) _ _ (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa7.
  pose proof (exW_regs_call _ _ _ _ _ HRa7 (ex_regs_ok_junk vals7 r8 [tab38; exW_canary SEGS 415784 m8] 277%nat ltac:(vm_cast_no_check (eq_refl 277%nat))) CS7) as HRn8.
  clear HRa7.
  assert (HKa8 : know_ok SEGS (ex_envL vals7 r8 [tab38; exW_canary SEGS 415784 m8]) m8 _) by (exact (know_ok_agree SEGS 277%nat E7 _ m8 _ (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk7)).
  rewrite (fr_denot_agree 277%nat E7 (ex_envL vals7 r8 [tab38; exW_canary SEGS 415784 m8]) _ fr2 (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r8 ex_r10 (EVar 309) HRn8 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres7)) as HRx8. clear HRn8. rename HRx8 into HRn8.
  clear HR HK Hlf Hms HKc7 HKk7 KEPT7 HC7 HWs7 PMs7 Q10_7 Q11_7 Q1_7 Q2_7 Q4_7 PM7 HW7 FRs7 PMc7 CS7 SUB5 RM5 LEQ7 Ftab38x Lo7 OFF7 LDEL5 Hres7 ZERO7 Lpixs_a5 Ldata_a5 Lpixd_a5 Ldatad_a5 Lbufs1_a5 Lbufs2_a5 Ltabval_a5 PXdM7 PXd7 PXtM7 PXt7.
  subst M7. clear log7. clear E7. try clear Rc7. clear KN7.
  lazymatch type of HRn8 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn8 end.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals7 r8 [tab38; exW_canary SEGS 415784 m8]) m8) _ _ (ex_krange SEGS (ex_envL vals7 r8 [tab38; exW_canary SEGS 415784 m8]) m8 (EVar 309) tab38 4096 (2 ^ 47) eq_refl RRtab38 ltac:(clear - Gtab38 T1 T2 T3 LV Rnb; lia)) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals7 r8 [tab38; exW_canary SEGS 415784 m8]) m8))) as HKb8.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A6 m8 _ (s - 256) (Z.to_nat 256) CK HW8 GLO1 GLO2) as SOK8.
  pose proof (exW_canary_ok SEGS 415784 m8 (canary_any m8)) as CANOK8.
  pose (vals8 := vals7 ++ map (getr r8) ex_regs_list ++ map (Z_to_bv 64) [tab38; exW_canary SEGS 415784 m8]).
  pose proof (exW_kn_fixed SEGS C A6 m8 _ (ex_envL vals7 r8 [tab38; exW_canary SEGS 415784 m8]) (EVar 310) (EVar 32) (exW_canary SEGS 415784 m8) s 256 415784 65536 212992 213416 213568 213416 213568
                HW8 eq_refl (proj1 CANOK8) (proj2 CANOK8) eq_refl eq_refl eq_refl SOK8 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf8.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb8 (proj2 (Forall_app _ _ _) (conj HKf8 HKa8)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn8 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN8 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb8 HKf8 HKa8 SOK8 CANOK8.
  repeat match goal with H : getr r8 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc8 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E8 := EEx) in HR, Hlf, HK, Hms |- *; set (log8 := LLx) in Hms, Hlf; set (M8 := mem_denot E8 m8 log8) in Hms end.
  assert (WP8 : W C A6 M8 (with_vmmaps vm6 md) /\ POSTM C A0 s m8 M8).
  { subst M8. apply (exW_win_blks C A6 A0 m8 _ E8 log8 (EVar 32) s 256 [] CK HW8 SUB6 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP8 as [HWs8 PMs8].
  pose proof (exW_win_only E8 m8 log8 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs8. change (mem_denot E8 m8 log8) with M8 in FRs8.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log8 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC8 : carry log8 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc8 : know_ok SEGS E8 M8 kn1) by (apply (carry_after SEGS E8 m8 log8 kn0 [] kn1 scs hs HC8 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW8)) | exact (mp_lazy _ (w_pure _ _ _ _ HW8)) | exact Hms |].
  pose (BS8 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, data); (173%nat, wpl_of w 8); (207%nat, bufs1); (241%nat, bufs2); (275%nat, tabval); (309%nat, tab38)]).
  exW_regfactB BS8 HR ex_r10 Q10_8. exW_regfactB BS8 HR ex_r11 Q11_8. exW_regfactB BS8 HR ex_r1 Q1_8. exW_regfactB BS8 HR ex_r2 Q2_8. exW_regfactB BS8 HR ex_r4 Q4_8.
  clear BS8.
  lazymatch type of Q2_8 with _ = Z_to_bv 64 (s + ?off) => pose (OFF8 := off) end.
  (* [comment removed for export] *)
  assert (PXdM8 : PIXat M8 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_sess C A6 m8 M8 _ s 256 pixd _ CK HW8 GLO1 Lpixd_a6 PXd8 FRs8).
  assert (PXtM8 : PIXat M8 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_sess C A6 m8 M8 _ s 256 pixs _ CK HW8 GLO1 Lpixs_a6 PXt8 FRs8).
  pose proof (exT_livk_sess C A6 m8 M8 _ s 256 CK HW8 GLO1 FRs8) as LKs8.
  pose proof (zero_livk A6 m8 M8 _ _ LKs8 Ltab38_a6 Ztab38_8) as Ztab38M8.
  lazymatch type of Q1_8 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_8 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A6 M8 _ Rc8 (256) 4 (kR - RK_pix - RK_rmc - 1 - 1 - 1 - 1) (bR - RB_pix14 - RB_rmc - alloc_margin (wpl_of w 8 * 4) - alloc_margin (wpl_of w 8 * 4) - alloc_margin (256 * 4) - alloc_margin (256 * 4)) (Z_to_bv 64 ret) sp' S CK HWs8 Q10_8 Q11_8 ltac:(lia) ltac:(lia) ltac:(lia)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM6) ltac:(clear - HkR'; unfold RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB MG17 RBpos; lia) ltac:(unfold ROOM_NMAX; lia) Q1_8
             ltac:(red; apply bv_eq; reflexivity) Q4_8 Q2_8 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF8, CALLOC_STACK, ALLOC_STACK; clear - Hlo1; lia) ltac:(unfold OFF8; clear - Hhi; lia)) end end end.
  intros A7 m9 vm7 r9 res8 HW9 Hres8 CSx8 Hnz8 Ftab14x Lo8 F0tab14 LEQ8 ZERO8 ALtab14 TOP8 PMc8 RM7.
  pose proof CSx8 as CS8. clear CSx8.
  rewrite with_vmmaps_twice in HW9 |- *.
  assert (Eres8 : res8 = Z_to_bv 64 (u res8)) by (symmetry; apply zbv_self).
  pose proof (u64_range res8) as RRtab14. set (tab14 := u res8) in *. clearbody tab14. rewrite Eres8 in Hres8, Ftab14x, Lo8, F0tab14, LEQ8, ZERO8. clear Eres8 TOP8 Hnz8.
  change (256 * 4)%Z with 1024%Z in Lo8, ZERO8.
  assert (Gtab14 : (4096 <= tab14)%Z /\ (tab14 + 1024 <= alloc_top (c_vm C))%Z).
  { destruct (blk_range C A7 m9 _ (Z_to_bv 64 tab14) (1024) CK HW9 Lo8 ltac:(lia)) as [G1 G2]. rewrite u_Z2bv in G1, G2 by (clear - RRtab14; lia). split; assumption. }
  pose proof (fresh_sub A0 A6 _ SUB6 Ftab14x) as Ftab14.
  pose proof Lo8 as Ltab14_a7.
  assert (SUB7 : sub_live A0 A7).
  { intros q0 kq Lq. rewrite (LEQ8 q0 (ne_live A0 q0 _ kq Lq Ftab14)). exact (SUB6 q0 kq Lq). }
  pose proof (fun (q0 : word) (Hq : ~ In q0 (Z_to_bv 64 tab14 :: [Z_to_bv 64 tab38; Z_to_bv 64 tabval; Z_to_bv 64 bufs2; Z_to_bv 64 bufs1; Z_to_bv 64 pixd; Z_to_bv 64 datad])) => eq_trans (LEQ8 q0 (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL6 q0 (fun XX => Hq (or_intror XX)))) as LDEL7.
  pose proof (ne_live A6 _ _ _ Lpixs_a6 Ftab14x) as NE_pixs_tab14.
  pose proof (eq_trans (LEQ8 _ NE_pixs_tab14) Lpixs_a6) as Lpixs_a7.
  pose proof (ne_live A6 _ _ _ Ldata_a6 Ftab14x) as NE_data_tab14.
  pose proof (eq_trans (LEQ8 _ NE_data_tab14) Ldata_a6) as Ldata_a7.
  pose proof (ne_live A6 _ _ _ Lpixd_a6 Ftab14x) as NE_pixd_tab14.
  pose proof (eq_trans (LEQ8 _ NE_pixd_tab14) Lpixd_a6) as Lpixd_a7.
  pose proof (ne_live A6 _ _ _ Ldatad_a6 Ftab14x) as NE_datad_tab14.
  pose proof (eq_trans (LEQ8 _ NE_datad_tab14) Ldatad_a6) as Ldatad_a7.
  pose proof (ne_live A6 _ _ _ Lbufs1_a6 Ftab14x) as NE_bufs1_tab14.
  pose proof (eq_trans (LEQ8 _ NE_bufs1_tab14) Lbufs1_a6) as Lbufs1_a7.
  pose proof (ne_live A6 _ _ _ Lbufs2_a6 Ftab14x) as NE_bufs2_tab14.
  pose proof (eq_trans (LEQ8 _ NE_bufs2_tab14) Lbufs2_a6) as Lbufs2_a7.
  pose proof (ne_live A6 _ _ _ Ltabval_a6 Ftab14x) as NE_tabval_tab14.
  pose proof (eq_trans (LEQ8 _ NE_tabval_tab14) Ltabval_a6) as Ltabval_a7.
  pose proof (ne_live A6 _ _ _ Ltab38_a6 Ftab14x) as NE_tab38_tab14.
  pose proof (eq_trans (LEQ8 _ NE_tab38_tab14) Ltab38_a6) as Ltab38_a7.
  assert (PXd9 : PIXat m9 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_livk A6 M8 m9 pixd _ PXdM8 (proj2 PMc8) Lpixd_a6).
  assert (PXt9 : PIXat m9 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_livk A6 M8 m9 pixs _ PXtM8 (proj2 PMc8) Lpixs_a6).
  pose proof (zero_livk A6 M8 m9 _ _ (proj2 PMc8) Ltab38_a6 Ztab38M8) as Ztab38_9.
  pose proof ZERO8 as Ztab14_9.
  assert (PM9 : POSTM C A0 s m4 m9).
  { eapply POSTM_trans; [exact PM8|]. eapply POSTM_trans; [exact PMs8|]. apply (POSTM_sub C A0 A6 _ _ _ SUB6). apply (POSTM_mono C A6 (s + OFF8) s); [unfold OFF8; lia | exact PMc8]. }
  assert (KEPT8 : Forall (ex_region_kept E8 M8 m9) [(EVar 32, OFF8, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF8 256 M8 m9 E8 (EVar 32) CK (proj1 PMc8) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E8 M8 m9 _ [] _ HKc8 KEPT8) as HKk8.
  match type of HKk8 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E8 m9 kk') in HKk8 end.
  pose proof (regs_ok_agree 311%nat E8 (ex_envL vals8 r9 [tab14; exW_canary SEGS 415784 m9]) _ _ (vals_app_agree vals8 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa8.
  pose proof (exW_regs_call _ _ _ _ _ HRa8 (ex_regs_ok_junk vals8 r9 [tab14; exW_canary SEGS 415784 m9] 311%nat ltac:(vm_cast_no_check (eq_refl 311%nat))) CS8) as HRn9.
  clear HRa8.
  assert (HKa9 : know_ok SEGS (ex_envL vals8 r9 [tab14; exW_canary SEGS 415784 m9]) m9 _) by (exact (know_ok_agree SEGS 311%nat E8 _ m9 _ (vals_app_agree vals8 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk8)).
  rewrite (fr_denot_agree 311%nat E8 (ex_envL vals8 r9 [tab14; exW_canary SEGS 415784 m9]) _ fr2 (vals_app_agree vals8 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r9 ex_r10 (EVar 343) HRn9 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres8)) as HRx9. clear HRn9. rename HRx9 into HRn9.
  clear HR HK Hlf Hms HKc8 HKk8 KEPT8 HC8 HWs8 PMs8 Q10_8 Q11_8 Q1_8 Q2_8 Q4_8 PM8 HW8 FRs8 PMc8 CS8 SUB6 RM6 LEQ8 Ftab14x Lo8 OFF8 LDEL6 Hres8 ZERO8 Lpixs_a6 Ldata_a6 Lpixd_a6 Ldatad_a6 Lbufs1_a6 Lbufs2_a6 Ltabval_a6 Ltab38_a6 PXdM8 PXd8 PXtM8 PXt8 Ztab38M8 Ztab38_8 LKs8.
  subst M8. clear log8. clear E8. try clear Rc8. clear KN8.
  lazymatch type of HRn9 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn9 end.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals8 r9 [tab14; exW_canary SEGS 415784 m9]) m9) _ _ (ex_krange SEGS (ex_envL vals8 r9 [tab14; exW_canary SEGS 415784 m9]) m9 (EVar 343) tab14 4096 (2 ^ 47) eq_refl RRtab14 ltac:(clear - Gtab14 T1 T2 T3 LV Rnb; lia)) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals8 r9 [tab14; exW_canary SEGS 415784 m9]) m9))) as HKb9.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A7 m9 _ (s - 256) (Z.to_nat 256) CK HW9 GLO1 GLO2) as SOK9.
  pose proof (exW_canary_ok SEGS 415784 m9 (canary_any m9)) as CANOK9.
  pose (vals9 := vals8 ++ map (getr r9) ex_regs_list ++ map (Z_to_bv 64) [tab14; exW_canary SEGS 415784 m9]).
  pose proof (exW_kn_fixed SEGS C A7 m9 _ (ex_envL vals8 r9 [tab14; exW_canary SEGS 415784 m9]) (EVar 344) (EVar 32) (exW_canary SEGS 415784 m9) s 256 415784 65536 212992 213416 213568 213416 213568
                HW9 eq_refl (proj1 CANOK9) (proj2 CANOK9) eq_refl eq_refl eq_refl SOK9 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf9.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb9 (proj2 (Forall_app _ _ _) (conj HKf9 HKa9)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn9 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN9 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb9 HKf9 HKa9 SOK9 CANOK9.
  repeat match goal with H : getr r9 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc9 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E9 := EEx) in HR, Hlf, HK, Hms |- *; set (log9 := LLx) in Hms, Hlf; set (M9 := mem_denot E9 m9 log9) in Hms end.
  assert (WP9 : W C A7 M9 (with_vmmaps vm7 md) /\ POSTM C A0 s m9 M9).
  { subst M9. apply (exW_win_blks C A7 A0 m9 _ E9 log9 (EVar 32) s 256 [] CK HW9 SUB7 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP9 as [HWs9 PMs9].
  pose proof (exW_win_only E9 m9 log9 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs9. change (mem_denot E9 m9 log9) with M9 in FRs9.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log9 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC9 : carry log9 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc9 : know_ok SEGS E9 M9 kn1) by (apply (carry_after SEGS E9 m9 log9 kn0 [] kn1 scs hs HC9 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW9)) | exact (mp_lazy _ (w_pure _ _ _ _ HW9)) | exact Hms |].
  pose (BS9 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, data); (173%nat, wpl_of w 8); (207%nat, bufs1); (241%nat, bufs2); (275%nat, tabval); (309%nat, tab38); (343%nat, tab14)]).
  exW_regfactB BS9 HR ex_r2 Q2_9. exW_regfactB BS9 HR ex_r9 Q9_9. exW_regfactB BS9 HR ex_r18 Q18_9. exW_regfactB BS9 HR ex_r20 Q20_9. exW_regfactB BS9 HR ex_r21 Q21_9. exW_regfactB BS9 HR ex_r22 Q22_9. exW_regfactB BS9 HR ex_r25 Q25_9.
  clear BS9.
  (* [comment removed for export] *)
  assert (PXdM9 : PIXat M9 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_sess C A7 m9 M9 _ s 256 pixd _ CK HW9 GLO1 Lpixd_a7 PXd9 FRs9).
  assert (PXtM9 : PIXat M9 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_sess C A7 m9 M9 _ s 256 pixs _ CK HW9 GLO1 Lpixs_a7 PXt9 FRs9).
  pose proof (exT_livk_sess C A7 m9 M9 _ s 256 CK HW9 GLO1 FRs9) as LKs9.
  pose proof (zero_livk A7 m9 M9 _ _ LKs9 Ltab38_a7 Ztab38_9) as Ztab38M9.
  pose proof (zero_livk A7 m9 M9 _ _ LKs9 Ltab14_a7 Ztab14_9) as Ztab14M9.
  pose (BSx9 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, data); (173%nat, wpl_of w 8); (207%nat, bufs1); (241%nat, bufs2); (275%nat, tabval); (309%nat, tab38); (343%nat, tab14)]).
  exW_cellB HK Hlf r0 BSx9 (EVar 32) s (-108)%Z 4%nat KC0. exW_cellB HK Hlf r0 BSx9 (EVar 32) s (-112)%Z 4%nat KC1. exW_cellB HK Hlf r0 BSx9 (EVar 32) s (-152)%Z 8%nat KC2. exW_cellB HK Hlf r0 BSx9 (EVar 32) s (-160)%Z 8%nat KC3. exW_cellB HK Hlf r0 BSx9 (EVar 32) s (-168)%Z 8%nat KC4.
  clear BSx9.
  assert (NDk : List.NoDup [Z_to_bv 64 datad; Z_to_bv 64 data; Z_to_bv 64 bufs1; Z_to_bv 64 bufs2; Z_to_bv 64 tabval; Z_to_bv 64 tab38; Z_to_bv 64 tab14]).
  { apply List.NoDup_cons; [cbn [List.In]; intros HH; repeat (destruct HH as [EE|HH]; [first [exact ((fun EE => NE_datad_data (eq_sym EE)) EE) | exact ((fun EE => NE_datad_bufs1 (eq_sym EE)) EE) | exact ((fun EE => NE_datad_bufs2 (eq_sym EE)) EE) | exact ((fun EE => NE_datad_tabval (eq_sym EE)) EE) | exact ((fun EE => NE_datad_tab38 (eq_sym EE)) EE) | exact ((fun EE => NE_datad_tab14 (eq_sym EE)) EE)]|]); exact HH|]. apply List.NoDup_cons; [cbn [List.In]; intros HH; repeat (destruct HH as [EE|HH]; [first [exact ((fun EE => NE_data_bufs1 (eq_sym EE)) EE) | exact ((fun EE => NE_data_bufs2 (eq_sym EE)) EE) | exact ((fun EE => NE_data_tabval (eq_sym EE)) EE) | exact ((fun EE => NE_data_tab38 (eq_sym EE)) EE) | exact ((fun EE => NE_data_tab14 (eq_sym EE)) EE)]|]); exact HH|]. apply List.NoDup_cons; [cbn [List.In]; intros HH; repeat (destruct HH as [EE|HH]; [first [exact ((fun EE => NE_bufs1_bufs2 (eq_sym EE)) EE) | exact ((fun EE => NE_bufs1_tabval (eq_sym EE)) EE) | exact ((fun EE => NE_bufs1_tab38 (eq_sym EE)) EE) | exact ((fun EE => NE_bufs1_tab14 (eq_sym EE)) EE)]|]); exact HH|]. apply List.NoDup_cons; [cbn [List.In]; intros HH; repeat (destruct HH as [EE|HH]; [first [exact ((fun EE => NE_bufs2_tabval (eq_sym EE)) EE) | exact ((fun EE => NE_bufs2_tab38 (eq_sym EE)) EE) | exact ((fun EE => NE_bufs2_tab14 (eq_sym EE)) EE)]|]); exact HH|]. apply List.NoDup_cons; [cbn [List.In]; intros HH; repeat (destruct HH as [EE|HH]; [first [exact ((fun EE => NE_tabval_tab38 (eq_sym EE)) EE) | exact ((fun EE => NE_tabval_tab14 (eq_sym EE)) EE)]|]); exact HH|]. apply List.NoDup_cons; [cbn [List.In]; intros HH; repeat (destruct HH as [EE|HH]; [first [exact ((fun EE => NE_tab38_tab14 (eq_sym EE)) EE)]|]); exact HH|]. apply List.NoDup_cons; [intros []|]. apply List.NoDup_nil. }
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (d2k_hop_W fxk C A7 A0 M9 _ Rc9 s w h datad data bufs1 bufs2 tabval tab38 tab14 S CK HWs9 SUB7 Hs16 ltac:(clear - Hlo1; lia) Hhi HOK Hw1 Hh1
             Ldatad_a7 Fdatad F0datad Ldata_a7 Lbufs1_a7 Fbufs1 F0bufs1 Lbufs2_a7 Fbufs2 F0bufs2 Ltabval_a7 Ftabval F0tabval Ltab38_a7 Ftab38 F0tab38 Ltab14_a7 Ftab14 F0tab14 RRdatad RRdata RRbufs1 RRbufs2 RRtabval RRtab38 RRtab14 NDk Ztab38M9 Ztab14M9 Q2_9 Q9_9 Q18_9 Q20_9 Q21_9 Q22_9 Q25_9 KC0 KC1 KC2 KC3 KC4) end.
  intros r10 m10 HW10 PMl9 AGR9  KEPTS9 KEEPB9.
  assert (PM10 : POSTM C A0 s m4 m10).
  { eapply POSTM_trans; [exact PM9|]. eapply POSTM_trans; [exact PMs9 | exact PMl9]. }
  assert (PXd10 : PIXat m10 pixd (set_data (pix_hdr w h 2) datad)).
  { apply (pix_keepl A7 M9 m10 pixd _ [Z_to_bv 64 datad; Z_to_bv 64 bufs1; Z_to_bv 64 bufs2; Z_to_bv 64 tabval; Z_to_bv 64 tab38; Z_to_bv 64 tab14] PXdM9 Lpixd_a7); [|exact KEEPB9].
    cbn [List.In]. intros HH. repeat (destruct HH as [EE|HH]; [first [exact (NE_pixd_datad (eq_sym EE)) | exact (NE_pixd_bufs1 (eq_sym EE)) | exact (NE_pixd_bufs2 (eq_sym EE)) | exact (NE_pixd_tabval (eq_sym EE)) | exact (NE_pixd_tab38 (eq_sym EE)) | exact (NE_pixd_tab14 (eq_sym EE))]|]). exact HH. }
  assert (PXt10 : PIXat m10 pixs (set_rc (hdv w h 8 0 data) 2)).
  { apply (pix_keepl A7 M9 m10 pixs _ [Z_to_bv 64 datad; Z_to_bv 64 bufs1; Z_to_bv 64 bufs2; Z_to_bv 64 tabval; Z_to_bv 64 tab38; Z_to_bv 64 tab14] PXtM9 Lpixs_a7); [|exact KEEPB9].
    cbn [List.In]. intros HH. repeat (destruct HH as [EE|HH]; [first [exact (NE_pixs_datad (eq_sym EE)) | exact (NE_pixs_bufs1 (eq_sym EE)) | exact (NE_pixs_bufs2 (eq_sym EE)) | exact (NE_pixs_tabval (eq_sym EE)) | exact (NE_pixs_tab38 (eq_sym EE)) | exact (NE_pixs_tab14 (eq_sym EE))]|]). exact HH. }
  assert (KEPT9 : Forall (ex_region_kept E9 M9 m10) [(EVar 32, (-208)%Z, (-200)%Z); (EVar 32, (-184)%Z, (-176)%Z); (EVar 32, (-168)%Z, (0)%Z)]).
  { constructor; [exact (exT_kept_in E9 M9 m10 (EVar 32) s (-208) (-200) (s + -208) (s + -200) (fun a Ha => KEPTS9 a (or_introl Ha)) eq_refl RS (Z.le_refl _) (Z.le_refl _))|]. constructor; [exact (exT_kept_in E9 M9 m10 (EVar 32) s (-184) (-176) (s + -184) (s + -176) (fun a Ha => KEPTS9 a (or_intror (or_introl Ha))) eq_refl RS (Z.le_refl _) (Z.le_refl _))|]. constructor; [exact (exT_kept_in E9 M9 m10 (EVar 32) s (-168) (0) (s + -168) (s + 0) (fun a Ha => KEPTS9 a (or_intror (or_intror Ha))) eq_refl RS (Z.le_refl _) (Z.le_refl _))|]. constructor. }
  pose proof (ex_know_keepD SEGS E9 M9 m10 _ [] _ HKc9 KEPT9) as HKk9.
  match type of HKk9 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E9 m10 kk') in HKk9 end.
  pose proof (regs_ok_agree 345%nat E9 (ex_envL vals9 r10 [exW_canary SEGS 415784 m10]) _ _ (vals_app_agree vals9 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa9.
  pose proof (exW_regs_keep _ _ _ _ _ [1%nat; 5%nat; 6%nat; 7%nat; 8%nat; 10%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 19%nat; 23%nat; 24%nat; 26%nat; 27%nat; 28%nat; 29%nat; 30%nat; 31%nat] HRa9 (ex_regs_ok_junk vals9 r10 [exW_canary SEGS 415784 m10] 345%nat ltac:(vm_cast_no_check (eq_refl 345%nat))) (exW_agree_keep _ _ _ AGR9)) as HRn10.
  clear HRa9.
  assert (HKa10 : know_ok SEGS (ex_envL vals9 r10 [exW_canary SEGS 415784 m10]) m10 _) by (exact (know_ok_agree SEGS 345%nat E9 _ m10 _ (vals_app_agree vals9 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk9)).
  rewrite (fr_denot_agree 345%nat E9 (ex_envL vals9 r10 [exW_canary SEGS 415784 m10]) _ fr2 (vals_app_agree vals9 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc9 HKk9 KEPT9 HC9 HWs9 PMs9 Q2_9 Q9_9 Q18_9 Q20_9 Q21_9 Q22_9 Q25_9 PM9 HW9 FRs9 AGR9 KEPTS9 KEEPB9 PMl9 NDk KC0 KC1 KC2 KC3 KC4 PXdM9 PXd9 PXtM9 PXt9 LKs9 Ztab38M9 Ztab38_9 Ztab14M9 Ztab14_9.
  subst M9. clear log9. clear E9. try clear Rc9. clear KN9.
  lazymatch type of HRn10 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn10 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A7 m10 _ (s - 256) (Z.to_nat 256) CK HW10 GLO1 GLO2) as SOK10.
  pose proof (exW_canary_ok SEGS 415784 m10 (canary_any m10)) as CANOK10.
  pose (vals10 := vals9 ++ map (getr r10) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m10]).
  pose proof (exW_kn_fixed SEGS C A7 m10 _ (ex_envL vals9 r10 [exW_canary SEGS 415784 m10]) (EVar 377) (EVar 32) (exW_canary SEGS 415784 m10) s 256 415784 65536 212992 213416 213568 213416 213568
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
  exb_exit ST Rc10 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E10 := EEx) in HR, Hlf, HK, Hms |- *; set (log10 := LLx) in Hms, Hlf; set (M10 := mem_denot E10 m10 log10) in Hms end.
  assert (WP10 : W C A7 M10 (with_vmmaps vm7 md) /\ POSTM C A0 s m10 M10).
  { subst M10. apply (exW_win_blks C A7 A0 m10 _ E10 log10 (EVar 32) s 256 [] CK HW10 SUB7 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP10 as [HWs10 PMs10].
  pose proof (exW_win_only E10 m10 log10 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs10. change (mem_denot E10 m10 log10) with M10 in FRs10.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log10 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC10 : carry log10 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc10 : know_ok SEGS E10 M10 kn1) by (apply (carry_after SEGS E10 m10 log10 kn0 [] kn1 scs hs HC10 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW10)) | exact (mp_lazy _ (w_pure _ _ _ _ HW10)) | exact Hms |].
  pose (BS10 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, data); (173%nat, wpl_of w 8); (207%nat, bufs1); (241%nat, bufs2); (275%nat, tabval); (309%nat, tab38); (343%nat, tab14)]).
  exW_regfactB BS10 HR ex_r10 Q10_10. exW_regfactB BS10 HR ex_r11 Q11_10. exW_regfactB BS10 HR ex_r1 Q1_10. exW_regfactB BS10 HR ex_r2 Q2_10. exW_regfactB BS10 HR ex_r4 Q4_10.
  clear BS10.
  lazymatch type of Q2_10 with _ = Z_to_bv 64 (s + ?off) => pose (OFF10 := off) end.
  (* [comment removed for export] *)
  assert (PXdM10 : PIXat M10 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_sess C A7 m10 M10 _ s 256 pixd _ CK HW10 GLO1 Lpixd_a7 PXd10 FRs10).
  assert (PXtM10 : PIXat M10 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_sess C A7 m10 M10 _ s 256 pixs _ CK HW10 GLO1 Lpixs_a7 PXt10 FRs10).
  lazymatch type of Q1_10 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixcmapCreateLinear24_W fxk C A7 M10 _ Rc10 (s + OFF10)%Z (Z_to_bv 64 ra) S CK HWs10 Q2_10
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF10, CML_STACK, CALLOC_STACK, ALLOC_STACK; clear - Hlo1; lia) ltac:(unfold OFF10; clear - Hhi; lia) Q1_10 ltac:(red; apply bv_eq; reflexivity) Q4_10 Q10_10 Q11_10
             (kR - RK_pix - RK_rmc - 1 - 1 - 1 - 1 - 1)%Z (bR - RB_pix14 - RB_rmc - alloc_margin (wpl_of w 8 * 4) - alloc_margin (wpl_of w 8 * 4) - alloc_margin (256 * 4) - alloc_margin (256 * 4) - alloc_margin (256 * 4))%Z ltac:(rewrite with_vmmaps_vmmaps; exact RM7) ltac:(clear - HkR'; unfold RK_cml, RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB MG17 RBpos; lia)) end end.
  intros A8 m11 vm8 r11 cmd arrd HW11 CSx10 PMc10 A10_10 CMN RM8.
  pose proof CSx10 as CS10. clear CSx10.
  rewrite with_vmmaps_twice in HW11 |- *.
  destruct CMN as (Gcmd1 & Gcmd2 & Garrd1 & Garrd2 & NEcmarr & Fcmdx & Farrdx & F0cmd & F0arrd & Lcmd_a8 & Larrd_a8 & CMP11 & CMOK & LEQ10).
  cbn [c_arr c_nalloc] in Garrd1, Garrd2, NEcmarr, Farrdx, F0arrd, Larrd_a8, LEQ10. change (4 * 4)%Z with 16%Z in Garrd2, Larrd_a8.
  assert (RRcmd : (0 <= cmd < 2 ^ 64)%Z) by lia. assert (RRarrd : (0 <= arrd < 2 ^ 64)%Z) by lia.
  pose proof (fresh_sub A0 A7 _ SUB7 Fcmdx) as Fcmd. pose proof (fresh_sub A0 A7 _ SUB7 Farrdx) as Farrd.
  assert (SUB8 : sub_live A0 A8).
  { intros q0 kq Lq. rewrite (LEQ10 q0 (ne_live A0 q0 _ kq Lq Fcmd) (ne_live A0 q0 _ kq Lq Farrd)). exact (SUB7 q0 kq Lq). }
  pose proof (fun (q0 : word) (Hq : ~ In q0 (Z_to_bv 64 cmd :: Z_to_bv 64 arrd :: [Z_to_bv 64 tab14; Z_to_bv 64 tab38; Z_to_bv 64 tabval; Z_to_bv 64 bufs2; Z_to_bv 64 bufs1; Z_to_bv 64 pixd; Z_to_bv 64 datad])) =>
                eq_trans (LEQ10 q0 (fun EE => Hq (or_introl (eq_sym EE))) (fun EE => Hq (or_intror (or_introl (eq_sym EE))))) (LDEL7 q0 (fun XX => Hq (or_intror (or_intror XX))))) as LDEL8.
  pose proof (ne_live A7 _ _ _ Lpixs_a7 Fcmdx) as NE_pixs_cmd. pose proof (ne_live A7 _ _ _ Lpixs_a7 Farrdx) as NE_pixs_arrd.
  pose proof (eq_trans (LEQ10 _ NE_pixs_cmd NE_pixs_arrd) Lpixs_a7) as Lpixs_a8.
  pose proof (ne_live A7 _ _ _ Ldata_a7 Fcmdx) as NE_data_cmd. pose proof (ne_live A7 _ _ _ Ldata_a7 Farrdx) as NE_data_arrd.
  pose proof (eq_trans (LEQ10 _ NE_data_cmd NE_data_arrd) Ldata_a7) as Ldata_a8.
  pose proof (ne_live A7 _ _ _ Lpixd_a7 Fcmdx) as NE_pixd_cmd. pose proof (ne_live A7 _ _ _ Lpixd_a7 Farrdx) as NE_pixd_arrd.
  pose proof (eq_trans (LEQ10 _ NE_pixd_cmd NE_pixd_arrd) Lpixd_a7) as Lpixd_a8.
  pose proof (ne_live A7 _ _ _ Ldatad_a7 Fcmdx) as NE_datad_cmd. pose proof (ne_live A7 _ _ _ Ldatad_a7 Farrdx) as NE_datad_arrd.
  pose proof (eq_trans (LEQ10 _ NE_datad_cmd NE_datad_arrd) Ldatad_a7) as Ldatad_a8.
  pose proof (ne_live A7 _ _ _ Lbufs1_a7 Fcmdx) as NE_bufs1_cmd. pose proof (ne_live A7 _ _ _ Lbufs1_a7 Farrdx) as NE_bufs1_arrd.
  pose proof (eq_trans (LEQ10 _ NE_bufs1_cmd NE_bufs1_arrd) Lbufs1_a7) as Lbufs1_a8.
  pose proof (ne_live A7 _ _ _ Lbufs2_a7 Fcmdx) as NE_bufs2_cmd. pose proof (ne_live A7 _ _ _ Lbufs2_a7 Farrdx) as NE_bufs2_arrd.
  pose proof (eq_trans (LEQ10 _ NE_bufs2_cmd NE_bufs2_arrd) Lbufs2_a7) as Lbufs2_a8.
  pose proof (ne_live A7 _ _ _ Ltabval_a7 Fcmdx) as NE_tabval_cmd. pose proof (ne_live A7 _ _ _ Ltabval_a7 Farrdx) as NE_tabval_arrd.
  pose proof (eq_trans (LEQ10 _ NE_tabval_cmd NE_tabval_arrd) Ltabval_a7) as Ltabval_a8.
  pose proof (ne_live A7 _ _ _ Ltab38_a7 Fcmdx) as NE_tab38_cmd. pose proof (ne_live A7 _ _ _ Ltab38_a7 Farrdx) as NE_tab38_arrd.
  pose proof (eq_trans (LEQ10 _ NE_tab38_cmd NE_tab38_arrd) Ltab38_a7) as Ltab38_a8.
  pose proof (ne_live A7 _ _ _ Ltab14_a7 Fcmdx) as NE_tab14_cmd. pose proof (ne_live A7 _ _ _ Ltab14_a7 Farrdx) as NE_tab14_arrd.
  pose proof (eq_trans (LEQ10 _ NE_tab14_cmd NE_tab14_arrd) Ltab14_a7) as Ltab14_a8.
  assert (PXd11 : PIXat m11 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_livk A7 M10 m11 pixd _ PXdM10 (proj2 PMc10) Lpixd_a7).
  assert (PXt11 : PIXat m11 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_livk A7 M10 m11 pixs _ PXtM10 (proj2 PMc10) Lpixs_a7).
  assert (PM11 : POSTM C A0 s m4 m11).
  { eapply POSTM_trans; [exact PM10|]. eapply POSTM_trans; [exact PMs10|]. apply (POSTM_sub C A0 A7 _ _ _ SUB7). apply (POSTM_mono C A7 (s + OFF10) s); [unfold OFF10; lia | exact PMc10]. }
  assert (KEPT10 : Forall (ex_region_kept E10 M10 m11) [(EVar 32, OFF10, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF10 256 M10 m11 E10 (EVar 32) CK (proj1 PMc10) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E10 M10 m11 _ [] _ HKc10 KEPT10) as HKk10.
  match type of HKk10 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E10 m11 kk') in HKk10 end.
  pose proof (regs_ok_agree 378%nat E10 (ex_envL vals10 r11 [cmd; exW_canary SEGS 415784 m11]) _ _ (vals_app_agree vals10 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa10.
  pose proof (exW_regs_call _ _ _ _ _ HRa10 (ex_regs_ok_junk vals10 r11 [cmd; exW_canary SEGS 415784 m11] 378%nat ltac:(vm_cast_no_check (eq_refl 378%nat))) CS10) as HRn11.
  clear HRa10.
  assert (HKa11 : know_ok SEGS (ex_envL vals10 r11 [cmd; exW_canary SEGS 415784 m11]) m11 _) by (exact (know_ok_agree SEGS 378%nat E10 _ m11 _ (vals_app_agree vals10 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk10)).
  rewrite (fr_denot_agree 378%nat E10 (ex_envL vals10 r11 [cmd; exW_canary SEGS 415784 m11]) _ fr2 (vals_app_agree vals10 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r11 ex_r10 (EVar 410) HRn11 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_10)) as HRx11. clear HRn11. rename HRx11 into HRn11.
  clear HR HK Hlf Hms HKc10 HKk10 KEPT10 HC10 HWs10 PMs10 Q10_10 Q11_10 Q1_10 Q2_10 Q4_10 PM10 HW10 FRs10 PMc10 CS10 SUB7 RM7 LEQ10 Fcmdx Farrdx OFF10 LDEL7 A10_10 Lpixs_a7 Ldata_a7 Lpixd_a7 Ldatad_a7 Lbufs1_a7 Lbufs2_a7 Ltabval_a7 Ltab38_a7 Ltab14_a7 PXdM10 PXd10 PXtM10 PXt10.
  subst M10. clear log10. clear E10. try clear Rc10. clear KN10.
  lazymatch type of HRn11 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn11 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A8 m11 _ (s - 256) (Z.to_nat 256) CK HW11 GLO1 GLO2) as SOK11.
  pose proof (exW_canary_ok SEGS 415784 m11 (canary_any m11)) as CANOK11.
  pose (vals11 := vals10 ++ map (getr r11) ex_regs_list ++ map (Z_to_bv 64) [cmd; exW_canary SEGS 415784 m11]).
  pose proof (exW_kn_fixed SEGS C A8 m11 _ (ex_envL vals10 r11 [cmd; exW_canary SEGS 415784 m11]) (EVar 411) (EVar 32) (exW_canary SEGS 415784 m11) s 256 415784 65536 212992 213416 213568 213416 213568
                HW11 eq_refl (proj1 CANOK11) (proj2 CANOK11) eq_refl eq_refl eq_refl SOK11 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf11.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf11 HKa11)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn11 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN11 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf11 HKa11 SOK11 CANOK11.
  repeat match goal with H : getr r11 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc11 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E11 := EEx) in HR, Hlf, HK, Hms |- *; set (log11 := LLx) in Hms, Hlf; set (M11 := mem_denot E11 m11 log11) in Hms end.
  assert (WP11 : W C A8 M11 (with_vmmaps vm8 md) /\ POSTM C A0 s m11 M11).
  { subst M11. apply (exW_win_blks C A8 A0 m11 _ E11 log11 (EVar 32) s 256 [] CK HW11 SUB8 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP11 as [HWs11 PMs11].
  pose proof (exW_win_only E11 m11 log11 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs11. change (mem_denot E11 m11 log11) with M11 in FRs11.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log11 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC11 : carry log11 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc11 : know_ok SEGS E11 M11 kn1) by (apply (carry_after SEGS E11 m11 log11 kn0 [] kn1 scs hs HC11 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW11)) | exact (mp_lazy _ (w_pure _ _ _ _ HW11)) | exact Hms |].
  pose (BS11 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, data); (173%nat, wpl_of w 8); (207%nat, bufs1); (241%nat, bufs2); (275%nat, tabval); (309%nat, tab38); (343%nat, tab14); (410%nat, cmd)]).
  exW_regfactB BS11 HR ex_r10 Q10_11. exW_regfactB BS11 HR ex_r11 Q11_11. exW_regfactB BS11 HR ex_r1 Q1_11. exW_regfactB BS11 HR ex_r2 Q2_11.
  clear BS11.
  lazymatch type of Q2_11 with _ = Z_to_bv 64 (s + ?off) => pose (OFF11 := off) end.
  (* [comment removed for export] *)
  assert (PXdM11 : PIXat M11 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_sess C A8 m11 M11 _ s 256 pixd _ CK HW11 GLO1 Lpixd_a8 PXd11 FRs11).
  assert (PXtM11 : PIXat M11 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_sess C A8 m11 M11 _ s 256 pixs _ CK HW11 GLO1 Lpixs_a8 PXt11 FRs11).
  assert (CMPM11 : CMAPat M11 cmd (CMAPV arrd 2 4 4 0)) by exact (exT_cmap_sess C A8 m11 M11 _ s 256 cmd _ CK HW11 GLO1 Lcmd_a8 CMP11 FRs11).
  rewrite PC_SETCMAP_eq.
  lazymatch type of Q1_11 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixSetColormap_S_W (fx := fxk) C A0 A8 M11 _ Rc11 (s + OFF11) pixd cmd (set_data (pix_hdr w h 2) datad) (CMAPV arrd 2 4 4 0) (Z_to_bv 64 ra) S CK HWs11 SUB8 Q2_11
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF11; clear - Hlo1; lia) ltac:(unfold OFF11; clear - Hhi; lia) Q1_11 ltac:(red; apply bv_eq; reflexivity) Q10_11 Q11_11
             PXdM11 eq_refl Lpixd_a8 Fpixd F0pixd CMPM11 CMOK Lcmd_a8 NE_pixd_cmd) end end.
  intros m12 r12 HW12 CSx11 PMc11 PXd12 CMP12 A10_11 KEEPS11.
  pose proof CSx11 as CS11. clear CSx11.
  assert (PXt12 : PIXat m12 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (pix_keep1 A8 M11 m12 pixs _ _ PXtM11 Lpixs_a8 (fun EE => NE_pixd_pixs (eq_sym EE)) KEEPS11).
  assert (PM12 : POSTM C A0 s m4 m12).
  { eapply POSTM_trans; [exact PM11|]. eapply POSTM_trans; [exact PMs11|]. apply (POSTM_mono C A0 (s + OFF11) s); [unfold OFF11; lia | exact PMc11]. }
  assert (KEPT11 : Forall (ex_region_kept E11 M11 m12) [(EVar 32, OFF11, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF11 256 M11 m12 E11 (EVar 32) CK (proj1 PMc11) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E11 M11 m12 _ [] _ HKc11 KEPT11) as HKk11.
  match type of HKk11 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E11 m12 kk') in HKk11 end.
  pose proof (regs_ok_agree 412%nat E11 (ex_envL vals11 r12 [exW_canary SEGS 415784 m12]) _ _ (vals_app_agree vals11 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa11.
  pose proof (exW_regs_call _ _ _ _ _ HRa11 (ex_regs_ok_junk vals11 r12 [exW_canary SEGS 415784 m12] 412%nat ltac:(vm_cast_no_check (eq_refl 412%nat))) CS11) as HRn12.
  clear HRa11.
  assert (HKa12 : know_ok SEGS (ex_envL vals11 r12 [exW_canary SEGS 415784 m12]) m12 _) by (exact (know_ok_agree SEGS 412%nat E11 _ m12 _ (vals_app_agree vals11 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk11)).
  rewrite (fr_denot_agree 412%nat E11 (ex_envL vals11 r12 [exW_canary SEGS 415784 m12]) _ fr2 (vals_app_agree vals11 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc11 HKk11 KEPT11 HC11 HWs11 PMs11 Q10_11 Q11_11 Q1_11 Q2_11 PM11 HW11 FRs11 PMc11 CS11 OFF11 A10_11 KEEPS11 PXdM11 PXd11 PXtM11 PXt11 CMPM11 CMP11.
  subst M11. clear log11. clear E11. try clear Rc11. clear KN11.
  lazymatch type of HRn12 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn12 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A8 m12 _ (s - 256) (Z.to_nat 256) CK HW12 GLO1 GLO2) as SOK12.
  pose proof (exW_canary_ok SEGS 415784 m12 (canary_any m12)) as CANOK12.
  pose (vals12 := vals11 ++ map (getr r12) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m12]).
  pose proof (exW_kn_fixed SEGS C A8 m12 _ (ex_envL vals11 r12 [exW_canary SEGS 415784 m12]) (EVar 444) (EVar 32) (exW_canary SEGS 415784 m12) s 256 415784 65536 212992 213416 213568 213416 213568
                HW12 eq_refl (proj1 CANOK12) (proj2 CANOK12) eq_refl eq_refl eq_refl SOK12 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf12.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf12 HKa12)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn12 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN12 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf12 HKa12 SOK12 CANOK12.
  repeat match goal with H : getr r12 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc12 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E12 := EEx) in HR, Hlf, HK, Hms |- *; set (log12 := LLx) in Hms, Hlf; set (M12 := mem_denot E12 m12 log12) in Hms end.
  assert (WP12 : W C A8 M12 (with_vmmaps vm8 md) /\ POSTM C A0 s m12 M12).
  { subst M12. apply (exW_win_blks C A8 A0 m12 _ E12 log12 (EVar 32) s 256 [] CK HW12 SUB8 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP12 as [HWs12 PMs12].
  pose proof (exW_win_only E12 m12 log12 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs12. change (mem_denot E12 m12 log12) with M12 in FRs12.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log12 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC12 : carry log12 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc12 : know_ok SEGS E12 M12 kn1) by (apply (carry_after SEGS E12 m12 log12 kn0 [] kn1 scs hs HC12 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW12)) | exact (mp_lazy _ (w_pure _ _ _ _ HW12)) | exact Hms |].
  pose (BS12 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, data); (173%nat, wpl_of w 8); (207%nat, bufs1); (241%nat, bufs2); (275%nat, tabval); (309%nat, tab38); (343%nat, tab14); (410%nat, cmd)]).
  exW_regfactB BS12 HR ex_r10 Q10_12. exW_regfactB BS12 HR ex_r1 Q1_12. exW_regfactB BS12 HR ex_r2 Q2_12. exW_regfactB BS12 HR ex_r4 Q4_12.
  clear BS12.
  lazymatch type of Q2_12 with _ = Z_to_bv 64 (s + ?off) => pose (OFF12 := off) end.
  (* [comment removed for export] *)
  assert (PXdM12 : PIXat M12 pixd (set_cmap (set_data (pix_hdr w h 2) datad) cmd)) by exact (exT_pix_sess C A8 m12 M12 _ s 256 pixd _ CK HW12 GLO1 Lpixd_a8 PXd12 FRs12).
  assert (PXtM12 : PIXat M12 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_sess C A8 m12 M12 _ s 256 pixs _ CK HW12 GLO1 Lpixs_a8 PXt12 FRs12).
  assert (CMPM12 : CMAPat M12 cmd (CMAPV arrd 2 4 4 0)) by exact (exT_cmap_sess C A8 m12 M12 _ s 256 cmd _ CK HW12 GLO1 Lcmd_a8 CMP12 FRs12).
  lazymatch type of Q1_12 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_12 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A8 M12 _ Rc12 (Z_to_bv 64 bufs1) (Z_to_bv 64 ret) (4 * wpl_of w 8) sp' S CK HWs12 Q10_12 Lbufs1_a8 F0bufs1 Q1_12
             ltac:(red; apply bv_eq; reflexivity) Q4_12 Q2_12 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF12, ALLOC_STACK; clear - Hlo1; lia) ltac:(unfold OFF12; clear - Hhi; lia)) end end end.
  intros A9 m13 vm9 r13 HW13 CSx12 Ldead12 LEQ12 PMc12 RTR12.
  pose proof CSx12 as CS12. clear CSx12.
  rewrite with_vmmaps_twice in HW13 |- *.
  assert (SUB9 : sub_live A0 A9).
  { intros q0 kq Lq. rewrite (LEQ12 q0 (ne_live A0 q0 _ kq Lq Fbufs1)). exact (SUB8 q0 kq Lq). }
  assert (LDEL9 : forall q0 : word, ~ In q0 [Z_to_bv 64 cmd; Z_to_bv 64 arrd; Z_to_bv 64 tab14; Z_to_bv 64 tab38; Z_to_bv 64 tabval; Z_to_bv 64 bufs2; Z_to_bv 64 pixd; Z_to_bv 64 datad] -> live A9 q0 = live A0 q0).
  { intros q0 Hq. destruct (decide (Z_to_bv 64 bufs1 = q0)) as [<-|NEq]; [rewrite Ldead12, Fbufs1; reflexivity|]. rewrite (LEQ12 q0 (fun EE => NEq (eq_sym EE))). apply LDEL8. clear - Hq NEq. cbn [In] in *. tauto. }
  pose proof (eq_trans (LEQ12 _ NE_pixs_bufs1) Lpixs_a8) as Lpixs_a9.
  pose proof (eq_trans (LEQ12 _ NE_data_bufs1) Ldata_a8) as Ldata_a9.
  pose proof (eq_trans (LEQ12 _ NE_pixd_bufs1) Lpixd_a8) as Lpixd_a9.
  pose proof (eq_trans (LEQ12 _ NE_datad_bufs1) Ldatad_a8) as Ldatad_a9.
  pose proof (eq_trans (LEQ12 _ (fun EE => NE_bufs1_bufs2 (eq_sym EE))) Lbufs2_a8) as Lbufs2_a9.
  pose proof (eq_trans (LEQ12 _ (fun EE => NE_bufs1_tabval (eq_sym EE))) Ltabval_a8) as Ltabval_a9.
  pose proof (eq_trans (LEQ12 _ (fun EE => NE_bufs1_tab38 (eq_sym EE))) Ltab38_a8) as Ltab38_a9.
  pose proof (eq_trans (LEQ12 _ (fun EE => NE_bufs1_tab14 (eq_sym EE))) Ltab14_a8) as Ltab14_a9.
  pose proof (eq_trans (LEQ12 _ (fun EE => NE_bufs1_cmd (eq_sym EE))) Lcmd_a8) as Lcmd_a9.
  pose proof (eq_trans (LEQ12 _ (fun EE => NE_bufs1_arrd (eq_sym EE))) Larrd_a8) as Larrd_a9.
  assert (PXd13 : PIXat m13 pixd (set_cmap (set_data (pix_hdr w h 2) datad) cmd)) by exact (exT_pix_livk A9 M12 m13 pixd _ PXdM12 (proj2 PMc12) Lpixd_a9).
  assert (PXt13 : PIXat m13 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_livk A9 M12 m13 pixs _ PXtM12 (proj2 PMc12) Lpixs_a9).
  assert (CMP13 : CMAPat m13 cmd (CMAPV arrd 2 4 4 0)) by exact (exT_cmap_livk A9 M12 m13 cmd _ CMPM12 (proj2 PMc12) Lcmd_a9).
  assert (PM13 : POSTM C A0 s m4 m13).
  { eapply POSTM_trans; [exact PM12|]. eapply POSTM_trans; [exact PMs12|]. apply (POSTM_sub C A0 A9 _ _ _ SUB9). apply (POSTM_mono C A9 (s + OFF12) s); [unfold OFF12; lia | exact PMc12]. }
  pose proof (RTR12 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM8) ltac:(clear - HkR'; unfold RK_cml, RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB MG17 RBpos; lia)) as RM9. rewrite !Z.sub_0_r in RM9.
  assert (KEPT12 : Forall (ex_region_kept E12 M12 m13) [(EVar 32, OFF12, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF12 256 M12 m13 E12 (EVar 32) CK (proj1 PMc12) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E12 M12 m13 _ [] _ HKc12 KEPT12) as HKk12.
  match type of HKk12 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E12 m13 kk') in HKk12 end.
  pose proof (regs_ok_agree 445%nat E12 (ex_envL vals12 r13 [exW_canary SEGS 415784 m13]) _ _ (vals_app_agree vals12 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa12.
  pose proof (exW_regs_call _ _ _ _ _ HRa12 (ex_regs_ok_junk vals12 r13 [exW_canary SEGS 415784 m13] 445%nat ltac:(vm_cast_no_check (eq_refl 445%nat))) CS12) as HRn13.
  clear HRa12.
  assert (HKa13 : know_ok SEGS (ex_envL vals12 r13 [exW_canary SEGS 415784 m13]) m13 _) by (exact (know_ok_agree SEGS 445%nat E12 _ m13 _ (vals_app_agree vals12 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk12)).
  rewrite (fr_denot_agree 445%nat E12 (ex_envL vals12 r13 [exW_canary SEGS 415784 m13]) _ fr2 (vals_app_agree vals12 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc12 HKk12 KEPT12 HC12 HWs12 PMs12 Q10_12 Q1_12 Q2_12 Q4_12 PM12 HW12 FRs12 PMc12 CS12 SUB8 RM8 Ldead12 LEQ12 RTR12 Lbufs1_a8 OFF12 LDEL8 Lpixs_a8 Ldata_a8 Lpixd_a8 Ldatad_a8 Lbufs2_a8 Ltabval_a8 Ltab38_a8 Ltab14_a8 Lcmd_a8 Larrd_a8 PXdM12 PXd12 PXtM12 PXt12 CMPM12 CMP12.
  subst M12. clear log12. clear E12. try clear Rc12. clear KN12.
  lazymatch type of HRn13 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn13 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A9 m13 _ (s - 256) (Z.to_nat 256) CK HW13 GLO1 GLO2) as SOK13.
  pose proof (exW_canary_ok SEGS 415784 m13 (canary_any m13)) as CANOK13.
  pose (vals13 := vals12 ++ map (getr r13) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m13]).
  pose proof (exW_kn_fixed SEGS C A9 m13 _ (ex_envL vals12 r13 [exW_canary SEGS 415784 m13]) (EVar 477) (EVar 32) (exW_canary SEGS 415784 m13) s 256 415784 65536 212992 213416 213568 213416 213568
                HW13 eq_refl (proj1 CANOK13) (proj2 CANOK13) eq_refl eq_refl eq_refl SOK13 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf13.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf13 HKa13)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn13 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN13 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf13 HKa13 SOK13 CANOK13.
  repeat match goal with H : getr r13 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc13 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E13 := EEx) in HR, Hlf, HK, Hms |- *; set (log13 := LLx) in Hms, Hlf; set (M13 := mem_denot E13 m13 log13) in Hms end.
  assert (WP13 : W C A9 M13 (with_vmmaps vm9 md) /\ POSTM C A0 s m13 M13).
  { subst M13. apply (exW_win_blks C A9 A0 m13 _ E13 log13 (EVar 32) s 256 [] CK HW13 SUB9 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP13 as [HWs13 PMs13].
  pose proof (exW_win_only E13 m13 log13 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs13. change (mem_denot E13 m13 log13) with M13 in FRs13.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log13 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC13 : carry log13 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc13 : know_ok SEGS E13 M13 kn1) by (apply (carry_after SEGS E13 m13 log13 kn0 [] kn1 scs hs HC13 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW13)) | exact (mp_lazy _ (w_pure _ _ _ _ HW13)) | exact Hms |].
  pose (BS13 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, data); (173%nat, wpl_of w 8); (207%nat, bufs1); (241%nat, bufs2); (275%nat, tabval); (309%nat, tab38); (343%nat, tab14); (410%nat, cmd)]).
  exW_regfactB BS13 HR ex_r10 Q10_13. exW_regfactB BS13 HR ex_r1 Q1_13. exW_regfactB BS13 HR ex_r2 Q2_13. exW_regfactB BS13 HR ex_r4 Q4_13.
  clear BS13.
  lazymatch type of Q2_13 with _ = Z_to_bv 64 (s + ?off) => pose (OFF13 := off) end.
  (* [comment removed for export] *)
  assert (PXdM13 : PIXat M13 pixd (set_cmap (set_data (pix_hdr w h 2) datad) cmd)) by exact (exT_pix_sess C A9 m13 M13 _ s 256 pixd _ CK HW13 GLO1 Lpixd_a9 PXd13 FRs13).
  assert (PXtM13 : PIXat M13 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_sess C A9 m13 M13 _ s 256 pixs _ CK HW13 GLO1 Lpixs_a9 PXt13 FRs13).
  assert (CMPM13 : CMAPat M13 cmd (CMAPV arrd 2 4 4 0)) by exact (exT_cmap_sess C A9 m13 M13 _ s 256 cmd _ CK HW13 GLO1 Lcmd_a9 CMP13 FRs13).
  lazymatch type of Q1_13 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_13 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A9 M13 _ Rc13 (Z_to_bv 64 bufs2) (Z_to_bv 64 ret) (4 * wpl_of w 8) sp' S CK HWs13 Q10_13 Lbufs2_a9 F0bufs2 Q1_13
             ltac:(red; apply bv_eq; reflexivity) Q4_13 Q2_13 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF13, ALLOC_STACK; clear - Hlo1; lia) ltac:(unfold OFF13; clear - Hhi; lia)) end end end.
  intros A10 m14 vm10 r14 HW14 CSx13 Ldead13 LEQ13 PMc13 RTR13.
  pose proof CSx13 as CS13. clear CSx13.
  rewrite with_vmmaps_twice in HW14 |- *.
  assert (SUB10 : sub_live A0 A10).
  { intros q0 kq Lq. rewrite (LEQ13 q0 (ne_live A0 q0 _ kq Lq Fbufs2)). exact (SUB9 q0 kq Lq). }
  assert (LDEL10 : forall q0 : word, ~ In q0 [Z_to_bv 64 cmd; Z_to_bv 64 arrd; Z_to_bv 64 tab14; Z_to_bv 64 tab38; Z_to_bv 64 tabval; Z_to_bv 64 pixd; Z_to_bv 64 datad] -> live A10 q0 = live A0 q0).
  { intros q0 Hq. destruct (decide (Z_to_bv 64 bufs2 = q0)) as [<-|NEq]; [rewrite Ldead13, Fbufs2; reflexivity|]. rewrite (LEQ13 q0 (fun EE => NEq (eq_sym EE))). apply LDEL9. clear - Hq NEq. cbn [In] in *. tauto. }
  pose proof (eq_trans (LEQ13 _ NE_pixs_bufs2) Lpixs_a9) as Lpixs_a10.
  pose proof (eq_trans (LEQ13 _ NE_data_bufs2) Ldata_a9) as Ldata_a10.
  pose proof (eq_trans (LEQ13 _ NE_pixd_bufs2) Lpixd_a9) as Lpixd_a10.
  pose proof (eq_trans (LEQ13 _ NE_datad_bufs2) Ldatad_a9) as Ldatad_a10.
  pose proof (eq_trans (LEQ13 _ (fun EE => NE_bufs2_tabval (eq_sym EE))) Ltabval_a9) as Ltabval_a10.
  pose proof (eq_trans (LEQ13 _ (fun EE => NE_bufs2_tab38 (eq_sym EE))) Ltab38_a9) as Ltab38_a10.
  pose proof (eq_trans (LEQ13 _ (fun EE => NE_bufs2_tab14 (eq_sym EE))) Ltab14_a9) as Ltab14_a10.
  pose proof (eq_trans (LEQ13 _ (fun EE => NE_bufs2_cmd (eq_sym EE))) Lcmd_a9) as Lcmd_a10.
  pose proof (eq_trans (LEQ13 _ (fun EE => NE_bufs2_arrd (eq_sym EE))) Larrd_a9) as Larrd_a10.
  assert (PXd14 : PIXat m14 pixd (set_cmap (set_data (pix_hdr w h 2) datad) cmd)) by exact (exT_pix_livk A10 M13 m14 pixd _ PXdM13 (proj2 PMc13) Lpixd_a10).
  assert (PXt14 : PIXat m14 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_livk A10 M13 m14 pixs _ PXtM13 (proj2 PMc13) Lpixs_a10).
  assert (CMP14 : CMAPat m14 cmd (CMAPV arrd 2 4 4 0)) by exact (exT_cmap_livk A10 M13 m14 cmd _ CMPM13 (proj2 PMc13) Lcmd_a10).
  assert (PM14 : POSTM C A0 s m4 m14).
  { eapply POSTM_trans; [exact PM13|]. eapply POSTM_trans; [exact PMs13|]. apply (POSTM_sub C A0 A10 _ _ _ SUB10). apply (POSTM_mono C A10 (s + OFF13) s); [unfold OFF13; lia | exact PMc13]. }
  pose proof (RTR13 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM9) ltac:(clear - HkR'; unfold RK_cml, RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB MG17 RBpos; lia)) as RM10. rewrite !Z.sub_0_r in RM10.
  assert (KEPT13 : Forall (ex_region_kept E13 M13 m14) [(EVar 32, OFF13, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF13 256 M13 m14 E13 (EVar 32) CK (proj1 PMc13) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E13 M13 m14 _ [] _ HKc13 KEPT13) as HKk13.
  match type of HKk13 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E13 m14 kk') in HKk13 end.
  pose proof (regs_ok_agree 478%nat E13 (ex_envL vals13 r14 [exW_canary SEGS 415784 m14]) _ _ (vals_app_agree vals13 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa13.
  pose proof (exW_regs_call _ _ _ _ _ HRa13 (ex_regs_ok_junk vals13 r14 [exW_canary SEGS 415784 m14] 478%nat ltac:(vm_cast_no_check (eq_refl 478%nat))) CS13) as HRn14.
  clear HRa13.
  assert (HKa14 : know_ok SEGS (ex_envL vals13 r14 [exW_canary SEGS 415784 m14]) m14 _) by (exact (know_ok_agree SEGS 478%nat E13 _ m14 _ (vals_app_agree vals13 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk13)).
  rewrite (fr_denot_agree 478%nat E13 (ex_envL vals13 r14 [exW_canary SEGS 415784 m14]) _ fr2 (vals_app_agree vals13 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc13 HKk13 KEPT13 HC13 HWs13 PMs13 Q10_13 Q1_13 Q2_13 Q4_13 PM13 HW13 FRs13 PMc13 CS13 SUB9 RM9 Ldead13 LEQ13 RTR13 Lbufs2_a9 OFF13 LDEL9 Lpixs_a9 Ldata_a9 Lpixd_a9 Ldatad_a9 Ltabval_a9 Ltab38_a9 Ltab14_a9 Lcmd_a9 Larrd_a9 PXdM13 PXd13 PXtM13 PXt13 CMPM13 CMP13.
  subst M13. clear log13. clear E13. try clear Rc13. clear KN13.
  lazymatch type of HRn14 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn14 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A10 m14 _ (s - 256) (Z.to_nat 256) CK HW14 GLO1 GLO2) as SOK14.
  pose proof (exW_canary_ok SEGS 415784 m14 (canary_any m14)) as CANOK14.
  pose (vals14 := vals13 ++ map (getr r14) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m14]).
  pose proof (exW_kn_fixed SEGS C A10 m14 _ (ex_envL vals13 r14 [exW_canary SEGS 415784 m14]) (EVar 510) (EVar 32) (exW_canary SEGS 415784 m14) s 256 415784 65536 212992 213416 213568 213416 213568
                HW14 eq_refl (proj1 CANOK14) (proj2 CANOK14) eq_refl eq_refl eq_refl SOK14 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf14.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf14 HKa14)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn14 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN14 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf14 HKa14 SOK14 CANOK14.
  repeat match goal with H : getr r14 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc14 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E14 := EEx) in HR, Hlf, HK, Hms |- *; set (log14 := LLx) in Hms, Hlf; set (M14 := mem_denot E14 m14 log14) in Hms end.
  assert (WP14 : W C A10 M14 (with_vmmaps vm10 md) /\ POSTM C A0 s m14 M14).
  { subst M14. apply (exW_win_blks C A10 A0 m14 _ E14 log14 (EVar 32) s 256 [] CK HW14 SUB10 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP14 as [HWs14 PMs14].
  pose proof (exW_win_only E14 m14 log14 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs14. change (mem_denot E14 m14 log14) with M14 in FRs14.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log14 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC14 : carry log14 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc14 : know_ok SEGS E14 M14 kn1) by (apply (carry_after SEGS E14 m14 log14 kn0 [] kn1 scs hs HC14 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW14)) | exact (mp_lazy _ (w_pure _ _ _ _ HW14)) | exact Hms |].
  pose (BS14 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, data); (173%nat, wpl_of w 8); (207%nat, bufs1); (241%nat, bufs2); (275%nat, tabval); (309%nat, tab38); (343%nat, tab14); (410%nat, cmd)]).
  exW_regfactB BS14 HR ex_r10 Q10_14. exW_regfactB BS14 HR ex_r1 Q1_14. exW_regfactB BS14 HR ex_r2 Q2_14. exW_regfactB BS14 HR ex_r4 Q4_14.
  clear BS14.
  lazymatch type of Q2_14 with _ = Z_to_bv 64 (s + ?off) => pose (OFF14 := off) end.
  (* [comment removed for export] *)
  assert (PXdM14 : PIXat M14 pixd (set_cmap (set_data (pix_hdr w h 2) datad) cmd)) by exact (exT_pix_sess C A10 m14 M14 _ s 256 pixd _ CK HW14 GLO1 Lpixd_a10 PXd14 FRs14).
  assert (PXtM14 : PIXat M14 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_sess C A10 m14 M14 _ s 256 pixs _ CK HW14 GLO1 Lpixs_a10 PXt14 FRs14).
  assert (CMPM14 : CMAPat M14 cmd (CMAPV arrd 2 4 4 0)) by exact (exT_cmap_sess C A10 m14 M14 _ s 256 cmd _ CK HW14 GLO1 Lcmd_a10 CMP14 FRs14).
  lazymatch type of Q1_14 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_14 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A10 M14 _ Rc14 (Z_to_bv 64 tabval) (Z_to_bv 64 ret) (1024) sp' S CK HWs14 Q10_14 Ltabval_a10 F0tabval Q1_14
             ltac:(red; apply bv_eq; reflexivity) Q4_14 Q2_14 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF14, ALLOC_STACK; clear - Hlo1; lia) ltac:(unfold OFF14; clear - Hhi; lia)) end end end.
  intros A11 m15 vm11 r15 HW15 CSx14 Ldead14 LEQ14 PMc14 RTR14.
  pose proof CSx14 as CS14. clear CSx14.
  rewrite with_vmmaps_twice in HW15 |- *.
  assert (SUB11 : sub_live A0 A11).
  { intros q0 kq Lq. rewrite (LEQ14 q0 (ne_live A0 q0 _ kq Lq Ftabval)). exact (SUB10 q0 kq Lq). }
  assert (LDEL11 : forall q0 : word, ~ In q0 [Z_to_bv 64 cmd; Z_to_bv 64 arrd; Z_to_bv 64 tab14; Z_to_bv 64 tab38; Z_to_bv 64 pixd; Z_to_bv 64 datad] -> live A11 q0 = live A0 q0).
  { intros q0 Hq. destruct (decide (Z_to_bv 64 tabval = q0)) as [<-|NEq]; [rewrite Ldead14, Ftabval; reflexivity|]. rewrite (LEQ14 q0 (fun EE => NEq (eq_sym EE))). apply LDEL10. clear - Hq NEq. cbn [In] in *. tauto. }
  pose proof (eq_trans (LEQ14 _ NE_pixs_tabval) Lpixs_a10) as Lpixs_a11.
  pose proof (eq_trans (LEQ14 _ NE_data_tabval) Ldata_a10) as Ldata_a11.
  pose proof (eq_trans (LEQ14 _ NE_pixd_tabval) Lpixd_a10) as Lpixd_a11.
  pose proof (eq_trans (LEQ14 _ NE_datad_tabval) Ldatad_a10) as Ldatad_a11.
  pose proof (eq_trans (LEQ14 _ (fun EE => NE_tabval_tab38 (eq_sym EE))) Ltab38_a10) as Ltab38_a11.
  pose proof (eq_trans (LEQ14 _ (fun EE => NE_tabval_tab14 (eq_sym EE))) Ltab14_a10) as Ltab14_a11.
  pose proof (eq_trans (LEQ14 _ (fun EE => NE_tabval_cmd (eq_sym EE))) Lcmd_a10) as Lcmd_a11.
  pose proof (eq_trans (LEQ14 _ (fun EE => NE_tabval_arrd (eq_sym EE))) Larrd_a10) as Larrd_a11.
  assert (PXd15 : PIXat m15 pixd (set_cmap (set_data (pix_hdr w h 2) datad) cmd)) by exact (exT_pix_livk A11 M14 m15 pixd _ PXdM14 (proj2 PMc14) Lpixd_a11).
  assert (PXt15 : PIXat m15 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_livk A11 M14 m15 pixs _ PXtM14 (proj2 PMc14) Lpixs_a11).
  assert (CMP15 : CMAPat m15 cmd (CMAPV arrd 2 4 4 0)) by exact (exT_cmap_livk A11 M14 m15 cmd _ CMPM14 (proj2 PMc14) Lcmd_a11).
  assert (PM15 : POSTM C A0 s m4 m15).
  { eapply POSTM_trans; [exact PM14|]. eapply POSTM_trans; [exact PMs14|]. apply (POSTM_sub C A0 A11 _ _ _ SUB11). apply (POSTM_mono C A11 (s + OFF14) s); [unfold OFF14; lia | exact PMc14]. }
  pose proof (RTR14 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM10) ltac:(clear - HkR'; unfold RK_cml, RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB MG17 RBpos; lia)) as RM11. rewrite !Z.sub_0_r in RM11.
  assert (KEPT14 : Forall (ex_region_kept E14 M14 m15) [(EVar 32, OFF14, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF14 256 M14 m15 E14 (EVar 32) CK (proj1 PMc14) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E14 M14 m15 _ [] _ HKc14 KEPT14) as HKk14.
  match type of HKk14 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E14 m15 kk') in HKk14 end.
  pose proof (regs_ok_agree 511%nat E14 (ex_envL vals14 r15 [exW_canary SEGS 415784 m15]) _ _ (vals_app_agree vals14 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa14.
  pose proof (exW_regs_call _ _ _ _ _ HRa14 (ex_regs_ok_junk vals14 r15 [exW_canary SEGS 415784 m15] 511%nat ltac:(vm_cast_no_check (eq_refl 511%nat))) CS14) as HRn15.
  clear HRa14.
  assert (HKa15 : know_ok SEGS (ex_envL vals14 r15 [exW_canary SEGS 415784 m15]) m15 _) by (exact (know_ok_agree SEGS 511%nat E14 _ m15 _ (vals_app_agree vals14 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk14)).
  rewrite (fr_denot_agree 511%nat E14 (ex_envL vals14 r15 [exW_canary SEGS 415784 m15]) _ fr2 (vals_app_agree vals14 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc14 HKk14 KEPT14 HC14 HWs14 PMs14 Q10_14 Q1_14 Q2_14 Q4_14 PM14 HW14 FRs14 PMc14 CS14 SUB10 RM10 Ldead14 LEQ14 RTR14 Ltabval_a10 OFF14 LDEL10 Lpixs_a10 Ldata_a10 Lpixd_a10 Ldatad_a10 Ltab38_a10 Ltab14_a10 Lcmd_a10 Larrd_a10 PXdM14 PXd14 PXtM14 PXt14 CMPM14 CMP14.
  subst M14. clear log14. clear E14. try clear Rc14. clear KN14.
  lazymatch type of HRn15 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn15 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A11 m15 _ (s - 256) (Z.to_nat 256) CK HW15 GLO1 GLO2) as SOK15.
  pose proof (exW_canary_ok SEGS 415784 m15 (canary_any m15)) as CANOK15.
  pose (vals15 := vals14 ++ map (getr r15) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m15]).
  pose proof (exW_kn_fixed SEGS C A11 m15 _ (ex_envL vals14 r15 [exW_canary SEGS 415784 m15]) (EVar 543) (EVar 32) (exW_canary SEGS 415784 m15) s 256 415784 65536 212992 213416 213568 213416 213568
                HW15 eq_refl (proj1 CANOK15) (proj2 CANOK15) eq_refl eq_refl eq_refl SOK15 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf15.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf15 HKa15)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn15 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN15 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf15 HKa15 SOK15 CANOK15.
  repeat match goal with H : getr r15 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc15 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E15 := EEx) in HR, Hlf, HK, Hms |- *; set (log15 := LLx) in Hms, Hlf; set (M15 := mem_denot E15 m15 log15) in Hms end.
  assert (WP15 : W C A11 M15 (with_vmmaps vm11 md) /\ POSTM C A0 s m15 M15).
  { subst M15. apply (exW_win_blks C A11 A0 m15 _ E15 log15 (EVar 32) s 256 [] CK HW15 SUB11 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP15 as [HWs15 PMs15].
  pose proof (exW_win_only E15 m15 log15 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs15. change (mem_denot E15 m15 log15) with M15 in FRs15.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log15 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC15 : carry log15 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc15 : know_ok SEGS E15 M15 kn1) by (apply (carry_after SEGS E15 m15 log15 kn0 [] kn1 scs hs HC15 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW15)) | exact (mp_lazy _ (w_pure _ _ _ _ HW15)) | exact Hms |].
  pose (BS15 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, data); (173%nat, wpl_of w 8); (207%nat, bufs1); (241%nat, bufs2); (275%nat, tabval); (309%nat, tab38); (343%nat, tab14); (410%nat, cmd)]).
  exW_regfactB BS15 HR ex_r10 Q10_15. exW_regfactB BS15 HR ex_r1 Q1_15. exW_regfactB BS15 HR ex_r2 Q2_15. exW_regfactB BS15 HR ex_r4 Q4_15.
  clear BS15.
  lazymatch type of Q2_15 with _ = Z_to_bv 64 (s + ?off) => pose (OFF15 := off) end.
  (* [comment removed for export] *)
  assert (PXdM15 : PIXat M15 pixd (set_cmap (set_data (pix_hdr w h 2) datad) cmd)) by exact (exT_pix_sess C A11 m15 M15 _ s 256 pixd _ CK HW15 GLO1 Lpixd_a11 PXd15 FRs15).
  assert (PXtM15 : PIXat M15 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_sess C A11 m15 M15 _ s 256 pixs _ CK HW15 GLO1 Lpixs_a11 PXt15 FRs15).
  assert (CMPM15 : CMAPat M15 cmd (CMAPV arrd 2 4 4 0)) by exact (exT_cmap_sess C A11 m15 M15 _ s 256 cmd _ CK HW15 GLO1 Lcmd_a11 CMP15 FRs15).
  lazymatch type of Q1_15 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_15 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A11 M15 _ Rc15 (Z_to_bv 64 tab38) (Z_to_bv 64 ret) (1024) sp' S CK HWs15 Q10_15 Ltab38_a11 F0tab38 Q1_15
             ltac:(red; apply bv_eq; reflexivity) Q4_15 Q2_15 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF15, ALLOC_STACK; clear - Hlo1; lia) ltac:(unfold OFF15; clear - Hhi; lia)) end end end.
  intros A12 m16 vm12 r16 HW16 CSx15 Ldead15 LEQ15 PMc15 RTR15.
  pose proof CSx15 as CS15. clear CSx15.
  rewrite with_vmmaps_twice in HW16 |- *.
  assert (SUB12 : sub_live A0 A12).
  { intros q0 kq Lq. rewrite (LEQ15 q0 (ne_live A0 q0 _ kq Lq Ftab38)). exact (SUB11 q0 kq Lq). }
  assert (LDEL12 : forall q0 : word, ~ In q0 [Z_to_bv 64 cmd; Z_to_bv 64 arrd; Z_to_bv 64 tab14; Z_to_bv 64 pixd; Z_to_bv 64 datad] -> live A12 q0 = live A0 q0).
  { intros q0 Hq. destruct (decide (Z_to_bv 64 tab38 = q0)) as [<-|NEq]; [rewrite Ldead15, Ftab38; reflexivity|]. rewrite (LEQ15 q0 (fun EE => NEq (eq_sym EE))). apply LDEL11. clear - Hq NEq. cbn [In] in *. tauto. }
  pose proof (eq_trans (LEQ15 _ NE_pixs_tab38) Lpixs_a11) as Lpixs_a12.
  pose proof (eq_trans (LEQ15 _ NE_data_tab38) Ldata_a11) as Ldata_a12.
  pose proof (eq_trans (LEQ15 _ NE_pixd_tab38) Lpixd_a11) as Lpixd_a12.
  pose proof (eq_trans (LEQ15 _ NE_datad_tab38) Ldatad_a11) as Ldatad_a12.
  pose proof (eq_trans (LEQ15 _ (fun EE => NE_tab38_tab14 (eq_sym EE))) Ltab14_a11) as Ltab14_a12.
  pose proof (eq_trans (LEQ15 _ (fun EE => NE_tab38_cmd (eq_sym EE))) Lcmd_a11) as Lcmd_a12.
  pose proof (eq_trans (LEQ15 _ (fun EE => NE_tab38_arrd (eq_sym EE))) Larrd_a11) as Larrd_a12.
  assert (PXd16 : PIXat m16 pixd (set_cmap (set_data (pix_hdr w h 2) datad) cmd)) by exact (exT_pix_livk A12 M15 m16 pixd _ PXdM15 (proj2 PMc15) Lpixd_a12).
  assert (PXt16 : PIXat m16 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_livk A12 M15 m16 pixs _ PXtM15 (proj2 PMc15) Lpixs_a12).
  assert (CMP16 : CMAPat m16 cmd (CMAPV arrd 2 4 4 0)) by exact (exT_cmap_livk A12 M15 m16 cmd _ CMPM15 (proj2 PMc15) Lcmd_a12).
  assert (PM16 : POSTM C A0 s m4 m16).
  { eapply POSTM_trans; [exact PM15|]. eapply POSTM_trans; [exact PMs15|]. apply (POSTM_sub C A0 A12 _ _ _ SUB12). apply (POSTM_mono C A12 (s + OFF15) s); [unfold OFF15; lia | exact PMc15]. }
  pose proof (RTR15 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM11) ltac:(clear - HkR'; unfold RK_cml, RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB MG17 RBpos; lia)) as RM12. rewrite !Z.sub_0_r in RM12.
  assert (KEPT15 : Forall (ex_region_kept E15 M15 m16) [(EVar 32, OFF15, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF15 256 M15 m16 E15 (EVar 32) CK (proj1 PMc15) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E15 M15 m16 _ [] _ HKc15 KEPT15) as HKk15.
  match type of HKk15 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E15 m16 kk') in HKk15 end.
  pose proof (regs_ok_agree 544%nat E15 (ex_envL vals15 r16 [exW_canary SEGS 415784 m16]) _ _ (vals_app_agree vals15 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa15.
  pose proof (exW_regs_call _ _ _ _ _ HRa15 (ex_regs_ok_junk vals15 r16 [exW_canary SEGS 415784 m16] 544%nat ltac:(vm_cast_no_check (eq_refl 544%nat))) CS15) as HRn16.
  clear HRa15.
  assert (HKa16 : know_ok SEGS (ex_envL vals15 r16 [exW_canary SEGS 415784 m16]) m16 _) by (exact (know_ok_agree SEGS 544%nat E15 _ m16 _ (vals_app_agree vals15 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk15)).
  rewrite (fr_denot_agree 544%nat E15 (ex_envL vals15 r16 [exW_canary SEGS 415784 m16]) _ fr2 (vals_app_agree vals15 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc15 HKk15 KEPT15 HC15 HWs15 PMs15 Q10_15 Q1_15 Q2_15 Q4_15 PM15 HW15 FRs15 PMc15 CS15 SUB11 RM11 Ldead15 LEQ15 RTR15 Ltab38_a11 OFF15 LDEL11 Lpixs_a11 Ldata_a11 Lpixd_a11 Ldatad_a11 Ltab14_a11 Lcmd_a11 Larrd_a11 PXdM15 PXd15 PXtM15 PXt15 CMPM15 CMP15.
  subst M15. clear log15. clear E15. try clear Rc15. clear KN15.
  lazymatch type of HRn16 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn16 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A12 m16 _ (s - 256) (Z.to_nat 256) CK HW16 GLO1 GLO2) as SOK16.
  pose proof (exW_canary_ok SEGS 415784 m16 (canary_any m16)) as CANOK16.
  pose (vals16 := vals15 ++ map (getr r16) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m16]).
  pose proof (exW_kn_fixed SEGS C A12 m16 _ (ex_envL vals15 r16 [exW_canary SEGS 415784 m16]) (EVar 576) (EVar 32) (exW_canary SEGS 415784 m16) s 256 415784 65536 212992 213416 213568 213416 213568
                HW16 eq_refl (proj1 CANOK16) (proj2 CANOK16) eq_refl eq_refl eq_refl SOK16 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf16.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf16 HKa16)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn16 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN16 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf16 HKa16 SOK16 CANOK16.
  repeat match goal with H : getr r16 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc16 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E16 := EEx) in HR, Hlf, HK, Hms |- *; set (log16 := LLx) in Hms, Hlf; set (M16 := mem_denot E16 m16 log16) in Hms end.
  assert (WP16 : W C A12 M16 (with_vmmaps vm12 md) /\ POSTM C A0 s m16 M16).
  { subst M16. apply (exW_win_blks C A12 A0 m16 _ E16 log16 (EVar 32) s 256 [] CK HW16 SUB12 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP16 as [HWs16 PMs16].
  pose proof (exW_win_only E16 m16 log16 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs16. change (mem_denot E16 m16 log16) with M16 in FRs16.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log16 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC16 : carry log16 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc16 : know_ok SEGS E16 M16 kn1) by (apply (carry_after SEGS E16 m16 log16 kn0 [] kn1 scs hs HC16 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW16)) | exact (mp_lazy _ (w_pure _ _ _ _ HW16)) | exact Hms |].
  pose (BS16 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, data); (173%nat, wpl_of w 8); (207%nat, bufs1); (241%nat, bufs2); (275%nat, tabval); (309%nat, tab38); (343%nat, tab14); (410%nat, cmd)]).
  exW_regfactB BS16 HR ex_r10 Q10_16. exW_regfactB BS16 HR ex_r1 Q1_16. exW_regfactB BS16 HR ex_r2 Q2_16. exW_regfactB BS16 HR ex_r4 Q4_16.
  clear BS16.
  lazymatch type of Q2_16 with _ = Z_to_bv 64 (s + ?off) => pose (OFF16 := off) end.
  (* [comment removed for export] *)
  assert (PXdM16 : PIXat M16 pixd (set_cmap (set_data (pix_hdr w h 2) datad) cmd)) by exact (exT_pix_sess C A12 m16 M16 _ s 256 pixd _ CK HW16 GLO1 Lpixd_a12 PXd16 FRs16).
  assert (PXtM16 : PIXat M16 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_sess C A12 m16 M16 _ s 256 pixs _ CK HW16 GLO1 Lpixs_a12 PXt16 FRs16).
  assert (CMPM16 : CMAPat M16 cmd (CMAPV arrd 2 4 4 0)) by exact (exT_cmap_sess C A12 m16 M16 _ s 256 cmd _ CK HW16 GLO1 Lcmd_a12 CMP16 FRs16).
  lazymatch type of Q1_16 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_16 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A12 M16 _ Rc16 (Z_to_bv 64 tab14) (Z_to_bv 64 ret) (1024) sp' S CK HWs16 Q10_16 Ltab14_a12 F0tab14 Q1_16
             ltac:(red; apply bv_eq; reflexivity) Q4_16 Q2_16 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF16, ALLOC_STACK; clear - Hlo1; lia) ltac:(unfold OFF16; clear - Hhi; lia)) end end end.
  intros A13 m17 vm13 r17 HW17 CSx16 Ldead16 LEQ16 PMc16 RTR16.
  pose proof CSx16 as CS16. clear CSx16.
  rewrite with_vmmaps_twice in HW17 |- *.
  assert (SUB13 : sub_live A0 A13).
  { intros q0 kq Lq. rewrite (LEQ16 q0 (ne_live A0 q0 _ kq Lq Ftab14)). exact (SUB12 q0 kq Lq). }
  assert (LDEL13 : forall q0 : word, ~ In q0 [Z_to_bv 64 cmd; Z_to_bv 64 arrd; Z_to_bv 64 pixd; Z_to_bv 64 datad] -> live A13 q0 = live A0 q0).
  { intros q0 Hq. destruct (decide (Z_to_bv 64 tab14 = q0)) as [<-|NEq]; [rewrite Ldead16, Ftab14; reflexivity|]. rewrite (LEQ16 q0 (fun EE => NEq (eq_sym EE))). apply LDEL12. clear - Hq NEq. cbn [In] in *. tauto. }
  pose proof (eq_trans (LEQ16 _ NE_pixs_tab14) Lpixs_a12) as Lpixs_a13.
  pose proof (eq_trans (LEQ16 _ NE_data_tab14) Ldata_a12) as Ldata_a13.
  pose proof (eq_trans (LEQ16 _ NE_pixd_tab14) Lpixd_a12) as Lpixd_a13.
  pose proof (eq_trans (LEQ16 _ NE_datad_tab14) Ldatad_a12) as Ldatad_a13.
  pose proof (eq_trans (LEQ16 _ (fun EE => NE_tab14_cmd (eq_sym EE))) Lcmd_a12) as Lcmd_a13.
  pose proof (eq_trans (LEQ16 _ (fun EE => NE_tab14_arrd (eq_sym EE))) Larrd_a12) as Larrd_a13.
  assert (PXd17 : PIXat m17 pixd (set_cmap (set_data (pix_hdr w h 2) datad) cmd)) by exact (exT_pix_livk A13 M16 m17 pixd _ PXdM16 (proj2 PMc16) Lpixd_a13).
  assert (PXt17 : PIXat m17 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_livk A13 M16 m17 pixs _ PXtM16 (proj2 PMc16) Lpixs_a13).
  assert (CMP17 : CMAPat m17 cmd (CMAPV arrd 2 4 4 0)) by exact (exT_cmap_livk A13 M16 m17 cmd _ CMPM16 (proj2 PMc16) Lcmd_a13).
  assert (PM17 : POSTM C A0 s m4 m17).
  { eapply POSTM_trans; [exact PM16|]. eapply POSTM_trans; [exact PMs16|]. apply (POSTM_sub C A0 A13 _ _ _ SUB13). apply (POSTM_mono C A13 (s + OFF16) s); [unfold OFF16; lia | exact PMc16]. }
  pose proof (RTR16 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM12) ltac:(clear - HkR'; unfold RK_cml, RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB MG17 RBpos; lia)) as RM13. rewrite !Z.sub_0_r in RM13.
  assert (KEPT16 : Forall (ex_region_kept E16 M16 m17) [(EVar 32, OFF16, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF16 256 M16 m17 E16 (EVar 32) CK (proj1 PMc16) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E16 M16 m17 _ [] _ HKc16 KEPT16) as HKk16.
  match type of HKk16 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E16 m17 kk') in HKk16 end.
  pose proof (regs_ok_agree 577%nat E16 (ex_envL vals16 r17 [exW_canary SEGS 415784 m17]) _ _ (vals_app_agree vals16 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa16.
  pose proof (exW_regs_call _ _ _ _ _ HRa16 (ex_regs_ok_junk vals16 r17 [exW_canary SEGS 415784 m17] 577%nat ltac:(vm_cast_no_check (eq_refl 577%nat))) CS16) as HRn17.
  clear HRa16.
  assert (HKa17 : know_ok SEGS (ex_envL vals16 r17 [exW_canary SEGS 415784 m17]) m17 _) by (exact (know_ok_agree SEGS 577%nat E16 _ m17 _ (vals_app_agree vals16 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk16)).
  rewrite (fr_denot_agree 577%nat E16 (ex_envL vals16 r17 [exW_canary SEGS 415784 m17]) _ fr2 (vals_app_agree vals16 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc16 HKk16 KEPT16 HC16 HWs16 PMs16 Q10_16 Q1_16 Q2_16 Q4_16 PM16 HW16 FRs16 PMc16 CS16 SUB12 RM12 Ldead16 LEQ16 RTR16 Ltab14_a12 OFF16 LDEL12 Lpixs_a12 Ldata_a12 Lpixd_a12 Ldatad_a12 Lcmd_a12 Larrd_a12 PXdM16 PXd16 PXtM16 PXt16 CMPM16 CMP16.
  subst M16. clear log16. clear E16. try clear Rc16. clear KN16.
  lazymatch type of HRn17 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn17 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A13 m17 _ (s - 256) (Z.to_nat 256) CK HW17 GLO1 GLO2) as SOK17.
  pose proof (exW_canary_ok SEGS 415784 m17 (canary_any m17)) as CANOK17.
  pose (vals17 := vals16 ++ map (getr r17) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m17]).
  pose proof (exW_kn_fixed SEGS C A13 m17 _ (ex_envL vals16 r17 [exW_canary SEGS 415784 m17]) (EVar 609) (EVar 32) (exW_canary SEGS 415784 m17) s 256 415784 65536 212992 213416 213568 213416 213568
                HW17 eq_refl (proj1 CANOK17) (proj2 CANOK17) eq_refl eq_refl eq_refl SOK17 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf17.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf17 HKa17)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn17 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN17 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf17 HKa17 SOK17 CANOK17.
  repeat match goal with H : getr r17 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc17 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E17 := EEx) in HR, Hlf, HK, Hms |- *; set (log17 := LLx) in Hms, Hlf; set (M17 := mem_denot E17 m17 log17) in Hms end.
  assert (WP17 : W C A13 M17 (with_vmmaps vm13 md) /\ POSTM C A0 s m17 M17).
  { subst M17. apply (exW_win_blks C A13 A0 m17 _ E17 log17 (EVar 32) s 256 [] CK HW17 SUB13 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP17 as [HWs17 PMs17].
  pose proof (exW_win_only E17 m17 log17 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs17. change (mem_denot E17 m17 log17) with M17 in FRs17.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log17 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC17 : carry log17 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc17 : know_ok SEGS E17 M17 kn1) by (apply (carry_after SEGS E17 m17 log17 kn0 [] kn1 scs hs HC17 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW17)) | exact (mp_lazy _ (w_pure _ _ _ _ HW17)) | exact Hms |].
  pose (BS17 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, data); (173%nat, wpl_of w 8); (207%nat, bufs1); (241%nat, bufs2); (275%nat, tabval); (309%nat, tab38); (343%nat, tab14); (410%nat, cmd)]).
  exW_regfactB BS17 HR ex_r10 Q10_17. exW_regfactB BS17 HR ex_r1 Q1_17. exW_regfactB BS17 HR ex_r2 Q2_17. exW_regfactB BS17 HR ex_r4 Q4_17.
  clear BS17.
  lazymatch type of Q2_17 with _ = Z_to_bv 64 (s + ?off) => pose (OFF17 := off) end.
  (* [comment removed for export] *)
  pose (BSx17 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, data); (173%nat, wpl_of w 8); (207%nat, bufs1); (241%nat, bufs2); (275%nat, tabval); (309%nat, tab38); (343%nat, tab14); (410%nat, cmd)]).
  exW_cellB HK Hlf r0 BSx17 (EVar 32) s (-128)%Z 8%nat CELLpp.
  clear BSx17.
  assert (PXdM17 : PIXat M17 pixd (set_cmap (set_data (pix_hdr w h 2) datad) cmd)) by exact (exT_pix_sess C A13 m17 M17 _ s 256 pixd _ CK HW17 GLO1 Lpixd_a13 PXd17 FRs17).
  assert (PXtM17 : PIXat M17 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_sess C A13 m17 M17 _ s 256 pixs _ CK HW17 GLO1 Lpixs_a13 PXt17 FRs17).
  assert (CMPM17 : CMAPat M17 cmd (CMAPV arrd 2 4 4 0)) by exact (exT_cmap_sess C A13 m17 M17 _ s 256 cmd _ CK HW17 GLO1 Lcmd_a13 CMP17 FRs17).
  assert (PPlo : (s + OFF17 <= s + -128)%Z) by (unfold OFF17; lia). assert (PPhi : (s + -128 + 8 <= c_top C)%Z) by lia.
  lazymatch type of Q1_17 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixDestroy_rc2s_W fxk C A13 M17 _ Rc17 (s + OFF17)%Z (s + -128)%Z pixs (set_rc (hdv w h 8 0 data) 2) (Z_to_bv 64 ra) S CK HWs17 Q2_17
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF17, PXD2_STACK, ALLOC_STACK; clear - Hlo1; lia) PPlo PPhi ltac:(rewrite <- Zplus_mod_idemp_l, Hs8; reflexivity) Q1_17 ltac:(red; apply bv_eq; reflexivity) Q10_17 CELLpp
             PXtM17 eq_refl Lpixs_a13 F0pixs) end end.
  intros m18 r18 HW18 CSx17 PMD FRMs17.
  pose proof CSx17 as CS17. clear CSx17.
  assert (PMB18 : POSTM C A0 s m0 m18).
  { apply (CLONEK A13 M17 m18 _ (s + -128)%Z HWs17 SUB13 ltac:(lia) ltac:(lia) ltac:(lia) (POSTM_trans _ _ _ _ _ _ PM17 PMs17) PMD). }
  assert (PXd18 : PIXat m18 pixd (set_cmap (set_data (pix_hdr w h 2) datad) cmd)) by exact (exT_pix_patch2 C A13 A13 M17 m18 _ pixd pixs 64 (pixs + 20) (s + -128) (Z_to_le_bytes 4 1) (Z_to_le_bytes 8 0) _ CK HWs17 Lpixd_a13 Lpixs_a13 NE_pixd_pixs RRpixs ltac:(lia) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) PXdM17 (proj2 PMD) Lpixd_a13).
  assert (CMP18 : CMAPat m18 cmd (CMAPV arrd 2 4 4 0)) by exact (exT_cmap_patch2 C A13 A13 M17 m18 _ cmd pixs 64 (pixs + 20) (s + -128) (Z_to_le_bytes 4 1) (Z_to_le_bytes 8 0) _ CK HWs17 Lcmd_a13 Lpixs_a13 (fun EE => NE_pixs_cmd (eq_sym EE)) RRpixs ltac:(lia) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) CMPM17 (proj2 PMD) Lcmd_a13).
  assert (FRMx17 : FRM C (s + -120) (wbytes (wbytes M17 (Z_to_bv 64 (pixs + 20)) (Z_to_le_bytes 4 1)) (Z_to_bv 64 (s + -128)) (Z_to_le_bytes 8 0)) m18).
  { replace (s + -120)%Z with (s + -128 + 8)%Z by lia. exact (proj1 PMD). }
  pose proof (POSTM_refl C A0 s m18) as PM18.
  assert (KEPT17 : Forall (ex_region_kept E17 M17 m18) [(EVar 32, (-120)%Z, 0%Z); (EVar 32, OFF17, (-128)%Z)]).
  { constructor; [exact (exT_kept_patch2 C A13 _ s (-120) 256 M17 m18 E17 (EVar 32) pixs 64 (pixs + 20) (s + -128) (Z_to_le_bytes 4 1) (Z_to_le_bytes 8 0) CK HWs17 Lpixs_a13 RRpixs ltac:(lia) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) FRMx17 Hlo Hhi eq_refl eq_refl eq_refl ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia))|]. constructor; [exact (exT_kept_in E17 M17 m18 (EVar 32) s OFF17 (-128) (s + OFF17) (s + -128) FRMs17 eq_refl RS (Z.le_refl _) (Z.le_refl _))|]. constructor. }
  pose proof (ex_know_keepD SEGS E17 M17 m18 _ [] _ HKc17 KEPT17) as HKk17.
  match type of HKk17 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E17 m18 kk') in HKk17 end.
  pose proof (regs_ok_agree 610%nat E17 (ex_envL vals17 r18 [exW_canary SEGS 415784 m18]) _ _ (vals_app_agree vals17 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa17.
  pose proof (exW_regs_call _ _ _ _ _ HRa17 (ex_regs_ok_junk vals17 r18 [exW_canary SEGS 415784 m18] 610%nat ltac:(vm_cast_no_check (eq_refl 610%nat))) CS17) as HRn18.
  clear HRa17.
  assert (HKa18 : know_ok SEGS (ex_envL vals17 r18 [exW_canary SEGS 415784 m18]) m18 _) by (exact (know_ok_agree SEGS 610%nat E17 _ m18 _ (vals_app_agree vals17 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk17)).
  rewrite (fr_denot_agree 610%nat E17 (ex_envL vals17 r18 [exW_canary SEGS 415784 m18]) _ fr2 (vals_app_agree vals17 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc17 HKk17 KEPT17 HC17 HWs17 PMs17 Q10_17 Q1_17 Q2_17 Q4_17 PM17 HW17 FRs17 CS17 OFF17 CELLpp PPlo PPhi PXdM17 PXd17 PXtM17 PXt17 CMPM17 CMP17 PMD FRMx17 CLONEK FRMs17.
  subst M17. clear log17. clear E17. try clear Rc17. clear KN17.
  lazymatch type of HRn18 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn18 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A13 m18 _ (s - 256) (Z.to_nat 256) CK HW18 GLO1 GLO2) as SOK18.
  pose proof (exW_canary_ok SEGS 415784 m18 (canary_any m18)) as CANOK18.
  pose (vals18 := vals17 ++ map (getr r18) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m18]).
  pose proof (exW_kn_fixed SEGS C A13 m18 _ (ex_envL vals17 r18 [exW_canary SEGS 415784 m18]) (EVar 642) (EVar 32) (exW_canary SEGS 415784 m18) s 256 415784 65536 212992 213416 213568 213416 213568
                HW18 eq_refl (proj1 CANOK18) (proj2 CANOK18) eq_refl eq_refl eq_refl SOK18 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf18.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf18 HKa18)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn18 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN18 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf18 HKa18 SOK18 CANOK18.
  repeat match goal with H : getr r18 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E18 := EEx) in HR, Hlf, HK, Hms |- *; set (log18 := LLx) in Hms, Hlf; set (M18 := mem_denot E18 m18 log18) in Hms end.
  assert (WP18 : W C A13 M18 (with_vmmaps vm13 md) /\ POSTM C A0 s m18 M18).
  { subst M18. apply (exW_win_blks C A13 A0 m18 _ E18 log18 (EVar 32) s 256 [] CK HW18 SUB13 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP18 as [HWs18 PMs18].
  pose proof (exW_win_only E18 m18 log18 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs18. change (mem_denot E18 m18 log18) with M18 in FRs18.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW18)) | exact (mp_lazy _ (w_pure _ _ _ _ HW18)) | exact Hms |].
  pose (BSF := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, data); (173%nat, wpl_of w 8); (207%nat, bufs1); (241%nat, bufs2); (275%nat, tabval); (309%nat, tab38); (343%nat, tab14); (410%nat, cmd)]).
  exW_regfactB BSF HR ex_r10 G10.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ => apply (HC fxk A13 M18 vm13 RcF FZ HWs18) end.
  + lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 RcF [(2%nat, EVar 32); (4%nat, ELit 284096)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor; [symmetry; exact HTP | constructor]] | vm_compute; reflexivity] end.
  + exact (POSTM_trans _ _ _ _ _ _ PMB18 PMs18).
  + right. exists pixd, datad, cmd, (CMAPV arrd 2 4 4 0). split; [exact G10|]. split; [|split; [clear - Gcmd1; lia | split; [reflexivity | split; reflexivity]]].
    refine (conj Gpd1 (conj Gpd2 (conj ALpixd (conj Gdd1 (conj Gdd2 (conj ALdatad (conj NEpd (conj Fpixd (conj Fdatad (conj F0pixd (conj F0datad (conj Lpixd_a13 (conj Ldatad_a13 (conj _ _)))))))))))))).
    * exact (exT_pix_sess C A13 m18 M18 _ s 256 pixd _ CK HW18 GLO1 Lpixd_a13 PXd18 FRs18).
    * right. exists arrd. cbn [c_d c_nalloc c_n].
      refine (conj CMOK (conj Gcmd1 (conj Gcmd2 (conj Garrd1 (conj _ (conj NEcmarr (conj _ (conj _ (conj _ (conj _ (conj Fcmd (conj Farrd (conj F0cmd (conj F0arrd (conj Lcmd_a13 (conj _ (conj _ _))))))))))))))))).
      -- exact Garrd2.
      -- intros EE. exact (NE_pixd_cmd (f_equal (Z_to_bv 64) (eq_sym EE))).
      -- intros EE. exact (NE_datad_cmd (f_equal (Z_to_bv 64) (eq_sym EE))).
      -- intros EE. exact (NE_pixd_arrd (f_equal (Z_to_bv 64) (eq_sym EE))).
      -- intros EE. exact (NE_datad_arrd (f_equal (Z_to_bv 64) (eq_sym EE))).
      -- exact Larrd_a13.
      -- exact (exT_cmap_sess C A13 m18 M18 _ s 256 cmd _ CK HW18 GLO1 Lcmd_a13 CMP18 FRs18).
      -- intros q0 N1 N2 N3 N4. apply LDEL13. clear - N1 N2 N3 N4. cbn [In]. intros [EE|[EE|[EE|[EE|[]]]]]; [apply N3 | apply N4 | apply N1 | apply N2]; symmetry; exact EE.
  + apply (aroom_mono _ _ _ _ _ _ RM13); [unfold RK_d2bpp; clear - HkR'; unfold RK_cml in *; lia | unfold RB_d2bpp; clear - HbR' MGB MG17 RBpos; lia].
  - (* [comment removed for export] *)
    destruct PTN as (Gpt1 & Gpt2 & ALpixt & Gdt1 & Gdt2 & ALdatat & NEptdt & Fpixtx & Fdatatx & F0pixt & F0datat & Lpixt_a2 & Ldatat_a2 & PXt4 & CMR).
    destruct CMR as [(_ & LEQ3) | (ad & _ & XX & _)]; [|exfalso; apply XX; reflexivity].
    assert (RRpixt : (0 <= pixt < 2 ^ 64)%Z) by lia. assert (RRdatat : (0 <= datat < 2 ^ 64)%Z) by lia.
    assert (PMB4 : POSTM C A0 s m0 m4).
    { eapply POSTM_trans; [exact PMB|]. apply (POSTM_sub C A0 A1 _ _ _ SUB1). apply (POSTM_mono C A1 (s + OFF3) s); [unfold OFF3; lia | exact PMc3]. }
    assert (PXd4 : PIXat m4 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_livk A1 M3 m4 pixd _ PXdM3 (proj2 PMc3) Lpixd_a1).
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
  pose (BS4 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, pixt); (173%nat, datat); (174%nat, wpl_of w 8)]).
  exW_regfactB BS4 HR ex_r10 Q10_4. exW_regfactB BS4 HR ex_r11 Q11_4. exW_regfactB BS4 HR ex_r1 Q1_4. exW_regfactB BS4 HR ex_r2 Q2_4. exW_regfactB BS4 HR ex_r4 Q4_4.
  clear BS4.
  lazymatch type of Q2_4 with _ = Z_to_bv 64 (s + ?off) => pose (OFF4 := off) end.
  (* [comment removed for export] *)
  assert (PXdM4 : PIXat M4 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_sess C A2 m4 M4 _ s 256 pixd _ CK HW4 GLO1 Lpixd_a2 PXd4 FRs4).
  assert (PXtM4 : PIXat M4 pixt (hdv w h 8 0 datat)) by exact (exT_pix_sess C A2 m4 M4 _ s 256 pixt _ CK HW4 GLO1 Lpixt_a2 PXt4 FRs4).
  lazymatch type of Q1_4 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_4 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A2 M4 _ Rc4 (wpl_of w 8) 4 (kR - RK_pix - RK_rmc) (bR - RB_pix14 - RB_rmc) (Z_to_bv 64 ret) sp' S CK HWs4 Q10_4 Q11_4 ltac:(clear - Gwpls; lia) ltac:(lia) ltac:(clear - Gwpls; lia)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM2) ltac:(clear - HkR'; unfold RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB MG17 RBpos; lia) ltac:(unfold ROOM_NMAX; clear - Gwpls; lia) Q1_4
             ltac:(red; apply bv_eq; reflexivity) Q4_4 Q2_4 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF4, CALLOC_STACK, ALLOC_STACK; clear - Hlo1; lia) ltac:(unfold OFF4; clear - Hhi; lia)) end end end.
  intros A3 m5 vm3 r5 res4 HW5 Hres4 CSx4 Hnz4 Fbufs1x Lo4 F0bufs1 LEQ4 ZERO4 ALbufs1 TOP4 PMc4 RM3.
  pose proof CSx4 as CS4. clear CSx4.
  rewrite with_vmmaps_twice in HW5 |- *.
  assert (Eres4 : res4 = Z_to_bv 64 (u res4)) by (symmetry; apply zbv_self).
  pose proof (u64_range res4) as RRbufs1. set (bufs1 := u res4) in *. clearbody bufs1. rewrite Eres4 in Hres4, Fbufs1x, Lo4, F0bufs1, LEQ4, ZERO4. clear Eres4 TOP4 Hnz4.
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
  assert (PXd5 : PIXat m5 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_livk A2 M4 m5 pixd _ PXdM4 (proj2 PMc4) Lpixd_a2).
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
  clear HR HK Hlf Hms HKc4 HKk4 KEPT4 HC4 HWs4 PMs4 Q10_4 Q11_4 Q1_4 Q2_4 Q4_4 PM4 HW4 FRs4 PMc4 CS4 SUB2 RM2 LEQ4 Fbufs1x Lo4 OFF4 LDEL2 Hres4 ZERO4 Lpixs_a2 Ldata_a2 Lpixd_a2 Ldatad_a2 Lpixt_a2 Ldatat_a2 PXdM4 PXd4 PXtM4 PXt4.
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
  pose (BS5 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, pixt); (173%nat, datat); (174%nat, wpl_of w 8); (208%nat, bufs1)]).
  exW_regfactB BS5 HR ex_r10 Q10_5. exW_regfactB BS5 HR ex_r11 Q11_5. exW_regfactB BS5 HR ex_r1 Q1_5. exW_regfactB BS5 HR ex_r2 Q2_5. exW_regfactB BS5 HR ex_r4 Q4_5.
  clear BS5.
  lazymatch type of Q2_5 with _ = Z_to_bv 64 (s + ?off) => pose (OFF5 := off) end.
  (* [comment removed for export] *)
  assert (PXdM5 : PIXat M5 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_sess C A3 m5 M5 _ s 256 pixd _ CK HW5 GLO1 Lpixd_a3 PXd5 FRs5).
  assert (PXtM5 : PIXat M5 pixt (hdv w h 8 0 datat)) by exact (exT_pix_sess C A3 m5 M5 _ s 256 pixt _ CK HW5 GLO1 Lpixt_a3 PXt5 FRs5).
  lazymatch type of Q1_5 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_5 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A3 M5 _ Rc5 (wpl_of w 8) 4 (kR - RK_pix - RK_rmc - 1) (bR - RB_pix14 - RB_rmc - alloc_margin (wpl_of w 8 * 4)) (Z_to_bv 64 ret) sp' S CK HWs5 Q10_5 Q11_5 ltac:(clear - Gwpls; lia) ltac:(lia) ltac:(clear - Gwpls; lia)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM3) ltac:(clear - HkR'; unfold RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB MG17 RBpos; lia) ltac:(unfold ROOM_NMAX; clear - Gwpls; lia) Q1_5
             ltac:(red; apply bv_eq; reflexivity) Q4_5 Q2_5 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF5, CALLOC_STACK, ALLOC_STACK; clear - Hlo1; lia) ltac:(unfold OFF5; clear - Hhi; lia)) end end end.
  intros A4 m6 vm4 r6 res5 HW6 Hres5 CSx5 Hnz5 Fbufs2x Lo5 F0bufs2 LEQ5 ZERO5 ALbufs2 TOP5 PMc5 RM4.
  pose proof CSx5 as CS5. clear CSx5.
  rewrite with_vmmaps_twice in HW6 |- *.
  assert (Eres5 : res5 = Z_to_bv 64 (u res5)) by (symmetry; apply zbv_self).
  pose proof (u64_range res5) as RRbufs2. set (bufs2 := u res5) in *. clearbody bufs2. rewrite Eres5 in Hres5, Fbufs2x, Lo5, F0bufs2, LEQ5, ZERO5. clear Eres5 TOP5 Hnz5.
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
  assert (PXd6 : PIXat m6 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_livk A3 M5 m6 pixd _ PXdM5 (proj2 PMc5) Lpixd_a3).
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
  clear HR HK Hlf Hms HKc5 HKk5 KEPT5 HC5 HWs5 PMs5 Q10_5 Q11_5 Q1_5 Q2_5 Q4_5 PM5 HW5 FRs5 PMc5 CS5 SUB3 RM3 LEQ5 Fbufs2x Lo5 OFF5 LDEL3 Hres5 ZERO5 Lpixs_a3 Ldata_a3 Lpixd_a3 Ldatad_a3 Lpixt_a3 Ldatat_a3 Lbufs1_a3 PXdM5 PXd5 PXtM5 PXt5.
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
  pose (BS6 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, pixt); (173%nat, datat); (174%nat, wpl_of w 8); (208%nat, bufs1); (242%nat, bufs2)]).
  exW_regfactB BS6 HR ex_r10 Q10_6. exW_regfactB BS6 HR ex_r11 Q11_6. exW_regfactB BS6 HR ex_r1 Q1_6. exW_regfactB BS6 HR ex_r2 Q2_6. exW_regfactB BS6 HR ex_r4 Q4_6.
  clear BS6.
  lazymatch type of Q2_6 with _ = Z_to_bv 64 (s + ?off) => pose (OFF6 := off) end.
  (* [comment removed for export] *)
  assert (PXdM6 : PIXat M6 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_sess C A4 m6 M6 _ s 256 pixd _ CK HW6 GLO1 Lpixd_a4 PXd6 FRs6).
  assert (PXtM6 : PIXat M6 pixt (hdv w h 8 0 datat)) by exact (exT_pix_sess C A4 m6 M6 _ s 256 pixt _ CK HW6 GLO1 Lpixt_a4 PXt6 FRs6).
  lazymatch type of Q1_6 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_6 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A4 M6 _ Rc6 (256) 4 (kR - RK_pix - RK_rmc - 1 - 1) (bR - RB_pix14 - RB_rmc - alloc_margin (wpl_of w 8 * 4) - alloc_margin (wpl_of w 8 * 4)) (Z_to_bv 64 ret) sp' S CK HWs6 Q10_6 Q11_6 ltac:(lia) ltac:(lia) ltac:(lia)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM4) ltac:(clear - HkR'; unfold RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB MG17 RBpos; lia) ltac:(unfold ROOM_NMAX; lia) Q1_6
             ltac:(red; apply bv_eq; reflexivity) Q4_6 Q2_6 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF6, CALLOC_STACK, ALLOC_STACK; clear - Hlo1; lia) ltac:(unfold OFF6; clear - Hhi; lia)) end end end.
  intros A5 m7 vm5 r7 res6 HW7 Hres6 CSx6 Hnz6 Ftabvalx Lo6 F0tabval LEQ6 ZERO6 ALtabval TOP6 PMc6 RM5.
  pose proof CSx6 as CS6. clear CSx6.
  rewrite with_vmmaps_twice in HW7 |- *.
  assert (Eres6 : res6 = Z_to_bv 64 (u res6)) by (symmetry; apply zbv_self).
  pose proof (u64_range res6) as RRtabval. set (tabval := u res6) in *. clearbody tabval. rewrite Eres6 in Hres6, Ftabvalx, Lo6, F0tabval, LEQ6, ZERO6. clear Eres6 TOP6 Hnz6.
  change (256 * 4)%Z with 1024%Z in Lo6, ZERO6.
  assert (Gtabval : (4096 <= tabval)%Z /\ (tabval + 1024 <= alloc_top (c_vm C))%Z).
  { destruct (blk_range C A5 m7 _ (Z_to_bv 64 tabval) (1024) CK HW7 Lo6 ltac:(lia)) as [G1 G2]. rewrite u_Z2bv in G1, G2 by (clear - RRtabval; lia). split; assumption. }
  pose proof (fresh_sub A0 A4 _ SUB4 Ftabvalx) as Ftabval.
  pose proof Lo6 as Ltabval_a5.
  assert (SUB5 : sub_live A0 A5).
  { intros q0 kq Lq. rewrite (LEQ6 q0 (ne_live A0 q0 _ kq Lq Ftabval)). exact (SUB4 q0 kq Lq). }
  pose proof (fun (q0 : word) (Hq : ~ In q0 (Z_to_bv 64 tabval :: [Z_to_bv 64 bufs2; Z_to_bv 64 bufs1; Z_to_bv 64 pixt; Z_to_bv 64 datat; Z_to_bv 64 pixd; Z_to_bv 64 datad])) => eq_trans (LEQ6 q0 (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL4 q0 (fun XX => Hq (or_intror XX)))) as LDEL5.
  pose proof (ne_live A4 _ _ _ Lpixs_a4 Ftabvalx) as NE_pixs_tabval.
  pose proof (eq_trans (LEQ6 _ NE_pixs_tabval) Lpixs_a4) as Lpixs_a5.
  pose proof (ne_live A4 _ _ _ Ldata_a4 Ftabvalx) as NE_data_tabval.
  pose proof (eq_trans (LEQ6 _ NE_data_tabval) Ldata_a4) as Ldata_a5.
  pose proof (ne_live A4 _ _ _ Lpixd_a4 Ftabvalx) as NE_pixd_tabval.
  pose proof (eq_trans (LEQ6 _ NE_pixd_tabval) Lpixd_a4) as Lpixd_a5.
  pose proof (ne_live A4 _ _ _ Ldatad_a4 Ftabvalx) as NE_datad_tabval.
  pose proof (eq_trans (LEQ6 _ NE_datad_tabval) Ldatad_a4) as Ldatad_a5.
  pose proof (ne_live A4 _ _ _ Lpixt_a4 Ftabvalx) as NE_pixt_tabval.
  pose proof (eq_trans (LEQ6 _ NE_pixt_tabval) Lpixt_a4) as Lpixt_a5.
  pose proof (ne_live A4 _ _ _ Ldatat_a4 Ftabvalx) as NE_datat_tabval.
  pose proof (eq_trans (LEQ6 _ NE_datat_tabval) Ldatat_a4) as Ldatat_a5.
  pose proof (ne_live A4 _ _ _ Lbufs1_a4 Ftabvalx) as NE_bufs1_tabval.
  pose proof (eq_trans (LEQ6 _ NE_bufs1_tabval) Lbufs1_a4) as Lbufs1_a5.
  pose proof (ne_live A4 _ _ _ Lbufs2_a4 Ftabvalx) as NE_bufs2_tabval.
  pose proof (eq_trans (LEQ6 _ NE_bufs2_tabval) Lbufs2_a4) as Lbufs2_a5.
  assert (PXd7 : PIXat m7 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_livk A4 M6 m7 pixd _ PXdM6 (proj2 PMc6) Lpixd_a4).
  assert (PXt7 : PIXat m7 pixt (hdv w h 8 0 datat)) by exact (exT_pix_livk A4 M6 m7 pixt _ PXtM6 (proj2 PMc6) Lpixt_a4).
  assert (PM7 : POSTM C A0 s m4 m7).
  { eapply POSTM_trans; [exact PM6|]. eapply POSTM_trans; [exact PMs6|]. apply (POSTM_sub C A0 A4 _ _ _ SUB4). apply (POSTM_mono C A4 (s + OFF6) s); [unfold OFF6; lia | exact PMc6]. }
  assert (KEPT6 : Forall (ex_region_kept E6 M6 m7) [(EVar 32, OFF6, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF6 256 M6 m7 E6 (EVar 32) CK (proj1 PMc6) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E6 M6 m7 _ [] _ HKc6 KEPT6) as HKk6.
  match type of HKk6 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E6 m7 kk') in HKk6 end.
  pose proof (regs_ok_agree 244%nat E6 (ex_envL vals6 r7 [tabval; exW_canary SEGS 415784 m7]) _ _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa6.
  pose proof (exW_regs_call _ _ _ _ _ HRa6 (ex_regs_ok_junk vals6 r7 [tabval; exW_canary SEGS 415784 m7] 244%nat ltac:(vm_cast_no_check (eq_refl 244%nat))) CS6) as HRn7.
  clear HRa6.
  assert (HKa7 : know_ok SEGS (ex_envL vals6 r7 [tabval; exW_canary SEGS 415784 m7]) m7 _) by (exact (know_ok_agree SEGS 244%nat E6 _ m7 _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk6)).
  rewrite (fr_denot_agree 244%nat E6 (ex_envL vals6 r7 [tabval; exW_canary SEGS 415784 m7]) _ fr2 (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r7 ex_r10 (EVar 276) HRn7 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres6)) as HRx7. clear HRn7. rename HRx7 into HRn7.
  clear HR HK Hlf Hms HKc6 HKk6 KEPT6 HC6 HWs6 PMs6 Q10_6 Q11_6 Q1_6 Q2_6 Q4_6 PM6 HW6 FRs6 PMc6 CS6 SUB4 RM4 LEQ6 Ftabvalx Lo6 OFF6 LDEL4 Hres6 ZERO6 Lpixs_a4 Ldata_a4 Lpixd_a4 Ldatad_a4 Lpixt_a4 Ldatat_a4 Lbufs1_a4 Lbufs2_a4 PXdM6 PXd6 PXtM6 PXt6.
  subst M6. clear log6. clear E6. try clear Rc6. clear KN6.
  lazymatch type of HRn7 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn7 end.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [tabval; exW_canary SEGS 415784 m7]) m7) _ _ (ex_krange SEGS (ex_envL vals6 r7 [tabval; exW_canary SEGS 415784 m7]) m7 (EVar 276) tabval 4096 (2 ^ 47) eq_refl RRtabval ltac:(clear - Gtabval T1 T2 T3 LV Rnb; lia)) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals6 r7 [tabval; exW_canary SEGS 415784 m7]) m7))) as HKb7.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A5 m7 _ (s - 256) (Z.to_nat 256) CK HW7 GLO1 GLO2) as SOK7.
  pose proof (exW_canary_ok SEGS 415784 m7 (canary_any m7)) as CANOK7.
  pose (vals7 := vals6 ++ map (getr r7) ex_regs_list ++ map (Z_to_bv 64) [tabval; exW_canary SEGS 415784 m7]).
  pose proof (exW_kn_fixed SEGS C A5 m7 _ (ex_envL vals6 r7 [tabval; exW_canary SEGS 415784 m7]) (EVar 277) (EVar 32) (exW_canary SEGS 415784 m7) s 256 415784 65536 212992 213416 213568 213416 213568
                HW7 eq_refl (proj1 CANOK7) (proj2 CANOK7) eq_refl eq_refl eq_refl SOK7 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf7.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb7 (proj2 (Forall_app _ _ _) (conj HKf7 HKa7)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn7 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN7 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb7 HKf7 HKa7 SOK7 CANOK7.
  repeat match goal with H : getr r7 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc7 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E7 := EEx) in HR, Hlf, HK, Hms |- *; set (log7 := LLx) in Hms, Hlf; set (M7 := mem_denot E7 m7 log7) in Hms end.
  assert (WP7 : W C A5 M7 (with_vmmaps vm5 md) /\ POSTM C A0 s m7 M7).
  { subst M7. apply (exW_win_blks C A5 A0 m7 _ E7 log7 (EVar 32) s 256 [] CK HW7 SUB5 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP7 as [HWs7 PMs7].
  pose proof (exW_win_only E7 m7 log7 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs7. change (mem_denot E7 m7 log7) with M7 in FRs7.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log7 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC7 : carry log7 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc7 : know_ok SEGS E7 M7 kn1) by (apply (carry_after SEGS E7 m7 log7 kn0 [] kn1 scs hs HC7 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact Hms |].
  pose (BS7 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, pixt); (173%nat, datat); (174%nat, wpl_of w 8); (208%nat, bufs1); (242%nat, bufs2); (276%nat, tabval)]).
  exW_regfactB BS7 HR ex_r10 Q10_7. exW_regfactB BS7 HR ex_r11 Q11_7. exW_regfactB BS7 HR ex_r1 Q1_7. exW_regfactB BS7 HR ex_r2 Q2_7. exW_regfactB BS7 HR ex_r4 Q4_7.
  clear BS7.
  lazymatch type of Q2_7 with _ = Z_to_bv 64 (s + ?off) => pose (OFF7 := off) end.
  (* [comment removed for export] *)
  assert (PXdM7 : PIXat M7 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_sess C A5 m7 M7 _ s 256 pixd _ CK HW7 GLO1 Lpixd_a5 PXd7 FRs7).
  assert (PXtM7 : PIXat M7 pixt (hdv w h 8 0 datat)) by exact (exT_pix_sess C A5 m7 M7 _ s 256 pixt _ CK HW7 GLO1 Lpixt_a5 PXt7 FRs7).
  lazymatch type of Q1_7 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_7 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A5 M7 _ Rc7 (256) 4 (kR - RK_pix - RK_rmc - 1 - 1 - 1) (bR - RB_pix14 - RB_rmc - alloc_margin (wpl_of w 8 * 4) - alloc_margin (wpl_of w 8 * 4) - alloc_margin (256 * 4)) (Z_to_bv 64 ret) sp' S CK HWs7 Q10_7 Q11_7 ltac:(lia) ltac:(lia) ltac:(lia)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM5) ltac:(clear - HkR'; unfold RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB MG17 RBpos; lia) ltac:(unfold ROOM_NMAX; lia) Q1_7
             ltac:(red; apply bv_eq; reflexivity) Q4_7 Q2_7 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF7, CALLOC_STACK, ALLOC_STACK; clear - Hlo1; lia) ltac:(unfold OFF7; clear - Hhi; lia)) end end end.
  intros A6 m8 vm6 r8 res7 HW8 Hres7 CSx7 Hnz7 Ftab38x Lo7 F0tab38 LEQ7 ZERO7 ALtab38 TOP7 PMc7 RM6.
  pose proof CSx7 as CS7. clear CSx7.
  rewrite with_vmmaps_twice in HW8 |- *.
  assert (Eres7 : res7 = Z_to_bv 64 (u res7)) by (symmetry; apply zbv_self).
  pose proof (u64_range res7) as RRtab38. set (tab38 := u res7) in *. clearbody tab38. rewrite Eres7 in Hres7, Ftab38x, Lo7, F0tab38, LEQ7, ZERO7. clear Eres7 TOP7 Hnz7.
  change (256 * 4)%Z with 1024%Z in Lo7, ZERO7.
  assert (Gtab38 : (4096 <= tab38)%Z /\ (tab38 + 1024 <= alloc_top (c_vm C))%Z).
  { destruct (blk_range C A6 m8 _ (Z_to_bv 64 tab38) (1024) CK HW8 Lo7 ltac:(lia)) as [G1 G2]. rewrite u_Z2bv in G1, G2 by (clear - RRtab38; lia). split; assumption. }
  pose proof (fresh_sub A0 A5 _ SUB5 Ftab38x) as Ftab38.
  pose proof Lo7 as Ltab38_a6.
  assert (SUB6 : sub_live A0 A6).
  { intros q0 kq Lq. rewrite (LEQ7 q0 (ne_live A0 q0 _ kq Lq Ftab38)). exact (SUB5 q0 kq Lq). }
  pose proof (fun (q0 : word) (Hq : ~ In q0 (Z_to_bv 64 tab38 :: [Z_to_bv 64 tabval; Z_to_bv 64 bufs2; Z_to_bv 64 bufs1; Z_to_bv 64 pixt; Z_to_bv 64 datat; Z_to_bv 64 pixd; Z_to_bv 64 datad])) => eq_trans (LEQ7 q0 (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL5 q0 (fun XX => Hq (or_intror XX)))) as LDEL6.
  pose proof (ne_live A5 _ _ _ Lpixs_a5 Ftab38x) as NE_pixs_tab38.
  pose proof (eq_trans (LEQ7 _ NE_pixs_tab38) Lpixs_a5) as Lpixs_a6.
  pose proof (ne_live A5 _ _ _ Ldata_a5 Ftab38x) as NE_data_tab38.
  pose proof (eq_trans (LEQ7 _ NE_data_tab38) Ldata_a5) as Ldata_a6.
  pose proof (ne_live A5 _ _ _ Lpixd_a5 Ftab38x) as NE_pixd_tab38.
  pose proof (eq_trans (LEQ7 _ NE_pixd_tab38) Lpixd_a5) as Lpixd_a6.
  pose proof (ne_live A5 _ _ _ Ldatad_a5 Ftab38x) as NE_datad_tab38.
  pose proof (eq_trans (LEQ7 _ NE_datad_tab38) Ldatad_a5) as Ldatad_a6.
  pose proof (ne_live A5 _ _ _ Lpixt_a5 Ftab38x) as NE_pixt_tab38.
  pose proof (eq_trans (LEQ7 _ NE_pixt_tab38) Lpixt_a5) as Lpixt_a6.
  pose proof (ne_live A5 _ _ _ Ldatat_a5 Ftab38x) as NE_datat_tab38.
  pose proof (eq_trans (LEQ7 _ NE_datat_tab38) Ldatat_a5) as Ldatat_a6.
  pose proof (ne_live A5 _ _ _ Lbufs1_a5 Ftab38x) as NE_bufs1_tab38.
  pose proof (eq_trans (LEQ7 _ NE_bufs1_tab38) Lbufs1_a5) as Lbufs1_a6.
  pose proof (ne_live A5 _ _ _ Lbufs2_a5 Ftab38x) as NE_bufs2_tab38.
  pose proof (eq_trans (LEQ7 _ NE_bufs2_tab38) Lbufs2_a5) as Lbufs2_a6.
  pose proof (ne_live A5 _ _ _ Ltabval_a5 Ftab38x) as NE_tabval_tab38.
  pose proof (eq_trans (LEQ7 _ NE_tabval_tab38) Ltabval_a5) as Ltabval_a6.
  assert (PXd8 : PIXat m8 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_livk A5 M7 m8 pixd _ PXdM7 (proj2 PMc7) Lpixd_a5).
  assert (PXt8 : PIXat m8 pixt (hdv w h 8 0 datat)) by exact (exT_pix_livk A5 M7 m8 pixt _ PXtM7 (proj2 PMc7) Lpixt_a5).
  pose proof ZERO7 as Ztab38_8.
  assert (PM8 : POSTM C A0 s m4 m8).
  { eapply POSTM_trans; [exact PM7|]. eapply POSTM_trans; [exact PMs7|]. apply (POSTM_sub C A0 A5 _ _ _ SUB5). apply (POSTM_mono C A5 (s + OFF7) s); [unfold OFF7; lia | exact PMc7]. }
  assert (KEPT7 : Forall (ex_region_kept E7 M7 m8) [(EVar 32, OFF7, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF7 256 M7 m8 E7 (EVar 32) CK (proj1 PMc7) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E7 M7 m8 _ [] _ HKc7 KEPT7) as HKk7.
  match type of HKk7 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E7 m8 kk') in HKk7 end.
  pose proof (regs_ok_agree 278%nat E7 (ex_envL vals7 r8 [tab38; exW_canary SEGS 415784 m8]) _ _ (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa7.
  pose proof (exW_regs_call _ _ _ _ _ HRa7 (ex_regs_ok_junk vals7 r8 [tab38; exW_canary SEGS 415784 m8] 278%nat ltac:(vm_cast_no_check (eq_refl 278%nat))) CS7) as HRn8.
  clear HRa7.
  assert (HKa8 : know_ok SEGS (ex_envL vals7 r8 [tab38; exW_canary SEGS 415784 m8]) m8 _) by (exact (know_ok_agree SEGS 278%nat E7 _ m8 _ (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk7)).
  rewrite (fr_denot_agree 278%nat E7 (ex_envL vals7 r8 [tab38; exW_canary SEGS 415784 m8]) _ fr2 (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r8 ex_r10 (EVar 310) HRn8 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres7)) as HRx8. clear HRn8. rename HRx8 into HRn8.
  clear HR HK Hlf Hms HKc7 HKk7 KEPT7 HC7 HWs7 PMs7 Q10_7 Q11_7 Q1_7 Q2_7 Q4_7 PM7 HW7 FRs7 PMc7 CS7 SUB5 RM5 LEQ7 Ftab38x Lo7 OFF7 LDEL5 Hres7 ZERO7 Lpixs_a5 Ldata_a5 Lpixd_a5 Ldatad_a5 Lpixt_a5 Ldatat_a5 Lbufs1_a5 Lbufs2_a5 Ltabval_a5 PXdM7 PXd7 PXtM7 PXt7.
  subst M7. clear log7. clear E7. try clear Rc7. clear KN7.
  lazymatch type of HRn8 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn8 end.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals7 r8 [tab38; exW_canary SEGS 415784 m8]) m8) _ _ (ex_krange SEGS (ex_envL vals7 r8 [tab38; exW_canary SEGS 415784 m8]) m8 (EVar 310) tab38 4096 (2 ^ 47) eq_refl RRtab38 ltac:(clear - Gtab38 T1 T2 T3 LV Rnb; lia)) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals7 r8 [tab38; exW_canary SEGS 415784 m8]) m8))) as HKb8.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A6 m8 _ (s - 256) (Z.to_nat 256) CK HW8 GLO1 GLO2) as SOK8.
  pose proof (exW_canary_ok SEGS 415784 m8 (canary_any m8)) as CANOK8.
  pose (vals8 := vals7 ++ map (getr r8) ex_regs_list ++ map (Z_to_bv 64) [tab38; exW_canary SEGS 415784 m8]).
  pose proof (exW_kn_fixed SEGS C A6 m8 _ (ex_envL vals7 r8 [tab38; exW_canary SEGS 415784 m8]) (EVar 311) (EVar 32) (exW_canary SEGS 415784 m8) s 256 415784 65536 212992 213416 213568 213416 213568
                HW8 eq_refl (proj1 CANOK8) (proj2 CANOK8) eq_refl eq_refl eq_refl SOK8 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf8.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb8 (proj2 (Forall_app _ _ _) (conj HKf8 HKa8)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn8 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN8 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb8 HKf8 HKa8 SOK8 CANOK8.
  repeat match goal with H : getr r8 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc8 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E8 := EEx) in HR, Hlf, HK, Hms |- *; set (log8 := LLx) in Hms, Hlf; set (M8 := mem_denot E8 m8 log8) in Hms end.
  assert (WP8 : W C A6 M8 (with_vmmaps vm6 md) /\ POSTM C A0 s m8 M8).
  { subst M8. apply (exW_win_blks C A6 A0 m8 _ E8 log8 (EVar 32) s 256 [] CK HW8 SUB6 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP8 as [HWs8 PMs8].
  pose proof (exW_win_only E8 m8 log8 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs8. change (mem_denot E8 m8 log8) with M8 in FRs8.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log8 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC8 : carry log8 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc8 : know_ok SEGS E8 M8 kn1) by (apply (carry_after SEGS E8 m8 log8 kn0 [] kn1 scs hs HC8 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW8)) | exact (mp_lazy _ (w_pure _ _ _ _ HW8)) | exact Hms |].
  pose (BS8 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, pixt); (173%nat, datat); (174%nat, wpl_of w 8); (208%nat, bufs1); (242%nat, bufs2); (276%nat, tabval); (310%nat, tab38)]).
  exW_regfactB BS8 HR ex_r10 Q10_8. exW_regfactB BS8 HR ex_r11 Q11_8. exW_regfactB BS8 HR ex_r1 Q1_8. exW_regfactB BS8 HR ex_r2 Q2_8. exW_regfactB BS8 HR ex_r4 Q4_8.
  clear BS8.
  lazymatch type of Q2_8 with _ = Z_to_bv 64 (s + ?off) => pose (OFF8 := off) end.
  (* [comment removed for export] *)
  assert (PXdM8 : PIXat M8 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_sess C A6 m8 M8 _ s 256 pixd _ CK HW8 GLO1 Lpixd_a6 PXd8 FRs8).
  assert (PXtM8 : PIXat M8 pixt (hdv w h 8 0 datat)) by exact (exT_pix_sess C A6 m8 M8 _ s 256 pixt _ CK HW8 GLO1 Lpixt_a6 PXt8 FRs8).
  pose proof (exT_livk_sess C A6 m8 M8 _ s 256 CK HW8 GLO1 FRs8) as LKs8.
  pose proof (zero_livk A6 m8 M8 _ _ LKs8 Ltab38_a6 Ztab38_8) as Ztab38M8.
  lazymatch type of Q1_8 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_8 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A6 M8 _ Rc8 (256) 4 (kR - RK_pix - RK_rmc - 1 - 1 - 1 - 1) (bR - RB_pix14 - RB_rmc - alloc_margin (wpl_of w 8 * 4) - alloc_margin (wpl_of w 8 * 4) - alloc_margin (256 * 4) - alloc_margin (256 * 4)) (Z_to_bv 64 ret) sp' S CK HWs8 Q10_8 Q11_8 ltac:(lia) ltac:(lia) ltac:(lia)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM6) ltac:(clear - HkR'; unfold RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB MG17 RBpos; lia) ltac:(unfold ROOM_NMAX; lia) Q1_8
             ltac:(red; apply bv_eq; reflexivity) Q4_8 Q2_8 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF8, CALLOC_STACK, ALLOC_STACK; clear - Hlo1; lia) ltac:(unfold OFF8; clear - Hhi; lia)) end end end.
  intros A7 m9 vm7 r9 res8 HW9 Hres8 CSx8 Hnz8 Ftab14x Lo8 F0tab14 LEQ8 ZERO8 ALtab14 TOP8 PMc8 RM7.
  pose proof CSx8 as CS8. clear CSx8.
  rewrite with_vmmaps_twice in HW9 |- *.
  assert (Eres8 : res8 = Z_to_bv 64 (u res8)) by (symmetry; apply zbv_self).
  pose proof (u64_range res8) as RRtab14. set (tab14 := u res8) in *. clearbody tab14. rewrite Eres8 in Hres8, Ftab14x, Lo8, F0tab14, LEQ8, ZERO8. clear Eres8 TOP8 Hnz8.
  change (256 * 4)%Z with 1024%Z in Lo8, ZERO8.
  assert (Gtab14 : (4096 <= tab14)%Z /\ (tab14 + 1024 <= alloc_top (c_vm C))%Z).
  { destruct (blk_range C A7 m9 _ (Z_to_bv 64 tab14) (1024) CK HW9 Lo8 ltac:(lia)) as [G1 G2]. rewrite u_Z2bv in G1, G2 by (clear - RRtab14; lia). split; assumption. }
  pose proof (fresh_sub A0 A6 _ SUB6 Ftab14x) as Ftab14.
  pose proof Lo8 as Ltab14_a7.
  assert (SUB7 : sub_live A0 A7).
  { intros q0 kq Lq. rewrite (LEQ8 q0 (ne_live A0 q0 _ kq Lq Ftab14)). exact (SUB6 q0 kq Lq). }
  pose proof (fun (q0 : word) (Hq : ~ In q0 (Z_to_bv 64 tab14 :: [Z_to_bv 64 tab38; Z_to_bv 64 tabval; Z_to_bv 64 bufs2; Z_to_bv 64 bufs1; Z_to_bv 64 pixt; Z_to_bv 64 datat; Z_to_bv 64 pixd; Z_to_bv 64 datad])) => eq_trans (LEQ8 q0 (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL6 q0 (fun XX => Hq (or_intror XX)))) as LDEL7.
  pose proof (ne_live A6 _ _ _ Lpixs_a6 Ftab14x) as NE_pixs_tab14.
  pose proof (eq_trans (LEQ8 _ NE_pixs_tab14) Lpixs_a6) as Lpixs_a7.
  pose proof (ne_live A6 _ _ _ Ldata_a6 Ftab14x) as NE_data_tab14.
  pose proof (eq_trans (LEQ8 _ NE_data_tab14) Ldata_a6) as Ldata_a7.
  pose proof (ne_live A6 _ _ _ Lpixd_a6 Ftab14x) as NE_pixd_tab14.
  pose proof (eq_trans (LEQ8 _ NE_pixd_tab14) Lpixd_a6) as Lpixd_a7.
  pose proof (ne_live A6 _ _ _ Ldatad_a6 Ftab14x) as NE_datad_tab14.
  pose proof (eq_trans (LEQ8 _ NE_datad_tab14) Ldatad_a6) as Ldatad_a7.
  pose proof (ne_live A6 _ _ _ Lpixt_a6 Ftab14x) as NE_pixt_tab14.
  pose proof (eq_trans (LEQ8 _ NE_pixt_tab14) Lpixt_a6) as Lpixt_a7.
  pose proof (ne_live A6 _ _ _ Ldatat_a6 Ftab14x) as NE_datat_tab14.
  pose proof (eq_trans (LEQ8 _ NE_datat_tab14) Ldatat_a6) as Ldatat_a7.
  pose proof (ne_live A6 _ _ _ Lbufs1_a6 Ftab14x) as NE_bufs1_tab14.
  pose proof (eq_trans (LEQ8 _ NE_bufs1_tab14) Lbufs1_a6) as Lbufs1_a7.
  pose proof (ne_live A6 _ _ _ Lbufs2_a6 Ftab14x) as NE_bufs2_tab14.
  pose proof (eq_trans (LEQ8 _ NE_bufs2_tab14) Lbufs2_a6) as Lbufs2_a7.
  pose proof (ne_live A6 _ _ _ Ltabval_a6 Ftab14x) as NE_tabval_tab14.
  pose proof (eq_trans (LEQ8 _ NE_tabval_tab14) Ltabval_a6) as Ltabval_a7.
  pose proof (ne_live A6 _ _ _ Ltab38_a6 Ftab14x) as NE_tab38_tab14.
  pose proof (eq_trans (LEQ8 _ NE_tab38_tab14) Ltab38_a6) as Ltab38_a7.
  assert (PXd9 : PIXat m9 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_livk A6 M8 m9 pixd _ PXdM8 (proj2 PMc8) Lpixd_a6).
  assert (PXt9 : PIXat m9 pixt (hdv w h 8 0 datat)) by exact (exT_pix_livk A6 M8 m9 pixt _ PXtM8 (proj2 PMc8) Lpixt_a6).
  pose proof (zero_livk A6 M8 m9 _ _ (proj2 PMc8) Ltab38_a6 Ztab38M8) as Ztab38_9.
  pose proof ZERO8 as Ztab14_9.
  assert (PM9 : POSTM C A0 s m4 m9).
  { eapply POSTM_trans; [exact PM8|]. eapply POSTM_trans; [exact PMs8|]. apply (POSTM_sub C A0 A6 _ _ _ SUB6). apply (POSTM_mono C A6 (s + OFF8) s); [unfold OFF8; lia | exact PMc8]. }
  assert (KEPT8 : Forall (ex_region_kept E8 M8 m9) [(EVar 32, OFF8, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF8 256 M8 m9 E8 (EVar 32) CK (proj1 PMc8) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E8 M8 m9 _ [] _ HKc8 KEPT8) as HKk8.
  match type of HKk8 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E8 m9 kk') in HKk8 end.
  pose proof (regs_ok_agree 312%nat E8 (ex_envL vals8 r9 [tab14; exW_canary SEGS 415784 m9]) _ _ (vals_app_agree vals8 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa8.
  pose proof (exW_regs_call _ _ _ _ _ HRa8 (ex_regs_ok_junk vals8 r9 [tab14; exW_canary SEGS 415784 m9] 312%nat ltac:(vm_cast_no_check (eq_refl 312%nat))) CS8) as HRn9.
  clear HRa8.
  assert (HKa9 : know_ok SEGS (ex_envL vals8 r9 [tab14; exW_canary SEGS 415784 m9]) m9 _) by (exact (know_ok_agree SEGS 312%nat E8 _ m9 _ (vals_app_agree vals8 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk8)).
  rewrite (fr_denot_agree 312%nat E8 (ex_envL vals8 r9 [tab14; exW_canary SEGS 415784 m9]) _ fr2 (vals_app_agree vals8 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r9 ex_r10 (EVar 344) HRn9 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres8)) as HRx9. clear HRn9. rename HRx9 into HRn9.
  clear HR HK Hlf Hms HKc8 HKk8 KEPT8 HC8 HWs8 PMs8 Q10_8 Q11_8 Q1_8 Q2_8 Q4_8 PM8 HW8 FRs8 PMc8 CS8 SUB6 RM6 LEQ8 Ftab14x Lo8 OFF8 LDEL6 Hres8 ZERO8 Lpixs_a6 Ldata_a6 Lpixd_a6 Ldatad_a6 Lpixt_a6 Ldatat_a6 Lbufs1_a6 Lbufs2_a6 Ltabval_a6 Ltab38_a6 PXdM8 PXd8 PXtM8 PXt8 Ztab38M8 Ztab38_8 LKs8.
  subst M8. clear log8. clear E8. try clear Rc8. clear KN8.
  lazymatch type of HRn9 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn9 end.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals8 r9 [tab14; exW_canary SEGS 415784 m9]) m9) _ _ (ex_krange SEGS (ex_envL vals8 r9 [tab14; exW_canary SEGS 415784 m9]) m9 (EVar 344) tab14 4096 (2 ^ 47) eq_refl RRtab14 ltac:(clear - Gtab14 T1 T2 T3 LV Rnb; lia)) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals8 r9 [tab14; exW_canary SEGS 415784 m9]) m9))) as HKb9.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A7 m9 _ (s - 256) (Z.to_nat 256) CK HW9 GLO1 GLO2) as SOK9.
  pose proof (exW_canary_ok SEGS 415784 m9 (canary_any m9)) as CANOK9.
  pose (vals9 := vals8 ++ map (getr r9) ex_regs_list ++ map (Z_to_bv 64) [tab14; exW_canary SEGS 415784 m9]).
  pose proof (exW_kn_fixed SEGS C A7 m9 _ (ex_envL vals8 r9 [tab14; exW_canary SEGS 415784 m9]) (EVar 345) (EVar 32) (exW_canary SEGS 415784 m9) s 256 415784 65536 212992 213416 213568 213416 213568
                HW9 eq_refl (proj1 CANOK9) (proj2 CANOK9) eq_refl eq_refl eq_refl SOK9 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf9.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb9 (proj2 (Forall_app _ _ _) (conj HKf9 HKa9)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn9 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN9 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb9 HKf9 HKa9 SOK9 CANOK9.
  repeat match goal with H : getr r9 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc9 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E9 := EEx) in HR, Hlf, HK, Hms |- *; set (log9 := LLx) in Hms, Hlf; set (M9 := mem_denot E9 m9 log9) in Hms end.
  assert (WP9 : W C A7 M9 (with_vmmaps vm7 md) /\ POSTM C A0 s m9 M9).
  { subst M9. apply (exW_win_blks C A7 A0 m9 _ E9 log9 (EVar 32) s 256 [] CK HW9 SUB7 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP9 as [HWs9 PMs9].
  pose proof (exW_win_only E9 m9 log9 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs9. change (mem_denot E9 m9 log9) with M9 in FRs9.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log9 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC9 : carry log9 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc9 : know_ok SEGS E9 M9 kn1) by (apply (carry_after SEGS E9 m9 log9 kn0 [] kn1 scs hs HC9 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW9)) | exact (mp_lazy _ (w_pure _ _ _ _ HW9)) | exact Hms |].
  pose (BS9 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, pixt); (173%nat, datat); (174%nat, wpl_of w 8); (208%nat, bufs1); (242%nat, bufs2); (276%nat, tabval); (310%nat, tab38); (344%nat, tab14)]).
  exW_regfactB BS9 HR ex_r2 Q2_9. exW_regfactB BS9 HR ex_r9 Q9_9. exW_regfactB BS9 HR ex_r18 Q18_9. exW_regfactB BS9 HR ex_r20 Q20_9. exW_regfactB BS9 HR ex_r21 Q21_9. exW_regfactB BS9 HR ex_r22 Q22_9. exW_regfactB BS9 HR ex_r25 Q25_9.
  clear BS9.
  (* [comment removed for export] *)
  assert (PXdM9 : PIXat M9 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_sess C A7 m9 M9 _ s 256 pixd _ CK HW9 GLO1 Lpixd_a7 PXd9 FRs9).
  assert (PXtM9 : PIXat M9 pixt (hdv w h 8 0 datat)) by exact (exT_pix_sess C A7 m9 M9 _ s 256 pixt _ CK HW9 GLO1 Lpixt_a7 PXt9 FRs9).
  pose proof (exT_livk_sess C A7 m9 M9 _ s 256 CK HW9 GLO1 FRs9) as LKs9.
  pose proof (zero_livk A7 m9 M9 _ _ LKs9 Ltab38_a7 Ztab38_9) as Ztab38M9.
  pose proof (zero_livk A7 m9 M9 _ _ LKs9 Ltab14_a7 Ztab14_9) as Ztab14M9.
  pose (BSx9 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, pixt); (173%nat, datat); (174%nat, wpl_of w 8); (208%nat, bufs1); (242%nat, bufs2); (276%nat, tabval); (310%nat, tab38); (344%nat, tab14)]).
  exW_cellB HK Hlf r0 BSx9 (EVar 32) s (-108)%Z 4%nat KC0. exW_cellB HK Hlf r0 BSx9 (EVar 32) s (-112)%Z 4%nat KC1. exW_cellB HK Hlf r0 BSx9 (EVar 32) s (-152)%Z 8%nat KC2. exW_cellB HK Hlf r0 BSx9 (EVar 32) s (-160)%Z 8%nat KC3. exW_cellB HK Hlf r0 BSx9 (EVar 32) s (-168)%Z 8%nat KC4.
  clear BSx9.
  assert (NDk : List.NoDup [Z_to_bv 64 datad; Z_to_bv 64 datat; Z_to_bv 64 bufs1; Z_to_bv 64 bufs2; Z_to_bv 64 tabval; Z_to_bv 64 tab38; Z_to_bv 64 tab14]).
  { apply List.NoDup_cons; [cbn [List.In]; intros HH; repeat (destruct HH as [EE|HH]; [first [exact ((fun EE => NE_datad_datat (eq_sym EE)) EE) | exact ((fun EE => NE_datad_bufs1 (eq_sym EE)) EE) | exact ((fun EE => NE_datad_bufs2 (eq_sym EE)) EE) | exact ((fun EE => NE_datad_tabval (eq_sym EE)) EE) | exact ((fun EE => NE_datad_tab38 (eq_sym EE)) EE) | exact ((fun EE => NE_datad_tab14 (eq_sym EE)) EE)]|]); exact HH|]. apply List.NoDup_cons; [cbn [List.In]; intros HH; repeat (destruct HH as [EE|HH]; [first [exact ((fun EE => NE_datat_bufs1 (eq_sym EE)) EE) | exact ((fun EE => NE_datat_bufs2 (eq_sym EE)) EE) | exact ((fun EE => NE_datat_tabval (eq_sym EE)) EE) | exact ((fun EE => NE_datat_tab38 (eq_sym EE)) EE) | exact ((fun EE => NE_datat_tab14 (eq_sym EE)) EE)]|]); exact HH|]. apply List.NoDup_cons; [cbn [List.In]; intros HH; repeat (destruct HH as [EE|HH]; [first [exact ((fun EE => NE_bufs1_bufs2 (eq_sym EE)) EE) | exact ((fun EE => NE_bufs1_tabval (eq_sym EE)) EE) | exact ((fun EE => NE_bufs1_tab38 (eq_sym EE)) EE) | exact ((fun EE => NE_bufs1_tab14 (eq_sym EE)) EE)]|]); exact HH|]. apply List.NoDup_cons; [cbn [List.In]; intros HH; repeat (destruct HH as [EE|HH]; [first [exact ((fun EE => NE_bufs2_tabval (eq_sym EE)) EE) | exact ((fun EE => NE_bufs2_tab38 (eq_sym EE)) EE) | exact ((fun EE => NE_bufs2_tab14 (eq_sym EE)) EE)]|]); exact HH|]. apply List.NoDup_cons; [cbn [List.In]; intros HH; repeat (destruct HH as [EE|HH]; [first [exact ((fun EE => NE_tabval_tab38 (eq_sym EE)) EE) | exact ((fun EE => NE_tabval_tab14 (eq_sym EE)) EE)]|]); exact HH|]. apply List.NoDup_cons; [cbn [List.In]; intros HH; repeat (destruct HH as [EE|HH]; [first [exact ((fun EE => NE_tab38_tab14 (eq_sym EE)) EE)]|]); exact HH|]. apply List.NoDup_cons; [intros []|]. apply List.NoDup_nil. }
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (d2k_hop_W fxk C A7 A0 M9 _ Rc9 s w h datad datat bufs1 bufs2 tabval tab38 tab14 S CK HWs9 SUB7 Hs16 ltac:(clear - Hlo1; lia) Hhi HOK Hw1 Hh1
             Ldatad_a7 Fdatad F0datad Ldatat_a7 Lbufs1_a7 Fbufs1 F0bufs1 Lbufs2_a7 Fbufs2 F0bufs2 Ltabval_a7 Ftabval F0tabval Ltab38_a7 Ftab38 F0tab38 Ltab14_a7 Ftab14 F0tab14 RRdatad RRdatat RRbufs1 RRbufs2 RRtabval RRtab38 RRtab14 NDk Ztab38M9 Ztab14M9 Q2_9 Q9_9 Q18_9 Q20_9 Q21_9 Q22_9 Q25_9 KC0 KC1 KC2 KC3 KC4) end.
  intros r10 m10 HW10 PMl9 AGR9  KEPTS9 KEEPB9.
  assert (PM10 : POSTM C A0 s m4 m10).
  { eapply POSTM_trans; [exact PM9|]. eapply POSTM_trans; [exact PMs9 | exact PMl9]. }
  assert (PXd10 : PIXat m10 pixd (set_data (pix_hdr w h 2) datad)).
  { apply (pix_keepl A7 M9 m10 pixd _ [Z_to_bv 64 datad; Z_to_bv 64 bufs1; Z_to_bv 64 bufs2; Z_to_bv 64 tabval; Z_to_bv 64 tab38; Z_to_bv 64 tab14] PXdM9 Lpixd_a7); [|exact KEEPB9].
    cbn [List.In]. intros HH. repeat (destruct HH as [EE|HH]; [first [exact (NE_pixd_datad (eq_sym EE)) | exact (NE_pixd_bufs1 (eq_sym EE)) | exact (NE_pixd_bufs2 (eq_sym EE)) | exact (NE_pixd_tabval (eq_sym EE)) | exact (NE_pixd_tab38 (eq_sym EE)) | exact (NE_pixd_tab14 (eq_sym EE))]|]). exact HH. }
  assert (PXt10 : PIXat m10 pixt (hdv w h 8 0 datat)).
  { apply (pix_keepl A7 M9 m10 pixt _ [Z_to_bv 64 datad; Z_to_bv 64 bufs1; Z_to_bv 64 bufs2; Z_to_bv 64 tabval; Z_to_bv 64 tab38; Z_to_bv 64 tab14] PXtM9 Lpixt_a7); [|exact KEEPB9].
    cbn [List.In]. intros HH. repeat (destruct HH as [EE|HH]; [first [exact (NE_pixt_datad (eq_sym EE)) | exact (NE_pixt_bufs1 (eq_sym EE)) | exact (NE_pixt_bufs2 (eq_sym EE)) | exact (NE_pixt_tabval (eq_sym EE)) | exact (NE_pixt_tab38 (eq_sym EE)) | exact (NE_pixt_tab14 (eq_sym EE))]|]). exact HH. }
  assert (KEPT9 : Forall (ex_region_kept E9 M9 m10) [(EVar 32, (-208)%Z, (-200)%Z); (EVar 32, (-184)%Z, (-176)%Z); (EVar 32, (-168)%Z, (0)%Z)]).
  { constructor; [exact (exT_kept_in E9 M9 m10 (EVar 32) s (-208) (-200) (s + -208) (s + -200) (fun a Ha => KEPTS9 a (or_introl Ha)) eq_refl RS (Z.le_refl _) (Z.le_refl _))|]. constructor; [exact (exT_kept_in E9 M9 m10 (EVar 32) s (-184) (-176) (s + -184) (s + -176) (fun a Ha => KEPTS9 a (or_intror (or_introl Ha))) eq_refl RS (Z.le_refl _) (Z.le_refl _))|]. constructor; [exact (exT_kept_in E9 M9 m10 (EVar 32) s (-168) (0) (s + -168) (s + 0) (fun a Ha => KEPTS9 a (or_intror (or_intror Ha))) eq_refl RS (Z.le_refl _) (Z.le_refl _))|]. constructor. }
  pose proof (ex_know_keepD SEGS E9 M9 m10 _ [] _ HKc9 KEPT9) as HKk9.
  match type of HKk9 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E9 m10 kk') in HKk9 end.
  pose proof (regs_ok_agree 346%nat E9 (ex_envL vals9 r10 [exW_canary SEGS 415784 m10]) _ _ (vals_app_agree vals9 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa9.
  pose proof (exW_regs_keep _ _ _ _ _ [1%nat; 5%nat; 6%nat; 7%nat; 8%nat; 10%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 19%nat; 23%nat; 24%nat; 26%nat; 27%nat; 28%nat; 29%nat; 30%nat; 31%nat] HRa9 (ex_regs_ok_junk vals9 r10 [exW_canary SEGS 415784 m10] 346%nat ltac:(vm_cast_no_check (eq_refl 346%nat))) (exW_agree_keep _ _ _ AGR9)) as HRn10.
  clear HRa9.
  assert (HKa10 : know_ok SEGS (ex_envL vals9 r10 [exW_canary SEGS 415784 m10]) m10 _) by (exact (know_ok_agree SEGS 346%nat E9 _ m10 _ (vals_app_agree vals9 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk9)).
  rewrite (fr_denot_agree 346%nat E9 (ex_envL vals9 r10 [exW_canary SEGS 415784 m10]) _ fr2 (vals_app_agree vals9 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc9 HKk9 KEPT9 HC9 HWs9 PMs9 Q2_9 Q9_9 Q18_9 Q20_9 Q21_9 Q22_9 Q25_9 PM9 HW9 FRs9 AGR9 KEPTS9 KEEPB9 PMl9 NDk KC0 KC1 KC2 KC3 KC4 PXdM9 PXd9 PXtM9 PXt9 LKs9 Ztab38M9 Ztab38_9 Ztab14M9 Ztab14_9.
  subst M9. clear log9. clear E9. try clear Rc9. clear KN9.
  lazymatch type of HRn10 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn10 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A7 m10 _ (s - 256) (Z.to_nat 256) CK HW10 GLO1 GLO2) as SOK10.
  pose proof (exW_canary_ok SEGS 415784 m10 (canary_any m10)) as CANOK10.
  pose (vals10 := vals9 ++ map (getr r10) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m10]).
  pose proof (exW_kn_fixed SEGS C A7 m10 _ (ex_envL vals9 r10 [exW_canary SEGS 415784 m10]) (EVar 378) (EVar 32) (exW_canary SEGS 415784 m10) s 256 415784 65536 212992 213416 213568 213416 213568
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
  exb_exit ST Rc10 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E10 := EEx) in HR, Hlf, HK, Hms |- *; set (log10 := LLx) in Hms, Hlf; set (M10 := mem_denot E10 m10 log10) in Hms end.
  assert (WP10 : W C A7 M10 (with_vmmaps vm7 md) /\ POSTM C A0 s m10 M10).
  { subst M10. apply (exW_win_blks C A7 A0 m10 _ E10 log10 (EVar 32) s 256 [] CK HW10 SUB7 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP10 as [HWs10 PMs10].
  pose proof (exW_win_only E10 m10 log10 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs10. change (mem_denot E10 m10 log10) with M10 in FRs10.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log10 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC10 : carry log10 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc10 : know_ok SEGS E10 M10 kn1) by (apply (carry_after SEGS E10 m10 log10 kn0 [] kn1 scs hs HC10 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW10)) | exact (mp_lazy _ (w_pure _ _ _ _ HW10)) | exact Hms |].
  pose (BS10 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, pixt); (173%nat, datat); (174%nat, wpl_of w 8); (208%nat, bufs1); (242%nat, bufs2); (276%nat, tabval); (310%nat, tab38); (344%nat, tab14)]).
  exW_regfactB BS10 HR ex_r10 Q10_10. exW_regfactB BS10 HR ex_r11 Q11_10. exW_regfactB BS10 HR ex_r1 Q1_10. exW_regfactB BS10 HR ex_r2 Q2_10. exW_regfactB BS10 HR ex_r4 Q4_10.
  clear BS10.
  lazymatch type of Q2_10 with _ = Z_to_bv 64 (s + ?off) => pose (OFF10 := off) end.
  (* [comment removed for export] *)
  assert (PXdM10 : PIXat M10 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_sess C A7 m10 M10 _ s 256 pixd _ CK HW10 GLO1 Lpixd_a7 PXd10 FRs10).
  assert (PXtM10 : PIXat M10 pixt (hdv w h 8 0 datat)) by exact (exT_pix_sess C A7 m10 M10 _ s 256 pixt _ CK HW10 GLO1 Lpixt_a7 PXt10 FRs10).
  lazymatch type of Q1_10 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixcmapCreateLinear24_W fxk C A7 M10 _ Rc10 (s + OFF10)%Z (Z_to_bv 64 ra) S CK HWs10 Q2_10
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF10, CML_STACK, CALLOC_STACK, ALLOC_STACK; clear - Hlo1; lia) ltac:(unfold OFF10; clear - Hhi; lia) Q1_10 ltac:(red; apply bv_eq; reflexivity) Q4_10 Q10_10 Q11_10
             (kR - RK_pix - RK_rmc - 1 - 1 - 1 - 1 - 1)%Z (bR - RB_pix14 - RB_rmc - alloc_margin (wpl_of w 8 * 4) - alloc_margin (wpl_of w 8 * 4) - alloc_margin (256 * 4) - alloc_margin (256 * 4) - alloc_margin (256 * 4))%Z ltac:(rewrite with_vmmaps_vmmaps; exact RM7) ltac:(clear - HkR'; unfold RK_cml, RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB MG17 RBpos; lia)) end end.
  intros A8 m11 vm8 r11 cmd arrd HW11 CSx10 PMc10 A10_10 CMN RM8.
  pose proof CSx10 as CS10. clear CSx10.
  rewrite with_vmmaps_twice in HW11 |- *.
  destruct CMN as (Gcmd1 & Gcmd2 & Garrd1 & Garrd2 & NEcmarr & Fcmdx & Farrdx & F0cmd & F0arrd & Lcmd_a8 & Larrd_a8 & CMP11 & CMOK & LEQ10).
  cbn [c_arr c_nalloc] in Garrd1, Garrd2, NEcmarr, Farrdx, F0arrd, Larrd_a8, LEQ10. change (4 * 4)%Z with 16%Z in Garrd2, Larrd_a8.
  assert (RRcmd : (0 <= cmd < 2 ^ 64)%Z) by lia. assert (RRarrd : (0 <= arrd < 2 ^ 64)%Z) by lia.
  pose proof (fresh_sub A0 A7 _ SUB7 Fcmdx) as Fcmd. pose proof (fresh_sub A0 A7 _ SUB7 Farrdx) as Farrd.
  assert (SUB8 : sub_live A0 A8).
  { intros q0 kq Lq. rewrite (LEQ10 q0 (ne_live A0 q0 _ kq Lq Fcmd) (ne_live A0 q0 _ kq Lq Farrd)). exact (SUB7 q0 kq Lq). }
  pose proof (fun (q0 : word) (Hq : ~ In q0 (Z_to_bv 64 cmd :: Z_to_bv 64 arrd :: [Z_to_bv 64 tab14; Z_to_bv 64 tab38; Z_to_bv 64 tabval; Z_to_bv 64 bufs2; Z_to_bv 64 bufs1; Z_to_bv 64 pixt; Z_to_bv 64 datat; Z_to_bv 64 pixd; Z_to_bv 64 datad])) =>
                eq_trans (LEQ10 q0 (fun EE => Hq (or_introl (eq_sym EE))) (fun EE => Hq (or_intror (or_introl (eq_sym EE))))) (LDEL7 q0 (fun XX => Hq (or_intror (or_intror XX))))) as LDEL8.
  pose proof (ne_live A7 _ _ _ Lpixs_a7 Fcmdx) as NE_pixs_cmd. pose proof (ne_live A7 _ _ _ Lpixs_a7 Farrdx) as NE_pixs_arrd.
  pose proof (eq_trans (LEQ10 _ NE_pixs_cmd NE_pixs_arrd) Lpixs_a7) as Lpixs_a8.
  pose proof (ne_live A7 _ _ _ Ldata_a7 Fcmdx) as NE_data_cmd. pose proof (ne_live A7 _ _ _ Ldata_a7 Farrdx) as NE_data_arrd.
  pose proof (eq_trans (LEQ10 _ NE_data_cmd NE_data_arrd) Ldata_a7) as Ldata_a8.
  pose proof (ne_live A7 _ _ _ Lpixd_a7 Fcmdx) as NE_pixd_cmd. pose proof (ne_live A7 _ _ _ Lpixd_a7 Farrdx) as NE_pixd_arrd.
  pose proof (eq_trans (LEQ10 _ NE_pixd_cmd NE_pixd_arrd) Lpixd_a7) as Lpixd_a8.
  pose proof (ne_live A7 _ _ _ Ldatad_a7 Fcmdx) as NE_datad_cmd. pose proof (ne_live A7 _ _ _ Ldatad_a7 Farrdx) as NE_datad_arrd.
  pose proof (eq_trans (LEQ10 _ NE_datad_cmd NE_datad_arrd) Ldatad_a7) as Ldatad_a8.
  pose proof (ne_live A7 _ _ _ Lpixt_a7 Fcmdx) as NE_pixt_cmd. pose proof (ne_live A7 _ _ _ Lpixt_a7 Farrdx) as NE_pixt_arrd.
  pose proof (eq_trans (LEQ10 _ NE_pixt_cmd NE_pixt_arrd) Lpixt_a7) as Lpixt_a8.
  pose proof (ne_live A7 _ _ _ Ldatat_a7 Fcmdx) as NE_datat_cmd. pose proof (ne_live A7 _ _ _ Ldatat_a7 Farrdx) as NE_datat_arrd.
  pose proof (eq_trans (LEQ10 _ NE_datat_cmd NE_datat_arrd) Ldatat_a7) as Ldatat_a8.
  pose proof (ne_live A7 _ _ _ Lbufs1_a7 Fcmdx) as NE_bufs1_cmd. pose proof (ne_live A7 _ _ _ Lbufs1_a7 Farrdx) as NE_bufs1_arrd.
  pose proof (eq_trans (LEQ10 _ NE_bufs1_cmd NE_bufs1_arrd) Lbufs1_a7) as Lbufs1_a8.
  pose proof (ne_live A7 _ _ _ Lbufs2_a7 Fcmdx) as NE_bufs2_cmd. pose proof (ne_live A7 _ _ _ Lbufs2_a7 Farrdx) as NE_bufs2_arrd.
  pose proof (eq_trans (LEQ10 _ NE_bufs2_cmd NE_bufs2_arrd) Lbufs2_a7) as Lbufs2_a8.
  pose proof (ne_live A7 _ _ _ Ltabval_a7 Fcmdx) as NE_tabval_cmd. pose proof (ne_live A7 _ _ _ Ltabval_a7 Farrdx) as NE_tabval_arrd.
  pose proof (eq_trans (LEQ10 _ NE_tabval_cmd NE_tabval_arrd) Ltabval_a7) as Ltabval_a8.
  pose proof (ne_live A7 _ _ _ Ltab38_a7 Fcmdx) as NE_tab38_cmd. pose proof (ne_live A7 _ _ _ Ltab38_a7 Farrdx) as NE_tab38_arrd.
  pose proof (eq_trans (LEQ10 _ NE_tab38_cmd NE_tab38_arrd) Ltab38_a7) as Ltab38_a8.
  pose proof (ne_live A7 _ _ _ Ltab14_a7 Fcmdx) as NE_tab14_cmd. pose proof (ne_live A7 _ _ _ Ltab14_a7 Farrdx) as NE_tab14_arrd.
  pose proof (eq_trans (LEQ10 _ NE_tab14_cmd NE_tab14_arrd) Ltab14_a7) as Ltab14_a8.
  assert (PXd11 : PIXat m11 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_livk A7 M10 m11 pixd _ PXdM10 (proj2 PMc10) Lpixd_a7).
  assert (PXt11 : PIXat m11 pixt (hdv w h 8 0 datat)) by exact (exT_pix_livk A7 M10 m11 pixt _ PXtM10 (proj2 PMc10) Lpixt_a7).
  assert (PM11 : POSTM C A0 s m4 m11).
  { eapply POSTM_trans; [exact PM10|]. eapply POSTM_trans; [exact PMs10|]. apply (POSTM_sub C A0 A7 _ _ _ SUB7). apply (POSTM_mono C A7 (s + OFF10) s); [unfold OFF10; lia | exact PMc10]. }
  assert (KEPT10 : Forall (ex_region_kept E10 M10 m11) [(EVar 32, OFF10, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF10 256 M10 m11 E10 (EVar 32) CK (proj1 PMc10) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E10 M10 m11 _ [] _ HKc10 KEPT10) as HKk10.
  match type of HKk10 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E10 m11 kk') in HKk10 end.
  pose proof (regs_ok_agree 379%nat E10 (ex_envL vals10 r11 [cmd; exW_canary SEGS 415784 m11]) _ _ (vals_app_agree vals10 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa10.
  pose proof (exW_regs_call _ _ _ _ _ HRa10 (ex_regs_ok_junk vals10 r11 [cmd; exW_canary SEGS 415784 m11] 379%nat ltac:(vm_cast_no_check (eq_refl 379%nat))) CS10) as HRn11.
  clear HRa10.
  assert (HKa11 : know_ok SEGS (ex_envL vals10 r11 [cmd; exW_canary SEGS 415784 m11]) m11 _) by (exact (know_ok_agree SEGS 379%nat E10 _ m11 _ (vals_app_agree vals10 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk10)).
  rewrite (fr_denot_agree 379%nat E10 (ex_envL vals10 r11 [cmd; exW_canary SEGS 415784 m11]) _ fr2 (vals_app_agree vals10 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r11 ex_r10 (EVar 411) HRn11 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_10)) as HRx11. clear HRn11. rename HRx11 into HRn11.
  clear HR HK Hlf Hms HKc10 HKk10 KEPT10 HC10 HWs10 PMs10 Q10_10 Q11_10 Q1_10 Q2_10 Q4_10 PM10 HW10 FRs10 PMc10 CS10 SUB7 RM7 LEQ10 Fcmdx Farrdx OFF10 LDEL7 A10_10 Lpixs_a7 Ldata_a7 Lpixd_a7 Ldatad_a7 Lpixt_a7 Ldatat_a7 Lbufs1_a7 Lbufs2_a7 Ltabval_a7 Ltab38_a7 Ltab14_a7 PXdM10 PXd10 PXtM10 PXt10.
  subst M10. clear log10. clear E10. try clear Rc10. clear KN10.
  lazymatch type of HRn11 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn11 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A8 m11 _ (s - 256) (Z.to_nat 256) CK HW11 GLO1 GLO2) as SOK11.
  pose proof (exW_canary_ok SEGS 415784 m11 (canary_any m11)) as CANOK11.
  pose (vals11 := vals10 ++ map (getr r11) ex_regs_list ++ map (Z_to_bv 64) [cmd; exW_canary SEGS 415784 m11]).
  pose proof (exW_kn_fixed SEGS C A8 m11 _ (ex_envL vals10 r11 [cmd; exW_canary SEGS 415784 m11]) (EVar 412) (EVar 32) (exW_canary SEGS 415784 m11) s 256 415784 65536 212992 213416 213568 213416 213568
                HW11 eq_refl (proj1 CANOK11) (proj2 CANOK11) eq_refl eq_refl eq_refl SOK11 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf11.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf11 HKa11)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn11 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN11 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf11 HKa11 SOK11 CANOK11.
  repeat match goal with H : getr r11 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc11 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E11 := EEx) in HR, Hlf, HK, Hms |- *; set (log11 := LLx) in Hms, Hlf; set (M11 := mem_denot E11 m11 log11) in Hms end.
  assert (WP11 : W C A8 M11 (with_vmmaps vm8 md) /\ POSTM C A0 s m11 M11).
  { subst M11. apply (exW_win_blks C A8 A0 m11 _ E11 log11 (EVar 32) s 256 [] CK HW11 SUB8 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP11 as [HWs11 PMs11].
  pose proof (exW_win_only E11 m11 log11 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs11. change (mem_denot E11 m11 log11) with M11 in FRs11.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log11 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC11 : carry log11 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc11 : know_ok SEGS E11 M11 kn1) by (apply (carry_after SEGS E11 m11 log11 kn0 [] kn1 scs hs HC11 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW11)) | exact (mp_lazy _ (w_pure _ _ _ _ HW11)) | exact Hms |].
  pose (BS11 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, pixt); (173%nat, datat); (174%nat, wpl_of w 8); (208%nat, bufs1); (242%nat, bufs2); (276%nat, tabval); (310%nat, tab38); (344%nat, tab14); (411%nat, cmd)]).
  exW_regfactB BS11 HR ex_r10 Q10_11. exW_regfactB BS11 HR ex_r11 Q11_11. exW_regfactB BS11 HR ex_r1 Q1_11. exW_regfactB BS11 HR ex_r2 Q2_11.
  clear BS11.
  lazymatch type of Q2_11 with _ = Z_to_bv 64 (s + ?off) => pose (OFF11 := off) end.
  (* [comment removed for export] *)
  assert (PXdM11 : PIXat M11 pixd (set_data (pix_hdr w h 2) datad)) by exact (exT_pix_sess C A8 m11 M11 _ s 256 pixd _ CK HW11 GLO1 Lpixd_a8 PXd11 FRs11).
  assert (PXtM11 : PIXat M11 pixt (hdv w h 8 0 datat)) by exact (exT_pix_sess C A8 m11 M11 _ s 256 pixt _ CK HW11 GLO1 Lpixt_a8 PXt11 FRs11).
  assert (CMPM11 : CMAPat M11 cmd (CMAPV arrd 2 4 4 0)) by exact (exT_cmap_sess C A8 m11 M11 _ s 256 cmd _ CK HW11 GLO1 Lcmd_a8 CMP11 FRs11).
  rewrite PC_SETCMAP_eq.
  lazymatch type of Q1_11 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixSetColormap_S_W (fx := fxk) C A0 A8 M11 _ Rc11 (s + OFF11) pixd cmd (set_data (pix_hdr w h 2) datad) (CMAPV arrd 2 4 4 0) (Z_to_bv 64 ra) S CK HWs11 SUB8 Q2_11
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF11; clear - Hlo1; lia) ltac:(unfold OFF11; clear - Hhi; lia) Q1_11 ltac:(red; apply bv_eq; reflexivity) Q10_11 Q11_11
             PXdM11 eq_refl Lpixd_a8 Fpixd F0pixd CMPM11 CMOK Lcmd_a8 NE_pixd_cmd) end end.
  intros m12 r12 HW12 CSx11 PMc11 PXd12 CMP12 A10_11 KEEPS11.
  pose proof CSx11 as CS11. clear CSx11.
  assert (PXt12 : PIXat m12 pixt (hdv w h 8 0 datat)) by exact (pix_keep1 A8 M11 m12 pixt _ _ PXtM11 Lpixt_a8 (fun EE => NE_pixd_pixt (eq_sym EE)) KEEPS11).
  assert (PM12 : POSTM C A0 s m4 m12).
  { eapply POSTM_trans; [exact PM11|]. eapply POSTM_trans; [exact PMs11|]. apply (POSTM_mono C A0 (s + OFF11) s); [unfold OFF11; lia | exact PMc11]. }
  assert (KEPT11 : Forall (ex_region_kept E11 M11 m12) [(EVar 32, OFF11, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF11 256 M11 m12 E11 (EVar 32) CK (proj1 PMc11) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E11 M11 m12 _ [] _ HKc11 KEPT11) as HKk11.
  match type of HKk11 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E11 m12 kk') in HKk11 end.
  pose proof (regs_ok_agree 413%nat E11 (ex_envL vals11 r12 [exW_canary SEGS 415784 m12]) _ _ (vals_app_agree vals11 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa11.
  pose proof (exW_regs_call _ _ _ _ _ HRa11 (ex_regs_ok_junk vals11 r12 [exW_canary SEGS 415784 m12] 413%nat ltac:(vm_cast_no_check (eq_refl 413%nat))) CS11) as HRn12.
  clear HRa11.
  assert (HKa12 : know_ok SEGS (ex_envL vals11 r12 [exW_canary SEGS 415784 m12]) m12 _) by (exact (know_ok_agree SEGS 413%nat E11 _ m12 _ (vals_app_agree vals11 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk11)).
  rewrite (fr_denot_agree 413%nat E11 (ex_envL vals11 r12 [exW_canary SEGS 415784 m12]) _ fr2 (vals_app_agree vals11 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc11 HKk11 KEPT11 HC11 HWs11 PMs11 Q10_11 Q11_11 Q1_11 Q2_11 PM11 HW11 FRs11 PMc11 CS11 OFF11 A10_11 KEEPS11 PXdM11 PXd11 PXtM11 PXt11 CMPM11 CMP11.
  subst M11. clear log11. clear E11. try clear Rc11. clear KN11.
  lazymatch type of HRn12 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn12 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A8 m12 _ (s - 256) (Z.to_nat 256) CK HW12 GLO1 GLO2) as SOK12.
  pose proof (exW_canary_ok SEGS 415784 m12 (canary_any m12)) as CANOK12.
  pose (vals12 := vals11 ++ map (getr r12) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m12]).
  pose proof (exW_kn_fixed SEGS C A8 m12 _ (ex_envL vals11 r12 [exW_canary SEGS 415784 m12]) (EVar 445) (EVar 32) (exW_canary SEGS 415784 m12) s 256 415784 65536 212992 213416 213568 213416 213568
                HW12 eq_refl (proj1 CANOK12) (proj2 CANOK12) eq_refl eq_refl eq_refl SOK12 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf12.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf12 HKa12)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn12 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN12 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf12 HKa12 SOK12 CANOK12.
  repeat match goal with H : getr r12 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc12 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E12 := EEx) in HR, Hlf, HK, Hms |- *; set (log12 := LLx) in Hms, Hlf; set (M12 := mem_denot E12 m12 log12) in Hms end.
  assert (WP12 : W C A8 M12 (with_vmmaps vm8 md) /\ POSTM C A0 s m12 M12).
  { subst M12. apply (exW_win_blks C A8 A0 m12 _ E12 log12 (EVar 32) s 256 [] CK HW12 SUB8 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP12 as [HWs12 PMs12].
  pose proof (exW_win_only E12 m12 log12 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs12. change (mem_denot E12 m12 log12) with M12 in FRs12.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log12 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC12 : carry log12 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc12 : know_ok SEGS E12 M12 kn1) by (apply (carry_after SEGS E12 m12 log12 kn0 [] kn1 scs hs HC12 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW12)) | exact (mp_lazy _ (w_pure _ _ _ _ HW12)) | exact Hms |].
  pose (BS12 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, pixt); (173%nat, datat); (174%nat, wpl_of w 8); (208%nat, bufs1); (242%nat, bufs2); (276%nat, tabval); (310%nat, tab38); (344%nat, tab14); (411%nat, cmd)]).
  exW_regfactB BS12 HR ex_r10 Q10_12. exW_regfactB BS12 HR ex_r1 Q1_12. exW_regfactB BS12 HR ex_r2 Q2_12. exW_regfactB BS12 HR ex_r4 Q4_12.
  clear BS12.
  lazymatch type of Q2_12 with _ = Z_to_bv 64 (s + ?off) => pose (OFF12 := off) end.
  (* [comment removed for export] *)
  assert (PXdM12 : PIXat M12 pixd (set_cmap (set_data (pix_hdr w h 2) datad) cmd)) by exact (exT_pix_sess C A8 m12 M12 _ s 256 pixd _ CK HW12 GLO1 Lpixd_a8 PXd12 FRs12).
  assert (PXtM12 : PIXat M12 pixt (hdv w h 8 0 datat)) by exact (exT_pix_sess C A8 m12 M12 _ s 256 pixt _ CK HW12 GLO1 Lpixt_a8 PXt12 FRs12).
  assert (CMPM12 : CMAPat M12 cmd (CMAPV arrd 2 4 4 0)) by exact (exT_cmap_sess C A8 m12 M12 _ s 256 cmd _ CK HW12 GLO1 Lcmd_a8 CMP12 FRs12).
  lazymatch type of Q1_12 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_12 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A8 M12 _ Rc12 (Z_to_bv 64 bufs1) (Z_to_bv 64 ret) (4 * wpl_of w 8) sp' S CK HWs12 Q10_12 Lbufs1_a8 F0bufs1 Q1_12
             ltac:(red; apply bv_eq; reflexivity) Q4_12 Q2_12 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF12, ALLOC_STACK; clear - Hlo1; lia) ltac:(unfold OFF12; clear - Hhi; lia)) end end end.
  intros A9 m13 vm9 r13 HW13 CSx12 Ldead12 LEQ12 PMc12 RTR12.
  pose proof CSx12 as CS12. clear CSx12.
  rewrite with_vmmaps_twice in HW13 |- *.
  assert (SUB9 : sub_live A0 A9).
  { intros q0 kq Lq. rewrite (LEQ12 q0 (ne_live A0 q0 _ kq Lq Fbufs1)). exact (SUB8 q0 kq Lq). }
  assert (LDEL9 : forall q0 : word, ~ In q0 [Z_to_bv 64 cmd; Z_to_bv 64 arrd; Z_to_bv 64 tab14; Z_to_bv 64 tab38; Z_to_bv 64 tabval; Z_to_bv 64 bufs2; Z_to_bv 64 pixt; Z_to_bv 64 datat; Z_to_bv 64 pixd; Z_to_bv 64 datad] -> live A9 q0 = live A0 q0).
  { intros q0 Hq. destruct (decide (Z_to_bv 64 bufs1 = q0)) as [<-|NEq]; [rewrite Ldead12, Fbufs1; reflexivity|]. rewrite (LEQ12 q0 (fun EE => NEq (eq_sym EE))). apply LDEL8. clear - Hq NEq. cbn [In] in *. tauto. }
  pose proof (eq_trans (LEQ12 _ NE_pixs_bufs1) Lpixs_a8) as Lpixs_a9.
  pose proof (eq_trans (LEQ12 _ NE_data_bufs1) Ldata_a8) as Ldata_a9.
  pose proof (eq_trans (LEQ12 _ NE_pixd_bufs1) Lpixd_a8) as Lpixd_a9.
  pose proof (eq_trans (LEQ12 _ NE_datad_bufs1) Ldatad_a8) as Ldatad_a9.
  pose proof (eq_trans (LEQ12 _ NE_pixt_bufs1) Lpixt_a8) as Lpixt_a9.
  pose proof (eq_trans (LEQ12 _ NE_datat_bufs1) Ldatat_a8) as Ldatat_a9.
  pose proof (eq_trans (LEQ12 _ (fun EE => NE_bufs1_bufs2 (eq_sym EE))) Lbufs2_a8) as Lbufs2_a9.
  pose proof (eq_trans (LEQ12 _ (fun EE => NE_bufs1_tabval (eq_sym EE))) Ltabval_a8) as Ltabval_a9.
  pose proof (eq_trans (LEQ12 _ (fun EE => NE_bufs1_tab38 (eq_sym EE))) Ltab38_a8) as Ltab38_a9.
  pose proof (eq_trans (LEQ12 _ (fun EE => NE_bufs1_tab14 (eq_sym EE))) Ltab14_a8) as Ltab14_a9.
  pose proof (eq_trans (LEQ12 _ (fun EE => NE_bufs1_cmd (eq_sym EE))) Lcmd_a8) as Lcmd_a9.
  pose proof (eq_trans (LEQ12 _ (fun EE => NE_bufs1_arrd (eq_sym EE))) Larrd_a8) as Larrd_a9.
  assert (PXd13 : PIXat m13 pixd (set_cmap (set_data (pix_hdr w h 2) datad) cmd)) by exact (exT_pix_livk A9 M12 m13 pixd _ PXdM12 (proj2 PMc12) Lpixd_a9).
  assert (PXt13 : PIXat m13 pixt (hdv w h 8 0 datat)) by exact (exT_pix_livk A9 M12 m13 pixt _ PXtM12 (proj2 PMc12) Lpixt_a9).
  assert (CMP13 : CMAPat m13 cmd (CMAPV arrd 2 4 4 0)) by exact (exT_cmap_livk A9 M12 m13 cmd _ CMPM12 (proj2 PMc12) Lcmd_a9).
  assert (PM13 : POSTM C A0 s m4 m13).
  { eapply POSTM_trans; [exact PM12|]. eapply POSTM_trans; [exact PMs12|]. apply (POSTM_sub C A0 A9 _ _ _ SUB9). apply (POSTM_mono C A9 (s + OFF12) s); [unfold OFF12; lia | exact PMc12]. }
  pose proof (RTR12 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM8) ltac:(clear - HkR'; unfold RK_cml, RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB MG17 RBpos; lia)) as RM9. rewrite !Z.sub_0_r in RM9.
  assert (KEPT12 : Forall (ex_region_kept E12 M12 m13) [(EVar 32, OFF12, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF12 256 M12 m13 E12 (EVar 32) CK (proj1 PMc12) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E12 M12 m13 _ [] _ HKc12 KEPT12) as HKk12.
  match type of HKk12 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E12 m13 kk') in HKk12 end.
  pose proof (regs_ok_agree 446%nat E12 (ex_envL vals12 r13 [exW_canary SEGS 415784 m13]) _ _ (vals_app_agree vals12 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa12.
  pose proof (exW_regs_call _ _ _ _ _ HRa12 (ex_regs_ok_junk vals12 r13 [exW_canary SEGS 415784 m13] 446%nat ltac:(vm_cast_no_check (eq_refl 446%nat))) CS12) as HRn13.
  clear HRa12.
  assert (HKa13 : know_ok SEGS (ex_envL vals12 r13 [exW_canary SEGS 415784 m13]) m13 _) by (exact (know_ok_agree SEGS 446%nat E12 _ m13 _ (vals_app_agree vals12 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk12)).
  rewrite (fr_denot_agree 446%nat E12 (ex_envL vals12 r13 [exW_canary SEGS 415784 m13]) _ fr2 (vals_app_agree vals12 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc12 HKk12 KEPT12 HC12 HWs12 PMs12 Q10_12 Q1_12 Q2_12 Q4_12 PM12 HW12 FRs12 PMc12 CS12 SUB8 RM8 Ldead12 LEQ12 RTR12 Lbufs1_a8 OFF12 LDEL8 Lpixs_a8 Ldata_a8 Lpixd_a8 Ldatad_a8 Lpixt_a8 Ldatat_a8 Lbufs2_a8 Ltabval_a8 Ltab38_a8 Ltab14_a8 Lcmd_a8 Larrd_a8 PXdM12 PXd12 PXtM12 PXt12 CMPM12 CMP12.
  subst M12. clear log12. clear E12. try clear Rc12. clear KN12.
  lazymatch type of HRn13 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn13 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A9 m13 _ (s - 256) (Z.to_nat 256) CK HW13 GLO1 GLO2) as SOK13.
  pose proof (exW_canary_ok SEGS 415784 m13 (canary_any m13)) as CANOK13.
  pose (vals13 := vals12 ++ map (getr r13) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m13]).
  pose proof (exW_kn_fixed SEGS C A9 m13 _ (ex_envL vals12 r13 [exW_canary SEGS 415784 m13]) (EVar 478) (EVar 32) (exW_canary SEGS 415784 m13) s 256 415784 65536 212992 213416 213568 213416 213568
                HW13 eq_refl (proj1 CANOK13) (proj2 CANOK13) eq_refl eq_refl eq_refl SOK13 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf13.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf13 HKa13)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn13 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN13 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf13 HKa13 SOK13 CANOK13.
  repeat match goal with H : getr r13 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc13 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E13 := EEx) in HR, Hlf, HK, Hms |- *; set (log13 := LLx) in Hms, Hlf; set (M13 := mem_denot E13 m13 log13) in Hms end.
  assert (WP13 : W C A9 M13 (with_vmmaps vm9 md) /\ POSTM C A0 s m13 M13).
  { subst M13. apply (exW_win_blks C A9 A0 m13 _ E13 log13 (EVar 32) s 256 [] CK HW13 SUB9 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP13 as [HWs13 PMs13].
  pose proof (exW_win_only E13 m13 log13 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs13. change (mem_denot E13 m13 log13) with M13 in FRs13.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log13 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC13 : carry log13 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc13 : know_ok SEGS E13 M13 kn1) by (apply (carry_after SEGS E13 m13 log13 kn0 [] kn1 scs hs HC13 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW13)) | exact (mp_lazy _ (w_pure _ _ _ _ HW13)) | exact Hms |].
  pose (BS13 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, pixt); (173%nat, datat); (174%nat, wpl_of w 8); (208%nat, bufs1); (242%nat, bufs2); (276%nat, tabval); (310%nat, tab38); (344%nat, tab14); (411%nat, cmd)]).
  exW_regfactB BS13 HR ex_r10 Q10_13. exW_regfactB BS13 HR ex_r1 Q1_13. exW_regfactB BS13 HR ex_r2 Q2_13. exW_regfactB BS13 HR ex_r4 Q4_13.
  clear BS13.
  lazymatch type of Q2_13 with _ = Z_to_bv 64 (s + ?off) => pose (OFF13 := off) end.
  (* [comment removed for export] *)
  assert (PXdM13 : PIXat M13 pixd (set_cmap (set_data (pix_hdr w h 2) datad) cmd)) by exact (exT_pix_sess C A9 m13 M13 _ s 256 pixd _ CK HW13 GLO1 Lpixd_a9 PXd13 FRs13).
  assert (PXtM13 : PIXat M13 pixt (hdv w h 8 0 datat)) by exact (exT_pix_sess C A9 m13 M13 _ s 256 pixt _ CK HW13 GLO1 Lpixt_a9 PXt13 FRs13).
  assert (CMPM13 : CMAPat M13 cmd (CMAPV arrd 2 4 4 0)) by exact (exT_cmap_sess C A9 m13 M13 _ s 256 cmd _ CK HW13 GLO1 Lcmd_a9 CMP13 FRs13).
  lazymatch type of Q1_13 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_13 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A9 M13 _ Rc13 (Z_to_bv 64 bufs2) (Z_to_bv 64 ret) (4 * wpl_of w 8) sp' S CK HWs13 Q10_13 Lbufs2_a9 F0bufs2 Q1_13
             ltac:(red; apply bv_eq; reflexivity) Q4_13 Q2_13 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF13, ALLOC_STACK; clear - Hlo1; lia) ltac:(unfold OFF13; clear - Hhi; lia)) end end end.
  intros A10 m14 vm10 r14 HW14 CSx13 Ldead13 LEQ13 PMc13 RTR13.
  pose proof CSx13 as CS13. clear CSx13.
  rewrite with_vmmaps_twice in HW14 |- *.
  assert (SUB10 : sub_live A0 A10).
  { intros q0 kq Lq. rewrite (LEQ13 q0 (ne_live A0 q0 _ kq Lq Fbufs2)). exact (SUB9 q0 kq Lq). }
  assert (LDEL10 : forall q0 : word, ~ In q0 [Z_to_bv 64 cmd; Z_to_bv 64 arrd; Z_to_bv 64 tab14; Z_to_bv 64 tab38; Z_to_bv 64 tabval; Z_to_bv 64 pixt; Z_to_bv 64 datat; Z_to_bv 64 pixd; Z_to_bv 64 datad] -> live A10 q0 = live A0 q0).
  { intros q0 Hq. destruct (decide (Z_to_bv 64 bufs2 = q0)) as [<-|NEq]; [rewrite Ldead13, Fbufs2; reflexivity|]. rewrite (LEQ13 q0 (fun EE => NEq (eq_sym EE))). apply LDEL9. clear - Hq NEq. cbn [In] in *. tauto. }
  pose proof (eq_trans (LEQ13 _ NE_pixs_bufs2) Lpixs_a9) as Lpixs_a10.
  pose proof (eq_trans (LEQ13 _ NE_data_bufs2) Ldata_a9) as Ldata_a10.
  pose proof (eq_trans (LEQ13 _ NE_pixd_bufs2) Lpixd_a9) as Lpixd_a10.
  pose proof (eq_trans (LEQ13 _ NE_datad_bufs2) Ldatad_a9) as Ldatad_a10.
  pose proof (eq_trans (LEQ13 _ NE_pixt_bufs2) Lpixt_a9) as Lpixt_a10.
  pose proof (eq_trans (LEQ13 _ NE_datat_bufs2) Ldatat_a9) as Ldatat_a10.
  pose proof (eq_trans (LEQ13 _ (fun EE => NE_bufs2_tabval (eq_sym EE))) Ltabval_a9) as Ltabval_a10.
  pose proof (eq_trans (LEQ13 _ (fun EE => NE_bufs2_tab38 (eq_sym EE))) Ltab38_a9) as Ltab38_a10.
  pose proof (eq_trans (LEQ13 _ (fun EE => NE_bufs2_tab14 (eq_sym EE))) Ltab14_a9) as Ltab14_a10.
  pose proof (eq_trans (LEQ13 _ (fun EE => NE_bufs2_cmd (eq_sym EE))) Lcmd_a9) as Lcmd_a10.
  pose proof (eq_trans (LEQ13 _ (fun EE => NE_bufs2_arrd (eq_sym EE))) Larrd_a9) as Larrd_a10.
  assert (PXd14 : PIXat m14 pixd (set_cmap (set_data (pix_hdr w h 2) datad) cmd)) by exact (exT_pix_livk A10 M13 m14 pixd _ PXdM13 (proj2 PMc13) Lpixd_a10).
  assert (PXt14 : PIXat m14 pixt (hdv w h 8 0 datat)) by exact (exT_pix_livk A10 M13 m14 pixt _ PXtM13 (proj2 PMc13) Lpixt_a10).
  assert (CMP14 : CMAPat m14 cmd (CMAPV arrd 2 4 4 0)) by exact (exT_cmap_livk A10 M13 m14 cmd _ CMPM13 (proj2 PMc13) Lcmd_a10).
  assert (PM14 : POSTM C A0 s m4 m14).
  { eapply POSTM_trans; [exact PM13|]. eapply POSTM_trans; [exact PMs13|]. apply (POSTM_sub C A0 A10 _ _ _ SUB10). apply (POSTM_mono C A10 (s + OFF13) s); [unfold OFF13; lia | exact PMc13]. }
  pose proof (RTR13 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM9) ltac:(clear - HkR'; unfold RK_cml, RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB MG17 RBpos; lia)) as RM10. rewrite !Z.sub_0_r in RM10.
  assert (KEPT13 : Forall (ex_region_kept E13 M13 m14) [(EVar 32, OFF13, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF13 256 M13 m14 E13 (EVar 32) CK (proj1 PMc13) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E13 M13 m14 _ [] _ HKc13 KEPT13) as HKk13.
  match type of HKk13 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E13 m14 kk') in HKk13 end.
  pose proof (regs_ok_agree 479%nat E13 (ex_envL vals13 r14 [exW_canary SEGS 415784 m14]) _ _ (vals_app_agree vals13 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa13.
  pose proof (exW_regs_call _ _ _ _ _ HRa13 (ex_regs_ok_junk vals13 r14 [exW_canary SEGS 415784 m14] 479%nat ltac:(vm_cast_no_check (eq_refl 479%nat))) CS13) as HRn14.
  clear HRa13.
  assert (HKa14 : know_ok SEGS (ex_envL vals13 r14 [exW_canary SEGS 415784 m14]) m14 _) by (exact (know_ok_agree SEGS 479%nat E13 _ m14 _ (vals_app_agree vals13 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk13)).
  rewrite (fr_denot_agree 479%nat E13 (ex_envL vals13 r14 [exW_canary SEGS 415784 m14]) _ fr2 (vals_app_agree vals13 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc13 HKk13 KEPT13 HC13 HWs13 PMs13 Q10_13 Q1_13 Q2_13 Q4_13 PM13 HW13 FRs13 PMc13 CS13 SUB9 RM9 Ldead13 LEQ13 RTR13 Lbufs2_a9 OFF13 LDEL9 Lpixs_a9 Ldata_a9 Lpixd_a9 Ldatad_a9 Lpixt_a9 Ldatat_a9 Ltabval_a9 Ltab38_a9 Ltab14_a9 Lcmd_a9 Larrd_a9 PXdM13 PXd13 PXtM13 PXt13 CMPM13 CMP13.
  subst M13. clear log13. clear E13. try clear Rc13. clear KN13.
  lazymatch type of HRn14 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn14 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A10 m14 _ (s - 256) (Z.to_nat 256) CK HW14 GLO1 GLO2) as SOK14.
  pose proof (exW_canary_ok SEGS 415784 m14 (canary_any m14)) as CANOK14.
  pose (vals14 := vals13 ++ map (getr r14) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m14]).
  pose proof (exW_kn_fixed SEGS C A10 m14 _ (ex_envL vals13 r14 [exW_canary SEGS 415784 m14]) (EVar 511) (EVar 32) (exW_canary SEGS 415784 m14) s 256 415784 65536 212992 213416 213568 213416 213568
                HW14 eq_refl (proj1 CANOK14) (proj2 CANOK14) eq_refl eq_refl eq_refl SOK14 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf14.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf14 HKa14)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn14 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN14 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf14 HKa14 SOK14 CANOK14.
  repeat match goal with H : getr r14 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc14 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E14 := EEx) in HR, Hlf, HK, Hms |- *; set (log14 := LLx) in Hms, Hlf; set (M14 := mem_denot E14 m14 log14) in Hms end.
  assert (WP14 : W C A10 M14 (with_vmmaps vm10 md) /\ POSTM C A0 s m14 M14).
  { subst M14. apply (exW_win_blks C A10 A0 m14 _ E14 log14 (EVar 32) s 256 [] CK HW14 SUB10 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP14 as [HWs14 PMs14].
  pose proof (exW_win_only E14 m14 log14 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs14. change (mem_denot E14 m14 log14) with M14 in FRs14.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log14 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC14 : carry log14 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc14 : know_ok SEGS E14 M14 kn1) by (apply (carry_after SEGS E14 m14 log14 kn0 [] kn1 scs hs HC14 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW14)) | exact (mp_lazy _ (w_pure _ _ _ _ HW14)) | exact Hms |].
  pose (BS14 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, pixt); (173%nat, datat); (174%nat, wpl_of w 8); (208%nat, bufs1); (242%nat, bufs2); (276%nat, tabval); (310%nat, tab38); (344%nat, tab14); (411%nat, cmd)]).
  exW_regfactB BS14 HR ex_r10 Q10_14. exW_regfactB BS14 HR ex_r1 Q1_14. exW_regfactB BS14 HR ex_r2 Q2_14. exW_regfactB BS14 HR ex_r4 Q4_14.
  clear BS14.
  lazymatch type of Q2_14 with _ = Z_to_bv 64 (s + ?off) => pose (OFF14 := off) end.
  (* [comment removed for export] *)
  assert (PXdM14 : PIXat M14 pixd (set_cmap (set_data (pix_hdr w h 2) datad) cmd)) by exact (exT_pix_sess C A10 m14 M14 _ s 256 pixd _ CK HW14 GLO1 Lpixd_a10 PXd14 FRs14).
  assert (PXtM14 : PIXat M14 pixt (hdv w h 8 0 datat)) by exact (exT_pix_sess C A10 m14 M14 _ s 256 pixt _ CK HW14 GLO1 Lpixt_a10 PXt14 FRs14).
  assert (CMPM14 : CMAPat M14 cmd (CMAPV arrd 2 4 4 0)) by exact (exT_cmap_sess C A10 m14 M14 _ s 256 cmd _ CK HW14 GLO1 Lcmd_a10 CMP14 FRs14).
  lazymatch type of Q1_14 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_14 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A10 M14 _ Rc14 (Z_to_bv 64 tabval) (Z_to_bv 64 ret) (1024) sp' S CK HWs14 Q10_14 Ltabval_a10 F0tabval Q1_14
             ltac:(red; apply bv_eq; reflexivity) Q4_14 Q2_14 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF14, ALLOC_STACK; clear - Hlo1; lia) ltac:(unfold OFF14; clear - Hhi; lia)) end end end.
  intros A11 m15 vm11 r15 HW15 CSx14 Ldead14 LEQ14 PMc14 RTR14.
  pose proof CSx14 as CS14. clear CSx14.
  rewrite with_vmmaps_twice in HW15 |- *.
  assert (SUB11 : sub_live A0 A11).
  { intros q0 kq Lq. rewrite (LEQ14 q0 (ne_live A0 q0 _ kq Lq Ftabval)). exact (SUB10 q0 kq Lq). }
  assert (LDEL11 : forall q0 : word, ~ In q0 [Z_to_bv 64 cmd; Z_to_bv 64 arrd; Z_to_bv 64 tab14; Z_to_bv 64 tab38; Z_to_bv 64 pixt; Z_to_bv 64 datat; Z_to_bv 64 pixd; Z_to_bv 64 datad] -> live A11 q0 = live A0 q0).
  { intros q0 Hq. destruct (decide (Z_to_bv 64 tabval = q0)) as [<-|NEq]; [rewrite Ldead14, Ftabval; reflexivity|]. rewrite (LEQ14 q0 (fun EE => NEq (eq_sym EE))). apply LDEL10. clear - Hq NEq. cbn [In] in *. tauto. }
  pose proof (eq_trans (LEQ14 _ NE_pixs_tabval) Lpixs_a10) as Lpixs_a11.
  pose proof (eq_trans (LEQ14 _ NE_data_tabval) Ldata_a10) as Ldata_a11.
  pose proof (eq_trans (LEQ14 _ NE_pixd_tabval) Lpixd_a10) as Lpixd_a11.
  pose proof (eq_trans (LEQ14 _ NE_datad_tabval) Ldatad_a10) as Ldatad_a11.
  pose proof (eq_trans (LEQ14 _ NE_pixt_tabval) Lpixt_a10) as Lpixt_a11.
  pose proof (eq_trans (LEQ14 _ NE_datat_tabval) Ldatat_a10) as Ldatat_a11.
  pose proof (eq_trans (LEQ14 _ (fun EE => NE_tabval_tab38 (eq_sym EE))) Ltab38_a10) as Ltab38_a11.
  pose proof (eq_trans (LEQ14 _ (fun EE => NE_tabval_tab14 (eq_sym EE))) Ltab14_a10) as Ltab14_a11.
  pose proof (eq_trans (LEQ14 _ (fun EE => NE_tabval_cmd (eq_sym EE))) Lcmd_a10) as Lcmd_a11.
  pose proof (eq_trans (LEQ14 _ (fun EE => NE_tabval_arrd (eq_sym EE))) Larrd_a10) as Larrd_a11.
  assert (PXd15 : PIXat m15 pixd (set_cmap (set_data (pix_hdr w h 2) datad) cmd)) by exact (exT_pix_livk A11 M14 m15 pixd _ PXdM14 (proj2 PMc14) Lpixd_a11).
  assert (PXt15 : PIXat m15 pixt (hdv w h 8 0 datat)) by exact (exT_pix_livk A11 M14 m15 pixt _ PXtM14 (proj2 PMc14) Lpixt_a11).
  assert (CMP15 : CMAPat m15 cmd (CMAPV arrd 2 4 4 0)) by exact (exT_cmap_livk A11 M14 m15 cmd _ CMPM14 (proj2 PMc14) Lcmd_a11).
  assert (PM15 : POSTM C A0 s m4 m15).
  { eapply POSTM_trans; [exact PM14|]. eapply POSTM_trans; [exact PMs14|]. apply (POSTM_sub C A0 A11 _ _ _ SUB11). apply (POSTM_mono C A11 (s + OFF14) s); [unfold OFF14; lia | exact PMc14]. }
  pose proof (RTR14 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM10) ltac:(clear - HkR'; unfold RK_cml, RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB MG17 RBpos; lia)) as RM11. rewrite !Z.sub_0_r in RM11.
  assert (KEPT14 : Forall (ex_region_kept E14 M14 m15) [(EVar 32, OFF14, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF14 256 M14 m15 E14 (EVar 32) CK (proj1 PMc14) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E14 M14 m15 _ [] _ HKc14 KEPT14) as HKk14.
  match type of HKk14 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E14 m15 kk') in HKk14 end.
  pose proof (regs_ok_agree 512%nat E14 (ex_envL vals14 r15 [exW_canary SEGS 415784 m15]) _ _ (vals_app_agree vals14 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa14.
  pose proof (exW_regs_call _ _ _ _ _ HRa14 (ex_regs_ok_junk vals14 r15 [exW_canary SEGS 415784 m15] 512%nat ltac:(vm_cast_no_check (eq_refl 512%nat))) CS14) as HRn15.
  clear HRa14.
  assert (HKa15 : know_ok SEGS (ex_envL vals14 r15 [exW_canary SEGS 415784 m15]) m15 _) by (exact (know_ok_agree SEGS 512%nat E14 _ m15 _ (vals_app_agree vals14 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk14)).
  rewrite (fr_denot_agree 512%nat E14 (ex_envL vals14 r15 [exW_canary SEGS 415784 m15]) _ fr2 (vals_app_agree vals14 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc14 HKk14 KEPT14 HC14 HWs14 PMs14 Q10_14 Q1_14 Q2_14 Q4_14 PM14 HW14 FRs14 PMc14 CS14 SUB10 RM10 Ldead14 LEQ14 RTR14 Ltabval_a10 OFF14 LDEL10 Lpixs_a10 Ldata_a10 Lpixd_a10 Ldatad_a10 Lpixt_a10 Ldatat_a10 Ltab38_a10 Ltab14_a10 Lcmd_a10 Larrd_a10 PXdM14 PXd14 PXtM14 PXt14 CMPM14 CMP14.
  subst M14. clear log14. clear E14. try clear Rc14. clear KN14.
  lazymatch type of HRn15 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn15 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A11 m15 _ (s - 256) (Z.to_nat 256) CK HW15 GLO1 GLO2) as SOK15.
  pose proof (exW_canary_ok SEGS 415784 m15 (canary_any m15)) as CANOK15.
  pose (vals15 := vals14 ++ map (getr r15) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m15]).
  pose proof (exW_kn_fixed SEGS C A11 m15 _ (ex_envL vals14 r15 [exW_canary SEGS 415784 m15]) (EVar 544) (EVar 32) (exW_canary SEGS 415784 m15) s 256 415784 65536 212992 213416 213568 213416 213568
                HW15 eq_refl (proj1 CANOK15) (proj2 CANOK15) eq_refl eq_refl eq_refl SOK15 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf15.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf15 HKa15)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn15 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN15 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf15 HKa15 SOK15 CANOK15.
  repeat match goal with H : getr r15 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc15 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E15 := EEx) in HR, Hlf, HK, Hms |- *; set (log15 := LLx) in Hms, Hlf; set (M15 := mem_denot E15 m15 log15) in Hms end.
  assert (WP15 : W C A11 M15 (with_vmmaps vm11 md) /\ POSTM C A0 s m15 M15).
  { subst M15. apply (exW_win_blks C A11 A0 m15 _ E15 log15 (EVar 32) s 256 [] CK HW15 SUB11 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP15 as [HWs15 PMs15].
  pose proof (exW_win_only E15 m15 log15 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs15. change (mem_denot E15 m15 log15) with M15 in FRs15.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log15 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC15 : carry log15 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc15 : know_ok SEGS E15 M15 kn1) by (apply (carry_after SEGS E15 m15 log15 kn0 [] kn1 scs hs HC15 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW15)) | exact (mp_lazy _ (w_pure _ _ _ _ HW15)) | exact Hms |].
  pose (BS15 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, pixt); (173%nat, datat); (174%nat, wpl_of w 8); (208%nat, bufs1); (242%nat, bufs2); (276%nat, tabval); (310%nat, tab38); (344%nat, tab14); (411%nat, cmd)]).
  exW_regfactB BS15 HR ex_r10 Q10_15. exW_regfactB BS15 HR ex_r1 Q1_15. exW_regfactB BS15 HR ex_r2 Q2_15. exW_regfactB BS15 HR ex_r4 Q4_15.
  clear BS15.
  lazymatch type of Q2_15 with _ = Z_to_bv 64 (s + ?off) => pose (OFF15 := off) end.
  (* [comment removed for export] *)
  assert (PXdM15 : PIXat M15 pixd (set_cmap (set_data (pix_hdr w h 2) datad) cmd)) by exact (exT_pix_sess C A11 m15 M15 _ s 256 pixd _ CK HW15 GLO1 Lpixd_a11 PXd15 FRs15).
  assert (PXtM15 : PIXat M15 pixt (hdv w h 8 0 datat)) by exact (exT_pix_sess C A11 m15 M15 _ s 256 pixt _ CK HW15 GLO1 Lpixt_a11 PXt15 FRs15).
  assert (CMPM15 : CMAPat M15 cmd (CMAPV arrd 2 4 4 0)) by exact (exT_cmap_sess C A11 m15 M15 _ s 256 cmd _ CK HW15 GLO1 Lcmd_a11 CMP15 FRs15).
  lazymatch type of Q1_15 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_15 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A11 M15 _ Rc15 (Z_to_bv 64 tab38) (Z_to_bv 64 ret) (1024) sp' S CK HWs15 Q10_15 Ltab38_a11 F0tab38 Q1_15
             ltac:(red; apply bv_eq; reflexivity) Q4_15 Q2_15 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF15, ALLOC_STACK; clear - Hlo1; lia) ltac:(unfold OFF15; clear - Hhi; lia)) end end end.
  intros A12 m16 vm12 r16 HW16 CSx15 Ldead15 LEQ15 PMc15 RTR15.
  pose proof CSx15 as CS15. clear CSx15.
  rewrite with_vmmaps_twice in HW16 |- *.
  assert (SUB12 : sub_live A0 A12).
  { intros q0 kq Lq. rewrite (LEQ15 q0 (ne_live A0 q0 _ kq Lq Ftab38)). exact (SUB11 q0 kq Lq). }
  assert (LDEL12 : forall q0 : word, ~ In q0 [Z_to_bv 64 cmd; Z_to_bv 64 arrd; Z_to_bv 64 tab14; Z_to_bv 64 pixt; Z_to_bv 64 datat; Z_to_bv 64 pixd; Z_to_bv 64 datad] -> live A12 q0 = live A0 q0).
  { intros q0 Hq. destruct (decide (Z_to_bv 64 tab38 = q0)) as [<-|NEq]; [rewrite Ldead15, Ftab38; reflexivity|]. rewrite (LEQ15 q0 (fun EE => NEq (eq_sym EE))). apply LDEL11. clear - Hq NEq. cbn [In] in *. tauto. }
  pose proof (eq_trans (LEQ15 _ NE_pixs_tab38) Lpixs_a11) as Lpixs_a12.
  pose proof (eq_trans (LEQ15 _ NE_data_tab38) Ldata_a11) as Ldata_a12.
  pose proof (eq_trans (LEQ15 _ NE_pixd_tab38) Lpixd_a11) as Lpixd_a12.
  pose proof (eq_trans (LEQ15 _ NE_datad_tab38) Ldatad_a11) as Ldatad_a12.
  pose proof (eq_trans (LEQ15 _ NE_pixt_tab38) Lpixt_a11) as Lpixt_a12.
  pose proof (eq_trans (LEQ15 _ NE_datat_tab38) Ldatat_a11) as Ldatat_a12.
  pose proof (eq_trans (LEQ15 _ (fun EE => NE_tab38_tab14 (eq_sym EE))) Ltab14_a11) as Ltab14_a12.
  pose proof (eq_trans (LEQ15 _ (fun EE => NE_tab38_cmd (eq_sym EE))) Lcmd_a11) as Lcmd_a12.
  pose proof (eq_trans (LEQ15 _ (fun EE => NE_tab38_arrd (eq_sym EE))) Larrd_a11) as Larrd_a12.
  assert (PXd16 : PIXat m16 pixd (set_cmap (set_data (pix_hdr w h 2) datad) cmd)) by exact (exT_pix_livk A12 M15 m16 pixd _ PXdM15 (proj2 PMc15) Lpixd_a12).
  assert (PXt16 : PIXat m16 pixt (hdv w h 8 0 datat)) by exact (exT_pix_livk A12 M15 m16 pixt _ PXtM15 (proj2 PMc15) Lpixt_a12).
  assert (CMP16 : CMAPat m16 cmd (CMAPV arrd 2 4 4 0)) by exact (exT_cmap_livk A12 M15 m16 cmd _ CMPM15 (proj2 PMc15) Lcmd_a12).
  assert (PM16 : POSTM C A0 s m4 m16).
  { eapply POSTM_trans; [exact PM15|]. eapply POSTM_trans; [exact PMs15|]. apply (POSTM_sub C A0 A12 _ _ _ SUB12). apply (POSTM_mono C A12 (s + OFF15) s); [unfold OFF15; lia | exact PMc15]. }
  pose proof (RTR15 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM11) ltac:(clear - HkR'; unfold RK_cml, RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB MG17 RBpos; lia)) as RM12. rewrite !Z.sub_0_r in RM12.
  assert (KEPT15 : Forall (ex_region_kept E15 M15 m16) [(EVar 32, OFF15, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF15 256 M15 m16 E15 (EVar 32) CK (proj1 PMc15) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E15 M15 m16 _ [] _ HKc15 KEPT15) as HKk15.
  match type of HKk15 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E15 m16 kk') in HKk15 end.
  pose proof (regs_ok_agree 545%nat E15 (ex_envL vals15 r16 [exW_canary SEGS 415784 m16]) _ _ (vals_app_agree vals15 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa15.
  pose proof (exW_regs_call _ _ _ _ _ HRa15 (ex_regs_ok_junk vals15 r16 [exW_canary SEGS 415784 m16] 545%nat ltac:(vm_cast_no_check (eq_refl 545%nat))) CS15) as HRn16.
  clear HRa15.
  assert (HKa16 : know_ok SEGS (ex_envL vals15 r16 [exW_canary SEGS 415784 m16]) m16 _) by (exact (know_ok_agree SEGS 545%nat E15 _ m16 _ (vals_app_agree vals15 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk15)).
  rewrite (fr_denot_agree 545%nat E15 (ex_envL vals15 r16 [exW_canary SEGS 415784 m16]) _ fr2 (vals_app_agree vals15 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc15 HKk15 KEPT15 HC15 HWs15 PMs15 Q10_15 Q1_15 Q2_15 Q4_15 PM15 HW15 FRs15 PMc15 CS15 SUB11 RM11 Ldead15 LEQ15 RTR15 Ltab38_a11 OFF15 LDEL11 Lpixs_a11 Ldata_a11 Lpixd_a11 Ldatad_a11 Lpixt_a11 Ldatat_a11 Ltab14_a11 Lcmd_a11 Larrd_a11 PXdM15 PXd15 PXtM15 PXt15 CMPM15 CMP15.
  subst M15. clear log15. clear E15. try clear Rc15. clear KN15.
  lazymatch type of HRn16 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn16 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A12 m16 _ (s - 256) (Z.to_nat 256) CK HW16 GLO1 GLO2) as SOK16.
  pose proof (exW_canary_ok SEGS 415784 m16 (canary_any m16)) as CANOK16.
  pose (vals16 := vals15 ++ map (getr r16) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m16]).
  pose proof (exW_kn_fixed SEGS C A12 m16 _ (ex_envL vals15 r16 [exW_canary SEGS 415784 m16]) (EVar 577) (EVar 32) (exW_canary SEGS 415784 m16) s 256 415784 65536 212992 213416 213568 213416 213568
                HW16 eq_refl (proj1 CANOK16) (proj2 CANOK16) eq_refl eq_refl eq_refl SOK16 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf16.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf16 HKa16)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn16 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN16 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf16 HKa16 SOK16 CANOK16.
  repeat match goal with H : getr r16 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc16 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E16 := EEx) in HR, Hlf, HK, Hms |- *; set (log16 := LLx) in Hms, Hlf; set (M16 := mem_denot E16 m16 log16) in Hms end.
  assert (WP16 : W C A12 M16 (with_vmmaps vm12 md) /\ POSTM C A0 s m16 M16).
  { subst M16. apply (exW_win_blks C A12 A0 m16 _ E16 log16 (EVar 32) s 256 [] CK HW16 SUB12 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP16 as [HWs16 PMs16].
  pose proof (exW_win_only E16 m16 log16 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs16. change (mem_denot E16 m16 log16) with M16 in FRs16.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log16 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC16 : carry log16 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc16 : know_ok SEGS E16 M16 kn1) by (apply (carry_after SEGS E16 m16 log16 kn0 [] kn1 scs hs HC16 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW16)) | exact (mp_lazy _ (w_pure _ _ _ _ HW16)) | exact Hms |].
  pose (BS16 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, pixt); (173%nat, datat); (174%nat, wpl_of w 8); (208%nat, bufs1); (242%nat, bufs2); (276%nat, tabval); (310%nat, tab38); (344%nat, tab14); (411%nat, cmd)]).
  exW_regfactB BS16 HR ex_r10 Q10_16. exW_regfactB BS16 HR ex_r1 Q1_16. exW_regfactB BS16 HR ex_r2 Q2_16. exW_regfactB BS16 HR ex_r4 Q4_16.
  clear BS16.
  lazymatch type of Q2_16 with _ = Z_to_bv 64 (s + ?off) => pose (OFF16 := off) end.
  (* [comment removed for export] *)
  assert (PXdM16 : PIXat M16 pixd (set_cmap (set_data (pix_hdr w h 2) datad) cmd)) by exact (exT_pix_sess C A12 m16 M16 _ s 256 pixd _ CK HW16 GLO1 Lpixd_a12 PXd16 FRs16).
  assert (PXtM16 : PIXat M16 pixt (hdv w h 8 0 datat)) by exact (exT_pix_sess C A12 m16 M16 _ s 256 pixt _ CK HW16 GLO1 Lpixt_a12 PXt16 FRs16).
  assert (CMPM16 : CMAPat M16 cmd (CMAPV arrd 2 4 4 0)) by exact (exT_cmap_sess C A12 m16 M16 _ s 256 cmd _ CK HW16 GLO1 Lcmd_a12 CMP16 FRs16).
  lazymatch type of Q1_16 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_16 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A12 M16 _ Rc16 (Z_to_bv 64 tab14) (Z_to_bv 64 ret) (1024) sp' S CK HWs16 Q10_16 Ltab14_a12 F0tab14 Q1_16
             ltac:(red; apply bv_eq; reflexivity) Q4_16 Q2_16 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF16, ALLOC_STACK; clear - Hlo1; lia) ltac:(unfold OFF16; clear - Hhi; lia)) end end end.
  intros A13 m17 vm13 r17 HW17 CSx16 Ldead16 LEQ16 PMc16 RTR16.
  pose proof CSx16 as CS16. clear CSx16.
  rewrite with_vmmaps_twice in HW17 |- *.
  assert (SUB13 : sub_live A0 A13).
  { intros q0 kq Lq. rewrite (LEQ16 q0 (ne_live A0 q0 _ kq Lq Ftab14)). exact (SUB12 q0 kq Lq). }
  assert (LDEL13 : forall q0 : word, ~ In q0 [Z_to_bv 64 cmd; Z_to_bv 64 arrd; Z_to_bv 64 pixt; Z_to_bv 64 datat; Z_to_bv 64 pixd; Z_to_bv 64 datad] -> live A13 q0 = live A0 q0).
  { intros q0 Hq. destruct (decide (Z_to_bv 64 tab14 = q0)) as [<-|NEq]; [rewrite Ldead16, Ftab14; reflexivity|]. rewrite (LEQ16 q0 (fun EE => NEq (eq_sym EE))). apply LDEL12. clear - Hq NEq. cbn [In] in *. tauto. }
  pose proof (eq_trans (LEQ16 _ NE_pixs_tab14) Lpixs_a12) as Lpixs_a13.
  pose proof (eq_trans (LEQ16 _ NE_data_tab14) Ldata_a12) as Ldata_a13.
  pose proof (eq_trans (LEQ16 _ NE_pixd_tab14) Lpixd_a12) as Lpixd_a13.
  pose proof (eq_trans (LEQ16 _ NE_datad_tab14) Ldatad_a12) as Ldatad_a13.
  pose proof (eq_trans (LEQ16 _ NE_pixt_tab14) Lpixt_a12) as Lpixt_a13.
  pose proof (eq_trans (LEQ16 _ NE_datat_tab14) Ldatat_a12) as Ldatat_a13.
  pose proof (eq_trans (LEQ16 _ (fun EE => NE_tab14_cmd (eq_sym EE))) Lcmd_a12) as Lcmd_a13.
  pose proof (eq_trans (LEQ16 _ (fun EE => NE_tab14_arrd (eq_sym EE))) Larrd_a12) as Larrd_a13.
  assert (PXd17 : PIXat m17 pixd (set_cmap (set_data (pix_hdr w h 2) datad) cmd)) by exact (exT_pix_livk A13 M16 m17 pixd _ PXdM16 (proj2 PMc16) Lpixd_a13).
  assert (PXt17 : PIXat m17 pixt (hdv w h 8 0 datat)) by exact (exT_pix_livk A13 M16 m17 pixt _ PXtM16 (proj2 PMc16) Lpixt_a13).
  assert (CMP17 : CMAPat m17 cmd (CMAPV arrd 2 4 4 0)) by exact (exT_cmap_livk A13 M16 m17 cmd _ CMPM16 (proj2 PMc16) Lcmd_a13).
  assert (PM17 : POSTM C A0 s m4 m17).
  { eapply POSTM_trans; [exact PM16|]. eapply POSTM_trans; [exact PMs16|]. apply (POSTM_sub C A0 A13 _ _ _ SUB13). apply (POSTM_mono C A13 (s + OFF16) s); [unfold OFF16; lia | exact PMc16]. }
  pose proof (RTR16 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM12) ltac:(clear - HkR'; unfold RK_cml, RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB MG17 RBpos; lia)) as RM13. rewrite !Z.sub_0_r in RM13.
  assert (KEPT16 : Forall (ex_region_kept E16 M16 m17) [(EVar 32, OFF16, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF16 256 M16 m17 E16 (EVar 32) CK (proj1 PMc16) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E16 M16 m17 _ [] _ HKc16 KEPT16) as HKk16.
  match type of HKk16 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E16 m17 kk') in HKk16 end.
  pose proof (regs_ok_agree 578%nat E16 (ex_envL vals16 r17 [exW_canary SEGS 415784 m17]) _ _ (vals_app_agree vals16 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa16.
  pose proof (exW_regs_call _ _ _ _ _ HRa16 (ex_regs_ok_junk vals16 r17 [exW_canary SEGS 415784 m17] 578%nat ltac:(vm_cast_no_check (eq_refl 578%nat))) CS16) as HRn17.
  clear HRa16.
  assert (HKa17 : know_ok SEGS (ex_envL vals16 r17 [exW_canary SEGS 415784 m17]) m17 _) by (exact (know_ok_agree SEGS 578%nat E16 _ m17 _ (vals_app_agree vals16 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk16)).
  rewrite (fr_denot_agree 578%nat E16 (ex_envL vals16 r17 [exW_canary SEGS 415784 m17]) _ fr2 (vals_app_agree vals16 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc16 HKk16 KEPT16 HC16 HWs16 PMs16 Q10_16 Q1_16 Q2_16 Q4_16 PM16 HW16 FRs16 PMc16 CS16 SUB12 RM12 Ldead16 LEQ16 RTR16 Ltab14_a12 OFF16 LDEL12 Lpixs_a12 Ldata_a12 Lpixd_a12 Ldatad_a12 Lpixt_a12 Ldatat_a12 Lcmd_a12 Larrd_a12 PXdM16 PXd16 PXtM16 PXt16 CMPM16 CMP16.
  subst M16. clear log16. clear E16. try clear Rc16. clear KN16.
  lazymatch type of HRn17 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn17 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A13 m17 _ (s - 256) (Z.to_nat 256) CK HW17 GLO1 GLO2) as SOK17.
  pose proof (exW_canary_ok SEGS 415784 m17 (canary_any m17)) as CANOK17.
  pose (vals17 := vals16 ++ map (getr r17) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m17]).
  pose proof (exW_kn_fixed SEGS C A13 m17 _ (ex_envL vals16 r17 [exW_canary SEGS 415784 m17]) (EVar 610) (EVar 32) (exW_canary SEGS 415784 m17) s 256 415784 65536 212992 213416 213568 213416 213568
                HW17 eq_refl (proj1 CANOK17) (proj2 CANOK17) eq_refl eq_refl eq_refl SOK17 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf17.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf17 HKa17)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn17 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN17 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf17 HKa17 SOK17 CANOK17.
  repeat match goal with H : getr r17 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc17 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E17 := EEx) in HR, Hlf, HK, Hms |- *; set (log17 := LLx) in Hms, Hlf; set (M17 := mem_denot E17 m17 log17) in Hms end.
  assert (WP17 : W C A13 M17 (with_vmmaps vm13 md) /\ POSTM C A0 s m17 M17).
  { subst M17. apply (exW_win_blks C A13 A0 m17 _ E17 log17 (EVar 32) s 256 [] CK HW17 SUB13 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP17 as [HWs17 PMs17].
  pose proof (exW_win_only E17 m17 log17 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs17. change (mem_denot E17 m17 log17) with M17 in FRs17.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log17 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC17 : carry log17 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc17 : know_ok SEGS E17 M17 kn1) by (apply (carry_after SEGS E17 m17 log17 kn0 [] kn1 scs hs HC17 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW17)) | exact (mp_lazy _ (w_pure _ _ _ _ HW17)) | exact Hms |].
  pose (BS17 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, pixt); (173%nat, datat); (174%nat, wpl_of w 8); (208%nat, bufs1); (242%nat, bufs2); (276%nat, tabval); (310%nat, tab38); (344%nat, tab14); (411%nat, cmd)]).
  exW_regfactB BS17 HR ex_r10 Q10_17. exW_regfactB BS17 HR ex_r1 Q1_17. exW_regfactB BS17 HR ex_r2 Q2_17. exW_regfactB BS17 HR ex_r4 Q4_17.
  clear BS17.
  lazymatch type of Q2_17 with _ = Z_to_bv 64 (s + ?off) => pose (OFF17 := off) end.
  (* [comment removed for export] *)
  pose (BSx17 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, pixt); (173%nat, datat); (174%nat, wpl_of w 8); (208%nat, bufs1); (242%nat, bufs2); (276%nat, tabval); (310%nat, tab38); (344%nat, tab14); (411%nat, cmd)]).
  exW_cellB HK Hlf r0 BSx17 (EVar 32) s (-128)%Z 8%nat CELLpp.
  clear BSx17.
  assert (PXdM17 : PIXat M17 pixd (set_cmap (set_data (pix_hdr w h 2) datad) cmd)) by exact (exT_pix_sess C A13 m17 M17 _ s 256 pixd _ CK HW17 GLO1 Lpixd_a13 PXd17 FRs17).
  assert (PXtM17 : PIXat M17 pixt (hdv w h 8 0 datat)) by exact (exT_pix_sess C A13 m17 M17 _ s 256 pixt _ CK HW17 GLO1 Lpixt_a13 PXt17 FRs17).
  assert (CMPM17 : CMAPat M17 cmd (CMAPV arrd 2 4 4 0)) by exact (exT_cmap_sess C A13 m17 M17 _ s 256 cmd _ CK HW17 GLO1 Lcmd_a13 CMP17 FRs17).
  assert (PPlo : (s + OFF17 <= s + -128)%Z) by (unfold OFF17; lia). assert (PPhi : (s + -128 + 8 <= c_top C)%Z) by lia.
  rewrite PC_DESTROY_eq.
  lazymatch type of Q1_17 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixDestroy_keep_W (fx := fxk) C A13 M17 _ Rc17 (s + OFF17) (s + -128) pixt 0 0 (4 * (wpl_of w 8 * h)) (hdv w h 8 0 datat) cv (Z_to_bv 64 ra) S CK HWs17 Q2_17
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF17, ALLOC_STACK; clear - Hlo1; lia) PPlo PPhi Q1_17 ltac:(red; apply bv_eq; reflexivity) Q4_17 ltac:(rewrite <- Zplus_mod_idemp_l, Hs8; reflexivity) Q10_17 CELLpp
             PXtM17 eq_refl eq_refl eq_refl Lpixt_a13 F0pixt Ldatat_a13 F0datat Rns (fun EE => NEptdt (eq_sym EE)) (or_introl eq_refl)) end end.
  intros A14 m18 vm14 r18 HW18 CSx17 PDP PMc17 CELL0 FRMs17 RTR17.
  pose proof CSx17 as CS17. clear CSx17.
  rewrite with_vmmaps_twice in HW18 |- *.
  destruct PDP as (Dpixt & Ddatat & _ & LEQ17). change (p_data (hdv w h 8 0 datat)) with datat in Ddatat, LEQ17.
  assert (NZdatat : datat <> 0%Z) by lia.
  pose proof (fun (q0 : word) (N1 : q0 <> Z_to_bv 64 pixt) (N2 : q0 <> Z_to_bv 64 datat) => LEQ17 q0 N1 (fun _ => N2) (fun XX : 0%Z <> 0%Z => False_ind _ (XX eq_refl))) as LEQx17.
  pose proof (eq_trans (LEQx17 _ NE_pixd_pixt NE_pixd_datat) Lpixd_a13) as Lpixd_a14.
  pose proof (eq_trans (LEQx17 _ NE_datad_pixt NE_datad_datat) Ldatad_a13) as Ldatad_a14.
  pose proof (eq_trans (LEQx17 _ (fun EE => NE_pixt_cmd (eq_sym EE)) (fun EE => NE_datat_cmd (eq_sym EE))) Lcmd_a13) as Lcmd_a14.
  pose proof (eq_trans (LEQx17 _ (fun EE => NE_pixt_arrd (eq_sym EE)) (fun EE => NE_datat_arrd (eq_sym EE))) Larrd_a13) as Larrd_a14.
  assert (SUB14 : sub_live A0 A14).
  { intros q0 kq Lq. rewrite (LEQx17 q0 (ne_live A0 q0 _ kq Lq Fpixt) (ne_live A0 q0 _ kq Lq Fdatat)). exact (SUB13 _ _ Lq). }
  assert (LDEL14 : forall q0 : word, ~ In q0 [Z_to_bv 64 cmd; Z_to_bv 64 arrd; Z_to_bv 64 pixd; Z_to_bv 64 datad] -> live A14 q0 = live A0 q0).
  { intros q0 Hq. destruct (decide (Z_to_bv 64 pixt = q0)) as [<-|NEq1]; [rewrite Dpixt, Fpixt; reflexivity|].
    destruct (decide (Z_to_bv 64 datat = q0)) as [<-|NEq2]; [rewrite (Ddatat NZdatat), Fdatat; reflexivity|].
    rewrite (LEQx17 q0 (fun EE => NEq1 (eq_sym EE)) (fun EE => NEq2 (eq_sym EE))). apply LDEL13. clear - Hq NEq1 NEq2. cbn [In] in *. tauto. }
  pose proof (RTR17 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM13) ltac:(clear - HkR'; unfold RK_cml, RK_rmc, RK_pix in *; lia) ltac:(clear - HbR' MGB MG17 RBpos; lia)) as RM14. rewrite !Z.sub_0_r in RM14.
  assert (PMB18 : POSTM C A0 s m0 m18).
  { eapply POSTM_trans; [exact PMB4|]. eapply POSTM_trans; [exact (POSTM_trans _ _ _ _ _ _ PM17 PMs17)|]. apply (POSTM_sub C A0 A14 _ _ _ SUB14). apply (POSTM_mono C A14 (s + -128 + 8) s); [lia | exact PMc17]. }
  assert (PXd18 : PIXat m18 pixd (set_cmap (set_data (pix_hdr w h 2) datad) cmd)) by exact (exT_pix_livk A14 M17 m18 pixd _ PXdM17 (proj2 PMc17) Lpixd_a14).
  assert (CMP18 : CMAPat m18 cmd (CMAPV arrd 2 4 4 0)) by exact (exT_cmap_livk A14 M17 m18 cmd _ CMPM17 (proj2 PMc17) Lcmd_a14).
  assert (FRMx17 : FRM C (s + -120) M17 m18).
  { replace (s + -120)%Z with (s + -128 + 8)%Z by lia. exact (proj1 PMc17). }
  pose proof (POSTM_refl C A0 s m18) as PM18.
  assert (KEPT17 : Forall (ex_region_kept E17 M17 m18) [(EVar 32, (-120)%Z, 0%Z); (EVar 32, OFF17, (-128)%Z)]).
  { constructor; [exact (exW_kept_stack2 C s (-120) 256 M17 m18 E17 (EVar 32) CK FRMx17 Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exT_kept_in E17 M17 m18 (EVar 32) s OFF17 (-128) (s + OFF17) (s + -128) FRMs17 eq_refl RS (Z.le_refl _) (Z.le_refl _))|]. constructor. }
  pose proof (ex_know_keepD SEGS E17 M17 m18 _ [] _ HKc17 KEPT17) as HKk17.
  match type of HKk17 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E17 m18 kk') in HKk17 end.
  pose proof (regs_ok_agree 611%nat E17 (ex_envL vals17 r18 [exW_canary SEGS 415784 m18]) _ _ (vals_app_agree vals17 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa17.
  pose proof (exW_regs_call _ _ _ _ _ HRa17 (ex_regs_ok_junk vals17 r18 [exW_canary SEGS 415784 m18] 611%nat ltac:(vm_cast_no_check (eq_refl 611%nat))) CS17) as HRn18.
  clear HRa17.
  assert (HKa18 : know_ok SEGS (ex_envL vals17 r18 [exW_canary SEGS 415784 m18]) m18 _) by (exact (know_ok_agree SEGS 611%nat E17 _ m18 _ (vals_app_agree vals17 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk17)).
  rewrite (fr_denot_agree 611%nat E17 (ex_envL vals17 r18 [exW_canary SEGS 415784 m18]) _ fr2 (vals_app_agree vals17 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc17 HKk17 KEPT17 HC17 HWs17 PMs17 Q10_17 Q1_17 Q2_17 Q4_17 PM17 HW17 FRs17 CS17 OFF17 CELLpp PPlo PPhi PXdM17 PXd17 PXtM17 PXt17 CMPM17 CMP17 PMc17 FRMx17 CELL0 FRMs17 RTR17 LEQ17 LEQx17 LDEL13 PMB4 RM13.
  subst M17. clear log17. clear E17. try clear Rc17. clear KN17.
  lazymatch type of HRn18 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn18 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A14 m18 _ (s - 256) (Z.to_nat 256) CK HW18 GLO1 GLO2) as SOK18.
  pose proof (exW_canary_ok SEGS 415784 m18 (canary_any m18)) as CANOK18.
  pose (vals18 := vals17 ++ map (getr r18) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m18]).
  pose proof (exW_kn_fixed SEGS C A14 m18 _ (ex_envL vals17 r18 [exW_canary SEGS 415784 m18]) (EVar 643) (EVar 32) (exW_canary SEGS 415784 m18) s 256 415784 65536 212992 213416 213568 213416 213568
                HW18 eq_refl (proj1 CANOK18) (proj2 CANOK18) eq_refl eq_refl eq_refl SOK18 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf18.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf18 HKa18)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn18 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN18 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf18 HKa18 SOK18 CANOK18.
  repeat match goal with H : getr r18 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E18 := EEx) in HR, Hlf, HK, Hms |- *; set (log18 := LLx) in Hms, Hlf; set (M18 := mem_denot E18 m18 log18) in Hms end.
  assert (WP18 : W C A14 M18 (with_vmmaps vm14 md) /\ POSTM C A0 s m18 M18).
  { subst M18. apply (exW_win_blks C A14 A0 m18 _ E18 log18 (EVar 32) s 256 [] CK HW18 SUB14 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP18 as [HWs18 PMs18].
  pose proof (exW_win_only E18 m18 log18 (EVar 32) s 256 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs18. change (mem_denot E18 m18 log18) with M18 in FRs18.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW18)) | exact (mp_lazy _ (w_pure _ _ _ _ HW18)) | exact Hms |].
  pose (BSF := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, pixd); (71%nat, datad); (72%nat, wpl_of w 2); (172%nat, pixt); (173%nat, datat); (174%nat, wpl_of w 8); (208%nat, bufs1); (242%nat, bufs2); (276%nat, tabval); (310%nat, tab38); (344%nat, tab14); (411%nat, cmd)]).
  exW_regfactB BSF HR ex_r10 G10.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ => apply (HC fxk A14 M18 vm14 RcF FZ HWs18) end.
  + lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 RcF [(2%nat, EVar 32); (4%nat, ELit 284096)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor; [symmetry; exact HTP | constructor]] | vm_compute; reflexivity] end.
  + exact (POSTM_trans _ _ _ _ _ _ PMB18 PMs18).
  + right. exists pixd, datad, cmd, (CMAPV arrd 2 4 4 0). split; [exact G10|]. split; [|split; [clear - Gcmd1; lia | split; [reflexivity | split; reflexivity]]].
    refine (conj Gpd1 (conj Gpd2 (conj ALpixd (conj Gdd1 (conj Gdd2 (conj ALdatad (conj NEpd (conj Fpixd (conj Fdatad (conj F0pixd (conj F0datad (conj Lpixd_a14 (conj Ldatad_a14 (conj _ _)))))))))))))).
    * exact (exT_pix_sess C A14 m18 M18 _ s 256 pixd _ CK HW18 GLO1 Lpixd_a14 PXd18 FRs18).
    * right. exists arrd. cbn [c_d c_nalloc c_n].
      refine (conj CMOK (conj Gcmd1 (conj Gcmd2 (conj Garrd1 (conj _ (conj NEcmarr (conj _ (conj _ (conj _ (conj _ (conj Fcmd (conj Farrd (conj F0cmd (conj F0arrd (conj Lcmd_a14 (conj _ (conj _ _))))))))))))))))).
      -- exact Garrd2.
      -- intros EE. exact (NE_pixd_cmd (f_equal (Z_to_bv 64) (eq_sym EE))).
      -- intros EE. exact (NE_datad_cmd (f_equal (Z_to_bv 64) (eq_sym EE))).
      -- intros EE. exact (NE_pixd_arrd (f_equal (Z_to_bv 64) (eq_sym EE))).
      -- intros EE. exact (NE_datad_arrd (f_equal (Z_to_bv 64) (eq_sym EE))).
      -- exact Larrd_a14.
      -- exact (exT_cmap_sess C A14 m18 M18 _ s 256 cmd _ CK HW18 GLO1 Lcmd_a14 CMP18 FRs18).
      -- intros q0 N1 N2 N3 N4. apply LDEL14. clear - N1 N2 N3 N4. cbn [In]. intros [EE|[EE|[EE|[EE|[]]]]]; [apply N3 | apply N4 | apply N1 | apply N2]; symmetry; exact EE.
  + apply (aroom_mono _ _ _ _ _ _ RM14); [unfold RK_d2bpp; clear - HkR'; unfold RK_cml in *; lia | unfold RB_d2bpp; clear - HbR' MGB MG17 RBpos; lia].
Qed.
End Spec.
End Chain.
