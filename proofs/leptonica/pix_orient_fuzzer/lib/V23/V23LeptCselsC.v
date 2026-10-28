(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit FPSteps FPStepsV.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptRoom LeptExec LeptExecW LeptExecFP.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptDilW V23LeptSelDA V23LeptCselsA.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptExecSq.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptCselsA O23LeptCselsC.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptExecT LeptExecB.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Chain.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
(* [comment removed for export] *)
#[local] Existing Instance exf_fxd | 100.

Definition STOPS : list Z := [1107680; 1107992]%Z.
Definition FDEF : list (nat * nat) := [(8%nat, 33%nat)].   (* [comment removed for export] *)
Definition CSELS_WIN : Z := 4304.

(* [comment removed for export] *)
Lemma csels_chain30 : forall (fx : FPState) C A m md regs (s : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> frm_zero (@fp_csr fx) ->
  getr regs 2 = Z_to_bv 64 (s + -48) -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CSELS_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 1278416 ->
  getr regs 10 = Z_to_bv 64 30 -> getr regs 11 = Z_to_bv 64 1 -> getr regs 12 = Z_to_bv 64 (s + -16) -> getr regs 13 = Z_to_bv 64 (s + -24) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (6 <= kR)%Z -> (6 * 2 ^ 17 <= bR)%Z ->
  (forall (fr' : bvmap 5 word) (cs' : bv 32) A' m' vm' regs' (sel1 arr1 r1_0 sel2 arr2 r2_0 : Z),
     frm_zero cs' -> (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get (@fp_regs fx) r) ->
     W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> getr regs' 10 = Z_to_bv 64 0 ->
     sub_live A A' -> POSTM C A s m m' -> O23LeptCselsA.cs_fra s (-16) (-24) m m' ->
     aroom A' vm' (kR - 6) (bR - 6 * 2 ^ 17) ->
     cs_cell m' ((s + -16)%Z, 8%nat, sel1) -> cs_cell m' ((s + -24)%Z, 8%nat, sel2) ->
     cs_sel_facts C A A' m' sel1 arr1 1 6 0 3 [r1_0] [[1; 1; 1; 1; 1; 1]]%Z ->
     cs_sel_facts C A A' m' sel2 arr2 1 30 0 15 [r2_0] [[0; 0; 0; 1; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 1; 0; 0]]%Z ->
     List.NoDup (O23LeptCselsA.cs_words sel1 arr1 [r1_0] ++ O23LeptCselsA.cs_words sel2 arr2 [r2_0]) ->
     (forall q : word, ~ In q (O23LeptCselsA.cs_words sel1 arr1 [r1_0] ++ O23LeptCselsA.cs_words sel2 arr2 [r2_0]) -> live A' q = live A q) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 669044) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 s ret S CK HW0 HFZ H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 H13 kR bR RM0 HkR HbR HC.
  unfold CSELS_WIN in *.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 (s + -48))) by exact H2.
  assert (HTP : ex_keep (getr r0 ex_r4 = Z_to_bv 64 1278416)) by exact H4.
  destruct fx as [fr cs]. cbn [fp_csr] in HFZ. rename HFZ into FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  pose proof (O23LeptCselsA.cs_fra_refl s (-16) (-24) m0) as CF0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  replace kR with (kR - 0)%Z in RM0 by lia. replace bR with (bR - 0 * 2 ^ 17)%Z in RM0 by lia.
  pose (valsI := @nil word).
  pose proof (fun (q : word) (_ : ~ In q []) => eq_refl (live A0 q)) as LDEL0.
  assert (GLO1 : (c_top C - LSTK <= s - 4304)%Z) by lia.
  assert (GLO2 : (s - 4304 + Z.of_nat (Z.to_nat 4304) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (4304 <= s)%Z) by lia.
  pose proof (W_sok_win C A0 m0 _ (s - 4304) (Z.to_nat 4304) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 1410112 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0]) (EVar 34) (EVar 32) (exW_canary SEGS 1410112 m0) s 4304 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0]) m0 [KRange (EVar 32) 1425616 (2 ^ 63); KAlign (EVar 32) 16]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 HKf0)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exq_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 4304 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  assert (CFs0 : O23LeptCselsA.cs_fra s (-16) (-24) m0 M0).
  { subst M0. apply (cs_frame_sess C A0 A0 m0 m0 _ E0 log0 (EVar 32) s 4304 (-16) (-24) [] CK HW0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exact RS | lia | exact Hhi | reflexivity | | reflexivity | exact CF0]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r1 Q1_0. exW_regfactB BS0 HR ex_r2 Q2_0. exW_regfactB BS0 HR ex_r4 Q4_0.
  clear BS0.
  lazymatch type of Q2_0 with _ = Z_to_bv 64 (s + ?off) => pose (OFF0 := off) end.
  pose proof (alloc_margin_small (1 * 32) ltac:(exW_cmp)) as MG0.
  lazymatch type of Q1_0 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_0 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A0 M0 _ Rc0 1 32 (kR - 0) (bR - 0 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs0 Q10_0 Q11_0 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM0) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_0
             ltac:(red; apply bv_eq; reflexivity) Q4_0 Q2_0 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A1 m1 vm1 r1 res0 HW1 Hres0 CSx0 Hnz0 Fsel1x Lo0 F0sel1 LEQ0 ZERO0 ALsel1 TOP0 PMc0 RM1.
  pose proof CSx0 as CS0. clear CSx0.
  rewrite with_vmmaps_twice in HW1 |- *.
  assert (Eres0 : res0 = Z_to_bv 64 (u res0)) by (symmetry; apply zbv_self).
  pose proof (u64_range res0) as RRsel1. set (sel1 := u res0) in *. clearbody sel1. rewrite Eres0 in Hres0, Fsel1x, Lo0, F0sel1, LEQ0, ZERO0. clear Eres0.
  change (1 * 32)%Z with 32%Z in *.
  pose proof (exW_blk_img_apart_h2 C A1 m1 _ sel1 32 CK HW1 Lo0 RRsel1 eq_refl eq_refl) as IMGAPsel1. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPsel1.
  pose proof (exW_win_blk_apart_h C A1 m1 _ s 4304 sel1 32 CK HW1 Lo0 eq_refl RRsel1 GLO1) as WAPsel1.
  assert (Fsel1 : live A0 (Z_to_bv 64 sel1) = None).
  { destruct (live A0 (Z_to_bv 64 sel1)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB0 _ _ EE) as XX. first [discriminate Fsel1x | (rewrite Fsel1x in XX; discriminate XX)]. }
  pose proof Lo0 as Lsel1_a1.
  assert (SUB1 : sub_live A0 A1).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 sel1) by (intros ->; rewrite Fsel1 in Lq; discriminate Lq). rewrite (LEQ0 q NEq). exact (SUB0 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 sel1 :: [])) => eq_trans (LEQ0 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL0 q (fun XX => Hq (or_intror XX)))) as LDEL1.
  assert (PM1 : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|]. apply (POSTM_sub C A0 A0 _ _ _ SUB0).
    apply (POSTM_mono C A0 (s + OFF0) s); [unfold OFF0; lia | exact PMc0]. }
  pose proof (cs_frame_hop C s 4304 OFF0 (-16) (-24) m0 M0 m1 CK (proj1 PMc0) ltac:(lia) ltac:(vm_cast_no_check (eq_refl true)) ltac:(vm_cast_no_check (eq_refl true)) CFs0) as CF1.
  replace (kR - 0 - 1)%Z with (kR - 1)%Z in RM1 by lia. rewrite MG0 in RM1. replace (bR - 0 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 1 * 2 ^ 17)%Z in RM1 by lia.
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, OFF0, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF0 4304 M0 m1 E0 (EVar 32) CK (proj1 PMc0) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E0 m1 kk') in HKk0 end.
  pose proof (regs_ok_agree 35%nat E0 (ex_envL vals0 r1 [sel1; exW_canary SEGS 1410112 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [sel1; exW_canary SEGS 1410112 m1] 35%nat ltac:(vm_cast_no_check (eq_refl 35%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [sel1; exW_canary SEGS 1410112 m1]) m1 _) by (exact (know_ok_agree SEGS 35%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  rewrite (fr_denot_agree 35%nat E0 (ex_envL vals0 r1 [sel1; exW_canary SEGS 1410112 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r1 ex_r10 (EVar 67) HRn1 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres0)) as HRx1. clear HRn1. rename HRx1 into HRn1.
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q11_0 Q1_0 Q2_0 Q4_0 PM0 HW0 PMc0 CS0 SUB0 RM0 MG0 TOP0 LEQ0 Hnz0 Fsel1x Lo0 OFF0 LDEL0 CF0 CFs0.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  pose proof (exW_kn_blk SEGS C A1 m1 _ (ex_envL vals0 r1 [sel1; exW_canary SEGS 1410112 m1]) (EVar 67) (EVar 32) sel1 32 s 4304 65536 1347584 p16_segs CK HW1 Lsel1_a1 RRsel1 eq_refl eq_refl eq_refl RS ALsel1 ZERO0 WAPsel1 IMGAPsel1) as HKb1.
  pose proof (W_sok_win C A1 m1 _ (s - 4304) (Z.to_nat 4304) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 1410112 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [sel1; exW_canary SEGS 1410112 m1]).
  pose proof (exW_kn_fixed SEGS C A1 m1 _ (ex_envL vals0 r1 [sel1; exW_canary SEGS 1410112 m1]) (EVar 68) (EVar 32) (exW_canary SEGS 1410112 m1) s 4304 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb1 (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb1 HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  exq_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO0 ALsel1.
  exb_exit ST Rc1 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A1 M1 (with_vmmaps vm1 md) /\ POSTM C A0 s m1 M1).
  { subst M1. apply (exW_win_blks C A1 A0 m1 _ E1 log1 (EVar 32) s 4304 [(EVar 67, sel1, 32%Z)] CK HW1 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a1 (conj Fsel1 F0sel1))))|]. constructor. }
  assert (CFs1 : O23LeptCselsA.cs_fra s (-16) (-24) m0 M1).
  { subst M1. apply (cs_frame_sess C A1 A0 m0 m1 _ E1 log1 (EVar 32) s 4304 (-16) (-24) [(EVar 67, sel1, 32%Z)] CK HW1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exact RS | lia | exact Hhi | reflexivity | | reflexivity | exact CF1]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a1 (conj Fsel1 F0sel1))))|]. constructor. }
  destruct WP1 as [HWs1 PMs1].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log1 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC1 : carry log1 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc1 : know_ok SEGS E1 M1 kn1) by (apply (carry_after SEGS E1 m1 log1 kn0 [] kn1 scs hs HC1 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose (BS1 := [(32%nat, s); (67%nat, sel1)]).
  exW_regfactB BS1 HR ex_r10 Q10_1. exW_regfactB BS1 HR ex_r11 Q11_1. exW_regfactB BS1 HR ex_r1 Q1_1. exW_regfactB BS1 HR ex_r2 Q2_1. exW_regfactB BS1 HR ex_r4 Q4_1.
  clear BS1.
  lazymatch type of Q2_1 with _ = Z_to_bv 64 (s + ?off) => pose (OFF1 := off) end.
  pose proof (alloc_margin_small (1 * 8) ltac:(exW_cmp)) as MG1.
  lazymatch type of Q1_1 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_1 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A1 M1 _ Rc1 1 8 (kR - 1) (bR - 1 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs1 Q10_1 Q11_1 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM1) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_1
             ltac:(red; apply bv_eq; reflexivity) Q4_1 Q2_1 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A2 m2 vm2 r2 res1 HW2 Hres1 CSx1 Hnz1 Farr1x Lo1 F0arr1 LEQ1 ZERO1 ALarr1 TOP1 PMc1 RM2.
  pose proof CSx1 as CS1. clear CSx1.
  rewrite with_vmmaps_twice in HW2 |- *.
  assert (Eres1 : res1 = Z_to_bv 64 (u res1)) by (symmetry; apply zbv_self).
  pose proof (u64_range res1) as RRarr1. set (arr1 := u res1) in *. clearbody arr1. rewrite Eres1 in Hres1, Farr1x, Lo1, F0arr1, LEQ1, ZERO1. clear Eres1.
  change (1 * 8)%Z with 8%Z in *.
  pose proof (exW_blk_img_apart_h2 C A2 m2 _ arr1 8 CK HW2 Lo1 RRarr1 eq_refl eq_refl) as IMGAParr1. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAParr1.
  pose proof (exW_win_blk_apart_h C A2 m2 _ s 4304 arr1 8 CK HW2 Lo1 eq_refl RRarr1 GLO1) as WAParr1.
  assert (Farr1 : live A0 (Z_to_bv 64 arr1) = None).
  { destruct (live A0 (Z_to_bv 64 arr1)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB1 _ _ EE) as XX. first [discriminate Farr1x | (rewrite Farr1x in XX; discriminate XX)]. }
  pose proof Lo1 as Larr1_a2.
  assert (SUB2 : sub_live A0 A2).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 arr1) by (intros ->; rewrite Farr1 in Lq; discriminate Lq). rewrite (LEQ1 q NEq). exact (SUB1 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 arr1 :: [Z_to_bv 64 sel1])) => eq_trans (LEQ1 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL1 q (fun XX => Hq (or_intror XX)))) as LDEL2.
  assert (NE_sel1_arr1 : Z_to_bv 64 sel1 <> Z_to_bv 64 arr1) by (intros EE; rewrite EE in Lsel1_a1; rewrite Farr1x in Lsel1_a1; discriminate Lsel1_a1).
  assert (Lsel1_a2 : live A2 (Z_to_bv 64 sel1) = Some 32%Z) by (rewrite (LEQ1 _ NE_sel1_arr1); exact Lsel1_a1).
  pose proof (exW_blk_apart_h C A2 m2 _ sel1 arr1 32 8 CK HW2 Lsel1_a2 Larr1_a2 NE_sel1_arr1 RRsel1 RRarr1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel1_arr1.
  assert (PM2 : POSTM C A0 s m0 m2).
  { eapply POSTM_trans; [exact PM1|]. eapply POSTM_trans; [exact PMs1|]. apply (POSTM_sub C A0 A1 _ _ _ SUB1).
    apply (POSTM_mono C A1 (s + OFF1) s); [unfold OFF1; lia | exact PMc1]. }
  pose proof (cs_frame_hop C s 4304 OFF1 (-16) (-24) m0 M1 m2 CK (proj1 PMc1) ltac:(lia) ltac:(vm_cast_no_check (eq_refl true)) ltac:(vm_cast_no_check (eq_refl true)) CFs1) as CF2.
  replace (kR - 1 - 1)%Z with (kR - 2)%Z in RM2 by lia. rewrite MG1 in RM2. replace (bR - 1 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 2 * 2 ^ 17)%Z in RM2 by lia.
  assert (KEPT1 : Forall (ex_region_kept E1 M1 m2) [(EVar 32, OFF1, 0%Z); (EVar 67, 0%Z, 32%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF1 4304 M1 m2 E1 (EVar 32) CK (proj1 PMc1) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A1 A1 M1 _ M1 m2 E1 (EVar 67) sel1 32 CK HWs1 Lsel1_a1 RRsel1 eq_refl (proj2 PMc1) Lsel1_a1 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E1 M1 m2 _ [] _ HKc1 KEPT1) as HKk1.
  match type of HKk1 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E1 m2 kk') in HKk1 end.
  pose proof (regs_ok_agree 69%nat E1 (ex_envL vals1 r2 [arr1; exW_canary SEGS 1410112 m2]) _ _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa1.
  pose proof (exW_regs_call _ _ _ _ _ HRa1 (ex_regs_ok_junk vals1 r2 [arr1; exW_canary SEGS 1410112 m2] 69%nat ltac:(vm_cast_no_check (eq_refl 69%nat))) CS1) as HRn2.
  clear HRa1.
  assert (HKa2 : know_ok SEGS (ex_envL vals1 r2 [arr1; exW_canary SEGS 1410112 m2]) m2 _) by (exact (know_ok_agree SEGS 69%nat E1 _ m2 _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk1)).
  rewrite (fr_denot_agree 69%nat E1 (ex_envL vals1 r2 [arr1; exW_canary SEGS 1410112 m2]) _ fr (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r2 ex_r10 (EVar 101) HRn2 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres1)) as HRx2. clear HRn2. rename HRx2 into HRn2.
  clear HR HK Hlf Hms HKc1 HKk1 KEPT1 HC1 HWs1 PMs1 Q10_1 Q11_1 Q1_1 Q2_1 Q4_1 PM1 HW1 PMc1 CS1 SUB1 RM1 MG1 TOP1 LEQ1 Hnz1 Farr1x Lo1 OFF1 LDEL1 CF1 CFs1 Lsel1_a1.
  subst M1. clear log1. clear E1. try clear Rc1. clear KN1.
  lazymatch type of HRn2 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn2 end.
  pose proof (exW_kn_blk SEGS C A2 m2 _ (ex_envL vals1 r2 [arr1; exW_canary SEGS 1410112 m2]) (EVar 101) (EVar 32) arr1 8 s 4304 65536 1347584 p16_segs CK HW2 Larr1_a2 RRarr1 eq_refl eq_refl eq_refl RS ALarr1 ZERO1 WAParr1 IMGAParr1) as HKb2.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals1 r2 [arr1; exW_canary SEGS 1410112 m2]) m2) _ _ (ex_kdisj_apart SEGS (ex_envL vals1 r2 [arr1; exW_canary SEGS 1410112 m2]) m2 (EVar 67) (EVar 101) sel1 arr1 0 32 0 8 eq_refl eq_refl RRsel1 RRarr1 AP_sel1_arr1) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals1 r2 [arr1; exW_canary SEGS 1410112 m2]) m2))) as HKd2.
  pose proof (W_sok_win C A2 m2 _ (s - 4304) (Z.to_nat 4304) CK HW2 GLO1 GLO2) as SOK2.
  pose proof (exW_canary_ok SEGS 1410112 m2 (canary_any m2)) as CANOK2.
  pose (vals2 := vals1 ++ map (getr r2) ex_regs_list ++ map (Z_to_bv 64) [arr1; exW_canary SEGS 1410112 m2]).
  pose proof (exW_kn_fixed SEGS C A2 m2 _ (ex_envL vals1 r2 [arr1; exW_canary SEGS 1410112 m2]) (EVar 102) (EVar 32) (exW_canary SEGS 1410112 m2) s 4304 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW2 eq_refl (proj1 CANOK2) (proj2 CANOK2) eq_refl eq_refl eq_refl SOK2 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf2.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb2 (proj2 (Forall_app _ _ _) (conj HKd2 (proj2 (Forall_app _ _ _) (conj HKf2 HKa2)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn2 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN2 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb2 HKd2 HKf2 HKa2 SOK2 CANOK2.
  repeat match goal with H : getr r2 _ = _ |- _ => clear H end.
  exq_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO1 ALarr1.
  exb_exit ST Rc2 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E2 := EEx) in HR, Hlf, HK, Hms |- *; set (log2 := LLx) in Hms, Hlf; set (M2 := mem_denot E2 m2 log2) in Hms end.
  assert (WP2 : W C A2 M2 (with_vmmaps vm2 md) /\ POSTM C A0 s m2 M2).
  { subst M2. apply (exW_win_blks C A2 A0 m2 _ E2 log2 (EVar 32) s 4304 [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 8%Z)] CK HW2 SUB2 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a2 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a2 (conj Farr1 F0arr1))))|]. constructor. }
  assert (CFs2 : O23LeptCselsA.cs_fra s (-16) (-24) m0 M2).
  { subst M2. apply (cs_frame_sess C A2 A0 m0 m2 _ E2 log2 (EVar 32) s 4304 (-16) (-24) [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 8%Z)] CK HW2 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exact RS | lia | exact Hhi | reflexivity | | reflexivity | exact CF2]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a2 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a2 (conj Farr1 F0arr1))))|]. constructor. }
  destruct WP2 as [HWs2 PMs2].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log2 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC2 : carry log2 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc2 : know_ok SEGS E2 M2 kn1) by (apply (carry_after SEGS E2 m2 log2 kn0 [] kn1 scs hs HC2 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact Hms |].
  pose (BS2 := [(32%nat, s); (67%nat, sel1); (101%nat, arr1)]).
  exW_regfactB BS2 HR ex_r10 Q10_2. exW_regfactB BS2 HR ex_r11 Q11_2. exW_regfactB BS2 HR ex_r1 Q1_2. exW_regfactB BS2 HR ex_r2 Q2_2. exW_regfactB BS2 HR ex_r4 Q4_2.
  clear BS2.
  lazymatch type of Q2_2 with _ = Z_to_bv 64 (s + ?off) => pose (OFF2 := off) end.
  pose proof (alloc_margin_small (6 * 4) ltac:(exW_cmp)) as MG2.
  lazymatch type of Q1_2 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_2 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A2 M2 _ Rc2 6 4 (kR - 2) (bR - 2 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs2 Q10_2 Q11_2 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM2) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_2
             ltac:(red; apply bv_eq; reflexivity) Q4_2 Q2_2 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A3 m3 vm3 r3 res2 HW3 Hres2 CSx2 Hnz2 Fr1_0x Lo2 F0r1_0 LEQ2 ZERO2 ALr1_0 TOP2 PMc2 RM3.
  pose proof CSx2 as CS2. clear CSx2.
  rewrite with_vmmaps_twice in HW3 |- *.
  assert (Eres2 : res2 = Z_to_bv 64 (u res2)) by (symmetry; apply zbv_self).
  pose proof (u64_range res2) as RRr1_0. set (r1_0 := u res2) in *. clearbody r1_0. rewrite Eres2 in Hres2, Fr1_0x, Lo2, F0r1_0, LEQ2, ZERO2. clear Eres2.
  change (6 * 4)%Z with 24%Z in *.
  pose proof (exW_blk_img_apart_h2 C A3 m3 _ r1_0 24 CK HW3 Lo2 RRr1_0 eq_refl eq_refl) as IMGAPr1_0. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPr1_0.
  pose proof (exW_win_blk_apart_h C A3 m3 _ s 4304 r1_0 24 CK HW3 Lo2 eq_refl RRr1_0 GLO1) as WAPr1_0.
  assert (Fr1_0 : live A0 (Z_to_bv 64 r1_0) = None).
  { destruct (live A0 (Z_to_bv 64 r1_0)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB2 _ _ EE) as XX. first [discriminate Fr1_0x | (rewrite Fr1_0x in XX; discriminate XX)]. }
  pose proof Lo2 as Lr1_0_a3.
  assert (SUB3 : sub_live A0 A3).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 r1_0) by (intros ->; rewrite Fr1_0 in Lq; discriminate Lq). rewrite (LEQ2 q NEq). exact (SUB2 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 r1_0 :: [Z_to_bv 64 arr1; Z_to_bv 64 sel1])) => eq_trans (LEQ2 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL2 q (fun XX => Hq (or_intror XX)))) as LDEL3.
  assert (NE_sel1_r1_0 : Z_to_bv 64 sel1 <> Z_to_bv 64 r1_0) by (intros EE; rewrite EE in Lsel1_a2; rewrite Fr1_0x in Lsel1_a2; discriminate Lsel1_a2).
  assert (Lsel1_a3 : live A3 (Z_to_bv 64 sel1) = Some 32%Z) by (rewrite (LEQ2 _ NE_sel1_r1_0); exact Lsel1_a2).
  pose proof (exW_blk_apart_h C A3 m3 _ sel1 r1_0 32 24 CK HW3 Lsel1_a3 Lr1_0_a3 NE_sel1_r1_0 RRsel1 RRr1_0 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel1_r1_0.
  assert (NE_arr1_r1_0 : Z_to_bv 64 arr1 <> Z_to_bv 64 r1_0) by (intros EE; rewrite EE in Larr1_a2; rewrite Fr1_0x in Larr1_a2; discriminate Larr1_a2).
  assert (Larr1_a3 : live A3 (Z_to_bv 64 arr1) = Some 8%Z) by (rewrite (LEQ2 _ NE_arr1_r1_0); exact Larr1_a2).
  pose proof (exW_blk_apart_h C A3 m3 _ arr1 r1_0 8 24 CK HW3 Larr1_a3 Lr1_0_a3 NE_arr1_r1_0 RRarr1 RRr1_0 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr1_r1_0.
  assert (PM3 : POSTM C A0 s m0 m3).
  { eapply POSTM_trans; [exact PM2|]. eapply POSTM_trans; [exact PMs2|]. apply (POSTM_sub C A0 A2 _ _ _ SUB2).
    apply (POSTM_mono C A2 (s + OFF2) s); [unfold OFF2; lia | exact PMc2]. }
  pose proof (cs_frame_hop C s 4304 OFF2 (-16) (-24) m0 M2 m3 CK (proj1 PMc2) ltac:(lia) ltac:(vm_cast_no_check (eq_refl true)) ltac:(vm_cast_no_check (eq_refl true)) CFs2) as CF3.
  replace (kR - 2 - 1)%Z with (kR - 3)%Z in RM3 by lia. rewrite MG2 in RM3. replace (bR - 2 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 3 * 2 ^ 17)%Z in RM3 by lia.
  assert (KEPT2 : Forall (ex_region_kept E2 M2 m3) [(EVar 32, OFF2, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 8%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF2 4304 M2 m3 E2 (EVar 32) CK (proj1 PMc2) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A2 A2 M2 _ M2 m3 E2 (EVar 67) sel1 32 CK HWs2 Lsel1_a2 RRsel1 eq_refl (proj2 PMc2) Lsel1_a2 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A2 A2 M2 _ M2 m3 E2 (EVar 101) arr1 8 CK HWs2 Larr1_a2 RRarr1 eq_refl (proj2 PMc2) Larr1_a2 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E2 M2 m3 _ [] _ HKc2 KEPT2) as HKk2.
  match type of HKk2 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E2 m3 kk') in HKk2 end.
  pose proof (regs_ok_agree 103%nat E2 (ex_envL vals2 r3 [r1_0; exW_canary SEGS 1410112 m3]) _ _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa2.
  pose proof (exW_regs_call _ _ _ _ _ HRa2 (ex_regs_ok_junk vals2 r3 [r1_0; exW_canary SEGS 1410112 m3] 103%nat ltac:(vm_cast_no_check (eq_refl 103%nat))) CS2) as HRn3.
  clear HRa2.
  assert (HKa3 : know_ok SEGS (ex_envL vals2 r3 [r1_0; exW_canary SEGS 1410112 m3]) m3 _) by (exact (know_ok_agree SEGS 103%nat E2 _ m3 _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk2)).
  rewrite (fr_denot_agree 103%nat E2 (ex_envL vals2 r3 [r1_0; exW_canary SEGS 1410112 m3]) _ fr (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r3 ex_r10 (EVar 135) HRn3 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres2)) as HRx3. clear HRn3. rename HRx3 into HRn3.
  clear HR HK Hlf Hms HKc2 HKk2 KEPT2 HC2 HWs2 PMs2 Q10_2 Q11_2 Q1_2 Q2_2 Q4_2 PM2 HW2 PMc2 CS2 SUB2 RM2 MG2 TOP2 LEQ2 Hnz2 Fr1_0x Lo2 OFF2 LDEL2 CF2 CFs2 Lsel1_a2 Larr1_a2.
  subst M2. clear log2. clear E2. try clear Rc2. clear KN2.
  lazymatch type of HRn3 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn3 end.
  pose proof (exW_kn_blk SEGS C A3 m3 _ (ex_envL vals2 r3 [r1_0; exW_canary SEGS 1410112 m3]) (EVar 135) (EVar 32) r1_0 24 s 4304 65536 1347584 p16_segs CK HW3 Lr1_0_a3 RRr1_0 eq_refl eq_refl eq_refl RS ALr1_0 ZERO2 WAPr1_0 IMGAPr1_0) as HKb3.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals2 r3 [r1_0; exW_canary SEGS 1410112 m3]) m3) _ _ (ex_kdisj_apart SEGS (ex_envL vals2 r3 [r1_0; exW_canary SEGS 1410112 m3]) m3 (EVar 67) (EVar 135) sel1 r1_0 0 32 0 24 eq_refl eq_refl RRsel1 RRr1_0 AP_sel1_r1_0) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals2 r3 [r1_0; exW_canary SEGS 1410112 m3]) m3) _ _ (ex_kdisj_apart SEGS (ex_envL vals2 r3 [r1_0; exW_canary SEGS 1410112 m3]) m3 (EVar 101) (EVar 135) arr1 r1_0 0 8 0 24 eq_refl eq_refl RRarr1 RRr1_0 AP_arr1_r1_0) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals2 r3 [r1_0; exW_canary SEGS 1410112 m3]) m3)))) as HKd3.
  pose proof (W_sok_win C A3 m3 _ (s - 4304) (Z.to_nat 4304) CK HW3 GLO1 GLO2) as SOK3.
  pose proof (exW_canary_ok SEGS 1410112 m3 (canary_any m3)) as CANOK3.
  pose (vals3 := vals2 ++ map (getr r3) ex_regs_list ++ map (Z_to_bv 64) [r1_0; exW_canary SEGS 1410112 m3]).
  pose proof (exW_kn_fixed SEGS C A3 m3 _ (ex_envL vals2 r3 [r1_0; exW_canary SEGS 1410112 m3]) (EVar 136) (EVar 32) (exW_canary SEGS 1410112 m3) s 4304 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW3 eq_refl (proj1 CANOK3) (proj2 CANOK3) eq_refl eq_refl eq_refl SOK3 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf3.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb3 (proj2 (Forall_app _ _ _) (conj HKd3 (proj2 (Forall_app _ _ _) (conj HKf3 HKa3)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn3 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN3 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb3 HKd3 HKf3 HKa3 SOK3 CANOK3.
  repeat match goal with H : getr r3 _ = _ |- _ => clear H end.
  exq_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO2 ALr1_0.
  exb_exit ST Rc3 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E3 := EEx) in HR, Hlf, HK, Hms |- *; set (log3 := LLx) in Hms, Hlf; set (M3 := mem_denot E3 m3 log3) in Hms end.
  assert (WP3 : W C A3 M3 (with_vmmaps vm3 md) /\ POSTM C A0 s m3 M3).
  { subst M3. apply (exW_win_blks C A3 A0 m3 _ E3 log3 (EVar 32) s 4304 [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 8%Z); (EVar 135, r1_0, 24%Z)] CK HW3 SUB3 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a3 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a3 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a3 (conj Fr1_0 F0r1_0))))|]. constructor. }
  assert (CFs3 : O23LeptCselsA.cs_fra s (-16) (-24) m0 M3).
  { subst M3. apply (cs_frame_sess C A3 A0 m0 m3 _ E3 log3 (EVar 32) s 4304 (-16) (-24) [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 8%Z); (EVar 135, r1_0, 24%Z)] CK HW3 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exact RS | lia | exact Hhi | reflexivity | | reflexivity | exact CF3]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a3 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a3 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a3 (conj Fr1_0 F0r1_0))))|]. constructor. }
  destruct WP3 as [HWs3 PMs3].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log3 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC3 : carry log3 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc3 : know_ok SEGS E3 M3 kn1) by (apply (carry_after SEGS E3 m3 log3 kn0 [] kn1 scs hs HC3 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact Hms |].
  pose (BS3 := [(32%nat, s); (67%nat, sel1); (101%nat, arr1); (135%nat, r1_0)]).
  exW_regfactB BS3 HR ex_r10 Q10_3. exW_regfactB BS3 HR ex_r11 Q11_3. exW_regfactB BS3 HR ex_r1 Q1_3. exW_regfactB BS3 HR ex_r2 Q2_3. exW_regfactB BS3 HR ex_r4 Q4_3.
  clear BS3.
  lazymatch type of Q2_3 with _ = Z_to_bv 64 (s + ?off) => pose (OFF3 := off) end.
  pose proof (alloc_margin_small (1 * 32) ltac:(exW_cmp)) as MG3.
  lazymatch type of Q1_3 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_3 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A3 M3 _ Rc3 1 32 (kR - 3) (bR - 3 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs3 Q10_3 Q11_3 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM3) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_3
             ltac:(red; apply bv_eq; reflexivity) Q4_3 Q2_3 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A4 m4 vm4 r4 res3 HW4 Hres3 CSx3 Hnz3 Fsel2x Lo3 F0sel2 LEQ3 ZERO3 ALsel2 TOP3 PMc3 RM4.
  pose proof CSx3 as CS3. clear CSx3.
  rewrite with_vmmaps_twice in HW4 |- *.
  assert (Eres3 : res3 = Z_to_bv 64 (u res3)) by (symmetry; apply zbv_self).
  pose proof (u64_range res3) as RRsel2. set (sel2 := u res3) in *. clearbody sel2. rewrite Eres3 in Hres3, Fsel2x, Lo3, F0sel2, LEQ3, ZERO3. clear Eres3.
  change (1 * 32)%Z with 32%Z in *.
  pose proof (exW_blk_img_apart_h2 C A4 m4 _ sel2 32 CK HW4 Lo3 RRsel2 eq_refl eq_refl) as IMGAPsel2. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPsel2.
  pose proof (exW_win_blk_apart_h C A4 m4 _ s 4304 sel2 32 CK HW4 Lo3 eq_refl RRsel2 GLO1) as WAPsel2.
  assert (Fsel2 : live A0 (Z_to_bv 64 sel2) = None).
  { destruct (live A0 (Z_to_bv 64 sel2)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB3 _ _ EE) as XX. first [discriminate Fsel2x | (rewrite Fsel2x in XX; discriminate XX)]. }
  pose proof Lo3 as Lsel2_a4.
  assert (SUB4 : sub_live A0 A4).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 sel2) by (intros ->; rewrite Fsel2 in Lq; discriminate Lq). rewrite (LEQ3 q NEq). exact (SUB3 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 sel2 :: [Z_to_bv 64 r1_0; Z_to_bv 64 arr1; Z_to_bv 64 sel1])) => eq_trans (LEQ3 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL3 q (fun XX => Hq (or_intror XX)))) as LDEL4.
  assert (NE_sel1_sel2 : Z_to_bv 64 sel1 <> Z_to_bv 64 sel2) by (intros EE; rewrite EE in Lsel1_a3; rewrite Fsel2x in Lsel1_a3; discriminate Lsel1_a3).
  assert (Lsel1_a4 : live A4 (Z_to_bv 64 sel1) = Some 32%Z) by (rewrite (LEQ3 _ NE_sel1_sel2); exact Lsel1_a3).
  pose proof (exW_blk_apart_h C A4 m4 _ sel1 sel2 32 32 CK HW4 Lsel1_a4 Lsel2_a4 NE_sel1_sel2 RRsel1 RRsel2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel1_sel2.
  assert (NE_arr1_sel2 : Z_to_bv 64 arr1 <> Z_to_bv 64 sel2) by (intros EE; rewrite EE in Larr1_a3; rewrite Fsel2x in Larr1_a3; discriminate Larr1_a3).
  assert (Larr1_a4 : live A4 (Z_to_bv 64 arr1) = Some 8%Z) by (rewrite (LEQ3 _ NE_arr1_sel2); exact Larr1_a3).
  pose proof (exW_blk_apart_h C A4 m4 _ arr1 sel2 8 32 CK HW4 Larr1_a4 Lsel2_a4 NE_arr1_sel2 RRarr1 RRsel2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr1_sel2.
  assert (NE_r1_0_sel2 : Z_to_bv 64 r1_0 <> Z_to_bv 64 sel2) by (intros EE; rewrite EE in Lr1_0_a3; rewrite Fsel2x in Lr1_0_a3; discriminate Lr1_0_a3).
  assert (Lr1_0_a4 : live A4 (Z_to_bv 64 r1_0) = Some 24%Z) by (rewrite (LEQ3 _ NE_r1_0_sel2); exact Lr1_0_a3).
  pose proof (exW_blk_apart_h C A4 m4 _ r1_0 sel2 24 32 CK HW4 Lr1_0_a4 Lsel2_a4 NE_r1_0_sel2 RRr1_0 RRsel2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_0_sel2.
  assert (PM4 : POSTM C A0 s m0 m4).
  { eapply POSTM_trans; [exact PM3|]. eapply POSTM_trans; [exact PMs3|]. apply (POSTM_sub C A0 A3 _ _ _ SUB3).
    apply (POSTM_mono C A3 (s + OFF3) s); [unfold OFF3; lia | exact PMc3]. }
  pose proof (cs_frame_hop C s 4304 OFF3 (-16) (-24) m0 M3 m4 CK (proj1 PMc3) ltac:(lia) ltac:(vm_cast_no_check (eq_refl true)) ltac:(vm_cast_no_check (eq_refl true)) CFs3) as CF4.
  replace (kR - 3 - 1)%Z with (kR - 4)%Z in RM4 by lia. rewrite MG3 in RM4. replace (bR - 3 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 4 * 2 ^ 17)%Z in RM4 by lia.
  assert (KEPT3 : Forall (ex_region_kept E3 M3 m4) [(EVar 32, OFF3, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 8%Z); (EVar 135, 0%Z, 24%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF3 4304 M3 m4 E3 (EVar 32) CK (proj1 PMc3) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A3 A3 M3 _ M3 m4 E3 (EVar 67) sel1 32 CK HWs3 Lsel1_a3 RRsel1 eq_refl (proj2 PMc3) Lsel1_a3 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A3 A3 M3 _ M3 m4 E3 (EVar 101) arr1 8 CK HWs3 Larr1_a3 RRarr1 eq_refl (proj2 PMc3) Larr1_a3 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A3 A3 M3 _ M3 m4 E3 (EVar 135) r1_0 24 CK HWs3 Lr1_0_a3 RRr1_0 eq_refl (proj2 PMc3) Lr1_0_a3 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E3 M3 m4 _ [] _ HKc3 KEPT3) as HKk3.
  match type of HKk3 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E3 m4 kk') in HKk3 end.
  pose proof (regs_ok_agree 137%nat E3 (ex_envL vals3 r4 [sel2; exW_canary SEGS 1410112 m4]) _ _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa3.
  pose proof (exW_regs_call _ _ _ _ _ HRa3 (ex_regs_ok_junk vals3 r4 [sel2; exW_canary SEGS 1410112 m4] 137%nat ltac:(vm_cast_no_check (eq_refl 137%nat))) CS3) as HRn4.
  clear HRa3.
  assert (HKa4 : know_ok SEGS (ex_envL vals3 r4 [sel2; exW_canary SEGS 1410112 m4]) m4 _) by (exact (know_ok_agree SEGS 137%nat E3 _ m4 _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk3)).
  rewrite (fr_denot_agree 137%nat E3 (ex_envL vals3 r4 [sel2; exW_canary SEGS 1410112 m4]) _ fr (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r4 ex_r10 (EVar 169) HRn4 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres3)) as HRx4. clear HRn4. rename HRx4 into HRn4.
  clear HR HK Hlf Hms HKc3 HKk3 KEPT3 HC3 HWs3 PMs3 Q10_3 Q11_3 Q1_3 Q2_3 Q4_3 PM3 HW3 PMc3 CS3 SUB3 RM3 MG3 TOP3 LEQ3 Hnz3 Fsel2x Lo3 OFF3 LDEL3 CF3 CFs3 Lsel1_a3 Larr1_a3 Lr1_0_a3.
  subst M3. clear log3. clear E3. try clear Rc3. clear KN3.
  lazymatch type of HRn4 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn4 end.
  pose proof (exW_kn_blk SEGS C A4 m4 _ (ex_envL vals3 r4 [sel2; exW_canary SEGS 1410112 m4]) (EVar 169) (EVar 32) sel2 32 s 4304 65536 1347584 p16_segs CK HW4 Lsel2_a4 RRsel2 eq_refl eq_refl eq_refl RS ALsel2 ZERO3 WAPsel2 IMGAPsel2) as HKb4.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals3 r4 [sel2; exW_canary SEGS 1410112 m4]) m4) _ _ (ex_kdisj_apart SEGS (ex_envL vals3 r4 [sel2; exW_canary SEGS 1410112 m4]) m4 (EVar 67) (EVar 169) sel1 sel2 0 32 0 32 eq_refl eq_refl RRsel1 RRsel2 AP_sel1_sel2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals3 r4 [sel2; exW_canary SEGS 1410112 m4]) m4) _ _ (ex_kdisj_apart SEGS (ex_envL vals3 r4 [sel2; exW_canary SEGS 1410112 m4]) m4 (EVar 101) (EVar 169) arr1 sel2 0 8 0 32 eq_refl eq_refl RRarr1 RRsel2 AP_arr1_sel2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals3 r4 [sel2; exW_canary SEGS 1410112 m4]) m4) _ _ (ex_kdisj_apart SEGS (ex_envL vals3 r4 [sel2; exW_canary SEGS 1410112 m4]) m4 (EVar 135) (EVar 169) r1_0 sel2 0 24 0 32 eq_refl eq_refl RRr1_0 RRsel2 AP_r1_0_sel2) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals3 r4 [sel2; exW_canary SEGS 1410112 m4]) m4))))) as HKd4.
  pose proof (W_sok_win C A4 m4 _ (s - 4304) (Z.to_nat 4304) CK HW4 GLO1 GLO2) as SOK4.
  pose proof (exW_canary_ok SEGS 1410112 m4 (canary_any m4)) as CANOK4.
  pose (vals4 := vals3 ++ map (getr r4) ex_regs_list ++ map (Z_to_bv 64) [sel2; exW_canary SEGS 1410112 m4]).
  pose proof (exW_kn_fixed SEGS C A4 m4 _ (ex_envL vals3 r4 [sel2; exW_canary SEGS 1410112 m4]) (EVar 170) (EVar 32) (exW_canary SEGS 1410112 m4) s 4304 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW4 eq_refl (proj1 CANOK4) (proj2 CANOK4) eq_refl eq_refl eq_refl SOK4 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf4.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb4 (proj2 (Forall_app _ _ _) (conj HKd4 (proj2 (Forall_app _ _ _) (conj HKf4 HKa4)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn4 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN4 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb4 HKd4 HKf4 HKa4 SOK4 CANOK4.
  repeat match goal with H : getr r4 _ = _ |- _ => clear H end.
  exq_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO3 ALsel2.
  exb_exit ST Rc4 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E4 := EEx) in HR, Hlf, HK, Hms |- *; set (log4 := LLx) in Hms, Hlf; set (M4 := mem_denot E4 m4 log4) in Hms end.
  assert (WP4 : W C A4 M4 (with_vmmaps vm4 md) /\ POSTM C A0 s m4 M4).
  { subst M4. apply (exW_win_blks C A4 A0 m4 _ E4 log4 (EVar 32) s 4304 [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 8%Z); (EVar 135, r1_0, 24%Z); (EVar 169, sel2, 32%Z)] CK HW4 SUB4 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a4 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a4 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a4 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRsel2 (conj Lsel2_a4 (conj Fsel2 F0sel2))))|]. constructor. }
  assert (CFs4 : O23LeptCselsA.cs_fra s (-16) (-24) m0 M4).
  { subst M4. apply (cs_frame_sess C A4 A0 m0 m4 _ E4 log4 (EVar 32) s 4304 (-16) (-24) [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 8%Z); (EVar 135, r1_0, 24%Z); (EVar 169, sel2, 32%Z)] CK HW4 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exact RS | lia | exact Hhi | reflexivity | | reflexivity | exact CF4]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a4 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a4 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a4 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRsel2 (conj Lsel2_a4 (conj Fsel2 F0sel2))))|]. constructor. }
  destruct WP4 as [HWs4 PMs4].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log4 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC4 : carry log4 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc4 : know_ok SEGS E4 M4 kn1) by (apply (carry_after SEGS E4 m4 log4 kn0 [] kn1 scs hs HC4 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact Hms |].
  pose (BS4 := [(32%nat, s); (67%nat, sel1); (101%nat, arr1); (135%nat, r1_0); (169%nat, sel2)]).
  exW_regfactB BS4 HR ex_r10 Q10_4. exW_regfactB BS4 HR ex_r11 Q11_4. exW_regfactB BS4 HR ex_r1 Q1_4. exW_regfactB BS4 HR ex_r2 Q2_4. exW_regfactB BS4 HR ex_r4 Q4_4.
  clear BS4.
  lazymatch type of Q2_4 with _ = Z_to_bv 64 (s + ?off) => pose (OFF4 := off) end.
  pose proof (alloc_margin_small (1 * 8) ltac:(exW_cmp)) as MG4.
  lazymatch type of Q1_4 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_4 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A4 M4 _ Rc4 1 8 (kR - 4) (bR - 4 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs4 Q10_4 Q11_4 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM4) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_4
             ltac:(red; apply bv_eq; reflexivity) Q4_4 Q2_4 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A5 m5 vm5 r5 res4 HW5 Hres4 CSx4 Hnz4 Farr2x Lo4 F0arr2 LEQ4 ZERO4 ALarr2 TOP4 PMc4 RM5.
  pose proof CSx4 as CS4. clear CSx4.
  rewrite with_vmmaps_twice in HW5 |- *.
  assert (Eres4 : res4 = Z_to_bv 64 (u res4)) by (symmetry; apply zbv_self).
  pose proof (u64_range res4) as RRarr2. set (arr2 := u res4) in *. clearbody arr2. rewrite Eres4 in Hres4, Farr2x, Lo4, F0arr2, LEQ4, ZERO4. clear Eres4.
  change (1 * 8)%Z with 8%Z in *.
  pose proof (exW_blk_img_apart_h2 C A5 m5 _ arr2 8 CK HW5 Lo4 RRarr2 eq_refl eq_refl) as IMGAParr2. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAParr2.
  pose proof (exW_win_blk_apart_h C A5 m5 _ s 4304 arr2 8 CK HW5 Lo4 eq_refl RRarr2 GLO1) as WAParr2.
  assert (Farr2 : live A0 (Z_to_bv 64 arr2) = None).
  { destruct (live A0 (Z_to_bv 64 arr2)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB4 _ _ EE) as XX. first [discriminate Farr2x | (rewrite Farr2x in XX; discriminate XX)]. }
  pose proof Lo4 as Larr2_a5.
  assert (SUB5 : sub_live A0 A5).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 arr2) by (intros ->; rewrite Farr2 in Lq; discriminate Lq). rewrite (LEQ4 q NEq). exact (SUB4 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 arr2 :: [Z_to_bv 64 sel2; Z_to_bv 64 r1_0; Z_to_bv 64 arr1; Z_to_bv 64 sel1])) => eq_trans (LEQ4 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL4 q (fun XX => Hq (or_intror XX)))) as LDEL5.
  assert (NE_sel1_arr2 : Z_to_bv 64 sel1 <> Z_to_bv 64 arr2) by (intros EE; rewrite EE in Lsel1_a4; rewrite Farr2x in Lsel1_a4; discriminate Lsel1_a4).
  assert (Lsel1_a5 : live A5 (Z_to_bv 64 sel1) = Some 32%Z) by (rewrite (LEQ4 _ NE_sel1_arr2); exact Lsel1_a4).
  pose proof (exW_blk_apart_h C A5 m5 _ sel1 arr2 32 8 CK HW5 Lsel1_a5 Larr2_a5 NE_sel1_arr2 RRsel1 RRarr2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel1_arr2.
  assert (NE_arr1_arr2 : Z_to_bv 64 arr1 <> Z_to_bv 64 arr2) by (intros EE; rewrite EE in Larr1_a4; rewrite Farr2x in Larr1_a4; discriminate Larr1_a4).
  assert (Larr1_a5 : live A5 (Z_to_bv 64 arr1) = Some 8%Z) by (rewrite (LEQ4 _ NE_arr1_arr2); exact Larr1_a4).
  pose proof (exW_blk_apart_h C A5 m5 _ arr1 arr2 8 8 CK HW5 Larr1_a5 Larr2_a5 NE_arr1_arr2 RRarr1 RRarr2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr1_arr2.
  assert (NE_r1_0_arr2 : Z_to_bv 64 r1_0 <> Z_to_bv 64 arr2) by (intros EE; rewrite EE in Lr1_0_a4; rewrite Farr2x in Lr1_0_a4; discriminate Lr1_0_a4).
  assert (Lr1_0_a5 : live A5 (Z_to_bv 64 r1_0) = Some 24%Z) by (rewrite (LEQ4 _ NE_r1_0_arr2); exact Lr1_0_a4).
  pose proof (exW_blk_apart_h C A5 m5 _ r1_0 arr2 24 8 CK HW5 Lr1_0_a5 Larr2_a5 NE_r1_0_arr2 RRr1_0 RRarr2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_0_arr2.
  assert (NE_sel2_arr2 : Z_to_bv 64 sel2 <> Z_to_bv 64 arr2) by (intros EE; rewrite EE in Lsel2_a4; rewrite Farr2x in Lsel2_a4; discriminate Lsel2_a4).
  assert (Lsel2_a5 : live A5 (Z_to_bv 64 sel2) = Some 32%Z) by (rewrite (LEQ4 _ NE_sel2_arr2); exact Lsel2_a4).
  pose proof (exW_blk_apart_h C A5 m5 _ sel2 arr2 32 8 CK HW5 Lsel2_a5 Larr2_a5 NE_sel2_arr2 RRsel2 RRarr2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel2_arr2.
  assert (PM5 : POSTM C A0 s m0 m5).
  { eapply POSTM_trans; [exact PM4|]. eapply POSTM_trans; [exact PMs4|]. apply (POSTM_sub C A0 A4 _ _ _ SUB4).
    apply (POSTM_mono C A4 (s + OFF4) s); [unfold OFF4; lia | exact PMc4]. }
  pose proof (cs_frame_hop C s 4304 OFF4 (-16) (-24) m0 M4 m5 CK (proj1 PMc4) ltac:(lia) ltac:(vm_cast_no_check (eq_refl true)) ltac:(vm_cast_no_check (eq_refl true)) CFs4) as CF5.
  replace (kR - 4 - 1)%Z with (kR - 5)%Z in RM5 by lia. rewrite MG4 in RM5. replace (bR - 4 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 5 * 2 ^ 17)%Z in RM5 by lia.
  assert (KEPT4 : Forall (ex_region_kept E4 M4 m5) [(EVar 32, OFF4, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 8%Z); (EVar 135, 0%Z, 24%Z); (EVar 169, 0%Z, 32%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF4 4304 M4 m5 E4 (EVar 32) CK (proj1 PMc4) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 M4 _ M4 m5 E4 (EVar 67) sel1 32 CK HWs4 Lsel1_a4 RRsel1 eq_refl (proj2 PMc4) Lsel1_a4 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 M4 _ M4 m5 E4 (EVar 101) arr1 8 CK HWs4 Larr1_a4 RRarr1 eq_refl (proj2 PMc4) Larr1_a4 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 M4 _ M4 m5 E4 (EVar 135) r1_0 24 CK HWs4 Lr1_0_a4 RRr1_0 eq_refl (proj2 PMc4) Lr1_0_a4 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 M4 _ M4 m5 E4 (EVar 169) sel2 32 CK HWs4 Lsel2_a4 RRsel2 eq_refl (proj2 PMc4) Lsel2_a4 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E4 M4 m5 _ [] _ HKc4 KEPT4) as HKk4.
  match type of HKk4 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E4 m5 kk') in HKk4 end.
  pose proof (regs_ok_agree 171%nat E4 (ex_envL vals4 r5 [arr2; exW_canary SEGS 1410112 m5]) _ _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa4.
  pose proof (exW_regs_call _ _ _ _ _ HRa4 (ex_regs_ok_junk vals4 r5 [arr2; exW_canary SEGS 1410112 m5] 171%nat ltac:(vm_cast_no_check (eq_refl 171%nat))) CS4) as HRn5.
  clear HRa4.
  assert (HKa5 : know_ok SEGS (ex_envL vals4 r5 [arr2; exW_canary SEGS 1410112 m5]) m5 _) by (exact (know_ok_agree SEGS 171%nat E4 _ m5 _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk4)).
  rewrite (fr_denot_agree 171%nat E4 (ex_envL vals4 r5 [arr2; exW_canary SEGS 1410112 m5]) _ fr (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r5 ex_r10 (EVar 203) HRn5 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres4)) as HRx5. clear HRn5. rename HRx5 into HRn5.
  clear HR HK Hlf Hms HKc4 HKk4 KEPT4 HC4 HWs4 PMs4 Q10_4 Q11_4 Q1_4 Q2_4 Q4_4 PM4 HW4 PMc4 CS4 SUB4 RM4 MG4 TOP4 LEQ4 Hnz4 Farr2x Lo4 OFF4 LDEL4 CF4 CFs4 Lsel1_a4 Larr1_a4 Lr1_0_a4 Lsel2_a4.
  subst M4. clear log4. clear E4. try clear Rc4. clear KN4.
  lazymatch type of HRn5 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn5 end.
  pose proof (exW_kn_blk SEGS C A5 m5 _ (ex_envL vals4 r5 [arr2; exW_canary SEGS 1410112 m5]) (EVar 203) (EVar 32) arr2 8 s 4304 65536 1347584 p16_segs CK HW5 Larr2_a5 RRarr2 eq_refl eq_refl eq_refl RS ALarr2 ZERO4 WAParr2 IMGAParr2) as HKb5.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [arr2; exW_canary SEGS 1410112 m5]) m5) _ _ (ex_kdisj_apart SEGS (ex_envL vals4 r5 [arr2; exW_canary SEGS 1410112 m5]) m5 (EVar 67) (EVar 203) sel1 arr2 0 32 0 8 eq_refl eq_refl RRsel1 RRarr2 AP_sel1_arr2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [arr2; exW_canary SEGS 1410112 m5]) m5) _ _ (ex_kdisj_apart SEGS (ex_envL vals4 r5 [arr2; exW_canary SEGS 1410112 m5]) m5 (EVar 101) (EVar 203) arr1 arr2 0 8 0 8 eq_refl eq_refl RRarr1 RRarr2 AP_arr1_arr2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [arr2; exW_canary SEGS 1410112 m5]) m5) _ _ (ex_kdisj_apart SEGS (ex_envL vals4 r5 [arr2; exW_canary SEGS 1410112 m5]) m5 (EVar 135) (EVar 203) r1_0 arr2 0 24 0 8 eq_refl eq_refl RRr1_0 RRarr2 AP_r1_0_arr2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [arr2; exW_canary SEGS 1410112 m5]) m5) _ _ (ex_kdisj_apart SEGS (ex_envL vals4 r5 [arr2; exW_canary SEGS 1410112 m5]) m5 (EVar 169) (EVar 203) sel2 arr2 0 32 0 8 eq_refl eq_refl RRsel2 RRarr2 AP_sel2_arr2) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals4 r5 [arr2; exW_canary SEGS 1410112 m5]) m5)))))) as HKd5.
  pose proof (W_sok_win C A5 m5 _ (s - 4304) (Z.to_nat 4304) CK HW5 GLO1 GLO2) as SOK5.
  pose proof (exW_canary_ok SEGS 1410112 m5 (canary_any m5)) as CANOK5.
  pose (vals5 := vals4 ++ map (getr r5) ex_regs_list ++ map (Z_to_bv 64) [arr2; exW_canary SEGS 1410112 m5]).
  pose proof (exW_kn_fixed SEGS C A5 m5 _ (ex_envL vals4 r5 [arr2; exW_canary SEGS 1410112 m5]) (EVar 204) (EVar 32) (exW_canary SEGS 1410112 m5) s 4304 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW5 eq_refl (proj1 CANOK5) (proj2 CANOK5) eq_refl eq_refl eq_refl SOK5 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf5.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb5 (proj2 (Forall_app _ _ _) (conj HKd5 (proj2 (Forall_app _ _ _) (conj HKf5 HKa5)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn5 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN5 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb5 HKd5 HKf5 HKa5 SOK5 CANOK5.
  repeat match goal with H : getr r5 _ = _ |- _ => clear H end.
  exq_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO4 ALarr2.
  exb_exit ST Rc5 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E5 := EEx) in HR, Hlf, HK, Hms |- *; set (log5 := LLx) in Hms, Hlf; set (M5 := mem_denot E5 m5 log5) in Hms end.
  assert (WP5 : W C A5 M5 (with_vmmaps vm5 md) /\ POSTM C A0 s m5 M5).
  { subst M5. apply (exW_win_blks C A5 A0 m5 _ E5 log5 (EVar 32) s 4304 [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 8%Z); (EVar 135, r1_0, 24%Z); (EVar 169, sel2, 32%Z); (EVar 203, arr2, 8%Z)] CK HW5 SUB5 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a5 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a5 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a5 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRsel2 (conj Lsel2_a5 (conj Fsel2 F0sel2))))|]. constructor; [exact (conj eq_refl (conj RRarr2 (conj Larr2_a5 (conj Farr2 F0arr2))))|]. constructor. }
  assert (CFs5 : O23LeptCselsA.cs_fra s (-16) (-24) m0 M5).
  { subst M5. apply (cs_frame_sess C A5 A0 m0 m5 _ E5 log5 (EVar 32) s 4304 (-16) (-24) [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 8%Z); (EVar 135, r1_0, 24%Z); (EVar 169, sel2, 32%Z); (EVar 203, arr2, 8%Z)] CK HW5 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exact RS | lia | exact Hhi | reflexivity | | reflexivity | exact CF5]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a5 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a5 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a5 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRsel2 (conj Lsel2_a5 (conj Fsel2 F0sel2))))|]. constructor; [exact (conj eq_refl (conj RRarr2 (conj Larr2_a5 (conj Farr2 F0arr2))))|]. constructor. }
  destruct WP5 as [HWs5 PMs5].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log5 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC5 : carry log5 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc5 : know_ok SEGS E5 M5 kn1) by (apply (carry_after SEGS E5 m5 log5 kn0 [] kn1 scs hs HC5 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact Hms |].
  pose (BS5 := [(32%nat, s); (67%nat, sel1); (101%nat, arr1); (135%nat, r1_0); (169%nat, sel2); (203%nat, arr2)]).
  exW_regfactB BS5 HR ex_r10 Q10_5. exW_regfactB BS5 HR ex_r11 Q11_5. exW_regfactB BS5 HR ex_r1 Q1_5. exW_regfactB BS5 HR ex_r2 Q2_5. exW_regfactB BS5 HR ex_r4 Q4_5.
  clear BS5.
  lazymatch type of Q2_5 with _ = Z_to_bv 64 (s + ?off) => pose (OFF5 := off) end.
  pose proof (alloc_margin_small (30 * 4) ltac:(exW_cmp)) as MG5.
  lazymatch type of Q1_5 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_5 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A5 M5 _ Rc5 30 4 (kR - 5) (bR - 5 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs5 Q10_5 Q11_5 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM5) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_5
             ltac:(red; apply bv_eq; reflexivity) Q4_5 Q2_5 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A6 m6 vm6 r6 res5 HW6 Hres5 CSx5 Hnz5 Fr2_0x Lo5 F0r2_0 LEQ5 ZERO5 ALr2_0 TOP5 PMc5 RM6.
  pose proof CSx5 as CS5. clear CSx5.
  rewrite with_vmmaps_twice in HW6 |- *.
  assert (Eres5 : res5 = Z_to_bv 64 (u res5)) by (symmetry; apply zbv_self).
  pose proof (u64_range res5) as RRr2_0. set (r2_0 := u res5) in *. clearbody r2_0. rewrite Eres5 in Hres5, Fr2_0x, Lo5, F0r2_0, LEQ5, ZERO5. clear Eres5.
  change (30 * 4)%Z with 120%Z in *.
  pose proof (exW_blk_img_apart_h2 C A6 m6 _ r2_0 120 CK HW6 Lo5 RRr2_0 eq_refl eq_refl) as IMGAPr2_0. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPr2_0.
  pose proof (exW_win_blk_apart_h C A6 m6 _ s 4304 r2_0 120 CK HW6 Lo5 eq_refl RRr2_0 GLO1) as WAPr2_0.
  assert (Fr2_0 : live A0 (Z_to_bv 64 r2_0) = None).
  { destruct (live A0 (Z_to_bv 64 r2_0)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB5 _ _ EE) as XX. first [discriminate Fr2_0x | (rewrite Fr2_0x in XX; discriminate XX)]. }
  pose proof Lo5 as Lr2_0_a6.
  assert (SUB6 : sub_live A0 A6).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 r2_0) by (intros ->; rewrite Fr2_0 in Lq; discriminate Lq). rewrite (LEQ5 q NEq). exact (SUB5 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 r2_0 :: [Z_to_bv 64 arr2; Z_to_bv 64 sel2; Z_to_bv 64 r1_0; Z_to_bv 64 arr1; Z_to_bv 64 sel1])) => eq_trans (LEQ5 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL5 q (fun XX => Hq (or_intror XX)))) as LDEL6.
  assert (NE_sel1_r2_0 : Z_to_bv 64 sel1 <> Z_to_bv 64 r2_0) by (intros EE; rewrite EE in Lsel1_a5; rewrite Fr2_0x in Lsel1_a5; discriminate Lsel1_a5).
  assert (Lsel1_a6 : live A6 (Z_to_bv 64 sel1) = Some 32%Z) by (rewrite (LEQ5 _ NE_sel1_r2_0); exact Lsel1_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ sel1 r2_0 32 120 CK HW6 Lsel1_a6 Lr2_0_a6 NE_sel1_r2_0 RRsel1 RRr2_0 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel1_r2_0.
  assert (NE_arr1_r2_0 : Z_to_bv 64 arr1 <> Z_to_bv 64 r2_0) by (intros EE; rewrite EE in Larr1_a5; rewrite Fr2_0x in Larr1_a5; discriminate Larr1_a5).
  assert (Larr1_a6 : live A6 (Z_to_bv 64 arr1) = Some 8%Z) by (rewrite (LEQ5 _ NE_arr1_r2_0); exact Larr1_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ arr1 r2_0 8 120 CK HW6 Larr1_a6 Lr2_0_a6 NE_arr1_r2_0 RRarr1 RRr2_0 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr1_r2_0.
  assert (NE_r1_0_r2_0 : Z_to_bv 64 r1_0 <> Z_to_bv 64 r2_0) by (intros EE; rewrite EE in Lr1_0_a5; rewrite Fr2_0x in Lr1_0_a5; discriminate Lr1_0_a5).
  assert (Lr1_0_a6 : live A6 (Z_to_bv 64 r1_0) = Some 24%Z) by (rewrite (LEQ5 _ NE_r1_0_r2_0); exact Lr1_0_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ r1_0 r2_0 24 120 CK HW6 Lr1_0_a6 Lr2_0_a6 NE_r1_0_r2_0 RRr1_0 RRr2_0 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_0_r2_0.
  assert (NE_sel2_r2_0 : Z_to_bv 64 sel2 <> Z_to_bv 64 r2_0) by (intros EE; rewrite EE in Lsel2_a5; rewrite Fr2_0x in Lsel2_a5; discriminate Lsel2_a5).
  assert (Lsel2_a6 : live A6 (Z_to_bv 64 sel2) = Some 32%Z) by (rewrite (LEQ5 _ NE_sel2_r2_0); exact Lsel2_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ sel2 r2_0 32 120 CK HW6 Lsel2_a6 Lr2_0_a6 NE_sel2_r2_0 RRsel2 RRr2_0 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel2_r2_0.
  assert (NE_arr2_r2_0 : Z_to_bv 64 arr2 <> Z_to_bv 64 r2_0) by (intros EE; rewrite EE in Larr2_a5; rewrite Fr2_0x in Larr2_a5; discriminate Larr2_a5).
  assert (Larr2_a6 : live A6 (Z_to_bv 64 arr2) = Some 8%Z) by (rewrite (LEQ5 _ NE_arr2_r2_0); exact Larr2_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ arr2 r2_0 8 120 CK HW6 Larr2_a6 Lr2_0_a6 NE_arr2_r2_0 RRarr2 RRr2_0 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr2_r2_0.
  assert (PM6 : POSTM C A0 s m0 m6).
  { eapply POSTM_trans; [exact PM5|]. eapply POSTM_trans; [exact PMs5|]. apply (POSTM_sub C A0 A5 _ _ _ SUB5).
    apply (POSTM_mono C A5 (s + OFF5) s); [unfold OFF5; lia | exact PMc5]. }
  pose proof (cs_frame_hop C s 4304 OFF5 (-16) (-24) m0 M5 m6 CK (proj1 PMc5) ltac:(lia) ltac:(vm_cast_no_check (eq_refl true)) ltac:(vm_cast_no_check (eq_refl true)) CFs5) as CF6.
  replace (kR - 5 - 1)%Z with (kR - 6)%Z in RM6 by lia. rewrite MG5 in RM6. replace (bR - 5 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 6 * 2 ^ 17)%Z in RM6 by lia.
  assert (KEPT5 : Forall (ex_region_kept E5 M5 m6) [(EVar 32, OFF5, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 8%Z); (EVar 135, 0%Z, 24%Z); (EVar 169, 0%Z, 32%Z); (EVar 203, 0%Z, 8%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF5 4304 M5 m6 E5 (EVar 32) CK (proj1 PMc5) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 67) sel1 32 CK HWs5 Lsel1_a5 RRsel1 eq_refl (proj2 PMc5) Lsel1_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 101) arr1 8 CK HWs5 Larr1_a5 RRarr1 eq_refl (proj2 PMc5) Larr1_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 135) r1_0 24 CK HWs5 Lr1_0_a5 RRr1_0 eq_refl (proj2 PMc5) Lr1_0_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 169) sel2 32 CK HWs5 Lsel2_a5 RRsel2 eq_refl (proj2 PMc5) Lsel2_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 203) arr2 8 CK HWs5 Larr2_a5 RRarr2 eq_refl (proj2 PMc5) Larr2_a5 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E5 M5 m6 _ [] _ HKc5 KEPT5) as HKk5.
  match type of HKk5 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E5 m6 kk') in HKk5 end.
  pose proof (regs_ok_agree 205%nat E5 (ex_envL vals5 r6 [r2_0; exW_canary SEGS 1410112 m6]) _ _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa5.
  pose proof (exW_regs_call _ _ _ _ _ HRa5 (ex_regs_ok_junk vals5 r6 [r2_0; exW_canary SEGS 1410112 m6] 205%nat ltac:(vm_cast_no_check (eq_refl 205%nat))) CS5) as HRn6.
  clear HRa5.
  assert (HKa6 : know_ok SEGS (ex_envL vals5 r6 [r2_0; exW_canary SEGS 1410112 m6]) m6 _) by (exact (know_ok_agree SEGS 205%nat E5 _ m6 _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk5)).
  rewrite (fr_denot_agree 205%nat E5 (ex_envL vals5 r6 [r2_0; exW_canary SEGS 1410112 m6]) _ fr (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r6 ex_r10 (EVar 237) HRn6 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres5)) as HRx6. clear HRn6. rename HRx6 into HRn6.
  clear HR HK Hlf Hms HKc5 HKk5 KEPT5 HC5 HWs5 PMs5 Q10_5 Q11_5 Q1_5 Q2_5 Q4_5 PM5 HW5 PMc5 CS5 SUB5 RM5 MG5 TOP5 LEQ5 Hnz5 Fr2_0x Lo5 OFF5 LDEL5 CF5 CFs5 Lsel1_a5 Larr1_a5 Lr1_0_a5 Lsel2_a5 Larr2_a5.
  subst M5. clear log5. clear E5. try clear Rc5. clear KN5.
  lazymatch type of HRn6 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn6 end.
  pose proof (exW_kn_blk SEGS C A6 m6 _ (ex_envL vals5 r6 [r2_0; exW_canary SEGS 1410112 m6]) (EVar 237) (EVar 32) r2_0 120 s 4304 65536 1347584 p16_segs CK HW6 Lr2_0_a6 RRr2_0 eq_refl eq_refl eq_refl RS ALr2_0 ZERO5 WAPr2_0 IMGAPr2_0) as HKb6.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [r2_0; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [r2_0; exW_canary SEGS 1410112 m6]) m6 (EVar 67) (EVar 237) sel1 r2_0 0 32 0 120 eq_refl eq_refl RRsel1 RRr2_0 AP_sel1_r2_0) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [r2_0; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [r2_0; exW_canary SEGS 1410112 m6]) m6 (EVar 101) (EVar 237) arr1 r2_0 0 8 0 120 eq_refl eq_refl RRarr1 RRr2_0 AP_arr1_r2_0) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [r2_0; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [r2_0; exW_canary SEGS 1410112 m6]) m6 (EVar 135) (EVar 237) r1_0 r2_0 0 24 0 120 eq_refl eq_refl RRr1_0 RRr2_0 AP_r1_0_r2_0) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [r2_0; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [r2_0; exW_canary SEGS 1410112 m6]) m6 (EVar 169) (EVar 237) sel2 r2_0 0 32 0 120 eq_refl eq_refl RRsel2 RRr2_0 AP_sel2_r2_0) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [r2_0; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [r2_0; exW_canary SEGS 1410112 m6]) m6 (EVar 203) (EVar 237) arr2 r2_0 0 8 0 120 eq_refl eq_refl RRarr2 RRr2_0 AP_arr2_r2_0) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals5 r6 [r2_0; exW_canary SEGS 1410112 m6]) m6))))))) as HKd6.
  pose proof (W_sok_win C A6 m6 _ (s - 4304) (Z.to_nat 4304) CK HW6 GLO1 GLO2) as SOK6.
  pose proof (exW_canary_ok SEGS 1410112 m6 (canary_any m6)) as CANOK6.
  pose (vals6 := vals5 ++ map (getr r6) ex_regs_list ++ map (Z_to_bv 64) [r2_0; exW_canary SEGS 1410112 m6]).
  pose proof (exW_kn_fixed SEGS C A6 m6 _ (ex_envL vals5 r6 [r2_0; exW_canary SEGS 1410112 m6]) (EVar 238) (EVar 32) (exW_canary SEGS 1410112 m6) s 4304 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW6 eq_refl (proj1 CANOK6) (proj2 CANOK6) eq_refl eq_refl eq_refl SOK6 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf6.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb6 (proj2 (Forall_app _ _ _) (conj HKd6 (proj2 (Forall_app _ _ _) (conj HKf6 HKa6)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn6 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN6 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb6 HKd6 HKf6 HKa6 SOK6 CANOK6.
  repeat match goal with H : getr r6 _ = _ |- _ => clear H end.
  exq_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO5 ALr2_0.
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E6 := EEx) in HR, Hlf, HK, Hms |- *; set (log6 := LLx) in Hms, Hlf; set (M6 := mem_denot E6 m6 log6) in Hms end.
  assert (WP6 : W C A6 M6 (with_vmmaps vm6 md) /\ POSTM C A0 s m6 M6).
  { subst M6. apply (exW_win_blks C A6 A0 m6 _ E6 log6 (EVar 32) s 4304 [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 8%Z); (EVar 135, r1_0, 24%Z); (EVar 169, sel2, 32%Z); (EVar 203, arr2, 8%Z); (EVar 237, r2_0, 120%Z)] CK HW6 SUB6 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a6 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a6 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a6 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRsel2 (conj Lsel2_a6 (conj Fsel2 F0sel2))))|]. constructor; [exact (conj eq_refl (conj RRarr2 (conj Larr2_a6 (conj Farr2 F0arr2))))|]. constructor; [exact (conj eq_refl (conj RRr2_0 (conj Lr2_0_a6 (conj Fr2_0 F0r2_0))))|]. constructor. }
  assert (CFs6 : O23LeptCselsA.cs_fra s (-16) (-24) m0 M6).
  { subst M6. apply (cs_frame_sess C A6 A0 m0 m6 _ E6 log6 (EVar 32) s 4304 (-16) (-24) [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 8%Z); (EVar 135, r1_0, 24%Z); (EVar 169, sel2, 32%Z); (EVar 203, arr2, 8%Z); (EVar 237, r2_0, 120%Z)] CK HW6 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exact RS | lia | exact Hhi | reflexivity | | reflexivity | exact CF6]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a6 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a6 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a6 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRsel2 (conj Lsel2_a6 (conj Fsel2 F0sel2))))|]. constructor; [exact (conj eq_refl (conj RRarr2 (conj Larr2_a6 (conj Farr2 F0arr2))))|]. constructor; [exact (conj eq_refl (conj RRr2_0 (conj Lr2_0_a6 (conj Fr2_0 F0r2_0))))|]. constructor. }
  destruct WP6 as [HWs6 PMs6].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact Hms |].
  pose (BSF := [(32%nat, s); (67%nat, sel1); (101%nat, arr1); (135%nat, r1_0); (169%nat, sel2); (203%nat, arr2); (237%nat, r2_0)]).
  exW_regfactB BSF HR ex_r10 G10.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-16)%Z 8%nat CO1.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-24)%Z 8%nat CO2.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel1 0%Z 4%nat Csel1_0.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel1 4%Z 4%nat Csel1_4.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel1 8%Z 4%nat Csel1_8.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel1 12%Z 4%nat Csel1_12.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel1 16%Z 8%nat Csel1_16.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel1 24%Z 8%nat Csel1_24.
  exW_cellB HK Hlf r0 BSF (EVar 101) arr1 0%Z 8%nat Carr1_0.
  exW_cellB HK Hlf r0 BSF (EVar 135) r1_0 0%Z 4%nat Cr1_0_0.
  exW_cellB HK Hlf r0 BSF (EVar 135) r1_0 4%Z 4%nat Cr1_0_4.
  exW_cellB HK Hlf r0 BSF (EVar 135) r1_0 8%Z 4%nat Cr1_0_8.
  exW_cellB HK Hlf r0 BSF (EVar 135) r1_0 12%Z 4%nat Cr1_0_12.
  exW_cellB HK Hlf r0 BSF (EVar 135) r1_0 16%Z 4%nat Cr1_0_16.
  exW_cellB HK Hlf r0 BSF (EVar 135) r1_0 20%Z 4%nat Cr1_0_20.
  assert (SF1 : cs_sel_facts C A0 A6 M6 sel1 arr1 1 6 0 3 [r1_0] [[1; 1; 1; 1; 1; 1]]%Z).
  { split; [|split; [|split]].
    - cbn [map]. constructor; [exact (conj Lsel1_a6 (conj Fsel1 (conj F0sel1 RRsel1)))|]. constructor; [exact (conj Larr1_a6 (conj Farr1 (conj F0arr1 RRarr1)))|]. constructor; [exact (conj Lr1_0_a6 (conj Fr1_0 (conj F0r1_0 RRr1_0)))|]. constructor.
    - constructor; [exact Csel1_0|]. constructor; [exact Csel1_4|]. constructor; [exact Csel1_8|]. constructor; [exact Csel1_12|]. constructor; [exact Csel1_16|]. constructor; [exact Csel1_24|]. constructor.
    - cbn [O23LeptCselsA.cs_mk]. constructor; [exact Carr1_0|]. constructor.
    - cbn [O23LeptCselsA.cs_mk]. constructor; [constructor; [exact Cr1_0_0|]; constructor; [exact Cr1_0_4|]; constructor; [exact Cr1_0_8|]; constructor; [exact Cr1_0_12|]; constructor; [exact Cr1_0_16|]; constructor; [exact Cr1_0_20|]; constructor|]. constructor. }
  exW_cellB HK Hlf r0 BSF (EVar 169) sel2 0%Z 4%nat Csel2_0.
  exW_cellB HK Hlf r0 BSF (EVar 169) sel2 4%Z 4%nat Csel2_4.
  exW_cellB HK Hlf r0 BSF (EVar 169) sel2 8%Z 4%nat Csel2_8.
  exW_cellB HK Hlf r0 BSF (EVar 169) sel2 12%Z 4%nat Csel2_12.
  exW_cellB HK Hlf r0 BSF (EVar 169) sel2 16%Z 8%nat Csel2_16.
  exW_cellB HK Hlf r0 BSF (EVar 169) sel2 24%Z 8%nat Csel2_24.
  exW_cellB HK Hlf r0 BSF (EVar 203) arr2 0%Z 8%nat Carr2_0.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 0%Z 4%nat Cr2_0_0.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 4%Z 4%nat Cr2_0_4.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 8%Z 4%nat Cr2_0_8.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 12%Z 4%nat Cr2_0_12.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 16%Z 4%nat Cr2_0_16.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 20%Z 4%nat Cr2_0_20.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 24%Z 4%nat Cr2_0_24.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 28%Z 4%nat Cr2_0_28.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 32%Z 4%nat Cr2_0_32.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 36%Z 4%nat Cr2_0_36.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 40%Z 4%nat Cr2_0_40.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 44%Z 4%nat Cr2_0_44.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 48%Z 4%nat Cr2_0_48.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 52%Z 4%nat Cr2_0_52.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 56%Z 4%nat Cr2_0_56.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 60%Z 4%nat Cr2_0_60.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 64%Z 4%nat Cr2_0_64.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 68%Z 4%nat Cr2_0_68.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 72%Z 4%nat Cr2_0_72.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 76%Z 4%nat Cr2_0_76.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 80%Z 4%nat Cr2_0_80.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 84%Z 4%nat Cr2_0_84.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 88%Z 4%nat Cr2_0_88.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 92%Z 4%nat Cr2_0_92.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 96%Z 4%nat Cr2_0_96.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 100%Z 4%nat Cr2_0_100.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 104%Z 4%nat Cr2_0_104.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 108%Z 4%nat Cr2_0_108.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 112%Z 4%nat Cr2_0_112.
  exW_cellB HK Hlf r0 BSF (EVar 237) r2_0 116%Z 4%nat Cr2_0_116.
  assert (SF2 : cs_sel_facts C A0 A6 M6 sel2 arr2 1 30 0 15 [r2_0] [[0; 0; 0; 1; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 1; 0; 0]]%Z).
  { split; [|split; [|split]].
    - cbn [map]. constructor; [exact (conj Lsel2_a6 (conj Fsel2 (conj F0sel2 RRsel2)))|]. constructor; [exact (conj Larr2_a6 (conj Farr2 (conj F0arr2 RRarr2)))|]. constructor; [exact (conj Lr2_0_a6 (conj Fr2_0 (conj F0r2_0 RRr2_0)))|]. constructor.
    - constructor; [exact Csel2_0|]. constructor; [exact Csel2_4|]. constructor; [exact Csel2_8|]. constructor; [exact Csel2_12|]. constructor; [exact Csel2_16|]. constructor; [exact Csel2_24|]. constructor.
    - cbn [O23LeptCselsA.cs_mk]. constructor; [exact Carr2_0|]. constructor.
    - cbn [O23LeptCselsA.cs_mk]. constructor; [constructor; [exact Cr2_0_0|]; constructor; [exact Cr2_0_4|]; constructor; [exact Cr2_0_8|]; constructor; [exact Cr2_0_12|]; constructor; [exact Cr2_0_16|]; constructor; [exact Cr2_0_20|]; constructor; [exact Cr2_0_24|]; constructor; [exact Cr2_0_28|]; constructor; [exact Cr2_0_32|]; constructor; [exact Cr2_0_36|]; constructor; [exact Cr2_0_40|]; constructor; [exact Cr2_0_44|]; constructor; [exact Cr2_0_48|]; constructor; [exact Cr2_0_52|]; constructor; [exact Cr2_0_56|]; constructor; [exact Cr2_0_60|]; constructor; [exact Cr2_0_64|]; constructor; [exact Cr2_0_68|]; constructor; [exact Cr2_0_72|]; constructor; [exact Cr2_0_76|]; constructor; [exact Cr2_0_80|]; constructor; [exact Cr2_0_84|]; constructor; [exact Cr2_0_88|]; constructor; [exact Cr2_0_92|]; constructor; [exact Cr2_0_96|]; constructor; [exact Cr2_0_100|]; constructor; [exact Cr2_0_104|]; constructor; [exact Cr2_0_108|]; constructor; [exact Cr2_0_112|]; constructor; [exact Cr2_0_116|]; constructor|]. constructor. }
  assert (ND : List.NoDup (O23LeptCselsA.cs_words sel1 arr1 [r1_0] ++ O23LeptCselsA.cs_words sel2 arr2 [r2_0])).
  { cbn [O23LeptCselsA.cs_words map app]. repeat constructor. all: intros X; cbn [In] in X; repeat (destruct X as [X|X]; [match goal with H : Z_to_bv 64 _ <> Z_to_bv 64 _ |- _ => first [exact (H X) | exact (H (eq_sym X))] end|]); exact X. }
  assert (LD : forall q : word, ~ In q (O23LeptCselsA.cs_words sel1 arr1 [r1_0] ++ O23LeptCselsA.cs_words sel2 arr2 [r2_0]) -> live A6 q = live A0 q).
  { intros q Hq. apply LDEL6. intros X. apply Hq. clear - X. cbn [O23LeptCselsA.cs_words map app In] in X |- *. tauto. }
  lazymatch goal with |- realizes _ (mkCfg (@mkst (mkFP ?frF ?csF) _ _ _ _) _) _ => assert (FSK : forall r : reg, In (u r) fs_list -> reg_get frF r = reg_get fr r) end.
  { intros r Hr. apply (fr_kept_incl _ _ _ O23LeptCselsA.cs_fkeys r); [vm_compute; reflexivity | exact (O23LeptCselsA.cs_fs_keys r Hr)]. }
  assert (CSK : cs_kept r0 RcF).
  { lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 RcF [(2%nat, EAlu ALU_ADD (EVar 32) (ELit (-48))); (4%nat, ELit 1278416)] HR) end; [exW_entry_vars | constructor; [refine (eq_trans (ex_ptr_val s (-48)) _); symmetry; exact HSP | constructor; [symmetry; exact HTP | constructor]] | vm_compute; reflexivity]. }
  exact (HC _ _ A6 M6 vm6 RcF sel1 arr1 r1_0 sel2 arr2 r2_0 FZ FSK HWs6 CSK G10 SUB6 (POSTM_trans _ _ _ _ _ _ PM6 PMs6) CFs6 RM6 CO1 CO2 SF1 SF2 ND LD).
Qed.

(* [comment removed for export] *)
Lemma csels_chain8 : forall (fx : FPState) C A m md regs (s : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> frm_zero (@fp_csr fx) ->
  getr regs 2 = Z_to_bv 64 (s + -48) -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CSELS_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 1278416 ->
  getr regs 10 = Z_to_bv 64 8 -> getr regs 11 = Z_to_bv 64 2 -> getr regs 12 = Z_to_bv 64 (s + -32) -> getr regs 13 = Z_to_bv 64 (s + -40) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (16 <= kR)%Z -> (16 * 2 ^ 17 <= bR)%Z ->
  (forall (fr' : bvmap 5 word) (cs' : bv 32) A' m' vm' regs' (sel1 arr1 r1_0 r1_1 r1_2 r1_3 sel2 arr2 r2_0 r2_1 r2_2 r2_3 r2_4 r2_5 r2_6 r2_7 : Z),
     frm_zero cs' -> (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get (@fp_regs fx) r) ->
     W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> getr regs' 10 = Z_to_bv 64 0 ->
     sub_live A A' -> POSTM C A s m m' -> O23LeptCselsA.cs_fra s (-32) (-40) m m' ->
     aroom A' vm' (kR - 16) (bR - 16 * 2 ^ 17) ->
     cs_cell m' ((s + -32)%Z, 8%nat, sel1) -> cs_cell m' ((s + -40)%Z, 8%nat, sel2) ->
     cs_sel_facts C A A' m' sel1 arr1 4 1 2 0 [r1_0; r1_1; r1_2; r1_3] [[1]; [1]; [1]; [1]]%Z ->
     cs_sel_facts C A A' m' sel2 arr2 8 1 4 0 [r2_0; r2_1; r2_2; r2_3; r2_4; r2_5; r2_6; r2_7] [[0]; [0]; [1]; [0]; [0]; [0]; [1]; [0]]%Z ->
     List.NoDup (O23LeptCselsA.cs_words sel1 arr1 [r1_0; r1_1; r1_2; r1_3] ++ O23LeptCselsA.cs_words sel2 arr2 [r2_0; r2_1; r2_2; r2_3; r2_4; r2_5; r2_6; r2_7]) ->
     (forall q : word, ~ In q (O23LeptCselsA.cs_words sel1 arr1 [r1_0; r1_1; r1_2; r1_3] ++ O23LeptCselsA.cs_words sel2 arr2 [r2_0; r2_1; r2_2; r2_3; r2_4; r2_5; r2_6; r2_7]) -> live A' q = live A q) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 669044) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 s ret S CK HW0 HFZ H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 H13 kR bR RM0 HkR HbR HC.
  unfold CSELS_WIN in *.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 (s + -48))) by exact H2.
  assert (HTP : ex_keep (getr r0 ex_r4 = Z_to_bv 64 1278416)) by exact H4.
  destruct fx as [fr cs]. cbn [fp_csr] in HFZ. rename HFZ into FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  pose proof (O23LeptCselsA.cs_fra_refl s (-32) (-40) m0) as CF0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  replace kR with (kR - 0)%Z in RM0 by lia. replace bR with (bR - 0 * 2 ^ 17)%Z in RM0 by lia.
  pose (valsI := @nil word).
  pose proof (fun (q : word) (_ : ~ In q []) => eq_refl (live A0 q)) as LDEL0.
  assert (GLO1 : (c_top C - LSTK <= s - 4304)%Z) by lia.
  assert (GLO2 : (s - 4304 + Z.of_nat (Z.to_nat 4304) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (4304 <= s)%Z) by lia.
  pose proof (W_sok_win C A0 m0 _ (s - 4304) (Z.to_nat 4304) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 1410112 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0]) (EVar 34) (EVar 32) (exW_canary SEGS 1410112 m0) s 4304 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0]) m0 [KRange (EVar 32) 1425616 (2 ^ 63); KAlign (EVar 32) 16]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 HKf0)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exq_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 4304 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  assert (CFs0 : O23LeptCselsA.cs_fra s (-32) (-40) m0 M0).
  { subst M0. apply (cs_frame_sess C A0 A0 m0 m0 _ E0 log0 (EVar 32) s 4304 (-32) (-40) [] CK HW0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exact RS | lia | exact Hhi | reflexivity | | reflexivity | exact CF0]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r1 Q1_0. exW_regfactB BS0 HR ex_r2 Q2_0. exW_regfactB BS0 HR ex_r4 Q4_0.
  clear BS0.
  lazymatch type of Q2_0 with _ = Z_to_bv 64 (s + ?off) => pose (OFF0 := off) end.
  pose proof (alloc_margin_small (1 * 32) ltac:(exW_cmp)) as MG0.
  lazymatch type of Q1_0 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_0 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A0 M0 _ Rc0 1 32 (kR - 0) (bR - 0 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs0 Q10_0 Q11_0 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM0) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_0
             ltac:(red; apply bv_eq; reflexivity) Q4_0 Q2_0 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A1 m1 vm1 r1 res0 HW1 Hres0 CSx0 Hnz0 Fsel1x Lo0 F0sel1 LEQ0 ZERO0 ALsel1 TOP0 PMc0 RM1.
  pose proof CSx0 as CS0. clear CSx0.
  rewrite with_vmmaps_twice in HW1 |- *.
  assert (Eres0 : res0 = Z_to_bv 64 (u res0)) by (symmetry; apply zbv_self).
  pose proof (u64_range res0) as RRsel1. set (sel1 := u res0) in *. clearbody sel1. rewrite Eres0 in Hres0, Fsel1x, Lo0, F0sel1, LEQ0, ZERO0. clear Eres0.
  change (1 * 32)%Z with 32%Z in *.
  pose proof (exW_blk_img_apart_h2 C A1 m1 _ sel1 32 CK HW1 Lo0 RRsel1 eq_refl eq_refl) as IMGAPsel1. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPsel1.
  pose proof (exW_win_blk_apart_h C A1 m1 _ s 4304 sel1 32 CK HW1 Lo0 eq_refl RRsel1 GLO1) as WAPsel1.
  assert (Fsel1 : live A0 (Z_to_bv 64 sel1) = None).
  { destruct (live A0 (Z_to_bv 64 sel1)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB0 _ _ EE) as XX. first [discriminate Fsel1x | (rewrite Fsel1x in XX; discriminate XX)]. }
  pose proof Lo0 as Lsel1_a1.
  assert (SUB1 : sub_live A0 A1).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 sel1) by (intros ->; rewrite Fsel1 in Lq; discriminate Lq). rewrite (LEQ0 q NEq). exact (SUB0 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 sel1 :: [])) => eq_trans (LEQ0 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL0 q (fun XX => Hq (or_intror XX)))) as LDEL1.
  assert (PM1 : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|]. apply (POSTM_sub C A0 A0 _ _ _ SUB0).
    apply (POSTM_mono C A0 (s + OFF0) s); [unfold OFF0; lia | exact PMc0]. }
  pose proof (cs_frame_hop C s 4304 OFF0 (-32) (-40) m0 M0 m1 CK (proj1 PMc0) ltac:(lia) ltac:(vm_cast_no_check (eq_refl true)) ltac:(vm_cast_no_check (eq_refl true)) CFs0) as CF1.
  replace (kR - 0 - 1)%Z with (kR - 1)%Z in RM1 by lia. rewrite MG0 in RM1. replace (bR - 0 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 1 * 2 ^ 17)%Z in RM1 by lia.
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, OFF0, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF0 4304 M0 m1 E0 (EVar 32) CK (proj1 PMc0) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E0 m1 kk') in HKk0 end.
  pose proof (regs_ok_agree 35%nat E0 (ex_envL vals0 r1 [sel1; exW_canary SEGS 1410112 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [sel1; exW_canary SEGS 1410112 m1] 35%nat ltac:(vm_cast_no_check (eq_refl 35%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [sel1; exW_canary SEGS 1410112 m1]) m1 _) by (exact (know_ok_agree SEGS 35%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  rewrite (fr_denot_agree 35%nat E0 (ex_envL vals0 r1 [sel1; exW_canary SEGS 1410112 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r1 ex_r10 (EVar 67) HRn1 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres0)) as HRx1. clear HRn1. rename HRx1 into HRn1.
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q11_0 Q1_0 Q2_0 Q4_0 PM0 HW0 PMc0 CS0 SUB0 RM0 MG0 TOP0 LEQ0 Hnz0 Fsel1x Lo0 OFF0 LDEL0 CF0 CFs0.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  pose proof (exW_kn_blk SEGS C A1 m1 _ (ex_envL vals0 r1 [sel1; exW_canary SEGS 1410112 m1]) (EVar 67) (EVar 32) sel1 32 s 4304 65536 1347584 p16_segs CK HW1 Lsel1_a1 RRsel1 eq_refl eq_refl eq_refl RS ALsel1 ZERO0 WAPsel1 IMGAPsel1) as HKb1.
  pose proof (W_sok_win C A1 m1 _ (s - 4304) (Z.to_nat 4304) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 1410112 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [sel1; exW_canary SEGS 1410112 m1]).
  pose proof (exW_kn_fixed SEGS C A1 m1 _ (ex_envL vals0 r1 [sel1; exW_canary SEGS 1410112 m1]) (EVar 68) (EVar 32) (exW_canary SEGS 1410112 m1) s 4304 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb1 (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb1 HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  exq_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO0 ALsel1.
  exb_exit ST Rc1 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A1 M1 (with_vmmaps vm1 md) /\ POSTM C A0 s m1 M1).
  { subst M1. apply (exW_win_blks C A1 A0 m1 _ E1 log1 (EVar 32) s 4304 [(EVar 67, sel1, 32%Z)] CK HW1 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a1 (conj Fsel1 F0sel1))))|]. constructor. }
  assert (CFs1 : O23LeptCselsA.cs_fra s (-32) (-40) m0 M1).
  { subst M1. apply (cs_frame_sess C A1 A0 m0 m1 _ E1 log1 (EVar 32) s 4304 (-32) (-40) [(EVar 67, sel1, 32%Z)] CK HW1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exact RS | lia | exact Hhi | reflexivity | | reflexivity | exact CF1]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a1 (conj Fsel1 F0sel1))))|]. constructor. }
  destruct WP1 as [HWs1 PMs1].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log1 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC1 : carry log1 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc1 : know_ok SEGS E1 M1 kn1) by (apply (carry_after SEGS E1 m1 log1 kn0 [] kn1 scs hs HC1 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose (BS1 := [(32%nat, s); (67%nat, sel1)]).
  exW_regfactB BS1 HR ex_r10 Q10_1. exW_regfactB BS1 HR ex_r11 Q11_1. exW_regfactB BS1 HR ex_r1 Q1_1. exW_regfactB BS1 HR ex_r2 Q2_1. exW_regfactB BS1 HR ex_r4 Q4_1.
  clear BS1.
  lazymatch type of Q2_1 with _ = Z_to_bv 64 (s + ?off) => pose (OFF1 := off) end.
  pose proof (alloc_margin_small (4 * 8) ltac:(exW_cmp)) as MG1.
  lazymatch type of Q1_1 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_1 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A1 M1 _ Rc1 4 8 (kR - 1) (bR - 1 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs1 Q10_1 Q11_1 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM1) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_1
             ltac:(red; apply bv_eq; reflexivity) Q4_1 Q2_1 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A2 m2 vm2 r2 res1 HW2 Hres1 CSx1 Hnz1 Farr1x Lo1 F0arr1 LEQ1 ZERO1 ALarr1 TOP1 PMc1 RM2.
  pose proof CSx1 as CS1. clear CSx1.
  rewrite with_vmmaps_twice in HW2 |- *.
  assert (Eres1 : res1 = Z_to_bv 64 (u res1)) by (symmetry; apply zbv_self).
  pose proof (u64_range res1) as RRarr1. set (arr1 := u res1) in *. clearbody arr1. rewrite Eres1 in Hres1, Farr1x, Lo1, F0arr1, LEQ1, ZERO1. clear Eres1.
  change (4 * 8)%Z with 32%Z in *.
  pose proof (exW_blk_img_apart_h2 C A2 m2 _ arr1 32 CK HW2 Lo1 RRarr1 eq_refl eq_refl) as IMGAParr1. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAParr1.
  pose proof (exW_win_blk_apart_h C A2 m2 _ s 4304 arr1 32 CK HW2 Lo1 eq_refl RRarr1 GLO1) as WAParr1.
  assert (Farr1 : live A0 (Z_to_bv 64 arr1) = None).
  { destruct (live A0 (Z_to_bv 64 arr1)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB1 _ _ EE) as XX. first [discriminate Farr1x | (rewrite Farr1x in XX; discriminate XX)]. }
  pose proof Lo1 as Larr1_a2.
  assert (SUB2 : sub_live A0 A2).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 arr1) by (intros ->; rewrite Farr1 in Lq; discriminate Lq). rewrite (LEQ1 q NEq). exact (SUB1 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 arr1 :: [Z_to_bv 64 sel1])) => eq_trans (LEQ1 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL1 q (fun XX => Hq (or_intror XX)))) as LDEL2.
  assert (NE_sel1_arr1 : Z_to_bv 64 sel1 <> Z_to_bv 64 arr1) by (intros EE; rewrite EE in Lsel1_a1; rewrite Farr1x in Lsel1_a1; discriminate Lsel1_a1).
  assert (Lsel1_a2 : live A2 (Z_to_bv 64 sel1) = Some 32%Z) by (rewrite (LEQ1 _ NE_sel1_arr1); exact Lsel1_a1).
  pose proof (exW_blk_apart_h C A2 m2 _ sel1 arr1 32 32 CK HW2 Lsel1_a2 Larr1_a2 NE_sel1_arr1 RRsel1 RRarr1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel1_arr1.
  assert (PM2 : POSTM C A0 s m0 m2).
  { eapply POSTM_trans; [exact PM1|]. eapply POSTM_trans; [exact PMs1|]. apply (POSTM_sub C A0 A1 _ _ _ SUB1).
    apply (POSTM_mono C A1 (s + OFF1) s); [unfold OFF1; lia | exact PMc1]. }
  pose proof (cs_frame_hop C s 4304 OFF1 (-32) (-40) m0 M1 m2 CK (proj1 PMc1) ltac:(lia) ltac:(vm_cast_no_check (eq_refl true)) ltac:(vm_cast_no_check (eq_refl true)) CFs1) as CF2.
  replace (kR - 1 - 1)%Z with (kR - 2)%Z in RM2 by lia. rewrite MG1 in RM2. replace (bR - 1 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 2 * 2 ^ 17)%Z in RM2 by lia.
  assert (KEPT1 : Forall (ex_region_kept E1 M1 m2) [(EVar 32, OFF1, 0%Z); (EVar 67, 0%Z, 32%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF1 4304 M1 m2 E1 (EVar 32) CK (proj1 PMc1) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A1 A1 M1 _ M1 m2 E1 (EVar 67) sel1 32 CK HWs1 Lsel1_a1 RRsel1 eq_refl (proj2 PMc1) Lsel1_a1 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E1 M1 m2 _ [] _ HKc1 KEPT1) as HKk1.
  match type of HKk1 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E1 m2 kk') in HKk1 end.
  pose proof (regs_ok_agree 69%nat E1 (ex_envL vals1 r2 [arr1; exW_canary SEGS 1410112 m2]) _ _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa1.
  pose proof (exW_regs_call _ _ _ _ _ HRa1 (ex_regs_ok_junk vals1 r2 [arr1; exW_canary SEGS 1410112 m2] 69%nat ltac:(vm_cast_no_check (eq_refl 69%nat))) CS1) as HRn2.
  clear HRa1.
  assert (HKa2 : know_ok SEGS (ex_envL vals1 r2 [arr1; exW_canary SEGS 1410112 m2]) m2 _) by (exact (know_ok_agree SEGS 69%nat E1 _ m2 _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk1)).
  rewrite (fr_denot_agree 69%nat E1 (ex_envL vals1 r2 [arr1; exW_canary SEGS 1410112 m2]) _ fr (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r2 ex_r10 (EVar 101) HRn2 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres1)) as HRx2. clear HRn2. rename HRx2 into HRn2.
  clear HR HK Hlf Hms HKc1 HKk1 KEPT1 HC1 HWs1 PMs1 Q10_1 Q11_1 Q1_1 Q2_1 Q4_1 PM1 HW1 PMc1 CS1 SUB1 RM1 MG1 TOP1 LEQ1 Hnz1 Farr1x Lo1 OFF1 LDEL1 CF1 CFs1 Lsel1_a1.
  subst M1. clear log1. clear E1. try clear Rc1. clear KN1.
  lazymatch type of HRn2 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn2 end.
  pose proof (exW_kn_blk SEGS C A2 m2 _ (ex_envL vals1 r2 [arr1; exW_canary SEGS 1410112 m2]) (EVar 101) (EVar 32) arr1 32 s 4304 65536 1347584 p16_segs CK HW2 Larr1_a2 RRarr1 eq_refl eq_refl eq_refl RS ALarr1 ZERO1 WAParr1 IMGAParr1) as HKb2.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals1 r2 [arr1; exW_canary SEGS 1410112 m2]) m2) _ _ (ex_kdisj_apart SEGS (ex_envL vals1 r2 [arr1; exW_canary SEGS 1410112 m2]) m2 (EVar 67) (EVar 101) sel1 arr1 0 32 0 32 eq_refl eq_refl RRsel1 RRarr1 AP_sel1_arr1) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals1 r2 [arr1; exW_canary SEGS 1410112 m2]) m2))) as HKd2.
  pose proof (W_sok_win C A2 m2 _ (s - 4304) (Z.to_nat 4304) CK HW2 GLO1 GLO2) as SOK2.
  pose proof (exW_canary_ok SEGS 1410112 m2 (canary_any m2)) as CANOK2.
  pose (vals2 := vals1 ++ map (getr r2) ex_regs_list ++ map (Z_to_bv 64) [arr1; exW_canary SEGS 1410112 m2]).
  pose proof (exW_kn_fixed SEGS C A2 m2 _ (ex_envL vals1 r2 [arr1; exW_canary SEGS 1410112 m2]) (EVar 102) (EVar 32) (exW_canary SEGS 1410112 m2) s 4304 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW2 eq_refl (proj1 CANOK2) (proj2 CANOK2) eq_refl eq_refl eq_refl SOK2 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf2.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb2 (proj2 (Forall_app _ _ _) (conj HKd2 (proj2 (Forall_app _ _ _) (conj HKf2 HKa2)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn2 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN2 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb2 HKd2 HKf2 HKa2 SOK2 CANOK2.
  repeat match goal with H : getr r2 _ = _ |- _ => clear H end.
  exq_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO1 ALarr1.
  exb_exit ST Rc2 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E2 := EEx) in HR, Hlf, HK, Hms |- *; set (log2 := LLx) in Hms, Hlf; set (M2 := mem_denot E2 m2 log2) in Hms end.
  assert (WP2 : W C A2 M2 (with_vmmaps vm2 md) /\ POSTM C A0 s m2 M2).
  { subst M2. apply (exW_win_blks C A2 A0 m2 _ E2 log2 (EVar 32) s 4304 [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z)] CK HW2 SUB2 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a2 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a2 (conj Farr1 F0arr1))))|]. constructor. }
  assert (CFs2 : O23LeptCselsA.cs_fra s (-32) (-40) m0 M2).
  { subst M2. apply (cs_frame_sess C A2 A0 m0 m2 _ E2 log2 (EVar 32) s 4304 (-32) (-40) [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z)] CK HW2 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exact RS | lia | exact Hhi | reflexivity | | reflexivity | exact CF2]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a2 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a2 (conj Farr1 F0arr1))))|]. constructor. }
  destruct WP2 as [HWs2 PMs2].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log2 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC2 : carry log2 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc2 : know_ok SEGS E2 M2 kn1) by (apply (carry_after SEGS E2 m2 log2 kn0 [] kn1 scs hs HC2 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact Hms |].
  pose (BS2 := [(32%nat, s); (67%nat, sel1); (101%nat, arr1)]).
  exW_regfactB BS2 HR ex_r10 Q10_2. exW_regfactB BS2 HR ex_r11 Q11_2. exW_regfactB BS2 HR ex_r1 Q1_2. exW_regfactB BS2 HR ex_r2 Q2_2. exW_regfactB BS2 HR ex_r4 Q4_2.
  clear BS2.
  lazymatch type of Q2_2 with _ = Z_to_bv 64 (s + ?off) => pose (OFF2 := off) end.
  pose proof (alloc_margin_small (1 * 4) ltac:(exW_cmp)) as MG2.
  lazymatch type of Q1_2 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_2 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A2 M2 _ Rc2 1 4 (kR - 2) (bR - 2 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs2 Q10_2 Q11_2 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM2) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_2
             ltac:(red; apply bv_eq; reflexivity) Q4_2 Q2_2 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A3 m3 vm3 r3 res2 HW3 Hres2 CSx2 Hnz2 Fr1_0x Lo2 F0r1_0 LEQ2 ZERO2 ALr1_0 TOP2 PMc2 RM3.
  pose proof CSx2 as CS2. clear CSx2.
  rewrite with_vmmaps_twice in HW3 |- *.
  assert (Eres2 : res2 = Z_to_bv 64 (u res2)) by (symmetry; apply zbv_self).
  pose proof (u64_range res2) as RRr1_0. set (r1_0 := u res2) in *. clearbody r1_0. rewrite Eres2 in Hres2, Fr1_0x, Lo2, F0r1_0, LEQ2, ZERO2. clear Eres2.
  change (1 * 4)%Z with 4%Z in *.
  pose proof (exW_blk_img_apart_h2 C A3 m3 _ r1_0 4 CK HW3 Lo2 RRr1_0 eq_refl eq_refl) as IMGAPr1_0. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPr1_0.
  pose proof (exW_win_blk_apart_h C A3 m3 _ s 4304 r1_0 4 CK HW3 Lo2 eq_refl RRr1_0 GLO1) as WAPr1_0.
  assert (Fr1_0 : live A0 (Z_to_bv 64 r1_0) = None).
  { destruct (live A0 (Z_to_bv 64 r1_0)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB2 _ _ EE) as XX. first [discriminate Fr1_0x | (rewrite Fr1_0x in XX; discriminate XX)]. }
  pose proof Lo2 as Lr1_0_a3.
  assert (SUB3 : sub_live A0 A3).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 r1_0) by (intros ->; rewrite Fr1_0 in Lq; discriminate Lq). rewrite (LEQ2 q NEq). exact (SUB2 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 r1_0 :: [Z_to_bv 64 arr1; Z_to_bv 64 sel1])) => eq_trans (LEQ2 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL2 q (fun XX => Hq (or_intror XX)))) as LDEL3.
  assert (NE_sel1_r1_0 : Z_to_bv 64 sel1 <> Z_to_bv 64 r1_0) by (intros EE; rewrite EE in Lsel1_a2; rewrite Fr1_0x in Lsel1_a2; discriminate Lsel1_a2).
  assert (Lsel1_a3 : live A3 (Z_to_bv 64 sel1) = Some 32%Z) by (rewrite (LEQ2 _ NE_sel1_r1_0); exact Lsel1_a2).
  pose proof (exW_blk_apart_h C A3 m3 _ sel1 r1_0 32 4 CK HW3 Lsel1_a3 Lr1_0_a3 NE_sel1_r1_0 RRsel1 RRr1_0 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel1_r1_0.
  assert (NE_arr1_r1_0 : Z_to_bv 64 arr1 <> Z_to_bv 64 r1_0) by (intros EE; rewrite EE in Larr1_a2; rewrite Fr1_0x in Larr1_a2; discriminate Larr1_a2).
  assert (Larr1_a3 : live A3 (Z_to_bv 64 arr1) = Some 32%Z) by (rewrite (LEQ2 _ NE_arr1_r1_0); exact Larr1_a2).
  pose proof (exW_blk_apart_h C A3 m3 _ arr1 r1_0 32 4 CK HW3 Larr1_a3 Lr1_0_a3 NE_arr1_r1_0 RRarr1 RRr1_0 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr1_r1_0.
  assert (PM3 : POSTM C A0 s m0 m3).
  { eapply POSTM_trans; [exact PM2|]. eapply POSTM_trans; [exact PMs2|]. apply (POSTM_sub C A0 A2 _ _ _ SUB2).
    apply (POSTM_mono C A2 (s + OFF2) s); [unfold OFF2; lia | exact PMc2]. }
  pose proof (cs_frame_hop C s 4304 OFF2 (-32) (-40) m0 M2 m3 CK (proj1 PMc2) ltac:(lia) ltac:(vm_cast_no_check (eq_refl true)) ltac:(vm_cast_no_check (eq_refl true)) CFs2) as CF3.
  replace (kR - 2 - 1)%Z with (kR - 3)%Z in RM3 by lia. rewrite MG2 in RM3. replace (bR - 2 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 3 * 2 ^ 17)%Z in RM3 by lia.
  assert (KEPT2 : Forall (ex_region_kept E2 M2 m3) [(EVar 32, OFF2, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 32%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF2 4304 M2 m3 E2 (EVar 32) CK (proj1 PMc2) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A2 A2 M2 _ M2 m3 E2 (EVar 67) sel1 32 CK HWs2 Lsel1_a2 RRsel1 eq_refl (proj2 PMc2) Lsel1_a2 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A2 A2 M2 _ M2 m3 E2 (EVar 101) arr1 32 CK HWs2 Larr1_a2 RRarr1 eq_refl (proj2 PMc2) Larr1_a2 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E2 M2 m3 _ [] _ HKc2 KEPT2) as HKk2.
  match type of HKk2 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E2 m3 kk') in HKk2 end.
  pose proof (regs_ok_agree 103%nat E2 (ex_envL vals2 r3 [r1_0; exW_canary SEGS 1410112 m3]) _ _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa2.
  pose proof (exW_regs_call _ _ _ _ _ HRa2 (ex_regs_ok_junk vals2 r3 [r1_0; exW_canary SEGS 1410112 m3] 103%nat ltac:(vm_cast_no_check (eq_refl 103%nat))) CS2) as HRn3.
  clear HRa2.
  assert (HKa3 : know_ok SEGS (ex_envL vals2 r3 [r1_0; exW_canary SEGS 1410112 m3]) m3 _) by (exact (know_ok_agree SEGS 103%nat E2 _ m3 _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk2)).
  rewrite (fr_denot_agree 103%nat E2 (ex_envL vals2 r3 [r1_0; exW_canary SEGS 1410112 m3]) _ fr (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r3 ex_r10 (EVar 135) HRn3 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres2)) as HRx3. clear HRn3. rename HRx3 into HRn3.
  clear HR HK Hlf Hms HKc2 HKk2 KEPT2 HC2 HWs2 PMs2 Q10_2 Q11_2 Q1_2 Q2_2 Q4_2 PM2 HW2 PMc2 CS2 SUB2 RM2 MG2 TOP2 LEQ2 Hnz2 Fr1_0x Lo2 OFF2 LDEL2 CF2 CFs2 Lsel1_a2 Larr1_a2.
  subst M2. clear log2. clear E2. try clear Rc2. clear KN2.
  lazymatch type of HRn3 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn3 end.
  pose proof (exW_kn_blk SEGS C A3 m3 _ (ex_envL vals2 r3 [r1_0; exW_canary SEGS 1410112 m3]) (EVar 135) (EVar 32) r1_0 4 s 4304 65536 1347584 p16_segs CK HW3 Lr1_0_a3 RRr1_0 eq_refl eq_refl eq_refl RS ALr1_0 ZERO2 WAPr1_0 IMGAPr1_0) as HKb3.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals2 r3 [r1_0; exW_canary SEGS 1410112 m3]) m3) _ _ (ex_kdisj_apart SEGS (ex_envL vals2 r3 [r1_0; exW_canary SEGS 1410112 m3]) m3 (EVar 67) (EVar 135) sel1 r1_0 0 32 0 4 eq_refl eq_refl RRsel1 RRr1_0 AP_sel1_r1_0) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals2 r3 [r1_0; exW_canary SEGS 1410112 m3]) m3) _ _ (ex_kdisj_apart SEGS (ex_envL vals2 r3 [r1_0; exW_canary SEGS 1410112 m3]) m3 (EVar 101) (EVar 135) arr1 r1_0 0 32 0 4 eq_refl eq_refl RRarr1 RRr1_0 AP_arr1_r1_0) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals2 r3 [r1_0; exW_canary SEGS 1410112 m3]) m3)))) as HKd3.
  pose proof (W_sok_win C A3 m3 _ (s - 4304) (Z.to_nat 4304) CK HW3 GLO1 GLO2) as SOK3.
  pose proof (exW_canary_ok SEGS 1410112 m3 (canary_any m3)) as CANOK3.
  pose (vals3 := vals2 ++ map (getr r3) ex_regs_list ++ map (Z_to_bv 64) [r1_0; exW_canary SEGS 1410112 m3]).
  pose proof (exW_kn_fixed SEGS C A3 m3 _ (ex_envL vals2 r3 [r1_0; exW_canary SEGS 1410112 m3]) (EVar 136) (EVar 32) (exW_canary SEGS 1410112 m3) s 4304 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW3 eq_refl (proj1 CANOK3) (proj2 CANOK3) eq_refl eq_refl eq_refl SOK3 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf3.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb3 (proj2 (Forall_app _ _ _) (conj HKd3 (proj2 (Forall_app _ _ _) (conj HKf3 HKa3)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn3 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN3 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb3 HKd3 HKf3 HKa3 SOK3 CANOK3.
  repeat match goal with H : getr r3 _ = _ |- _ => clear H end.
  exq_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO2 ALr1_0.
  exb_exit ST Rc3 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E3 := EEx) in HR, Hlf, HK, Hms |- *; set (log3 := LLx) in Hms, Hlf; set (M3 := mem_denot E3 m3 log3) in Hms end.
  assert (WP3 : W C A3 M3 (with_vmmaps vm3 md) /\ POSTM C A0 s m3 M3).
  { subst M3. apply (exW_win_blks C A3 A0 m3 _ E3 log3 (EVar 32) s 4304 [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z); (EVar 135, r1_0, 4%Z)] CK HW3 SUB3 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a3 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a3 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a3 (conj Fr1_0 F0r1_0))))|]. constructor. }
  assert (CFs3 : O23LeptCselsA.cs_fra s (-32) (-40) m0 M3).
  { subst M3. apply (cs_frame_sess C A3 A0 m0 m3 _ E3 log3 (EVar 32) s 4304 (-32) (-40) [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z); (EVar 135, r1_0, 4%Z)] CK HW3 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exact RS | lia | exact Hhi | reflexivity | | reflexivity | exact CF3]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a3 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a3 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a3 (conj Fr1_0 F0r1_0))))|]. constructor. }
  destruct WP3 as [HWs3 PMs3].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log3 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC3 : carry log3 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc3 : know_ok SEGS E3 M3 kn1) by (apply (carry_after SEGS E3 m3 log3 kn0 [] kn1 scs hs HC3 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact Hms |].
  pose (BS3 := [(32%nat, s); (67%nat, sel1); (101%nat, arr1); (135%nat, r1_0)]).
  exW_regfactB BS3 HR ex_r10 Q10_3. exW_regfactB BS3 HR ex_r11 Q11_3. exW_regfactB BS3 HR ex_r1 Q1_3. exW_regfactB BS3 HR ex_r2 Q2_3. exW_regfactB BS3 HR ex_r4 Q4_3.
  clear BS3.
  lazymatch type of Q2_3 with _ = Z_to_bv 64 (s + ?off) => pose (OFF3 := off) end.
  pose proof (alloc_margin_small (1 * 4) ltac:(exW_cmp)) as MG3.
  lazymatch type of Q1_3 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_3 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A3 M3 _ Rc3 1 4 (kR - 3) (bR - 3 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs3 Q10_3 Q11_3 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM3) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_3
             ltac:(red; apply bv_eq; reflexivity) Q4_3 Q2_3 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A4 m4 vm4 r4 res3 HW4 Hres3 CSx3 Hnz3 Fr1_1x Lo3 F0r1_1 LEQ3 ZERO3 ALr1_1 TOP3 PMc3 RM4.
  pose proof CSx3 as CS3. clear CSx3.
  rewrite with_vmmaps_twice in HW4 |- *.
  assert (Eres3 : res3 = Z_to_bv 64 (u res3)) by (symmetry; apply zbv_self).
  pose proof (u64_range res3) as RRr1_1. set (r1_1 := u res3) in *. clearbody r1_1. rewrite Eres3 in Hres3, Fr1_1x, Lo3, F0r1_1, LEQ3, ZERO3. clear Eres3.
  change (1 * 4)%Z with 4%Z in *.
  pose proof (exW_blk_img_apart_h2 C A4 m4 _ r1_1 4 CK HW4 Lo3 RRr1_1 eq_refl eq_refl) as IMGAPr1_1. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPr1_1.
  pose proof (exW_win_blk_apart_h C A4 m4 _ s 4304 r1_1 4 CK HW4 Lo3 eq_refl RRr1_1 GLO1) as WAPr1_1.
  assert (Fr1_1 : live A0 (Z_to_bv 64 r1_1) = None).
  { destruct (live A0 (Z_to_bv 64 r1_1)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB3 _ _ EE) as XX. first [discriminate Fr1_1x | (rewrite Fr1_1x in XX; discriminate XX)]. }
  pose proof Lo3 as Lr1_1_a4.
  assert (SUB4 : sub_live A0 A4).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 r1_1) by (intros ->; rewrite Fr1_1 in Lq; discriminate Lq). rewrite (LEQ3 q NEq). exact (SUB3 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 r1_1 :: [Z_to_bv 64 r1_0; Z_to_bv 64 arr1; Z_to_bv 64 sel1])) => eq_trans (LEQ3 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL3 q (fun XX => Hq (or_intror XX)))) as LDEL4.
  assert (NE_sel1_r1_1 : Z_to_bv 64 sel1 <> Z_to_bv 64 r1_1) by (intros EE; rewrite EE in Lsel1_a3; rewrite Fr1_1x in Lsel1_a3; discriminate Lsel1_a3).
  assert (Lsel1_a4 : live A4 (Z_to_bv 64 sel1) = Some 32%Z) by (rewrite (LEQ3 _ NE_sel1_r1_1); exact Lsel1_a3).
  pose proof (exW_blk_apart_h C A4 m4 _ sel1 r1_1 32 4 CK HW4 Lsel1_a4 Lr1_1_a4 NE_sel1_r1_1 RRsel1 RRr1_1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel1_r1_1.
  assert (NE_arr1_r1_1 : Z_to_bv 64 arr1 <> Z_to_bv 64 r1_1) by (intros EE; rewrite EE in Larr1_a3; rewrite Fr1_1x in Larr1_a3; discriminate Larr1_a3).
  assert (Larr1_a4 : live A4 (Z_to_bv 64 arr1) = Some 32%Z) by (rewrite (LEQ3 _ NE_arr1_r1_1); exact Larr1_a3).
  pose proof (exW_blk_apart_h C A4 m4 _ arr1 r1_1 32 4 CK HW4 Larr1_a4 Lr1_1_a4 NE_arr1_r1_1 RRarr1 RRr1_1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr1_r1_1.
  assert (NE_r1_0_r1_1 : Z_to_bv 64 r1_0 <> Z_to_bv 64 r1_1) by (intros EE; rewrite EE in Lr1_0_a3; rewrite Fr1_1x in Lr1_0_a3; discriminate Lr1_0_a3).
  assert (Lr1_0_a4 : live A4 (Z_to_bv 64 r1_0) = Some 4%Z) by (rewrite (LEQ3 _ NE_r1_0_r1_1); exact Lr1_0_a3).
  pose proof (exW_blk_apart_h C A4 m4 _ r1_0 r1_1 4 4 CK HW4 Lr1_0_a4 Lr1_1_a4 NE_r1_0_r1_1 RRr1_0 RRr1_1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_0_r1_1.
  assert (PM4 : POSTM C A0 s m0 m4).
  { eapply POSTM_trans; [exact PM3|]. eapply POSTM_trans; [exact PMs3|]. apply (POSTM_sub C A0 A3 _ _ _ SUB3).
    apply (POSTM_mono C A3 (s + OFF3) s); [unfold OFF3; lia | exact PMc3]. }
  pose proof (cs_frame_hop C s 4304 OFF3 (-32) (-40) m0 M3 m4 CK (proj1 PMc3) ltac:(lia) ltac:(vm_cast_no_check (eq_refl true)) ltac:(vm_cast_no_check (eq_refl true)) CFs3) as CF4.
  replace (kR - 3 - 1)%Z with (kR - 4)%Z in RM4 by lia. rewrite MG3 in RM4. replace (bR - 3 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 4 * 2 ^ 17)%Z in RM4 by lia.
  assert (KEPT3 : Forall (ex_region_kept E3 M3 m4) [(EVar 32, OFF3, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 32%Z); (EVar 135, 0%Z, 4%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF3 4304 M3 m4 E3 (EVar 32) CK (proj1 PMc3) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A3 A3 M3 _ M3 m4 E3 (EVar 67) sel1 32 CK HWs3 Lsel1_a3 RRsel1 eq_refl (proj2 PMc3) Lsel1_a3 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A3 A3 M3 _ M3 m4 E3 (EVar 101) arr1 32 CK HWs3 Larr1_a3 RRarr1 eq_refl (proj2 PMc3) Larr1_a3 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A3 A3 M3 _ M3 m4 E3 (EVar 135) r1_0 4 CK HWs3 Lr1_0_a3 RRr1_0 eq_refl (proj2 PMc3) Lr1_0_a3 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E3 M3 m4 _ [] _ HKc3 KEPT3) as HKk3.
  match type of HKk3 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E3 m4 kk') in HKk3 end.
  pose proof (regs_ok_agree 137%nat E3 (ex_envL vals3 r4 [r1_1; exW_canary SEGS 1410112 m4]) _ _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa3.
  pose proof (exW_regs_call _ _ _ _ _ HRa3 (ex_regs_ok_junk vals3 r4 [r1_1; exW_canary SEGS 1410112 m4] 137%nat ltac:(vm_cast_no_check (eq_refl 137%nat))) CS3) as HRn4.
  clear HRa3.
  assert (HKa4 : know_ok SEGS (ex_envL vals3 r4 [r1_1; exW_canary SEGS 1410112 m4]) m4 _) by (exact (know_ok_agree SEGS 137%nat E3 _ m4 _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk3)).
  rewrite (fr_denot_agree 137%nat E3 (ex_envL vals3 r4 [r1_1; exW_canary SEGS 1410112 m4]) _ fr (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r4 ex_r10 (EVar 169) HRn4 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres3)) as HRx4. clear HRn4. rename HRx4 into HRn4.
  clear HR HK Hlf Hms HKc3 HKk3 KEPT3 HC3 HWs3 PMs3 Q10_3 Q11_3 Q1_3 Q2_3 Q4_3 PM3 HW3 PMc3 CS3 SUB3 RM3 MG3 TOP3 LEQ3 Hnz3 Fr1_1x Lo3 OFF3 LDEL3 CF3 CFs3 Lsel1_a3 Larr1_a3 Lr1_0_a3.
  subst M3. clear log3. clear E3. try clear Rc3. clear KN3.
  lazymatch type of HRn4 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn4 end.
  pose proof (exW_kn_blk SEGS C A4 m4 _ (ex_envL vals3 r4 [r1_1; exW_canary SEGS 1410112 m4]) (EVar 169) (EVar 32) r1_1 4 s 4304 65536 1347584 p16_segs CK HW4 Lr1_1_a4 RRr1_1 eq_refl eq_refl eq_refl RS ALr1_1 ZERO3 WAPr1_1 IMGAPr1_1) as HKb4.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals3 r4 [r1_1; exW_canary SEGS 1410112 m4]) m4) _ _ (ex_kdisj_apart SEGS (ex_envL vals3 r4 [r1_1; exW_canary SEGS 1410112 m4]) m4 (EVar 67) (EVar 169) sel1 r1_1 0 32 0 4 eq_refl eq_refl RRsel1 RRr1_1 AP_sel1_r1_1) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals3 r4 [r1_1; exW_canary SEGS 1410112 m4]) m4) _ _ (ex_kdisj_apart SEGS (ex_envL vals3 r4 [r1_1; exW_canary SEGS 1410112 m4]) m4 (EVar 101) (EVar 169) arr1 r1_1 0 32 0 4 eq_refl eq_refl RRarr1 RRr1_1 AP_arr1_r1_1) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals3 r4 [r1_1; exW_canary SEGS 1410112 m4]) m4) _ _ (ex_kdisj_apart SEGS (ex_envL vals3 r4 [r1_1; exW_canary SEGS 1410112 m4]) m4 (EVar 135) (EVar 169) r1_0 r1_1 0 4 0 4 eq_refl eq_refl RRr1_0 RRr1_1 AP_r1_0_r1_1) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals3 r4 [r1_1; exW_canary SEGS 1410112 m4]) m4))))) as HKd4.
  pose proof (W_sok_win C A4 m4 _ (s - 4304) (Z.to_nat 4304) CK HW4 GLO1 GLO2) as SOK4.
  pose proof (exW_canary_ok SEGS 1410112 m4 (canary_any m4)) as CANOK4.
  pose (vals4 := vals3 ++ map (getr r4) ex_regs_list ++ map (Z_to_bv 64) [r1_1; exW_canary SEGS 1410112 m4]).
  pose proof (exW_kn_fixed SEGS C A4 m4 _ (ex_envL vals3 r4 [r1_1; exW_canary SEGS 1410112 m4]) (EVar 170) (EVar 32) (exW_canary SEGS 1410112 m4) s 4304 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW4 eq_refl (proj1 CANOK4) (proj2 CANOK4) eq_refl eq_refl eq_refl SOK4 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf4.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb4 (proj2 (Forall_app _ _ _) (conj HKd4 (proj2 (Forall_app _ _ _) (conj HKf4 HKa4)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn4 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN4 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb4 HKd4 HKf4 HKa4 SOK4 CANOK4.
  repeat match goal with H : getr r4 _ = _ |- _ => clear H end.
  exq_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO3 ALr1_1.
  exb_exit ST Rc4 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E4 := EEx) in HR, Hlf, HK, Hms |- *; set (log4 := LLx) in Hms, Hlf; set (M4 := mem_denot E4 m4 log4) in Hms end.
  assert (WP4 : W C A4 M4 (with_vmmaps vm4 md) /\ POSTM C A0 s m4 M4).
  { subst M4. apply (exW_win_blks C A4 A0 m4 _ E4 log4 (EVar 32) s 4304 [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z); (EVar 135, r1_0, 4%Z); (EVar 169, r1_1, 4%Z)] CK HW4 SUB4 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a4 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a4 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a4 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRr1_1 (conj Lr1_1_a4 (conj Fr1_1 F0r1_1))))|]. constructor. }
  assert (CFs4 : O23LeptCselsA.cs_fra s (-32) (-40) m0 M4).
  { subst M4. apply (cs_frame_sess C A4 A0 m0 m4 _ E4 log4 (EVar 32) s 4304 (-32) (-40) [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z); (EVar 135, r1_0, 4%Z); (EVar 169, r1_1, 4%Z)] CK HW4 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exact RS | lia | exact Hhi | reflexivity | | reflexivity | exact CF4]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a4 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a4 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a4 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRr1_1 (conj Lr1_1_a4 (conj Fr1_1 F0r1_1))))|]. constructor. }
  destruct WP4 as [HWs4 PMs4].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log4 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC4 : carry log4 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc4 : know_ok SEGS E4 M4 kn1) by (apply (carry_after SEGS E4 m4 log4 kn0 [] kn1 scs hs HC4 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact Hms |].
  pose (BS4 := [(32%nat, s); (67%nat, sel1); (101%nat, arr1); (135%nat, r1_0); (169%nat, r1_1)]).
  exW_regfactB BS4 HR ex_r10 Q10_4. exW_regfactB BS4 HR ex_r11 Q11_4. exW_regfactB BS4 HR ex_r1 Q1_4. exW_regfactB BS4 HR ex_r2 Q2_4. exW_regfactB BS4 HR ex_r4 Q4_4.
  clear BS4.
  lazymatch type of Q2_4 with _ = Z_to_bv 64 (s + ?off) => pose (OFF4 := off) end.
  pose proof (alloc_margin_small (1 * 4) ltac:(exW_cmp)) as MG4.
  lazymatch type of Q1_4 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_4 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A4 M4 _ Rc4 1 4 (kR - 4) (bR - 4 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs4 Q10_4 Q11_4 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM4) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_4
             ltac:(red; apply bv_eq; reflexivity) Q4_4 Q2_4 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A5 m5 vm5 r5 res4 HW5 Hres4 CSx4 Hnz4 Fr1_2x Lo4 F0r1_2 LEQ4 ZERO4 ALr1_2 TOP4 PMc4 RM5.
  pose proof CSx4 as CS4. clear CSx4.
  rewrite with_vmmaps_twice in HW5 |- *.
  assert (Eres4 : res4 = Z_to_bv 64 (u res4)) by (symmetry; apply zbv_self).
  pose proof (u64_range res4) as RRr1_2. set (r1_2 := u res4) in *. clearbody r1_2. rewrite Eres4 in Hres4, Fr1_2x, Lo4, F0r1_2, LEQ4, ZERO4. clear Eres4.
  change (1 * 4)%Z with 4%Z in *.
  pose proof (exW_blk_img_apart_h2 C A5 m5 _ r1_2 4 CK HW5 Lo4 RRr1_2 eq_refl eq_refl) as IMGAPr1_2. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPr1_2.
  pose proof (exW_win_blk_apart_h C A5 m5 _ s 4304 r1_2 4 CK HW5 Lo4 eq_refl RRr1_2 GLO1) as WAPr1_2.
  assert (Fr1_2 : live A0 (Z_to_bv 64 r1_2) = None).
  { destruct (live A0 (Z_to_bv 64 r1_2)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB4 _ _ EE) as XX. first [discriminate Fr1_2x | (rewrite Fr1_2x in XX; discriminate XX)]. }
  pose proof Lo4 as Lr1_2_a5.
  assert (SUB5 : sub_live A0 A5).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 r1_2) by (intros ->; rewrite Fr1_2 in Lq; discriminate Lq). rewrite (LEQ4 q NEq). exact (SUB4 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 r1_2 :: [Z_to_bv 64 r1_1; Z_to_bv 64 r1_0; Z_to_bv 64 arr1; Z_to_bv 64 sel1])) => eq_trans (LEQ4 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL4 q (fun XX => Hq (or_intror XX)))) as LDEL5.
  assert (NE_sel1_r1_2 : Z_to_bv 64 sel1 <> Z_to_bv 64 r1_2) by (intros EE; rewrite EE in Lsel1_a4; rewrite Fr1_2x in Lsel1_a4; discriminate Lsel1_a4).
  assert (Lsel1_a5 : live A5 (Z_to_bv 64 sel1) = Some 32%Z) by (rewrite (LEQ4 _ NE_sel1_r1_2); exact Lsel1_a4).
  pose proof (exW_blk_apart_h C A5 m5 _ sel1 r1_2 32 4 CK HW5 Lsel1_a5 Lr1_2_a5 NE_sel1_r1_2 RRsel1 RRr1_2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel1_r1_2.
  assert (NE_arr1_r1_2 : Z_to_bv 64 arr1 <> Z_to_bv 64 r1_2) by (intros EE; rewrite EE in Larr1_a4; rewrite Fr1_2x in Larr1_a4; discriminate Larr1_a4).
  assert (Larr1_a5 : live A5 (Z_to_bv 64 arr1) = Some 32%Z) by (rewrite (LEQ4 _ NE_arr1_r1_2); exact Larr1_a4).
  pose proof (exW_blk_apart_h C A5 m5 _ arr1 r1_2 32 4 CK HW5 Larr1_a5 Lr1_2_a5 NE_arr1_r1_2 RRarr1 RRr1_2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr1_r1_2.
  assert (NE_r1_0_r1_2 : Z_to_bv 64 r1_0 <> Z_to_bv 64 r1_2) by (intros EE; rewrite EE in Lr1_0_a4; rewrite Fr1_2x in Lr1_0_a4; discriminate Lr1_0_a4).
  assert (Lr1_0_a5 : live A5 (Z_to_bv 64 r1_0) = Some 4%Z) by (rewrite (LEQ4 _ NE_r1_0_r1_2); exact Lr1_0_a4).
  pose proof (exW_blk_apart_h C A5 m5 _ r1_0 r1_2 4 4 CK HW5 Lr1_0_a5 Lr1_2_a5 NE_r1_0_r1_2 RRr1_0 RRr1_2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_0_r1_2.
  assert (NE_r1_1_r1_2 : Z_to_bv 64 r1_1 <> Z_to_bv 64 r1_2) by (intros EE; rewrite EE in Lr1_1_a4; rewrite Fr1_2x in Lr1_1_a4; discriminate Lr1_1_a4).
  assert (Lr1_1_a5 : live A5 (Z_to_bv 64 r1_1) = Some 4%Z) by (rewrite (LEQ4 _ NE_r1_1_r1_2); exact Lr1_1_a4).
  pose proof (exW_blk_apart_h C A5 m5 _ r1_1 r1_2 4 4 CK HW5 Lr1_1_a5 Lr1_2_a5 NE_r1_1_r1_2 RRr1_1 RRr1_2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_1_r1_2.
  assert (PM5 : POSTM C A0 s m0 m5).
  { eapply POSTM_trans; [exact PM4|]. eapply POSTM_trans; [exact PMs4|]. apply (POSTM_sub C A0 A4 _ _ _ SUB4).
    apply (POSTM_mono C A4 (s + OFF4) s); [unfold OFF4; lia | exact PMc4]. }
  pose proof (cs_frame_hop C s 4304 OFF4 (-32) (-40) m0 M4 m5 CK (proj1 PMc4) ltac:(lia) ltac:(vm_cast_no_check (eq_refl true)) ltac:(vm_cast_no_check (eq_refl true)) CFs4) as CF5.
  replace (kR - 4 - 1)%Z with (kR - 5)%Z in RM5 by lia. rewrite MG4 in RM5. replace (bR - 4 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 5 * 2 ^ 17)%Z in RM5 by lia.
  assert (KEPT4 : Forall (ex_region_kept E4 M4 m5) [(EVar 32, OFF4, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 32%Z); (EVar 135, 0%Z, 4%Z); (EVar 169, 0%Z, 4%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF4 4304 M4 m5 E4 (EVar 32) CK (proj1 PMc4) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 M4 _ M4 m5 E4 (EVar 67) sel1 32 CK HWs4 Lsel1_a4 RRsel1 eq_refl (proj2 PMc4) Lsel1_a4 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 M4 _ M4 m5 E4 (EVar 101) arr1 32 CK HWs4 Larr1_a4 RRarr1 eq_refl (proj2 PMc4) Larr1_a4 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 M4 _ M4 m5 E4 (EVar 135) r1_0 4 CK HWs4 Lr1_0_a4 RRr1_0 eq_refl (proj2 PMc4) Lr1_0_a4 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 M4 _ M4 m5 E4 (EVar 169) r1_1 4 CK HWs4 Lr1_1_a4 RRr1_1 eq_refl (proj2 PMc4) Lr1_1_a4 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E4 M4 m5 _ [] _ HKc4 KEPT4) as HKk4.
  match type of HKk4 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E4 m5 kk') in HKk4 end.
  pose proof (regs_ok_agree 171%nat E4 (ex_envL vals4 r5 [r1_2; exW_canary SEGS 1410112 m5]) _ _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa4.
  pose proof (exW_regs_call _ _ _ _ _ HRa4 (ex_regs_ok_junk vals4 r5 [r1_2; exW_canary SEGS 1410112 m5] 171%nat ltac:(vm_cast_no_check (eq_refl 171%nat))) CS4) as HRn5.
  clear HRa4.
  assert (HKa5 : know_ok SEGS (ex_envL vals4 r5 [r1_2; exW_canary SEGS 1410112 m5]) m5 _) by (exact (know_ok_agree SEGS 171%nat E4 _ m5 _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk4)).
  rewrite (fr_denot_agree 171%nat E4 (ex_envL vals4 r5 [r1_2; exW_canary SEGS 1410112 m5]) _ fr (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r5 ex_r10 (EVar 203) HRn5 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres4)) as HRx5. clear HRn5. rename HRx5 into HRn5.
  clear HR HK Hlf Hms HKc4 HKk4 KEPT4 HC4 HWs4 PMs4 Q10_4 Q11_4 Q1_4 Q2_4 Q4_4 PM4 HW4 PMc4 CS4 SUB4 RM4 MG4 TOP4 LEQ4 Hnz4 Fr1_2x Lo4 OFF4 LDEL4 CF4 CFs4 Lsel1_a4 Larr1_a4 Lr1_0_a4 Lr1_1_a4.
  subst M4. clear log4. clear E4. try clear Rc4. clear KN4.
  lazymatch type of HRn5 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn5 end.
  pose proof (exW_kn_blk SEGS C A5 m5 _ (ex_envL vals4 r5 [r1_2; exW_canary SEGS 1410112 m5]) (EVar 203) (EVar 32) r1_2 4 s 4304 65536 1347584 p16_segs CK HW5 Lr1_2_a5 RRr1_2 eq_refl eq_refl eq_refl RS ALr1_2 ZERO4 WAPr1_2 IMGAPr1_2) as HKb5.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [r1_2; exW_canary SEGS 1410112 m5]) m5) _ _ (ex_kdisj_apart SEGS (ex_envL vals4 r5 [r1_2; exW_canary SEGS 1410112 m5]) m5 (EVar 67) (EVar 203) sel1 r1_2 0 32 0 4 eq_refl eq_refl RRsel1 RRr1_2 AP_sel1_r1_2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [r1_2; exW_canary SEGS 1410112 m5]) m5) _ _ (ex_kdisj_apart SEGS (ex_envL vals4 r5 [r1_2; exW_canary SEGS 1410112 m5]) m5 (EVar 101) (EVar 203) arr1 r1_2 0 32 0 4 eq_refl eq_refl RRarr1 RRr1_2 AP_arr1_r1_2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [r1_2; exW_canary SEGS 1410112 m5]) m5) _ _ (ex_kdisj_apart SEGS (ex_envL vals4 r5 [r1_2; exW_canary SEGS 1410112 m5]) m5 (EVar 135) (EVar 203) r1_0 r1_2 0 4 0 4 eq_refl eq_refl RRr1_0 RRr1_2 AP_r1_0_r1_2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [r1_2; exW_canary SEGS 1410112 m5]) m5) _ _ (ex_kdisj_apart SEGS (ex_envL vals4 r5 [r1_2; exW_canary SEGS 1410112 m5]) m5 (EVar 169) (EVar 203) r1_1 r1_2 0 4 0 4 eq_refl eq_refl RRr1_1 RRr1_2 AP_r1_1_r1_2) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals4 r5 [r1_2; exW_canary SEGS 1410112 m5]) m5)))))) as HKd5.
  pose proof (W_sok_win C A5 m5 _ (s - 4304) (Z.to_nat 4304) CK HW5 GLO1 GLO2) as SOK5.
  pose proof (exW_canary_ok SEGS 1410112 m5 (canary_any m5)) as CANOK5.
  pose (vals5 := vals4 ++ map (getr r5) ex_regs_list ++ map (Z_to_bv 64) [r1_2; exW_canary SEGS 1410112 m5]).
  pose proof (exW_kn_fixed SEGS C A5 m5 _ (ex_envL vals4 r5 [r1_2; exW_canary SEGS 1410112 m5]) (EVar 204) (EVar 32) (exW_canary SEGS 1410112 m5) s 4304 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW5 eq_refl (proj1 CANOK5) (proj2 CANOK5) eq_refl eq_refl eq_refl SOK5 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf5.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb5 (proj2 (Forall_app _ _ _) (conj HKd5 (proj2 (Forall_app _ _ _) (conj HKf5 HKa5)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn5 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN5 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb5 HKd5 HKf5 HKa5 SOK5 CANOK5.
  repeat match goal with H : getr r5 _ = _ |- _ => clear H end.
  exq_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO4 ALr1_2.
  exb_exit ST Rc5 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E5 := EEx) in HR, Hlf, HK, Hms |- *; set (log5 := LLx) in Hms, Hlf; set (M5 := mem_denot E5 m5 log5) in Hms end.
  assert (WP5 : W C A5 M5 (with_vmmaps vm5 md) /\ POSTM C A0 s m5 M5).
  { subst M5. apply (exW_win_blks C A5 A0 m5 _ E5 log5 (EVar 32) s 4304 [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z); (EVar 135, r1_0, 4%Z); (EVar 169, r1_1, 4%Z); (EVar 203, r1_2, 4%Z)] CK HW5 SUB5 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a5 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a5 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a5 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRr1_1 (conj Lr1_1_a5 (conj Fr1_1 F0r1_1))))|]. constructor; [exact (conj eq_refl (conj RRr1_2 (conj Lr1_2_a5 (conj Fr1_2 F0r1_2))))|]. constructor. }
  assert (CFs5 : O23LeptCselsA.cs_fra s (-32) (-40) m0 M5).
  { subst M5. apply (cs_frame_sess C A5 A0 m0 m5 _ E5 log5 (EVar 32) s 4304 (-32) (-40) [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z); (EVar 135, r1_0, 4%Z); (EVar 169, r1_1, 4%Z); (EVar 203, r1_2, 4%Z)] CK HW5 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exact RS | lia | exact Hhi | reflexivity | | reflexivity | exact CF5]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a5 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a5 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a5 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRr1_1 (conj Lr1_1_a5 (conj Fr1_1 F0r1_1))))|]. constructor; [exact (conj eq_refl (conj RRr1_2 (conj Lr1_2_a5 (conj Fr1_2 F0r1_2))))|]. constructor. }
  destruct WP5 as [HWs5 PMs5].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log5 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC5 : carry log5 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc5 : know_ok SEGS E5 M5 kn1) by (apply (carry_after SEGS E5 m5 log5 kn0 [] kn1 scs hs HC5 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact Hms |].
  pose (BS5 := [(32%nat, s); (67%nat, sel1); (101%nat, arr1); (135%nat, r1_0); (169%nat, r1_1); (203%nat, r1_2)]).
  exW_regfactB BS5 HR ex_r10 Q10_5. exW_regfactB BS5 HR ex_r11 Q11_5. exW_regfactB BS5 HR ex_r1 Q1_5. exW_regfactB BS5 HR ex_r2 Q2_5. exW_regfactB BS5 HR ex_r4 Q4_5.
  clear BS5.
  lazymatch type of Q2_5 with _ = Z_to_bv 64 (s + ?off) => pose (OFF5 := off) end.
  pose proof (alloc_margin_small (1 * 4) ltac:(exW_cmp)) as MG5.
  lazymatch type of Q1_5 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_5 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A5 M5 _ Rc5 1 4 (kR - 5) (bR - 5 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs5 Q10_5 Q11_5 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM5) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_5
             ltac:(red; apply bv_eq; reflexivity) Q4_5 Q2_5 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A6 m6 vm6 r6 res5 HW6 Hres5 CSx5 Hnz5 Fr1_3x Lo5 F0r1_3 LEQ5 ZERO5 ALr1_3 TOP5 PMc5 RM6.
  pose proof CSx5 as CS5. clear CSx5.
  rewrite with_vmmaps_twice in HW6 |- *.
  assert (Eres5 : res5 = Z_to_bv 64 (u res5)) by (symmetry; apply zbv_self).
  pose proof (u64_range res5) as RRr1_3. set (r1_3 := u res5) in *. clearbody r1_3. rewrite Eres5 in Hres5, Fr1_3x, Lo5, F0r1_3, LEQ5, ZERO5. clear Eres5.
  change (1 * 4)%Z with 4%Z in *.
  pose proof (exW_blk_img_apart_h2 C A6 m6 _ r1_3 4 CK HW6 Lo5 RRr1_3 eq_refl eq_refl) as IMGAPr1_3. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPr1_3.
  pose proof (exW_win_blk_apart_h C A6 m6 _ s 4304 r1_3 4 CK HW6 Lo5 eq_refl RRr1_3 GLO1) as WAPr1_3.
  assert (Fr1_3 : live A0 (Z_to_bv 64 r1_3) = None).
  { destruct (live A0 (Z_to_bv 64 r1_3)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB5 _ _ EE) as XX. first [discriminate Fr1_3x | (rewrite Fr1_3x in XX; discriminate XX)]. }
  pose proof Lo5 as Lr1_3_a6.
  assert (SUB6 : sub_live A0 A6).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 r1_3) by (intros ->; rewrite Fr1_3 in Lq; discriminate Lq). rewrite (LEQ5 q NEq). exact (SUB5 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 r1_3 :: [Z_to_bv 64 r1_2; Z_to_bv 64 r1_1; Z_to_bv 64 r1_0; Z_to_bv 64 arr1; Z_to_bv 64 sel1])) => eq_trans (LEQ5 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL5 q (fun XX => Hq (or_intror XX)))) as LDEL6.
  assert (NE_sel1_r1_3 : Z_to_bv 64 sel1 <> Z_to_bv 64 r1_3) by (intros EE; rewrite EE in Lsel1_a5; rewrite Fr1_3x in Lsel1_a5; discriminate Lsel1_a5).
  assert (Lsel1_a6 : live A6 (Z_to_bv 64 sel1) = Some 32%Z) by (rewrite (LEQ5 _ NE_sel1_r1_3); exact Lsel1_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ sel1 r1_3 32 4 CK HW6 Lsel1_a6 Lr1_3_a6 NE_sel1_r1_3 RRsel1 RRr1_3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel1_r1_3.
  assert (NE_arr1_r1_3 : Z_to_bv 64 arr1 <> Z_to_bv 64 r1_3) by (intros EE; rewrite EE in Larr1_a5; rewrite Fr1_3x in Larr1_a5; discriminate Larr1_a5).
  assert (Larr1_a6 : live A6 (Z_to_bv 64 arr1) = Some 32%Z) by (rewrite (LEQ5 _ NE_arr1_r1_3); exact Larr1_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ arr1 r1_3 32 4 CK HW6 Larr1_a6 Lr1_3_a6 NE_arr1_r1_3 RRarr1 RRr1_3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr1_r1_3.
  assert (NE_r1_0_r1_3 : Z_to_bv 64 r1_0 <> Z_to_bv 64 r1_3) by (intros EE; rewrite EE in Lr1_0_a5; rewrite Fr1_3x in Lr1_0_a5; discriminate Lr1_0_a5).
  assert (Lr1_0_a6 : live A6 (Z_to_bv 64 r1_0) = Some 4%Z) by (rewrite (LEQ5 _ NE_r1_0_r1_3); exact Lr1_0_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ r1_0 r1_3 4 4 CK HW6 Lr1_0_a6 Lr1_3_a6 NE_r1_0_r1_3 RRr1_0 RRr1_3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_0_r1_3.
  assert (NE_r1_1_r1_3 : Z_to_bv 64 r1_1 <> Z_to_bv 64 r1_3) by (intros EE; rewrite EE in Lr1_1_a5; rewrite Fr1_3x in Lr1_1_a5; discriminate Lr1_1_a5).
  assert (Lr1_1_a6 : live A6 (Z_to_bv 64 r1_1) = Some 4%Z) by (rewrite (LEQ5 _ NE_r1_1_r1_3); exact Lr1_1_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ r1_1 r1_3 4 4 CK HW6 Lr1_1_a6 Lr1_3_a6 NE_r1_1_r1_3 RRr1_1 RRr1_3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_1_r1_3.
  assert (NE_r1_2_r1_3 : Z_to_bv 64 r1_2 <> Z_to_bv 64 r1_3) by (intros EE; rewrite EE in Lr1_2_a5; rewrite Fr1_3x in Lr1_2_a5; discriminate Lr1_2_a5).
  assert (Lr1_2_a6 : live A6 (Z_to_bv 64 r1_2) = Some 4%Z) by (rewrite (LEQ5 _ NE_r1_2_r1_3); exact Lr1_2_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ r1_2 r1_3 4 4 CK HW6 Lr1_2_a6 Lr1_3_a6 NE_r1_2_r1_3 RRr1_2 RRr1_3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_2_r1_3.
  assert (PM6 : POSTM C A0 s m0 m6).
  { eapply POSTM_trans; [exact PM5|]. eapply POSTM_trans; [exact PMs5|]. apply (POSTM_sub C A0 A5 _ _ _ SUB5).
    apply (POSTM_mono C A5 (s + OFF5) s); [unfold OFF5; lia | exact PMc5]. }
  pose proof (cs_frame_hop C s 4304 OFF5 (-32) (-40) m0 M5 m6 CK (proj1 PMc5) ltac:(lia) ltac:(vm_cast_no_check (eq_refl true)) ltac:(vm_cast_no_check (eq_refl true)) CFs5) as CF6.
  replace (kR - 5 - 1)%Z with (kR - 6)%Z in RM6 by lia. rewrite MG5 in RM6. replace (bR - 5 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 6 * 2 ^ 17)%Z in RM6 by lia.
  assert (KEPT5 : Forall (ex_region_kept E5 M5 m6) [(EVar 32, OFF5, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 32%Z); (EVar 135, 0%Z, 4%Z); (EVar 169, 0%Z, 4%Z); (EVar 203, 0%Z, 4%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF5 4304 M5 m6 E5 (EVar 32) CK (proj1 PMc5) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 67) sel1 32 CK HWs5 Lsel1_a5 RRsel1 eq_refl (proj2 PMc5) Lsel1_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 101) arr1 32 CK HWs5 Larr1_a5 RRarr1 eq_refl (proj2 PMc5) Larr1_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 135) r1_0 4 CK HWs5 Lr1_0_a5 RRr1_0 eq_refl (proj2 PMc5) Lr1_0_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 169) r1_1 4 CK HWs5 Lr1_1_a5 RRr1_1 eq_refl (proj2 PMc5) Lr1_1_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 203) r1_2 4 CK HWs5 Lr1_2_a5 RRr1_2 eq_refl (proj2 PMc5) Lr1_2_a5 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E5 M5 m6 _ [] _ HKc5 KEPT5) as HKk5.
  match type of HKk5 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E5 m6 kk') in HKk5 end.
  pose proof (regs_ok_agree 205%nat E5 (ex_envL vals5 r6 [r1_3; exW_canary SEGS 1410112 m6]) _ _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa5.
  pose proof (exW_regs_call _ _ _ _ _ HRa5 (ex_regs_ok_junk vals5 r6 [r1_3; exW_canary SEGS 1410112 m6] 205%nat ltac:(vm_cast_no_check (eq_refl 205%nat))) CS5) as HRn6.
  clear HRa5.
  assert (HKa6 : know_ok SEGS (ex_envL vals5 r6 [r1_3; exW_canary SEGS 1410112 m6]) m6 _) by (exact (know_ok_agree SEGS 205%nat E5 _ m6 _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk5)).
  rewrite (fr_denot_agree 205%nat E5 (ex_envL vals5 r6 [r1_3; exW_canary SEGS 1410112 m6]) _ fr (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r6 ex_r10 (EVar 237) HRn6 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres5)) as HRx6. clear HRn6. rename HRx6 into HRn6.
  clear HR HK Hlf Hms HKc5 HKk5 KEPT5 HC5 HWs5 PMs5 Q10_5 Q11_5 Q1_5 Q2_5 Q4_5 PM5 HW5 PMc5 CS5 SUB5 RM5 MG5 TOP5 LEQ5 Hnz5 Fr1_3x Lo5 OFF5 LDEL5 CF5 CFs5 Lsel1_a5 Larr1_a5 Lr1_0_a5 Lr1_1_a5 Lr1_2_a5.
  subst M5. clear log5. clear E5. try clear Rc5. clear KN5.
  lazymatch type of HRn6 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn6 end.
  pose proof (exW_kn_blk SEGS C A6 m6 _ (ex_envL vals5 r6 [r1_3; exW_canary SEGS 1410112 m6]) (EVar 237) (EVar 32) r1_3 4 s 4304 65536 1347584 p16_segs CK HW6 Lr1_3_a6 RRr1_3 eq_refl eq_refl eq_refl RS ALr1_3 ZERO5 WAPr1_3 IMGAPr1_3) as HKb6.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [r1_3; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [r1_3; exW_canary SEGS 1410112 m6]) m6 (EVar 67) (EVar 237) sel1 r1_3 0 32 0 4 eq_refl eq_refl RRsel1 RRr1_3 AP_sel1_r1_3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [r1_3; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [r1_3; exW_canary SEGS 1410112 m6]) m6 (EVar 101) (EVar 237) arr1 r1_3 0 32 0 4 eq_refl eq_refl RRarr1 RRr1_3 AP_arr1_r1_3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [r1_3; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [r1_3; exW_canary SEGS 1410112 m6]) m6 (EVar 135) (EVar 237) r1_0 r1_3 0 4 0 4 eq_refl eq_refl RRr1_0 RRr1_3 AP_r1_0_r1_3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [r1_3; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [r1_3; exW_canary SEGS 1410112 m6]) m6 (EVar 169) (EVar 237) r1_1 r1_3 0 4 0 4 eq_refl eq_refl RRr1_1 RRr1_3 AP_r1_1_r1_3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [r1_3; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [r1_3; exW_canary SEGS 1410112 m6]) m6 (EVar 203) (EVar 237) r1_2 r1_3 0 4 0 4 eq_refl eq_refl RRr1_2 RRr1_3 AP_r1_2_r1_3) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals5 r6 [r1_3; exW_canary SEGS 1410112 m6]) m6))))))) as HKd6.
  pose proof (W_sok_win C A6 m6 _ (s - 4304) (Z.to_nat 4304) CK HW6 GLO1 GLO2) as SOK6.
  pose proof (exW_canary_ok SEGS 1410112 m6 (canary_any m6)) as CANOK6.
  pose (vals6 := vals5 ++ map (getr r6) ex_regs_list ++ map (Z_to_bv 64) [r1_3; exW_canary SEGS 1410112 m6]).
  pose proof (exW_kn_fixed SEGS C A6 m6 _ (ex_envL vals5 r6 [r1_3; exW_canary SEGS 1410112 m6]) (EVar 238) (EVar 32) (exW_canary SEGS 1410112 m6) s 4304 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW6 eq_refl (proj1 CANOK6) (proj2 CANOK6) eq_refl eq_refl eq_refl SOK6 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf6.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb6 (proj2 (Forall_app _ _ _) (conj HKd6 (proj2 (Forall_app _ _ _) (conj HKf6 HKa6)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn6 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN6 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb6 HKd6 HKf6 HKa6 SOK6 CANOK6.
  repeat match goal with H : getr r6 _ = _ |- _ => clear H end.
  exq_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO5 ALr1_3.
  exb_exit ST Rc6 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E6 := EEx) in HR, Hlf, HK, Hms |- *; set (log6 := LLx) in Hms, Hlf; set (M6 := mem_denot E6 m6 log6) in Hms end.
  assert (WP6 : W C A6 M6 (with_vmmaps vm6 md) /\ POSTM C A0 s m6 M6).
  { subst M6. apply (exW_win_blks C A6 A0 m6 _ E6 log6 (EVar 32) s 4304 [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z); (EVar 135, r1_0, 4%Z); (EVar 169, r1_1, 4%Z); (EVar 203, r1_2, 4%Z); (EVar 237, r1_3, 4%Z)] CK HW6 SUB6 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a6 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a6 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a6 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRr1_1 (conj Lr1_1_a6 (conj Fr1_1 F0r1_1))))|]. constructor; [exact (conj eq_refl (conj RRr1_2 (conj Lr1_2_a6 (conj Fr1_2 F0r1_2))))|]. constructor; [exact (conj eq_refl (conj RRr1_3 (conj Lr1_3_a6 (conj Fr1_3 F0r1_3))))|]. constructor. }
  assert (CFs6 : O23LeptCselsA.cs_fra s (-32) (-40) m0 M6).
  { subst M6. apply (cs_frame_sess C A6 A0 m0 m6 _ E6 log6 (EVar 32) s 4304 (-32) (-40) [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z); (EVar 135, r1_0, 4%Z); (EVar 169, r1_1, 4%Z); (EVar 203, r1_2, 4%Z); (EVar 237, r1_3, 4%Z)] CK HW6 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exact RS | lia | exact Hhi | reflexivity | | reflexivity | exact CF6]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a6 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a6 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a6 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRr1_1 (conj Lr1_1_a6 (conj Fr1_1 F0r1_1))))|]. constructor; [exact (conj eq_refl (conj RRr1_2 (conj Lr1_2_a6 (conj Fr1_2 F0r1_2))))|]. constructor; [exact (conj eq_refl (conj RRr1_3 (conj Lr1_3_a6 (conj Fr1_3 F0r1_3))))|]. constructor. }
  destruct WP6 as [HWs6 PMs6].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log6 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC6 : carry log6 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc6 : know_ok SEGS E6 M6 kn1) by (apply (carry_after SEGS E6 m6 log6 kn0 [] kn1 scs hs HC6 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact Hms |].
  pose (BS6 := [(32%nat, s); (67%nat, sel1); (101%nat, arr1); (135%nat, r1_0); (169%nat, r1_1); (203%nat, r1_2); (237%nat, r1_3)]).
  exW_regfactB BS6 HR ex_r10 Q10_6. exW_regfactB BS6 HR ex_r11 Q11_6. exW_regfactB BS6 HR ex_r1 Q1_6. exW_regfactB BS6 HR ex_r2 Q2_6. exW_regfactB BS6 HR ex_r4 Q4_6.
  clear BS6.
  lazymatch type of Q2_6 with _ = Z_to_bv 64 (s + ?off) => pose (OFF6 := off) end.
  pose proof (alloc_margin_small (1 * 32) ltac:(exW_cmp)) as MG6.
  lazymatch type of Q1_6 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_6 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A6 M6 _ Rc6 1 32 (kR - 6) (bR - 6 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs6 Q10_6 Q11_6 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM6) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_6
             ltac:(red; apply bv_eq; reflexivity) Q4_6 Q2_6 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A7 m7 vm7 r7 res6 HW7 Hres6 CSx6 Hnz6 Fsel2x Lo6 F0sel2 LEQ6 ZERO6 ALsel2 TOP6 PMc6 RM7.
  pose proof CSx6 as CS6. clear CSx6.
  rewrite with_vmmaps_twice in HW7 |- *.
  assert (Eres6 : res6 = Z_to_bv 64 (u res6)) by (symmetry; apply zbv_self).
  pose proof (u64_range res6) as RRsel2. set (sel2 := u res6) in *. clearbody sel2. rewrite Eres6 in Hres6, Fsel2x, Lo6, F0sel2, LEQ6, ZERO6. clear Eres6.
  change (1 * 32)%Z with 32%Z in *.
  pose proof (exW_blk_img_apart_h2 C A7 m7 _ sel2 32 CK HW7 Lo6 RRsel2 eq_refl eq_refl) as IMGAPsel2. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPsel2.
  pose proof (exW_win_blk_apart_h C A7 m7 _ s 4304 sel2 32 CK HW7 Lo6 eq_refl RRsel2 GLO1) as WAPsel2.
  assert (Fsel2 : live A0 (Z_to_bv 64 sel2) = None).
  { destruct (live A0 (Z_to_bv 64 sel2)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB6 _ _ EE) as XX. first [discriminate Fsel2x | (rewrite Fsel2x in XX; discriminate XX)]. }
  pose proof Lo6 as Lsel2_a7.
  assert (SUB7 : sub_live A0 A7).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 sel2) by (intros ->; rewrite Fsel2 in Lq; discriminate Lq). rewrite (LEQ6 q NEq). exact (SUB6 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 sel2 :: [Z_to_bv 64 r1_3; Z_to_bv 64 r1_2; Z_to_bv 64 r1_1; Z_to_bv 64 r1_0; Z_to_bv 64 arr1; Z_to_bv 64 sel1])) => eq_trans (LEQ6 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL6 q (fun XX => Hq (or_intror XX)))) as LDEL7.
  assert (NE_sel1_sel2 : Z_to_bv 64 sel1 <> Z_to_bv 64 sel2) by (intros EE; rewrite EE in Lsel1_a6; rewrite Fsel2x in Lsel1_a6; discriminate Lsel1_a6).
  assert (Lsel1_a7 : live A7 (Z_to_bv 64 sel1) = Some 32%Z) by (rewrite (LEQ6 _ NE_sel1_sel2); exact Lsel1_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ sel1 sel2 32 32 CK HW7 Lsel1_a7 Lsel2_a7 NE_sel1_sel2 RRsel1 RRsel2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel1_sel2.
  assert (NE_arr1_sel2 : Z_to_bv 64 arr1 <> Z_to_bv 64 sel2) by (intros EE; rewrite EE in Larr1_a6; rewrite Fsel2x in Larr1_a6; discriminate Larr1_a6).
  assert (Larr1_a7 : live A7 (Z_to_bv 64 arr1) = Some 32%Z) by (rewrite (LEQ6 _ NE_arr1_sel2); exact Larr1_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ arr1 sel2 32 32 CK HW7 Larr1_a7 Lsel2_a7 NE_arr1_sel2 RRarr1 RRsel2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr1_sel2.
  assert (NE_r1_0_sel2 : Z_to_bv 64 r1_0 <> Z_to_bv 64 sel2) by (intros EE; rewrite EE in Lr1_0_a6; rewrite Fsel2x in Lr1_0_a6; discriminate Lr1_0_a6).
  assert (Lr1_0_a7 : live A7 (Z_to_bv 64 r1_0) = Some 4%Z) by (rewrite (LEQ6 _ NE_r1_0_sel2); exact Lr1_0_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ r1_0 sel2 4 32 CK HW7 Lr1_0_a7 Lsel2_a7 NE_r1_0_sel2 RRr1_0 RRsel2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_0_sel2.
  assert (NE_r1_1_sel2 : Z_to_bv 64 r1_1 <> Z_to_bv 64 sel2) by (intros EE; rewrite EE in Lr1_1_a6; rewrite Fsel2x in Lr1_1_a6; discriminate Lr1_1_a6).
  assert (Lr1_1_a7 : live A7 (Z_to_bv 64 r1_1) = Some 4%Z) by (rewrite (LEQ6 _ NE_r1_1_sel2); exact Lr1_1_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ r1_1 sel2 4 32 CK HW7 Lr1_1_a7 Lsel2_a7 NE_r1_1_sel2 RRr1_1 RRsel2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_1_sel2.
  assert (NE_r1_2_sel2 : Z_to_bv 64 r1_2 <> Z_to_bv 64 sel2) by (intros EE; rewrite EE in Lr1_2_a6; rewrite Fsel2x in Lr1_2_a6; discriminate Lr1_2_a6).
  assert (Lr1_2_a7 : live A7 (Z_to_bv 64 r1_2) = Some 4%Z) by (rewrite (LEQ6 _ NE_r1_2_sel2); exact Lr1_2_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ r1_2 sel2 4 32 CK HW7 Lr1_2_a7 Lsel2_a7 NE_r1_2_sel2 RRr1_2 RRsel2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_2_sel2.
  assert (NE_r1_3_sel2 : Z_to_bv 64 r1_3 <> Z_to_bv 64 sel2) by (intros EE; rewrite EE in Lr1_3_a6; rewrite Fsel2x in Lr1_3_a6; discriminate Lr1_3_a6).
  assert (Lr1_3_a7 : live A7 (Z_to_bv 64 r1_3) = Some 4%Z) by (rewrite (LEQ6 _ NE_r1_3_sel2); exact Lr1_3_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ r1_3 sel2 4 32 CK HW7 Lr1_3_a7 Lsel2_a7 NE_r1_3_sel2 RRr1_3 RRsel2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_3_sel2.
  assert (PM7 : POSTM C A0 s m0 m7).
  { eapply POSTM_trans; [exact PM6|]. eapply POSTM_trans; [exact PMs6|]. apply (POSTM_sub C A0 A6 _ _ _ SUB6).
    apply (POSTM_mono C A6 (s + OFF6) s); [unfold OFF6; lia | exact PMc6]. }
  pose proof (cs_frame_hop C s 4304 OFF6 (-32) (-40) m0 M6 m7 CK (proj1 PMc6) ltac:(lia) ltac:(vm_cast_no_check (eq_refl true)) ltac:(vm_cast_no_check (eq_refl true)) CFs6) as CF7.
  replace (kR - 6 - 1)%Z with (kR - 7)%Z in RM7 by lia. rewrite MG6 in RM7. replace (bR - 6 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 7 * 2 ^ 17)%Z in RM7 by lia.
  assert (KEPT6 : Forall (ex_region_kept E6 M6 m7) [(EVar 32, OFF6, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 32%Z); (EVar 135, 0%Z, 4%Z); (EVar 169, 0%Z, 4%Z); (EVar 203, 0%Z, 4%Z); (EVar 237, 0%Z, 4%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF6 4304 M6 m7 E6 (EVar 32) CK (proj1 PMc6) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 67) sel1 32 CK HWs6 Lsel1_a6 RRsel1 eq_refl (proj2 PMc6) Lsel1_a6 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 101) arr1 32 CK HWs6 Larr1_a6 RRarr1 eq_refl (proj2 PMc6) Larr1_a6 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 135) r1_0 4 CK HWs6 Lr1_0_a6 RRr1_0 eq_refl (proj2 PMc6) Lr1_0_a6 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 169) r1_1 4 CK HWs6 Lr1_1_a6 RRr1_1 eq_refl (proj2 PMc6) Lr1_1_a6 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 203) r1_2 4 CK HWs6 Lr1_2_a6 RRr1_2 eq_refl (proj2 PMc6) Lr1_2_a6 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 237) r1_3 4 CK HWs6 Lr1_3_a6 RRr1_3 eq_refl (proj2 PMc6) Lr1_3_a6 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E6 M6 m7 _ [] _ HKc6 KEPT6) as HKk6.
  match type of HKk6 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E6 m7 kk') in HKk6 end.
  pose proof (regs_ok_agree 239%nat E6 (ex_envL vals6 r7 [sel2; exW_canary SEGS 1410112 m7]) _ _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa6.
  pose proof (exW_regs_call _ _ _ _ _ HRa6 (ex_regs_ok_junk vals6 r7 [sel2; exW_canary SEGS 1410112 m7] 239%nat ltac:(vm_cast_no_check (eq_refl 239%nat))) CS6) as HRn7.
  clear HRa6.
  assert (HKa7 : know_ok SEGS (ex_envL vals6 r7 [sel2; exW_canary SEGS 1410112 m7]) m7 _) by (exact (know_ok_agree SEGS 239%nat E6 _ m7 _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk6)).
  rewrite (fr_denot_agree 239%nat E6 (ex_envL vals6 r7 [sel2; exW_canary SEGS 1410112 m7]) _ fr (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r7 ex_r10 (EVar 271) HRn7 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres6)) as HRx7. clear HRn7. rename HRx7 into HRn7.
  clear HR HK Hlf Hms HKc6 HKk6 KEPT6 HC6 HWs6 PMs6 Q10_6 Q11_6 Q1_6 Q2_6 Q4_6 PM6 HW6 PMc6 CS6 SUB6 RM6 MG6 TOP6 LEQ6 Hnz6 Fsel2x Lo6 OFF6 LDEL6 CF6 CFs6 Lsel1_a6 Larr1_a6 Lr1_0_a6 Lr1_1_a6 Lr1_2_a6 Lr1_3_a6.
  subst M6. clear log6. clear E6. try clear Rc6. clear KN6.
  lazymatch type of HRn7 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn7 end.
  pose proof (exW_kn_blk SEGS C A7 m7 _ (ex_envL vals6 r7 [sel2; exW_canary SEGS 1410112 m7]) (EVar 271) (EVar 32) sel2 32 s 4304 65536 1347584 p16_segs CK HW7 Lsel2_a7 RRsel2 eq_refl eq_refl eq_refl RS ALsel2 ZERO6 WAPsel2 IMGAPsel2) as HKb7.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [sel2; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [sel2; exW_canary SEGS 1410112 m7]) m7 (EVar 67) (EVar 271) sel1 sel2 0 32 0 32 eq_refl eq_refl RRsel1 RRsel2 AP_sel1_sel2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [sel2; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [sel2; exW_canary SEGS 1410112 m7]) m7 (EVar 101) (EVar 271) arr1 sel2 0 32 0 32 eq_refl eq_refl RRarr1 RRsel2 AP_arr1_sel2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [sel2; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [sel2; exW_canary SEGS 1410112 m7]) m7 (EVar 135) (EVar 271) r1_0 sel2 0 4 0 32 eq_refl eq_refl RRr1_0 RRsel2 AP_r1_0_sel2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [sel2; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [sel2; exW_canary SEGS 1410112 m7]) m7 (EVar 169) (EVar 271) r1_1 sel2 0 4 0 32 eq_refl eq_refl RRr1_1 RRsel2 AP_r1_1_sel2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [sel2; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [sel2; exW_canary SEGS 1410112 m7]) m7 (EVar 203) (EVar 271) r1_2 sel2 0 4 0 32 eq_refl eq_refl RRr1_2 RRsel2 AP_r1_2_sel2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [sel2; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [sel2; exW_canary SEGS 1410112 m7]) m7 (EVar 237) (EVar 271) r1_3 sel2 0 4 0 32 eq_refl eq_refl RRr1_3 RRsel2 AP_r1_3_sel2) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals6 r7 [sel2; exW_canary SEGS 1410112 m7]) m7)))))))) as HKd7.
  pose proof (W_sok_win C A7 m7 _ (s - 4304) (Z.to_nat 4304) CK HW7 GLO1 GLO2) as SOK7.
  pose proof (exW_canary_ok SEGS 1410112 m7 (canary_any m7)) as CANOK7.
  pose (vals7 := vals6 ++ map (getr r7) ex_regs_list ++ map (Z_to_bv 64) [sel2; exW_canary SEGS 1410112 m7]).
  pose proof (exW_kn_fixed SEGS C A7 m7 _ (ex_envL vals6 r7 [sel2; exW_canary SEGS 1410112 m7]) (EVar 272) (EVar 32) (exW_canary SEGS 1410112 m7) s 4304 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW7 eq_refl (proj1 CANOK7) (proj2 CANOK7) eq_refl eq_refl eq_refl SOK7 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf7.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb7 (proj2 (Forall_app _ _ _) (conj HKd7 (proj2 (Forall_app _ _ _) (conj HKf7 HKa7)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn7 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN7 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb7 HKd7 HKf7 HKa7 SOK7 CANOK7.
  repeat match goal with H : getr r7 _ = _ |- _ => clear H end.
  exq_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO6 ALsel2.
  exb_exit ST Rc7 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E7 := EEx) in HR, Hlf, HK, Hms |- *; set (log7 := LLx) in Hms, Hlf; set (M7 := mem_denot E7 m7 log7) in Hms end.
  assert (WP7 : W C A7 M7 (with_vmmaps vm7 md) /\ POSTM C A0 s m7 M7).
  { subst M7. apply (exW_win_blks C A7 A0 m7 _ E7 log7 (EVar 32) s 4304 [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z); (EVar 135, r1_0, 4%Z); (EVar 169, r1_1, 4%Z); (EVar 203, r1_2, 4%Z); (EVar 237, r1_3, 4%Z); (EVar 271, sel2, 32%Z)] CK HW7 SUB7 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a7 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a7 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a7 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRr1_1 (conj Lr1_1_a7 (conj Fr1_1 F0r1_1))))|]. constructor; [exact (conj eq_refl (conj RRr1_2 (conj Lr1_2_a7 (conj Fr1_2 F0r1_2))))|]. constructor; [exact (conj eq_refl (conj RRr1_3 (conj Lr1_3_a7 (conj Fr1_3 F0r1_3))))|]. constructor; [exact (conj eq_refl (conj RRsel2 (conj Lsel2_a7 (conj Fsel2 F0sel2))))|]. constructor. }
  assert (CFs7 : O23LeptCselsA.cs_fra s (-32) (-40) m0 M7).
  { subst M7. apply (cs_frame_sess C A7 A0 m0 m7 _ E7 log7 (EVar 32) s 4304 (-32) (-40) [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z); (EVar 135, r1_0, 4%Z); (EVar 169, r1_1, 4%Z); (EVar 203, r1_2, 4%Z); (EVar 237, r1_3, 4%Z); (EVar 271, sel2, 32%Z)] CK HW7 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exact RS | lia | exact Hhi | reflexivity | | reflexivity | exact CF7]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a7 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a7 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a7 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRr1_1 (conj Lr1_1_a7 (conj Fr1_1 F0r1_1))))|]. constructor; [exact (conj eq_refl (conj RRr1_2 (conj Lr1_2_a7 (conj Fr1_2 F0r1_2))))|]. constructor; [exact (conj eq_refl (conj RRr1_3 (conj Lr1_3_a7 (conj Fr1_3 F0r1_3))))|]. constructor; [exact (conj eq_refl (conj RRsel2 (conj Lsel2_a7 (conj Fsel2 F0sel2))))|]. constructor. }
  destruct WP7 as [HWs7 PMs7].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log7 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC7 : carry log7 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc7 : know_ok SEGS E7 M7 kn1) by (apply (carry_after SEGS E7 m7 log7 kn0 [] kn1 scs hs HC7 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact Hms |].
  pose (BS7 := [(32%nat, s); (67%nat, sel1); (101%nat, arr1); (135%nat, r1_0); (169%nat, r1_1); (203%nat, r1_2); (237%nat, r1_3); (271%nat, sel2)]).
  exW_regfactB BS7 HR ex_r10 Q10_7. exW_regfactB BS7 HR ex_r11 Q11_7. exW_regfactB BS7 HR ex_r1 Q1_7. exW_regfactB BS7 HR ex_r2 Q2_7. exW_regfactB BS7 HR ex_r4 Q4_7.
  clear BS7.
  lazymatch type of Q2_7 with _ = Z_to_bv 64 (s + ?off) => pose (OFF7 := off) end.
  pose proof (alloc_margin_small (8 * 8) ltac:(exW_cmp)) as MG7.
  lazymatch type of Q1_7 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_7 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A7 M7 _ Rc7 8 8 (kR - 7) (bR - 7 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs7 Q10_7 Q11_7 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM7) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_7
             ltac:(red; apply bv_eq; reflexivity) Q4_7 Q2_7 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A8 m8 vm8 r8 res7 HW8 Hres7 CSx7 Hnz7 Farr2x Lo7 F0arr2 LEQ7 ZERO7 ALarr2 TOP7 PMc7 RM8.
  pose proof CSx7 as CS7. clear CSx7.
  rewrite with_vmmaps_twice in HW8 |- *.
  assert (Eres7 : res7 = Z_to_bv 64 (u res7)) by (symmetry; apply zbv_self).
  pose proof (u64_range res7) as RRarr2. set (arr2 := u res7) in *. clearbody arr2. rewrite Eres7 in Hres7, Farr2x, Lo7, F0arr2, LEQ7, ZERO7. clear Eres7.
  change (8 * 8)%Z with 64%Z in *.
  pose proof (exW_blk_img_apart_h2 C A8 m8 _ arr2 64 CK HW8 Lo7 RRarr2 eq_refl eq_refl) as IMGAParr2. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAParr2.
  pose proof (exW_win_blk_apart_h C A8 m8 _ s 4304 arr2 64 CK HW8 Lo7 eq_refl RRarr2 GLO1) as WAParr2.
  assert (Farr2 : live A0 (Z_to_bv 64 arr2) = None).
  { destruct (live A0 (Z_to_bv 64 arr2)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB7 _ _ EE) as XX. first [discriminate Farr2x | (rewrite Farr2x in XX; discriminate XX)]. }
  pose proof Lo7 as Larr2_a8.
  assert (SUB8 : sub_live A0 A8).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 arr2) by (intros ->; rewrite Farr2 in Lq; discriminate Lq). rewrite (LEQ7 q NEq). exact (SUB7 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 arr2 :: [Z_to_bv 64 sel2; Z_to_bv 64 r1_3; Z_to_bv 64 r1_2; Z_to_bv 64 r1_1; Z_to_bv 64 r1_0; Z_to_bv 64 arr1; Z_to_bv 64 sel1])) => eq_trans (LEQ7 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL7 q (fun XX => Hq (or_intror XX)))) as LDEL8.
  assert (NE_sel1_arr2 : Z_to_bv 64 sel1 <> Z_to_bv 64 arr2) by (intros EE; rewrite EE in Lsel1_a7; rewrite Farr2x in Lsel1_a7; discriminate Lsel1_a7).
  assert (Lsel1_a8 : live A8 (Z_to_bv 64 sel1) = Some 32%Z) by (rewrite (LEQ7 _ NE_sel1_arr2); exact Lsel1_a7).
  pose proof (exW_blk_apart_h C A8 m8 _ sel1 arr2 32 64 CK HW8 Lsel1_a8 Larr2_a8 NE_sel1_arr2 RRsel1 RRarr2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel1_arr2.
  assert (NE_arr1_arr2 : Z_to_bv 64 arr1 <> Z_to_bv 64 arr2) by (intros EE; rewrite EE in Larr1_a7; rewrite Farr2x in Larr1_a7; discriminate Larr1_a7).
  assert (Larr1_a8 : live A8 (Z_to_bv 64 arr1) = Some 32%Z) by (rewrite (LEQ7 _ NE_arr1_arr2); exact Larr1_a7).
  pose proof (exW_blk_apart_h C A8 m8 _ arr1 arr2 32 64 CK HW8 Larr1_a8 Larr2_a8 NE_arr1_arr2 RRarr1 RRarr2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr1_arr2.
  assert (NE_r1_0_arr2 : Z_to_bv 64 r1_0 <> Z_to_bv 64 arr2) by (intros EE; rewrite EE in Lr1_0_a7; rewrite Farr2x in Lr1_0_a7; discriminate Lr1_0_a7).
  assert (Lr1_0_a8 : live A8 (Z_to_bv 64 r1_0) = Some 4%Z) by (rewrite (LEQ7 _ NE_r1_0_arr2); exact Lr1_0_a7).
  pose proof (exW_blk_apart_h C A8 m8 _ r1_0 arr2 4 64 CK HW8 Lr1_0_a8 Larr2_a8 NE_r1_0_arr2 RRr1_0 RRarr2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_0_arr2.
  assert (NE_r1_1_arr2 : Z_to_bv 64 r1_1 <> Z_to_bv 64 arr2) by (intros EE; rewrite EE in Lr1_1_a7; rewrite Farr2x in Lr1_1_a7; discriminate Lr1_1_a7).
  assert (Lr1_1_a8 : live A8 (Z_to_bv 64 r1_1) = Some 4%Z) by (rewrite (LEQ7 _ NE_r1_1_arr2); exact Lr1_1_a7).
  pose proof (exW_blk_apart_h C A8 m8 _ r1_1 arr2 4 64 CK HW8 Lr1_1_a8 Larr2_a8 NE_r1_1_arr2 RRr1_1 RRarr2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_1_arr2.
  assert (NE_r1_2_arr2 : Z_to_bv 64 r1_2 <> Z_to_bv 64 arr2) by (intros EE; rewrite EE in Lr1_2_a7; rewrite Farr2x in Lr1_2_a7; discriminate Lr1_2_a7).
  assert (Lr1_2_a8 : live A8 (Z_to_bv 64 r1_2) = Some 4%Z) by (rewrite (LEQ7 _ NE_r1_2_arr2); exact Lr1_2_a7).
  pose proof (exW_blk_apart_h C A8 m8 _ r1_2 arr2 4 64 CK HW8 Lr1_2_a8 Larr2_a8 NE_r1_2_arr2 RRr1_2 RRarr2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_2_arr2.
  assert (NE_r1_3_arr2 : Z_to_bv 64 r1_3 <> Z_to_bv 64 arr2) by (intros EE; rewrite EE in Lr1_3_a7; rewrite Farr2x in Lr1_3_a7; discriminate Lr1_3_a7).
  assert (Lr1_3_a8 : live A8 (Z_to_bv 64 r1_3) = Some 4%Z) by (rewrite (LEQ7 _ NE_r1_3_arr2); exact Lr1_3_a7).
  pose proof (exW_blk_apart_h C A8 m8 _ r1_3 arr2 4 64 CK HW8 Lr1_3_a8 Larr2_a8 NE_r1_3_arr2 RRr1_3 RRarr2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_3_arr2.
  assert (NE_sel2_arr2 : Z_to_bv 64 sel2 <> Z_to_bv 64 arr2) by (intros EE; rewrite EE in Lsel2_a7; rewrite Farr2x in Lsel2_a7; discriminate Lsel2_a7).
  assert (Lsel2_a8 : live A8 (Z_to_bv 64 sel2) = Some 32%Z) by (rewrite (LEQ7 _ NE_sel2_arr2); exact Lsel2_a7).
  pose proof (exW_blk_apart_h C A8 m8 _ sel2 arr2 32 64 CK HW8 Lsel2_a8 Larr2_a8 NE_sel2_arr2 RRsel2 RRarr2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel2_arr2.
  assert (PM8 : POSTM C A0 s m0 m8).
  { eapply POSTM_trans; [exact PM7|]. eapply POSTM_trans; [exact PMs7|]. apply (POSTM_sub C A0 A7 _ _ _ SUB7).
    apply (POSTM_mono C A7 (s + OFF7) s); [unfold OFF7; lia | exact PMc7]. }
  pose proof (cs_frame_hop C s 4304 OFF7 (-32) (-40) m0 M7 m8 CK (proj1 PMc7) ltac:(lia) ltac:(vm_cast_no_check (eq_refl true)) ltac:(vm_cast_no_check (eq_refl true)) CFs7) as CF8.
  replace (kR - 7 - 1)%Z with (kR - 8)%Z in RM8 by lia. rewrite MG7 in RM8. replace (bR - 7 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 8 * 2 ^ 17)%Z in RM8 by lia.
  assert (KEPT7 : Forall (ex_region_kept E7 M7 m8) [(EVar 32, OFF7, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 32%Z); (EVar 135, 0%Z, 4%Z); (EVar 169, 0%Z, 4%Z); (EVar 203, 0%Z, 4%Z); (EVar 237, 0%Z, 4%Z); (EVar 271, 0%Z, 32%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF7 4304 M7 m8 E7 (EVar 32) CK (proj1 PMc7) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A7 A7 M7 _ M7 m8 E7 (EVar 67) sel1 32 CK HWs7 Lsel1_a7 RRsel1 eq_refl (proj2 PMc7) Lsel1_a7 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A7 A7 M7 _ M7 m8 E7 (EVar 101) arr1 32 CK HWs7 Larr1_a7 RRarr1 eq_refl (proj2 PMc7) Larr1_a7 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A7 A7 M7 _ M7 m8 E7 (EVar 135) r1_0 4 CK HWs7 Lr1_0_a7 RRr1_0 eq_refl (proj2 PMc7) Lr1_0_a7 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A7 A7 M7 _ M7 m8 E7 (EVar 169) r1_1 4 CK HWs7 Lr1_1_a7 RRr1_1 eq_refl (proj2 PMc7) Lr1_1_a7 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A7 A7 M7 _ M7 m8 E7 (EVar 203) r1_2 4 CK HWs7 Lr1_2_a7 RRr1_2 eq_refl (proj2 PMc7) Lr1_2_a7 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A7 A7 M7 _ M7 m8 E7 (EVar 237) r1_3 4 CK HWs7 Lr1_3_a7 RRr1_3 eq_refl (proj2 PMc7) Lr1_3_a7 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A7 A7 M7 _ M7 m8 E7 (EVar 271) sel2 32 CK HWs7 Lsel2_a7 RRsel2 eq_refl (proj2 PMc7) Lsel2_a7 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E7 M7 m8 _ [] _ HKc7 KEPT7) as HKk7.
  match type of HKk7 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E7 m8 kk') in HKk7 end.
  pose proof (regs_ok_agree 273%nat E7 (ex_envL vals7 r8 [arr2; exW_canary SEGS 1410112 m8]) _ _ (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa7.
  pose proof (exW_regs_call _ _ _ _ _ HRa7 (ex_regs_ok_junk vals7 r8 [arr2; exW_canary SEGS 1410112 m8] 273%nat ltac:(vm_cast_no_check (eq_refl 273%nat))) CS7) as HRn8.
  clear HRa7.
  assert (HKa8 : know_ok SEGS (ex_envL vals7 r8 [arr2; exW_canary SEGS 1410112 m8]) m8 _) by (exact (know_ok_agree SEGS 273%nat E7 _ m8 _ (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk7)).
  rewrite (fr_denot_agree 273%nat E7 (ex_envL vals7 r8 [arr2; exW_canary SEGS 1410112 m8]) _ fr (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r8 ex_r10 (EVar 305) HRn8 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres7)) as HRx8. clear HRn8. rename HRx8 into HRn8.
  clear HR HK Hlf Hms HKc7 HKk7 KEPT7 HC7 HWs7 PMs7 Q10_7 Q11_7 Q1_7 Q2_7 Q4_7 PM7 HW7 PMc7 CS7 SUB7 RM7 MG7 TOP7 LEQ7 Hnz7 Farr2x Lo7 OFF7 LDEL7 CF7 CFs7 Lsel1_a7 Larr1_a7 Lr1_0_a7 Lr1_1_a7 Lr1_2_a7 Lr1_3_a7 Lsel2_a7.
  subst M7. clear log7. clear E7. try clear Rc7. clear KN7.
  lazymatch type of HRn8 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn8 end.
  pose proof (exW_kn_blk SEGS C A8 m8 _ (ex_envL vals7 r8 [arr2; exW_canary SEGS 1410112 m8]) (EVar 305) (EVar 32) arr2 64 s 4304 65536 1347584 p16_segs CK HW8 Larr2_a8 RRarr2 eq_refl eq_refl eq_refl RS ALarr2 ZERO7 WAParr2 IMGAParr2) as HKb8.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals7 r8 [arr2; exW_canary SEGS 1410112 m8]) m8) _ _ (ex_kdisj_apart SEGS (ex_envL vals7 r8 [arr2; exW_canary SEGS 1410112 m8]) m8 (EVar 67) (EVar 305) sel1 arr2 0 32 0 64 eq_refl eq_refl RRsel1 RRarr2 AP_sel1_arr2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals7 r8 [arr2; exW_canary SEGS 1410112 m8]) m8) _ _ (ex_kdisj_apart SEGS (ex_envL vals7 r8 [arr2; exW_canary SEGS 1410112 m8]) m8 (EVar 101) (EVar 305) arr1 arr2 0 32 0 64 eq_refl eq_refl RRarr1 RRarr2 AP_arr1_arr2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals7 r8 [arr2; exW_canary SEGS 1410112 m8]) m8) _ _ (ex_kdisj_apart SEGS (ex_envL vals7 r8 [arr2; exW_canary SEGS 1410112 m8]) m8 (EVar 135) (EVar 305) r1_0 arr2 0 4 0 64 eq_refl eq_refl RRr1_0 RRarr2 AP_r1_0_arr2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals7 r8 [arr2; exW_canary SEGS 1410112 m8]) m8) _ _ (ex_kdisj_apart SEGS (ex_envL vals7 r8 [arr2; exW_canary SEGS 1410112 m8]) m8 (EVar 169) (EVar 305) r1_1 arr2 0 4 0 64 eq_refl eq_refl RRr1_1 RRarr2 AP_r1_1_arr2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals7 r8 [arr2; exW_canary SEGS 1410112 m8]) m8) _ _ (ex_kdisj_apart SEGS (ex_envL vals7 r8 [arr2; exW_canary SEGS 1410112 m8]) m8 (EVar 203) (EVar 305) r1_2 arr2 0 4 0 64 eq_refl eq_refl RRr1_2 RRarr2 AP_r1_2_arr2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals7 r8 [arr2; exW_canary SEGS 1410112 m8]) m8) _ _ (ex_kdisj_apart SEGS (ex_envL vals7 r8 [arr2; exW_canary SEGS 1410112 m8]) m8 (EVar 237) (EVar 305) r1_3 arr2 0 4 0 64 eq_refl eq_refl RRr1_3 RRarr2 AP_r1_3_arr2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals7 r8 [arr2; exW_canary SEGS 1410112 m8]) m8) _ _ (ex_kdisj_apart SEGS (ex_envL vals7 r8 [arr2; exW_canary SEGS 1410112 m8]) m8 (EVar 271) (EVar 305) sel2 arr2 0 32 0 64 eq_refl eq_refl RRsel2 RRarr2 AP_sel2_arr2) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals7 r8 [arr2; exW_canary SEGS 1410112 m8]) m8))))))))) as HKd8.
  pose proof (W_sok_win C A8 m8 _ (s - 4304) (Z.to_nat 4304) CK HW8 GLO1 GLO2) as SOK8.
  pose proof (exW_canary_ok SEGS 1410112 m8 (canary_any m8)) as CANOK8.
  pose (vals8 := vals7 ++ map (getr r8) ex_regs_list ++ map (Z_to_bv 64) [arr2; exW_canary SEGS 1410112 m8]).
  pose proof (exW_kn_fixed SEGS C A8 m8 _ (ex_envL vals7 r8 [arr2; exW_canary SEGS 1410112 m8]) (EVar 306) (EVar 32) (exW_canary SEGS 1410112 m8) s 4304 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW8 eq_refl (proj1 CANOK8) (proj2 CANOK8) eq_refl eq_refl eq_refl SOK8 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf8.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb8 (proj2 (Forall_app _ _ _) (conj HKd8 (proj2 (Forall_app _ _ _) (conj HKf8 HKa8)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn8 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN8 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb8 HKd8 HKf8 HKa8 SOK8 CANOK8.
  repeat match goal with H : getr r8 _ = _ |- _ => clear H end.
  exq_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO7 ALarr2.
  exb_exit ST Rc8 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E8 := EEx) in HR, Hlf, HK, Hms |- *; set (log8 := LLx) in Hms, Hlf; set (M8 := mem_denot E8 m8 log8) in Hms end.
  assert (WP8 : W C A8 M8 (with_vmmaps vm8 md) /\ POSTM C A0 s m8 M8).
  { subst M8. apply (exW_win_blks C A8 A0 m8 _ E8 log8 (EVar 32) s 4304 [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z); (EVar 135, r1_0, 4%Z); (EVar 169, r1_1, 4%Z); (EVar 203, r1_2, 4%Z); (EVar 237, r1_3, 4%Z); (EVar 271, sel2, 32%Z); (EVar 305, arr2, 64%Z)] CK HW8 SUB8 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a8 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a8 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a8 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRr1_1 (conj Lr1_1_a8 (conj Fr1_1 F0r1_1))))|]. constructor; [exact (conj eq_refl (conj RRr1_2 (conj Lr1_2_a8 (conj Fr1_2 F0r1_2))))|]. constructor; [exact (conj eq_refl (conj RRr1_3 (conj Lr1_3_a8 (conj Fr1_3 F0r1_3))))|]. constructor; [exact (conj eq_refl (conj RRsel2 (conj Lsel2_a8 (conj Fsel2 F0sel2))))|]. constructor; [exact (conj eq_refl (conj RRarr2 (conj Larr2_a8 (conj Farr2 F0arr2))))|]. constructor. }
  assert (CFs8 : O23LeptCselsA.cs_fra s (-32) (-40) m0 M8).
  { subst M8. apply (cs_frame_sess C A8 A0 m0 m8 _ E8 log8 (EVar 32) s 4304 (-32) (-40) [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z); (EVar 135, r1_0, 4%Z); (EVar 169, r1_1, 4%Z); (EVar 203, r1_2, 4%Z); (EVar 237, r1_3, 4%Z); (EVar 271, sel2, 32%Z); (EVar 305, arr2, 64%Z)] CK HW8 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exact RS | lia | exact Hhi | reflexivity | | reflexivity | exact CF8]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a8 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a8 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a8 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRr1_1 (conj Lr1_1_a8 (conj Fr1_1 F0r1_1))))|]. constructor; [exact (conj eq_refl (conj RRr1_2 (conj Lr1_2_a8 (conj Fr1_2 F0r1_2))))|]. constructor; [exact (conj eq_refl (conj RRr1_3 (conj Lr1_3_a8 (conj Fr1_3 F0r1_3))))|]. constructor; [exact (conj eq_refl (conj RRsel2 (conj Lsel2_a8 (conj Fsel2 F0sel2))))|]. constructor; [exact (conj eq_refl (conj RRarr2 (conj Larr2_a8 (conj Farr2 F0arr2))))|]. constructor. }
  destruct WP8 as [HWs8 PMs8].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log8 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC8 : carry log8 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc8 : know_ok SEGS E8 M8 kn1) by (apply (carry_after SEGS E8 m8 log8 kn0 [] kn1 scs hs HC8 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW8)) | exact (mp_lazy _ (w_pure _ _ _ _ HW8)) | exact Hms |].
  pose (BS8 := [(32%nat, s); (67%nat, sel1); (101%nat, arr1); (135%nat, r1_0); (169%nat, r1_1); (203%nat, r1_2); (237%nat, r1_3); (271%nat, sel2); (305%nat, arr2)]).
  exW_regfactB BS8 HR ex_r10 Q10_8. exW_regfactB BS8 HR ex_r11 Q11_8. exW_regfactB BS8 HR ex_r1 Q1_8. exW_regfactB BS8 HR ex_r2 Q2_8. exW_regfactB BS8 HR ex_r4 Q4_8.
  clear BS8.
  lazymatch type of Q2_8 with _ = Z_to_bv 64 (s + ?off) => pose (OFF8 := off) end.
  pose proof (alloc_margin_small (1 * 4) ltac:(exW_cmp)) as MG8.
  lazymatch type of Q1_8 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_8 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A8 M8 _ Rc8 1 4 (kR - 8) (bR - 8 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs8 Q10_8 Q11_8 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM8) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_8
             ltac:(red; apply bv_eq; reflexivity) Q4_8 Q2_8 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A9 m9 vm9 r9 res8 HW9 Hres8 CSx8 Hnz8 Fr2_0x Lo8 F0r2_0 LEQ8 ZERO8 ALr2_0 TOP8 PMc8 RM9.
  pose proof CSx8 as CS8. clear CSx8.
  rewrite with_vmmaps_twice in HW9 |- *.
  assert (Eres8 : res8 = Z_to_bv 64 (u res8)) by (symmetry; apply zbv_self).
  pose proof (u64_range res8) as RRr2_0. set (r2_0 := u res8) in *. clearbody r2_0. rewrite Eres8 in Hres8, Fr2_0x, Lo8, F0r2_0, LEQ8, ZERO8. clear Eres8.
  change (1 * 4)%Z with 4%Z in *.
  pose proof (exW_blk_img_apart_h2 C A9 m9 _ r2_0 4 CK HW9 Lo8 RRr2_0 eq_refl eq_refl) as IMGAPr2_0. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPr2_0.
  pose proof (exW_win_blk_apart_h C A9 m9 _ s 4304 r2_0 4 CK HW9 Lo8 eq_refl RRr2_0 GLO1) as WAPr2_0.
  assert (Fr2_0 : live A0 (Z_to_bv 64 r2_0) = None).
  { destruct (live A0 (Z_to_bv 64 r2_0)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB8 _ _ EE) as XX. first [discriminate Fr2_0x | (rewrite Fr2_0x in XX; discriminate XX)]. }
  pose proof Lo8 as Lr2_0_a9.
  assert (SUB9 : sub_live A0 A9).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 r2_0) by (intros ->; rewrite Fr2_0 in Lq; discriminate Lq). rewrite (LEQ8 q NEq). exact (SUB8 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 r2_0 :: [Z_to_bv 64 arr2; Z_to_bv 64 sel2; Z_to_bv 64 r1_3; Z_to_bv 64 r1_2; Z_to_bv 64 r1_1; Z_to_bv 64 r1_0; Z_to_bv 64 arr1; Z_to_bv 64 sel1])) => eq_trans (LEQ8 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL8 q (fun XX => Hq (or_intror XX)))) as LDEL9.
  assert (NE_sel1_r2_0 : Z_to_bv 64 sel1 <> Z_to_bv 64 r2_0) by (intros EE; rewrite EE in Lsel1_a8; rewrite Fr2_0x in Lsel1_a8; discriminate Lsel1_a8).
  assert (Lsel1_a9 : live A9 (Z_to_bv 64 sel1) = Some 32%Z) by (rewrite (LEQ8 _ NE_sel1_r2_0); exact Lsel1_a8).
  pose proof (exW_blk_apart_h C A9 m9 _ sel1 r2_0 32 4 CK HW9 Lsel1_a9 Lr2_0_a9 NE_sel1_r2_0 RRsel1 RRr2_0 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel1_r2_0.
  assert (NE_arr1_r2_0 : Z_to_bv 64 arr1 <> Z_to_bv 64 r2_0) by (intros EE; rewrite EE in Larr1_a8; rewrite Fr2_0x in Larr1_a8; discriminate Larr1_a8).
  assert (Larr1_a9 : live A9 (Z_to_bv 64 arr1) = Some 32%Z) by (rewrite (LEQ8 _ NE_arr1_r2_0); exact Larr1_a8).
  pose proof (exW_blk_apart_h C A9 m9 _ arr1 r2_0 32 4 CK HW9 Larr1_a9 Lr2_0_a9 NE_arr1_r2_0 RRarr1 RRr2_0 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr1_r2_0.
  assert (NE_r1_0_r2_0 : Z_to_bv 64 r1_0 <> Z_to_bv 64 r2_0) by (intros EE; rewrite EE in Lr1_0_a8; rewrite Fr2_0x in Lr1_0_a8; discriminate Lr1_0_a8).
  assert (Lr1_0_a9 : live A9 (Z_to_bv 64 r1_0) = Some 4%Z) by (rewrite (LEQ8 _ NE_r1_0_r2_0); exact Lr1_0_a8).
  pose proof (exW_blk_apart_h C A9 m9 _ r1_0 r2_0 4 4 CK HW9 Lr1_0_a9 Lr2_0_a9 NE_r1_0_r2_0 RRr1_0 RRr2_0 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_0_r2_0.
  assert (NE_r1_1_r2_0 : Z_to_bv 64 r1_1 <> Z_to_bv 64 r2_0) by (intros EE; rewrite EE in Lr1_1_a8; rewrite Fr2_0x in Lr1_1_a8; discriminate Lr1_1_a8).
  assert (Lr1_1_a9 : live A9 (Z_to_bv 64 r1_1) = Some 4%Z) by (rewrite (LEQ8 _ NE_r1_1_r2_0); exact Lr1_1_a8).
  pose proof (exW_blk_apart_h C A9 m9 _ r1_1 r2_0 4 4 CK HW9 Lr1_1_a9 Lr2_0_a9 NE_r1_1_r2_0 RRr1_1 RRr2_0 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_1_r2_0.
  assert (NE_r1_2_r2_0 : Z_to_bv 64 r1_2 <> Z_to_bv 64 r2_0) by (intros EE; rewrite EE in Lr1_2_a8; rewrite Fr2_0x in Lr1_2_a8; discriminate Lr1_2_a8).
  assert (Lr1_2_a9 : live A9 (Z_to_bv 64 r1_2) = Some 4%Z) by (rewrite (LEQ8 _ NE_r1_2_r2_0); exact Lr1_2_a8).
  pose proof (exW_blk_apart_h C A9 m9 _ r1_2 r2_0 4 4 CK HW9 Lr1_2_a9 Lr2_0_a9 NE_r1_2_r2_0 RRr1_2 RRr2_0 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_2_r2_0.
  assert (NE_r1_3_r2_0 : Z_to_bv 64 r1_3 <> Z_to_bv 64 r2_0) by (intros EE; rewrite EE in Lr1_3_a8; rewrite Fr2_0x in Lr1_3_a8; discriminate Lr1_3_a8).
  assert (Lr1_3_a9 : live A9 (Z_to_bv 64 r1_3) = Some 4%Z) by (rewrite (LEQ8 _ NE_r1_3_r2_0); exact Lr1_3_a8).
  pose proof (exW_blk_apart_h C A9 m9 _ r1_3 r2_0 4 4 CK HW9 Lr1_3_a9 Lr2_0_a9 NE_r1_3_r2_0 RRr1_3 RRr2_0 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_3_r2_0.
  assert (NE_sel2_r2_0 : Z_to_bv 64 sel2 <> Z_to_bv 64 r2_0) by (intros EE; rewrite EE in Lsel2_a8; rewrite Fr2_0x in Lsel2_a8; discriminate Lsel2_a8).
  assert (Lsel2_a9 : live A9 (Z_to_bv 64 sel2) = Some 32%Z) by (rewrite (LEQ8 _ NE_sel2_r2_0); exact Lsel2_a8).
  pose proof (exW_blk_apart_h C A9 m9 _ sel2 r2_0 32 4 CK HW9 Lsel2_a9 Lr2_0_a9 NE_sel2_r2_0 RRsel2 RRr2_0 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel2_r2_0.
  assert (NE_arr2_r2_0 : Z_to_bv 64 arr2 <> Z_to_bv 64 r2_0) by (intros EE; rewrite EE in Larr2_a8; rewrite Fr2_0x in Larr2_a8; discriminate Larr2_a8).
  assert (Larr2_a9 : live A9 (Z_to_bv 64 arr2) = Some 64%Z) by (rewrite (LEQ8 _ NE_arr2_r2_0); exact Larr2_a8).
  pose proof (exW_blk_apart_h C A9 m9 _ arr2 r2_0 64 4 CK HW9 Larr2_a9 Lr2_0_a9 NE_arr2_r2_0 RRarr2 RRr2_0 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr2_r2_0.
  assert (PM9 : POSTM C A0 s m0 m9).
  { eapply POSTM_trans; [exact PM8|]. eapply POSTM_trans; [exact PMs8|]. apply (POSTM_sub C A0 A8 _ _ _ SUB8).
    apply (POSTM_mono C A8 (s + OFF8) s); [unfold OFF8; lia | exact PMc8]. }
  pose proof (cs_frame_hop C s 4304 OFF8 (-32) (-40) m0 M8 m9 CK (proj1 PMc8) ltac:(lia) ltac:(vm_cast_no_check (eq_refl true)) ltac:(vm_cast_no_check (eq_refl true)) CFs8) as CF9.
  replace (kR - 8 - 1)%Z with (kR - 9)%Z in RM9 by lia. rewrite MG8 in RM9. replace (bR - 8 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 9 * 2 ^ 17)%Z in RM9 by lia.
  assert (KEPT8 : Forall (ex_region_kept E8 M8 m9) [(EVar 32, OFF8, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 32%Z); (EVar 135, 0%Z, 4%Z); (EVar 169, 0%Z, 4%Z); (EVar 203, 0%Z, 4%Z); (EVar 237, 0%Z, 4%Z); (EVar 271, 0%Z, 32%Z); (EVar 305, 0%Z, 64%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF8 4304 M8 m9 E8 (EVar 32) CK (proj1 PMc8) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A8 A8 M8 _ M8 m9 E8 (EVar 67) sel1 32 CK HWs8 Lsel1_a8 RRsel1 eq_refl (proj2 PMc8) Lsel1_a8 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A8 A8 M8 _ M8 m9 E8 (EVar 101) arr1 32 CK HWs8 Larr1_a8 RRarr1 eq_refl (proj2 PMc8) Larr1_a8 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A8 A8 M8 _ M8 m9 E8 (EVar 135) r1_0 4 CK HWs8 Lr1_0_a8 RRr1_0 eq_refl (proj2 PMc8) Lr1_0_a8 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A8 A8 M8 _ M8 m9 E8 (EVar 169) r1_1 4 CK HWs8 Lr1_1_a8 RRr1_1 eq_refl (proj2 PMc8) Lr1_1_a8 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A8 A8 M8 _ M8 m9 E8 (EVar 203) r1_2 4 CK HWs8 Lr1_2_a8 RRr1_2 eq_refl (proj2 PMc8) Lr1_2_a8 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A8 A8 M8 _ M8 m9 E8 (EVar 237) r1_3 4 CK HWs8 Lr1_3_a8 RRr1_3 eq_refl (proj2 PMc8) Lr1_3_a8 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A8 A8 M8 _ M8 m9 E8 (EVar 271) sel2 32 CK HWs8 Lsel2_a8 RRsel2 eq_refl (proj2 PMc8) Lsel2_a8 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A8 A8 M8 _ M8 m9 E8 (EVar 305) arr2 64 CK HWs8 Larr2_a8 RRarr2 eq_refl (proj2 PMc8) Larr2_a8 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E8 M8 m9 _ [] _ HKc8 KEPT8) as HKk8.
  match type of HKk8 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E8 m9 kk') in HKk8 end.
  pose proof (regs_ok_agree 307%nat E8 (ex_envL vals8 r9 [r2_0; exW_canary SEGS 1410112 m9]) _ _ (vals_app_agree vals8 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa8.
  pose proof (exW_regs_call _ _ _ _ _ HRa8 (ex_regs_ok_junk vals8 r9 [r2_0; exW_canary SEGS 1410112 m9] 307%nat ltac:(vm_cast_no_check (eq_refl 307%nat))) CS8) as HRn9.
  clear HRa8.
  assert (HKa9 : know_ok SEGS (ex_envL vals8 r9 [r2_0; exW_canary SEGS 1410112 m9]) m9 _) by (exact (know_ok_agree SEGS 307%nat E8 _ m9 _ (vals_app_agree vals8 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk8)).
  rewrite (fr_denot_agree 307%nat E8 (ex_envL vals8 r9 [r2_0; exW_canary SEGS 1410112 m9]) _ fr (vals_app_agree vals8 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r9 ex_r10 (EVar 339) HRn9 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres8)) as HRx9. clear HRn9. rename HRx9 into HRn9.
  clear HR HK Hlf Hms HKc8 HKk8 KEPT8 HC8 HWs8 PMs8 Q10_8 Q11_8 Q1_8 Q2_8 Q4_8 PM8 HW8 PMc8 CS8 SUB8 RM8 MG8 TOP8 LEQ8 Hnz8 Fr2_0x Lo8 OFF8 LDEL8 CF8 CFs8 Lsel1_a8 Larr1_a8 Lr1_0_a8 Lr1_1_a8 Lr1_2_a8 Lr1_3_a8 Lsel2_a8 Larr2_a8.
  subst M8. clear log8. clear E8. try clear Rc8. clear KN8.
  lazymatch type of HRn9 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn9 end.
  pose proof (exW_kn_blk SEGS C A9 m9 _ (ex_envL vals8 r9 [r2_0; exW_canary SEGS 1410112 m9]) (EVar 339) (EVar 32) r2_0 4 s 4304 65536 1347584 p16_segs CK HW9 Lr2_0_a9 RRr2_0 eq_refl eq_refl eq_refl RS ALr2_0 ZERO8 WAPr2_0 IMGAPr2_0) as HKb9.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals8 r9 [r2_0; exW_canary SEGS 1410112 m9]) m9) _ _ (ex_kdisj_apart SEGS (ex_envL vals8 r9 [r2_0; exW_canary SEGS 1410112 m9]) m9 (EVar 67) (EVar 339) sel1 r2_0 0 32 0 4 eq_refl eq_refl RRsel1 RRr2_0 AP_sel1_r2_0) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals8 r9 [r2_0; exW_canary SEGS 1410112 m9]) m9) _ _ (ex_kdisj_apart SEGS (ex_envL vals8 r9 [r2_0; exW_canary SEGS 1410112 m9]) m9 (EVar 101) (EVar 339) arr1 r2_0 0 32 0 4 eq_refl eq_refl RRarr1 RRr2_0 AP_arr1_r2_0) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals8 r9 [r2_0; exW_canary SEGS 1410112 m9]) m9) _ _ (ex_kdisj_apart SEGS (ex_envL vals8 r9 [r2_0; exW_canary SEGS 1410112 m9]) m9 (EVar 135) (EVar 339) r1_0 r2_0 0 4 0 4 eq_refl eq_refl RRr1_0 RRr2_0 AP_r1_0_r2_0) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals8 r9 [r2_0; exW_canary SEGS 1410112 m9]) m9) _ _ (ex_kdisj_apart SEGS (ex_envL vals8 r9 [r2_0; exW_canary SEGS 1410112 m9]) m9 (EVar 169) (EVar 339) r1_1 r2_0 0 4 0 4 eq_refl eq_refl RRr1_1 RRr2_0 AP_r1_1_r2_0) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals8 r9 [r2_0; exW_canary SEGS 1410112 m9]) m9) _ _ (ex_kdisj_apart SEGS (ex_envL vals8 r9 [r2_0; exW_canary SEGS 1410112 m9]) m9 (EVar 203) (EVar 339) r1_2 r2_0 0 4 0 4 eq_refl eq_refl RRr1_2 RRr2_0 AP_r1_2_r2_0) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals8 r9 [r2_0; exW_canary SEGS 1410112 m9]) m9) _ _ (ex_kdisj_apart SEGS (ex_envL vals8 r9 [r2_0; exW_canary SEGS 1410112 m9]) m9 (EVar 237) (EVar 339) r1_3 r2_0 0 4 0 4 eq_refl eq_refl RRr1_3 RRr2_0 AP_r1_3_r2_0) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals8 r9 [r2_0; exW_canary SEGS 1410112 m9]) m9) _ _ (ex_kdisj_apart SEGS (ex_envL vals8 r9 [r2_0; exW_canary SEGS 1410112 m9]) m9 (EVar 271) (EVar 339) sel2 r2_0 0 32 0 4 eq_refl eq_refl RRsel2 RRr2_0 AP_sel2_r2_0) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals8 r9 [r2_0; exW_canary SEGS 1410112 m9]) m9) _ _ (ex_kdisj_apart SEGS (ex_envL vals8 r9 [r2_0; exW_canary SEGS 1410112 m9]) m9 (EVar 305) (EVar 339) arr2 r2_0 0 64 0 4 eq_refl eq_refl RRarr2 RRr2_0 AP_arr2_r2_0) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals8 r9 [r2_0; exW_canary SEGS 1410112 m9]) m9)))))))))) as HKd9.
  pose proof (W_sok_win C A9 m9 _ (s - 4304) (Z.to_nat 4304) CK HW9 GLO1 GLO2) as SOK9.
  pose proof (exW_canary_ok SEGS 1410112 m9 (canary_any m9)) as CANOK9.
  pose (vals9 := vals8 ++ map (getr r9) ex_regs_list ++ map (Z_to_bv 64) [r2_0; exW_canary SEGS 1410112 m9]).
  pose proof (exW_kn_fixed SEGS C A9 m9 _ (ex_envL vals8 r9 [r2_0; exW_canary SEGS 1410112 m9]) (EVar 340) (EVar 32) (exW_canary SEGS 1410112 m9) s 4304 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW9 eq_refl (proj1 CANOK9) (proj2 CANOK9) eq_refl eq_refl eq_refl SOK9 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf9.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb9 (proj2 (Forall_app _ _ _) (conj HKd9 (proj2 (Forall_app _ _ _) (conj HKf9 HKa9)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn9 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN9 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb9 HKd9 HKf9 HKa9 SOK9 CANOK9.
  repeat match goal with H : getr r9 _ = _ |- _ => clear H end.
  exq_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO8 ALr2_0.
  exb_exit ST Rc9 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E9 := EEx) in HR, Hlf, HK, Hms |- *; set (log9 := LLx) in Hms, Hlf; set (M9 := mem_denot E9 m9 log9) in Hms end.
  assert (WP9 : W C A9 M9 (with_vmmaps vm9 md) /\ POSTM C A0 s m9 M9).
  { subst M9. apply (exW_win_blks C A9 A0 m9 _ E9 log9 (EVar 32) s 4304 [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z); (EVar 135, r1_0, 4%Z); (EVar 169, r1_1, 4%Z); (EVar 203, r1_2, 4%Z); (EVar 237, r1_3, 4%Z); (EVar 271, sel2, 32%Z); (EVar 305, arr2, 64%Z); (EVar 339, r2_0, 4%Z)] CK HW9 SUB9 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a9 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a9 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a9 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRr1_1 (conj Lr1_1_a9 (conj Fr1_1 F0r1_1))))|]. constructor; [exact (conj eq_refl (conj RRr1_2 (conj Lr1_2_a9 (conj Fr1_2 F0r1_2))))|]. constructor; [exact (conj eq_refl (conj RRr1_3 (conj Lr1_3_a9 (conj Fr1_3 F0r1_3))))|]. constructor; [exact (conj eq_refl (conj RRsel2 (conj Lsel2_a9 (conj Fsel2 F0sel2))))|]. constructor; [exact (conj eq_refl (conj RRarr2 (conj Larr2_a9 (conj Farr2 F0arr2))))|]. constructor; [exact (conj eq_refl (conj RRr2_0 (conj Lr2_0_a9 (conj Fr2_0 F0r2_0))))|]. constructor. }
  assert (CFs9 : O23LeptCselsA.cs_fra s (-32) (-40) m0 M9).
  { subst M9. apply (cs_frame_sess C A9 A0 m0 m9 _ E9 log9 (EVar 32) s 4304 (-32) (-40) [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z); (EVar 135, r1_0, 4%Z); (EVar 169, r1_1, 4%Z); (EVar 203, r1_2, 4%Z); (EVar 237, r1_3, 4%Z); (EVar 271, sel2, 32%Z); (EVar 305, arr2, 64%Z); (EVar 339, r2_0, 4%Z)] CK HW9 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exact RS | lia | exact Hhi | reflexivity | | reflexivity | exact CF9]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a9 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a9 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a9 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRr1_1 (conj Lr1_1_a9 (conj Fr1_1 F0r1_1))))|]. constructor; [exact (conj eq_refl (conj RRr1_2 (conj Lr1_2_a9 (conj Fr1_2 F0r1_2))))|]. constructor; [exact (conj eq_refl (conj RRr1_3 (conj Lr1_3_a9 (conj Fr1_3 F0r1_3))))|]. constructor; [exact (conj eq_refl (conj RRsel2 (conj Lsel2_a9 (conj Fsel2 F0sel2))))|]. constructor; [exact (conj eq_refl (conj RRarr2 (conj Larr2_a9 (conj Farr2 F0arr2))))|]. constructor; [exact (conj eq_refl (conj RRr2_0 (conj Lr2_0_a9 (conj Fr2_0 F0r2_0))))|]. constructor. }
  destruct WP9 as [HWs9 PMs9].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log9 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC9 : carry log9 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc9 : know_ok SEGS E9 M9 kn1) by (apply (carry_after SEGS E9 m9 log9 kn0 [] kn1 scs hs HC9 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW9)) | exact (mp_lazy _ (w_pure _ _ _ _ HW9)) | exact Hms |].
  pose (BS9 := [(32%nat, s); (67%nat, sel1); (101%nat, arr1); (135%nat, r1_0); (169%nat, r1_1); (203%nat, r1_2); (237%nat, r1_3); (271%nat, sel2); (305%nat, arr2); (339%nat, r2_0)]).
  exW_regfactB BS9 HR ex_r10 Q10_9. exW_regfactB BS9 HR ex_r11 Q11_9. exW_regfactB BS9 HR ex_r1 Q1_9. exW_regfactB BS9 HR ex_r2 Q2_9. exW_regfactB BS9 HR ex_r4 Q4_9.
  clear BS9.
  lazymatch type of Q2_9 with _ = Z_to_bv 64 (s + ?off) => pose (OFF9 := off) end.
  pose proof (alloc_margin_small (1 * 4) ltac:(exW_cmp)) as MG9.
  lazymatch type of Q1_9 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_9 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A9 M9 _ Rc9 1 4 (kR - 9) (bR - 9 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs9 Q10_9 Q11_9 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM9) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_9
             ltac:(red; apply bv_eq; reflexivity) Q4_9 Q2_9 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A10 m10 vm10 r10 res9 HW10 Hres9 CSx9 Hnz9 Fr2_1x Lo9 F0r2_1 LEQ9 ZERO9 ALr2_1 TOP9 PMc9 RM10.
  pose proof CSx9 as CS9. clear CSx9.
  rewrite with_vmmaps_twice in HW10 |- *.
  assert (Eres9 : res9 = Z_to_bv 64 (u res9)) by (symmetry; apply zbv_self).
  pose proof (u64_range res9) as RRr2_1. set (r2_1 := u res9) in *. clearbody r2_1. rewrite Eres9 in Hres9, Fr2_1x, Lo9, F0r2_1, LEQ9, ZERO9. clear Eres9.
  change (1 * 4)%Z with 4%Z in *.
  pose proof (exW_blk_img_apart_h2 C A10 m10 _ r2_1 4 CK HW10 Lo9 RRr2_1 eq_refl eq_refl) as IMGAPr2_1. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPr2_1.
  pose proof (exW_win_blk_apart_h C A10 m10 _ s 4304 r2_1 4 CK HW10 Lo9 eq_refl RRr2_1 GLO1) as WAPr2_1.
  assert (Fr2_1 : live A0 (Z_to_bv 64 r2_1) = None).
  { destruct (live A0 (Z_to_bv 64 r2_1)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB9 _ _ EE) as XX. first [discriminate Fr2_1x | (rewrite Fr2_1x in XX; discriminate XX)]. }
  pose proof Lo9 as Lr2_1_a10.
  assert (SUB10 : sub_live A0 A10).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 r2_1) by (intros ->; rewrite Fr2_1 in Lq; discriminate Lq). rewrite (LEQ9 q NEq). exact (SUB9 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 r2_1 :: [Z_to_bv 64 r2_0; Z_to_bv 64 arr2; Z_to_bv 64 sel2; Z_to_bv 64 r1_3; Z_to_bv 64 r1_2; Z_to_bv 64 r1_1; Z_to_bv 64 r1_0; Z_to_bv 64 arr1; Z_to_bv 64 sel1])) => eq_trans (LEQ9 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL9 q (fun XX => Hq (or_intror XX)))) as LDEL10.
  assert (NE_sel1_r2_1 : Z_to_bv 64 sel1 <> Z_to_bv 64 r2_1) by (intros EE; rewrite EE in Lsel1_a9; rewrite Fr2_1x in Lsel1_a9; discriminate Lsel1_a9).
  assert (Lsel1_a10 : live A10 (Z_to_bv 64 sel1) = Some 32%Z) by (rewrite (LEQ9 _ NE_sel1_r2_1); exact Lsel1_a9).
  pose proof (exW_blk_apart_h C A10 m10 _ sel1 r2_1 32 4 CK HW10 Lsel1_a10 Lr2_1_a10 NE_sel1_r2_1 RRsel1 RRr2_1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel1_r2_1.
  assert (NE_arr1_r2_1 : Z_to_bv 64 arr1 <> Z_to_bv 64 r2_1) by (intros EE; rewrite EE in Larr1_a9; rewrite Fr2_1x in Larr1_a9; discriminate Larr1_a9).
  assert (Larr1_a10 : live A10 (Z_to_bv 64 arr1) = Some 32%Z) by (rewrite (LEQ9 _ NE_arr1_r2_1); exact Larr1_a9).
  pose proof (exW_blk_apart_h C A10 m10 _ arr1 r2_1 32 4 CK HW10 Larr1_a10 Lr2_1_a10 NE_arr1_r2_1 RRarr1 RRr2_1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr1_r2_1.
  assert (NE_r1_0_r2_1 : Z_to_bv 64 r1_0 <> Z_to_bv 64 r2_1) by (intros EE; rewrite EE in Lr1_0_a9; rewrite Fr2_1x in Lr1_0_a9; discriminate Lr1_0_a9).
  assert (Lr1_0_a10 : live A10 (Z_to_bv 64 r1_0) = Some 4%Z) by (rewrite (LEQ9 _ NE_r1_0_r2_1); exact Lr1_0_a9).
  pose proof (exW_blk_apart_h C A10 m10 _ r1_0 r2_1 4 4 CK HW10 Lr1_0_a10 Lr2_1_a10 NE_r1_0_r2_1 RRr1_0 RRr2_1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_0_r2_1.
  assert (NE_r1_1_r2_1 : Z_to_bv 64 r1_1 <> Z_to_bv 64 r2_1) by (intros EE; rewrite EE in Lr1_1_a9; rewrite Fr2_1x in Lr1_1_a9; discriminate Lr1_1_a9).
  assert (Lr1_1_a10 : live A10 (Z_to_bv 64 r1_1) = Some 4%Z) by (rewrite (LEQ9 _ NE_r1_1_r2_1); exact Lr1_1_a9).
  pose proof (exW_blk_apart_h C A10 m10 _ r1_1 r2_1 4 4 CK HW10 Lr1_1_a10 Lr2_1_a10 NE_r1_1_r2_1 RRr1_1 RRr2_1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_1_r2_1.
  assert (NE_r1_2_r2_1 : Z_to_bv 64 r1_2 <> Z_to_bv 64 r2_1) by (intros EE; rewrite EE in Lr1_2_a9; rewrite Fr2_1x in Lr1_2_a9; discriminate Lr1_2_a9).
  assert (Lr1_2_a10 : live A10 (Z_to_bv 64 r1_2) = Some 4%Z) by (rewrite (LEQ9 _ NE_r1_2_r2_1); exact Lr1_2_a9).
  pose proof (exW_blk_apart_h C A10 m10 _ r1_2 r2_1 4 4 CK HW10 Lr1_2_a10 Lr2_1_a10 NE_r1_2_r2_1 RRr1_2 RRr2_1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_2_r2_1.
  assert (NE_r1_3_r2_1 : Z_to_bv 64 r1_3 <> Z_to_bv 64 r2_1) by (intros EE; rewrite EE in Lr1_3_a9; rewrite Fr2_1x in Lr1_3_a9; discriminate Lr1_3_a9).
  assert (Lr1_3_a10 : live A10 (Z_to_bv 64 r1_3) = Some 4%Z) by (rewrite (LEQ9 _ NE_r1_3_r2_1); exact Lr1_3_a9).
  pose proof (exW_blk_apart_h C A10 m10 _ r1_3 r2_1 4 4 CK HW10 Lr1_3_a10 Lr2_1_a10 NE_r1_3_r2_1 RRr1_3 RRr2_1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_3_r2_1.
  assert (NE_sel2_r2_1 : Z_to_bv 64 sel2 <> Z_to_bv 64 r2_1) by (intros EE; rewrite EE in Lsel2_a9; rewrite Fr2_1x in Lsel2_a9; discriminate Lsel2_a9).
  assert (Lsel2_a10 : live A10 (Z_to_bv 64 sel2) = Some 32%Z) by (rewrite (LEQ9 _ NE_sel2_r2_1); exact Lsel2_a9).
  pose proof (exW_blk_apart_h C A10 m10 _ sel2 r2_1 32 4 CK HW10 Lsel2_a10 Lr2_1_a10 NE_sel2_r2_1 RRsel2 RRr2_1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel2_r2_1.
  assert (NE_arr2_r2_1 : Z_to_bv 64 arr2 <> Z_to_bv 64 r2_1) by (intros EE; rewrite EE in Larr2_a9; rewrite Fr2_1x in Larr2_a9; discriminate Larr2_a9).
  assert (Larr2_a10 : live A10 (Z_to_bv 64 arr2) = Some 64%Z) by (rewrite (LEQ9 _ NE_arr2_r2_1); exact Larr2_a9).
  pose proof (exW_blk_apart_h C A10 m10 _ arr2 r2_1 64 4 CK HW10 Larr2_a10 Lr2_1_a10 NE_arr2_r2_1 RRarr2 RRr2_1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr2_r2_1.
  assert (NE_r2_0_r2_1 : Z_to_bv 64 r2_0 <> Z_to_bv 64 r2_1) by (intros EE; rewrite EE in Lr2_0_a9; rewrite Fr2_1x in Lr2_0_a9; discriminate Lr2_0_a9).
  assert (Lr2_0_a10 : live A10 (Z_to_bv 64 r2_0) = Some 4%Z) by (rewrite (LEQ9 _ NE_r2_0_r2_1); exact Lr2_0_a9).
  pose proof (exW_blk_apart_h C A10 m10 _ r2_0 r2_1 4 4 CK HW10 Lr2_0_a10 Lr2_1_a10 NE_r2_0_r2_1 RRr2_0 RRr2_1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r2_0_r2_1.
  assert (PM10 : POSTM C A0 s m0 m10).
  { eapply POSTM_trans; [exact PM9|]. eapply POSTM_trans; [exact PMs9|]. apply (POSTM_sub C A0 A9 _ _ _ SUB9).
    apply (POSTM_mono C A9 (s + OFF9) s); [unfold OFF9; lia | exact PMc9]. }
  pose proof (cs_frame_hop C s 4304 OFF9 (-32) (-40) m0 M9 m10 CK (proj1 PMc9) ltac:(lia) ltac:(vm_cast_no_check (eq_refl true)) ltac:(vm_cast_no_check (eq_refl true)) CFs9) as CF10.
  replace (kR - 9 - 1)%Z with (kR - 10)%Z in RM10 by lia. rewrite MG9 in RM10. replace (bR - 9 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 10 * 2 ^ 17)%Z in RM10 by lia.
  assert (KEPT9 : Forall (ex_region_kept E9 M9 m10) [(EVar 32, OFF9, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 32%Z); (EVar 135, 0%Z, 4%Z); (EVar 169, 0%Z, 4%Z); (EVar 203, 0%Z, 4%Z); (EVar 237, 0%Z, 4%Z); (EVar 271, 0%Z, 32%Z); (EVar 305, 0%Z, 64%Z); (EVar 339, 0%Z, 4%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF9 4304 M9 m10 E9 (EVar 32) CK (proj1 PMc9) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A9 A9 M9 _ M9 m10 E9 (EVar 67) sel1 32 CK HWs9 Lsel1_a9 RRsel1 eq_refl (proj2 PMc9) Lsel1_a9 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A9 A9 M9 _ M9 m10 E9 (EVar 101) arr1 32 CK HWs9 Larr1_a9 RRarr1 eq_refl (proj2 PMc9) Larr1_a9 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A9 A9 M9 _ M9 m10 E9 (EVar 135) r1_0 4 CK HWs9 Lr1_0_a9 RRr1_0 eq_refl (proj2 PMc9) Lr1_0_a9 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A9 A9 M9 _ M9 m10 E9 (EVar 169) r1_1 4 CK HWs9 Lr1_1_a9 RRr1_1 eq_refl (proj2 PMc9) Lr1_1_a9 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A9 A9 M9 _ M9 m10 E9 (EVar 203) r1_2 4 CK HWs9 Lr1_2_a9 RRr1_2 eq_refl (proj2 PMc9) Lr1_2_a9 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A9 A9 M9 _ M9 m10 E9 (EVar 237) r1_3 4 CK HWs9 Lr1_3_a9 RRr1_3 eq_refl (proj2 PMc9) Lr1_3_a9 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A9 A9 M9 _ M9 m10 E9 (EVar 271) sel2 32 CK HWs9 Lsel2_a9 RRsel2 eq_refl (proj2 PMc9) Lsel2_a9 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A9 A9 M9 _ M9 m10 E9 (EVar 305) arr2 64 CK HWs9 Larr2_a9 RRarr2 eq_refl (proj2 PMc9) Larr2_a9 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A9 A9 M9 _ M9 m10 E9 (EVar 339) r2_0 4 CK HWs9 Lr2_0_a9 RRr2_0 eq_refl (proj2 PMc9) Lr2_0_a9 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E9 M9 m10 _ [] _ HKc9 KEPT9) as HKk9.
  match type of HKk9 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E9 m10 kk') in HKk9 end.
  pose proof (regs_ok_agree 341%nat E9 (ex_envL vals9 r10 [r2_1; exW_canary SEGS 1410112 m10]) _ _ (vals_app_agree vals9 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa9.
  pose proof (exW_regs_call _ _ _ _ _ HRa9 (ex_regs_ok_junk vals9 r10 [r2_1; exW_canary SEGS 1410112 m10] 341%nat ltac:(vm_cast_no_check (eq_refl 341%nat))) CS9) as HRn10.
  clear HRa9.
  assert (HKa10 : know_ok SEGS (ex_envL vals9 r10 [r2_1; exW_canary SEGS 1410112 m10]) m10 _) by (exact (know_ok_agree SEGS 341%nat E9 _ m10 _ (vals_app_agree vals9 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk9)).
  rewrite (fr_denot_agree 341%nat E9 (ex_envL vals9 r10 [r2_1; exW_canary SEGS 1410112 m10]) _ fr (vals_app_agree vals9 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r10 ex_r10 (EVar 373) HRn10 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres9)) as HRx10. clear HRn10. rename HRx10 into HRn10.
  clear HR HK Hlf Hms HKc9 HKk9 KEPT9 HC9 HWs9 PMs9 Q10_9 Q11_9 Q1_9 Q2_9 Q4_9 PM9 HW9 PMc9 CS9 SUB9 RM9 MG9 TOP9 LEQ9 Hnz9 Fr2_1x Lo9 OFF9 LDEL9 CF9 CFs9 Lsel1_a9 Larr1_a9 Lr1_0_a9 Lr1_1_a9 Lr1_2_a9 Lr1_3_a9 Lsel2_a9 Larr2_a9 Lr2_0_a9.
  subst M9. clear log9. clear E9. try clear Rc9. clear KN9.
  lazymatch type of HRn10 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn10 end.
  pose proof (exW_kn_blk SEGS C A10 m10 _ (ex_envL vals9 r10 [r2_1; exW_canary SEGS 1410112 m10]) (EVar 373) (EVar 32) r2_1 4 s 4304 65536 1347584 p16_segs CK HW10 Lr2_1_a10 RRr2_1 eq_refl eq_refl eq_refl RS ALr2_1 ZERO9 WAPr2_1 IMGAPr2_1) as HKb10.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals9 r10 [r2_1; exW_canary SEGS 1410112 m10]) m10) _ _ (ex_kdisj_apart SEGS (ex_envL vals9 r10 [r2_1; exW_canary SEGS 1410112 m10]) m10 (EVar 67) (EVar 373) sel1 r2_1 0 32 0 4 eq_refl eq_refl RRsel1 RRr2_1 AP_sel1_r2_1) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals9 r10 [r2_1; exW_canary SEGS 1410112 m10]) m10) _ _ (ex_kdisj_apart SEGS (ex_envL vals9 r10 [r2_1; exW_canary SEGS 1410112 m10]) m10 (EVar 101) (EVar 373) arr1 r2_1 0 32 0 4 eq_refl eq_refl RRarr1 RRr2_1 AP_arr1_r2_1) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals9 r10 [r2_1; exW_canary SEGS 1410112 m10]) m10) _ _ (ex_kdisj_apart SEGS (ex_envL vals9 r10 [r2_1; exW_canary SEGS 1410112 m10]) m10 (EVar 135) (EVar 373) r1_0 r2_1 0 4 0 4 eq_refl eq_refl RRr1_0 RRr2_1 AP_r1_0_r2_1) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals9 r10 [r2_1; exW_canary SEGS 1410112 m10]) m10) _ _ (ex_kdisj_apart SEGS (ex_envL vals9 r10 [r2_1; exW_canary SEGS 1410112 m10]) m10 (EVar 169) (EVar 373) r1_1 r2_1 0 4 0 4 eq_refl eq_refl RRr1_1 RRr2_1 AP_r1_1_r2_1) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals9 r10 [r2_1; exW_canary SEGS 1410112 m10]) m10) _ _ (ex_kdisj_apart SEGS (ex_envL vals9 r10 [r2_1; exW_canary SEGS 1410112 m10]) m10 (EVar 203) (EVar 373) r1_2 r2_1 0 4 0 4 eq_refl eq_refl RRr1_2 RRr2_1 AP_r1_2_r2_1) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals9 r10 [r2_1; exW_canary SEGS 1410112 m10]) m10) _ _ (ex_kdisj_apart SEGS (ex_envL vals9 r10 [r2_1; exW_canary SEGS 1410112 m10]) m10 (EVar 237) (EVar 373) r1_3 r2_1 0 4 0 4 eq_refl eq_refl RRr1_3 RRr2_1 AP_r1_3_r2_1) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals9 r10 [r2_1; exW_canary SEGS 1410112 m10]) m10) _ _ (ex_kdisj_apart SEGS (ex_envL vals9 r10 [r2_1; exW_canary SEGS 1410112 m10]) m10 (EVar 271) (EVar 373) sel2 r2_1 0 32 0 4 eq_refl eq_refl RRsel2 RRr2_1 AP_sel2_r2_1) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals9 r10 [r2_1; exW_canary SEGS 1410112 m10]) m10) _ _ (ex_kdisj_apart SEGS (ex_envL vals9 r10 [r2_1; exW_canary SEGS 1410112 m10]) m10 (EVar 305) (EVar 373) arr2 r2_1 0 64 0 4 eq_refl eq_refl RRarr2 RRr2_1 AP_arr2_r2_1) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals9 r10 [r2_1; exW_canary SEGS 1410112 m10]) m10) _ _ (ex_kdisj_apart SEGS (ex_envL vals9 r10 [r2_1; exW_canary SEGS 1410112 m10]) m10 (EVar 339) (EVar 373) r2_0 r2_1 0 4 0 4 eq_refl eq_refl RRr2_0 RRr2_1 AP_r2_0_r2_1) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals9 r10 [r2_1; exW_canary SEGS 1410112 m10]) m10))))))))))) as HKd10.
  pose proof (W_sok_win C A10 m10 _ (s - 4304) (Z.to_nat 4304) CK HW10 GLO1 GLO2) as SOK10.
  pose proof (exW_canary_ok SEGS 1410112 m10 (canary_any m10)) as CANOK10.
  pose (vals10 := vals9 ++ map (getr r10) ex_regs_list ++ map (Z_to_bv 64) [r2_1; exW_canary SEGS 1410112 m10]).
  pose proof (exW_kn_fixed SEGS C A10 m10 _ (ex_envL vals9 r10 [r2_1; exW_canary SEGS 1410112 m10]) (EVar 374) (EVar 32) (exW_canary SEGS 1410112 m10) s 4304 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW10 eq_refl (proj1 CANOK10) (proj2 CANOK10) eq_refl eq_refl eq_refl SOK10 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf10.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb10 (proj2 (Forall_app _ _ _) (conj HKd10 (proj2 (Forall_app _ _ _) (conj HKf10 HKa10)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn10 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN10 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb10 HKd10 HKf10 HKa10 SOK10 CANOK10.
  repeat match goal with H : getr r10 _ = _ |- _ => clear H end.
  exq_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO9 ALr2_1.
  exb_exit ST Rc10 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E10 := EEx) in HR, Hlf, HK, Hms |- *; set (log10 := LLx) in Hms, Hlf; set (M10 := mem_denot E10 m10 log10) in Hms end.
  assert (WP10 : W C A10 M10 (with_vmmaps vm10 md) /\ POSTM C A0 s m10 M10).
  { subst M10. apply (exW_win_blks C A10 A0 m10 _ E10 log10 (EVar 32) s 4304 [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z); (EVar 135, r1_0, 4%Z); (EVar 169, r1_1, 4%Z); (EVar 203, r1_2, 4%Z); (EVar 237, r1_3, 4%Z); (EVar 271, sel2, 32%Z); (EVar 305, arr2, 64%Z); (EVar 339, r2_0, 4%Z); (EVar 373, r2_1, 4%Z)] CK HW10 SUB10 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a10 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a10 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a10 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRr1_1 (conj Lr1_1_a10 (conj Fr1_1 F0r1_1))))|]. constructor; [exact (conj eq_refl (conj RRr1_2 (conj Lr1_2_a10 (conj Fr1_2 F0r1_2))))|]. constructor; [exact (conj eq_refl (conj RRr1_3 (conj Lr1_3_a10 (conj Fr1_3 F0r1_3))))|]. constructor; [exact (conj eq_refl (conj RRsel2 (conj Lsel2_a10 (conj Fsel2 F0sel2))))|]. constructor; [exact (conj eq_refl (conj RRarr2 (conj Larr2_a10 (conj Farr2 F0arr2))))|]. constructor; [exact (conj eq_refl (conj RRr2_0 (conj Lr2_0_a10 (conj Fr2_0 F0r2_0))))|]. constructor; [exact (conj eq_refl (conj RRr2_1 (conj Lr2_1_a10 (conj Fr2_1 F0r2_1))))|]. constructor. }
  assert (CFs10 : O23LeptCselsA.cs_fra s (-32) (-40) m0 M10).
  { subst M10. apply (cs_frame_sess C A10 A0 m0 m10 _ E10 log10 (EVar 32) s 4304 (-32) (-40) [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z); (EVar 135, r1_0, 4%Z); (EVar 169, r1_1, 4%Z); (EVar 203, r1_2, 4%Z); (EVar 237, r1_3, 4%Z); (EVar 271, sel2, 32%Z); (EVar 305, arr2, 64%Z); (EVar 339, r2_0, 4%Z); (EVar 373, r2_1, 4%Z)] CK HW10 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exact RS | lia | exact Hhi | reflexivity | | reflexivity | exact CF10]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a10 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a10 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a10 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRr1_1 (conj Lr1_1_a10 (conj Fr1_1 F0r1_1))))|]. constructor; [exact (conj eq_refl (conj RRr1_2 (conj Lr1_2_a10 (conj Fr1_2 F0r1_2))))|]. constructor; [exact (conj eq_refl (conj RRr1_3 (conj Lr1_3_a10 (conj Fr1_3 F0r1_3))))|]. constructor; [exact (conj eq_refl (conj RRsel2 (conj Lsel2_a10 (conj Fsel2 F0sel2))))|]. constructor; [exact (conj eq_refl (conj RRarr2 (conj Larr2_a10 (conj Farr2 F0arr2))))|]. constructor; [exact (conj eq_refl (conj RRr2_0 (conj Lr2_0_a10 (conj Fr2_0 F0r2_0))))|]. constructor; [exact (conj eq_refl (conj RRr2_1 (conj Lr2_1_a10 (conj Fr2_1 F0r2_1))))|]. constructor. }
  destruct WP10 as [HWs10 PMs10].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log10 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC10 : carry log10 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc10 : know_ok SEGS E10 M10 kn1) by (apply (carry_after SEGS E10 m10 log10 kn0 [] kn1 scs hs HC10 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW10)) | exact (mp_lazy _ (w_pure _ _ _ _ HW10)) | exact Hms |].
  pose (BS10 := [(32%nat, s); (67%nat, sel1); (101%nat, arr1); (135%nat, r1_0); (169%nat, r1_1); (203%nat, r1_2); (237%nat, r1_3); (271%nat, sel2); (305%nat, arr2); (339%nat, r2_0); (373%nat, r2_1)]).
  exW_regfactB BS10 HR ex_r10 Q10_10. exW_regfactB BS10 HR ex_r11 Q11_10. exW_regfactB BS10 HR ex_r1 Q1_10. exW_regfactB BS10 HR ex_r2 Q2_10. exW_regfactB BS10 HR ex_r4 Q4_10.
  clear BS10.
  lazymatch type of Q2_10 with _ = Z_to_bv 64 (s + ?off) => pose (OFF10 := off) end.
  pose proof (alloc_margin_small (1 * 4) ltac:(exW_cmp)) as MG10.
  lazymatch type of Q1_10 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_10 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A10 M10 _ Rc10 1 4 (kR - 10) (bR - 10 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs10 Q10_10 Q11_10 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM10) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_10
             ltac:(red; apply bv_eq; reflexivity) Q4_10 Q2_10 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A11 m11 vm11 r11 res10 HW11 Hres10 CSx10 Hnz10 Fr2_2x Lo10 F0r2_2 LEQ10 ZERO10 ALr2_2 TOP10 PMc10 RM11.
  pose proof CSx10 as CS10. clear CSx10.
  rewrite with_vmmaps_twice in HW11 |- *.
  assert (Eres10 : res10 = Z_to_bv 64 (u res10)) by (symmetry; apply zbv_self).
  pose proof (u64_range res10) as RRr2_2. set (r2_2 := u res10) in *. clearbody r2_2. rewrite Eres10 in Hres10, Fr2_2x, Lo10, F0r2_2, LEQ10, ZERO10. clear Eres10.
  change (1 * 4)%Z with 4%Z in *.
  pose proof (exW_blk_img_apart_h2 C A11 m11 _ r2_2 4 CK HW11 Lo10 RRr2_2 eq_refl eq_refl) as IMGAPr2_2. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPr2_2.
  pose proof (exW_win_blk_apart_h C A11 m11 _ s 4304 r2_2 4 CK HW11 Lo10 eq_refl RRr2_2 GLO1) as WAPr2_2.
  assert (Fr2_2 : live A0 (Z_to_bv 64 r2_2) = None).
  { destruct (live A0 (Z_to_bv 64 r2_2)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB10 _ _ EE) as XX. first [discriminate Fr2_2x | (rewrite Fr2_2x in XX; discriminate XX)]. }
  pose proof Lo10 as Lr2_2_a11.
  assert (SUB11 : sub_live A0 A11).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 r2_2) by (intros ->; rewrite Fr2_2 in Lq; discriminate Lq). rewrite (LEQ10 q NEq). exact (SUB10 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 r2_2 :: [Z_to_bv 64 r2_1; Z_to_bv 64 r2_0; Z_to_bv 64 arr2; Z_to_bv 64 sel2; Z_to_bv 64 r1_3; Z_to_bv 64 r1_2; Z_to_bv 64 r1_1; Z_to_bv 64 r1_0; Z_to_bv 64 arr1; Z_to_bv 64 sel1])) => eq_trans (LEQ10 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL10 q (fun XX => Hq (or_intror XX)))) as LDEL11.
  assert (NE_sel1_r2_2 : Z_to_bv 64 sel1 <> Z_to_bv 64 r2_2) by (intros EE; rewrite EE in Lsel1_a10; rewrite Fr2_2x in Lsel1_a10; discriminate Lsel1_a10).
  assert (Lsel1_a11 : live A11 (Z_to_bv 64 sel1) = Some 32%Z) by (rewrite (LEQ10 _ NE_sel1_r2_2); exact Lsel1_a10).
  pose proof (exW_blk_apart_h C A11 m11 _ sel1 r2_2 32 4 CK HW11 Lsel1_a11 Lr2_2_a11 NE_sel1_r2_2 RRsel1 RRr2_2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel1_r2_2.
  assert (NE_arr1_r2_2 : Z_to_bv 64 arr1 <> Z_to_bv 64 r2_2) by (intros EE; rewrite EE in Larr1_a10; rewrite Fr2_2x in Larr1_a10; discriminate Larr1_a10).
  assert (Larr1_a11 : live A11 (Z_to_bv 64 arr1) = Some 32%Z) by (rewrite (LEQ10 _ NE_arr1_r2_2); exact Larr1_a10).
  pose proof (exW_blk_apart_h C A11 m11 _ arr1 r2_2 32 4 CK HW11 Larr1_a11 Lr2_2_a11 NE_arr1_r2_2 RRarr1 RRr2_2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr1_r2_2.
  assert (NE_r1_0_r2_2 : Z_to_bv 64 r1_0 <> Z_to_bv 64 r2_2) by (intros EE; rewrite EE in Lr1_0_a10; rewrite Fr2_2x in Lr1_0_a10; discriminate Lr1_0_a10).
  assert (Lr1_0_a11 : live A11 (Z_to_bv 64 r1_0) = Some 4%Z) by (rewrite (LEQ10 _ NE_r1_0_r2_2); exact Lr1_0_a10).
  pose proof (exW_blk_apart_h C A11 m11 _ r1_0 r2_2 4 4 CK HW11 Lr1_0_a11 Lr2_2_a11 NE_r1_0_r2_2 RRr1_0 RRr2_2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_0_r2_2.
  assert (NE_r1_1_r2_2 : Z_to_bv 64 r1_1 <> Z_to_bv 64 r2_2) by (intros EE; rewrite EE in Lr1_1_a10; rewrite Fr2_2x in Lr1_1_a10; discriminate Lr1_1_a10).
  assert (Lr1_1_a11 : live A11 (Z_to_bv 64 r1_1) = Some 4%Z) by (rewrite (LEQ10 _ NE_r1_1_r2_2); exact Lr1_1_a10).
  pose proof (exW_blk_apart_h C A11 m11 _ r1_1 r2_2 4 4 CK HW11 Lr1_1_a11 Lr2_2_a11 NE_r1_1_r2_2 RRr1_1 RRr2_2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_1_r2_2.
  assert (NE_r1_2_r2_2 : Z_to_bv 64 r1_2 <> Z_to_bv 64 r2_2) by (intros EE; rewrite EE in Lr1_2_a10; rewrite Fr2_2x in Lr1_2_a10; discriminate Lr1_2_a10).
  assert (Lr1_2_a11 : live A11 (Z_to_bv 64 r1_2) = Some 4%Z) by (rewrite (LEQ10 _ NE_r1_2_r2_2); exact Lr1_2_a10).
  pose proof (exW_blk_apart_h C A11 m11 _ r1_2 r2_2 4 4 CK HW11 Lr1_2_a11 Lr2_2_a11 NE_r1_2_r2_2 RRr1_2 RRr2_2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_2_r2_2.
  assert (NE_r1_3_r2_2 : Z_to_bv 64 r1_3 <> Z_to_bv 64 r2_2) by (intros EE; rewrite EE in Lr1_3_a10; rewrite Fr2_2x in Lr1_3_a10; discriminate Lr1_3_a10).
  assert (Lr1_3_a11 : live A11 (Z_to_bv 64 r1_3) = Some 4%Z) by (rewrite (LEQ10 _ NE_r1_3_r2_2); exact Lr1_3_a10).
  pose proof (exW_blk_apart_h C A11 m11 _ r1_3 r2_2 4 4 CK HW11 Lr1_3_a11 Lr2_2_a11 NE_r1_3_r2_2 RRr1_3 RRr2_2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_3_r2_2.
  assert (NE_sel2_r2_2 : Z_to_bv 64 sel2 <> Z_to_bv 64 r2_2) by (intros EE; rewrite EE in Lsel2_a10; rewrite Fr2_2x in Lsel2_a10; discriminate Lsel2_a10).
  assert (Lsel2_a11 : live A11 (Z_to_bv 64 sel2) = Some 32%Z) by (rewrite (LEQ10 _ NE_sel2_r2_2); exact Lsel2_a10).
  pose proof (exW_blk_apart_h C A11 m11 _ sel2 r2_2 32 4 CK HW11 Lsel2_a11 Lr2_2_a11 NE_sel2_r2_2 RRsel2 RRr2_2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel2_r2_2.
  assert (NE_arr2_r2_2 : Z_to_bv 64 arr2 <> Z_to_bv 64 r2_2) by (intros EE; rewrite EE in Larr2_a10; rewrite Fr2_2x in Larr2_a10; discriminate Larr2_a10).
  assert (Larr2_a11 : live A11 (Z_to_bv 64 arr2) = Some 64%Z) by (rewrite (LEQ10 _ NE_arr2_r2_2); exact Larr2_a10).
  pose proof (exW_blk_apart_h C A11 m11 _ arr2 r2_2 64 4 CK HW11 Larr2_a11 Lr2_2_a11 NE_arr2_r2_2 RRarr2 RRr2_2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr2_r2_2.
  assert (NE_r2_0_r2_2 : Z_to_bv 64 r2_0 <> Z_to_bv 64 r2_2) by (intros EE; rewrite EE in Lr2_0_a10; rewrite Fr2_2x in Lr2_0_a10; discriminate Lr2_0_a10).
  assert (Lr2_0_a11 : live A11 (Z_to_bv 64 r2_0) = Some 4%Z) by (rewrite (LEQ10 _ NE_r2_0_r2_2); exact Lr2_0_a10).
  pose proof (exW_blk_apart_h C A11 m11 _ r2_0 r2_2 4 4 CK HW11 Lr2_0_a11 Lr2_2_a11 NE_r2_0_r2_2 RRr2_0 RRr2_2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r2_0_r2_2.
  assert (NE_r2_1_r2_2 : Z_to_bv 64 r2_1 <> Z_to_bv 64 r2_2) by (intros EE; rewrite EE in Lr2_1_a10; rewrite Fr2_2x in Lr2_1_a10; discriminate Lr2_1_a10).
  assert (Lr2_1_a11 : live A11 (Z_to_bv 64 r2_1) = Some 4%Z) by (rewrite (LEQ10 _ NE_r2_1_r2_2); exact Lr2_1_a10).
  pose proof (exW_blk_apart_h C A11 m11 _ r2_1 r2_2 4 4 CK HW11 Lr2_1_a11 Lr2_2_a11 NE_r2_1_r2_2 RRr2_1 RRr2_2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r2_1_r2_2.
  assert (PM11 : POSTM C A0 s m0 m11).
  { eapply POSTM_trans; [exact PM10|]. eapply POSTM_trans; [exact PMs10|]. apply (POSTM_sub C A0 A10 _ _ _ SUB10).
    apply (POSTM_mono C A10 (s + OFF10) s); [unfold OFF10; lia | exact PMc10]. }
  pose proof (cs_frame_hop C s 4304 OFF10 (-32) (-40) m0 M10 m11 CK (proj1 PMc10) ltac:(lia) ltac:(vm_cast_no_check (eq_refl true)) ltac:(vm_cast_no_check (eq_refl true)) CFs10) as CF11.
  replace (kR - 10 - 1)%Z with (kR - 11)%Z in RM11 by lia. rewrite MG10 in RM11. replace (bR - 10 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 11 * 2 ^ 17)%Z in RM11 by lia.
  assert (KEPT10 : Forall (ex_region_kept E10 M10 m11) [(EVar 32, OFF10, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 32%Z); (EVar 135, 0%Z, 4%Z); (EVar 169, 0%Z, 4%Z); (EVar 203, 0%Z, 4%Z); (EVar 237, 0%Z, 4%Z); (EVar 271, 0%Z, 32%Z); (EVar 305, 0%Z, 64%Z); (EVar 339, 0%Z, 4%Z); (EVar 373, 0%Z, 4%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF10 4304 M10 m11 E10 (EVar 32) CK (proj1 PMc10) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A10 A10 M10 _ M10 m11 E10 (EVar 67) sel1 32 CK HWs10 Lsel1_a10 RRsel1 eq_refl (proj2 PMc10) Lsel1_a10 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A10 A10 M10 _ M10 m11 E10 (EVar 101) arr1 32 CK HWs10 Larr1_a10 RRarr1 eq_refl (proj2 PMc10) Larr1_a10 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A10 A10 M10 _ M10 m11 E10 (EVar 135) r1_0 4 CK HWs10 Lr1_0_a10 RRr1_0 eq_refl (proj2 PMc10) Lr1_0_a10 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A10 A10 M10 _ M10 m11 E10 (EVar 169) r1_1 4 CK HWs10 Lr1_1_a10 RRr1_1 eq_refl (proj2 PMc10) Lr1_1_a10 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A10 A10 M10 _ M10 m11 E10 (EVar 203) r1_2 4 CK HWs10 Lr1_2_a10 RRr1_2 eq_refl (proj2 PMc10) Lr1_2_a10 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A10 A10 M10 _ M10 m11 E10 (EVar 237) r1_3 4 CK HWs10 Lr1_3_a10 RRr1_3 eq_refl (proj2 PMc10) Lr1_3_a10 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A10 A10 M10 _ M10 m11 E10 (EVar 271) sel2 32 CK HWs10 Lsel2_a10 RRsel2 eq_refl (proj2 PMc10) Lsel2_a10 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A10 A10 M10 _ M10 m11 E10 (EVar 305) arr2 64 CK HWs10 Larr2_a10 RRarr2 eq_refl (proj2 PMc10) Larr2_a10 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A10 A10 M10 _ M10 m11 E10 (EVar 339) r2_0 4 CK HWs10 Lr2_0_a10 RRr2_0 eq_refl (proj2 PMc10) Lr2_0_a10 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A10 A10 M10 _ M10 m11 E10 (EVar 373) r2_1 4 CK HWs10 Lr2_1_a10 RRr2_1 eq_refl (proj2 PMc10) Lr2_1_a10 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E10 M10 m11 _ [] _ HKc10 KEPT10) as HKk10.
  match type of HKk10 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E10 m11 kk') in HKk10 end.
  pose proof (regs_ok_agree 375%nat E10 (ex_envL vals10 r11 [r2_2; exW_canary SEGS 1410112 m11]) _ _ (vals_app_agree vals10 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa10.
  pose proof (exW_regs_call _ _ _ _ _ HRa10 (ex_regs_ok_junk vals10 r11 [r2_2; exW_canary SEGS 1410112 m11] 375%nat ltac:(vm_cast_no_check (eq_refl 375%nat))) CS10) as HRn11.
  clear HRa10.
  assert (HKa11 : know_ok SEGS (ex_envL vals10 r11 [r2_2; exW_canary SEGS 1410112 m11]) m11 _) by (exact (know_ok_agree SEGS 375%nat E10 _ m11 _ (vals_app_agree vals10 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk10)).
  rewrite (fr_denot_agree 375%nat E10 (ex_envL vals10 r11 [r2_2; exW_canary SEGS 1410112 m11]) _ fr (vals_app_agree vals10 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r11 ex_r10 (EVar 407) HRn11 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres10)) as HRx11. clear HRn11. rename HRx11 into HRn11.
  clear HR HK Hlf Hms HKc10 HKk10 KEPT10 HC10 HWs10 PMs10 Q10_10 Q11_10 Q1_10 Q2_10 Q4_10 PM10 HW10 PMc10 CS10 SUB10 RM10 MG10 TOP10 LEQ10 Hnz10 Fr2_2x Lo10 OFF10 LDEL10 CF10 CFs10 Lsel1_a10 Larr1_a10 Lr1_0_a10 Lr1_1_a10 Lr1_2_a10 Lr1_3_a10 Lsel2_a10 Larr2_a10 Lr2_0_a10 Lr2_1_a10.
  subst M10. clear log10. clear E10. try clear Rc10. clear KN10.
  lazymatch type of HRn11 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn11 end.
  pose proof (exW_kn_blk SEGS C A11 m11 _ (ex_envL vals10 r11 [r2_2; exW_canary SEGS 1410112 m11]) (EVar 407) (EVar 32) r2_2 4 s 4304 65536 1347584 p16_segs CK HW11 Lr2_2_a11 RRr2_2 eq_refl eq_refl eq_refl RS ALr2_2 ZERO10 WAPr2_2 IMGAPr2_2) as HKb11.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals10 r11 [r2_2; exW_canary SEGS 1410112 m11]) m11) _ _ (ex_kdisj_apart SEGS (ex_envL vals10 r11 [r2_2; exW_canary SEGS 1410112 m11]) m11 (EVar 67) (EVar 407) sel1 r2_2 0 32 0 4 eq_refl eq_refl RRsel1 RRr2_2 AP_sel1_r2_2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals10 r11 [r2_2; exW_canary SEGS 1410112 m11]) m11) _ _ (ex_kdisj_apart SEGS (ex_envL vals10 r11 [r2_2; exW_canary SEGS 1410112 m11]) m11 (EVar 101) (EVar 407) arr1 r2_2 0 32 0 4 eq_refl eq_refl RRarr1 RRr2_2 AP_arr1_r2_2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals10 r11 [r2_2; exW_canary SEGS 1410112 m11]) m11) _ _ (ex_kdisj_apart SEGS (ex_envL vals10 r11 [r2_2; exW_canary SEGS 1410112 m11]) m11 (EVar 135) (EVar 407) r1_0 r2_2 0 4 0 4 eq_refl eq_refl RRr1_0 RRr2_2 AP_r1_0_r2_2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals10 r11 [r2_2; exW_canary SEGS 1410112 m11]) m11) _ _ (ex_kdisj_apart SEGS (ex_envL vals10 r11 [r2_2; exW_canary SEGS 1410112 m11]) m11 (EVar 169) (EVar 407) r1_1 r2_2 0 4 0 4 eq_refl eq_refl RRr1_1 RRr2_2 AP_r1_1_r2_2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals10 r11 [r2_2; exW_canary SEGS 1410112 m11]) m11) _ _ (ex_kdisj_apart SEGS (ex_envL vals10 r11 [r2_2; exW_canary SEGS 1410112 m11]) m11 (EVar 203) (EVar 407) r1_2 r2_2 0 4 0 4 eq_refl eq_refl RRr1_2 RRr2_2 AP_r1_2_r2_2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals10 r11 [r2_2; exW_canary SEGS 1410112 m11]) m11) _ _ (ex_kdisj_apart SEGS (ex_envL vals10 r11 [r2_2; exW_canary SEGS 1410112 m11]) m11 (EVar 237) (EVar 407) r1_3 r2_2 0 4 0 4 eq_refl eq_refl RRr1_3 RRr2_2 AP_r1_3_r2_2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals10 r11 [r2_2; exW_canary SEGS 1410112 m11]) m11) _ _ (ex_kdisj_apart SEGS (ex_envL vals10 r11 [r2_2; exW_canary SEGS 1410112 m11]) m11 (EVar 271) (EVar 407) sel2 r2_2 0 32 0 4 eq_refl eq_refl RRsel2 RRr2_2 AP_sel2_r2_2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals10 r11 [r2_2; exW_canary SEGS 1410112 m11]) m11) _ _ (ex_kdisj_apart SEGS (ex_envL vals10 r11 [r2_2; exW_canary SEGS 1410112 m11]) m11 (EVar 305) (EVar 407) arr2 r2_2 0 64 0 4 eq_refl eq_refl RRarr2 RRr2_2 AP_arr2_r2_2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals10 r11 [r2_2; exW_canary SEGS 1410112 m11]) m11) _ _ (ex_kdisj_apart SEGS (ex_envL vals10 r11 [r2_2; exW_canary SEGS 1410112 m11]) m11 (EVar 339) (EVar 407) r2_0 r2_2 0 4 0 4 eq_refl eq_refl RRr2_0 RRr2_2 AP_r2_0_r2_2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals10 r11 [r2_2; exW_canary SEGS 1410112 m11]) m11) _ _ (ex_kdisj_apart SEGS (ex_envL vals10 r11 [r2_2; exW_canary SEGS 1410112 m11]) m11 (EVar 373) (EVar 407) r2_1 r2_2 0 4 0 4 eq_refl eq_refl RRr2_1 RRr2_2 AP_r2_1_r2_2) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals10 r11 [r2_2; exW_canary SEGS 1410112 m11]) m11)))))))))))) as HKd11.
  pose proof (W_sok_win C A11 m11 _ (s - 4304) (Z.to_nat 4304) CK HW11 GLO1 GLO2) as SOK11.
  pose proof (exW_canary_ok SEGS 1410112 m11 (canary_any m11)) as CANOK11.
  pose (vals11 := vals10 ++ map (getr r11) ex_regs_list ++ map (Z_to_bv 64) [r2_2; exW_canary SEGS 1410112 m11]).
  pose proof (exW_kn_fixed SEGS C A11 m11 _ (ex_envL vals10 r11 [r2_2; exW_canary SEGS 1410112 m11]) (EVar 408) (EVar 32) (exW_canary SEGS 1410112 m11) s 4304 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW11 eq_refl (proj1 CANOK11) (proj2 CANOK11) eq_refl eq_refl eq_refl SOK11 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf11.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb11 (proj2 (Forall_app _ _ _) (conj HKd11 (proj2 (Forall_app _ _ _) (conj HKf11 HKa11)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn11 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN11 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb11 HKd11 HKf11 HKa11 SOK11 CANOK11.
  repeat match goal with H : getr r11 _ = _ |- _ => clear H end.
  exq_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO10 ALr2_2.
  exb_exit ST Rc11 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E11 := EEx) in HR, Hlf, HK, Hms |- *; set (log11 := LLx) in Hms, Hlf; set (M11 := mem_denot E11 m11 log11) in Hms end.
  assert (WP11 : W C A11 M11 (with_vmmaps vm11 md) /\ POSTM C A0 s m11 M11).
  { subst M11. apply (exW_win_blks C A11 A0 m11 _ E11 log11 (EVar 32) s 4304 [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z); (EVar 135, r1_0, 4%Z); (EVar 169, r1_1, 4%Z); (EVar 203, r1_2, 4%Z); (EVar 237, r1_3, 4%Z); (EVar 271, sel2, 32%Z); (EVar 305, arr2, 64%Z); (EVar 339, r2_0, 4%Z); (EVar 373, r2_1, 4%Z); (EVar 407, r2_2, 4%Z)] CK HW11 SUB11 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a11 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a11 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a11 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRr1_1 (conj Lr1_1_a11 (conj Fr1_1 F0r1_1))))|]. constructor; [exact (conj eq_refl (conj RRr1_2 (conj Lr1_2_a11 (conj Fr1_2 F0r1_2))))|]. constructor; [exact (conj eq_refl (conj RRr1_3 (conj Lr1_3_a11 (conj Fr1_3 F0r1_3))))|]. constructor; [exact (conj eq_refl (conj RRsel2 (conj Lsel2_a11 (conj Fsel2 F0sel2))))|]. constructor; [exact (conj eq_refl (conj RRarr2 (conj Larr2_a11 (conj Farr2 F0arr2))))|]. constructor; [exact (conj eq_refl (conj RRr2_0 (conj Lr2_0_a11 (conj Fr2_0 F0r2_0))))|]. constructor; [exact (conj eq_refl (conj RRr2_1 (conj Lr2_1_a11 (conj Fr2_1 F0r2_1))))|]. constructor; [exact (conj eq_refl (conj RRr2_2 (conj Lr2_2_a11 (conj Fr2_2 F0r2_2))))|]. constructor. }
  assert (CFs11 : O23LeptCselsA.cs_fra s (-32) (-40) m0 M11).
  { subst M11. apply (cs_frame_sess C A11 A0 m0 m11 _ E11 log11 (EVar 32) s 4304 (-32) (-40) [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z); (EVar 135, r1_0, 4%Z); (EVar 169, r1_1, 4%Z); (EVar 203, r1_2, 4%Z); (EVar 237, r1_3, 4%Z); (EVar 271, sel2, 32%Z); (EVar 305, arr2, 64%Z); (EVar 339, r2_0, 4%Z); (EVar 373, r2_1, 4%Z); (EVar 407, r2_2, 4%Z)] CK HW11 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exact RS | lia | exact Hhi | reflexivity | | reflexivity | exact CF11]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a11 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a11 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a11 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRr1_1 (conj Lr1_1_a11 (conj Fr1_1 F0r1_1))))|]. constructor; [exact (conj eq_refl (conj RRr1_2 (conj Lr1_2_a11 (conj Fr1_2 F0r1_2))))|]. constructor; [exact (conj eq_refl (conj RRr1_3 (conj Lr1_3_a11 (conj Fr1_3 F0r1_3))))|]. constructor; [exact (conj eq_refl (conj RRsel2 (conj Lsel2_a11 (conj Fsel2 F0sel2))))|]. constructor; [exact (conj eq_refl (conj RRarr2 (conj Larr2_a11 (conj Farr2 F0arr2))))|]. constructor; [exact (conj eq_refl (conj RRr2_0 (conj Lr2_0_a11 (conj Fr2_0 F0r2_0))))|]. constructor; [exact (conj eq_refl (conj RRr2_1 (conj Lr2_1_a11 (conj Fr2_1 F0r2_1))))|]. constructor; [exact (conj eq_refl (conj RRr2_2 (conj Lr2_2_a11 (conj Fr2_2 F0r2_2))))|]. constructor. }
  destruct WP11 as [HWs11 PMs11].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log11 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC11 : carry log11 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc11 : know_ok SEGS E11 M11 kn1) by (apply (carry_after SEGS E11 m11 log11 kn0 [] kn1 scs hs HC11 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW11)) | exact (mp_lazy _ (w_pure _ _ _ _ HW11)) | exact Hms |].
  pose (BS11 := [(32%nat, s); (67%nat, sel1); (101%nat, arr1); (135%nat, r1_0); (169%nat, r1_1); (203%nat, r1_2); (237%nat, r1_3); (271%nat, sel2); (305%nat, arr2); (339%nat, r2_0); (373%nat, r2_1); (407%nat, r2_2)]).
  exW_regfactB BS11 HR ex_r10 Q10_11. exW_regfactB BS11 HR ex_r11 Q11_11. exW_regfactB BS11 HR ex_r1 Q1_11. exW_regfactB BS11 HR ex_r2 Q2_11. exW_regfactB BS11 HR ex_r4 Q4_11.
  clear BS11.
  lazymatch type of Q2_11 with _ = Z_to_bv 64 (s + ?off) => pose (OFF11 := off) end.
  pose proof (alloc_margin_small (1 * 4) ltac:(exW_cmp)) as MG11.
  lazymatch type of Q1_11 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_11 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A11 M11 _ Rc11 1 4 (kR - 11) (bR - 11 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs11 Q10_11 Q11_11 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM11) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_11
             ltac:(red; apply bv_eq; reflexivity) Q4_11 Q2_11 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A12 m12 vm12 r12 res11 HW12 Hres11 CSx11 Hnz11 Fr2_3x Lo11 F0r2_3 LEQ11 ZERO11 ALr2_3 TOP11 PMc11 RM12.
  pose proof CSx11 as CS11. clear CSx11.
  rewrite with_vmmaps_twice in HW12 |- *.
  assert (Eres11 : res11 = Z_to_bv 64 (u res11)) by (symmetry; apply zbv_self).
  pose proof (u64_range res11) as RRr2_3. set (r2_3 := u res11) in *. clearbody r2_3. rewrite Eres11 in Hres11, Fr2_3x, Lo11, F0r2_3, LEQ11, ZERO11. clear Eres11.
  change (1 * 4)%Z with 4%Z in *.
  pose proof (exW_blk_img_apart_h2 C A12 m12 _ r2_3 4 CK HW12 Lo11 RRr2_3 eq_refl eq_refl) as IMGAPr2_3. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPr2_3.
  pose proof (exW_win_blk_apart_h C A12 m12 _ s 4304 r2_3 4 CK HW12 Lo11 eq_refl RRr2_3 GLO1) as WAPr2_3.
  assert (Fr2_3 : live A0 (Z_to_bv 64 r2_3) = None).
  { destruct (live A0 (Z_to_bv 64 r2_3)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB11 _ _ EE) as XX. first [discriminate Fr2_3x | (rewrite Fr2_3x in XX; discriminate XX)]. }
  pose proof Lo11 as Lr2_3_a12.
  assert (SUB12 : sub_live A0 A12).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 r2_3) by (intros ->; rewrite Fr2_3 in Lq; discriminate Lq). rewrite (LEQ11 q NEq). exact (SUB11 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 r2_3 :: [Z_to_bv 64 r2_2; Z_to_bv 64 r2_1; Z_to_bv 64 r2_0; Z_to_bv 64 arr2; Z_to_bv 64 sel2; Z_to_bv 64 r1_3; Z_to_bv 64 r1_2; Z_to_bv 64 r1_1; Z_to_bv 64 r1_0; Z_to_bv 64 arr1; Z_to_bv 64 sel1])) => eq_trans (LEQ11 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL11 q (fun XX => Hq (or_intror XX)))) as LDEL12.
  assert (NE_sel1_r2_3 : Z_to_bv 64 sel1 <> Z_to_bv 64 r2_3) by (intros EE; rewrite EE in Lsel1_a11; rewrite Fr2_3x in Lsel1_a11; discriminate Lsel1_a11).
  assert (Lsel1_a12 : live A12 (Z_to_bv 64 sel1) = Some 32%Z) by (rewrite (LEQ11 _ NE_sel1_r2_3); exact Lsel1_a11).
  pose proof (exW_blk_apart_h C A12 m12 _ sel1 r2_3 32 4 CK HW12 Lsel1_a12 Lr2_3_a12 NE_sel1_r2_3 RRsel1 RRr2_3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel1_r2_3.
  assert (NE_arr1_r2_3 : Z_to_bv 64 arr1 <> Z_to_bv 64 r2_3) by (intros EE; rewrite EE in Larr1_a11; rewrite Fr2_3x in Larr1_a11; discriminate Larr1_a11).
  assert (Larr1_a12 : live A12 (Z_to_bv 64 arr1) = Some 32%Z) by (rewrite (LEQ11 _ NE_arr1_r2_3); exact Larr1_a11).
  pose proof (exW_blk_apart_h C A12 m12 _ arr1 r2_3 32 4 CK HW12 Larr1_a12 Lr2_3_a12 NE_arr1_r2_3 RRarr1 RRr2_3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr1_r2_3.
  assert (NE_r1_0_r2_3 : Z_to_bv 64 r1_0 <> Z_to_bv 64 r2_3) by (intros EE; rewrite EE in Lr1_0_a11; rewrite Fr2_3x in Lr1_0_a11; discriminate Lr1_0_a11).
  assert (Lr1_0_a12 : live A12 (Z_to_bv 64 r1_0) = Some 4%Z) by (rewrite (LEQ11 _ NE_r1_0_r2_3); exact Lr1_0_a11).
  pose proof (exW_blk_apart_h C A12 m12 _ r1_0 r2_3 4 4 CK HW12 Lr1_0_a12 Lr2_3_a12 NE_r1_0_r2_3 RRr1_0 RRr2_3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_0_r2_3.
  assert (NE_r1_1_r2_3 : Z_to_bv 64 r1_1 <> Z_to_bv 64 r2_3) by (intros EE; rewrite EE in Lr1_1_a11; rewrite Fr2_3x in Lr1_1_a11; discriminate Lr1_1_a11).
  assert (Lr1_1_a12 : live A12 (Z_to_bv 64 r1_1) = Some 4%Z) by (rewrite (LEQ11 _ NE_r1_1_r2_3); exact Lr1_1_a11).
  pose proof (exW_blk_apart_h C A12 m12 _ r1_1 r2_3 4 4 CK HW12 Lr1_1_a12 Lr2_3_a12 NE_r1_1_r2_3 RRr1_1 RRr2_3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_1_r2_3.
  assert (NE_r1_2_r2_3 : Z_to_bv 64 r1_2 <> Z_to_bv 64 r2_3) by (intros EE; rewrite EE in Lr1_2_a11; rewrite Fr2_3x in Lr1_2_a11; discriminate Lr1_2_a11).
  assert (Lr1_2_a12 : live A12 (Z_to_bv 64 r1_2) = Some 4%Z) by (rewrite (LEQ11 _ NE_r1_2_r2_3); exact Lr1_2_a11).
  pose proof (exW_blk_apart_h C A12 m12 _ r1_2 r2_3 4 4 CK HW12 Lr1_2_a12 Lr2_3_a12 NE_r1_2_r2_3 RRr1_2 RRr2_3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_2_r2_3.
  assert (NE_r1_3_r2_3 : Z_to_bv 64 r1_3 <> Z_to_bv 64 r2_3) by (intros EE; rewrite EE in Lr1_3_a11; rewrite Fr2_3x in Lr1_3_a11; discriminate Lr1_3_a11).
  assert (Lr1_3_a12 : live A12 (Z_to_bv 64 r1_3) = Some 4%Z) by (rewrite (LEQ11 _ NE_r1_3_r2_3); exact Lr1_3_a11).
  pose proof (exW_blk_apart_h C A12 m12 _ r1_3 r2_3 4 4 CK HW12 Lr1_3_a12 Lr2_3_a12 NE_r1_3_r2_3 RRr1_3 RRr2_3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_3_r2_3.
  assert (NE_sel2_r2_3 : Z_to_bv 64 sel2 <> Z_to_bv 64 r2_3) by (intros EE; rewrite EE in Lsel2_a11; rewrite Fr2_3x in Lsel2_a11; discriminate Lsel2_a11).
  assert (Lsel2_a12 : live A12 (Z_to_bv 64 sel2) = Some 32%Z) by (rewrite (LEQ11 _ NE_sel2_r2_3); exact Lsel2_a11).
  pose proof (exW_blk_apart_h C A12 m12 _ sel2 r2_3 32 4 CK HW12 Lsel2_a12 Lr2_3_a12 NE_sel2_r2_3 RRsel2 RRr2_3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel2_r2_3.
  assert (NE_arr2_r2_3 : Z_to_bv 64 arr2 <> Z_to_bv 64 r2_3) by (intros EE; rewrite EE in Larr2_a11; rewrite Fr2_3x in Larr2_a11; discriminate Larr2_a11).
  assert (Larr2_a12 : live A12 (Z_to_bv 64 arr2) = Some 64%Z) by (rewrite (LEQ11 _ NE_arr2_r2_3); exact Larr2_a11).
  pose proof (exW_blk_apart_h C A12 m12 _ arr2 r2_3 64 4 CK HW12 Larr2_a12 Lr2_3_a12 NE_arr2_r2_3 RRarr2 RRr2_3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr2_r2_3.
  assert (NE_r2_0_r2_3 : Z_to_bv 64 r2_0 <> Z_to_bv 64 r2_3) by (intros EE; rewrite EE in Lr2_0_a11; rewrite Fr2_3x in Lr2_0_a11; discriminate Lr2_0_a11).
  assert (Lr2_0_a12 : live A12 (Z_to_bv 64 r2_0) = Some 4%Z) by (rewrite (LEQ11 _ NE_r2_0_r2_3); exact Lr2_0_a11).
  pose proof (exW_blk_apart_h C A12 m12 _ r2_0 r2_3 4 4 CK HW12 Lr2_0_a12 Lr2_3_a12 NE_r2_0_r2_3 RRr2_0 RRr2_3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r2_0_r2_3.
  assert (NE_r2_1_r2_3 : Z_to_bv 64 r2_1 <> Z_to_bv 64 r2_3) by (intros EE; rewrite EE in Lr2_1_a11; rewrite Fr2_3x in Lr2_1_a11; discriminate Lr2_1_a11).
  assert (Lr2_1_a12 : live A12 (Z_to_bv 64 r2_1) = Some 4%Z) by (rewrite (LEQ11 _ NE_r2_1_r2_3); exact Lr2_1_a11).
  pose proof (exW_blk_apart_h C A12 m12 _ r2_1 r2_3 4 4 CK HW12 Lr2_1_a12 Lr2_3_a12 NE_r2_1_r2_3 RRr2_1 RRr2_3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r2_1_r2_3.
  assert (NE_r2_2_r2_3 : Z_to_bv 64 r2_2 <> Z_to_bv 64 r2_3) by (intros EE; rewrite EE in Lr2_2_a11; rewrite Fr2_3x in Lr2_2_a11; discriminate Lr2_2_a11).
  assert (Lr2_2_a12 : live A12 (Z_to_bv 64 r2_2) = Some 4%Z) by (rewrite (LEQ11 _ NE_r2_2_r2_3); exact Lr2_2_a11).
  pose proof (exW_blk_apart_h C A12 m12 _ r2_2 r2_3 4 4 CK HW12 Lr2_2_a12 Lr2_3_a12 NE_r2_2_r2_3 RRr2_2 RRr2_3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r2_2_r2_3.
  assert (PM12 : POSTM C A0 s m0 m12).
  { eapply POSTM_trans; [exact PM11|]. eapply POSTM_trans; [exact PMs11|]. apply (POSTM_sub C A0 A11 _ _ _ SUB11).
    apply (POSTM_mono C A11 (s + OFF11) s); [unfold OFF11; lia | exact PMc11]. }
  pose proof (cs_frame_hop C s 4304 OFF11 (-32) (-40) m0 M11 m12 CK (proj1 PMc11) ltac:(lia) ltac:(vm_cast_no_check (eq_refl true)) ltac:(vm_cast_no_check (eq_refl true)) CFs11) as CF12.
  replace (kR - 11 - 1)%Z with (kR - 12)%Z in RM12 by lia. rewrite MG11 in RM12. replace (bR - 11 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 12 * 2 ^ 17)%Z in RM12 by lia.
  assert (KEPT11 : Forall (ex_region_kept E11 M11 m12) [(EVar 32, OFF11, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 32%Z); (EVar 135, 0%Z, 4%Z); (EVar 169, 0%Z, 4%Z); (EVar 203, 0%Z, 4%Z); (EVar 237, 0%Z, 4%Z); (EVar 271, 0%Z, 32%Z); (EVar 305, 0%Z, 64%Z); (EVar 339, 0%Z, 4%Z); (EVar 373, 0%Z, 4%Z); (EVar 407, 0%Z, 4%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF11 4304 M11 m12 E11 (EVar 32) CK (proj1 PMc11) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A11 A11 M11 _ M11 m12 E11 (EVar 67) sel1 32 CK HWs11 Lsel1_a11 RRsel1 eq_refl (proj2 PMc11) Lsel1_a11 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A11 A11 M11 _ M11 m12 E11 (EVar 101) arr1 32 CK HWs11 Larr1_a11 RRarr1 eq_refl (proj2 PMc11) Larr1_a11 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A11 A11 M11 _ M11 m12 E11 (EVar 135) r1_0 4 CK HWs11 Lr1_0_a11 RRr1_0 eq_refl (proj2 PMc11) Lr1_0_a11 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A11 A11 M11 _ M11 m12 E11 (EVar 169) r1_1 4 CK HWs11 Lr1_1_a11 RRr1_1 eq_refl (proj2 PMc11) Lr1_1_a11 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A11 A11 M11 _ M11 m12 E11 (EVar 203) r1_2 4 CK HWs11 Lr1_2_a11 RRr1_2 eq_refl (proj2 PMc11) Lr1_2_a11 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A11 A11 M11 _ M11 m12 E11 (EVar 237) r1_3 4 CK HWs11 Lr1_3_a11 RRr1_3 eq_refl (proj2 PMc11) Lr1_3_a11 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A11 A11 M11 _ M11 m12 E11 (EVar 271) sel2 32 CK HWs11 Lsel2_a11 RRsel2 eq_refl (proj2 PMc11) Lsel2_a11 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A11 A11 M11 _ M11 m12 E11 (EVar 305) arr2 64 CK HWs11 Larr2_a11 RRarr2 eq_refl (proj2 PMc11) Larr2_a11 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A11 A11 M11 _ M11 m12 E11 (EVar 339) r2_0 4 CK HWs11 Lr2_0_a11 RRr2_0 eq_refl (proj2 PMc11) Lr2_0_a11 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A11 A11 M11 _ M11 m12 E11 (EVar 373) r2_1 4 CK HWs11 Lr2_1_a11 RRr2_1 eq_refl (proj2 PMc11) Lr2_1_a11 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A11 A11 M11 _ M11 m12 E11 (EVar 407) r2_2 4 CK HWs11 Lr2_2_a11 RRr2_2 eq_refl (proj2 PMc11) Lr2_2_a11 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E11 M11 m12 _ [] _ HKc11 KEPT11) as HKk11.
  match type of HKk11 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E11 m12 kk') in HKk11 end.
  pose proof (regs_ok_agree 409%nat E11 (ex_envL vals11 r12 [r2_3; exW_canary SEGS 1410112 m12]) _ _ (vals_app_agree vals11 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa11.
  pose proof (exW_regs_call _ _ _ _ _ HRa11 (ex_regs_ok_junk vals11 r12 [r2_3; exW_canary SEGS 1410112 m12] 409%nat ltac:(vm_cast_no_check (eq_refl 409%nat))) CS11) as HRn12.
  clear HRa11.
  assert (HKa12 : know_ok SEGS (ex_envL vals11 r12 [r2_3; exW_canary SEGS 1410112 m12]) m12 _) by (exact (know_ok_agree SEGS 409%nat E11 _ m12 _ (vals_app_agree vals11 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk11)).
  rewrite (fr_denot_agree 409%nat E11 (ex_envL vals11 r12 [r2_3; exW_canary SEGS 1410112 m12]) _ fr (vals_app_agree vals11 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r12 ex_r10 (EVar 441) HRn12 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres11)) as HRx12. clear HRn12. rename HRx12 into HRn12.
  clear HR HK Hlf Hms HKc11 HKk11 KEPT11 HC11 HWs11 PMs11 Q10_11 Q11_11 Q1_11 Q2_11 Q4_11 PM11 HW11 PMc11 CS11 SUB11 RM11 MG11 TOP11 LEQ11 Hnz11 Fr2_3x Lo11 OFF11 LDEL11 CF11 CFs11 Lsel1_a11 Larr1_a11 Lr1_0_a11 Lr1_1_a11 Lr1_2_a11 Lr1_3_a11 Lsel2_a11 Larr2_a11 Lr2_0_a11 Lr2_1_a11 Lr2_2_a11.
  subst M11. clear log11. clear E11. try clear Rc11. clear KN11.
  lazymatch type of HRn12 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn12 end.
  pose proof (exW_kn_blk SEGS C A12 m12 _ (ex_envL vals11 r12 [r2_3; exW_canary SEGS 1410112 m12]) (EVar 441) (EVar 32) r2_3 4 s 4304 65536 1347584 p16_segs CK HW12 Lr2_3_a12 RRr2_3 eq_refl eq_refl eq_refl RS ALr2_3 ZERO11 WAPr2_3 IMGAPr2_3) as HKb12.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals11 r12 [r2_3; exW_canary SEGS 1410112 m12]) m12) _ _ (ex_kdisj_apart SEGS (ex_envL vals11 r12 [r2_3; exW_canary SEGS 1410112 m12]) m12 (EVar 67) (EVar 441) sel1 r2_3 0 32 0 4 eq_refl eq_refl RRsel1 RRr2_3 AP_sel1_r2_3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals11 r12 [r2_3; exW_canary SEGS 1410112 m12]) m12) _ _ (ex_kdisj_apart SEGS (ex_envL vals11 r12 [r2_3; exW_canary SEGS 1410112 m12]) m12 (EVar 101) (EVar 441) arr1 r2_3 0 32 0 4 eq_refl eq_refl RRarr1 RRr2_3 AP_arr1_r2_3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals11 r12 [r2_3; exW_canary SEGS 1410112 m12]) m12) _ _ (ex_kdisj_apart SEGS (ex_envL vals11 r12 [r2_3; exW_canary SEGS 1410112 m12]) m12 (EVar 135) (EVar 441) r1_0 r2_3 0 4 0 4 eq_refl eq_refl RRr1_0 RRr2_3 AP_r1_0_r2_3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals11 r12 [r2_3; exW_canary SEGS 1410112 m12]) m12) _ _ (ex_kdisj_apart SEGS (ex_envL vals11 r12 [r2_3; exW_canary SEGS 1410112 m12]) m12 (EVar 169) (EVar 441) r1_1 r2_3 0 4 0 4 eq_refl eq_refl RRr1_1 RRr2_3 AP_r1_1_r2_3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals11 r12 [r2_3; exW_canary SEGS 1410112 m12]) m12) _ _ (ex_kdisj_apart SEGS (ex_envL vals11 r12 [r2_3; exW_canary SEGS 1410112 m12]) m12 (EVar 203) (EVar 441) r1_2 r2_3 0 4 0 4 eq_refl eq_refl RRr1_2 RRr2_3 AP_r1_2_r2_3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals11 r12 [r2_3; exW_canary SEGS 1410112 m12]) m12) _ _ (ex_kdisj_apart SEGS (ex_envL vals11 r12 [r2_3; exW_canary SEGS 1410112 m12]) m12 (EVar 237) (EVar 441) r1_3 r2_3 0 4 0 4 eq_refl eq_refl RRr1_3 RRr2_3 AP_r1_3_r2_3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals11 r12 [r2_3; exW_canary SEGS 1410112 m12]) m12) _ _ (ex_kdisj_apart SEGS (ex_envL vals11 r12 [r2_3; exW_canary SEGS 1410112 m12]) m12 (EVar 271) (EVar 441) sel2 r2_3 0 32 0 4 eq_refl eq_refl RRsel2 RRr2_3 AP_sel2_r2_3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals11 r12 [r2_3; exW_canary SEGS 1410112 m12]) m12) _ _ (ex_kdisj_apart SEGS (ex_envL vals11 r12 [r2_3; exW_canary SEGS 1410112 m12]) m12 (EVar 305) (EVar 441) arr2 r2_3 0 64 0 4 eq_refl eq_refl RRarr2 RRr2_3 AP_arr2_r2_3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals11 r12 [r2_3; exW_canary SEGS 1410112 m12]) m12) _ _ (ex_kdisj_apart SEGS (ex_envL vals11 r12 [r2_3; exW_canary SEGS 1410112 m12]) m12 (EVar 339) (EVar 441) r2_0 r2_3 0 4 0 4 eq_refl eq_refl RRr2_0 RRr2_3 AP_r2_0_r2_3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals11 r12 [r2_3; exW_canary SEGS 1410112 m12]) m12) _ _ (ex_kdisj_apart SEGS (ex_envL vals11 r12 [r2_3; exW_canary SEGS 1410112 m12]) m12 (EVar 373) (EVar 441) r2_1 r2_3 0 4 0 4 eq_refl eq_refl RRr2_1 RRr2_3 AP_r2_1_r2_3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals11 r12 [r2_3; exW_canary SEGS 1410112 m12]) m12) _ _ (ex_kdisj_apart SEGS (ex_envL vals11 r12 [r2_3; exW_canary SEGS 1410112 m12]) m12 (EVar 407) (EVar 441) r2_2 r2_3 0 4 0 4 eq_refl eq_refl RRr2_2 RRr2_3 AP_r2_2_r2_3) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals11 r12 [r2_3; exW_canary SEGS 1410112 m12]) m12))))))))))))) as HKd12.
  pose proof (W_sok_win C A12 m12 _ (s - 4304) (Z.to_nat 4304) CK HW12 GLO1 GLO2) as SOK12.
  pose proof (exW_canary_ok SEGS 1410112 m12 (canary_any m12)) as CANOK12.
  pose (vals12 := vals11 ++ map (getr r12) ex_regs_list ++ map (Z_to_bv 64) [r2_3; exW_canary SEGS 1410112 m12]).
  pose proof (exW_kn_fixed SEGS C A12 m12 _ (ex_envL vals11 r12 [r2_3; exW_canary SEGS 1410112 m12]) (EVar 442) (EVar 32) (exW_canary SEGS 1410112 m12) s 4304 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW12 eq_refl (proj1 CANOK12) (proj2 CANOK12) eq_refl eq_refl eq_refl SOK12 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf12.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb12 (proj2 (Forall_app _ _ _) (conj HKd12 (proj2 (Forall_app _ _ _) (conj HKf12 HKa12)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn12 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN12 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb12 HKd12 HKf12 HKa12 SOK12 CANOK12.
  repeat match goal with H : getr r12 _ = _ |- _ => clear H end.
  exq_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO11 ALr2_3.
  exb_exit ST Rc12 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E12 := EEx) in HR, Hlf, HK, Hms |- *; set (log12 := LLx) in Hms, Hlf; set (M12 := mem_denot E12 m12 log12) in Hms end.
  assert (WP12 : W C A12 M12 (with_vmmaps vm12 md) /\ POSTM C A0 s m12 M12).
  { subst M12. apply (exW_win_blks C A12 A0 m12 _ E12 log12 (EVar 32) s 4304 [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z); (EVar 135, r1_0, 4%Z); (EVar 169, r1_1, 4%Z); (EVar 203, r1_2, 4%Z); (EVar 237, r1_3, 4%Z); (EVar 271, sel2, 32%Z); (EVar 305, arr2, 64%Z); (EVar 339, r2_0, 4%Z); (EVar 373, r2_1, 4%Z); (EVar 407, r2_2, 4%Z); (EVar 441, r2_3, 4%Z)] CK HW12 SUB12 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a12 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a12 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a12 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRr1_1 (conj Lr1_1_a12 (conj Fr1_1 F0r1_1))))|]. constructor; [exact (conj eq_refl (conj RRr1_2 (conj Lr1_2_a12 (conj Fr1_2 F0r1_2))))|]. constructor; [exact (conj eq_refl (conj RRr1_3 (conj Lr1_3_a12 (conj Fr1_3 F0r1_3))))|]. constructor; [exact (conj eq_refl (conj RRsel2 (conj Lsel2_a12 (conj Fsel2 F0sel2))))|]. constructor; [exact (conj eq_refl (conj RRarr2 (conj Larr2_a12 (conj Farr2 F0arr2))))|]. constructor; [exact (conj eq_refl (conj RRr2_0 (conj Lr2_0_a12 (conj Fr2_0 F0r2_0))))|]. constructor; [exact (conj eq_refl (conj RRr2_1 (conj Lr2_1_a12 (conj Fr2_1 F0r2_1))))|]. constructor; [exact (conj eq_refl (conj RRr2_2 (conj Lr2_2_a12 (conj Fr2_2 F0r2_2))))|]. constructor; [exact (conj eq_refl (conj RRr2_3 (conj Lr2_3_a12 (conj Fr2_3 F0r2_3))))|]. constructor. }
  assert (CFs12 : O23LeptCselsA.cs_fra s (-32) (-40) m0 M12).
  { subst M12. apply (cs_frame_sess C A12 A0 m0 m12 _ E12 log12 (EVar 32) s 4304 (-32) (-40) [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z); (EVar 135, r1_0, 4%Z); (EVar 169, r1_1, 4%Z); (EVar 203, r1_2, 4%Z); (EVar 237, r1_3, 4%Z); (EVar 271, sel2, 32%Z); (EVar 305, arr2, 64%Z); (EVar 339, r2_0, 4%Z); (EVar 373, r2_1, 4%Z); (EVar 407, r2_2, 4%Z); (EVar 441, r2_3, 4%Z)] CK HW12 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exact RS | lia | exact Hhi | reflexivity | | reflexivity | exact CF12]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a12 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a12 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a12 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRr1_1 (conj Lr1_1_a12 (conj Fr1_1 F0r1_1))))|]. constructor; [exact (conj eq_refl (conj RRr1_2 (conj Lr1_2_a12 (conj Fr1_2 F0r1_2))))|]. constructor; [exact (conj eq_refl (conj RRr1_3 (conj Lr1_3_a12 (conj Fr1_3 F0r1_3))))|]. constructor; [exact (conj eq_refl (conj RRsel2 (conj Lsel2_a12 (conj Fsel2 F0sel2))))|]. constructor; [exact (conj eq_refl (conj RRarr2 (conj Larr2_a12 (conj Farr2 F0arr2))))|]. constructor; [exact (conj eq_refl (conj RRr2_0 (conj Lr2_0_a12 (conj Fr2_0 F0r2_0))))|]. constructor; [exact (conj eq_refl (conj RRr2_1 (conj Lr2_1_a12 (conj Fr2_1 F0r2_1))))|]. constructor; [exact (conj eq_refl (conj RRr2_2 (conj Lr2_2_a12 (conj Fr2_2 F0r2_2))))|]. constructor; [exact (conj eq_refl (conj RRr2_3 (conj Lr2_3_a12 (conj Fr2_3 F0r2_3))))|]. constructor. }
  destruct WP12 as [HWs12 PMs12].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log12 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC12 : carry log12 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc12 : know_ok SEGS E12 M12 kn1) by (apply (carry_after SEGS E12 m12 log12 kn0 [] kn1 scs hs HC12 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW12)) | exact (mp_lazy _ (w_pure _ _ _ _ HW12)) | exact Hms |].
  pose (BS12 := [(32%nat, s); (67%nat, sel1); (101%nat, arr1); (135%nat, r1_0); (169%nat, r1_1); (203%nat, r1_2); (237%nat, r1_3); (271%nat, sel2); (305%nat, arr2); (339%nat, r2_0); (373%nat, r2_1); (407%nat, r2_2); (441%nat, r2_3)]).
  exW_regfactB BS12 HR ex_r10 Q10_12. exW_regfactB BS12 HR ex_r11 Q11_12. exW_regfactB BS12 HR ex_r1 Q1_12. exW_regfactB BS12 HR ex_r2 Q2_12. exW_regfactB BS12 HR ex_r4 Q4_12.
  clear BS12.
  lazymatch type of Q2_12 with _ = Z_to_bv 64 (s + ?off) => pose (OFF12 := off) end.
  pose proof (alloc_margin_small (1 * 4) ltac:(exW_cmp)) as MG12.
  lazymatch type of Q1_12 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_12 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A12 M12 _ Rc12 1 4 (kR - 12) (bR - 12 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs12 Q10_12 Q11_12 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM12) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_12
             ltac:(red; apply bv_eq; reflexivity) Q4_12 Q2_12 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A13 m13 vm13 r13 res12 HW13 Hres12 CSx12 Hnz12 Fr2_4x Lo12 F0r2_4 LEQ12 ZERO12 ALr2_4 TOP12 PMc12 RM13.
  pose proof CSx12 as CS12. clear CSx12.
  rewrite with_vmmaps_twice in HW13 |- *.
  assert (Eres12 : res12 = Z_to_bv 64 (u res12)) by (symmetry; apply zbv_self).
  pose proof (u64_range res12) as RRr2_4. set (r2_4 := u res12) in *. clearbody r2_4. rewrite Eres12 in Hres12, Fr2_4x, Lo12, F0r2_4, LEQ12, ZERO12. clear Eres12.
  change (1 * 4)%Z with 4%Z in *.
  pose proof (exW_blk_img_apart_h2 C A13 m13 _ r2_4 4 CK HW13 Lo12 RRr2_4 eq_refl eq_refl) as IMGAPr2_4. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPr2_4.
  pose proof (exW_win_blk_apart_h C A13 m13 _ s 4304 r2_4 4 CK HW13 Lo12 eq_refl RRr2_4 GLO1) as WAPr2_4.
  assert (Fr2_4 : live A0 (Z_to_bv 64 r2_4) = None).
  { destruct (live A0 (Z_to_bv 64 r2_4)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB12 _ _ EE) as XX. first [discriminate Fr2_4x | (rewrite Fr2_4x in XX; discriminate XX)]. }
  pose proof Lo12 as Lr2_4_a13.
  assert (SUB13 : sub_live A0 A13).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 r2_4) by (intros ->; rewrite Fr2_4 in Lq; discriminate Lq). rewrite (LEQ12 q NEq). exact (SUB12 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 r2_4 :: [Z_to_bv 64 r2_3; Z_to_bv 64 r2_2; Z_to_bv 64 r2_1; Z_to_bv 64 r2_0; Z_to_bv 64 arr2; Z_to_bv 64 sel2; Z_to_bv 64 r1_3; Z_to_bv 64 r1_2; Z_to_bv 64 r1_1; Z_to_bv 64 r1_0; Z_to_bv 64 arr1; Z_to_bv 64 sel1])) => eq_trans (LEQ12 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL12 q (fun XX => Hq (or_intror XX)))) as LDEL13.
  assert (NE_sel1_r2_4 : Z_to_bv 64 sel1 <> Z_to_bv 64 r2_4) by (intros EE; rewrite EE in Lsel1_a12; rewrite Fr2_4x in Lsel1_a12; discriminate Lsel1_a12).
  assert (Lsel1_a13 : live A13 (Z_to_bv 64 sel1) = Some 32%Z) by (rewrite (LEQ12 _ NE_sel1_r2_4); exact Lsel1_a12).
  pose proof (exW_blk_apart_h C A13 m13 _ sel1 r2_4 32 4 CK HW13 Lsel1_a13 Lr2_4_a13 NE_sel1_r2_4 RRsel1 RRr2_4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel1_r2_4.
  assert (NE_arr1_r2_4 : Z_to_bv 64 arr1 <> Z_to_bv 64 r2_4) by (intros EE; rewrite EE in Larr1_a12; rewrite Fr2_4x in Larr1_a12; discriminate Larr1_a12).
  assert (Larr1_a13 : live A13 (Z_to_bv 64 arr1) = Some 32%Z) by (rewrite (LEQ12 _ NE_arr1_r2_4); exact Larr1_a12).
  pose proof (exW_blk_apart_h C A13 m13 _ arr1 r2_4 32 4 CK HW13 Larr1_a13 Lr2_4_a13 NE_arr1_r2_4 RRarr1 RRr2_4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr1_r2_4.
  assert (NE_r1_0_r2_4 : Z_to_bv 64 r1_0 <> Z_to_bv 64 r2_4) by (intros EE; rewrite EE in Lr1_0_a12; rewrite Fr2_4x in Lr1_0_a12; discriminate Lr1_0_a12).
  assert (Lr1_0_a13 : live A13 (Z_to_bv 64 r1_0) = Some 4%Z) by (rewrite (LEQ12 _ NE_r1_0_r2_4); exact Lr1_0_a12).
  pose proof (exW_blk_apart_h C A13 m13 _ r1_0 r2_4 4 4 CK HW13 Lr1_0_a13 Lr2_4_a13 NE_r1_0_r2_4 RRr1_0 RRr2_4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_0_r2_4.
  assert (NE_r1_1_r2_4 : Z_to_bv 64 r1_1 <> Z_to_bv 64 r2_4) by (intros EE; rewrite EE in Lr1_1_a12; rewrite Fr2_4x in Lr1_1_a12; discriminate Lr1_1_a12).
  assert (Lr1_1_a13 : live A13 (Z_to_bv 64 r1_1) = Some 4%Z) by (rewrite (LEQ12 _ NE_r1_1_r2_4); exact Lr1_1_a12).
  pose proof (exW_blk_apart_h C A13 m13 _ r1_1 r2_4 4 4 CK HW13 Lr1_1_a13 Lr2_4_a13 NE_r1_1_r2_4 RRr1_1 RRr2_4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_1_r2_4.
  assert (NE_r1_2_r2_4 : Z_to_bv 64 r1_2 <> Z_to_bv 64 r2_4) by (intros EE; rewrite EE in Lr1_2_a12; rewrite Fr2_4x in Lr1_2_a12; discriminate Lr1_2_a12).
  assert (Lr1_2_a13 : live A13 (Z_to_bv 64 r1_2) = Some 4%Z) by (rewrite (LEQ12 _ NE_r1_2_r2_4); exact Lr1_2_a12).
  pose proof (exW_blk_apart_h C A13 m13 _ r1_2 r2_4 4 4 CK HW13 Lr1_2_a13 Lr2_4_a13 NE_r1_2_r2_4 RRr1_2 RRr2_4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_2_r2_4.
  assert (NE_r1_3_r2_4 : Z_to_bv 64 r1_3 <> Z_to_bv 64 r2_4) by (intros EE; rewrite EE in Lr1_3_a12; rewrite Fr2_4x in Lr1_3_a12; discriminate Lr1_3_a12).
  assert (Lr1_3_a13 : live A13 (Z_to_bv 64 r1_3) = Some 4%Z) by (rewrite (LEQ12 _ NE_r1_3_r2_4); exact Lr1_3_a12).
  pose proof (exW_blk_apart_h C A13 m13 _ r1_3 r2_4 4 4 CK HW13 Lr1_3_a13 Lr2_4_a13 NE_r1_3_r2_4 RRr1_3 RRr2_4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_3_r2_4.
  assert (NE_sel2_r2_4 : Z_to_bv 64 sel2 <> Z_to_bv 64 r2_4) by (intros EE; rewrite EE in Lsel2_a12; rewrite Fr2_4x in Lsel2_a12; discriminate Lsel2_a12).
  assert (Lsel2_a13 : live A13 (Z_to_bv 64 sel2) = Some 32%Z) by (rewrite (LEQ12 _ NE_sel2_r2_4); exact Lsel2_a12).
  pose proof (exW_blk_apart_h C A13 m13 _ sel2 r2_4 32 4 CK HW13 Lsel2_a13 Lr2_4_a13 NE_sel2_r2_4 RRsel2 RRr2_4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel2_r2_4.
  assert (NE_arr2_r2_4 : Z_to_bv 64 arr2 <> Z_to_bv 64 r2_4) by (intros EE; rewrite EE in Larr2_a12; rewrite Fr2_4x in Larr2_a12; discriminate Larr2_a12).
  assert (Larr2_a13 : live A13 (Z_to_bv 64 arr2) = Some 64%Z) by (rewrite (LEQ12 _ NE_arr2_r2_4); exact Larr2_a12).
  pose proof (exW_blk_apart_h C A13 m13 _ arr2 r2_4 64 4 CK HW13 Larr2_a13 Lr2_4_a13 NE_arr2_r2_4 RRarr2 RRr2_4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr2_r2_4.
  assert (NE_r2_0_r2_4 : Z_to_bv 64 r2_0 <> Z_to_bv 64 r2_4) by (intros EE; rewrite EE in Lr2_0_a12; rewrite Fr2_4x in Lr2_0_a12; discriminate Lr2_0_a12).
  assert (Lr2_0_a13 : live A13 (Z_to_bv 64 r2_0) = Some 4%Z) by (rewrite (LEQ12 _ NE_r2_0_r2_4); exact Lr2_0_a12).
  pose proof (exW_blk_apart_h C A13 m13 _ r2_0 r2_4 4 4 CK HW13 Lr2_0_a13 Lr2_4_a13 NE_r2_0_r2_4 RRr2_0 RRr2_4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r2_0_r2_4.
  assert (NE_r2_1_r2_4 : Z_to_bv 64 r2_1 <> Z_to_bv 64 r2_4) by (intros EE; rewrite EE in Lr2_1_a12; rewrite Fr2_4x in Lr2_1_a12; discriminate Lr2_1_a12).
  assert (Lr2_1_a13 : live A13 (Z_to_bv 64 r2_1) = Some 4%Z) by (rewrite (LEQ12 _ NE_r2_1_r2_4); exact Lr2_1_a12).
  pose proof (exW_blk_apart_h C A13 m13 _ r2_1 r2_4 4 4 CK HW13 Lr2_1_a13 Lr2_4_a13 NE_r2_1_r2_4 RRr2_1 RRr2_4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r2_1_r2_4.
  assert (NE_r2_2_r2_4 : Z_to_bv 64 r2_2 <> Z_to_bv 64 r2_4) by (intros EE; rewrite EE in Lr2_2_a12; rewrite Fr2_4x in Lr2_2_a12; discriminate Lr2_2_a12).
  assert (Lr2_2_a13 : live A13 (Z_to_bv 64 r2_2) = Some 4%Z) by (rewrite (LEQ12 _ NE_r2_2_r2_4); exact Lr2_2_a12).
  pose proof (exW_blk_apart_h C A13 m13 _ r2_2 r2_4 4 4 CK HW13 Lr2_2_a13 Lr2_4_a13 NE_r2_2_r2_4 RRr2_2 RRr2_4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r2_2_r2_4.
  assert (NE_r2_3_r2_4 : Z_to_bv 64 r2_3 <> Z_to_bv 64 r2_4) by (intros EE; rewrite EE in Lr2_3_a12; rewrite Fr2_4x in Lr2_3_a12; discriminate Lr2_3_a12).
  assert (Lr2_3_a13 : live A13 (Z_to_bv 64 r2_3) = Some 4%Z) by (rewrite (LEQ12 _ NE_r2_3_r2_4); exact Lr2_3_a12).
  pose proof (exW_blk_apart_h C A13 m13 _ r2_3 r2_4 4 4 CK HW13 Lr2_3_a13 Lr2_4_a13 NE_r2_3_r2_4 RRr2_3 RRr2_4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r2_3_r2_4.
  assert (PM13 : POSTM C A0 s m0 m13).
  { eapply POSTM_trans; [exact PM12|]. eapply POSTM_trans; [exact PMs12|]. apply (POSTM_sub C A0 A12 _ _ _ SUB12).
    apply (POSTM_mono C A12 (s + OFF12) s); [unfold OFF12; lia | exact PMc12]. }
  pose proof (cs_frame_hop C s 4304 OFF12 (-32) (-40) m0 M12 m13 CK (proj1 PMc12) ltac:(lia) ltac:(vm_cast_no_check (eq_refl true)) ltac:(vm_cast_no_check (eq_refl true)) CFs12) as CF13.
  replace (kR - 12 - 1)%Z with (kR - 13)%Z in RM13 by lia. rewrite MG12 in RM13. replace (bR - 12 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 13 * 2 ^ 17)%Z in RM13 by lia.
  assert (KEPT12 : Forall (ex_region_kept E12 M12 m13) [(EVar 32, OFF12, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 32%Z); (EVar 135, 0%Z, 4%Z); (EVar 169, 0%Z, 4%Z); (EVar 203, 0%Z, 4%Z); (EVar 237, 0%Z, 4%Z); (EVar 271, 0%Z, 32%Z); (EVar 305, 0%Z, 64%Z); (EVar 339, 0%Z, 4%Z); (EVar 373, 0%Z, 4%Z); (EVar 407, 0%Z, 4%Z); (EVar 441, 0%Z, 4%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF12 4304 M12 m13 E12 (EVar 32) CK (proj1 PMc12) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A12 A12 M12 _ M12 m13 E12 (EVar 67) sel1 32 CK HWs12 Lsel1_a12 RRsel1 eq_refl (proj2 PMc12) Lsel1_a12 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A12 A12 M12 _ M12 m13 E12 (EVar 101) arr1 32 CK HWs12 Larr1_a12 RRarr1 eq_refl (proj2 PMc12) Larr1_a12 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A12 A12 M12 _ M12 m13 E12 (EVar 135) r1_0 4 CK HWs12 Lr1_0_a12 RRr1_0 eq_refl (proj2 PMc12) Lr1_0_a12 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A12 A12 M12 _ M12 m13 E12 (EVar 169) r1_1 4 CK HWs12 Lr1_1_a12 RRr1_1 eq_refl (proj2 PMc12) Lr1_1_a12 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A12 A12 M12 _ M12 m13 E12 (EVar 203) r1_2 4 CK HWs12 Lr1_2_a12 RRr1_2 eq_refl (proj2 PMc12) Lr1_2_a12 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A12 A12 M12 _ M12 m13 E12 (EVar 237) r1_3 4 CK HWs12 Lr1_3_a12 RRr1_3 eq_refl (proj2 PMc12) Lr1_3_a12 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A12 A12 M12 _ M12 m13 E12 (EVar 271) sel2 32 CK HWs12 Lsel2_a12 RRsel2 eq_refl (proj2 PMc12) Lsel2_a12 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A12 A12 M12 _ M12 m13 E12 (EVar 305) arr2 64 CK HWs12 Larr2_a12 RRarr2 eq_refl (proj2 PMc12) Larr2_a12 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A12 A12 M12 _ M12 m13 E12 (EVar 339) r2_0 4 CK HWs12 Lr2_0_a12 RRr2_0 eq_refl (proj2 PMc12) Lr2_0_a12 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A12 A12 M12 _ M12 m13 E12 (EVar 373) r2_1 4 CK HWs12 Lr2_1_a12 RRr2_1 eq_refl (proj2 PMc12) Lr2_1_a12 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A12 A12 M12 _ M12 m13 E12 (EVar 407) r2_2 4 CK HWs12 Lr2_2_a12 RRr2_2 eq_refl (proj2 PMc12) Lr2_2_a12 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A12 A12 M12 _ M12 m13 E12 (EVar 441) r2_3 4 CK HWs12 Lr2_3_a12 RRr2_3 eq_refl (proj2 PMc12) Lr2_3_a12 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E12 M12 m13 _ [] _ HKc12 KEPT12) as HKk12.
  match type of HKk12 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E12 m13 kk') in HKk12 end.
  pose proof (regs_ok_agree 443%nat E12 (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) _ _ (vals_app_agree vals12 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa12.
  pose proof (exW_regs_call _ _ _ _ _ HRa12 (ex_regs_ok_junk vals12 r13 [r2_4; exW_canary SEGS 1410112 m13] 443%nat ltac:(vm_cast_no_check (eq_refl 443%nat))) CS12) as HRn13.
  clear HRa12.
  assert (HKa13 : know_ok SEGS (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) m13 _) by (exact (know_ok_agree SEGS 443%nat E12 _ m13 _ (vals_app_agree vals12 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk12)).
  rewrite (fr_denot_agree 443%nat E12 (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) _ fr (vals_app_agree vals12 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r13 ex_r10 (EVar 475) HRn13 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres12)) as HRx13. clear HRn13. rename HRx13 into HRn13.
  clear HR HK Hlf Hms HKc12 HKk12 KEPT12 HC12 HWs12 PMs12 Q10_12 Q11_12 Q1_12 Q2_12 Q4_12 PM12 HW12 PMc12 CS12 SUB12 RM12 MG12 TOP12 LEQ12 Hnz12 Fr2_4x Lo12 OFF12 LDEL12 CF12 CFs12 Lsel1_a12 Larr1_a12 Lr1_0_a12 Lr1_1_a12 Lr1_2_a12 Lr1_3_a12 Lsel2_a12 Larr2_a12 Lr2_0_a12 Lr2_1_a12 Lr2_2_a12 Lr2_3_a12.
  subst M12. clear log12. clear E12. try clear Rc12. clear KN12.
  lazymatch type of HRn13 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn13 end.
  pose proof (exW_kn_blk SEGS C A13 m13 _ (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) (EVar 475) (EVar 32) r2_4 4 s 4304 65536 1347584 p16_segs CK HW13 Lr2_4_a13 RRr2_4 eq_refl eq_refl eq_refl RS ALr2_4 ZERO12 WAPr2_4 IMGAPr2_4) as HKb13.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) m13) _ _ (ex_kdisj_apart SEGS (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) m13 (EVar 67) (EVar 475) sel1 r2_4 0 32 0 4 eq_refl eq_refl RRsel1 RRr2_4 AP_sel1_r2_4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) m13) _ _ (ex_kdisj_apart SEGS (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) m13 (EVar 101) (EVar 475) arr1 r2_4 0 32 0 4 eq_refl eq_refl RRarr1 RRr2_4 AP_arr1_r2_4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) m13) _ _ (ex_kdisj_apart SEGS (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) m13 (EVar 135) (EVar 475) r1_0 r2_4 0 4 0 4 eq_refl eq_refl RRr1_0 RRr2_4 AP_r1_0_r2_4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) m13) _ _ (ex_kdisj_apart SEGS (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) m13 (EVar 169) (EVar 475) r1_1 r2_4 0 4 0 4 eq_refl eq_refl RRr1_1 RRr2_4 AP_r1_1_r2_4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) m13) _ _ (ex_kdisj_apart SEGS (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) m13 (EVar 203) (EVar 475) r1_2 r2_4 0 4 0 4 eq_refl eq_refl RRr1_2 RRr2_4 AP_r1_2_r2_4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) m13) _ _ (ex_kdisj_apart SEGS (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) m13 (EVar 237) (EVar 475) r1_3 r2_4 0 4 0 4 eq_refl eq_refl RRr1_3 RRr2_4 AP_r1_3_r2_4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) m13) _ _ (ex_kdisj_apart SEGS (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) m13 (EVar 271) (EVar 475) sel2 r2_4 0 32 0 4 eq_refl eq_refl RRsel2 RRr2_4 AP_sel2_r2_4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) m13) _ _ (ex_kdisj_apart SEGS (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) m13 (EVar 305) (EVar 475) arr2 r2_4 0 64 0 4 eq_refl eq_refl RRarr2 RRr2_4 AP_arr2_r2_4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) m13) _ _ (ex_kdisj_apart SEGS (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) m13 (EVar 339) (EVar 475) r2_0 r2_4 0 4 0 4 eq_refl eq_refl RRr2_0 RRr2_4 AP_r2_0_r2_4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) m13) _ _ (ex_kdisj_apart SEGS (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) m13 (EVar 373) (EVar 475) r2_1 r2_4 0 4 0 4 eq_refl eq_refl RRr2_1 RRr2_4 AP_r2_1_r2_4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) m13) _ _ (ex_kdisj_apart SEGS (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) m13 (EVar 407) (EVar 475) r2_2 r2_4 0 4 0 4 eq_refl eq_refl RRr2_2 RRr2_4 AP_r2_2_r2_4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) m13) _ _ (ex_kdisj_apart SEGS (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) m13 (EVar 441) (EVar 475) r2_3 r2_4 0 4 0 4 eq_refl eq_refl RRr2_3 RRr2_4 AP_r2_3_r2_4) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) m13)))))))))))))) as HKd13.
  pose proof (W_sok_win C A13 m13 _ (s - 4304) (Z.to_nat 4304) CK HW13 GLO1 GLO2) as SOK13.
  pose proof (exW_canary_ok SEGS 1410112 m13 (canary_any m13)) as CANOK13.
  pose (vals13 := vals12 ++ map (getr r13) ex_regs_list ++ map (Z_to_bv 64) [r2_4; exW_canary SEGS 1410112 m13]).
  pose proof (exW_kn_fixed SEGS C A13 m13 _ (ex_envL vals12 r13 [r2_4; exW_canary SEGS 1410112 m13]) (EVar 476) (EVar 32) (exW_canary SEGS 1410112 m13) s 4304 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW13 eq_refl (proj1 CANOK13) (proj2 CANOK13) eq_refl eq_refl eq_refl SOK13 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf13.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb13 (proj2 (Forall_app _ _ _) (conj HKd13 (proj2 (Forall_app _ _ _) (conj HKf13 HKa13)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn13 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN13 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb13 HKd13 HKf13 HKa13 SOK13 CANOK13.
  repeat match goal with H : getr r13 _ = _ |- _ => clear H end.
  exq_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO12 ALr2_4.
  exb_exit ST Rc13 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E13 := EEx) in HR, Hlf, HK, Hms |- *; set (log13 := LLx) in Hms, Hlf; set (M13 := mem_denot E13 m13 log13) in Hms end.
  assert (WP13 : W C A13 M13 (with_vmmaps vm13 md) /\ POSTM C A0 s m13 M13).
  { subst M13. apply (exW_win_blks C A13 A0 m13 _ E13 log13 (EVar 32) s 4304 [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z); (EVar 135, r1_0, 4%Z); (EVar 169, r1_1, 4%Z); (EVar 203, r1_2, 4%Z); (EVar 237, r1_3, 4%Z); (EVar 271, sel2, 32%Z); (EVar 305, arr2, 64%Z); (EVar 339, r2_0, 4%Z); (EVar 373, r2_1, 4%Z); (EVar 407, r2_2, 4%Z); (EVar 441, r2_3, 4%Z); (EVar 475, r2_4, 4%Z)] CK HW13 SUB13 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a13 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a13 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a13 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRr1_1 (conj Lr1_1_a13 (conj Fr1_1 F0r1_1))))|]. constructor; [exact (conj eq_refl (conj RRr1_2 (conj Lr1_2_a13 (conj Fr1_2 F0r1_2))))|]. constructor; [exact (conj eq_refl (conj RRr1_3 (conj Lr1_3_a13 (conj Fr1_3 F0r1_3))))|]. constructor; [exact (conj eq_refl (conj RRsel2 (conj Lsel2_a13 (conj Fsel2 F0sel2))))|]. constructor; [exact (conj eq_refl (conj RRarr2 (conj Larr2_a13 (conj Farr2 F0arr2))))|]. constructor; [exact (conj eq_refl (conj RRr2_0 (conj Lr2_0_a13 (conj Fr2_0 F0r2_0))))|]. constructor; [exact (conj eq_refl (conj RRr2_1 (conj Lr2_1_a13 (conj Fr2_1 F0r2_1))))|]. constructor; [exact (conj eq_refl (conj RRr2_2 (conj Lr2_2_a13 (conj Fr2_2 F0r2_2))))|]. constructor; [exact (conj eq_refl (conj RRr2_3 (conj Lr2_3_a13 (conj Fr2_3 F0r2_3))))|]. constructor; [exact (conj eq_refl (conj RRr2_4 (conj Lr2_4_a13 (conj Fr2_4 F0r2_4))))|]. constructor. }
  assert (CFs13 : O23LeptCselsA.cs_fra s (-32) (-40) m0 M13).
  { subst M13. apply (cs_frame_sess C A13 A0 m0 m13 _ E13 log13 (EVar 32) s 4304 (-32) (-40) [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z); (EVar 135, r1_0, 4%Z); (EVar 169, r1_1, 4%Z); (EVar 203, r1_2, 4%Z); (EVar 237, r1_3, 4%Z); (EVar 271, sel2, 32%Z); (EVar 305, arr2, 64%Z); (EVar 339, r2_0, 4%Z); (EVar 373, r2_1, 4%Z); (EVar 407, r2_2, 4%Z); (EVar 441, r2_3, 4%Z); (EVar 475, r2_4, 4%Z)] CK HW13 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exact RS | lia | exact Hhi | reflexivity | | reflexivity | exact CF13]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a13 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a13 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a13 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRr1_1 (conj Lr1_1_a13 (conj Fr1_1 F0r1_1))))|]. constructor; [exact (conj eq_refl (conj RRr1_2 (conj Lr1_2_a13 (conj Fr1_2 F0r1_2))))|]. constructor; [exact (conj eq_refl (conj RRr1_3 (conj Lr1_3_a13 (conj Fr1_3 F0r1_3))))|]. constructor; [exact (conj eq_refl (conj RRsel2 (conj Lsel2_a13 (conj Fsel2 F0sel2))))|]. constructor; [exact (conj eq_refl (conj RRarr2 (conj Larr2_a13 (conj Farr2 F0arr2))))|]. constructor; [exact (conj eq_refl (conj RRr2_0 (conj Lr2_0_a13 (conj Fr2_0 F0r2_0))))|]. constructor; [exact (conj eq_refl (conj RRr2_1 (conj Lr2_1_a13 (conj Fr2_1 F0r2_1))))|]. constructor; [exact (conj eq_refl (conj RRr2_2 (conj Lr2_2_a13 (conj Fr2_2 F0r2_2))))|]. constructor; [exact (conj eq_refl (conj RRr2_3 (conj Lr2_3_a13 (conj Fr2_3 F0r2_3))))|]. constructor; [exact (conj eq_refl (conj RRr2_4 (conj Lr2_4_a13 (conj Fr2_4 F0r2_4))))|]. constructor. }
  destruct WP13 as [HWs13 PMs13].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log13 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC13 : carry log13 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc13 : know_ok SEGS E13 M13 kn1) by (apply (carry_after SEGS E13 m13 log13 kn0 [] kn1 scs hs HC13 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW13)) | exact (mp_lazy _ (w_pure _ _ _ _ HW13)) | exact Hms |].
  pose (BS13 := [(32%nat, s); (67%nat, sel1); (101%nat, arr1); (135%nat, r1_0); (169%nat, r1_1); (203%nat, r1_2); (237%nat, r1_3); (271%nat, sel2); (305%nat, arr2); (339%nat, r2_0); (373%nat, r2_1); (407%nat, r2_2); (441%nat, r2_3); (475%nat, r2_4)]).
  exW_regfactB BS13 HR ex_r10 Q10_13. exW_regfactB BS13 HR ex_r11 Q11_13. exW_regfactB BS13 HR ex_r1 Q1_13. exW_regfactB BS13 HR ex_r2 Q2_13. exW_regfactB BS13 HR ex_r4 Q4_13.
  clear BS13.
  lazymatch type of Q2_13 with _ = Z_to_bv 64 (s + ?off) => pose (OFF13 := off) end.
  pose proof (alloc_margin_small (1 * 4) ltac:(exW_cmp)) as MG13.
  lazymatch type of Q1_13 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_13 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A13 M13 _ Rc13 1 4 (kR - 13) (bR - 13 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs13 Q10_13 Q11_13 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM13) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_13
             ltac:(red; apply bv_eq; reflexivity) Q4_13 Q2_13 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A14 m14 vm14 r14 res13 HW14 Hres13 CSx13 Hnz13 Fr2_5x Lo13 F0r2_5 LEQ13 ZERO13 ALr2_5 TOP13 PMc13 RM14.
  pose proof CSx13 as CS13. clear CSx13.
  rewrite with_vmmaps_twice in HW14 |- *.
  assert (Eres13 : res13 = Z_to_bv 64 (u res13)) by (symmetry; apply zbv_self).
  pose proof (u64_range res13) as RRr2_5. set (r2_5 := u res13) in *. clearbody r2_5. rewrite Eres13 in Hres13, Fr2_5x, Lo13, F0r2_5, LEQ13, ZERO13. clear Eres13.
  change (1 * 4)%Z with 4%Z in *.
  pose proof (exW_blk_img_apart_h2 C A14 m14 _ r2_5 4 CK HW14 Lo13 RRr2_5 eq_refl eq_refl) as IMGAPr2_5. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPr2_5.
  pose proof (exW_win_blk_apart_h C A14 m14 _ s 4304 r2_5 4 CK HW14 Lo13 eq_refl RRr2_5 GLO1) as WAPr2_5.
  assert (Fr2_5 : live A0 (Z_to_bv 64 r2_5) = None).
  { destruct (live A0 (Z_to_bv 64 r2_5)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB13 _ _ EE) as XX. first [discriminate Fr2_5x | (rewrite Fr2_5x in XX; discriminate XX)]. }
  pose proof Lo13 as Lr2_5_a14.
  assert (SUB14 : sub_live A0 A14).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 r2_5) by (intros ->; rewrite Fr2_5 in Lq; discriminate Lq). rewrite (LEQ13 q NEq). exact (SUB13 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 r2_5 :: [Z_to_bv 64 r2_4; Z_to_bv 64 r2_3; Z_to_bv 64 r2_2; Z_to_bv 64 r2_1; Z_to_bv 64 r2_0; Z_to_bv 64 arr2; Z_to_bv 64 sel2; Z_to_bv 64 r1_3; Z_to_bv 64 r1_2; Z_to_bv 64 r1_1; Z_to_bv 64 r1_0; Z_to_bv 64 arr1; Z_to_bv 64 sel1])) => eq_trans (LEQ13 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL13 q (fun XX => Hq (or_intror XX)))) as LDEL14.
  assert (NE_sel1_r2_5 : Z_to_bv 64 sel1 <> Z_to_bv 64 r2_5) by (intros EE; rewrite EE in Lsel1_a13; rewrite Fr2_5x in Lsel1_a13; discriminate Lsel1_a13).
  assert (Lsel1_a14 : live A14 (Z_to_bv 64 sel1) = Some 32%Z) by (rewrite (LEQ13 _ NE_sel1_r2_5); exact Lsel1_a13).
  pose proof (exW_blk_apart_h C A14 m14 _ sel1 r2_5 32 4 CK HW14 Lsel1_a14 Lr2_5_a14 NE_sel1_r2_5 RRsel1 RRr2_5 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel1_r2_5.
  assert (NE_arr1_r2_5 : Z_to_bv 64 arr1 <> Z_to_bv 64 r2_5) by (intros EE; rewrite EE in Larr1_a13; rewrite Fr2_5x in Larr1_a13; discriminate Larr1_a13).
  assert (Larr1_a14 : live A14 (Z_to_bv 64 arr1) = Some 32%Z) by (rewrite (LEQ13 _ NE_arr1_r2_5); exact Larr1_a13).
  pose proof (exW_blk_apart_h C A14 m14 _ arr1 r2_5 32 4 CK HW14 Larr1_a14 Lr2_5_a14 NE_arr1_r2_5 RRarr1 RRr2_5 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr1_r2_5.
  assert (NE_r1_0_r2_5 : Z_to_bv 64 r1_0 <> Z_to_bv 64 r2_5) by (intros EE; rewrite EE in Lr1_0_a13; rewrite Fr2_5x in Lr1_0_a13; discriminate Lr1_0_a13).
  assert (Lr1_0_a14 : live A14 (Z_to_bv 64 r1_0) = Some 4%Z) by (rewrite (LEQ13 _ NE_r1_0_r2_5); exact Lr1_0_a13).
  pose proof (exW_blk_apart_h C A14 m14 _ r1_0 r2_5 4 4 CK HW14 Lr1_0_a14 Lr2_5_a14 NE_r1_0_r2_5 RRr1_0 RRr2_5 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_0_r2_5.
  assert (NE_r1_1_r2_5 : Z_to_bv 64 r1_1 <> Z_to_bv 64 r2_5) by (intros EE; rewrite EE in Lr1_1_a13; rewrite Fr2_5x in Lr1_1_a13; discriminate Lr1_1_a13).
  assert (Lr1_1_a14 : live A14 (Z_to_bv 64 r1_1) = Some 4%Z) by (rewrite (LEQ13 _ NE_r1_1_r2_5); exact Lr1_1_a13).
  pose proof (exW_blk_apart_h C A14 m14 _ r1_1 r2_5 4 4 CK HW14 Lr1_1_a14 Lr2_5_a14 NE_r1_1_r2_5 RRr1_1 RRr2_5 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_1_r2_5.
  assert (NE_r1_2_r2_5 : Z_to_bv 64 r1_2 <> Z_to_bv 64 r2_5) by (intros EE; rewrite EE in Lr1_2_a13; rewrite Fr2_5x in Lr1_2_a13; discriminate Lr1_2_a13).
  assert (Lr1_2_a14 : live A14 (Z_to_bv 64 r1_2) = Some 4%Z) by (rewrite (LEQ13 _ NE_r1_2_r2_5); exact Lr1_2_a13).
  pose proof (exW_blk_apart_h C A14 m14 _ r1_2 r2_5 4 4 CK HW14 Lr1_2_a14 Lr2_5_a14 NE_r1_2_r2_5 RRr1_2 RRr2_5 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_2_r2_5.
  assert (NE_r1_3_r2_5 : Z_to_bv 64 r1_3 <> Z_to_bv 64 r2_5) by (intros EE; rewrite EE in Lr1_3_a13; rewrite Fr2_5x in Lr1_3_a13; discriminate Lr1_3_a13).
  assert (Lr1_3_a14 : live A14 (Z_to_bv 64 r1_3) = Some 4%Z) by (rewrite (LEQ13 _ NE_r1_3_r2_5); exact Lr1_3_a13).
  pose proof (exW_blk_apart_h C A14 m14 _ r1_3 r2_5 4 4 CK HW14 Lr1_3_a14 Lr2_5_a14 NE_r1_3_r2_5 RRr1_3 RRr2_5 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_3_r2_5.
  assert (NE_sel2_r2_5 : Z_to_bv 64 sel2 <> Z_to_bv 64 r2_5) by (intros EE; rewrite EE in Lsel2_a13; rewrite Fr2_5x in Lsel2_a13; discriminate Lsel2_a13).
  assert (Lsel2_a14 : live A14 (Z_to_bv 64 sel2) = Some 32%Z) by (rewrite (LEQ13 _ NE_sel2_r2_5); exact Lsel2_a13).
  pose proof (exW_blk_apart_h C A14 m14 _ sel2 r2_5 32 4 CK HW14 Lsel2_a14 Lr2_5_a14 NE_sel2_r2_5 RRsel2 RRr2_5 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel2_r2_5.
  assert (NE_arr2_r2_5 : Z_to_bv 64 arr2 <> Z_to_bv 64 r2_5) by (intros EE; rewrite EE in Larr2_a13; rewrite Fr2_5x in Larr2_a13; discriminate Larr2_a13).
  assert (Larr2_a14 : live A14 (Z_to_bv 64 arr2) = Some 64%Z) by (rewrite (LEQ13 _ NE_arr2_r2_5); exact Larr2_a13).
  pose proof (exW_blk_apart_h C A14 m14 _ arr2 r2_5 64 4 CK HW14 Larr2_a14 Lr2_5_a14 NE_arr2_r2_5 RRarr2 RRr2_5 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr2_r2_5.
  assert (NE_r2_0_r2_5 : Z_to_bv 64 r2_0 <> Z_to_bv 64 r2_5) by (intros EE; rewrite EE in Lr2_0_a13; rewrite Fr2_5x in Lr2_0_a13; discriminate Lr2_0_a13).
  assert (Lr2_0_a14 : live A14 (Z_to_bv 64 r2_0) = Some 4%Z) by (rewrite (LEQ13 _ NE_r2_0_r2_5); exact Lr2_0_a13).
  pose proof (exW_blk_apart_h C A14 m14 _ r2_0 r2_5 4 4 CK HW14 Lr2_0_a14 Lr2_5_a14 NE_r2_0_r2_5 RRr2_0 RRr2_5 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r2_0_r2_5.
  assert (NE_r2_1_r2_5 : Z_to_bv 64 r2_1 <> Z_to_bv 64 r2_5) by (intros EE; rewrite EE in Lr2_1_a13; rewrite Fr2_5x in Lr2_1_a13; discriminate Lr2_1_a13).
  assert (Lr2_1_a14 : live A14 (Z_to_bv 64 r2_1) = Some 4%Z) by (rewrite (LEQ13 _ NE_r2_1_r2_5); exact Lr2_1_a13).
  pose proof (exW_blk_apart_h C A14 m14 _ r2_1 r2_5 4 4 CK HW14 Lr2_1_a14 Lr2_5_a14 NE_r2_1_r2_5 RRr2_1 RRr2_5 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r2_1_r2_5.
  assert (NE_r2_2_r2_5 : Z_to_bv 64 r2_2 <> Z_to_bv 64 r2_5) by (intros EE; rewrite EE in Lr2_2_a13; rewrite Fr2_5x in Lr2_2_a13; discriminate Lr2_2_a13).
  assert (Lr2_2_a14 : live A14 (Z_to_bv 64 r2_2) = Some 4%Z) by (rewrite (LEQ13 _ NE_r2_2_r2_5); exact Lr2_2_a13).
  pose proof (exW_blk_apart_h C A14 m14 _ r2_2 r2_5 4 4 CK HW14 Lr2_2_a14 Lr2_5_a14 NE_r2_2_r2_5 RRr2_2 RRr2_5 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r2_2_r2_5.
  assert (NE_r2_3_r2_5 : Z_to_bv 64 r2_3 <> Z_to_bv 64 r2_5) by (intros EE; rewrite EE in Lr2_3_a13; rewrite Fr2_5x in Lr2_3_a13; discriminate Lr2_3_a13).
  assert (Lr2_3_a14 : live A14 (Z_to_bv 64 r2_3) = Some 4%Z) by (rewrite (LEQ13 _ NE_r2_3_r2_5); exact Lr2_3_a13).
  pose proof (exW_blk_apart_h C A14 m14 _ r2_3 r2_5 4 4 CK HW14 Lr2_3_a14 Lr2_5_a14 NE_r2_3_r2_5 RRr2_3 RRr2_5 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r2_3_r2_5.
  assert (NE_r2_4_r2_5 : Z_to_bv 64 r2_4 <> Z_to_bv 64 r2_5) by (intros EE; rewrite EE in Lr2_4_a13; rewrite Fr2_5x in Lr2_4_a13; discriminate Lr2_4_a13).
  assert (Lr2_4_a14 : live A14 (Z_to_bv 64 r2_4) = Some 4%Z) by (rewrite (LEQ13 _ NE_r2_4_r2_5); exact Lr2_4_a13).
  pose proof (exW_blk_apart_h C A14 m14 _ r2_4 r2_5 4 4 CK HW14 Lr2_4_a14 Lr2_5_a14 NE_r2_4_r2_5 RRr2_4 RRr2_5 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r2_4_r2_5.
  assert (PM14 : POSTM C A0 s m0 m14).
  { eapply POSTM_trans; [exact PM13|]. eapply POSTM_trans; [exact PMs13|]. apply (POSTM_sub C A0 A13 _ _ _ SUB13).
    apply (POSTM_mono C A13 (s + OFF13) s); [unfold OFF13; lia | exact PMc13]. }
  pose proof (cs_frame_hop C s 4304 OFF13 (-32) (-40) m0 M13 m14 CK (proj1 PMc13) ltac:(lia) ltac:(vm_cast_no_check (eq_refl true)) ltac:(vm_cast_no_check (eq_refl true)) CFs13) as CF14.
  replace (kR - 13 - 1)%Z with (kR - 14)%Z in RM14 by lia. rewrite MG13 in RM14. replace (bR - 13 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 14 * 2 ^ 17)%Z in RM14 by lia.
  assert (KEPT13 : Forall (ex_region_kept E13 M13 m14) [(EVar 32, OFF13, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 32%Z); (EVar 135, 0%Z, 4%Z); (EVar 169, 0%Z, 4%Z); (EVar 203, 0%Z, 4%Z); (EVar 237, 0%Z, 4%Z); (EVar 271, 0%Z, 32%Z); (EVar 305, 0%Z, 64%Z); (EVar 339, 0%Z, 4%Z); (EVar 373, 0%Z, 4%Z); (EVar 407, 0%Z, 4%Z); (EVar 441, 0%Z, 4%Z); (EVar 475, 0%Z, 4%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF13 4304 M13 m14 E13 (EVar 32) CK (proj1 PMc13) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A13 A13 M13 _ M13 m14 E13 (EVar 67) sel1 32 CK HWs13 Lsel1_a13 RRsel1 eq_refl (proj2 PMc13) Lsel1_a13 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A13 A13 M13 _ M13 m14 E13 (EVar 101) arr1 32 CK HWs13 Larr1_a13 RRarr1 eq_refl (proj2 PMc13) Larr1_a13 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A13 A13 M13 _ M13 m14 E13 (EVar 135) r1_0 4 CK HWs13 Lr1_0_a13 RRr1_0 eq_refl (proj2 PMc13) Lr1_0_a13 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A13 A13 M13 _ M13 m14 E13 (EVar 169) r1_1 4 CK HWs13 Lr1_1_a13 RRr1_1 eq_refl (proj2 PMc13) Lr1_1_a13 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A13 A13 M13 _ M13 m14 E13 (EVar 203) r1_2 4 CK HWs13 Lr1_2_a13 RRr1_2 eq_refl (proj2 PMc13) Lr1_2_a13 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A13 A13 M13 _ M13 m14 E13 (EVar 237) r1_3 4 CK HWs13 Lr1_3_a13 RRr1_3 eq_refl (proj2 PMc13) Lr1_3_a13 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A13 A13 M13 _ M13 m14 E13 (EVar 271) sel2 32 CK HWs13 Lsel2_a13 RRsel2 eq_refl (proj2 PMc13) Lsel2_a13 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A13 A13 M13 _ M13 m14 E13 (EVar 305) arr2 64 CK HWs13 Larr2_a13 RRarr2 eq_refl (proj2 PMc13) Larr2_a13 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A13 A13 M13 _ M13 m14 E13 (EVar 339) r2_0 4 CK HWs13 Lr2_0_a13 RRr2_0 eq_refl (proj2 PMc13) Lr2_0_a13 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A13 A13 M13 _ M13 m14 E13 (EVar 373) r2_1 4 CK HWs13 Lr2_1_a13 RRr2_1 eq_refl (proj2 PMc13) Lr2_1_a13 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A13 A13 M13 _ M13 m14 E13 (EVar 407) r2_2 4 CK HWs13 Lr2_2_a13 RRr2_2 eq_refl (proj2 PMc13) Lr2_2_a13 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A13 A13 M13 _ M13 m14 E13 (EVar 441) r2_3 4 CK HWs13 Lr2_3_a13 RRr2_3 eq_refl (proj2 PMc13) Lr2_3_a13 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A13 A13 M13 _ M13 m14 E13 (EVar 475) r2_4 4 CK HWs13 Lr2_4_a13 RRr2_4 eq_refl (proj2 PMc13) Lr2_4_a13 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E13 M13 m14 _ [] _ HKc13 KEPT13) as HKk13.
  match type of HKk13 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E13 m14 kk') in HKk13 end.
  pose proof (regs_ok_agree 477%nat E13 (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) _ _ (vals_app_agree vals13 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa13.
  pose proof (exW_regs_call _ _ _ _ _ HRa13 (ex_regs_ok_junk vals13 r14 [r2_5; exW_canary SEGS 1410112 m14] 477%nat ltac:(vm_cast_no_check (eq_refl 477%nat))) CS13) as HRn14.
  clear HRa13.
  assert (HKa14 : know_ok SEGS (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) m14 _) by (exact (know_ok_agree SEGS 477%nat E13 _ m14 _ (vals_app_agree vals13 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk13)).
  rewrite (fr_denot_agree 477%nat E13 (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) _ fr (vals_app_agree vals13 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r14 ex_r10 (EVar 509) HRn14 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres13)) as HRx14. clear HRn14. rename HRx14 into HRn14.
  clear HR HK Hlf Hms HKc13 HKk13 KEPT13 HC13 HWs13 PMs13 Q10_13 Q11_13 Q1_13 Q2_13 Q4_13 PM13 HW13 PMc13 CS13 SUB13 RM13 MG13 TOP13 LEQ13 Hnz13 Fr2_5x Lo13 OFF13 LDEL13 CF13 CFs13 Lsel1_a13 Larr1_a13 Lr1_0_a13 Lr1_1_a13 Lr1_2_a13 Lr1_3_a13 Lsel2_a13 Larr2_a13 Lr2_0_a13 Lr2_1_a13 Lr2_2_a13 Lr2_3_a13 Lr2_4_a13.
  subst M13. clear log13. clear E13. try clear Rc13. clear KN13.
  lazymatch type of HRn14 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn14 end.
  pose proof (exW_kn_blk SEGS C A14 m14 _ (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) (EVar 509) (EVar 32) r2_5 4 s 4304 65536 1347584 p16_segs CK HW14 Lr2_5_a14 RRr2_5 eq_refl eq_refl eq_refl RS ALr2_5 ZERO13 WAPr2_5 IMGAPr2_5) as HKb14.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) m14) _ _ (ex_kdisj_apart SEGS (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) m14 (EVar 67) (EVar 509) sel1 r2_5 0 32 0 4 eq_refl eq_refl RRsel1 RRr2_5 AP_sel1_r2_5) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) m14) _ _ (ex_kdisj_apart SEGS (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) m14 (EVar 101) (EVar 509) arr1 r2_5 0 32 0 4 eq_refl eq_refl RRarr1 RRr2_5 AP_arr1_r2_5) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) m14) _ _ (ex_kdisj_apart SEGS (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) m14 (EVar 135) (EVar 509) r1_0 r2_5 0 4 0 4 eq_refl eq_refl RRr1_0 RRr2_5 AP_r1_0_r2_5) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) m14) _ _ (ex_kdisj_apart SEGS (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) m14 (EVar 169) (EVar 509) r1_1 r2_5 0 4 0 4 eq_refl eq_refl RRr1_1 RRr2_5 AP_r1_1_r2_5) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) m14) _ _ (ex_kdisj_apart SEGS (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) m14 (EVar 203) (EVar 509) r1_2 r2_5 0 4 0 4 eq_refl eq_refl RRr1_2 RRr2_5 AP_r1_2_r2_5) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) m14) _ _ (ex_kdisj_apart SEGS (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) m14 (EVar 237) (EVar 509) r1_3 r2_5 0 4 0 4 eq_refl eq_refl RRr1_3 RRr2_5 AP_r1_3_r2_5) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) m14) _ _ (ex_kdisj_apart SEGS (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) m14 (EVar 271) (EVar 509) sel2 r2_5 0 32 0 4 eq_refl eq_refl RRsel2 RRr2_5 AP_sel2_r2_5) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) m14) _ _ (ex_kdisj_apart SEGS (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) m14 (EVar 305) (EVar 509) arr2 r2_5 0 64 0 4 eq_refl eq_refl RRarr2 RRr2_5 AP_arr2_r2_5) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) m14) _ _ (ex_kdisj_apart SEGS (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) m14 (EVar 339) (EVar 509) r2_0 r2_5 0 4 0 4 eq_refl eq_refl RRr2_0 RRr2_5 AP_r2_0_r2_5) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) m14) _ _ (ex_kdisj_apart SEGS (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) m14 (EVar 373) (EVar 509) r2_1 r2_5 0 4 0 4 eq_refl eq_refl RRr2_1 RRr2_5 AP_r2_1_r2_5) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) m14) _ _ (ex_kdisj_apart SEGS (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) m14 (EVar 407) (EVar 509) r2_2 r2_5 0 4 0 4 eq_refl eq_refl RRr2_2 RRr2_5 AP_r2_2_r2_5) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) m14) _ _ (ex_kdisj_apart SEGS (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) m14 (EVar 441) (EVar 509) r2_3 r2_5 0 4 0 4 eq_refl eq_refl RRr2_3 RRr2_5 AP_r2_3_r2_5) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) m14) _ _ (ex_kdisj_apart SEGS (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) m14 (EVar 475) (EVar 509) r2_4 r2_5 0 4 0 4 eq_refl eq_refl RRr2_4 RRr2_5 AP_r2_4_r2_5) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) m14))))))))))))))) as HKd14.
  pose proof (W_sok_win C A14 m14 _ (s - 4304) (Z.to_nat 4304) CK HW14 GLO1 GLO2) as SOK14.
  pose proof (exW_canary_ok SEGS 1410112 m14 (canary_any m14)) as CANOK14.
  pose (vals14 := vals13 ++ map (getr r14) ex_regs_list ++ map (Z_to_bv 64) [r2_5; exW_canary SEGS 1410112 m14]).
  pose proof (exW_kn_fixed SEGS C A14 m14 _ (ex_envL vals13 r14 [r2_5; exW_canary SEGS 1410112 m14]) (EVar 510) (EVar 32) (exW_canary SEGS 1410112 m14) s 4304 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW14 eq_refl (proj1 CANOK14) (proj2 CANOK14) eq_refl eq_refl eq_refl SOK14 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf14.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb14 (proj2 (Forall_app _ _ _) (conj HKd14 (proj2 (Forall_app _ _ _) (conj HKf14 HKa14)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn14 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN14 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb14 HKd14 HKf14 HKa14 SOK14 CANOK14.
  repeat match goal with H : getr r14 _ = _ |- _ => clear H end.
  exq_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO13 ALr2_5.
  exb_exit ST Rc14 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E14 := EEx) in HR, Hlf, HK, Hms |- *; set (log14 := LLx) in Hms, Hlf; set (M14 := mem_denot E14 m14 log14) in Hms end.
  assert (WP14 : W C A14 M14 (with_vmmaps vm14 md) /\ POSTM C A0 s m14 M14).
  { subst M14. apply (exW_win_blks C A14 A0 m14 _ E14 log14 (EVar 32) s 4304 [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z); (EVar 135, r1_0, 4%Z); (EVar 169, r1_1, 4%Z); (EVar 203, r1_2, 4%Z); (EVar 237, r1_3, 4%Z); (EVar 271, sel2, 32%Z); (EVar 305, arr2, 64%Z); (EVar 339, r2_0, 4%Z); (EVar 373, r2_1, 4%Z); (EVar 407, r2_2, 4%Z); (EVar 441, r2_3, 4%Z); (EVar 475, r2_4, 4%Z); (EVar 509, r2_5, 4%Z)] CK HW14 SUB14 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a14 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a14 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a14 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRr1_1 (conj Lr1_1_a14 (conj Fr1_1 F0r1_1))))|]. constructor; [exact (conj eq_refl (conj RRr1_2 (conj Lr1_2_a14 (conj Fr1_2 F0r1_2))))|]. constructor; [exact (conj eq_refl (conj RRr1_3 (conj Lr1_3_a14 (conj Fr1_3 F0r1_3))))|]. constructor; [exact (conj eq_refl (conj RRsel2 (conj Lsel2_a14 (conj Fsel2 F0sel2))))|]. constructor; [exact (conj eq_refl (conj RRarr2 (conj Larr2_a14 (conj Farr2 F0arr2))))|]. constructor; [exact (conj eq_refl (conj RRr2_0 (conj Lr2_0_a14 (conj Fr2_0 F0r2_0))))|]. constructor; [exact (conj eq_refl (conj RRr2_1 (conj Lr2_1_a14 (conj Fr2_1 F0r2_1))))|]. constructor; [exact (conj eq_refl (conj RRr2_2 (conj Lr2_2_a14 (conj Fr2_2 F0r2_2))))|]. constructor; [exact (conj eq_refl (conj RRr2_3 (conj Lr2_3_a14 (conj Fr2_3 F0r2_3))))|]. constructor; [exact (conj eq_refl (conj RRr2_4 (conj Lr2_4_a14 (conj Fr2_4 F0r2_4))))|]. constructor; [exact (conj eq_refl (conj RRr2_5 (conj Lr2_5_a14 (conj Fr2_5 F0r2_5))))|]. constructor. }
  assert (CFs14 : O23LeptCselsA.cs_fra s (-32) (-40) m0 M14).
  { subst M14. apply (cs_frame_sess C A14 A0 m0 m14 _ E14 log14 (EVar 32) s 4304 (-32) (-40) [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z); (EVar 135, r1_0, 4%Z); (EVar 169, r1_1, 4%Z); (EVar 203, r1_2, 4%Z); (EVar 237, r1_3, 4%Z); (EVar 271, sel2, 32%Z); (EVar 305, arr2, 64%Z); (EVar 339, r2_0, 4%Z); (EVar 373, r2_1, 4%Z); (EVar 407, r2_2, 4%Z); (EVar 441, r2_3, 4%Z); (EVar 475, r2_4, 4%Z); (EVar 509, r2_5, 4%Z)] CK HW14 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exact RS | lia | exact Hhi | reflexivity | | reflexivity | exact CF14]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a14 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a14 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a14 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRr1_1 (conj Lr1_1_a14 (conj Fr1_1 F0r1_1))))|]. constructor; [exact (conj eq_refl (conj RRr1_2 (conj Lr1_2_a14 (conj Fr1_2 F0r1_2))))|]. constructor; [exact (conj eq_refl (conj RRr1_3 (conj Lr1_3_a14 (conj Fr1_3 F0r1_3))))|]. constructor; [exact (conj eq_refl (conj RRsel2 (conj Lsel2_a14 (conj Fsel2 F0sel2))))|]. constructor; [exact (conj eq_refl (conj RRarr2 (conj Larr2_a14 (conj Farr2 F0arr2))))|]. constructor; [exact (conj eq_refl (conj RRr2_0 (conj Lr2_0_a14 (conj Fr2_0 F0r2_0))))|]. constructor; [exact (conj eq_refl (conj RRr2_1 (conj Lr2_1_a14 (conj Fr2_1 F0r2_1))))|]. constructor; [exact (conj eq_refl (conj RRr2_2 (conj Lr2_2_a14 (conj Fr2_2 F0r2_2))))|]. constructor; [exact (conj eq_refl (conj RRr2_3 (conj Lr2_3_a14 (conj Fr2_3 F0r2_3))))|]. constructor; [exact (conj eq_refl (conj RRr2_4 (conj Lr2_4_a14 (conj Fr2_4 F0r2_4))))|]. constructor; [exact (conj eq_refl (conj RRr2_5 (conj Lr2_5_a14 (conj Fr2_5 F0r2_5))))|]. constructor. }
  destruct WP14 as [HWs14 PMs14].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log14 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC14 : carry log14 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc14 : know_ok SEGS E14 M14 kn1) by (apply (carry_after SEGS E14 m14 log14 kn0 [] kn1 scs hs HC14 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW14)) | exact (mp_lazy _ (w_pure _ _ _ _ HW14)) | exact Hms |].
  pose (BS14 := [(32%nat, s); (67%nat, sel1); (101%nat, arr1); (135%nat, r1_0); (169%nat, r1_1); (203%nat, r1_2); (237%nat, r1_3); (271%nat, sel2); (305%nat, arr2); (339%nat, r2_0); (373%nat, r2_1); (407%nat, r2_2); (441%nat, r2_3); (475%nat, r2_4); (509%nat, r2_5)]).
  exW_regfactB BS14 HR ex_r10 Q10_14. exW_regfactB BS14 HR ex_r11 Q11_14. exW_regfactB BS14 HR ex_r1 Q1_14. exW_regfactB BS14 HR ex_r2 Q2_14. exW_regfactB BS14 HR ex_r4 Q4_14.
  clear BS14.
  lazymatch type of Q2_14 with _ = Z_to_bv 64 (s + ?off) => pose (OFF14 := off) end.
  pose proof (alloc_margin_small (1 * 4) ltac:(exW_cmp)) as MG14.
  lazymatch type of Q1_14 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_14 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A14 M14 _ Rc14 1 4 (kR - 14) (bR - 14 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs14 Q10_14 Q11_14 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM14) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_14
             ltac:(red; apply bv_eq; reflexivity) Q4_14 Q2_14 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A15 m15 vm15 r15 res14 HW15 Hres14 CSx14 Hnz14 Fr2_6x Lo14 F0r2_6 LEQ14 ZERO14 ALr2_6 TOP14 PMc14 RM15.
  pose proof CSx14 as CS14. clear CSx14.
  rewrite with_vmmaps_twice in HW15 |- *.
  assert (Eres14 : res14 = Z_to_bv 64 (u res14)) by (symmetry; apply zbv_self).
  pose proof (u64_range res14) as RRr2_6. set (r2_6 := u res14) in *. clearbody r2_6. rewrite Eres14 in Hres14, Fr2_6x, Lo14, F0r2_6, LEQ14, ZERO14. clear Eres14.
  change (1 * 4)%Z with 4%Z in *.
  pose proof (exW_blk_img_apart_h2 C A15 m15 _ r2_6 4 CK HW15 Lo14 RRr2_6 eq_refl eq_refl) as IMGAPr2_6. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPr2_6.
  pose proof (exW_win_blk_apart_h C A15 m15 _ s 4304 r2_6 4 CK HW15 Lo14 eq_refl RRr2_6 GLO1) as WAPr2_6.
  assert (Fr2_6 : live A0 (Z_to_bv 64 r2_6) = None).
  { destruct (live A0 (Z_to_bv 64 r2_6)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB14 _ _ EE) as XX. first [discriminate Fr2_6x | (rewrite Fr2_6x in XX; discriminate XX)]. }
  pose proof Lo14 as Lr2_6_a15.
  assert (SUB15 : sub_live A0 A15).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 r2_6) by (intros ->; rewrite Fr2_6 in Lq; discriminate Lq). rewrite (LEQ14 q NEq). exact (SUB14 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 r2_6 :: [Z_to_bv 64 r2_5; Z_to_bv 64 r2_4; Z_to_bv 64 r2_3; Z_to_bv 64 r2_2; Z_to_bv 64 r2_1; Z_to_bv 64 r2_0; Z_to_bv 64 arr2; Z_to_bv 64 sel2; Z_to_bv 64 r1_3; Z_to_bv 64 r1_2; Z_to_bv 64 r1_1; Z_to_bv 64 r1_0; Z_to_bv 64 arr1; Z_to_bv 64 sel1])) => eq_trans (LEQ14 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL14 q (fun XX => Hq (or_intror XX)))) as LDEL15.
  assert (NE_sel1_r2_6 : Z_to_bv 64 sel1 <> Z_to_bv 64 r2_6) by (intros EE; rewrite EE in Lsel1_a14; rewrite Fr2_6x in Lsel1_a14; discriminate Lsel1_a14).
  assert (Lsel1_a15 : live A15 (Z_to_bv 64 sel1) = Some 32%Z) by (rewrite (LEQ14 _ NE_sel1_r2_6); exact Lsel1_a14).
  pose proof (exW_blk_apart_h C A15 m15 _ sel1 r2_6 32 4 CK HW15 Lsel1_a15 Lr2_6_a15 NE_sel1_r2_6 RRsel1 RRr2_6 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel1_r2_6.
  assert (NE_arr1_r2_6 : Z_to_bv 64 arr1 <> Z_to_bv 64 r2_6) by (intros EE; rewrite EE in Larr1_a14; rewrite Fr2_6x in Larr1_a14; discriminate Larr1_a14).
  assert (Larr1_a15 : live A15 (Z_to_bv 64 arr1) = Some 32%Z) by (rewrite (LEQ14 _ NE_arr1_r2_6); exact Larr1_a14).
  pose proof (exW_blk_apart_h C A15 m15 _ arr1 r2_6 32 4 CK HW15 Larr1_a15 Lr2_6_a15 NE_arr1_r2_6 RRarr1 RRr2_6 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr1_r2_6.
  assert (NE_r1_0_r2_6 : Z_to_bv 64 r1_0 <> Z_to_bv 64 r2_6) by (intros EE; rewrite EE in Lr1_0_a14; rewrite Fr2_6x in Lr1_0_a14; discriminate Lr1_0_a14).
  assert (Lr1_0_a15 : live A15 (Z_to_bv 64 r1_0) = Some 4%Z) by (rewrite (LEQ14 _ NE_r1_0_r2_6); exact Lr1_0_a14).
  pose proof (exW_blk_apart_h C A15 m15 _ r1_0 r2_6 4 4 CK HW15 Lr1_0_a15 Lr2_6_a15 NE_r1_0_r2_6 RRr1_0 RRr2_6 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_0_r2_6.
  assert (NE_r1_1_r2_6 : Z_to_bv 64 r1_1 <> Z_to_bv 64 r2_6) by (intros EE; rewrite EE in Lr1_1_a14; rewrite Fr2_6x in Lr1_1_a14; discriminate Lr1_1_a14).
  assert (Lr1_1_a15 : live A15 (Z_to_bv 64 r1_1) = Some 4%Z) by (rewrite (LEQ14 _ NE_r1_1_r2_6); exact Lr1_1_a14).
  pose proof (exW_blk_apart_h C A15 m15 _ r1_1 r2_6 4 4 CK HW15 Lr1_1_a15 Lr2_6_a15 NE_r1_1_r2_6 RRr1_1 RRr2_6 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_1_r2_6.
  assert (NE_r1_2_r2_6 : Z_to_bv 64 r1_2 <> Z_to_bv 64 r2_6) by (intros EE; rewrite EE in Lr1_2_a14; rewrite Fr2_6x in Lr1_2_a14; discriminate Lr1_2_a14).
  assert (Lr1_2_a15 : live A15 (Z_to_bv 64 r1_2) = Some 4%Z) by (rewrite (LEQ14 _ NE_r1_2_r2_6); exact Lr1_2_a14).
  pose proof (exW_blk_apart_h C A15 m15 _ r1_2 r2_6 4 4 CK HW15 Lr1_2_a15 Lr2_6_a15 NE_r1_2_r2_6 RRr1_2 RRr2_6 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_2_r2_6.
  assert (NE_r1_3_r2_6 : Z_to_bv 64 r1_3 <> Z_to_bv 64 r2_6) by (intros EE; rewrite EE in Lr1_3_a14; rewrite Fr2_6x in Lr1_3_a14; discriminate Lr1_3_a14).
  assert (Lr1_3_a15 : live A15 (Z_to_bv 64 r1_3) = Some 4%Z) by (rewrite (LEQ14 _ NE_r1_3_r2_6); exact Lr1_3_a14).
  pose proof (exW_blk_apart_h C A15 m15 _ r1_3 r2_6 4 4 CK HW15 Lr1_3_a15 Lr2_6_a15 NE_r1_3_r2_6 RRr1_3 RRr2_6 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_3_r2_6.
  assert (NE_sel2_r2_6 : Z_to_bv 64 sel2 <> Z_to_bv 64 r2_6) by (intros EE; rewrite EE in Lsel2_a14; rewrite Fr2_6x in Lsel2_a14; discriminate Lsel2_a14).
  assert (Lsel2_a15 : live A15 (Z_to_bv 64 sel2) = Some 32%Z) by (rewrite (LEQ14 _ NE_sel2_r2_6); exact Lsel2_a14).
  pose proof (exW_blk_apart_h C A15 m15 _ sel2 r2_6 32 4 CK HW15 Lsel2_a15 Lr2_6_a15 NE_sel2_r2_6 RRsel2 RRr2_6 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel2_r2_6.
  assert (NE_arr2_r2_6 : Z_to_bv 64 arr2 <> Z_to_bv 64 r2_6) by (intros EE; rewrite EE in Larr2_a14; rewrite Fr2_6x in Larr2_a14; discriminate Larr2_a14).
  assert (Larr2_a15 : live A15 (Z_to_bv 64 arr2) = Some 64%Z) by (rewrite (LEQ14 _ NE_arr2_r2_6); exact Larr2_a14).
  pose proof (exW_blk_apart_h C A15 m15 _ arr2 r2_6 64 4 CK HW15 Larr2_a15 Lr2_6_a15 NE_arr2_r2_6 RRarr2 RRr2_6 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr2_r2_6.
  assert (NE_r2_0_r2_6 : Z_to_bv 64 r2_0 <> Z_to_bv 64 r2_6) by (intros EE; rewrite EE in Lr2_0_a14; rewrite Fr2_6x in Lr2_0_a14; discriminate Lr2_0_a14).
  assert (Lr2_0_a15 : live A15 (Z_to_bv 64 r2_0) = Some 4%Z) by (rewrite (LEQ14 _ NE_r2_0_r2_6); exact Lr2_0_a14).
  pose proof (exW_blk_apart_h C A15 m15 _ r2_0 r2_6 4 4 CK HW15 Lr2_0_a15 Lr2_6_a15 NE_r2_0_r2_6 RRr2_0 RRr2_6 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r2_0_r2_6.
  assert (NE_r2_1_r2_6 : Z_to_bv 64 r2_1 <> Z_to_bv 64 r2_6) by (intros EE; rewrite EE in Lr2_1_a14; rewrite Fr2_6x in Lr2_1_a14; discriminate Lr2_1_a14).
  assert (Lr2_1_a15 : live A15 (Z_to_bv 64 r2_1) = Some 4%Z) by (rewrite (LEQ14 _ NE_r2_1_r2_6); exact Lr2_1_a14).
  pose proof (exW_blk_apart_h C A15 m15 _ r2_1 r2_6 4 4 CK HW15 Lr2_1_a15 Lr2_6_a15 NE_r2_1_r2_6 RRr2_1 RRr2_6 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r2_1_r2_6.
  assert (NE_r2_2_r2_6 : Z_to_bv 64 r2_2 <> Z_to_bv 64 r2_6) by (intros EE; rewrite EE in Lr2_2_a14; rewrite Fr2_6x in Lr2_2_a14; discriminate Lr2_2_a14).
  assert (Lr2_2_a15 : live A15 (Z_to_bv 64 r2_2) = Some 4%Z) by (rewrite (LEQ14 _ NE_r2_2_r2_6); exact Lr2_2_a14).
  pose proof (exW_blk_apart_h C A15 m15 _ r2_2 r2_6 4 4 CK HW15 Lr2_2_a15 Lr2_6_a15 NE_r2_2_r2_6 RRr2_2 RRr2_6 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r2_2_r2_6.
  assert (NE_r2_3_r2_6 : Z_to_bv 64 r2_3 <> Z_to_bv 64 r2_6) by (intros EE; rewrite EE in Lr2_3_a14; rewrite Fr2_6x in Lr2_3_a14; discriminate Lr2_3_a14).
  assert (Lr2_3_a15 : live A15 (Z_to_bv 64 r2_3) = Some 4%Z) by (rewrite (LEQ14 _ NE_r2_3_r2_6); exact Lr2_3_a14).
  pose proof (exW_blk_apart_h C A15 m15 _ r2_3 r2_6 4 4 CK HW15 Lr2_3_a15 Lr2_6_a15 NE_r2_3_r2_6 RRr2_3 RRr2_6 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r2_3_r2_6.
  assert (NE_r2_4_r2_6 : Z_to_bv 64 r2_4 <> Z_to_bv 64 r2_6) by (intros EE; rewrite EE in Lr2_4_a14; rewrite Fr2_6x in Lr2_4_a14; discriminate Lr2_4_a14).
  assert (Lr2_4_a15 : live A15 (Z_to_bv 64 r2_4) = Some 4%Z) by (rewrite (LEQ14 _ NE_r2_4_r2_6); exact Lr2_4_a14).
  pose proof (exW_blk_apart_h C A15 m15 _ r2_4 r2_6 4 4 CK HW15 Lr2_4_a15 Lr2_6_a15 NE_r2_4_r2_6 RRr2_4 RRr2_6 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r2_4_r2_6.
  assert (NE_r2_5_r2_6 : Z_to_bv 64 r2_5 <> Z_to_bv 64 r2_6) by (intros EE; rewrite EE in Lr2_5_a14; rewrite Fr2_6x in Lr2_5_a14; discriminate Lr2_5_a14).
  assert (Lr2_5_a15 : live A15 (Z_to_bv 64 r2_5) = Some 4%Z) by (rewrite (LEQ14 _ NE_r2_5_r2_6); exact Lr2_5_a14).
  pose proof (exW_blk_apart_h C A15 m15 _ r2_5 r2_6 4 4 CK HW15 Lr2_5_a15 Lr2_6_a15 NE_r2_5_r2_6 RRr2_5 RRr2_6 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r2_5_r2_6.
  assert (PM15 : POSTM C A0 s m0 m15).
  { eapply POSTM_trans; [exact PM14|]. eapply POSTM_trans; [exact PMs14|]. apply (POSTM_sub C A0 A14 _ _ _ SUB14).
    apply (POSTM_mono C A14 (s + OFF14) s); [unfold OFF14; lia | exact PMc14]. }
  pose proof (cs_frame_hop C s 4304 OFF14 (-32) (-40) m0 M14 m15 CK (proj1 PMc14) ltac:(lia) ltac:(vm_cast_no_check (eq_refl true)) ltac:(vm_cast_no_check (eq_refl true)) CFs14) as CF15.
  replace (kR - 14 - 1)%Z with (kR - 15)%Z in RM15 by lia. rewrite MG14 in RM15. replace (bR - 14 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 15 * 2 ^ 17)%Z in RM15 by lia.
  assert (KEPT14 : Forall (ex_region_kept E14 M14 m15) [(EVar 32, OFF14, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 32%Z); (EVar 135, 0%Z, 4%Z); (EVar 169, 0%Z, 4%Z); (EVar 203, 0%Z, 4%Z); (EVar 237, 0%Z, 4%Z); (EVar 271, 0%Z, 32%Z); (EVar 305, 0%Z, 64%Z); (EVar 339, 0%Z, 4%Z); (EVar 373, 0%Z, 4%Z); (EVar 407, 0%Z, 4%Z); (EVar 441, 0%Z, 4%Z); (EVar 475, 0%Z, 4%Z); (EVar 509, 0%Z, 4%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF14 4304 M14 m15 E14 (EVar 32) CK (proj1 PMc14) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A14 A14 M14 _ M14 m15 E14 (EVar 67) sel1 32 CK HWs14 Lsel1_a14 RRsel1 eq_refl (proj2 PMc14) Lsel1_a14 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A14 A14 M14 _ M14 m15 E14 (EVar 101) arr1 32 CK HWs14 Larr1_a14 RRarr1 eq_refl (proj2 PMc14) Larr1_a14 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A14 A14 M14 _ M14 m15 E14 (EVar 135) r1_0 4 CK HWs14 Lr1_0_a14 RRr1_0 eq_refl (proj2 PMc14) Lr1_0_a14 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A14 A14 M14 _ M14 m15 E14 (EVar 169) r1_1 4 CK HWs14 Lr1_1_a14 RRr1_1 eq_refl (proj2 PMc14) Lr1_1_a14 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A14 A14 M14 _ M14 m15 E14 (EVar 203) r1_2 4 CK HWs14 Lr1_2_a14 RRr1_2 eq_refl (proj2 PMc14) Lr1_2_a14 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A14 A14 M14 _ M14 m15 E14 (EVar 237) r1_3 4 CK HWs14 Lr1_3_a14 RRr1_3 eq_refl (proj2 PMc14) Lr1_3_a14 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A14 A14 M14 _ M14 m15 E14 (EVar 271) sel2 32 CK HWs14 Lsel2_a14 RRsel2 eq_refl (proj2 PMc14) Lsel2_a14 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A14 A14 M14 _ M14 m15 E14 (EVar 305) arr2 64 CK HWs14 Larr2_a14 RRarr2 eq_refl (proj2 PMc14) Larr2_a14 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A14 A14 M14 _ M14 m15 E14 (EVar 339) r2_0 4 CK HWs14 Lr2_0_a14 RRr2_0 eq_refl (proj2 PMc14) Lr2_0_a14 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A14 A14 M14 _ M14 m15 E14 (EVar 373) r2_1 4 CK HWs14 Lr2_1_a14 RRr2_1 eq_refl (proj2 PMc14) Lr2_1_a14 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A14 A14 M14 _ M14 m15 E14 (EVar 407) r2_2 4 CK HWs14 Lr2_2_a14 RRr2_2 eq_refl (proj2 PMc14) Lr2_2_a14 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A14 A14 M14 _ M14 m15 E14 (EVar 441) r2_3 4 CK HWs14 Lr2_3_a14 RRr2_3 eq_refl (proj2 PMc14) Lr2_3_a14 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A14 A14 M14 _ M14 m15 E14 (EVar 475) r2_4 4 CK HWs14 Lr2_4_a14 RRr2_4 eq_refl (proj2 PMc14) Lr2_4_a14 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A14 A14 M14 _ M14 m15 E14 (EVar 509) r2_5 4 CK HWs14 Lr2_5_a14 RRr2_5 eq_refl (proj2 PMc14) Lr2_5_a14 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E14 M14 m15 _ [] _ HKc14 KEPT14) as HKk14.
  match type of HKk14 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E14 m15 kk') in HKk14 end.
  pose proof (regs_ok_agree 511%nat E14 (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) _ _ (vals_app_agree vals14 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa14.
  pose proof (exW_regs_call _ _ _ _ _ HRa14 (ex_regs_ok_junk vals14 r15 [r2_6; exW_canary SEGS 1410112 m15] 511%nat ltac:(vm_cast_no_check (eq_refl 511%nat))) CS14) as HRn15.
  clear HRa14.
  assert (HKa15 : know_ok SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15 _) by (exact (know_ok_agree SEGS 511%nat E14 _ m15 _ (vals_app_agree vals14 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk14)).
  rewrite (fr_denot_agree 511%nat E14 (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) _ fr (vals_app_agree vals14 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r15 ex_r10 (EVar 543) HRn15 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres14)) as HRx15. clear HRn15. rename HRx15 into HRn15.
  clear HR HK Hlf Hms HKc14 HKk14 KEPT14 HC14 HWs14 PMs14 Q10_14 Q11_14 Q1_14 Q2_14 Q4_14 PM14 HW14 PMc14 CS14 SUB14 RM14 MG14 TOP14 LEQ14 Hnz14 Fr2_6x Lo14 OFF14 LDEL14 CF14 CFs14 Lsel1_a14 Larr1_a14 Lr1_0_a14 Lr1_1_a14 Lr1_2_a14 Lr1_3_a14 Lsel2_a14 Larr2_a14 Lr2_0_a14 Lr2_1_a14 Lr2_2_a14 Lr2_3_a14 Lr2_4_a14 Lr2_5_a14.
  subst M14. clear log14. clear E14. try clear Rc14. clear KN14.
  lazymatch type of HRn15 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn15 end.
  pose proof (exW_kn_blk SEGS C A15 m15 _ (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) (EVar 543) (EVar 32) r2_6 4 s 4304 65536 1347584 p16_segs CK HW15 Lr2_6_a15 RRr2_6 eq_refl eq_refl eq_refl RS ALr2_6 ZERO14 WAPr2_6 IMGAPr2_6) as HKb15.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15) _ _ (ex_kdisj_apart SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15 (EVar 67) (EVar 543) sel1 r2_6 0 32 0 4 eq_refl eq_refl RRsel1 RRr2_6 AP_sel1_r2_6) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15) _ _ (ex_kdisj_apart SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15 (EVar 101) (EVar 543) arr1 r2_6 0 32 0 4 eq_refl eq_refl RRarr1 RRr2_6 AP_arr1_r2_6) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15) _ _ (ex_kdisj_apart SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15 (EVar 135) (EVar 543) r1_0 r2_6 0 4 0 4 eq_refl eq_refl RRr1_0 RRr2_6 AP_r1_0_r2_6) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15) _ _ (ex_kdisj_apart SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15 (EVar 169) (EVar 543) r1_1 r2_6 0 4 0 4 eq_refl eq_refl RRr1_1 RRr2_6 AP_r1_1_r2_6) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15) _ _ (ex_kdisj_apart SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15 (EVar 203) (EVar 543) r1_2 r2_6 0 4 0 4 eq_refl eq_refl RRr1_2 RRr2_6 AP_r1_2_r2_6) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15) _ _ (ex_kdisj_apart SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15 (EVar 237) (EVar 543) r1_3 r2_6 0 4 0 4 eq_refl eq_refl RRr1_3 RRr2_6 AP_r1_3_r2_6) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15) _ _ (ex_kdisj_apart SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15 (EVar 271) (EVar 543) sel2 r2_6 0 32 0 4 eq_refl eq_refl RRsel2 RRr2_6 AP_sel2_r2_6) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15) _ _ (ex_kdisj_apart SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15 (EVar 305) (EVar 543) arr2 r2_6 0 64 0 4 eq_refl eq_refl RRarr2 RRr2_6 AP_arr2_r2_6) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15) _ _ (ex_kdisj_apart SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15 (EVar 339) (EVar 543) r2_0 r2_6 0 4 0 4 eq_refl eq_refl RRr2_0 RRr2_6 AP_r2_0_r2_6) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15) _ _ (ex_kdisj_apart SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15 (EVar 373) (EVar 543) r2_1 r2_6 0 4 0 4 eq_refl eq_refl RRr2_1 RRr2_6 AP_r2_1_r2_6) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15) _ _ (ex_kdisj_apart SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15 (EVar 407) (EVar 543) r2_2 r2_6 0 4 0 4 eq_refl eq_refl RRr2_2 RRr2_6 AP_r2_2_r2_6) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15) _ _ (ex_kdisj_apart SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15 (EVar 441) (EVar 543) r2_3 r2_6 0 4 0 4 eq_refl eq_refl RRr2_3 RRr2_6 AP_r2_3_r2_6) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15) _ _ (ex_kdisj_apart SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15 (EVar 475) (EVar 543) r2_4 r2_6 0 4 0 4 eq_refl eq_refl RRr2_4 RRr2_6 AP_r2_4_r2_6) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15) _ _ (ex_kdisj_apart SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15 (EVar 509) (EVar 543) r2_5 r2_6 0 4 0 4 eq_refl eq_refl RRr2_5 RRr2_6 AP_r2_5_r2_6) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) m15)))))))))))))))) as HKd15.
  pose proof (W_sok_win C A15 m15 _ (s - 4304) (Z.to_nat 4304) CK HW15 GLO1 GLO2) as SOK15.
  pose proof (exW_canary_ok SEGS 1410112 m15 (canary_any m15)) as CANOK15.
  pose (vals15 := vals14 ++ map (getr r15) ex_regs_list ++ map (Z_to_bv 64) [r2_6; exW_canary SEGS 1410112 m15]).
  pose proof (exW_kn_fixed SEGS C A15 m15 _ (ex_envL vals14 r15 [r2_6; exW_canary SEGS 1410112 m15]) (EVar 544) (EVar 32) (exW_canary SEGS 1410112 m15) s 4304 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW15 eq_refl (proj1 CANOK15) (proj2 CANOK15) eq_refl eq_refl eq_refl SOK15 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf15.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb15 (proj2 (Forall_app _ _ _) (conj HKd15 (proj2 (Forall_app _ _ _) (conj HKf15 HKa15)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn15 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN15 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb15 HKd15 HKf15 HKa15 SOK15 CANOK15.
  repeat match goal with H : getr r15 _ = _ |- _ => clear H end.
  exq_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO14 ALr2_6.
  exb_exit ST Rc15 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E15 := EEx) in HR, Hlf, HK, Hms |- *; set (log15 := LLx) in Hms, Hlf; set (M15 := mem_denot E15 m15 log15) in Hms end.
  assert (WP15 : W C A15 M15 (with_vmmaps vm15 md) /\ POSTM C A0 s m15 M15).
  { subst M15. apply (exW_win_blks C A15 A0 m15 _ E15 log15 (EVar 32) s 4304 [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z); (EVar 135, r1_0, 4%Z); (EVar 169, r1_1, 4%Z); (EVar 203, r1_2, 4%Z); (EVar 237, r1_3, 4%Z); (EVar 271, sel2, 32%Z); (EVar 305, arr2, 64%Z); (EVar 339, r2_0, 4%Z); (EVar 373, r2_1, 4%Z); (EVar 407, r2_2, 4%Z); (EVar 441, r2_3, 4%Z); (EVar 475, r2_4, 4%Z); (EVar 509, r2_5, 4%Z); (EVar 543, r2_6, 4%Z)] CK HW15 SUB15 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a15 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a15 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a15 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRr1_1 (conj Lr1_1_a15 (conj Fr1_1 F0r1_1))))|]. constructor; [exact (conj eq_refl (conj RRr1_2 (conj Lr1_2_a15 (conj Fr1_2 F0r1_2))))|]. constructor; [exact (conj eq_refl (conj RRr1_3 (conj Lr1_3_a15 (conj Fr1_3 F0r1_3))))|]. constructor; [exact (conj eq_refl (conj RRsel2 (conj Lsel2_a15 (conj Fsel2 F0sel2))))|]. constructor; [exact (conj eq_refl (conj RRarr2 (conj Larr2_a15 (conj Farr2 F0arr2))))|]. constructor; [exact (conj eq_refl (conj RRr2_0 (conj Lr2_0_a15 (conj Fr2_0 F0r2_0))))|]. constructor; [exact (conj eq_refl (conj RRr2_1 (conj Lr2_1_a15 (conj Fr2_1 F0r2_1))))|]. constructor; [exact (conj eq_refl (conj RRr2_2 (conj Lr2_2_a15 (conj Fr2_2 F0r2_2))))|]. constructor; [exact (conj eq_refl (conj RRr2_3 (conj Lr2_3_a15 (conj Fr2_3 F0r2_3))))|]. constructor; [exact (conj eq_refl (conj RRr2_4 (conj Lr2_4_a15 (conj Fr2_4 F0r2_4))))|]. constructor; [exact (conj eq_refl (conj RRr2_5 (conj Lr2_5_a15 (conj Fr2_5 F0r2_5))))|]. constructor; [exact (conj eq_refl (conj RRr2_6 (conj Lr2_6_a15 (conj Fr2_6 F0r2_6))))|]. constructor. }
  assert (CFs15 : O23LeptCselsA.cs_fra s (-32) (-40) m0 M15).
  { subst M15. apply (cs_frame_sess C A15 A0 m0 m15 _ E15 log15 (EVar 32) s 4304 (-32) (-40) [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z); (EVar 135, r1_0, 4%Z); (EVar 169, r1_1, 4%Z); (EVar 203, r1_2, 4%Z); (EVar 237, r1_3, 4%Z); (EVar 271, sel2, 32%Z); (EVar 305, arr2, 64%Z); (EVar 339, r2_0, 4%Z); (EVar 373, r2_1, 4%Z); (EVar 407, r2_2, 4%Z); (EVar 441, r2_3, 4%Z); (EVar 475, r2_4, 4%Z); (EVar 509, r2_5, 4%Z); (EVar 543, r2_6, 4%Z)] CK HW15 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exact RS | lia | exact Hhi | reflexivity | | reflexivity | exact CF15]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a15 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a15 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a15 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRr1_1 (conj Lr1_1_a15 (conj Fr1_1 F0r1_1))))|]. constructor; [exact (conj eq_refl (conj RRr1_2 (conj Lr1_2_a15 (conj Fr1_2 F0r1_2))))|]. constructor; [exact (conj eq_refl (conj RRr1_3 (conj Lr1_3_a15 (conj Fr1_3 F0r1_3))))|]. constructor; [exact (conj eq_refl (conj RRsel2 (conj Lsel2_a15 (conj Fsel2 F0sel2))))|]. constructor; [exact (conj eq_refl (conj RRarr2 (conj Larr2_a15 (conj Farr2 F0arr2))))|]. constructor; [exact (conj eq_refl (conj RRr2_0 (conj Lr2_0_a15 (conj Fr2_0 F0r2_0))))|]. constructor; [exact (conj eq_refl (conj RRr2_1 (conj Lr2_1_a15 (conj Fr2_1 F0r2_1))))|]. constructor; [exact (conj eq_refl (conj RRr2_2 (conj Lr2_2_a15 (conj Fr2_2 F0r2_2))))|]. constructor; [exact (conj eq_refl (conj RRr2_3 (conj Lr2_3_a15 (conj Fr2_3 F0r2_3))))|]. constructor; [exact (conj eq_refl (conj RRr2_4 (conj Lr2_4_a15 (conj Fr2_4 F0r2_4))))|]. constructor; [exact (conj eq_refl (conj RRr2_5 (conj Lr2_5_a15 (conj Fr2_5 F0r2_5))))|]. constructor; [exact (conj eq_refl (conj RRr2_6 (conj Lr2_6_a15 (conj Fr2_6 F0r2_6))))|]. constructor. }
  destruct WP15 as [HWs15 PMs15].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log15 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC15 : carry log15 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc15 : know_ok SEGS E15 M15 kn1) by (apply (carry_after SEGS E15 m15 log15 kn0 [] kn1 scs hs HC15 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW15)) | exact (mp_lazy _ (w_pure _ _ _ _ HW15)) | exact Hms |].
  pose (BS15 := [(32%nat, s); (67%nat, sel1); (101%nat, arr1); (135%nat, r1_0); (169%nat, r1_1); (203%nat, r1_2); (237%nat, r1_3); (271%nat, sel2); (305%nat, arr2); (339%nat, r2_0); (373%nat, r2_1); (407%nat, r2_2); (441%nat, r2_3); (475%nat, r2_4); (509%nat, r2_5); (543%nat, r2_6)]).
  exW_regfactB BS15 HR ex_r10 Q10_15. exW_regfactB BS15 HR ex_r11 Q11_15. exW_regfactB BS15 HR ex_r1 Q1_15. exW_regfactB BS15 HR ex_r2 Q2_15. exW_regfactB BS15 HR ex_r4 Q4_15.
  clear BS15.
  lazymatch type of Q2_15 with _ = Z_to_bv 64 (s + ?off) => pose (OFF15 := off) end.
  pose proof (alloc_margin_small (1 * 4) ltac:(exW_cmp)) as MG15.
  lazymatch type of Q1_15 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_15 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A15 M15 _ Rc15 1 4 (kR - 15) (bR - 15 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs15 Q10_15 Q11_15 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM15) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_15
             ltac:(red; apply bv_eq; reflexivity) Q4_15 Q2_15 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A16 m16 vm16 r16 res15 HW16 Hres15 CSx15 Hnz15 Fr2_7x Lo15 F0r2_7 LEQ15 ZERO15 ALr2_7 TOP15 PMc15 RM16.
  pose proof CSx15 as CS15. clear CSx15.
  rewrite with_vmmaps_twice in HW16 |- *.
  assert (Eres15 : res15 = Z_to_bv 64 (u res15)) by (symmetry; apply zbv_self).
  pose proof (u64_range res15) as RRr2_7. set (r2_7 := u res15) in *. clearbody r2_7. rewrite Eres15 in Hres15, Fr2_7x, Lo15, F0r2_7, LEQ15, ZERO15. clear Eres15.
  change (1 * 4)%Z with 4%Z in *.
  pose proof (exW_blk_img_apart_h2 C A16 m16 _ r2_7 4 CK HW16 Lo15 RRr2_7 eq_refl eq_refl) as IMGAPr2_7. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPr2_7.
  pose proof (exW_win_blk_apart_h C A16 m16 _ s 4304 r2_7 4 CK HW16 Lo15 eq_refl RRr2_7 GLO1) as WAPr2_7.
  assert (Fr2_7 : live A0 (Z_to_bv 64 r2_7) = None).
  { destruct (live A0 (Z_to_bv 64 r2_7)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB15 _ _ EE) as XX. first [discriminate Fr2_7x | (rewrite Fr2_7x in XX; discriminate XX)]. }
  pose proof Lo15 as Lr2_7_a16.
  assert (SUB16 : sub_live A0 A16).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 r2_7) by (intros ->; rewrite Fr2_7 in Lq; discriminate Lq). rewrite (LEQ15 q NEq). exact (SUB15 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 r2_7 :: [Z_to_bv 64 r2_6; Z_to_bv 64 r2_5; Z_to_bv 64 r2_4; Z_to_bv 64 r2_3; Z_to_bv 64 r2_2; Z_to_bv 64 r2_1; Z_to_bv 64 r2_0; Z_to_bv 64 arr2; Z_to_bv 64 sel2; Z_to_bv 64 r1_3; Z_to_bv 64 r1_2; Z_to_bv 64 r1_1; Z_to_bv 64 r1_0; Z_to_bv 64 arr1; Z_to_bv 64 sel1])) => eq_trans (LEQ15 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL15 q (fun XX => Hq (or_intror XX)))) as LDEL16.
  assert (NE_sel1_r2_7 : Z_to_bv 64 sel1 <> Z_to_bv 64 r2_7) by (intros EE; rewrite EE in Lsel1_a15; rewrite Fr2_7x in Lsel1_a15; discriminate Lsel1_a15).
  assert (Lsel1_a16 : live A16 (Z_to_bv 64 sel1) = Some 32%Z) by (rewrite (LEQ15 _ NE_sel1_r2_7); exact Lsel1_a15).
  pose proof (exW_blk_apart_h C A16 m16 _ sel1 r2_7 32 4 CK HW16 Lsel1_a16 Lr2_7_a16 NE_sel1_r2_7 RRsel1 RRr2_7 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel1_r2_7.
  assert (NE_arr1_r2_7 : Z_to_bv 64 arr1 <> Z_to_bv 64 r2_7) by (intros EE; rewrite EE in Larr1_a15; rewrite Fr2_7x in Larr1_a15; discriminate Larr1_a15).
  assert (Larr1_a16 : live A16 (Z_to_bv 64 arr1) = Some 32%Z) by (rewrite (LEQ15 _ NE_arr1_r2_7); exact Larr1_a15).
  pose proof (exW_blk_apart_h C A16 m16 _ arr1 r2_7 32 4 CK HW16 Larr1_a16 Lr2_7_a16 NE_arr1_r2_7 RRarr1 RRr2_7 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr1_r2_7.
  assert (NE_r1_0_r2_7 : Z_to_bv 64 r1_0 <> Z_to_bv 64 r2_7) by (intros EE; rewrite EE in Lr1_0_a15; rewrite Fr2_7x in Lr1_0_a15; discriminate Lr1_0_a15).
  assert (Lr1_0_a16 : live A16 (Z_to_bv 64 r1_0) = Some 4%Z) by (rewrite (LEQ15 _ NE_r1_0_r2_7); exact Lr1_0_a15).
  pose proof (exW_blk_apart_h C A16 m16 _ r1_0 r2_7 4 4 CK HW16 Lr1_0_a16 Lr2_7_a16 NE_r1_0_r2_7 RRr1_0 RRr2_7 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_0_r2_7.
  assert (NE_r1_1_r2_7 : Z_to_bv 64 r1_1 <> Z_to_bv 64 r2_7) by (intros EE; rewrite EE in Lr1_1_a15; rewrite Fr2_7x in Lr1_1_a15; discriminate Lr1_1_a15).
  assert (Lr1_1_a16 : live A16 (Z_to_bv 64 r1_1) = Some 4%Z) by (rewrite (LEQ15 _ NE_r1_1_r2_7); exact Lr1_1_a15).
  pose proof (exW_blk_apart_h C A16 m16 _ r1_1 r2_7 4 4 CK HW16 Lr1_1_a16 Lr2_7_a16 NE_r1_1_r2_7 RRr1_1 RRr2_7 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_1_r2_7.
  assert (NE_r1_2_r2_7 : Z_to_bv 64 r1_2 <> Z_to_bv 64 r2_7) by (intros EE; rewrite EE in Lr1_2_a15; rewrite Fr2_7x in Lr1_2_a15; discriminate Lr1_2_a15).
  assert (Lr1_2_a16 : live A16 (Z_to_bv 64 r1_2) = Some 4%Z) by (rewrite (LEQ15 _ NE_r1_2_r2_7); exact Lr1_2_a15).
  pose proof (exW_blk_apart_h C A16 m16 _ r1_2 r2_7 4 4 CK HW16 Lr1_2_a16 Lr2_7_a16 NE_r1_2_r2_7 RRr1_2 RRr2_7 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_2_r2_7.
  assert (NE_r1_3_r2_7 : Z_to_bv 64 r1_3 <> Z_to_bv 64 r2_7) by (intros EE; rewrite EE in Lr1_3_a15; rewrite Fr2_7x in Lr1_3_a15; discriminate Lr1_3_a15).
  assert (Lr1_3_a16 : live A16 (Z_to_bv 64 r1_3) = Some 4%Z) by (rewrite (LEQ15 _ NE_r1_3_r2_7); exact Lr1_3_a15).
  pose proof (exW_blk_apart_h C A16 m16 _ r1_3 r2_7 4 4 CK HW16 Lr1_3_a16 Lr2_7_a16 NE_r1_3_r2_7 RRr1_3 RRr2_7 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r1_3_r2_7.
  assert (NE_sel2_r2_7 : Z_to_bv 64 sel2 <> Z_to_bv 64 r2_7) by (intros EE; rewrite EE in Lsel2_a15; rewrite Fr2_7x in Lsel2_a15; discriminate Lsel2_a15).
  assert (Lsel2_a16 : live A16 (Z_to_bv 64 sel2) = Some 32%Z) by (rewrite (LEQ15 _ NE_sel2_r2_7); exact Lsel2_a15).
  pose proof (exW_blk_apart_h C A16 m16 _ sel2 r2_7 32 4 CK HW16 Lsel2_a16 Lr2_7_a16 NE_sel2_r2_7 RRsel2 RRr2_7 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel2_r2_7.
  assert (NE_arr2_r2_7 : Z_to_bv 64 arr2 <> Z_to_bv 64 r2_7) by (intros EE; rewrite EE in Larr2_a15; rewrite Fr2_7x in Larr2_a15; discriminate Larr2_a15).
  assert (Larr2_a16 : live A16 (Z_to_bv 64 arr2) = Some 64%Z) by (rewrite (LEQ15 _ NE_arr2_r2_7); exact Larr2_a15).
  pose proof (exW_blk_apart_h C A16 m16 _ arr2 r2_7 64 4 CK HW16 Larr2_a16 Lr2_7_a16 NE_arr2_r2_7 RRarr2 RRr2_7 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr2_r2_7.
  assert (NE_r2_0_r2_7 : Z_to_bv 64 r2_0 <> Z_to_bv 64 r2_7) by (intros EE; rewrite EE in Lr2_0_a15; rewrite Fr2_7x in Lr2_0_a15; discriminate Lr2_0_a15).
  assert (Lr2_0_a16 : live A16 (Z_to_bv 64 r2_0) = Some 4%Z) by (rewrite (LEQ15 _ NE_r2_0_r2_7); exact Lr2_0_a15).
  pose proof (exW_blk_apart_h C A16 m16 _ r2_0 r2_7 4 4 CK HW16 Lr2_0_a16 Lr2_7_a16 NE_r2_0_r2_7 RRr2_0 RRr2_7 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r2_0_r2_7.
  assert (NE_r2_1_r2_7 : Z_to_bv 64 r2_1 <> Z_to_bv 64 r2_7) by (intros EE; rewrite EE in Lr2_1_a15; rewrite Fr2_7x in Lr2_1_a15; discriminate Lr2_1_a15).
  assert (Lr2_1_a16 : live A16 (Z_to_bv 64 r2_1) = Some 4%Z) by (rewrite (LEQ15 _ NE_r2_1_r2_7); exact Lr2_1_a15).
  pose proof (exW_blk_apart_h C A16 m16 _ r2_1 r2_7 4 4 CK HW16 Lr2_1_a16 Lr2_7_a16 NE_r2_1_r2_7 RRr2_1 RRr2_7 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r2_1_r2_7.
  assert (NE_r2_2_r2_7 : Z_to_bv 64 r2_2 <> Z_to_bv 64 r2_7) by (intros EE; rewrite EE in Lr2_2_a15; rewrite Fr2_7x in Lr2_2_a15; discriminate Lr2_2_a15).
  assert (Lr2_2_a16 : live A16 (Z_to_bv 64 r2_2) = Some 4%Z) by (rewrite (LEQ15 _ NE_r2_2_r2_7); exact Lr2_2_a15).
  pose proof (exW_blk_apart_h C A16 m16 _ r2_2 r2_7 4 4 CK HW16 Lr2_2_a16 Lr2_7_a16 NE_r2_2_r2_7 RRr2_2 RRr2_7 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r2_2_r2_7.
  assert (NE_r2_3_r2_7 : Z_to_bv 64 r2_3 <> Z_to_bv 64 r2_7) by (intros EE; rewrite EE in Lr2_3_a15; rewrite Fr2_7x in Lr2_3_a15; discriminate Lr2_3_a15).
  assert (Lr2_3_a16 : live A16 (Z_to_bv 64 r2_3) = Some 4%Z) by (rewrite (LEQ15 _ NE_r2_3_r2_7); exact Lr2_3_a15).
  pose proof (exW_blk_apart_h C A16 m16 _ r2_3 r2_7 4 4 CK HW16 Lr2_3_a16 Lr2_7_a16 NE_r2_3_r2_7 RRr2_3 RRr2_7 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r2_3_r2_7.
  assert (NE_r2_4_r2_7 : Z_to_bv 64 r2_4 <> Z_to_bv 64 r2_7) by (intros EE; rewrite EE in Lr2_4_a15; rewrite Fr2_7x in Lr2_4_a15; discriminate Lr2_4_a15).
  assert (Lr2_4_a16 : live A16 (Z_to_bv 64 r2_4) = Some 4%Z) by (rewrite (LEQ15 _ NE_r2_4_r2_7); exact Lr2_4_a15).
  pose proof (exW_blk_apart_h C A16 m16 _ r2_4 r2_7 4 4 CK HW16 Lr2_4_a16 Lr2_7_a16 NE_r2_4_r2_7 RRr2_4 RRr2_7 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r2_4_r2_7.
  assert (NE_r2_5_r2_7 : Z_to_bv 64 r2_5 <> Z_to_bv 64 r2_7) by (intros EE; rewrite EE in Lr2_5_a15; rewrite Fr2_7x in Lr2_5_a15; discriminate Lr2_5_a15).
  assert (Lr2_5_a16 : live A16 (Z_to_bv 64 r2_5) = Some 4%Z) by (rewrite (LEQ15 _ NE_r2_5_r2_7); exact Lr2_5_a15).
  pose proof (exW_blk_apart_h C A16 m16 _ r2_5 r2_7 4 4 CK HW16 Lr2_5_a16 Lr2_7_a16 NE_r2_5_r2_7 RRr2_5 RRr2_7 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r2_5_r2_7.
  assert (NE_r2_6_r2_7 : Z_to_bv 64 r2_6 <> Z_to_bv 64 r2_7) by (intros EE; rewrite EE in Lr2_6_a15; rewrite Fr2_7x in Lr2_6_a15; discriminate Lr2_6_a15).
  assert (Lr2_6_a16 : live A16 (Z_to_bv 64 r2_6) = Some 4%Z) by (rewrite (LEQ15 _ NE_r2_6_r2_7); exact Lr2_6_a15).
  pose proof (exW_blk_apart_h C A16 m16 _ r2_6 r2_7 4 4 CK HW16 Lr2_6_a16 Lr2_7_a16 NE_r2_6_r2_7 RRr2_6 RRr2_7 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_r2_6_r2_7.
  assert (PM16 : POSTM C A0 s m0 m16).
  { eapply POSTM_trans; [exact PM15|]. eapply POSTM_trans; [exact PMs15|]. apply (POSTM_sub C A0 A15 _ _ _ SUB15).
    apply (POSTM_mono C A15 (s + OFF15) s); [unfold OFF15; lia | exact PMc15]. }
  pose proof (cs_frame_hop C s 4304 OFF15 (-32) (-40) m0 M15 m16 CK (proj1 PMc15) ltac:(lia) ltac:(vm_cast_no_check (eq_refl true)) ltac:(vm_cast_no_check (eq_refl true)) CFs15) as CF16.
  replace (kR - 15 - 1)%Z with (kR - 16)%Z in RM16 by lia. rewrite MG15 in RM16. replace (bR - 15 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 16 * 2 ^ 17)%Z in RM16 by lia.
  assert (KEPT15 : Forall (ex_region_kept E15 M15 m16) [(EVar 32, OFF15, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 32%Z); (EVar 135, 0%Z, 4%Z); (EVar 169, 0%Z, 4%Z); (EVar 203, 0%Z, 4%Z); (EVar 237, 0%Z, 4%Z); (EVar 271, 0%Z, 32%Z); (EVar 305, 0%Z, 64%Z); (EVar 339, 0%Z, 4%Z); (EVar 373, 0%Z, 4%Z); (EVar 407, 0%Z, 4%Z); (EVar 441, 0%Z, 4%Z); (EVar 475, 0%Z, 4%Z); (EVar 509, 0%Z, 4%Z); (EVar 543, 0%Z, 4%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF15 4304 M15 m16 E15 (EVar 32) CK (proj1 PMc15) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A15 A15 M15 _ M15 m16 E15 (EVar 67) sel1 32 CK HWs15 Lsel1_a15 RRsel1 eq_refl (proj2 PMc15) Lsel1_a15 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A15 A15 M15 _ M15 m16 E15 (EVar 101) arr1 32 CK HWs15 Larr1_a15 RRarr1 eq_refl (proj2 PMc15) Larr1_a15 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A15 A15 M15 _ M15 m16 E15 (EVar 135) r1_0 4 CK HWs15 Lr1_0_a15 RRr1_0 eq_refl (proj2 PMc15) Lr1_0_a15 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A15 A15 M15 _ M15 m16 E15 (EVar 169) r1_1 4 CK HWs15 Lr1_1_a15 RRr1_1 eq_refl (proj2 PMc15) Lr1_1_a15 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A15 A15 M15 _ M15 m16 E15 (EVar 203) r1_2 4 CK HWs15 Lr1_2_a15 RRr1_2 eq_refl (proj2 PMc15) Lr1_2_a15 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A15 A15 M15 _ M15 m16 E15 (EVar 237) r1_3 4 CK HWs15 Lr1_3_a15 RRr1_3 eq_refl (proj2 PMc15) Lr1_3_a15 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A15 A15 M15 _ M15 m16 E15 (EVar 271) sel2 32 CK HWs15 Lsel2_a15 RRsel2 eq_refl (proj2 PMc15) Lsel2_a15 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A15 A15 M15 _ M15 m16 E15 (EVar 305) arr2 64 CK HWs15 Larr2_a15 RRarr2 eq_refl (proj2 PMc15) Larr2_a15 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A15 A15 M15 _ M15 m16 E15 (EVar 339) r2_0 4 CK HWs15 Lr2_0_a15 RRr2_0 eq_refl (proj2 PMc15) Lr2_0_a15 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A15 A15 M15 _ M15 m16 E15 (EVar 373) r2_1 4 CK HWs15 Lr2_1_a15 RRr2_1 eq_refl (proj2 PMc15) Lr2_1_a15 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A15 A15 M15 _ M15 m16 E15 (EVar 407) r2_2 4 CK HWs15 Lr2_2_a15 RRr2_2 eq_refl (proj2 PMc15) Lr2_2_a15 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A15 A15 M15 _ M15 m16 E15 (EVar 441) r2_3 4 CK HWs15 Lr2_3_a15 RRr2_3 eq_refl (proj2 PMc15) Lr2_3_a15 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A15 A15 M15 _ M15 m16 E15 (EVar 475) r2_4 4 CK HWs15 Lr2_4_a15 RRr2_4 eq_refl (proj2 PMc15) Lr2_4_a15 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A15 A15 M15 _ M15 m16 E15 (EVar 509) r2_5 4 CK HWs15 Lr2_5_a15 RRr2_5 eq_refl (proj2 PMc15) Lr2_5_a15 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A15 A15 M15 _ M15 m16 E15 (EVar 543) r2_6 4 CK HWs15 Lr2_6_a15 RRr2_6 eq_refl (proj2 PMc15) Lr2_6_a15 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E15 M15 m16 _ [] _ HKc15 KEPT15) as HKk15.
  match type of HKk15 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E15 m16 kk') in HKk15 end.
  pose proof (regs_ok_agree 545%nat E15 (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) _ _ (vals_app_agree vals15 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa15.
  pose proof (exW_regs_call _ _ _ _ _ HRa15 (ex_regs_ok_junk vals15 r16 [r2_7; exW_canary SEGS 1410112 m16] 545%nat ltac:(vm_cast_no_check (eq_refl 545%nat))) CS15) as HRn16.
  clear HRa15.
  assert (HKa16 : know_ok SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16 _) by (exact (know_ok_agree SEGS 545%nat E15 _ m16 _ (vals_app_agree vals15 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk15)).
  rewrite (fr_denot_agree 545%nat E15 (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) _ fr (vals_app_agree vals15 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r16 ex_r10 (EVar 577) HRn16 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres15)) as HRx16. clear HRn16. rename HRx16 into HRn16.
  clear HR HK Hlf Hms HKc15 HKk15 KEPT15 HC15 HWs15 PMs15 Q10_15 Q11_15 Q1_15 Q2_15 Q4_15 PM15 HW15 PMc15 CS15 SUB15 RM15 MG15 TOP15 LEQ15 Hnz15 Fr2_7x Lo15 OFF15 LDEL15 CF15 CFs15 Lsel1_a15 Larr1_a15 Lr1_0_a15 Lr1_1_a15 Lr1_2_a15 Lr1_3_a15 Lsel2_a15 Larr2_a15 Lr2_0_a15 Lr2_1_a15 Lr2_2_a15 Lr2_3_a15 Lr2_4_a15 Lr2_5_a15 Lr2_6_a15.
  subst M15. clear log15. clear E15. try clear Rc15. clear KN15.
  lazymatch type of HRn16 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn16 end.
  pose proof (exW_kn_blk SEGS C A16 m16 _ (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) (EVar 577) (EVar 32) r2_7 4 s 4304 65536 1347584 p16_segs CK HW16 Lr2_7_a16 RRr2_7 eq_refl eq_refl eq_refl RS ALr2_7 ZERO15 WAPr2_7 IMGAPr2_7) as HKb16.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16) _ _ (ex_kdisj_apart SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16 (EVar 67) (EVar 577) sel1 r2_7 0 32 0 4 eq_refl eq_refl RRsel1 RRr2_7 AP_sel1_r2_7) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16) _ _ (ex_kdisj_apart SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16 (EVar 101) (EVar 577) arr1 r2_7 0 32 0 4 eq_refl eq_refl RRarr1 RRr2_7 AP_arr1_r2_7) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16) _ _ (ex_kdisj_apart SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16 (EVar 135) (EVar 577) r1_0 r2_7 0 4 0 4 eq_refl eq_refl RRr1_0 RRr2_7 AP_r1_0_r2_7) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16) _ _ (ex_kdisj_apart SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16 (EVar 169) (EVar 577) r1_1 r2_7 0 4 0 4 eq_refl eq_refl RRr1_1 RRr2_7 AP_r1_1_r2_7) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16) _ _ (ex_kdisj_apart SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16 (EVar 203) (EVar 577) r1_2 r2_7 0 4 0 4 eq_refl eq_refl RRr1_2 RRr2_7 AP_r1_2_r2_7) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16) _ _ (ex_kdisj_apart SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16 (EVar 237) (EVar 577) r1_3 r2_7 0 4 0 4 eq_refl eq_refl RRr1_3 RRr2_7 AP_r1_3_r2_7) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16) _ _ (ex_kdisj_apart SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16 (EVar 271) (EVar 577) sel2 r2_7 0 32 0 4 eq_refl eq_refl RRsel2 RRr2_7 AP_sel2_r2_7) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16) _ _ (ex_kdisj_apart SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16 (EVar 305) (EVar 577) arr2 r2_7 0 64 0 4 eq_refl eq_refl RRarr2 RRr2_7 AP_arr2_r2_7) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16) _ _ (ex_kdisj_apart SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16 (EVar 339) (EVar 577) r2_0 r2_7 0 4 0 4 eq_refl eq_refl RRr2_0 RRr2_7 AP_r2_0_r2_7) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16) _ _ (ex_kdisj_apart SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16 (EVar 373) (EVar 577) r2_1 r2_7 0 4 0 4 eq_refl eq_refl RRr2_1 RRr2_7 AP_r2_1_r2_7) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16) _ _ (ex_kdisj_apart SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16 (EVar 407) (EVar 577) r2_2 r2_7 0 4 0 4 eq_refl eq_refl RRr2_2 RRr2_7 AP_r2_2_r2_7) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16) _ _ (ex_kdisj_apart SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16 (EVar 441) (EVar 577) r2_3 r2_7 0 4 0 4 eq_refl eq_refl RRr2_3 RRr2_7 AP_r2_3_r2_7) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16) _ _ (ex_kdisj_apart SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16 (EVar 475) (EVar 577) r2_4 r2_7 0 4 0 4 eq_refl eq_refl RRr2_4 RRr2_7 AP_r2_4_r2_7) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16) _ _ (ex_kdisj_apart SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16 (EVar 509) (EVar 577) r2_5 r2_7 0 4 0 4 eq_refl eq_refl RRr2_5 RRr2_7 AP_r2_5_r2_7) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16) _ _ (ex_kdisj_apart SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16 (EVar 543) (EVar 577) r2_6 r2_7 0 4 0 4 eq_refl eq_refl RRr2_6 RRr2_7 AP_r2_6_r2_7) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) m16))))))))))))))))) as HKd16.
  pose proof (W_sok_win C A16 m16 _ (s - 4304) (Z.to_nat 4304) CK HW16 GLO1 GLO2) as SOK16.
  pose proof (exW_canary_ok SEGS 1410112 m16 (canary_any m16)) as CANOK16.
  pose (vals16 := vals15 ++ map (getr r16) ex_regs_list ++ map (Z_to_bv 64) [r2_7; exW_canary SEGS 1410112 m16]).
  pose proof (exW_kn_fixed SEGS C A16 m16 _ (ex_envL vals15 r16 [r2_7; exW_canary SEGS 1410112 m16]) (EVar 578) (EVar 32) (exW_canary SEGS 1410112 m16) s 4304 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW16 eq_refl (proj1 CANOK16) (proj2 CANOK16) eq_refl eq_refl eq_refl SOK16 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf16.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb16 (proj2 (Forall_app _ _ _) (conj HKd16 (proj2 (Forall_app _ _ _) (conj HKf16 HKa16)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn16 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN16 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb16 HKd16 HKf16 HKa16 SOK16 CANOK16.
  repeat match goal with H : getr r16 _ = _ |- _ => clear H end.
  exq_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO15 ALr2_7.
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E16 := EEx) in HR, Hlf, HK, Hms |- *; set (log16 := LLx) in Hms, Hlf; set (M16 := mem_denot E16 m16 log16) in Hms end.
  assert (WP16 : W C A16 M16 (with_vmmaps vm16 md) /\ POSTM C A0 s m16 M16).
  { subst M16. apply (exW_win_blks C A16 A0 m16 _ E16 log16 (EVar 32) s 4304 [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z); (EVar 135, r1_0, 4%Z); (EVar 169, r1_1, 4%Z); (EVar 203, r1_2, 4%Z); (EVar 237, r1_3, 4%Z); (EVar 271, sel2, 32%Z); (EVar 305, arr2, 64%Z); (EVar 339, r2_0, 4%Z); (EVar 373, r2_1, 4%Z); (EVar 407, r2_2, 4%Z); (EVar 441, r2_3, 4%Z); (EVar 475, r2_4, 4%Z); (EVar 509, r2_5, 4%Z); (EVar 543, r2_6, 4%Z); (EVar 577, r2_7, 4%Z)] CK HW16 SUB16 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a16 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a16 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a16 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRr1_1 (conj Lr1_1_a16 (conj Fr1_1 F0r1_1))))|]. constructor; [exact (conj eq_refl (conj RRr1_2 (conj Lr1_2_a16 (conj Fr1_2 F0r1_2))))|]. constructor; [exact (conj eq_refl (conj RRr1_3 (conj Lr1_3_a16 (conj Fr1_3 F0r1_3))))|]. constructor; [exact (conj eq_refl (conj RRsel2 (conj Lsel2_a16 (conj Fsel2 F0sel2))))|]. constructor; [exact (conj eq_refl (conj RRarr2 (conj Larr2_a16 (conj Farr2 F0arr2))))|]. constructor; [exact (conj eq_refl (conj RRr2_0 (conj Lr2_0_a16 (conj Fr2_0 F0r2_0))))|]. constructor; [exact (conj eq_refl (conj RRr2_1 (conj Lr2_1_a16 (conj Fr2_1 F0r2_1))))|]. constructor; [exact (conj eq_refl (conj RRr2_2 (conj Lr2_2_a16 (conj Fr2_2 F0r2_2))))|]. constructor; [exact (conj eq_refl (conj RRr2_3 (conj Lr2_3_a16 (conj Fr2_3 F0r2_3))))|]. constructor; [exact (conj eq_refl (conj RRr2_4 (conj Lr2_4_a16 (conj Fr2_4 F0r2_4))))|]. constructor; [exact (conj eq_refl (conj RRr2_5 (conj Lr2_5_a16 (conj Fr2_5 F0r2_5))))|]. constructor; [exact (conj eq_refl (conj RRr2_6 (conj Lr2_6_a16 (conj Fr2_6 F0r2_6))))|]. constructor; [exact (conj eq_refl (conj RRr2_7 (conj Lr2_7_a16 (conj Fr2_7 F0r2_7))))|]. constructor. }
  assert (CFs16 : O23LeptCselsA.cs_fra s (-32) (-40) m0 M16).
  { subst M16. apply (cs_frame_sess C A16 A0 m0 m16 _ E16 log16 (EVar 32) s 4304 (-32) (-40) [(EVar 67, sel1, 32%Z); (EVar 101, arr1, 32%Z); (EVar 135, r1_0, 4%Z); (EVar 169, r1_1, 4%Z); (EVar 203, r1_2, 4%Z); (EVar 237, r1_3, 4%Z); (EVar 271, sel2, 32%Z); (EVar 305, arr2, 64%Z); (EVar 339, r2_0, 4%Z); (EVar 373, r2_1, 4%Z); (EVar 407, r2_2, 4%Z); (EVar 441, r2_3, 4%Z); (EVar 475, r2_4, 4%Z); (EVar 509, r2_5, 4%Z); (EVar 543, r2_6, 4%Z); (EVar 577, r2_7, 4%Z)] CK HW16 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exact RS | lia | exact Hhi | reflexivity | | reflexivity | exact CF16]. constructor; [exact (conj eq_refl (conj RRsel1 (conj Lsel1_a16 (conj Fsel1 F0sel1))))|]. constructor; [exact (conj eq_refl (conj RRarr1 (conj Larr1_a16 (conj Farr1 F0arr1))))|]. constructor; [exact (conj eq_refl (conj RRr1_0 (conj Lr1_0_a16 (conj Fr1_0 F0r1_0))))|]. constructor; [exact (conj eq_refl (conj RRr1_1 (conj Lr1_1_a16 (conj Fr1_1 F0r1_1))))|]. constructor; [exact (conj eq_refl (conj RRr1_2 (conj Lr1_2_a16 (conj Fr1_2 F0r1_2))))|]. constructor; [exact (conj eq_refl (conj RRr1_3 (conj Lr1_3_a16 (conj Fr1_3 F0r1_3))))|]. constructor; [exact (conj eq_refl (conj RRsel2 (conj Lsel2_a16 (conj Fsel2 F0sel2))))|]. constructor; [exact (conj eq_refl (conj RRarr2 (conj Larr2_a16 (conj Farr2 F0arr2))))|]. constructor; [exact (conj eq_refl (conj RRr2_0 (conj Lr2_0_a16 (conj Fr2_0 F0r2_0))))|]. constructor; [exact (conj eq_refl (conj RRr2_1 (conj Lr2_1_a16 (conj Fr2_1 F0r2_1))))|]. constructor; [exact (conj eq_refl (conj RRr2_2 (conj Lr2_2_a16 (conj Fr2_2 F0r2_2))))|]. constructor; [exact (conj eq_refl (conj RRr2_3 (conj Lr2_3_a16 (conj Fr2_3 F0r2_3))))|]. constructor; [exact (conj eq_refl (conj RRr2_4 (conj Lr2_4_a16 (conj Fr2_4 F0r2_4))))|]. constructor; [exact (conj eq_refl (conj RRr2_5 (conj Lr2_5_a16 (conj Fr2_5 F0r2_5))))|]. constructor; [exact (conj eq_refl (conj RRr2_6 (conj Lr2_6_a16 (conj Fr2_6 F0r2_6))))|]. constructor; [exact (conj eq_refl (conj RRr2_7 (conj Lr2_7_a16 (conj Fr2_7 F0r2_7))))|]. constructor. }
  destruct WP16 as [HWs16 PMs16].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW16)) | exact (mp_lazy _ (w_pure _ _ _ _ HW16)) | exact Hms |].
  pose (BSF := [(32%nat, s); (67%nat, sel1); (101%nat, arr1); (135%nat, r1_0); (169%nat, r1_1); (203%nat, r1_2); (237%nat, r1_3); (271%nat, sel2); (305%nat, arr2); (339%nat, r2_0); (373%nat, r2_1); (407%nat, r2_2); (441%nat, r2_3); (475%nat, r2_4); (509%nat, r2_5); (543%nat, r2_6); (577%nat, r2_7)]).
  exW_regfactB BSF HR ex_r10 G10.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-32)%Z 8%nat CO1.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-40)%Z 8%nat CO2.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel1 0%Z 4%nat Csel1_0.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel1 4%Z 4%nat Csel1_4.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel1 8%Z 4%nat Csel1_8.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel1 12%Z 4%nat Csel1_12.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel1 16%Z 8%nat Csel1_16.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel1 24%Z 8%nat Csel1_24.
  exW_cellB HK Hlf r0 BSF (EVar 101) arr1 0%Z 8%nat Carr1_0.
  exW_cellB HK Hlf r0 BSF (EVar 101) arr1 8%Z 8%nat Carr1_8.
  exW_cellB HK Hlf r0 BSF (EVar 101) arr1 16%Z 8%nat Carr1_16.
  exW_cellB HK Hlf r0 BSF (EVar 101) arr1 24%Z 8%nat Carr1_24.
  exW_cellB HK Hlf r0 BSF (EVar 135) r1_0 0%Z 4%nat Cr1_0_0.
  exW_cellB HK Hlf r0 BSF (EVar 169) r1_1 0%Z 4%nat Cr1_1_0.
  exW_cellB HK Hlf r0 BSF (EVar 203) r1_2 0%Z 4%nat Cr1_2_0.
  exW_cellB HK Hlf r0 BSF (EVar 237) r1_3 0%Z 4%nat Cr1_3_0.
  assert (SF1 : cs_sel_facts C A0 A16 M16 sel1 arr1 4 1 2 0 [r1_0; r1_1; r1_2; r1_3] [[1]; [1]; [1]; [1]]%Z).
  { split; [|split; [|split]].
    - cbn [map]. constructor; [exact (conj Lsel1_a16 (conj Fsel1 (conj F0sel1 RRsel1)))|]. constructor; [exact (conj Larr1_a16 (conj Farr1 (conj F0arr1 RRarr1)))|]. constructor; [exact (conj Lr1_0_a16 (conj Fr1_0 (conj F0r1_0 RRr1_0)))|]. constructor; [exact (conj Lr1_1_a16 (conj Fr1_1 (conj F0r1_1 RRr1_1)))|]. constructor; [exact (conj Lr1_2_a16 (conj Fr1_2 (conj F0r1_2 RRr1_2)))|]. constructor; [exact (conj Lr1_3_a16 (conj Fr1_3 (conj F0r1_3 RRr1_3)))|]. constructor.
    - constructor; [exact Csel1_0|]. constructor; [exact Csel1_4|]. constructor; [exact Csel1_8|]. constructor; [exact Csel1_12|]. constructor; [exact Csel1_16|]. constructor; [exact Csel1_24|]. constructor.
    - cbn [O23LeptCselsA.cs_mk]. constructor; [exact Carr1_0|]. constructor; [exact Carr1_8|]. constructor; [exact Carr1_16|]. constructor; [exact Carr1_24|]. constructor.
    - cbn [O23LeptCselsA.cs_mk]. constructor; [constructor; [exact Cr1_0_0|]; constructor|]. constructor; [constructor; [exact Cr1_1_0|]; constructor|]. constructor; [constructor; [exact Cr1_2_0|]; constructor|]. constructor; [constructor; [exact Cr1_3_0|]; constructor|]. constructor. }
  exW_cellB HK Hlf r0 BSF (EVar 271) sel2 0%Z 4%nat Csel2_0.
  exW_cellB HK Hlf r0 BSF (EVar 271) sel2 4%Z 4%nat Csel2_4.
  exW_cellB HK Hlf r0 BSF (EVar 271) sel2 8%Z 4%nat Csel2_8.
  exW_cellB HK Hlf r0 BSF (EVar 271) sel2 12%Z 4%nat Csel2_12.
  exW_cellB HK Hlf r0 BSF (EVar 271) sel2 16%Z 8%nat Csel2_16.
  exW_cellB HK Hlf r0 BSF (EVar 271) sel2 24%Z 8%nat Csel2_24.
  exW_cellB HK Hlf r0 BSF (EVar 305) arr2 0%Z 8%nat Carr2_0.
  exW_cellB HK Hlf r0 BSF (EVar 305) arr2 8%Z 8%nat Carr2_8.
  exW_cellB HK Hlf r0 BSF (EVar 305) arr2 16%Z 8%nat Carr2_16.
  exW_cellB HK Hlf r0 BSF (EVar 305) arr2 24%Z 8%nat Carr2_24.
  exW_cellB HK Hlf r0 BSF (EVar 305) arr2 32%Z 8%nat Carr2_32.
  exW_cellB HK Hlf r0 BSF (EVar 305) arr2 40%Z 8%nat Carr2_40.
  exW_cellB HK Hlf r0 BSF (EVar 305) arr2 48%Z 8%nat Carr2_48.
  exW_cellB HK Hlf r0 BSF (EVar 305) arr2 56%Z 8%nat Carr2_56.
  exW_cellB HK Hlf r0 BSF (EVar 339) r2_0 0%Z 4%nat Cr2_0_0.
  exW_cellB HK Hlf r0 BSF (EVar 373) r2_1 0%Z 4%nat Cr2_1_0.
  exW_cellB HK Hlf r0 BSF (EVar 407) r2_2 0%Z 4%nat Cr2_2_0.
  exW_cellB HK Hlf r0 BSF (EVar 441) r2_3 0%Z 4%nat Cr2_3_0.
  exW_cellB HK Hlf r0 BSF (EVar 475) r2_4 0%Z 4%nat Cr2_4_0.
  exW_cellB HK Hlf r0 BSF (EVar 509) r2_5 0%Z 4%nat Cr2_5_0.
  exW_cellB HK Hlf r0 BSF (EVar 543) r2_6 0%Z 4%nat Cr2_6_0.
  exW_cellB HK Hlf r0 BSF (EVar 577) r2_7 0%Z 4%nat Cr2_7_0.
  assert (SF2 : cs_sel_facts C A0 A16 M16 sel2 arr2 8 1 4 0 [r2_0; r2_1; r2_2; r2_3; r2_4; r2_5; r2_6; r2_7] [[0]; [0]; [1]; [0]; [0]; [0]; [1]; [0]]%Z).
  { split; [|split; [|split]].
    - cbn [map]. constructor; [exact (conj Lsel2_a16 (conj Fsel2 (conj F0sel2 RRsel2)))|]. constructor; [exact (conj Larr2_a16 (conj Farr2 (conj F0arr2 RRarr2)))|]. constructor; [exact (conj Lr2_0_a16 (conj Fr2_0 (conj F0r2_0 RRr2_0)))|]. constructor; [exact (conj Lr2_1_a16 (conj Fr2_1 (conj F0r2_1 RRr2_1)))|]. constructor; [exact (conj Lr2_2_a16 (conj Fr2_2 (conj F0r2_2 RRr2_2)))|]. constructor; [exact (conj Lr2_3_a16 (conj Fr2_3 (conj F0r2_3 RRr2_3)))|]. constructor; [exact (conj Lr2_4_a16 (conj Fr2_4 (conj F0r2_4 RRr2_4)))|]. constructor; [exact (conj Lr2_5_a16 (conj Fr2_5 (conj F0r2_5 RRr2_5)))|]. constructor; [exact (conj Lr2_6_a16 (conj Fr2_6 (conj F0r2_6 RRr2_6)))|]. constructor; [exact (conj Lr2_7_a16 (conj Fr2_7 (conj F0r2_7 RRr2_7)))|]. constructor.
    - constructor; [exact Csel2_0|]. constructor; [exact Csel2_4|]. constructor; [exact Csel2_8|]. constructor; [exact Csel2_12|]. constructor; [exact Csel2_16|]. constructor; [exact Csel2_24|]. constructor.
    - cbn [O23LeptCselsA.cs_mk]. constructor; [exact Carr2_0|]. constructor; [exact Carr2_8|]. constructor; [exact Carr2_16|]. constructor; [exact Carr2_24|]. constructor; [exact Carr2_32|]. constructor; [exact Carr2_40|]. constructor; [exact Carr2_48|]. constructor; [exact Carr2_56|]. constructor.
    - cbn [O23LeptCselsA.cs_mk]. constructor; [constructor; [exact Cr2_0_0|]; constructor|]. constructor; [constructor; [exact Cr2_1_0|]; constructor|]. constructor; [constructor; [exact Cr2_2_0|]; constructor|]. constructor; [constructor; [exact Cr2_3_0|]; constructor|]. constructor; [constructor; [exact Cr2_4_0|]; constructor|]. constructor; [constructor; [exact Cr2_5_0|]; constructor|]. constructor; [constructor; [exact Cr2_6_0|]; constructor|]. constructor; [constructor; [exact Cr2_7_0|]; constructor|]. constructor. }
  assert (ND : List.NoDup (O23LeptCselsA.cs_words sel1 arr1 [r1_0; r1_1; r1_2; r1_3] ++ O23LeptCselsA.cs_words sel2 arr2 [r2_0; r2_1; r2_2; r2_3; r2_4; r2_5; r2_6; r2_7])).
  { cbn [O23LeptCselsA.cs_words map app]. repeat constructor. all: intros X; cbn [In] in X; repeat (destruct X as [X|X]; [match goal with H : Z_to_bv 64 _ <> Z_to_bv 64 _ |- _ => first [exact (H X) | exact (H (eq_sym X))] end|]); exact X. }
  assert (LD : forall q : word, ~ In q (O23LeptCselsA.cs_words sel1 arr1 [r1_0; r1_1; r1_2; r1_3] ++ O23LeptCselsA.cs_words sel2 arr2 [r2_0; r2_1; r2_2; r2_3; r2_4; r2_5; r2_6; r2_7]) -> live A16 q = live A0 q).
  { intros q Hq. apply LDEL16. intros X. apply Hq. clear - X. cbn [O23LeptCselsA.cs_words map app In] in X |- *. tauto. }
  lazymatch goal with |- realizes _ (mkCfg (@mkst (mkFP ?frF ?csF) _ _ _ _) _) _ => assert (FSK : forall r : reg, In (u r) fs_list -> reg_get frF r = reg_get fr r) end.
  { intros r Hr. apply (fr_kept_incl _ _ _ O23LeptCselsA.cs_fkeys r); [vm_compute; reflexivity | exact (O23LeptCselsA.cs_fs_keys r Hr)]. }
  assert (CSK : cs_kept r0 RcF).
  { lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 RcF [(2%nat, EAlu ALU_ADD (EVar 32) (ELit (-48))); (4%nat, ELit 1278416)] HR) end; [exW_entry_vars | constructor; [refine (eq_trans (ex_ptr_val s (-48)) _); symmetry; exact HSP | constructor; [symmetry; exact HTP | constructor]] | vm_compute; reflexivity]. }
  exact (HC _ _ A16 M16 vm16 RcF sel1 arr1 r1_0 r1_1 r1_2 r1_3 sel2 arr2 r2_0 r2_1 r2_2 r2_3 r2_4 r2_5 r2_6 r2_7 FZ FSK HWs16 CSK G10 SUB16 (POSTM_trans _ _ _ _ _ _ PM16 PMs16) CFs16 RM16 CO1 CO2 SF1 SF2 ND LD).
Qed.
End Chain.
