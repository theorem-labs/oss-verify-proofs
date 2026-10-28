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
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptSelDA.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptExecT.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LiaRel.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptSelDC.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_rel.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Chain.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
(* [comment removed for export] *)
#[local] Existing Instance exf_fxd | 100.

Definition STOPS : list Z := [1107680; 1107992]%Z.
Definition FDEF : list (nat * nat) := [(8%nat, 33%nat)].
Definition ex_rs34 : reg := 8%bv.

(* [comment removed for export] *)
Lemma seld_chain1 : forall (fx : FPState) C A m md regs (s psel sel dat row0 n0 : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + O23LeptSelDC.SELD_WIN <= s)%Z -> (s <= psel)%Z -> (psel + 8 <= c_top C)%Z -> (psel mod 8 = 0)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 1278416 -> getr regs 10 = Z_to_bv 64 psel ->
  rdn SEGS m (Z_to_bv 64 (psel + 0)) 8 = Some (Z_to_le_bytes 8 sel) ->
  rdn SEGS m (Z_to_bv 64 (sel + 0)) 4 = Some (Z_to_le_bytes 4 1) ->
  rdn SEGS m (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 dat) ->
  rdn SEGS m (Z_to_bv 64 (sel + 24)) 8 = Some (Z_to_le_bytes 8 0) ->
  rdn SEGS m (Z_to_bv 64 (dat + 0)) 8 = Some (Z_to_le_bytes 8 row0) ->
  live A (Z_to_bv 64 sel) = Some 32%Z -> live (c_A0 C) (Z_to_bv 64 sel) = None -> (0 <= sel < 2 ^ 64)%Z ->
  live A (Z_to_bv 64 dat) = Some 8%Z -> live (c_A0 C) (Z_to_bv 64 dat) = None -> (0 <= dat < 2 ^ 64)%Z ->
  live A (Z_to_bv 64 row0) = Some n0%Z -> live (c_A0 C) (Z_to_bv 64 row0) = None -> (0 <= row0 < 2 ^ 64)%Z ->
  Z_to_bv 64 sel <> Z_to_bv 64 dat ->
  Z_to_bv 64 sel <> Z_to_bv 64 row0 ->
  Z_to_bv 64 dat <> Z_to_bv 64 row0 ->
  (forall A' m' vm' regs',
     W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     live A' (Z_to_bv 64 sel) = None ->
     live A' (Z_to_bv 64 dat) = None ->
     live A' (Z_to_bv 64 row0) = None ->
     (forall q : word, ~ In q [Z_to_bv 64 sel; Z_to_bv 64 dat; Z_to_bv 64 row0] -> live A' q = live A q) ->
     POSTM C A' (psel + 8) m m' -> rdn SEGS m' (Z_to_bv 64 (psel + 0)) 8 = Some (Z_to_le_bytes 8 0) ->
     (forall a : word, (s <= u a < psel)%Z -> m' a = m a) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 674932) m al_rom) md) S.
Proof using P16 PINS.
  intros fx C A0 m0 md r0 s psel sel dat row0 n0 ret S CK HW0 H2 Hs16 Hlo Hsp Hph Hpal H1 Hret H4 H10 Mpsel Msy Mdat Mnm Mrow0
    Lsel_a0 F0sel RRsel Ldat_a0 F0dat RRdat Lrow0_a0 F0row0 RRrow0
    NE_sel_dat NE_sel_row0 NE_dat_row0 HC.
  unfold O23LeptSelDC.SELD_WIN in *.
  assert (Hhi : (s <= c_top C)%Z) by lia.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  assert (HTP : ex_keep (getr r0 ex_r4 = Z_to_bv 64 1278416)) by exact H4.
  destruct fx as [fr cs]. pose proof I as FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  assert (GLO1 : (c_top C - LSTK <= s - 1104)%Z) by lia.
  assert (GLO2 : (s - 1104 + Z.of_nat (Z.to_nat 1104) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (1104 <= s)%Z) by lia.
  assert (RP : (0 <= psel < 2 ^ 64)%Z) by lia.
  destruct (exW_blk_rng C A0 m0 _ sel 32 CK HW0 Lsel_a0 RRsel ltac:(lia)) as (GLsel & _ & GHsel).
  pose proof (ai_live_hull A0 m0 (m_vmmaps md) _ _ (w_inv _ _ _ _ HW0) Lsel_a0) as (_ & ALsel & _). rewrite u_Z2bv in ALsel by lia.
  pose proof (exW_win_blk_apart_h C A0 m0 _ s 1104 sel 32 CK HW0 Lsel_a0 eq_refl RRsel GLO1) as WAPsel.
  destruct (exW_blk_rng C A0 m0 _ dat 8 CK HW0 Ldat_a0 RRdat ltac:(lia)) as (GLdat & _ & GHdat).
  pose proof (ai_live_hull A0 m0 (m_vmmaps md) _ _ (w_inv _ _ _ _ HW0) Ldat_a0) as (_ & ALdat & _). rewrite u_Z2bv in ALdat by lia.
  pose proof (exW_win_blk_apart_h C A0 m0 _ s 1104 dat 8 CK HW0 Ldat_a0 eq_refl RRdat GLO1) as WAPdat.
  pose proof (W_sok_win C A0 m0 _ psel 8 CK HW0 ltac:(lia) ltac:(cbn; lia)) as SOKP.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose proof (POSTM_refl C A0 s m0) as PM0.
  pose proof (roomtr_refl A0 vm0 0 0 ltac:(lia) ltac:(lia)) as RT0.
  pose (valsI := @nil word).
  pose proof (fun (q : word) (_ : ~ In q []) => eq_refl (live A0 q)) as LDEL0.
  pose proof (W_sok_win C A0 m0 _ (s - 1104) (Z.to_nat 1104) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 1410112 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0; psel; sel; dat; row0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0; psel; sel; dat; row0]) (EVar 34) (EVar 32) (exW_canary SEGS 1410112 m0) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0; psel; sel; dat; row0]) m0 [KRange (EVar 32) 1422416 (2 ^ 63); KAlign (EVar 32) 16; KRange (EVar 35) 1422416 (2 ^ 63); KAlign (EVar 35) 8; KWr (SA (EVar 35) 0) 8; KWord (SA (EVar 35) 0) 8 (EVar 36); KDisj (SA (EVar 32) (- 1104)) 1104 (SA (EVar 35) 0) 8; KRange (EVar 36) 4096 (2 ^ 47); KAlign (EVar 36) 16; KDisj (SA (EVar 32) (- 1104)) 1104 (SA (EVar 36) 0) 32; KWord (SA (EVar 36) 0) 4 (ELit 1); KWord (SA (EVar 36) 16) 8 (EVar 37); KWord (SA (EVar 36) 24) 8 (ELit 0); KRange (EVar 37) 4096 (2 ^ 47); KAlign (EVar 37) 16; KDisj (SA (EVar 32) (- 1104)) 1104 (SA (EVar 37) 0) 8; KWord (SA (EVar 37) 0) 8 (EVar 38)]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 HKf0)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0; psel; sel; dat; row0] HR.
  pose proof (ex_regs_ok_reexpr _ _ r0 ex_r10 (EVar 35) HR ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact H10)) as HRx. clear HR. rename HRx into HR.
  lazymatch type of HR with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HR end.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win C A0 A0 m0 _ E0 log0 (EVar 32) s 1104 CK HW0 (sub_live_refl A0) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi]. }
  destruct WP0 as [HWs0 PMs0].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (35%nat, psel); (36%nat, sel); (37%nat, dat); (38%nat, row0)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r1 Q1_0. exW_regfactB BS0 HR ex_r2 Q2_0. exW_regfactB BS0 HR ex_r4 Q4_0.
  clear BS0.
  lazymatch type of Q2_0 with _ = Z_to_bv 64 (s + ?off) => pose (OFF0 := off) end.
  lazymatch type of Q1_0 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_0 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A0 M0 _ Rc0 (Z_to_bv 64 row0) (Z_to_bv 64 ret) n0 sp' S CK HWs0 Q10_0 Lrow0_a0 F0row0 Q1_0
             ltac:(red; apply bv_eq; reflexivity) Q4_0 Q2_0 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A1 m1 vm1 r1 HW1 CS0 Drow0_1 LEQ0 PMc0 RM0.
  rewrite with_vmmaps_twice in HW1 |- *. rewrite with_vmmaps_vmmaps in RM0.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT0 RM0 ltac:(lia) ltac:(lia)) as RT1. cbn [Z.add] in RT1.
  assert (Ldat_a1 : live A1 (Z_to_bv 64 dat) = Some 8%Z) by (rewrite (LEQ0 _ NE_dat_row0); exact Ldat_a0).
  assert (Lsel_a1 : live A1 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ0 _ NE_sel_row0); exact Lsel_a0).
  assert (SUB0 : sub_live A1 A0).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row0) by (intros ->; rewrite Drow0_1 in Lq; discriminate Lq). rewrite <- (LEQ0 q NEq). exact Lq. }
  assert (PM1 : POSTM C A1 s m0 m1).
  { apply (POSTM_trans C A1 s m0 M0 m1); [apply (POSTM_sub C A1 A0 _ _ _ SUB0); exact (POSTM_trans _ _ _ _ _ _ PM0 PMs0)|].
    apply (POSTM_mono C A1 (s + OFF0) s); [unfold OFF0; lia | exact PMc0]. }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row0 :: [])) => eq_trans (LEQ0 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL0 q (fun XX => Hq (or_intror XX)))) as LDEL1.
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, OFF0, 0%Z); (EVar 35, 0%Z, 8%Z); (EVar 36, 0%Z, 32%Z); (EVar 37, 0%Z, 8%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF0 1104 M0 m1 E0 (EVar 32) CK (proj1 PMc0) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (sd_kept_cell C (s + OFF0) psel M0 m1 E0 (EVar 35) CK (proj1 PMc0) ltac:(unfold OFF0; lia) ltac:(unfold OFF0; lia) RP eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A1 A0 M0 _ M0 m1 E0 (EVar 36) sel 32 CK HWs0 Lsel_a0 RRsel eq_refl (proj2 PMc0) Lsel_a1 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A1 A0 M0 _ M0 m1 E0 (EVar 37) dat 8 CK HWs0 Ldat_a0 RRdat eq_refl (proj2 PMc0) Ldat_a1 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E0 m1 kk') in HKk0 end.
  pose proof (regs_ok_agree 39%nat E0 (ex_envL vals0 r1 [exW_canary SEGS 1410112 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [exW_canary SEGS 1410112 m1] 39%nat ltac:(vm_cast_no_check (eq_refl 39%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [exW_canary SEGS 1410112 m1]) m1 _) by (exact (know_ok_agree SEGS 39%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  rewrite (fr_denot_agree 39%nat E0 (ex_envL vals0 r1 [exW_canary SEGS 1410112 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q1_0 Q2_0 Q4_0 PM0 HW0 PMc0 CS0 SUB0 RM0 RT0 LEQ0 OFF0 LDEL0 Lrow0_a0 Ldat_a0 Lsel_a0.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  pose proof (W_sok_win C A1 m1 _ (s - 1104) (Z.to_nat 1104) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 1410112 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m1]).
  pose proof (exW_kn_fixed SEGS C A1 m1 _ (ex_envL vals0 r1 [exW_canary SEGS 1410112 m1]) (EVar 71) (EVar 32) (exW_canary SEGS 1410112 m1) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc1 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A1 M1 (with_vmmaps vm1 md) /\ POSTM C A1 s m1 M1).
  { subst M1. apply (exW_win C A1 A1 m1 _ E1 log1 (EVar 32) s 1104 CK HW1 (sub_live_refl A1) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi]. }
  destruct WP1 as [HWs1 PMs1].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log1 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC1 : carry log1 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc1 : know_ok SEGS E1 M1 kn1) by (apply (carry_after SEGS E1 m1 log1 kn0 [] kn1 scs hs HC1 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose (BS1 := [(32%nat, s); (35%nat, psel); (36%nat, sel); (37%nat, dat); (38%nat, row0)]).
  exW_regfactB BS1 HR ex_r10 Q10_1. exW_regfactB BS1 HR ex_r1 Q1_1. exW_regfactB BS1 HR ex_r2 Q2_1. exW_regfactB BS1 HR ex_r4 Q4_1.
  clear BS1.
  lazymatch type of Q2_1 with _ = Z_to_bv 64 (s + ?off) => pose (OFF1 := off) end.
  lazymatch type of Q1_1 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_1 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A1 M1 _ Rc1 (Z_to_bv 64 dat) (Z_to_bv 64 ret) 8 sp' S CK HWs1 Q10_1 Ldat_a1 F0dat Q1_1
             ltac:(red; apply bv_eq; reflexivity) Q4_1 Q2_1 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A2 m2 vm2 r2 HW2 CS1 Ddat_2 LEQ1 PMc1 RM1.
  rewrite with_vmmaps_twice in HW2 |- *. rewrite with_vmmaps_vmmaps in RM1.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT1 RM1 ltac:(lia) ltac:(lia)) as RT2. cbn [Z.add] in RT2.
  assert (Lsel_a2 : live A2 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ1 _ NE_sel_dat); exact Lsel_a1).
  assert (Drow0_2 : live A2 (Z_to_bv 64 row0) = None) by (rewrite (LEQ1 _ (not_eq_sym NE_dat_row0)); exact Drow0_1).
  assert (SUB1 : sub_live A2 A1).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 dat) by (intros ->; rewrite Ddat_2 in Lq; discriminate Lq). rewrite <- (LEQ1 q NEq). exact Lq. }
  assert (PM2 : POSTM C A2 s m0 m2).
  { apply (POSTM_trans C A2 s m0 M1 m2); [apply (POSTM_sub C A2 A1 _ _ _ SUB1); exact (POSTM_trans _ _ _ _ _ _ PM1 PMs1)|].
    apply (POSTM_mono C A2 (s + OFF1) s); [unfold OFF1; lia | exact PMc1]. }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 dat :: [Z_to_bv 64 row0])) => eq_trans (LEQ1 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL1 q (fun XX => Hq (or_intror XX)))) as LDEL2.
  assert (KEPT1 : Forall (ex_region_kept E1 M1 m2) [(EVar 32, OFF1, 0%Z); (EVar 35, 0%Z, 8%Z); (EVar 36, 0%Z, 32%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF1 1104 M1 m2 E1 (EVar 32) CK (proj1 PMc1) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (sd_kept_cell C (s + OFF1) psel M1 m2 E1 (EVar 35) CK (proj1 PMc1) ltac:(unfold OFF1; lia) ltac:(unfold OFF1; lia) RP eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A2 A1 M1 _ M1 m2 E1 (EVar 36) sel 32 CK HWs1 Lsel_a1 RRsel eq_refl (proj2 PMc1) Lsel_a2 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E1 M1 m2 _ [] _ HKc1 KEPT1) as HKk1.
  match type of HKk1 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E1 m2 kk') in HKk1 end.
  pose proof (regs_ok_agree 72%nat E1 (ex_envL vals1 r2 [exW_canary SEGS 1410112 m2]) _ _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa1.
  pose proof (exW_regs_call _ _ _ _ _ HRa1 (ex_regs_ok_junk vals1 r2 [exW_canary SEGS 1410112 m2] 72%nat ltac:(vm_cast_no_check (eq_refl 72%nat))) CS1) as HRn2.
  clear HRa1.
  assert (HKa2 : know_ok SEGS (ex_envL vals1 r2 [exW_canary SEGS 1410112 m2]) m2 _) by (exact (know_ok_agree SEGS 72%nat E1 _ m2 _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk1)).
  rewrite (fr_denot_agree 72%nat E1 (ex_envL vals1 r2 [exW_canary SEGS 1410112 m2]) _ fr (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc1 HKk1 KEPT1 HC1 HWs1 PMs1 Q10_1 Q1_1 Q2_1 Q4_1 PM1 HW1 PMc1 CS1 SUB1 RM1 RT1 LEQ1 OFF1 LDEL1 Ldat_a1 Lsel_a1 Drow0_1.
  subst M1. clear log1. clear E1. try clear Rc1. clear KN1.
  lazymatch type of HRn2 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn2 end.
  pose proof (W_sok_win C A2 m2 _ (s - 1104) (Z.to_nat 1104) CK HW2 GLO1 GLO2) as SOK2.
  pose proof (exW_canary_ok SEGS 1410112 m2 (canary_any m2)) as CANOK2.
  pose (vals2 := vals1 ++ map (getr r2) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m2]).
  pose proof (exW_kn_fixed SEGS C A2 m2 _ (ex_envL vals1 r2 [exW_canary SEGS 1410112 m2]) (EVar 104) (EVar 32) (exW_canary SEGS 1410112 m2) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW2 eq_refl (proj1 CANOK2) (proj2 CANOK2) eq_refl eq_refl eq_refl SOK2 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf2.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf2 HKa2)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn2 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN2 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf2 HKa2 SOK2 CANOK2.
  repeat match goal with H : getr r2 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc2 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E2 := EEx) in HR, Hlf, HK, Hms |- *; set (log2 := LLx) in Hms, Hlf; set (M2 := mem_denot E2 m2 log2) in Hms end.
  assert (WP2 : W C A2 M2 (with_vmmaps vm2 md) /\ POSTM C A2 s m2 M2).
  { subst M2. apply (exW_win C A2 A2 m2 _ E2 log2 (EVar 32) s 1104 CK HW2 (sub_live_refl A2) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi]. }
  destruct WP2 as [HWs2 PMs2].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log2 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC2 : carry log2 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc2 : know_ok SEGS E2 M2 kn1) by (apply (carry_after SEGS E2 m2 log2 kn0 [] kn1 scs hs HC2 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact Hms |].
  pose (BS2 := [(32%nat, s); (35%nat, psel); (36%nat, sel); (37%nat, dat); (38%nat, row0)]).
  exW_regfactB BS2 HR ex_r10 Q10_2. exW_regfactB BS2 HR ex_r1 Q1_2. exW_regfactB BS2 HR ex_r2 Q2_2. exW_regfactB BS2 HR ex_r4 Q4_2.
  clear BS2.
  lazymatch type of Q2_2 with _ = Z_to_bv 64 (s + ?off) => pose (OFF2 := off) end.
  lazymatch type of Q1_2 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_2 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A2 M2 _ Rc2 (Z_to_bv 64 sel) (Z_to_bv 64 ret) 32 sp' S CK HWs2 Q10_2 Lsel_a2 F0sel Q1_2
             ltac:(red; apply bv_eq; reflexivity) Q4_2 Q2_2 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A3 m3 vm3 r3 HW3 CS2 Dsel_3 LEQ2 PMc2 RM2.
  rewrite with_vmmaps_twice in HW3 |- *. rewrite with_vmmaps_vmmaps in RM2.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT2 RM2 ltac:(lia) ltac:(lia)) as RT3. cbn [Z.add] in RT3.
  assert (Drow0_3 : live A3 (Z_to_bv 64 row0) = None) by (rewrite (LEQ2 _ (not_eq_sym NE_sel_row0)); exact Drow0_2).
  assert (Ddat_3 : live A3 (Z_to_bv 64 dat) = None) by (rewrite (LEQ2 _ (not_eq_sym NE_sel_dat)); exact Ddat_2).
  assert (SUB2 : sub_live A3 A2).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 sel) by (intros ->; rewrite Dsel_3 in Lq; discriminate Lq). rewrite <- (LEQ2 q NEq). exact Lq. }
  assert (PM3 : POSTM C A3 s m0 m3).
  { apply (POSTM_trans C A3 s m0 M2 m3); [apply (POSTM_sub C A3 A2 _ _ _ SUB2); exact (POSTM_trans _ _ _ _ _ _ PM2 PMs2)|].
    apply (POSTM_mono C A3 (s + OFF2) s); [unfold OFF2; lia | exact PMc2]. }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 sel :: [Z_to_bv 64 dat; Z_to_bv 64 row0])) => eq_trans (LEQ2 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL2 q (fun XX => Hq (or_intror XX)))) as LDEL3.
  assert (KEPT2 : Forall (ex_region_kept E2 M2 m3) [(EVar 32, OFF2, 0%Z); (EVar 35, 0%Z, 8%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF2 1104 M2 m3 E2 (EVar 32) CK (proj1 PMc2) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (sd_kept_cell C (s + OFF2) psel M2 m3 E2 (EVar 35) CK (proj1 PMc2) ltac:(unfold OFF2; lia) ltac:(unfold OFF2; lia) RP eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E2 M2 m3 _ [] _ HKc2 KEPT2) as HKk2.
  match type of HKk2 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E2 m3 kk') in HKk2 end.
  pose proof (regs_ok_agree 105%nat E2 (ex_envL vals2 r3 [exW_canary SEGS 1410112 m3]) _ _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa2.
  pose proof (exW_regs_call _ _ _ _ _ HRa2 (ex_regs_ok_junk vals2 r3 [exW_canary SEGS 1410112 m3] 105%nat ltac:(vm_cast_no_check (eq_refl 105%nat))) CS2) as HRn3.
  clear HRa2.
  assert (HKa3 : know_ok SEGS (ex_envL vals2 r3 [exW_canary SEGS 1410112 m3]) m3 _) by (exact (know_ok_agree SEGS 105%nat E2 _ m3 _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk2)).
  rewrite (fr_denot_agree 105%nat E2 (ex_envL vals2 r3 [exW_canary SEGS 1410112 m3]) _ fr (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc2 HKk2 KEPT2 HC2 HWs2 PMs2 Q10_2 Q1_2 Q2_2 Q4_2 PM2 HW2 PMc2 CS2 SUB2 RM2 RT2 LEQ2 OFF2 LDEL2 Lsel_a2 Drow0_2 Ddat_2.
  subst M2. clear log2. clear E2. try clear Rc2. clear KN2.
  lazymatch type of HRn3 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn3 end.
  pose proof (W_sok_win C A3 m3 _ (s - 1104) (Z.to_nat 1104) CK HW3 GLO1 GLO2) as SOK3.
  pose proof (exW_canary_ok SEGS 1410112 m3 (canary_any m3)) as CANOK3.
  pose (vals3 := vals2 ++ map (getr r3) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m3]).
  pose proof (exW_kn_fixed SEGS C A3 m3 _ (ex_envL vals2 r3 [exW_canary SEGS 1410112 m3]) (EVar 137) (EVar 32) (exW_canary SEGS 1410112 m3) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW3 eq_refl (proj1 CANOK3) (proj2 CANOK3) eq_refl eq_refl eq_refl SOK3 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf3.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf3 HKa3)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn3 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN3 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf3 HKa3 SOK3 CANOK3.
  repeat match goal with H : getr r3 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E3 := EEx) in HR, Hlf, HK, Hms |- *; set (log3 := LLx) in Hms, Hlf; set (M3 := mem_denot E3 m3 log3) in Hms end.
  assert (WP3 : W C A3 M3 (with_vmmaps vm3 md) /\ POSTM C A3 (psel + 8) m3 M3 /\ (forall a : word, (s <= u a < psel)%Z -> M3 a = m3 a)).
  { subst M3. apply (sd_win_cell C A3 A3 m3 _ E3 log3 (EVar 32) (EVar 35) s 1104 psel CK HW3 (sub_live_refl A3) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | reflexivity | lia | exact GLO1 | exact Hsp | exact Hph]. }
  destruct WP3 as (HWs3 & PMs3 & BET3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact Hms |].
  pose (BSF := [(32%nat, s); (35%nat, psel)]).
  exW_cellB HK Hlf r0 BSF (EVar 35) psel 0%Z 8%nat Cpsel.
  refine (HC A3 M3 vm3 RcF HWs3 _ Dsel_3 Ddat_3 Drow0_3
            ltac:(intros q Hq; apply LDEL3; intros Hin; apply Hq; cbn [In] in Hin |- *; tauto)
            (POSTM_trans _ _ _ _ _ _ (POSTM_mono C A3 s (psel + 8) m0 m3 ltac:(lia) PM3) PMs3) Cpsel
            (fun a Ha => eq_trans (BET3 a Ha) (sd_frm_above C s m0 m3 a CK (proj1 PM3) ltac:(lia) ltac:(lia))) RT3).
  lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 RcF [(2%nat, EVar 32); (4%nat, ELit 1278416)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor; [symmetry; exact HTP | constructor]] | vm_compute; reflexivity] end.
Qed.

(* [comment removed for export] *)
Lemma seld_chain4 : forall (fx : FPState) C A m md regs (s psel sel dat row0 row1 row2 row3 n0 n1 n2 n3 : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + O23LeptSelDC.SELD_WIN <= s)%Z -> (s <= psel)%Z -> (psel + 8 <= c_top C)%Z -> (psel mod 8 = 0)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 1278416 -> getr regs 10 = Z_to_bv 64 psel ->
  rdn SEGS m (Z_to_bv 64 (psel + 0)) 8 = Some (Z_to_le_bytes 8 sel) ->
  rdn SEGS m (Z_to_bv 64 (sel + 0)) 4 = Some (Z_to_le_bytes 4 4) ->
  rdn SEGS m (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 dat) ->
  rdn SEGS m (Z_to_bv 64 (sel + 24)) 8 = Some (Z_to_le_bytes 8 0) ->
  rdn SEGS m (Z_to_bv 64 (dat + 0)) 8 = Some (Z_to_le_bytes 8 row0) ->
  rdn SEGS m (Z_to_bv 64 (dat + 8)) 8 = Some (Z_to_le_bytes 8 row1) ->
  rdn SEGS m (Z_to_bv 64 (dat + 16)) 8 = Some (Z_to_le_bytes 8 row2) ->
  rdn SEGS m (Z_to_bv 64 (dat + 24)) 8 = Some (Z_to_le_bytes 8 row3) ->
  live A (Z_to_bv 64 sel) = Some 32%Z -> live (c_A0 C) (Z_to_bv 64 sel) = None -> (0 <= sel < 2 ^ 64)%Z ->
  live A (Z_to_bv 64 dat) = Some 32%Z -> live (c_A0 C) (Z_to_bv 64 dat) = None -> (0 <= dat < 2 ^ 64)%Z ->
  live A (Z_to_bv 64 row0) = Some n0%Z -> live (c_A0 C) (Z_to_bv 64 row0) = None -> (0 <= row0 < 2 ^ 64)%Z ->
  live A (Z_to_bv 64 row1) = Some n1%Z -> live (c_A0 C) (Z_to_bv 64 row1) = None -> (0 <= row1 < 2 ^ 64)%Z ->
  live A (Z_to_bv 64 row2) = Some n2%Z -> live (c_A0 C) (Z_to_bv 64 row2) = None -> (0 <= row2 < 2 ^ 64)%Z ->
  live A (Z_to_bv 64 row3) = Some n3%Z -> live (c_A0 C) (Z_to_bv 64 row3) = None -> (0 <= row3 < 2 ^ 64)%Z ->
  Z_to_bv 64 sel <> Z_to_bv 64 dat ->
  Z_to_bv 64 sel <> Z_to_bv 64 row0 ->
  Z_to_bv 64 dat <> Z_to_bv 64 row0 ->
  Z_to_bv 64 sel <> Z_to_bv 64 row1 ->
  Z_to_bv 64 dat <> Z_to_bv 64 row1 ->
  Z_to_bv 64 row0 <> Z_to_bv 64 row1 ->
  Z_to_bv 64 sel <> Z_to_bv 64 row2 ->
  Z_to_bv 64 dat <> Z_to_bv 64 row2 ->
  Z_to_bv 64 row0 <> Z_to_bv 64 row2 ->
  Z_to_bv 64 row1 <> Z_to_bv 64 row2 ->
  Z_to_bv 64 sel <> Z_to_bv 64 row3 ->
  Z_to_bv 64 dat <> Z_to_bv 64 row3 ->
  Z_to_bv 64 row0 <> Z_to_bv 64 row3 ->
  Z_to_bv 64 row1 <> Z_to_bv 64 row3 ->
  Z_to_bv 64 row2 <> Z_to_bv 64 row3 ->
  (forall A' m' vm' regs',
     W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     live A' (Z_to_bv 64 sel) = None ->
     live A' (Z_to_bv 64 dat) = None ->
     live A' (Z_to_bv 64 row0) = None ->
     live A' (Z_to_bv 64 row1) = None ->
     live A' (Z_to_bv 64 row2) = None ->
     live A' (Z_to_bv 64 row3) = None ->
     (forall q : word, ~ In q [Z_to_bv 64 sel; Z_to_bv 64 dat; Z_to_bv 64 row0; Z_to_bv 64 row1; Z_to_bv 64 row2; Z_to_bv 64 row3] -> live A' q = live A q) ->
     POSTM C A' (psel + 8) m m' -> rdn SEGS m' (Z_to_bv 64 (psel + 0)) 8 = Some (Z_to_le_bytes 8 0) ->
     (forall a : word, (s <= u a < psel)%Z -> m' a = m a) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 674932) m al_rom) md) S.
Proof using P16 PINS.
  intros fx C A0 m0 md r0 s psel sel dat row0 row1 row2 row3 n0 n1 n2 n3 ret S CK HW0 H2 Hs16 Hlo Hsp Hph Hpal H1 Hret H4 H10 Mpsel Msy Mdat Mnm Mrow0 Mrow1 Mrow2 Mrow3
    Lsel_a0 F0sel RRsel Ldat_a0 F0dat RRdat Lrow0_a0 F0row0 RRrow0 Lrow1_a0 F0row1 RRrow1 Lrow2_a0 F0row2 RRrow2 Lrow3_a0 F0row3 RRrow3
    NE_sel_dat NE_sel_row0 NE_dat_row0 NE_sel_row1 NE_dat_row1 NE_row0_row1 NE_sel_row2 NE_dat_row2 NE_row0_row2 NE_row1_row2 NE_sel_row3 NE_dat_row3 NE_row0_row3 NE_row1_row3 NE_row2_row3 HC.
  unfold O23LeptSelDC.SELD_WIN in *.
  assert (Hhi : (s <= c_top C)%Z) by lia.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  assert (HTP : ex_keep (getr r0 ex_r4 = Z_to_bv 64 1278416)) by exact H4.
  destruct fx as [fr cs]. pose proof I as FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  assert (GLO1 : (c_top C - LSTK <= s - 1104)%Z) by lia.
  assert (GLO2 : (s - 1104 + Z.of_nat (Z.to_nat 1104) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (1104 <= s)%Z) by lia.
  assert (RP : (0 <= psel < 2 ^ 64)%Z) by lia.
  destruct (exW_blk_rng C A0 m0 _ sel 32 CK HW0 Lsel_a0 RRsel ltac:(lia)) as (GLsel & _ & GHsel).
  pose proof (ai_live_hull A0 m0 (m_vmmaps md) _ _ (w_inv _ _ _ _ HW0) Lsel_a0) as (_ & ALsel & _). rewrite u_Z2bv in ALsel by lia.
  pose proof (exW_win_blk_apart_h C A0 m0 _ s 1104 sel 32 CK HW0 Lsel_a0 eq_refl RRsel GLO1) as WAPsel.
  destruct (exW_blk_rng C A0 m0 _ dat 32 CK HW0 Ldat_a0 RRdat ltac:(lia)) as (GLdat & _ & GHdat).
  pose proof (ai_live_hull A0 m0 (m_vmmaps md) _ _ (w_inv _ _ _ _ HW0) Ldat_a0) as (_ & ALdat & _). rewrite u_Z2bv in ALdat by lia.
  pose proof (exW_win_blk_apart_h C A0 m0 _ s 1104 dat 32 CK HW0 Ldat_a0 eq_refl RRdat GLO1) as WAPdat.
  pose proof (W_sok_win C A0 m0 _ psel 8 CK HW0 ltac:(lia) ltac:(cbn; lia)) as SOKP.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose proof (POSTM_refl C A0 s m0) as PM0.
  pose proof (roomtr_refl A0 vm0 0 0 ltac:(lia) ltac:(lia)) as RT0.
  pose (valsI := @nil word).
  pose proof (fun (q : word) (_ : ~ In q []) => eq_refl (live A0 q)) as LDEL0.
  pose proof (W_sok_win C A0 m0 _ (s - 1104) (Z.to_nat 1104) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 1410112 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0; psel; sel; dat; row0; row1; row2; row3]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0; psel; sel; dat; row0; row1; row2; row3]) (EVar 34) (EVar 32) (exW_canary SEGS 1410112 m0) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0; psel; sel; dat; row0; row1; row2; row3]) m0 [KRange (EVar 32) 1422416 (2 ^ 63); KAlign (EVar 32) 16; KRange (EVar 35) 1422416 (2 ^ 63); KAlign (EVar 35) 8; KWr (SA (EVar 35) 0) 8; KWord (SA (EVar 35) 0) 8 (EVar 36); KDisj (SA (EVar 32) (- 1104)) 1104 (SA (EVar 35) 0) 8; KRange (EVar 36) 4096 (2 ^ 47); KAlign (EVar 36) 16; KDisj (SA (EVar 32) (- 1104)) 1104 (SA (EVar 36) 0) 32; KWord (SA (EVar 36) 0) 4 (ELit 4); KWord (SA (EVar 36) 16) 8 (EVar 37); KWord (SA (EVar 36) 24) 8 (ELit 0); KRange (EVar 37) 4096 (2 ^ 47); KAlign (EVar 37) 16; KDisj (SA (EVar 32) (- 1104)) 1104 (SA (EVar 37) 0) 32; KWord (SA (EVar 37) 0) 8 (EVar 38); KWord (SA (EVar 37) 8) 8 (EVar 39); KWord (SA (EVar 37) 16) 8 (EVar 40); KWord (SA (EVar 37) 24) 8 (EVar 41)]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 HKf0)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0; psel; sel; dat; row0; row1; row2; row3] HR.
  pose proof (ex_regs_ok_reexpr _ _ r0 ex_r10 (EVar 35) HR ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact H10)) as HRx. clear HR. rename HRx into HR.
  lazymatch type of HR with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HR end.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win C A0 A0 m0 _ E0 log0 (EVar 32) s 1104 CK HW0 (sub_live_refl A0) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi]. }
  destruct WP0 as [HWs0 PMs0].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (35%nat, psel); (36%nat, sel); (37%nat, dat); (38%nat, row0); (39%nat, row1); (40%nat, row2); (41%nat, row3)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r1 Q1_0. exW_regfactB BS0 HR ex_r2 Q2_0. exW_regfactB BS0 HR ex_r4 Q4_0.
  clear BS0.
  lazymatch type of Q2_0 with _ = Z_to_bv 64 (s + ?off) => pose (OFF0 := off) end.
  lazymatch type of Q1_0 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_0 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A0 M0 _ Rc0 (Z_to_bv 64 row0) (Z_to_bv 64 ret) n0 sp' S CK HWs0 Q10_0 Lrow0_a0 F0row0 Q1_0
             ltac:(red; apply bv_eq; reflexivity) Q4_0 Q2_0 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A1 m1 vm1 r1 HW1 CS0 Drow0_1 LEQ0 PMc0 RM0.
  rewrite with_vmmaps_twice in HW1 |- *. rewrite with_vmmaps_vmmaps in RM0.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT0 RM0 ltac:(lia) ltac:(lia)) as RT1. cbn [Z.add] in RT1.
  assert (Lrow1_a1 : live A1 (Z_to_bv 64 row1) = Some n1%Z) by (rewrite (LEQ0 _ (not_eq_sym NE_row0_row1)); exact Lrow1_a0).
  assert (Lrow2_a1 : live A1 (Z_to_bv 64 row2) = Some n2%Z) by (rewrite (LEQ0 _ (not_eq_sym NE_row0_row2)); exact Lrow2_a0).
  assert (Lrow3_a1 : live A1 (Z_to_bv 64 row3) = Some n3%Z) by (rewrite (LEQ0 _ (not_eq_sym NE_row0_row3)); exact Lrow3_a0).
  assert (Ldat_a1 : live A1 (Z_to_bv 64 dat) = Some 32%Z) by (rewrite (LEQ0 _ NE_dat_row0); exact Ldat_a0).
  assert (Lsel_a1 : live A1 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ0 _ NE_sel_row0); exact Lsel_a0).
  assert (SUB0 : sub_live A1 A0).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row0) by (intros ->; rewrite Drow0_1 in Lq; discriminate Lq). rewrite <- (LEQ0 q NEq). exact Lq. }
  assert (PM1 : POSTM C A1 s m0 m1).
  { apply (POSTM_trans C A1 s m0 M0 m1); [apply (POSTM_sub C A1 A0 _ _ _ SUB0); exact (POSTM_trans _ _ _ _ _ _ PM0 PMs0)|].
    apply (POSTM_mono C A1 (s + OFF0) s); [unfold OFF0; lia | exact PMc0]. }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row0 :: [])) => eq_trans (LEQ0 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL0 q (fun XX => Hq (or_intror XX)))) as LDEL1.
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, OFF0, 0%Z); (EVar 35, 0%Z, 8%Z); (EVar 36, 0%Z, 32%Z); (EVar 37, 0%Z, 32%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF0 1104 M0 m1 E0 (EVar 32) CK (proj1 PMc0) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (sd_kept_cell C (s + OFF0) psel M0 m1 E0 (EVar 35) CK (proj1 PMc0) ltac:(unfold OFF0; lia) ltac:(unfold OFF0; lia) RP eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A1 A0 M0 _ M0 m1 E0 (EVar 36) sel 32 CK HWs0 Lsel_a0 RRsel eq_refl (proj2 PMc0) Lsel_a1 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A1 A0 M0 _ M0 m1 E0 (EVar 37) dat 32 CK HWs0 Ldat_a0 RRdat eq_refl (proj2 PMc0) Ldat_a1 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E0 m1 kk') in HKk0 end.
  pose proof (regs_ok_agree 42%nat E0 (ex_envL vals0 r1 [exW_canary SEGS 1410112 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [exW_canary SEGS 1410112 m1] 42%nat ltac:(vm_cast_no_check (eq_refl 42%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [exW_canary SEGS 1410112 m1]) m1 _) by (exact (know_ok_agree SEGS 42%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  rewrite (fr_denot_agree 42%nat E0 (ex_envL vals0 r1 [exW_canary SEGS 1410112 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q1_0 Q2_0 Q4_0 PM0 HW0 PMc0 CS0 SUB0 RM0 RT0 LEQ0 OFF0 LDEL0 Lrow0_a0 Lrow1_a0 Lrow2_a0 Lrow3_a0 Ldat_a0 Lsel_a0.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  pose proof (W_sok_win C A1 m1 _ (s - 1104) (Z.to_nat 1104) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 1410112 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m1]).
  pose proof (exW_kn_fixed SEGS C A1 m1 _ (ex_envL vals0 r1 [exW_canary SEGS 1410112 m1]) (EVar 74) (EVar 32) (exW_canary SEGS 1410112 m1) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc1 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A1 M1 (with_vmmaps vm1 md) /\ POSTM C A1 s m1 M1).
  { subst M1. apply (exW_win C A1 A1 m1 _ E1 log1 (EVar 32) s 1104 CK HW1 (sub_live_refl A1) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi]. }
  destruct WP1 as [HWs1 PMs1].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log1 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC1 : carry log1 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc1 : know_ok SEGS E1 M1 kn1) by (apply (carry_after SEGS E1 m1 log1 kn0 [] kn1 scs hs HC1 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose (BS1 := [(32%nat, s); (35%nat, psel); (36%nat, sel); (37%nat, dat); (38%nat, row0); (39%nat, row1); (40%nat, row2); (41%nat, row3)]).
  exW_regfactB BS1 HR ex_r10 Q10_1. exW_regfactB BS1 HR ex_r1 Q1_1. exW_regfactB BS1 HR ex_r2 Q2_1. exW_regfactB BS1 HR ex_r4 Q4_1.
  clear BS1.
  lazymatch type of Q2_1 with _ = Z_to_bv 64 (s + ?off) => pose (OFF1 := off) end.
  lazymatch type of Q1_1 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_1 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A1 M1 _ Rc1 (Z_to_bv 64 row1) (Z_to_bv 64 ret) n1 sp' S CK HWs1 Q10_1 Lrow1_a1 F0row1 Q1_1
             ltac:(red; apply bv_eq; reflexivity) Q4_1 Q2_1 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A2 m2 vm2 r2 HW2 CS1 Drow1_2 LEQ1 PMc1 RM1.
  rewrite with_vmmaps_twice in HW2 |- *. rewrite with_vmmaps_vmmaps in RM1.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT1 RM1 ltac:(lia) ltac:(lia)) as RT2. cbn [Z.add] in RT2.
  assert (Lrow2_a2 : live A2 (Z_to_bv 64 row2) = Some n2%Z) by (rewrite (LEQ1 _ (not_eq_sym NE_row1_row2)); exact Lrow2_a1).
  assert (Lrow3_a2 : live A2 (Z_to_bv 64 row3) = Some n3%Z) by (rewrite (LEQ1 _ (not_eq_sym NE_row1_row3)); exact Lrow3_a1).
  assert (Ldat_a2 : live A2 (Z_to_bv 64 dat) = Some 32%Z) by (rewrite (LEQ1 _ NE_dat_row1); exact Ldat_a1).
  assert (Lsel_a2 : live A2 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ1 _ NE_sel_row1); exact Lsel_a1).
  assert (Drow0_2 : live A2 (Z_to_bv 64 row0) = None) by (rewrite (LEQ1 _ NE_row0_row1); exact Drow0_1).
  assert (SUB1 : sub_live A2 A1).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row1) by (intros ->; rewrite Drow1_2 in Lq; discriminate Lq). rewrite <- (LEQ1 q NEq). exact Lq. }
  assert (PM2 : POSTM C A2 s m0 m2).
  { apply (POSTM_trans C A2 s m0 M1 m2); [apply (POSTM_sub C A2 A1 _ _ _ SUB1); exact (POSTM_trans _ _ _ _ _ _ PM1 PMs1)|].
    apply (POSTM_mono C A2 (s + OFF1) s); [unfold OFF1; lia | exact PMc1]. }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row1 :: [Z_to_bv 64 row0])) => eq_trans (LEQ1 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL1 q (fun XX => Hq (or_intror XX)))) as LDEL2.
  assert (KEPT1 : Forall (ex_region_kept E1 M1 m2) [(EVar 32, OFF1, 0%Z); (EVar 35, 0%Z, 8%Z); (EVar 36, 0%Z, 32%Z); (EVar 37, 0%Z, 32%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF1 1104 M1 m2 E1 (EVar 32) CK (proj1 PMc1) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (sd_kept_cell C (s + OFF1) psel M1 m2 E1 (EVar 35) CK (proj1 PMc1) ltac:(unfold OFF1; lia) ltac:(unfold OFF1; lia) RP eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A2 A1 M1 _ M1 m2 E1 (EVar 36) sel 32 CK HWs1 Lsel_a1 RRsel eq_refl (proj2 PMc1) Lsel_a2 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A2 A1 M1 _ M1 m2 E1 (EVar 37) dat 32 CK HWs1 Ldat_a1 RRdat eq_refl (proj2 PMc1) Ldat_a2 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E1 M1 m2 _ [] _ HKc1 KEPT1) as HKk1.
  match type of HKk1 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E1 m2 kk') in HKk1 end.
  pose proof (regs_ok_agree 75%nat E1 (ex_envL vals1 r2 [exW_canary SEGS 1410112 m2]) _ _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa1.
  pose proof (exW_regs_call _ _ _ _ _ HRa1 (ex_regs_ok_junk vals1 r2 [exW_canary SEGS 1410112 m2] 75%nat ltac:(vm_cast_no_check (eq_refl 75%nat))) CS1) as HRn2.
  clear HRa1.
  assert (HKa2 : know_ok SEGS (ex_envL vals1 r2 [exW_canary SEGS 1410112 m2]) m2 _) by (exact (know_ok_agree SEGS 75%nat E1 _ m2 _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk1)).
  rewrite (fr_denot_agree 75%nat E1 (ex_envL vals1 r2 [exW_canary SEGS 1410112 m2]) _ fr (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc1 HKk1 KEPT1 HC1 HWs1 PMs1 Q10_1 Q1_1 Q2_1 Q4_1 PM1 HW1 PMc1 CS1 SUB1 RM1 RT1 LEQ1 OFF1 LDEL1 Lrow1_a1 Lrow2_a1 Lrow3_a1 Ldat_a1 Lsel_a1 Drow0_1.
  subst M1. clear log1. clear E1. try clear Rc1. clear KN1.
  lazymatch type of HRn2 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn2 end.
  pose proof (W_sok_win C A2 m2 _ (s - 1104) (Z.to_nat 1104) CK HW2 GLO1 GLO2) as SOK2.
  pose proof (exW_canary_ok SEGS 1410112 m2 (canary_any m2)) as CANOK2.
  pose (vals2 := vals1 ++ map (getr r2) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m2]).
  pose proof (exW_kn_fixed SEGS C A2 m2 _ (ex_envL vals1 r2 [exW_canary SEGS 1410112 m2]) (EVar 107) (EVar 32) (exW_canary SEGS 1410112 m2) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW2 eq_refl (proj1 CANOK2) (proj2 CANOK2) eq_refl eq_refl eq_refl SOK2 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf2.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf2 HKa2)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn2 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN2 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf2 HKa2 SOK2 CANOK2.
  repeat match goal with H : getr r2 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc2 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E2 := EEx) in HR, Hlf, HK, Hms |- *; set (log2 := LLx) in Hms, Hlf; set (M2 := mem_denot E2 m2 log2) in Hms end.
  assert (WP2 : W C A2 M2 (with_vmmaps vm2 md) /\ POSTM C A2 s m2 M2).
  { subst M2. apply (exW_win C A2 A2 m2 _ E2 log2 (EVar 32) s 1104 CK HW2 (sub_live_refl A2) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi]. }
  destruct WP2 as [HWs2 PMs2].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log2 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC2 : carry log2 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc2 : know_ok SEGS E2 M2 kn1) by (apply (carry_after SEGS E2 m2 log2 kn0 [] kn1 scs hs HC2 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact Hms |].
  pose (BS2 := [(32%nat, s); (35%nat, psel); (36%nat, sel); (37%nat, dat); (38%nat, row0); (39%nat, row1); (40%nat, row2); (41%nat, row3)]).
  exW_regfactB BS2 HR ex_r10 Q10_2. exW_regfactB BS2 HR ex_r1 Q1_2. exW_regfactB BS2 HR ex_r2 Q2_2. exW_regfactB BS2 HR ex_r4 Q4_2.
  clear BS2.
  lazymatch type of Q2_2 with _ = Z_to_bv 64 (s + ?off) => pose (OFF2 := off) end.
  lazymatch type of Q1_2 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_2 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A2 M2 _ Rc2 (Z_to_bv 64 row2) (Z_to_bv 64 ret) n2 sp' S CK HWs2 Q10_2 Lrow2_a2 F0row2 Q1_2
             ltac:(red; apply bv_eq; reflexivity) Q4_2 Q2_2 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A3 m3 vm3 r3 HW3 CS2 Drow2_3 LEQ2 PMc2 RM2.
  rewrite with_vmmaps_twice in HW3 |- *. rewrite with_vmmaps_vmmaps in RM2.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT2 RM2 ltac:(lia) ltac:(lia)) as RT3. cbn [Z.add] in RT3.
  assert (Lrow3_a3 : live A3 (Z_to_bv 64 row3) = Some n3%Z) by (rewrite (LEQ2 _ (not_eq_sym NE_row2_row3)); exact Lrow3_a2).
  assert (Ldat_a3 : live A3 (Z_to_bv 64 dat) = Some 32%Z) by (rewrite (LEQ2 _ NE_dat_row2); exact Ldat_a2).
  assert (Lsel_a3 : live A3 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ2 _ NE_sel_row2); exact Lsel_a2).
  assert (Drow0_3 : live A3 (Z_to_bv 64 row0) = None) by (rewrite (LEQ2 _ NE_row0_row2); exact Drow0_2).
  assert (Drow1_3 : live A3 (Z_to_bv 64 row1) = None) by (rewrite (LEQ2 _ NE_row1_row2); exact Drow1_2).
  assert (SUB2 : sub_live A3 A2).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row2) by (intros ->; rewrite Drow2_3 in Lq; discriminate Lq). rewrite <- (LEQ2 q NEq). exact Lq. }
  assert (PM3 : POSTM C A3 s m0 m3).
  { apply (POSTM_trans C A3 s m0 M2 m3); [apply (POSTM_sub C A3 A2 _ _ _ SUB2); exact (POSTM_trans _ _ _ _ _ _ PM2 PMs2)|].
    apply (POSTM_mono C A3 (s + OFF2) s); [unfold OFF2; lia | exact PMc2]. }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row2 :: [Z_to_bv 64 row1; Z_to_bv 64 row0])) => eq_trans (LEQ2 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL2 q (fun XX => Hq (or_intror XX)))) as LDEL3.
  assert (KEPT2 : Forall (ex_region_kept E2 M2 m3) [(EVar 32, OFF2, 0%Z); (EVar 35, 0%Z, 8%Z); (EVar 36, 0%Z, 32%Z); (EVar 37, 0%Z, 32%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF2 1104 M2 m3 E2 (EVar 32) CK (proj1 PMc2) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (sd_kept_cell C (s + OFF2) psel M2 m3 E2 (EVar 35) CK (proj1 PMc2) ltac:(unfold OFF2; lia) ltac:(unfold OFF2; lia) RP eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A3 A2 M2 _ M2 m3 E2 (EVar 36) sel 32 CK HWs2 Lsel_a2 RRsel eq_refl (proj2 PMc2) Lsel_a3 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A3 A2 M2 _ M2 m3 E2 (EVar 37) dat 32 CK HWs2 Ldat_a2 RRdat eq_refl (proj2 PMc2) Ldat_a3 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E2 M2 m3 _ [] _ HKc2 KEPT2) as HKk2.
  match type of HKk2 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E2 m3 kk') in HKk2 end.
  pose proof (regs_ok_agree 108%nat E2 (ex_envL vals2 r3 [exW_canary SEGS 1410112 m3]) _ _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa2.
  pose proof (exW_regs_call _ _ _ _ _ HRa2 (ex_regs_ok_junk vals2 r3 [exW_canary SEGS 1410112 m3] 108%nat ltac:(vm_cast_no_check (eq_refl 108%nat))) CS2) as HRn3.
  clear HRa2.
  assert (HKa3 : know_ok SEGS (ex_envL vals2 r3 [exW_canary SEGS 1410112 m3]) m3 _) by (exact (know_ok_agree SEGS 108%nat E2 _ m3 _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk2)).
  rewrite (fr_denot_agree 108%nat E2 (ex_envL vals2 r3 [exW_canary SEGS 1410112 m3]) _ fr (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc2 HKk2 KEPT2 HC2 HWs2 PMs2 Q10_2 Q1_2 Q2_2 Q4_2 PM2 HW2 PMc2 CS2 SUB2 RM2 RT2 LEQ2 OFF2 LDEL2 Lrow2_a2 Lrow3_a2 Ldat_a2 Lsel_a2 Drow0_2 Drow1_2.
  subst M2. clear log2. clear E2. try clear Rc2. clear KN2.
  lazymatch type of HRn3 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn3 end.
  pose proof (W_sok_win C A3 m3 _ (s - 1104) (Z.to_nat 1104) CK HW3 GLO1 GLO2) as SOK3.
  pose proof (exW_canary_ok SEGS 1410112 m3 (canary_any m3)) as CANOK3.
  pose (vals3 := vals2 ++ map (getr r3) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m3]).
  pose proof (exW_kn_fixed SEGS C A3 m3 _ (ex_envL vals2 r3 [exW_canary SEGS 1410112 m3]) (EVar 140) (EVar 32) (exW_canary SEGS 1410112 m3) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW3 eq_refl (proj1 CANOK3) (proj2 CANOK3) eq_refl eq_refl eq_refl SOK3 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf3.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf3 HKa3)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn3 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN3 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf3 HKa3 SOK3 CANOK3.
  repeat match goal with H : getr r3 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc3 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E3 := EEx) in HR, Hlf, HK, Hms |- *; set (log3 := LLx) in Hms, Hlf; set (M3 := mem_denot E3 m3 log3) in Hms end.
  assert (WP3 : W C A3 M3 (with_vmmaps vm3 md) /\ POSTM C A3 s m3 M3).
  { subst M3. apply (exW_win C A3 A3 m3 _ E3 log3 (EVar 32) s 1104 CK HW3 (sub_live_refl A3) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi]. }
  destruct WP3 as [HWs3 PMs3].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log3 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC3 : carry log3 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc3 : know_ok SEGS E3 M3 kn1) by (apply (carry_after SEGS E3 m3 log3 kn0 [] kn1 scs hs HC3 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact Hms |].
  pose (BS3 := [(32%nat, s); (35%nat, psel); (36%nat, sel); (37%nat, dat); (38%nat, row0); (39%nat, row1); (40%nat, row2); (41%nat, row3)]).
  exW_regfactB BS3 HR ex_r10 Q10_3. exW_regfactB BS3 HR ex_r1 Q1_3. exW_regfactB BS3 HR ex_r2 Q2_3. exW_regfactB BS3 HR ex_r4 Q4_3.
  clear BS3.
  lazymatch type of Q2_3 with _ = Z_to_bv 64 (s + ?off) => pose (OFF3 := off) end.
  lazymatch type of Q1_3 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_3 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A3 M3 _ Rc3 (Z_to_bv 64 row3) (Z_to_bv 64 ret) n3 sp' S CK HWs3 Q10_3 Lrow3_a3 F0row3 Q1_3
             ltac:(red; apply bv_eq; reflexivity) Q4_3 Q2_3 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A4 m4 vm4 r4 HW4 CS3 Drow3_4 LEQ3 PMc3 RM3.
  rewrite with_vmmaps_twice in HW4 |- *. rewrite with_vmmaps_vmmaps in RM3.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT3 RM3 ltac:(lia) ltac:(lia)) as RT4. cbn [Z.add] in RT4.
  assert (Ldat_a4 : live A4 (Z_to_bv 64 dat) = Some 32%Z) by (rewrite (LEQ3 _ NE_dat_row3); exact Ldat_a3).
  assert (Lsel_a4 : live A4 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ3 _ NE_sel_row3); exact Lsel_a3).
  assert (Drow0_4 : live A4 (Z_to_bv 64 row0) = None) by (rewrite (LEQ3 _ NE_row0_row3); exact Drow0_3).
  assert (Drow1_4 : live A4 (Z_to_bv 64 row1) = None) by (rewrite (LEQ3 _ NE_row1_row3); exact Drow1_3).
  assert (Drow2_4 : live A4 (Z_to_bv 64 row2) = None) by (rewrite (LEQ3 _ NE_row2_row3); exact Drow2_3).
  assert (SUB3 : sub_live A4 A3).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row3) by (intros ->; rewrite Drow3_4 in Lq; discriminate Lq). rewrite <- (LEQ3 q NEq). exact Lq. }
  assert (PM4 : POSTM C A4 s m0 m4).
  { apply (POSTM_trans C A4 s m0 M3 m4); [apply (POSTM_sub C A4 A3 _ _ _ SUB3); exact (POSTM_trans _ _ _ _ _ _ PM3 PMs3)|].
    apply (POSTM_mono C A4 (s + OFF3) s); [unfold OFF3; lia | exact PMc3]. }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row3 :: [Z_to_bv 64 row2; Z_to_bv 64 row1; Z_to_bv 64 row0])) => eq_trans (LEQ3 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL3 q (fun XX => Hq (or_intror XX)))) as LDEL4.
  assert (KEPT3 : Forall (ex_region_kept E3 M3 m4) [(EVar 32, OFF3, 0%Z); (EVar 35, 0%Z, 8%Z); (EVar 36, 0%Z, 32%Z); (EVar 37, 0%Z, 32%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF3 1104 M3 m4 E3 (EVar 32) CK (proj1 PMc3) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (sd_kept_cell C (s + OFF3) psel M3 m4 E3 (EVar 35) CK (proj1 PMc3) ltac:(unfold OFF3; lia) ltac:(unfold OFF3; lia) RP eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A4 A3 M3 _ M3 m4 E3 (EVar 36) sel 32 CK HWs3 Lsel_a3 RRsel eq_refl (proj2 PMc3) Lsel_a4 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A4 A3 M3 _ M3 m4 E3 (EVar 37) dat 32 CK HWs3 Ldat_a3 RRdat eq_refl (proj2 PMc3) Ldat_a4 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E3 M3 m4 _ [] _ HKc3 KEPT3) as HKk3.
  match type of HKk3 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E3 m4 kk') in HKk3 end.
  pose proof (regs_ok_agree 141%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 1410112 m4]) _ _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa3.
  pose proof (exW_regs_call _ _ _ _ _ HRa3 (ex_regs_ok_junk vals3 r4 [exW_canary SEGS 1410112 m4] 141%nat ltac:(vm_cast_no_check (eq_refl 141%nat))) CS3) as HRn4.
  clear HRa3.
  assert (HKa4 : know_ok SEGS (ex_envL vals3 r4 [exW_canary SEGS 1410112 m4]) m4 _) by (exact (know_ok_agree SEGS 141%nat E3 _ m4 _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk3)).
  rewrite (fr_denot_agree 141%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 1410112 m4]) _ fr (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc3 HKk3 KEPT3 HC3 HWs3 PMs3 Q10_3 Q1_3 Q2_3 Q4_3 PM3 HW3 PMc3 CS3 SUB3 RM3 RT3 LEQ3 OFF3 LDEL3 Lrow3_a3 Ldat_a3 Lsel_a3 Drow0_3 Drow1_3 Drow2_3.
  subst M3. clear log3. clear E3. try clear Rc3. clear KN3.
  lazymatch type of HRn4 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn4 end.
  pose proof (W_sok_win C A4 m4 _ (s - 1104) (Z.to_nat 1104) CK HW4 GLO1 GLO2) as SOK4.
  pose proof (exW_canary_ok SEGS 1410112 m4 (canary_any m4)) as CANOK4.
  pose (vals4 := vals3 ++ map (getr r4) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m4]).
  pose proof (exW_kn_fixed SEGS C A4 m4 _ (ex_envL vals3 r4 [exW_canary SEGS 1410112 m4]) (EVar 173) (EVar 32) (exW_canary SEGS 1410112 m4) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW4 eq_refl (proj1 CANOK4) (proj2 CANOK4) eq_refl eq_refl eq_refl SOK4 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf4.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf4 HKa4)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn4 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN4 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf4 HKa4 SOK4 CANOK4.
  repeat match goal with H : getr r4 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc4 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E4 := EEx) in HR, Hlf, HK, Hms |- *; set (log4 := LLx) in Hms, Hlf; set (M4 := mem_denot E4 m4 log4) in Hms end.
  assert (WP4 : W C A4 M4 (with_vmmaps vm4 md) /\ POSTM C A4 s m4 M4).
  { subst M4. apply (exW_win C A4 A4 m4 _ E4 log4 (EVar 32) s 1104 CK HW4 (sub_live_refl A4) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi]. }
  destruct WP4 as [HWs4 PMs4].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log4 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC4 : carry log4 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc4 : know_ok SEGS E4 M4 kn1) by (apply (carry_after SEGS E4 m4 log4 kn0 [] kn1 scs hs HC4 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact Hms |].
  pose (BS4 := [(32%nat, s); (35%nat, psel); (36%nat, sel); (37%nat, dat); (38%nat, row0); (39%nat, row1); (40%nat, row2); (41%nat, row3)]).
  exW_regfactB BS4 HR ex_r10 Q10_4. exW_regfactB BS4 HR ex_r1 Q1_4. exW_regfactB BS4 HR ex_r2 Q2_4. exW_regfactB BS4 HR ex_r4 Q4_4.
  clear BS4.
  lazymatch type of Q2_4 with _ = Z_to_bv 64 (s + ?off) => pose (OFF4 := off) end.
  lazymatch type of Q1_4 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_4 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A4 M4 _ Rc4 (Z_to_bv 64 dat) (Z_to_bv 64 ret) 32 sp' S CK HWs4 Q10_4 Ldat_a4 F0dat Q1_4
             ltac:(red; apply bv_eq; reflexivity) Q4_4 Q2_4 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A5 m5 vm5 r5 HW5 CS4 Ddat_5 LEQ4 PMc4 RM4.
  rewrite with_vmmaps_twice in HW5 |- *. rewrite with_vmmaps_vmmaps in RM4.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT4 RM4 ltac:(lia) ltac:(lia)) as RT5. cbn [Z.add] in RT5.
  assert (Lsel_a5 : live A5 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ4 _ NE_sel_dat); exact Lsel_a4).
  assert (Drow0_5 : live A5 (Z_to_bv 64 row0) = None) by (rewrite (LEQ4 _ (not_eq_sym NE_dat_row0)); exact Drow0_4).
  assert (Drow1_5 : live A5 (Z_to_bv 64 row1) = None) by (rewrite (LEQ4 _ (not_eq_sym NE_dat_row1)); exact Drow1_4).
  assert (Drow2_5 : live A5 (Z_to_bv 64 row2) = None) by (rewrite (LEQ4 _ (not_eq_sym NE_dat_row2)); exact Drow2_4).
  assert (Drow3_5 : live A5 (Z_to_bv 64 row3) = None) by (rewrite (LEQ4 _ (not_eq_sym NE_dat_row3)); exact Drow3_4).
  assert (SUB4 : sub_live A5 A4).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 dat) by (intros ->; rewrite Ddat_5 in Lq; discriminate Lq). rewrite <- (LEQ4 q NEq). exact Lq. }
  assert (PM5 : POSTM C A5 s m0 m5).
  { apply (POSTM_trans C A5 s m0 M4 m5); [apply (POSTM_sub C A5 A4 _ _ _ SUB4); exact (POSTM_trans _ _ _ _ _ _ PM4 PMs4)|].
    apply (POSTM_mono C A5 (s + OFF4) s); [unfold OFF4; lia | exact PMc4]. }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 dat :: [Z_to_bv 64 row3; Z_to_bv 64 row2; Z_to_bv 64 row1; Z_to_bv 64 row0])) => eq_trans (LEQ4 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL4 q (fun XX => Hq (or_intror XX)))) as LDEL5.
  assert (KEPT4 : Forall (ex_region_kept E4 M4 m5) [(EVar 32, OFF4, 0%Z); (EVar 35, 0%Z, 8%Z); (EVar 36, 0%Z, 32%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF4 1104 M4 m5 E4 (EVar 32) CK (proj1 PMc4) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (sd_kept_cell C (s + OFF4) psel M4 m5 E4 (EVar 35) CK (proj1 PMc4) ltac:(unfold OFF4; lia) ltac:(unfold OFF4; lia) RP eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A5 A4 M4 _ M4 m5 E4 (EVar 36) sel 32 CK HWs4 Lsel_a4 RRsel eq_refl (proj2 PMc4) Lsel_a5 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E4 M4 m5 _ [] _ HKc4 KEPT4) as HKk4.
  match type of HKk4 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E4 m5 kk') in HKk4 end.
  pose proof (regs_ok_agree 174%nat E4 (ex_envL vals4 r5 [exW_canary SEGS 1410112 m5]) _ _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa4.
  pose proof (exW_regs_call _ _ _ _ _ HRa4 (ex_regs_ok_junk vals4 r5 [exW_canary SEGS 1410112 m5] 174%nat ltac:(vm_cast_no_check (eq_refl 174%nat))) CS4) as HRn5.
  clear HRa4.
  assert (HKa5 : know_ok SEGS (ex_envL vals4 r5 [exW_canary SEGS 1410112 m5]) m5 _) by (exact (know_ok_agree SEGS 174%nat E4 _ m5 _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk4)).
  rewrite (fr_denot_agree 174%nat E4 (ex_envL vals4 r5 [exW_canary SEGS 1410112 m5]) _ fr (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc4 HKk4 KEPT4 HC4 HWs4 PMs4 Q10_4 Q1_4 Q2_4 Q4_4 PM4 HW4 PMc4 CS4 SUB4 RM4 RT4 LEQ4 OFF4 LDEL4 Ldat_a4 Lsel_a4 Drow0_4 Drow1_4 Drow2_4 Drow3_4.
  subst M4. clear log4. clear E4. try clear Rc4. clear KN4.
  lazymatch type of HRn5 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn5 end.
  pose proof (W_sok_win C A5 m5 _ (s - 1104) (Z.to_nat 1104) CK HW5 GLO1 GLO2) as SOK5.
  pose proof (exW_canary_ok SEGS 1410112 m5 (canary_any m5)) as CANOK5.
  pose (vals5 := vals4 ++ map (getr r5) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m5]).
  pose proof (exW_kn_fixed SEGS C A5 m5 _ (ex_envL vals4 r5 [exW_canary SEGS 1410112 m5]) (EVar 206) (EVar 32) (exW_canary SEGS 1410112 m5) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW5 eq_refl (proj1 CANOK5) (proj2 CANOK5) eq_refl eq_refl eq_refl SOK5 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf5.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf5 HKa5)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn5 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN5 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf5 HKa5 SOK5 CANOK5.
  repeat match goal with H : getr r5 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc5 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E5 := EEx) in HR, Hlf, HK, Hms |- *; set (log5 := LLx) in Hms, Hlf; set (M5 := mem_denot E5 m5 log5) in Hms end.
  assert (WP5 : W C A5 M5 (with_vmmaps vm5 md) /\ POSTM C A5 s m5 M5).
  { subst M5. apply (exW_win C A5 A5 m5 _ E5 log5 (EVar 32) s 1104 CK HW5 (sub_live_refl A5) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi]. }
  destruct WP5 as [HWs5 PMs5].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log5 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC5 : carry log5 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc5 : know_ok SEGS E5 M5 kn1) by (apply (carry_after SEGS E5 m5 log5 kn0 [] kn1 scs hs HC5 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact Hms |].
  pose (BS5 := [(32%nat, s); (35%nat, psel); (36%nat, sel); (37%nat, dat); (38%nat, row0); (39%nat, row1); (40%nat, row2); (41%nat, row3)]).
  exW_regfactB BS5 HR ex_r10 Q10_5. exW_regfactB BS5 HR ex_r1 Q1_5. exW_regfactB BS5 HR ex_r2 Q2_5. exW_regfactB BS5 HR ex_r4 Q4_5.
  clear BS5.
  lazymatch type of Q2_5 with _ = Z_to_bv 64 (s + ?off) => pose (OFF5 := off) end.
  lazymatch type of Q1_5 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_5 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A5 M5 _ Rc5 (Z_to_bv 64 sel) (Z_to_bv 64 ret) 32 sp' S CK HWs5 Q10_5 Lsel_a5 F0sel Q1_5
             ltac:(red; apply bv_eq; reflexivity) Q4_5 Q2_5 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A6 m6 vm6 r6 HW6 CS5 Dsel_6 LEQ5 PMc5 RM5.
  rewrite with_vmmaps_twice in HW6 |- *. rewrite with_vmmaps_vmmaps in RM5.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT5 RM5 ltac:(lia) ltac:(lia)) as RT6. cbn [Z.add] in RT6.
  assert (Drow0_6 : live A6 (Z_to_bv 64 row0) = None) by (rewrite (LEQ5 _ (not_eq_sym NE_sel_row0)); exact Drow0_5).
  assert (Drow1_6 : live A6 (Z_to_bv 64 row1) = None) by (rewrite (LEQ5 _ (not_eq_sym NE_sel_row1)); exact Drow1_5).
  assert (Drow2_6 : live A6 (Z_to_bv 64 row2) = None) by (rewrite (LEQ5 _ (not_eq_sym NE_sel_row2)); exact Drow2_5).
  assert (Drow3_6 : live A6 (Z_to_bv 64 row3) = None) by (rewrite (LEQ5 _ (not_eq_sym NE_sel_row3)); exact Drow3_5).
  assert (Ddat_6 : live A6 (Z_to_bv 64 dat) = None) by (rewrite (LEQ5 _ (not_eq_sym NE_sel_dat)); exact Ddat_5).
  assert (SUB5 : sub_live A6 A5).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 sel) by (intros ->; rewrite Dsel_6 in Lq; discriminate Lq). rewrite <- (LEQ5 q NEq). exact Lq. }
  assert (PM6 : POSTM C A6 s m0 m6).
  { apply (POSTM_trans C A6 s m0 M5 m6); [apply (POSTM_sub C A6 A5 _ _ _ SUB5); exact (POSTM_trans _ _ _ _ _ _ PM5 PMs5)|].
    apply (POSTM_mono C A6 (s + OFF5) s); [unfold OFF5; lia | exact PMc5]. }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 sel :: [Z_to_bv 64 dat; Z_to_bv 64 row3; Z_to_bv 64 row2; Z_to_bv 64 row1; Z_to_bv 64 row0])) => eq_trans (LEQ5 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL5 q (fun XX => Hq (or_intror XX)))) as LDEL6.
  assert (KEPT5 : Forall (ex_region_kept E5 M5 m6) [(EVar 32, OFF5, 0%Z); (EVar 35, 0%Z, 8%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF5 1104 M5 m6 E5 (EVar 32) CK (proj1 PMc5) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (sd_kept_cell C (s + OFF5) psel M5 m6 E5 (EVar 35) CK (proj1 PMc5) ltac:(unfold OFF5; lia) ltac:(unfold OFF5; lia) RP eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E5 M5 m6 _ [] _ HKc5 KEPT5) as HKk5.
  match type of HKk5 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E5 m6 kk') in HKk5 end.
  pose proof (regs_ok_agree 207%nat E5 (ex_envL vals5 r6 [exW_canary SEGS 1410112 m6]) _ _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa5.
  pose proof (exW_regs_call _ _ _ _ _ HRa5 (ex_regs_ok_junk vals5 r6 [exW_canary SEGS 1410112 m6] 207%nat ltac:(vm_cast_no_check (eq_refl 207%nat))) CS5) as HRn6.
  clear HRa5.
  assert (HKa6 : know_ok SEGS (ex_envL vals5 r6 [exW_canary SEGS 1410112 m6]) m6 _) by (exact (know_ok_agree SEGS 207%nat E5 _ m6 _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk5)).
  rewrite (fr_denot_agree 207%nat E5 (ex_envL vals5 r6 [exW_canary SEGS 1410112 m6]) _ fr (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc5 HKk5 KEPT5 HC5 HWs5 PMs5 Q10_5 Q1_5 Q2_5 Q4_5 PM5 HW5 PMc5 CS5 SUB5 RM5 RT5 LEQ5 OFF5 LDEL5 Lsel_a5 Drow0_5 Drow1_5 Drow2_5 Drow3_5 Ddat_5.
  subst M5. clear log5. clear E5. try clear Rc5. clear KN5.
  lazymatch type of HRn6 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn6 end.
  pose proof (W_sok_win C A6 m6 _ (s - 1104) (Z.to_nat 1104) CK HW6 GLO1 GLO2) as SOK6.
  pose proof (exW_canary_ok SEGS 1410112 m6 (canary_any m6)) as CANOK6.
  pose (vals6 := vals5 ++ map (getr r6) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m6]).
  pose proof (exW_kn_fixed SEGS C A6 m6 _ (ex_envL vals5 r6 [exW_canary SEGS 1410112 m6]) (EVar 239) (EVar 32) (exW_canary SEGS 1410112 m6) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW6 eq_refl (proj1 CANOK6) (proj2 CANOK6) eq_refl eq_refl eq_refl SOK6 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf6.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf6 HKa6)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn6 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN6 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf6 HKa6 SOK6 CANOK6.
  repeat match goal with H : getr r6 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E6 := EEx) in HR, Hlf, HK, Hms |- *; set (log6 := LLx) in Hms, Hlf; set (M6 := mem_denot E6 m6 log6) in Hms end.
  assert (WP6 : W C A6 M6 (with_vmmaps vm6 md) /\ POSTM C A6 (psel + 8) m6 M6 /\ (forall a : word, (s <= u a < psel)%Z -> M6 a = m6 a)).
  { subst M6. apply (sd_win_cell C A6 A6 m6 _ E6 log6 (EVar 32) (EVar 35) s 1104 psel CK HW6 (sub_live_refl A6) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | reflexivity | lia | exact GLO1 | exact Hsp | exact Hph]. }
  destruct WP6 as (HWs6 & PMs6 & BET6).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact Hms |].
  pose (BSF := [(32%nat, s); (35%nat, psel)]).
  exW_cellB HK Hlf r0 BSF (EVar 35) psel 0%Z 8%nat Cpsel.
  refine (HC A6 M6 vm6 RcF HWs6 _ Dsel_6 Ddat_6 Drow0_6 Drow1_6 Drow2_6 Drow3_6
            ltac:(intros q Hq; apply LDEL6; intros Hin; apply Hq; cbn [In] in Hin |- *; tauto)
            (POSTM_trans _ _ _ _ _ _ (POSTM_mono C A6 s (psel + 8) m0 m6 ltac:(lia) PM6) PMs6) Cpsel
            (fun a Ha => eq_trans (BET6 a Ha) (sd_frm_above C s m0 m6 a CK (proj1 PM6) ltac:(lia) ltac:(lia))) RT6).
  lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 RcF [(2%nat, EVar 32); (4%nat, ELit 1278416)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor; [symmetry; exact HTP | constructor]] | vm_compute; reflexivity] end.
Qed.

(* [comment removed for export] *)
Lemma seld_chain5 : forall (fx : FPState) C A m md regs (s psel sel dat row0 row1 row2 row3 row4 n0 n1 n2 n3 n4 : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + O23LeptSelDC.SELD_WIN <= s)%Z -> (s <= psel)%Z -> (psel + 8 <= c_top C)%Z -> (psel mod 8 = 0)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 1278416 -> getr regs 10 = Z_to_bv 64 psel ->
  rdn SEGS m (Z_to_bv 64 (psel + 0)) 8 = Some (Z_to_le_bytes 8 sel) ->
  rdn SEGS m (Z_to_bv 64 (sel + 0)) 4 = Some (Z_to_le_bytes 4 5) ->
  rdn SEGS m (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 dat) ->
  rdn SEGS m (Z_to_bv 64 (sel + 24)) 8 = Some (Z_to_le_bytes 8 0) ->
  rdn SEGS m (Z_to_bv 64 (dat + 0)) 8 = Some (Z_to_le_bytes 8 row0) ->
  rdn SEGS m (Z_to_bv 64 (dat + 8)) 8 = Some (Z_to_le_bytes 8 row1) ->
  rdn SEGS m (Z_to_bv 64 (dat + 16)) 8 = Some (Z_to_le_bytes 8 row2) ->
  rdn SEGS m (Z_to_bv 64 (dat + 24)) 8 = Some (Z_to_le_bytes 8 row3) ->
  rdn SEGS m (Z_to_bv 64 (dat + 32)) 8 = Some (Z_to_le_bytes 8 row4) ->
  live A (Z_to_bv 64 sel) = Some 32%Z -> live (c_A0 C) (Z_to_bv 64 sel) = None -> (0 <= sel < 2 ^ 64)%Z ->
  live A (Z_to_bv 64 dat) = Some 40%Z -> live (c_A0 C) (Z_to_bv 64 dat) = None -> (0 <= dat < 2 ^ 64)%Z ->
  live A (Z_to_bv 64 row0) = Some n0%Z -> live (c_A0 C) (Z_to_bv 64 row0) = None -> (0 <= row0 < 2 ^ 64)%Z ->
  live A (Z_to_bv 64 row1) = Some n1%Z -> live (c_A0 C) (Z_to_bv 64 row1) = None -> (0 <= row1 < 2 ^ 64)%Z ->
  live A (Z_to_bv 64 row2) = Some n2%Z -> live (c_A0 C) (Z_to_bv 64 row2) = None -> (0 <= row2 < 2 ^ 64)%Z ->
  live A (Z_to_bv 64 row3) = Some n3%Z -> live (c_A0 C) (Z_to_bv 64 row3) = None -> (0 <= row3 < 2 ^ 64)%Z ->
  live A (Z_to_bv 64 row4) = Some n4%Z -> live (c_A0 C) (Z_to_bv 64 row4) = None -> (0 <= row4 < 2 ^ 64)%Z ->
  Z_to_bv 64 sel <> Z_to_bv 64 dat ->
  Z_to_bv 64 sel <> Z_to_bv 64 row0 ->
  Z_to_bv 64 dat <> Z_to_bv 64 row0 ->
  Z_to_bv 64 sel <> Z_to_bv 64 row1 ->
  Z_to_bv 64 dat <> Z_to_bv 64 row1 ->
  Z_to_bv 64 row0 <> Z_to_bv 64 row1 ->
  Z_to_bv 64 sel <> Z_to_bv 64 row2 ->
  Z_to_bv 64 dat <> Z_to_bv 64 row2 ->
  Z_to_bv 64 row0 <> Z_to_bv 64 row2 ->
  Z_to_bv 64 row1 <> Z_to_bv 64 row2 ->
  Z_to_bv 64 sel <> Z_to_bv 64 row3 ->
  Z_to_bv 64 dat <> Z_to_bv 64 row3 ->
  Z_to_bv 64 row0 <> Z_to_bv 64 row3 ->
  Z_to_bv 64 row1 <> Z_to_bv 64 row3 ->
  Z_to_bv 64 row2 <> Z_to_bv 64 row3 ->
  Z_to_bv 64 sel <> Z_to_bv 64 row4 ->
  Z_to_bv 64 dat <> Z_to_bv 64 row4 ->
  Z_to_bv 64 row0 <> Z_to_bv 64 row4 ->
  Z_to_bv 64 row1 <> Z_to_bv 64 row4 ->
  Z_to_bv 64 row2 <> Z_to_bv 64 row4 ->
  Z_to_bv 64 row3 <> Z_to_bv 64 row4 ->
  (forall A' m' vm' regs',
     W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     live A' (Z_to_bv 64 sel) = None ->
     live A' (Z_to_bv 64 dat) = None ->
     live A' (Z_to_bv 64 row0) = None ->
     live A' (Z_to_bv 64 row1) = None ->
     live A' (Z_to_bv 64 row2) = None ->
     live A' (Z_to_bv 64 row3) = None ->
     live A' (Z_to_bv 64 row4) = None ->
     (forall q : word, ~ In q [Z_to_bv 64 sel; Z_to_bv 64 dat; Z_to_bv 64 row0; Z_to_bv 64 row1; Z_to_bv 64 row2; Z_to_bv 64 row3; Z_to_bv 64 row4] -> live A' q = live A q) ->
     POSTM C A' (psel + 8) m m' -> rdn SEGS m' (Z_to_bv 64 (psel + 0)) 8 = Some (Z_to_le_bytes 8 0) ->
     (forall a : word, (s <= u a < psel)%Z -> m' a = m a) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 674932) m al_rom) md) S.
Proof using P16 PINS.
  intros fx C A0 m0 md r0 s psel sel dat row0 row1 row2 row3 row4 n0 n1 n2 n3 n4 ret S CK HW0 H2 Hs16 Hlo Hsp Hph Hpal H1 Hret H4 H10 Mpsel Msy Mdat Mnm Mrow0 Mrow1 Mrow2 Mrow3 Mrow4
    Lsel_a0 F0sel RRsel Ldat_a0 F0dat RRdat Lrow0_a0 F0row0 RRrow0 Lrow1_a0 F0row1 RRrow1 Lrow2_a0 F0row2 RRrow2 Lrow3_a0 F0row3 RRrow3 Lrow4_a0 F0row4 RRrow4
    NE_sel_dat NE_sel_row0 NE_dat_row0 NE_sel_row1 NE_dat_row1 NE_row0_row1 NE_sel_row2 NE_dat_row2 NE_row0_row2 NE_row1_row2 NE_sel_row3 NE_dat_row3 NE_row0_row3 NE_row1_row3 NE_row2_row3 NE_sel_row4 NE_dat_row4 NE_row0_row4 NE_row1_row4 NE_row2_row4 NE_row3_row4 HC.
  unfold O23LeptSelDC.SELD_WIN in *.
  assert (Hhi : (s <= c_top C)%Z) by lia.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  assert (HTP : ex_keep (getr r0 ex_r4 = Z_to_bv 64 1278416)) by exact H4.
  destruct fx as [fr cs]. pose proof I as FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  assert (GLO1 : (c_top C - LSTK <= s - 1104)%Z) by lia.
  assert (GLO2 : (s - 1104 + Z.of_nat (Z.to_nat 1104) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (1104 <= s)%Z) by lia.
  assert (RP : (0 <= psel < 2 ^ 64)%Z) by lia.
  destruct (exW_blk_rng C A0 m0 _ sel 32 CK HW0 Lsel_a0 RRsel ltac:(lia)) as (GLsel & _ & GHsel).
  pose proof (ai_live_hull A0 m0 (m_vmmaps md) _ _ (w_inv _ _ _ _ HW0) Lsel_a0) as (_ & ALsel & _). rewrite u_Z2bv in ALsel by lia.
  pose proof (exW_win_blk_apart_h C A0 m0 _ s 1104 sel 32 CK HW0 Lsel_a0 eq_refl RRsel GLO1) as WAPsel.
  destruct (exW_blk_rng C A0 m0 _ dat 40 CK HW0 Ldat_a0 RRdat ltac:(lia)) as (GLdat & _ & GHdat).
  pose proof (ai_live_hull A0 m0 (m_vmmaps md) _ _ (w_inv _ _ _ _ HW0) Ldat_a0) as (_ & ALdat & _). rewrite u_Z2bv in ALdat by lia.
  pose proof (exW_win_blk_apart_h C A0 m0 _ s 1104 dat 40 CK HW0 Ldat_a0 eq_refl RRdat GLO1) as WAPdat.
  pose proof (W_sok_win C A0 m0 _ psel 8 CK HW0 ltac:(lia) ltac:(cbn; lia)) as SOKP.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose proof (POSTM_refl C A0 s m0) as PM0.
  pose proof (roomtr_refl A0 vm0 0 0 ltac:(lia) ltac:(lia)) as RT0.
  pose (valsI := @nil word).
  pose proof (fun (q : word) (_ : ~ In q []) => eq_refl (live A0 q)) as LDEL0.
  pose proof (W_sok_win C A0 m0 _ (s - 1104) (Z.to_nat 1104) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 1410112 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0; psel; sel; dat; row0; row1; row2; row3; row4]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0; psel; sel; dat; row0; row1; row2; row3; row4]) (EVar 34) (EVar 32) (exW_canary SEGS 1410112 m0) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0; psel; sel; dat; row0; row1; row2; row3; row4]) m0 [KRange (EVar 32) 1422416 (2 ^ 63); KAlign (EVar 32) 16; KRange (EVar 35) 1422416 (2 ^ 63); KAlign (EVar 35) 8; KWr (SA (EVar 35) 0) 8; KWord (SA (EVar 35) 0) 8 (EVar 36); KDisj (SA (EVar 32) (- 1104)) 1104 (SA (EVar 35) 0) 8; KRange (EVar 36) 4096 (2 ^ 47); KAlign (EVar 36) 16; KDisj (SA (EVar 32) (- 1104)) 1104 (SA (EVar 36) 0) 32; KWord (SA (EVar 36) 0) 4 (ELit 5); KWord (SA (EVar 36) 16) 8 (EVar 37); KWord (SA (EVar 36) 24) 8 (ELit 0); KRange (EVar 37) 4096 (2 ^ 47); KAlign (EVar 37) 16; KDisj (SA (EVar 32) (- 1104)) 1104 (SA (EVar 37) 0) 40; KWord (SA (EVar 37) 0) 8 (EVar 38); KWord (SA (EVar 37) 8) 8 (EVar 39); KWord (SA (EVar 37) 16) 8 (EVar 40); KWord (SA (EVar 37) 24) 8 (EVar 41); KWord (SA (EVar 37) 32) 8 (EVar 42)]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 HKf0)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0; psel; sel; dat; row0; row1; row2; row3; row4] HR.
  pose proof (ex_regs_ok_reexpr _ _ r0 ex_r10 (EVar 35) HR ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact H10)) as HRx. clear HR. rename HRx into HR.
  lazymatch type of HR with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HR end.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win C A0 A0 m0 _ E0 log0 (EVar 32) s 1104 CK HW0 (sub_live_refl A0) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi]. }
  destruct WP0 as [HWs0 PMs0].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (35%nat, psel); (36%nat, sel); (37%nat, dat); (38%nat, row0); (39%nat, row1); (40%nat, row2); (41%nat, row3); (42%nat, row4)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r1 Q1_0. exW_regfactB BS0 HR ex_r2 Q2_0. exW_regfactB BS0 HR ex_r4 Q4_0.
  clear BS0.
  lazymatch type of Q2_0 with _ = Z_to_bv 64 (s + ?off) => pose (OFF0 := off) end.
  lazymatch type of Q1_0 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_0 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A0 M0 _ Rc0 (Z_to_bv 64 row0) (Z_to_bv 64 ret) n0 sp' S CK HWs0 Q10_0 Lrow0_a0 F0row0 Q1_0
             ltac:(red; apply bv_eq; reflexivity) Q4_0 Q2_0 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A1 m1 vm1 r1 HW1 CS0 Drow0_1 LEQ0 PMc0 RM0.
  rewrite with_vmmaps_twice in HW1 |- *. rewrite with_vmmaps_vmmaps in RM0.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT0 RM0 ltac:(lia) ltac:(lia)) as RT1. cbn [Z.add] in RT1.
  assert (Lrow1_a1 : live A1 (Z_to_bv 64 row1) = Some n1%Z) by (rewrite (LEQ0 _ (not_eq_sym NE_row0_row1)); exact Lrow1_a0).
  assert (Lrow2_a1 : live A1 (Z_to_bv 64 row2) = Some n2%Z) by (rewrite (LEQ0 _ (not_eq_sym NE_row0_row2)); exact Lrow2_a0).
  assert (Lrow3_a1 : live A1 (Z_to_bv 64 row3) = Some n3%Z) by (rewrite (LEQ0 _ (not_eq_sym NE_row0_row3)); exact Lrow3_a0).
  assert (Lrow4_a1 : live A1 (Z_to_bv 64 row4) = Some n4%Z) by (rewrite (LEQ0 _ (not_eq_sym NE_row0_row4)); exact Lrow4_a0).
  assert (Ldat_a1 : live A1 (Z_to_bv 64 dat) = Some 40%Z) by (rewrite (LEQ0 _ NE_dat_row0); exact Ldat_a0).
  assert (Lsel_a1 : live A1 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ0 _ NE_sel_row0); exact Lsel_a0).
  assert (SUB0 : sub_live A1 A0).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row0) by (intros ->; rewrite Drow0_1 in Lq; discriminate Lq). rewrite <- (LEQ0 q NEq). exact Lq. }
  assert (PM1 : POSTM C A1 s m0 m1).
  { apply (POSTM_trans C A1 s m0 M0 m1); [apply (POSTM_sub C A1 A0 _ _ _ SUB0); exact (POSTM_trans _ _ _ _ _ _ PM0 PMs0)|].
    apply (POSTM_mono C A1 (s + OFF0) s); [unfold OFF0; lia | exact PMc0]. }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row0 :: [])) => eq_trans (LEQ0 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL0 q (fun XX => Hq (or_intror XX)))) as LDEL1.
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, OFF0, 0%Z); (EVar 35, 0%Z, 8%Z); (EVar 36, 0%Z, 32%Z); (EVar 37, 0%Z, 40%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF0 1104 M0 m1 E0 (EVar 32) CK (proj1 PMc0) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (sd_kept_cell C (s + OFF0) psel M0 m1 E0 (EVar 35) CK (proj1 PMc0) ltac:(unfold OFF0; lia) ltac:(unfold OFF0; lia) RP eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A1 A0 M0 _ M0 m1 E0 (EVar 36) sel 32 CK HWs0 Lsel_a0 RRsel eq_refl (proj2 PMc0) Lsel_a1 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A1 A0 M0 _ M0 m1 E0 (EVar 37) dat 40 CK HWs0 Ldat_a0 RRdat eq_refl (proj2 PMc0) Ldat_a1 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E0 m1 kk') in HKk0 end.
  pose proof (regs_ok_agree 43%nat E0 (ex_envL vals0 r1 [exW_canary SEGS 1410112 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [exW_canary SEGS 1410112 m1] 43%nat ltac:(vm_cast_no_check (eq_refl 43%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [exW_canary SEGS 1410112 m1]) m1 _) by (exact (know_ok_agree SEGS 43%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  rewrite (fr_denot_agree 43%nat E0 (ex_envL vals0 r1 [exW_canary SEGS 1410112 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q1_0 Q2_0 Q4_0 PM0 HW0 PMc0 CS0 SUB0 RM0 RT0 LEQ0 OFF0 LDEL0 Lrow0_a0 Lrow1_a0 Lrow2_a0 Lrow3_a0 Lrow4_a0 Ldat_a0 Lsel_a0.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  pose proof (W_sok_win C A1 m1 _ (s - 1104) (Z.to_nat 1104) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 1410112 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m1]).
  pose proof (exW_kn_fixed SEGS C A1 m1 _ (ex_envL vals0 r1 [exW_canary SEGS 1410112 m1]) (EVar 75) (EVar 32) (exW_canary SEGS 1410112 m1) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc1 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A1 M1 (with_vmmaps vm1 md) /\ POSTM C A1 s m1 M1).
  { subst M1. apply (exW_win C A1 A1 m1 _ E1 log1 (EVar 32) s 1104 CK HW1 (sub_live_refl A1) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi]. }
  destruct WP1 as [HWs1 PMs1].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log1 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC1 : carry log1 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc1 : know_ok SEGS E1 M1 kn1) by (apply (carry_after SEGS E1 m1 log1 kn0 [] kn1 scs hs HC1 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose (BS1 := [(32%nat, s); (35%nat, psel); (36%nat, sel); (37%nat, dat); (38%nat, row0); (39%nat, row1); (40%nat, row2); (41%nat, row3); (42%nat, row4)]).
  exW_regfactB BS1 HR ex_r10 Q10_1. exW_regfactB BS1 HR ex_r1 Q1_1. exW_regfactB BS1 HR ex_r2 Q2_1. exW_regfactB BS1 HR ex_r4 Q4_1.
  clear BS1.
  lazymatch type of Q2_1 with _ = Z_to_bv 64 (s + ?off) => pose (OFF1 := off) end.
  lazymatch type of Q1_1 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_1 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A1 M1 _ Rc1 (Z_to_bv 64 row1) (Z_to_bv 64 ret) n1 sp' S CK HWs1 Q10_1 Lrow1_a1 F0row1 Q1_1
             ltac:(red; apply bv_eq; reflexivity) Q4_1 Q2_1 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A2 m2 vm2 r2 HW2 CS1 Drow1_2 LEQ1 PMc1 RM1.
  rewrite with_vmmaps_twice in HW2 |- *. rewrite with_vmmaps_vmmaps in RM1.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT1 RM1 ltac:(lia) ltac:(lia)) as RT2. cbn [Z.add] in RT2.
  assert (Lrow2_a2 : live A2 (Z_to_bv 64 row2) = Some n2%Z) by (rewrite (LEQ1 _ (not_eq_sym NE_row1_row2)); exact Lrow2_a1).
  assert (Lrow3_a2 : live A2 (Z_to_bv 64 row3) = Some n3%Z) by (rewrite (LEQ1 _ (not_eq_sym NE_row1_row3)); exact Lrow3_a1).
  assert (Lrow4_a2 : live A2 (Z_to_bv 64 row4) = Some n4%Z) by (rewrite (LEQ1 _ (not_eq_sym NE_row1_row4)); exact Lrow4_a1).
  assert (Ldat_a2 : live A2 (Z_to_bv 64 dat) = Some 40%Z) by (rewrite (LEQ1 _ NE_dat_row1); exact Ldat_a1).
  assert (Lsel_a2 : live A2 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ1 _ NE_sel_row1); exact Lsel_a1).
  assert (Drow0_2 : live A2 (Z_to_bv 64 row0) = None) by (rewrite (LEQ1 _ NE_row0_row1); exact Drow0_1).
  assert (SUB1 : sub_live A2 A1).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row1) by (intros ->; rewrite Drow1_2 in Lq; discriminate Lq). rewrite <- (LEQ1 q NEq). exact Lq. }
  assert (PM2 : POSTM C A2 s m0 m2).
  { apply (POSTM_trans C A2 s m0 M1 m2); [apply (POSTM_sub C A2 A1 _ _ _ SUB1); exact (POSTM_trans _ _ _ _ _ _ PM1 PMs1)|].
    apply (POSTM_mono C A2 (s + OFF1) s); [unfold OFF1; lia | exact PMc1]. }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row1 :: [Z_to_bv 64 row0])) => eq_trans (LEQ1 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL1 q (fun XX => Hq (or_intror XX)))) as LDEL2.
  assert (KEPT1 : Forall (ex_region_kept E1 M1 m2) [(EVar 32, OFF1, 0%Z); (EVar 35, 0%Z, 8%Z); (EVar 36, 0%Z, 32%Z); (EVar 37, 0%Z, 40%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF1 1104 M1 m2 E1 (EVar 32) CK (proj1 PMc1) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (sd_kept_cell C (s + OFF1) psel M1 m2 E1 (EVar 35) CK (proj1 PMc1) ltac:(unfold OFF1; lia) ltac:(unfold OFF1; lia) RP eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A2 A1 M1 _ M1 m2 E1 (EVar 36) sel 32 CK HWs1 Lsel_a1 RRsel eq_refl (proj2 PMc1) Lsel_a2 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A2 A1 M1 _ M1 m2 E1 (EVar 37) dat 40 CK HWs1 Ldat_a1 RRdat eq_refl (proj2 PMc1) Ldat_a2 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E1 M1 m2 _ [] _ HKc1 KEPT1) as HKk1.
  match type of HKk1 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E1 m2 kk') in HKk1 end.
  pose proof (regs_ok_agree 76%nat E1 (ex_envL vals1 r2 [exW_canary SEGS 1410112 m2]) _ _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa1.
  pose proof (exW_regs_call _ _ _ _ _ HRa1 (ex_regs_ok_junk vals1 r2 [exW_canary SEGS 1410112 m2] 76%nat ltac:(vm_cast_no_check (eq_refl 76%nat))) CS1) as HRn2.
  clear HRa1.
  assert (HKa2 : know_ok SEGS (ex_envL vals1 r2 [exW_canary SEGS 1410112 m2]) m2 _) by (exact (know_ok_agree SEGS 76%nat E1 _ m2 _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk1)).
  rewrite (fr_denot_agree 76%nat E1 (ex_envL vals1 r2 [exW_canary SEGS 1410112 m2]) _ fr (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc1 HKk1 KEPT1 HC1 HWs1 PMs1 Q10_1 Q1_1 Q2_1 Q4_1 PM1 HW1 PMc1 CS1 SUB1 RM1 RT1 LEQ1 OFF1 LDEL1 Lrow1_a1 Lrow2_a1 Lrow3_a1 Lrow4_a1 Ldat_a1 Lsel_a1 Drow0_1.
  subst M1. clear log1. clear E1. try clear Rc1. clear KN1.
  lazymatch type of HRn2 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn2 end.
  pose proof (W_sok_win C A2 m2 _ (s - 1104) (Z.to_nat 1104) CK HW2 GLO1 GLO2) as SOK2.
  pose proof (exW_canary_ok SEGS 1410112 m2 (canary_any m2)) as CANOK2.
  pose (vals2 := vals1 ++ map (getr r2) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m2]).
  pose proof (exW_kn_fixed SEGS C A2 m2 _ (ex_envL vals1 r2 [exW_canary SEGS 1410112 m2]) (EVar 108) (EVar 32) (exW_canary SEGS 1410112 m2) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW2 eq_refl (proj1 CANOK2) (proj2 CANOK2) eq_refl eq_refl eq_refl SOK2 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf2.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf2 HKa2)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn2 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN2 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf2 HKa2 SOK2 CANOK2.
  repeat match goal with H : getr r2 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc2 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E2 := EEx) in HR, Hlf, HK, Hms |- *; set (log2 := LLx) in Hms, Hlf; set (M2 := mem_denot E2 m2 log2) in Hms end.
  assert (WP2 : W C A2 M2 (with_vmmaps vm2 md) /\ POSTM C A2 s m2 M2).
  { subst M2. apply (exW_win C A2 A2 m2 _ E2 log2 (EVar 32) s 1104 CK HW2 (sub_live_refl A2) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi]. }
  destruct WP2 as [HWs2 PMs2].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log2 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC2 : carry log2 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc2 : know_ok SEGS E2 M2 kn1) by (apply (carry_after SEGS E2 m2 log2 kn0 [] kn1 scs hs HC2 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact Hms |].
  pose (BS2 := [(32%nat, s); (35%nat, psel); (36%nat, sel); (37%nat, dat); (38%nat, row0); (39%nat, row1); (40%nat, row2); (41%nat, row3); (42%nat, row4)]).
  exW_regfactB BS2 HR ex_r10 Q10_2. exW_regfactB BS2 HR ex_r1 Q1_2. exW_regfactB BS2 HR ex_r2 Q2_2. exW_regfactB BS2 HR ex_r4 Q4_2.
  clear BS2.
  lazymatch type of Q2_2 with _ = Z_to_bv 64 (s + ?off) => pose (OFF2 := off) end.
  lazymatch type of Q1_2 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_2 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A2 M2 _ Rc2 (Z_to_bv 64 row2) (Z_to_bv 64 ret) n2 sp' S CK HWs2 Q10_2 Lrow2_a2 F0row2 Q1_2
             ltac:(red; apply bv_eq; reflexivity) Q4_2 Q2_2 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A3 m3 vm3 r3 HW3 CS2 Drow2_3 LEQ2 PMc2 RM2.
  rewrite with_vmmaps_twice in HW3 |- *. rewrite with_vmmaps_vmmaps in RM2.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT2 RM2 ltac:(lia) ltac:(lia)) as RT3. cbn [Z.add] in RT3.
  assert (Lrow3_a3 : live A3 (Z_to_bv 64 row3) = Some n3%Z) by (rewrite (LEQ2 _ (not_eq_sym NE_row2_row3)); exact Lrow3_a2).
  assert (Lrow4_a3 : live A3 (Z_to_bv 64 row4) = Some n4%Z) by (rewrite (LEQ2 _ (not_eq_sym NE_row2_row4)); exact Lrow4_a2).
  assert (Ldat_a3 : live A3 (Z_to_bv 64 dat) = Some 40%Z) by (rewrite (LEQ2 _ NE_dat_row2); exact Ldat_a2).
  assert (Lsel_a3 : live A3 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ2 _ NE_sel_row2); exact Lsel_a2).
  assert (Drow0_3 : live A3 (Z_to_bv 64 row0) = None) by (rewrite (LEQ2 _ NE_row0_row2); exact Drow0_2).
  assert (Drow1_3 : live A3 (Z_to_bv 64 row1) = None) by (rewrite (LEQ2 _ NE_row1_row2); exact Drow1_2).
  assert (SUB2 : sub_live A3 A2).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row2) by (intros ->; rewrite Drow2_3 in Lq; discriminate Lq). rewrite <- (LEQ2 q NEq). exact Lq. }
  assert (PM3 : POSTM C A3 s m0 m3).
  { apply (POSTM_trans C A3 s m0 M2 m3); [apply (POSTM_sub C A3 A2 _ _ _ SUB2); exact (POSTM_trans _ _ _ _ _ _ PM2 PMs2)|].
    apply (POSTM_mono C A3 (s + OFF2) s); [unfold OFF2; lia | exact PMc2]. }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row2 :: [Z_to_bv 64 row1; Z_to_bv 64 row0])) => eq_trans (LEQ2 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL2 q (fun XX => Hq (or_intror XX)))) as LDEL3.
  assert (KEPT2 : Forall (ex_region_kept E2 M2 m3) [(EVar 32, OFF2, 0%Z); (EVar 35, 0%Z, 8%Z); (EVar 36, 0%Z, 32%Z); (EVar 37, 0%Z, 40%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF2 1104 M2 m3 E2 (EVar 32) CK (proj1 PMc2) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (sd_kept_cell C (s + OFF2) psel M2 m3 E2 (EVar 35) CK (proj1 PMc2) ltac:(unfold OFF2; lia) ltac:(unfold OFF2; lia) RP eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A3 A2 M2 _ M2 m3 E2 (EVar 36) sel 32 CK HWs2 Lsel_a2 RRsel eq_refl (proj2 PMc2) Lsel_a3 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A3 A2 M2 _ M2 m3 E2 (EVar 37) dat 40 CK HWs2 Ldat_a2 RRdat eq_refl (proj2 PMc2) Ldat_a3 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E2 M2 m3 _ [] _ HKc2 KEPT2) as HKk2.
  match type of HKk2 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E2 m3 kk') in HKk2 end.
  pose proof (regs_ok_agree 109%nat E2 (ex_envL vals2 r3 [exW_canary SEGS 1410112 m3]) _ _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa2.
  pose proof (exW_regs_call _ _ _ _ _ HRa2 (ex_regs_ok_junk vals2 r3 [exW_canary SEGS 1410112 m3] 109%nat ltac:(vm_cast_no_check (eq_refl 109%nat))) CS2) as HRn3.
  clear HRa2.
  assert (HKa3 : know_ok SEGS (ex_envL vals2 r3 [exW_canary SEGS 1410112 m3]) m3 _) by (exact (know_ok_agree SEGS 109%nat E2 _ m3 _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk2)).
  rewrite (fr_denot_agree 109%nat E2 (ex_envL vals2 r3 [exW_canary SEGS 1410112 m3]) _ fr (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc2 HKk2 KEPT2 HC2 HWs2 PMs2 Q10_2 Q1_2 Q2_2 Q4_2 PM2 HW2 PMc2 CS2 SUB2 RM2 RT2 LEQ2 OFF2 LDEL2 Lrow2_a2 Lrow3_a2 Lrow4_a2 Ldat_a2 Lsel_a2 Drow0_2 Drow1_2.
  subst M2. clear log2. clear E2. try clear Rc2. clear KN2.
  lazymatch type of HRn3 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn3 end.
  pose proof (W_sok_win C A3 m3 _ (s - 1104) (Z.to_nat 1104) CK HW3 GLO1 GLO2) as SOK3.
  pose proof (exW_canary_ok SEGS 1410112 m3 (canary_any m3)) as CANOK3.
  pose (vals3 := vals2 ++ map (getr r3) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m3]).
  pose proof (exW_kn_fixed SEGS C A3 m3 _ (ex_envL vals2 r3 [exW_canary SEGS 1410112 m3]) (EVar 141) (EVar 32) (exW_canary SEGS 1410112 m3) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW3 eq_refl (proj1 CANOK3) (proj2 CANOK3) eq_refl eq_refl eq_refl SOK3 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf3.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf3 HKa3)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn3 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN3 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf3 HKa3 SOK3 CANOK3.
  repeat match goal with H : getr r3 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc3 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E3 := EEx) in HR, Hlf, HK, Hms |- *; set (log3 := LLx) in Hms, Hlf; set (M3 := mem_denot E3 m3 log3) in Hms end.
  assert (WP3 : W C A3 M3 (with_vmmaps vm3 md) /\ POSTM C A3 s m3 M3).
  { subst M3. apply (exW_win C A3 A3 m3 _ E3 log3 (EVar 32) s 1104 CK HW3 (sub_live_refl A3) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi]. }
  destruct WP3 as [HWs3 PMs3].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log3 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC3 : carry log3 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc3 : know_ok SEGS E3 M3 kn1) by (apply (carry_after SEGS E3 m3 log3 kn0 [] kn1 scs hs HC3 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact Hms |].
  pose (BS3 := [(32%nat, s); (35%nat, psel); (36%nat, sel); (37%nat, dat); (38%nat, row0); (39%nat, row1); (40%nat, row2); (41%nat, row3); (42%nat, row4)]).
  exW_regfactB BS3 HR ex_r10 Q10_3. exW_regfactB BS3 HR ex_r1 Q1_3. exW_regfactB BS3 HR ex_r2 Q2_3. exW_regfactB BS3 HR ex_r4 Q4_3.
  clear BS3.
  lazymatch type of Q2_3 with _ = Z_to_bv 64 (s + ?off) => pose (OFF3 := off) end.
  lazymatch type of Q1_3 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_3 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A3 M3 _ Rc3 (Z_to_bv 64 row3) (Z_to_bv 64 ret) n3 sp' S CK HWs3 Q10_3 Lrow3_a3 F0row3 Q1_3
             ltac:(red; apply bv_eq; reflexivity) Q4_3 Q2_3 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A4 m4 vm4 r4 HW4 CS3 Drow3_4 LEQ3 PMc3 RM3.
  rewrite with_vmmaps_twice in HW4 |- *. rewrite with_vmmaps_vmmaps in RM3.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT3 RM3 ltac:(lia) ltac:(lia)) as RT4. cbn [Z.add] in RT4.
  assert (Lrow4_a4 : live A4 (Z_to_bv 64 row4) = Some n4%Z) by (rewrite (LEQ3 _ (not_eq_sym NE_row3_row4)); exact Lrow4_a3).
  assert (Ldat_a4 : live A4 (Z_to_bv 64 dat) = Some 40%Z) by (rewrite (LEQ3 _ NE_dat_row3); exact Ldat_a3).
  assert (Lsel_a4 : live A4 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ3 _ NE_sel_row3); exact Lsel_a3).
  assert (Drow0_4 : live A4 (Z_to_bv 64 row0) = None) by (rewrite (LEQ3 _ NE_row0_row3); exact Drow0_3).
  assert (Drow1_4 : live A4 (Z_to_bv 64 row1) = None) by (rewrite (LEQ3 _ NE_row1_row3); exact Drow1_3).
  assert (Drow2_4 : live A4 (Z_to_bv 64 row2) = None) by (rewrite (LEQ3 _ NE_row2_row3); exact Drow2_3).
  assert (SUB3 : sub_live A4 A3).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row3) by (intros ->; rewrite Drow3_4 in Lq; discriminate Lq). rewrite <- (LEQ3 q NEq). exact Lq. }
  assert (PM4 : POSTM C A4 s m0 m4).
  { apply (POSTM_trans C A4 s m0 M3 m4); [apply (POSTM_sub C A4 A3 _ _ _ SUB3); exact (POSTM_trans _ _ _ _ _ _ PM3 PMs3)|].
    apply (POSTM_mono C A4 (s + OFF3) s); [unfold OFF3; lia | exact PMc3]. }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row3 :: [Z_to_bv 64 row2; Z_to_bv 64 row1; Z_to_bv 64 row0])) => eq_trans (LEQ3 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL3 q (fun XX => Hq (or_intror XX)))) as LDEL4.
  assert (KEPT3 : Forall (ex_region_kept E3 M3 m4) [(EVar 32, OFF3, 0%Z); (EVar 35, 0%Z, 8%Z); (EVar 36, 0%Z, 32%Z); (EVar 37, 0%Z, 40%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF3 1104 M3 m4 E3 (EVar 32) CK (proj1 PMc3) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (sd_kept_cell C (s + OFF3) psel M3 m4 E3 (EVar 35) CK (proj1 PMc3) ltac:(unfold OFF3; lia) ltac:(unfold OFF3; lia) RP eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A4 A3 M3 _ M3 m4 E3 (EVar 36) sel 32 CK HWs3 Lsel_a3 RRsel eq_refl (proj2 PMc3) Lsel_a4 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A4 A3 M3 _ M3 m4 E3 (EVar 37) dat 40 CK HWs3 Ldat_a3 RRdat eq_refl (proj2 PMc3) Ldat_a4 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E3 M3 m4 _ [] _ HKc3 KEPT3) as HKk3.
  match type of HKk3 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E3 m4 kk') in HKk3 end.
  pose proof (regs_ok_agree 142%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 1410112 m4]) _ _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa3.
  pose proof (exW_regs_call _ _ _ _ _ HRa3 (ex_regs_ok_junk vals3 r4 [exW_canary SEGS 1410112 m4] 142%nat ltac:(vm_cast_no_check (eq_refl 142%nat))) CS3) as HRn4.
  clear HRa3.
  assert (HKa4 : know_ok SEGS (ex_envL vals3 r4 [exW_canary SEGS 1410112 m4]) m4 _) by (exact (know_ok_agree SEGS 142%nat E3 _ m4 _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk3)).
  rewrite (fr_denot_agree 142%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 1410112 m4]) _ fr (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc3 HKk3 KEPT3 HC3 HWs3 PMs3 Q10_3 Q1_3 Q2_3 Q4_3 PM3 HW3 PMc3 CS3 SUB3 RM3 RT3 LEQ3 OFF3 LDEL3 Lrow3_a3 Lrow4_a3 Ldat_a3 Lsel_a3 Drow0_3 Drow1_3 Drow2_3.
  subst M3. clear log3. clear E3. try clear Rc3. clear KN3.
  lazymatch type of HRn4 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn4 end.
  pose proof (W_sok_win C A4 m4 _ (s - 1104) (Z.to_nat 1104) CK HW4 GLO1 GLO2) as SOK4.
  pose proof (exW_canary_ok SEGS 1410112 m4 (canary_any m4)) as CANOK4.
  pose (vals4 := vals3 ++ map (getr r4) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m4]).
  pose proof (exW_kn_fixed SEGS C A4 m4 _ (ex_envL vals3 r4 [exW_canary SEGS 1410112 m4]) (EVar 174) (EVar 32) (exW_canary SEGS 1410112 m4) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW4 eq_refl (proj1 CANOK4) (proj2 CANOK4) eq_refl eq_refl eq_refl SOK4 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf4.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf4 HKa4)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn4 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN4 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf4 HKa4 SOK4 CANOK4.
  repeat match goal with H : getr r4 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc4 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E4 := EEx) in HR, Hlf, HK, Hms |- *; set (log4 := LLx) in Hms, Hlf; set (M4 := mem_denot E4 m4 log4) in Hms end.
  assert (WP4 : W C A4 M4 (with_vmmaps vm4 md) /\ POSTM C A4 s m4 M4).
  { subst M4. apply (exW_win C A4 A4 m4 _ E4 log4 (EVar 32) s 1104 CK HW4 (sub_live_refl A4) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi]. }
  destruct WP4 as [HWs4 PMs4].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log4 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC4 : carry log4 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc4 : know_ok SEGS E4 M4 kn1) by (apply (carry_after SEGS E4 m4 log4 kn0 [] kn1 scs hs HC4 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact Hms |].
  pose (BS4 := [(32%nat, s); (35%nat, psel); (36%nat, sel); (37%nat, dat); (38%nat, row0); (39%nat, row1); (40%nat, row2); (41%nat, row3); (42%nat, row4)]).
  exW_regfactB BS4 HR ex_r10 Q10_4. exW_regfactB BS4 HR ex_r1 Q1_4. exW_regfactB BS4 HR ex_r2 Q2_4. exW_regfactB BS4 HR ex_r4 Q4_4.
  clear BS4.
  lazymatch type of Q2_4 with _ = Z_to_bv 64 (s + ?off) => pose (OFF4 := off) end.
  lazymatch type of Q1_4 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_4 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A4 M4 _ Rc4 (Z_to_bv 64 row4) (Z_to_bv 64 ret) n4 sp' S CK HWs4 Q10_4 Lrow4_a4 F0row4 Q1_4
             ltac:(red; apply bv_eq; reflexivity) Q4_4 Q2_4 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A5 m5 vm5 r5 HW5 CS4 Drow4_5 LEQ4 PMc4 RM4.
  rewrite with_vmmaps_twice in HW5 |- *. rewrite with_vmmaps_vmmaps in RM4.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT4 RM4 ltac:(lia) ltac:(lia)) as RT5. cbn [Z.add] in RT5.
  assert (Ldat_a5 : live A5 (Z_to_bv 64 dat) = Some 40%Z) by (rewrite (LEQ4 _ NE_dat_row4); exact Ldat_a4).
  assert (Lsel_a5 : live A5 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ4 _ NE_sel_row4); exact Lsel_a4).
  assert (Drow0_5 : live A5 (Z_to_bv 64 row0) = None) by (rewrite (LEQ4 _ NE_row0_row4); exact Drow0_4).
  assert (Drow1_5 : live A5 (Z_to_bv 64 row1) = None) by (rewrite (LEQ4 _ NE_row1_row4); exact Drow1_4).
  assert (Drow2_5 : live A5 (Z_to_bv 64 row2) = None) by (rewrite (LEQ4 _ NE_row2_row4); exact Drow2_4).
  assert (Drow3_5 : live A5 (Z_to_bv 64 row3) = None) by (rewrite (LEQ4 _ NE_row3_row4); exact Drow3_4).
  assert (SUB4 : sub_live A5 A4).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row4) by (intros ->; rewrite Drow4_5 in Lq; discriminate Lq). rewrite <- (LEQ4 q NEq). exact Lq. }
  assert (PM5 : POSTM C A5 s m0 m5).
  { apply (POSTM_trans C A5 s m0 M4 m5); [apply (POSTM_sub C A5 A4 _ _ _ SUB4); exact (POSTM_trans _ _ _ _ _ _ PM4 PMs4)|].
    apply (POSTM_mono C A5 (s + OFF4) s); [unfold OFF4; lia | exact PMc4]. }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row4 :: [Z_to_bv 64 row3; Z_to_bv 64 row2; Z_to_bv 64 row1; Z_to_bv 64 row0])) => eq_trans (LEQ4 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL4 q (fun XX => Hq (or_intror XX)))) as LDEL5.
  assert (KEPT4 : Forall (ex_region_kept E4 M4 m5) [(EVar 32, OFF4, 0%Z); (EVar 35, 0%Z, 8%Z); (EVar 36, 0%Z, 32%Z); (EVar 37, 0%Z, 40%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF4 1104 M4 m5 E4 (EVar 32) CK (proj1 PMc4) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (sd_kept_cell C (s + OFF4) psel M4 m5 E4 (EVar 35) CK (proj1 PMc4) ltac:(unfold OFF4; lia) ltac:(unfold OFF4; lia) RP eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A5 A4 M4 _ M4 m5 E4 (EVar 36) sel 32 CK HWs4 Lsel_a4 RRsel eq_refl (proj2 PMc4) Lsel_a5 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A5 A4 M4 _ M4 m5 E4 (EVar 37) dat 40 CK HWs4 Ldat_a4 RRdat eq_refl (proj2 PMc4) Ldat_a5 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E4 M4 m5 _ [] _ HKc4 KEPT4) as HKk4.
  match type of HKk4 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E4 m5 kk') in HKk4 end.
  pose proof (regs_ok_agree 175%nat E4 (ex_envL vals4 r5 [exW_canary SEGS 1410112 m5]) _ _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa4.
  pose proof (exW_regs_call _ _ _ _ _ HRa4 (ex_regs_ok_junk vals4 r5 [exW_canary SEGS 1410112 m5] 175%nat ltac:(vm_cast_no_check (eq_refl 175%nat))) CS4) as HRn5.
  clear HRa4.
  assert (HKa5 : know_ok SEGS (ex_envL vals4 r5 [exW_canary SEGS 1410112 m5]) m5 _) by (exact (know_ok_agree SEGS 175%nat E4 _ m5 _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk4)).
  rewrite (fr_denot_agree 175%nat E4 (ex_envL vals4 r5 [exW_canary SEGS 1410112 m5]) _ fr (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc4 HKk4 KEPT4 HC4 HWs4 PMs4 Q10_4 Q1_4 Q2_4 Q4_4 PM4 HW4 PMc4 CS4 SUB4 RM4 RT4 LEQ4 OFF4 LDEL4 Lrow4_a4 Ldat_a4 Lsel_a4 Drow0_4 Drow1_4 Drow2_4 Drow3_4.
  subst M4. clear log4. clear E4. try clear Rc4. clear KN4.
  lazymatch type of HRn5 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn5 end.
  pose proof (W_sok_win C A5 m5 _ (s - 1104) (Z.to_nat 1104) CK HW5 GLO1 GLO2) as SOK5.
  pose proof (exW_canary_ok SEGS 1410112 m5 (canary_any m5)) as CANOK5.
  pose (vals5 := vals4 ++ map (getr r5) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m5]).
  pose proof (exW_kn_fixed SEGS C A5 m5 _ (ex_envL vals4 r5 [exW_canary SEGS 1410112 m5]) (EVar 207) (EVar 32) (exW_canary SEGS 1410112 m5) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW5 eq_refl (proj1 CANOK5) (proj2 CANOK5) eq_refl eq_refl eq_refl SOK5 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf5.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf5 HKa5)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn5 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN5 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf5 HKa5 SOK5 CANOK5.
  repeat match goal with H : getr r5 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc5 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E5 := EEx) in HR, Hlf, HK, Hms |- *; set (log5 := LLx) in Hms, Hlf; set (M5 := mem_denot E5 m5 log5) in Hms end.
  assert (WP5 : W C A5 M5 (with_vmmaps vm5 md) /\ POSTM C A5 s m5 M5).
  { subst M5. apply (exW_win C A5 A5 m5 _ E5 log5 (EVar 32) s 1104 CK HW5 (sub_live_refl A5) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi]. }
  destruct WP5 as [HWs5 PMs5].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log5 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC5 : carry log5 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc5 : know_ok SEGS E5 M5 kn1) by (apply (carry_after SEGS E5 m5 log5 kn0 [] kn1 scs hs HC5 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact Hms |].
  pose (BS5 := [(32%nat, s); (35%nat, psel); (36%nat, sel); (37%nat, dat); (38%nat, row0); (39%nat, row1); (40%nat, row2); (41%nat, row3); (42%nat, row4)]).
  exW_regfactB BS5 HR ex_r10 Q10_5. exW_regfactB BS5 HR ex_r1 Q1_5. exW_regfactB BS5 HR ex_r2 Q2_5. exW_regfactB BS5 HR ex_r4 Q4_5.
  clear BS5.
  lazymatch type of Q2_5 with _ = Z_to_bv 64 (s + ?off) => pose (OFF5 := off) end.
  lazymatch type of Q1_5 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_5 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A5 M5 _ Rc5 (Z_to_bv 64 dat) (Z_to_bv 64 ret) 40 sp' S CK HWs5 Q10_5 Ldat_a5 F0dat Q1_5
             ltac:(red; apply bv_eq; reflexivity) Q4_5 Q2_5 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A6 m6 vm6 r6 HW6 CS5 Ddat_6 LEQ5 PMc5 RM5.
  rewrite with_vmmaps_twice in HW6 |- *. rewrite with_vmmaps_vmmaps in RM5.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT5 RM5 ltac:(lia) ltac:(lia)) as RT6. cbn [Z.add] in RT6.
  assert (Lsel_a6 : live A6 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ5 _ NE_sel_dat); exact Lsel_a5).
  assert (Drow0_6 : live A6 (Z_to_bv 64 row0) = None) by (rewrite (LEQ5 _ (not_eq_sym NE_dat_row0)); exact Drow0_5).
  assert (Drow1_6 : live A6 (Z_to_bv 64 row1) = None) by (rewrite (LEQ5 _ (not_eq_sym NE_dat_row1)); exact Drow1_5).
  assert (Drow2_6 : live A6 (Z_to_bv 64 row2) = None) by (rewrite (LEQ5 _ (not_eq_sym NE_dat_row2)); exact Drow2_5).
  assert (Drow3_6 : live A6 (Z_to_bv 64 row3) = None) by (rewrite (LEQ5 _ (not_eq_sym NE_dat_row3)); exact Drow3_5).
  assert (Drow4_6 : live A6 (Z_to_bv 64 row4) = None) by (rewrite (LEQ5 _ (not_eq_sym NE_dat_row4)); exact Drow4_5).
  assert (SUB5 : sub_live A6 A5).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 dat) by (intros ->; rewrite Ddat_6 in Lq; discriminate Lq). rewrite <- (LEQ5 q NEq). exact Lq. }
  assert (PM6 : POSTM C A6 s m0 m6).
  { apply (POSTM_trans C A6 s m0 M5 m6); [apply (POSTM_sub C A6 A5 _ _ _ SUB5); exact (POSTM_trans _ _ _ _ _ _ PM5 PMs5)|].
    apply (POSTM_mono C A6 (s + OFF5) s); [unfold OFF5; lia | exact PMc5]. }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 dat :: [Z_to_bv 64 row4; Z_to_bv 64 row3; Z_to_bv 64 row2; Z_to_bv 64 row1; Z_to_bv 64 row0])) => eq_trans (LEQ5 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL5 q (fun XX => Hq (or_intror XX)))) as LDEL6.
  assert (KEPT5 : Forall (ex_region_kept E5 M5 m6) [(EVar 32, OFF5, 0%Z); (EVar 35, 0%Z, 8%Z); (EVar 36, 0%Z, 32%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF5 1104 M5 m6 E5 (EVar 32) CK (proj1 PMc5) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (sd_kept_cell C (s + OFF5) psel M5 m6 E5 (EVar 35) CK (proj1 PMc5) ltac:(unfold OFF5; lia) ltac:(unfold OFF5; lia) RP eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A6 A5 M5 _ M5 m6 E5 (EVar 36) sel 32 CK HWs5 Lsel_a5 RRsel eq_refl (proj2 PMc5) Lsel_a6 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E5 M5 m6 _ [] _ HKc5 KEPT5) as HKk5.
  match type of HKk5 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E5 m6 kk') in HKk5 end.
  pose proof (regs_ok_agree 208%nat E5 (ex_envL vals5 r6 [exW_canary SEGS 1410112 m6]) _ _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa5.
  pose proof (exW_regs_call _ _ _ _ _ HRa5 (ex_regs_ok_junk vals5 r6 [exW_canary SEGS 1410112 m6] 208%nat ltac:(vm_cast_no_check (eq_refl 208%nat))) CS5) as HRn6.
  clear HRa5.
  assert (HKa6 : know_ok SEGS (ex_envL vals5 r6 [exW_canary SEGS 1410112 m6]) m6 _) by (exact (know_ok_agree SEGS 208%nat E5 _ m6 _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk5)).
  rewrite (fr_denot_agree 208%nat E5 (ex_envL vals5 r6 [exW_canary SEGS 1410112 m6]) _ fr (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc5 HKk5 KEPT5 HC5 HWs5 PMs5 Q10_5 Q1_5 Q2_5 Q4_5 PM5 HW5 PMc5 CS5 SUB5 RM5 RT5 LEQ5 OFF5 LDEL5 Ldat_a5 Lsel_a5 Drow0_5 Drow1_5 Drow2_5 Drow3_5 Drow4_5.
  subst M5. clear log5. clear E5. try clear Rc5. clear KN5.
  lazymatch type of HRn6 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn6 end.
  pose proof (W_sok_win C A6 m6 _ (s - 1104) (Z.to_nat 1104) CK HW6 GLO1 GLO2) as SOK6.
  pose proof (exW_canary_ok SEGS 1410112 m6 (canary_any m6)) as CANOK6.
  pose (vals6 := vals5 ++ map (getr r6) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m6]).
  pose proof (exW_kn_fixed SEGS C A6 m6 _ (ex_envL vals5 r6 [exW_canary SEGS 1410112 m6]) (EVar 240) (EVar 32) (exW_canary SEGS 1410112 m6) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW6 eq_refl (proj1 CANOK6) (proj2 CANOK6) eq_refl eq_refl eq_refl SOK6 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf6.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf6 HKa6)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn6 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN6 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf6 HKa6 SOK6 CANOK6.
  repeat match goal with H : getr r6 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc6 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E6 := EEx) in HR, Hlf, HK, Hms |- *; set (log6 := LLx) in Hms, Hlf; set (M6 := mem_denot E6 m6 log6) in Hms end.
  assert (WP6 : W C A6 M6 (with_vmmaps vm6 md) /\ POSTM C A6 s m6 M6).
  { subst M6. apply (exW_win C A6 A6 m6 _ E6 log6 (EVar 32) s 1104 CK HW6 (sub_live_refl A6) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi]. }
  destruct WP6 as [HWs6 PMs6].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log6 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC6 : carry log6 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc6 : know_ok SEGS E6 M6 kn1) by (apply (carry_after SEGS E6 m6 log6 kn0 [] kn1 scs hs HC6 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact Hms |].
  pose (BS6 := [(32%nat, s); (35%nat, psel); (36%nat, sel); (37%nat, dat); (38%nat, row0); (39%nat, row1); (40%nat, row2); (41%nat, row3); (42%nat, row4)]).
  exW_regfactB BS6 HR ex_r10 Q10_6. exW_regfactB BS6 HR ex_r1 Q1_6. exW_regfactB BS6 HR ex_r2 Q2_6. exW_regfactB BS6 HR ex_r4 Q4_6.
  clear BS6.
  lazymatch type of Q2_6 with _ = Z_to_bv 64 (s + ?off) => pose (OFF6 := off) end.
  lazymatch type of Q1_6 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_6 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A6 M6 _ Rc6 (Z_to_bv 64 sel) (Z_to_bv 64 ret) 32 sp' S CK HWs6 Q10_6 Lsel_a6 F0sel Q1_6
             ltac:(red; apply bv_eq; reflexivity) Q4_6 Q2_6 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A7 m7 vm7 r7 HW7 CS6 Dsel_7 LEQ6 PMc6 RM6.
  rewrite with_vmmaps_twice in HW7 |- *. rewrite with_vmmaps_vmmaps in RM6.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT6 RM6 ltac:(lia) ltac:(lia)) as RT7. cbn [Z.add] in RT7.
  assert (Drow0_7 : live A7 (Z_to_bv 64 row0) = None) by (rewrite (LEQ6 _ (not_eq_sym NE_sel_row0)); exact Drow0_6).
  assert (Drow1_7 : live A7 (Z_to_bv 64 row1) = None) by (rewrite (LEQ6 _ (not_eq_sym NE_sel_row1)); exact Drow1_6).
  assert (Drow2_7 : live A7 (Z_to_bv 64 row2) = None) by (rewrite (LEQ6 _ (not_eq_sym NE_sel_row2)); exact Drow2_6).
  assert (Drow3_7 : live A7 (Z_to_bv 64 row3) = None) by (rewrite (LEQ6 _ (not_eq_sym NE_sel_row3)); exact Drow3_6).
  assert (Drow4_7 : live A7 (Z_to_bv 64 row4) = None) by (rewrite (LEQ6 _ (not_eq_sym NE_sel_row4)); exact Drow4_6).
  assert (Ddat_7 : live A7 (Z_to_bv 64 dat) = None) by (rewrite (LEQ6 _ (not_eq_sym NE_sel_dat)); exact Ddat_6).
  assert (SUB6 : sub_live A7 A6).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 sel) by (intros ->; rewrite Dsel_7 in Lq; discriminate Lq). rewrite <- (LEQ6 q NEq). exact Lq. }
  assert (PM7 : POSTM C A7 s m0 m7).
  { apply (POSTM_trans C A7 s m0 M6 m7); [apply (POSTM_sub C A7 A6 _ _ _ SUB6); exact (POSTM_trans _ _ _ _ _ _ PM6 PMs6)|].
    apply (POSTM_mono C A7 (s + OFF6) s); [unfold OFF6; lia | exact PMc6]. }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 sel :: [Z_to_bv 64 dat; Z_to_bv 64 row4; Z_to_bv 64 row3; Z_to_bv 64 row2; Z_to_bv 64 row1; Z_to_bv 64 row0])) => eq_trans (LEQ6 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL6 q (fun XX => Hq (or_intror XX)))) as LDEL7.
  assert (KEPT6 : Forall (ex_region_kept E6 M6 m7) [(EVar 32, OFF6, 0%Z); (EVar 35, 0%Z, 8%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF6 1104 M6 m7 E6 (EVar 32) CK (proj1 PMc6) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (sd_kept_cell C (s + OFF6) psel M6 m7 E6 (EVar 35) CK (proj1 PMc6) ltac:(unfold OFF6; lia) ltac:(unfold OFF6; lia) RP eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E6 M6 m7 _ [] _ HKc6 KEPT6) as HKk6.
  match type of HKk6 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E6 m7 kk') in HKk6 end.
  pose proof (regs_ok_agree 241%nat E6 (ex_envL vals6 r7 [exW_canary SEGS 1410112 m7]) _ _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa6.
  pose proof (exW_regs_call _ _ _ _ _ HRa6 (ex_regs_ok_junk vals6 r7 [exW_canary SEGS 1410112 m7] 241%nat ltac:(vm_cast_no_check (eq_refl 241%nat))) CS6) as HRn7.
  clear HRa6.
  assert (HKa7 : know_ok SEGS (ex_envL vals6 r7 [exW_canary SEGS 1410112 m7]) m7 _) by (exact (know_ok_agree SEGS 241%nat E6 _ m7 _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk6)).
  rewrite (fr_denot_agree 241%nat E6 (ex_envL vals6 r7 [exW_canary SEGS 1410112 m7]) _ fr (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc6 HKk6 KEPT6 HC6 HWs6 PMs6 Q10_6 Q1_6 Q2_6 Q4_6 PM6 HW6 PMc6 CS6 SUB6 RM6 RT6 LEQ6 OFF6 LDEL6 Lsel_a6 Drow0_6 Drow1_6 Drow2_6 Drow3_6 Drow4_6 Ddat_6.
  subst M6. clear log6. clear E6. try clear Rc6. clear KN6.
  lazymatch type of HRn7 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn7 end.
  pose proof (W_sok_win C A7 m7 _ (s - 1104) (Z.to_nat 1104) CK HW7 GLO1 GLO2) as SOK7.
  pose proof (exW_canary_ok SEGS 1410112 m7 (canary_any m7)) as CANOK7.
  pose (vals7 := vals6 ++ map (getr r7) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m7]).
  pose proof (exW_kn_fixed SEGS C A7 m7 _ (ex_envL vals6 r7 [exW_canary SEGS 1410112 m7]) (EVar 273) (EVar 32) (exW_canary SEGS 1410112 m7) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW7 eq_refl (proj1 CANOK7) (proj2 CANOK7) eq_refl eq_refl eq_refl SOK7 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf7.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf7 HKa7)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn7 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN7 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf7 HKa7 SOK7 CANOK7.
  repeat match goal with H : getr r7 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E7 := EEx) in HR, Hlf, HK, Hms |- *; set (log7 := LLx) in Hms, Hlf; set (M7 := mem_denot E7 m7 log7) in Hms end.
  assert (WP7 : W C A7 M7 (with_vmmaps vm7 md) /\ POSTM C A7 (psel + 8) m7 M7 /\ (forall a : word, (s <= u a < psel)%Z -> M7 a = m7 a)).
  { subst M7. apply (sd_win_cell C A7 A7 m7 _ E7 log7 (EVar 32) (EVar 35) s 1104 psel CK HW7 (sub_live_refl A7) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | reflexivity | lia | exact GLO1 | exact Hsp | exact Hph]. }
  destruct WP7 as (HWs7 & PMs7 & BET7).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact Hms |].
  pose (BSF := [(32%nat, s); (35%nat, psel)]).
  exW_cellB HK Hlf r0 BSF (EVar 35) psel 0%Z 8%nat Cpsel.
  refine (HC A7 M7 vm7 RcF HWs7 _ Dsel_7 Ddat_7 Drow0_7 Drow1_7 Drow2_7 Drow3_7 Drow4_7
            ltac:(intros q Hq; apply LDEL7; intros Hin; apply Hq; cbn [In] in Hin |- *; tauto)
            (POSTM_trans _ _ _ _ _ _ (POSTM_mono C A7 s (psel + 8) m0 m7 ltac:(lia) PM7) PMs7) Cpsel
            (fun a Ha => eq_trans (BET7 a Ha) (sd_frm_above C s m0 m7 a CK (proj1 PM7) ltac:(lia) ltac:(lia))) RT7).
  lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 RcF [(2%nat, EVar 32); (4%nat, ELit 1278416)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor; [symmetry; exact HTP | constructor]] | vm_compute; reflexivity] end.
Qed.

(* [comment removed for export] *)
Lemma seld_chain8 : forall (fx : FPState) C A m md regs (s psel sel dat row0 row1 row2 row3 row4 row5 row6 row7 n0 n1 n2 n3 n4 n5 n6 n7 : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + O23LeptSelDC.SELD_WIN <= s)%Z -> (s <= psel)%Z -> (psel + 8 <= c_top C)%Z -> (psel mod 8 = 0)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 1278416 -> getr regs 10 = Z_to_bv 64 psel ->
  rdn SEGS m (Z_to_bv 64 (psel + 0)) 8 = Some (Z_to_le_bytes 8 sel) ->
  rdn SEGS m (Z_to_bv 64 (sel + 0)) 4 = Some (Z_to_le_bytes 4 8) ->
  rdn SEGS m (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 dat) ->
  rdn SEGS m (Z_to_bv 64 (sel + 24)) 8 = Some (Z_to_le_bytes 8 0) ->
  rdn SEGS m (Z_to_bv 64 (dat + 0)) 8 = Some (Z_to_le_bytes 8 row0) ->
  rdn SEGS m (Z_to_bv 64 (dat + 8)) 8 = Some (Z_to_le_bytes 8 row1) ->
  rdn SEGS m (Z_to_bv 64 (dat + 16)) 8 = Some (Z_to_le_bytes 8 row2) ->
  rdn SEGS m (Z_to_bv 64 (dat + 24)) 8 = Some (Z_to_le_bytes 8 row3) ->
  rdn SEGS m (Z_to_bv 64 (dat + 32)) 8 = Some (Z_to_le_bytes 8 row4) ->
  rdn SEGS m (Z_to_bv 64 (dat + 40)) 8 = Some (Z_to_le_bytes 8 row5) ->
  rdn SEGS m (Z_to_bv 64 (dat + 48)) 8 = Some (Z_to_le_bytes 8 row6) ->
  rdn SEGS m (Z_to_bv 64 (dat + 56)) 8 = Some (Z_to_le_bytes 8 row7) ->
  live A (Z_to_bv 64 sel) = Some 32%Z -> live (c_A0 C) (Z_to_bv 64 sel) = None -> (0 <= sel < 2 ^ 64)%Z ->
  live A (Z_to_bv 64 dat) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 dat) = None -> (0 <= dat < 2 ^ 64)%Z ->
  live A (Z_to_bv 64 row0) = Some n0%Z -> live (c_A0 C) (Z_to_bv 64 row0) = None -> (0 <= row0 < 2 ^ 64)%Z ->
  live A (Z_to_bv 64 row1) = Some n1%Z -> live (c_A0 C) (Z_to_bv 64 row1) = None -> (0 <= row1 < 2 ^ 64)%Z ->
  live A (Z_to_bv 64 row2) = Some n2%Z -> live (c_A0 C) (Z_to_bv 64 row2) = None -> (0 <= row2 < 2 ^ 64)%Z ->
  live A (Z_to_bv 64 row3) = Some n3%Z -> live (c_A0 C) (Z_to_bv 64 row3) = None -> (0 <= row3 < 2 ^ 64)%Z ->
  live A (Z_to_bv 64 row4) = Some n4%Z -> live (c_A0 C) (Z_to_bv 64 row4) = None -> (0 <= row4 < 2 ^ 64)%Z ->
  live A (Z_to_bv 64 row5) = Some n5%Z -> live (c_A0 C) (Z_to_bv 64 row5) = None -> (0 <= row5 < 2 ^ 64)%Z ->
  live A (Z_to_bv 64 row6) = Some n6%Z -> live (c_A0 C) (Z_to_bv 64 row6) = None -> (0 <= row6 < 2 ^ 64)%Z ->
  live A (Z_to_bv 64 row7) = Some n7%Z -> live (c_A0 C) (Z_to_bv 64 row7) = None -> (0 <= row7 < 2 ^ 64)%Z ->
  Z_to_bv 64 sel <> Z_to_bv 64 dat ->
  Z_to_bv 64 sel <> Z_to_bv 64 row0 ->
  Z_to_bv 64 dat <> Z_to_bv 64 row0 ->
  Z_to_bv 64 sel <> Z_to_bv 64 row1 ->
  Z_to_bv 64 dat <> Z_to_bv 64 row1 ->
  Z_to_bv 64 row0 <> Z_to_bv 64 row1 ->
  Z_to_bv 64 sel <> Z_to_bv 64 row2 ->
  Z_to_bv 64 dat <> Z_to_bv 64 row2 ->
  Z_to_bv 64 row0 <> Z_to_bv 64 row2 ->
  Z_to_bv 64 row1 <> Z_to_bv 64 row2 ->
  Z_to_bv 64 sel <> Z_to_bv 64 row3 ->
  Z_to_bv 64 dat <> Z_to_bv 64 row3 ->
  Z_to_bv 64 row0 <> Z_to_bv 64 row3 ->
  Z_to_bv 64 row1 <> Z_to_bv 64 row3 ->
  Z_to_bv 64 row2 <> Z_to_bv 64 row3 ->
  Z_to_bv 64 sel <> Z_to_bv 64 row4 ->
  Z_to_bv 64 dat <> Z_to_bv 64 row4 ->
  Z_to_bv 64 row0 <> Z_to_bv 64 row4 ->
  Z_to_bv 64 row1 <> Z_to_bv 64 row4 ->
  Z_to_bv 64 row2 <> Z_to_bv 64 row4 ->
  Z_to_bv 64 row3 <> Z_to_bv 64 row4 ->
  Z_to_bv 64 sel <> Z_to_bv 64 row5 ->
  Z_to_bv 64 dat <> Z_to_bv 64 row5 ->
  Z_to_bv 64 row0 <> Z_to_bv 64 row5 ->
  Z_to_bv 64 row1 <> Z_to_bv 64 row5 ->
  Z_to_bv 64 row2 <> Z_to_bv 64 row5 ->
  Z_to_bv 64 row3 <> Z_to_bv 64 row5 ->
  Z_to_bv 64 row4 <> Z_to_bv 64 row5 ->
  Z_to_bv 64 sel <> Z_to_bv 64 row6 ->
  Z_to_bv 64 dat <> Z_to_bv 64 row6 ->
  Z_to_bv 64 row0 <> Z_to_bv 64 row6 ->
  Z_to_bv 64 row1 <> Z_to_bv 64 row6 ->
  Z_to_bv 64 row2 <> Z_to_bv 64 row6 ->
  Z_to_bv 64 row3 <> Z_to_bv 64 row6 ->
  Z_to_bv 64 row4 <> Z_to_bv 64 row6 ->
  Z_to_bv 64 row5 <> Z_to_bv 64 row6 ->
  Z_to_bv 64 sel <> Z_to_bv 64 row7 ->
  Z_to_bv 64 dat <> Z_to_bv 64 row7 ->
  Z_to_bv 64 row0 <> Z_to_bv 64 row7 ->
  Z_to_bv 64 row1 <> Z_to_bv 64 row7 ->
  Z_to_bv 64 row2 <> Z_to_bv 64 row7 ->
  Z_to_bv 64 row3 <> Z_to_bv 64 row7 ->
  Z_to_bv 64 row4 <> Z_to_bv 64 row7 ->
  Z_to_bv 64 row5 <> Z_to_bv 64 row7 ->
  Z_to_bv 64 row6 <> Z_to_bv 64 row7 ->
  (forall A' m' vm' regs',
     W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     live A' (Z_to_bv 64 sel) = None ->
     live A' (Z_to_bv 64 dat) = None ->
     live A' (Z_to_bv 64 row0) = None ->
     live A' (Z_to_bv 64 row1) = None ->
     live A' (Z_to_bv 64 row2) = None ->
     live A' (Z_to_bv 64 row3) = None ->
     live A' (Z_to_bv 64 row4) = None ->
     live A' (Z_to_bv 64 row5) = None ->
     live A' (Z_to_bv 64 row6) = None ->
     live A' (Z_to_bv 64 row7) = None ->
     (forall q : word, ~ In q [Z_to_bv 64 sel; Z_to_bv 64 dat; Z_to_bv 64 row0; Z_to_bv 64 row1; Z_to_bv 64 row2; Z_to_bv 64 row3; Z_to_bv 64 row4; Z_to_bv 64 row5; Z_to_bv 64 row6; Z_to_bv 64 row7] -> live A' q = live A q) ->
     POSTM C A' (psel + 8) m m' -> rdn SEGS m' (Z_to_bv 64 (psel + 0)) 8 = Some (Z_to_le_bytes 8 0) ->
     (forall a : word, (s <= u a < psel)%Z -> m' a = m a) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 674932) m al_rom) md) S.
Proof using P16 PINS.
  intros fx C A0 m0 md r0 s psel sel dat row0 row1 row2 row3 row4 row5 row6 row7 n0 n1 n2 n3 n4 n5 n6 n7 ret S CK HW0 H2 Hs16 Hlo Hsp Hph Hpal H1 Hret H4 H10 Mpsel Msy Mdat Mnm Mrow0 Mrow1 Mrow2 Mrow3 Mrow4 Mrow5 Mrow6 Mrow7
    Lsel_a0 F0sel RRsel Ldat_a0 F0dat RRdat Lrow0_a0 F0row0 RRrow0 Lrow1_a0 F0row1 RRrow1 Lrow2_a0 F0row2 RRrow2 Lrow3_a0 F0row3 RRrow3 Lrow4_a0 F0row4 RRrow4 Lrow5_a0 F0row5 RRrow5 Lrow6_a0 F0row6 RRrow6 Lrow7_a0 F0row7 RRrow7
    NE_sel_dat NE_sel_row0 NE_dat_row0 NE_sel_row1 NE_dat_row1 NE_row0_row1 NE_sel_row2 NE_dat_row2 NE_row0_row2 NE_row1_row2 NE_sel_row3 NE_dat_row3 NE_row0_row3 NE_row1_row3 NE_row2_row3 NE_sel_row4 NE_dat_row4 NE_row0_row4 NE_row1_row4 NE_row2_row4 NE_row3_row4 NE_sel_row5 NE_dat_row5 NE_row0_row5 NE_row1_row5 NE_row2_row5 NE_row3_row5 NE_row4_row5 NE_sel_row6 NE_dat_row6 NE_row0_row6 NE_row1_row6 NE_row2_row6 NE_row3_row6 NE_row4_row6 NE_row5_row6 NE_sel_row7 NE_dat_row7 NE_row0_row7 NE_row1_row7 NE_row2_row7 NE_row3_row7 NE_row4_row7 NE_row5_row7 NE_row6_row7 HC.
  unfold O23LeptSelDC.SELD_WIN in *.
  assert (Hhi : (s <= c_top C)%Z) by lia.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  assert (HTP : ex_keep (getr r0 ex_r4 = Z_to_bv 64 1278416)) by exact H4.
  destruct fx as [fr cs]. pose proof I as FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  assert (GLO1 : (c_top C - LSTK <= s - 1104)%Z) by lia.
  assert (GLO2 : (s - 1104 + Z.of_nat (Z.to_nat 1104) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (1104 <= s)%Z) by lia.
  assert (RP : (0 <= psel < 2 ^ 64)%Z) by lia.
  destruct (exW_blk_rng C A0 m0 _ sel 32 CK HW0 Lsel_a0 RRsel ltac:(lia)) as (GLsel & _ & GHsel).
  pose proof (ai_live_hull A0 m0 (m_vmmaps md) _ _ (w_inv _ _ _ _ HW0) Lsel_a0) as (_ & ALsel & _). rewrite u_Z2bv in ALsel by lia.
  pose proof (exW_win_blk_apart_h C A0 m0 _ s 1104 sel 32 CK HW0 Lsel_a0 eq_refl RRsel GLO1) as WAPsel.
  destruct (exW_blk_rng C A0 m0 _ dat 64 CK HW0 Ldat_a0 RRdat ltac:(lia)) as (GLdat & _ & GHdat).
  pose proof (ai_live_hull A0 m0 (m_vmmaps md) _ _ (w_inv _ _ _ _ HW0) Ldat_a0) as (_ & ALdat & _). rewrite u_Z2bv in ALdat by lia.
  pose proof (exW_win_blk_apart_h C A0 m0 _ s 1104 dat 64 CK HW0 Ldat_a0 eq_refl RRdat GLO1) as WAPdat.
  pose proof (W_sok_win C A0 m0 _ psel 8 CK HW0 ltac:(lia) ltac:(cbn; lia)) as SOKP.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose proof (POSTM_refl C A0 s m0) as PM0.
  pose proof (roomtr_refl A0 vm0 0 0 ltac:(lia) ltac:(lia)) as RT0.
  pose (valsI := @nil word).
  pose proof (fun (q : word) (_ : ~ In q []) => eq_refl (live A0 q)) as LDEL0.
  pose proof (W_sok_win C A0 m0 _ (s - 1104) (Z.to_nat 1104) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 1410112 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0; psel; sel; dat; row0; row1; row2; row3; row4; row5; row6; row7]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0; psel; sel; dat; row0; row1; row2; row3; row4; row5; row6; row7]) (EVar 34) (EVar 32) (exW_canary SEGS 1410112 m0) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0; psel; sel; dat; row0; row1; row2; row3; row4; row5; row6; row7]) m0 [KRange (EVar 32) 1422416 (2 ^ 63); KAlign (EVar 32) 16; KRange (EVar 35) 1422416 (2 ^ 63); KAlign (EVar 35) 8; KWr (SA (EVar 35) 0) 8; KWord (SA (EVar 35) 0) 8 (EVar 36); KDisj (SA (EVar 32) (- 1104)) 1104 (SA (EVar 35) 0) 8; KRange (EVar 36) 4096 (2 ^ 47); KAlign (EVar 36) 16; KDisj (SA (EVar 32) (- 1104)) 1104 (SA (EVar 36) 0) 32; KWord (SA (EVar 36) 0) 4 (ELit 8); KWord (SA (EVar 36) 16) 8 (EVar 37); KWord (SA (EVar 36) 24) 8 (ELit 0); KRange (EVar 37) 4096 (2 ^ 47); KAlign (EVar 37) 16; KDisj (SA (EVar 32) (- 1104)) 1104 (SA (EVar 37) 0) 64; KWord (SA (EVar 37) 0) 8 (EVar 38); KWord (SA (EVar 37) 8) 8 (EVar 39); KWord (SA (EVar 37) 16) 8 (EVar 40); KWord (SA (EVar 37) 24) 8 (EVar 41); KWord (SA (EVar 37) 32) 8 (EVar 42); KWord (SA (EVar 37) 40) 8 (EVar 43); KWord (SA (EVar 37) 48) 8 (EVar 44); KWord (SA (EVar 37) 56) 8 (EVar 45)]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 HKf0)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0; psel; sel; dat; row0; row1; row2; row3; row4; row5; row6; row7] HR.
  pose proof (ex_regs_ok_reexpr _ _ r0 ex_r10 (EVar 35) HR ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact H10)) as HRx. clear HR. rename HRx into HR.
  lazymatch type of HR with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HR end.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win C A0 A0 m0 _ E0 log0 (EVar 32) s 1104 CK HW0 (sub_live_refl A0) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi]. }
  destruct WP0 as [HWs0 PMs0].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (35%nat, psel); (36%nat, sel); (37%nat, dat); (38%nat, row0); (39%nat, row1); (40%nat, row2); (41%nat, row3); (42%nat, row4); (43%nat, row5); (44%nat, row6); (45%nat, row7)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r1 Q1_0. exW_regfactB BS0 HR ex_r2 Q2_0. exW_regfactB BS0 HR ex_r4 Q4_0.
  clear BS0.
  lazymatch type of Q2_0 with _ = Z_to_bv 64 (s + ?off) => pose (OFF0 := off) end.
  lazymatch type of Q1_0 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_0 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A0 M0 _ Rc0 (Z_to_bv 64 row0) (Z_to_bv 64 ret) n0 sp' S CK HWs0 Q10_0 Lrow0_a0 F0row0 Q1_0
             ltac:(red; apply bv_eq; reflexivity) Q4_0 Q2_0 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A1 m1 vm1 r1 HW1 CS0 Drow0_1 LEQ0 PMc0 RM0.
  rewrite with_vmmaps_twice in HW1 |- *. rewrite with_vmmaps_vmmaps in RM0.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT0 RM0 ltac:(lia) ltac:(lia)) as RT1. cbn [Z.add] in RT1.
  assert (Lrow1_a1 : live A1 (Z_to_bv 64 row1) = Some n1%Z) by (rewrite (LEQ0 _ (not_eq_sym NE_row0_row1)); exact Lrow1_a0).
  assert (Lrow2_a1 : live A1 (Z_to_bv 64 row2) = Some n2%Z) by (rewrite (LEQ0 _ (not_eq_sym NE_row0_row2)); exact Lrow2_a0).
  assert (Lrow3_a1 : live A1 (Z_to_bv 64 row3) = Some n3%Z) by (rewrite (LEQ0 _ (not_eq_sym NE_row0_row3)); exact Lrow3_a0).
  assert (Lrow4_a1 : live A1 (Z_to_bv 64 row4) = Some n4%Z) by (rewrite (LEQ0 _ (not_eq_sym NE_row0_row4)); exact Lrow4_a0).
  assert (Lrow5_a1 : live A1 (Z_to_bv 64 row5) = Some n5%Z) by (rewrite (LEQ0 _ (not_eq_sym NE_row0_row5)); exact Lrow5_a0).
  assert (Lrow6_a1 : live A1 (Z_to_bv 64 row6) = Some n6%Z) by (rewrite (LEQ0 _ (not_eq_sym NE_row0_row6)); exact Lrow6_a0).
  assert (Lrow7_a1 : live A1 (Z_to_bv 64 row7) = Some n7%Z) by (rewrite (LEQ0 _ (not_eq_sym NE_row0_row7)); exact Lrow7_a0).
  assert (Ldat_a1 : live A1 (Z_to_bv 64 dat) = Some 64%Z) by (rewrite (LEQ0 _ NE_dat_row0); exact Ldat_a0).
  assert (Lsel_a1 : live A1 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ0 _ NE_sel_row0); exact Lsel_a0).
  assert (SUB0 : sub_live A1 A0).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row0) by (intros ->; rewrite Drow0_1 in Lq; discriminate Lq). rewrite <- (LEQ0 q NEq). exact Lq. }
  assert (PM1 : POSTM C A1 s m0 m1).
  { apply (POSTM_trans C A1 s m0 M0 m1); [apply (POSTM_sub C A1 A0 _ _ _ SUB0); exact (POSTM_trans _ _ _ _ _ _ PM0 PMs0)|].
    apply (POSTM_mono C A1 (s + OFF0) s); [unfold OFF0; lia | exact PMc0]. }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row0 :: [])) => eq_trans (LEQ0 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL0 q (fun XX => Hq (or_intror XX)))) as LDEL1.
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, OFF0, 0%Z); (EVar 35, 0%Z, 8%Z); (EVar 36, 0%Z, 32%Z); (EVar 37, 0%Z, 64%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF0 1104 M0 m1 E0 (EVar 32) CK (proj1 PMc0) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (sd_kept_cell C (s + OFF0) psel M0 m1 E0 (EVar 35) CK (proj1 PMc0) ltac:(unfold OFF0; lia) ltac:(unfold OFF0; lia) RP eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A1 A0 M0 _ M0 m1 E0 (EVar 36) sel 32 CK HWs0 Lsel_a0 RRsel eq_refl (proj2 PMc0) Lsel_a1 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A1 A0 M0 _ M0 m1 E0 (EVar 37) dat 64 CK HWs0 Ldat_a0 RRdat eq_refl (proj2 PMc0) Ldat_a1 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E0 m1 kk') in HKk0 end.
  pose proof (regs_ok_agree 46%nat E0 (ex_envL vals0 r1 [exW_canary SEGS 1410112 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [exW_canary SEGS 1410112 m1] 46%nat ltac:(vm_cast_no_check (eq_refl 46%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [exW_canary SEGS 1410112 m1]) m1 _) by (exact (know_ok_agree SEGS 46%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  rewrite (fr_denot_agree 46%nat E0 (ex_envL vals0 r1 [exW_canary SEGS 1410112 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q1_0 Q2_0 Q4_0 PM0 HW0 PMc0 CS0 SUB0 RM0 RT0 LEQ0 OFF0 LDEL0 Lrow0_a0 Lrow1_a0 Lrow2_a0 Lrow3_a0 Lrow4_a0 Lrow5_a0 Lrow6_a0 Lrow7_a0 Ldat_a0 Lsel_a0.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  pose proof (W_sok_win C A1 m1 _ (s - 1104) (Z.to_nat 1104) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 1410112 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m1]).
  pose proof (exW_kn_fixed SEGS C A1 m1 _ (ex_envL vals0 r1 [exW_canary SEGS 1410112 m1]) (EVar 78) (EVar 32) (exW_canary SEGS 1410112 m1) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc1 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A1 M1 (with_vmmaps vm1 md) /\ POSTM C A1 s m1 M1).
  { subst M1. apply (exW_win C A1 A1 m1 _ E1 log1 (EVar 32) s 1104 CK HW1 (sub_live_refl A1) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi]. }
  destruct WP1 as [HWs1 PMs1].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log1 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC1 : carry log1 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc1 : know_ok SEGS E1 M1 kn1) by (apply (carry_after SEGS E1 m1 log1 kn0 [] kn1 scs hs HC1 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose (BS1 := [(32%nat, s); (35%nat, psel); (36%nat, sel); (37%nat, dat); (38%nat, row0); (39%nat, row1); (40%nat, row2); (41%nat, row3); (42%nat, row4); (43%nat, row5); (44%nat, row6); (45%nat, row7)]).
  exW_regfactB BS1 HR ex_r10 Q10_1. exW_regfactB BS1 HR ex_r1 Q1_1. exW_regfactB BS1 HR ex_r2 Q2_1. exW_regfactB BS1 HR ex_r4 Q4_1.
  clear BS1.
  lazymatch type of Q2_1 with _ = Z_to_bv 64 (s + ?off) => pose (OFF1 := off) end.
  lazymatch type of Q1_1 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_1 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A1 M1 _ Rc1 (Z_to_bv 64 row1) (Z_to_bv 64 ret) n1 sp' S CK HWs1 Q10_1 Lrow1_a1 F0row1 Q1_1
             ltac:(red; apply bv_eq; reflexivity) Q4_1 Q2_1 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A2 m2 vm2 r2 HW2 CS1 Drow1_2 LEQ1 PMc1 RM1.
  rewrite with_vmmaps_twice in HW2 |- *. rewrite with_vmmaps_vmmaps in RM1.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT1 RM1 ltac:(lia) ltac:(lia)) as RT2. cbn [Z.add] in RT2.
  assert (Lrow2_a2 : live A2 (Z_to_bv 64 row2) = Some n2%Z) by (rewrite (LEQ1 _ (not_eq_sym NE_row1_row2)); exact Lrow2_a1).
  assert (Lrow3_a2 : live A2 (Z_to_bv 64 row3) = Some n3%Z) by (rewrite (LEQ1 _ (not_eq_sym NE_row1_row3)); exact Lrow3_a1).
  assert (Lrow4_a2 : live A2 (Z_to_bv 64 row4) = Some n4%Z) by (rewrite (LEQ1 _ (not_eq_sym NE_row1_row4)); exact Lrow4_a1).
  assert (Lrow5_a2 : live A2 (Z_to_bv 64 row5) = Some n5%Z) by (rewrite (LEQ1 _ (not_eq_sym NE_row1_row5)); exact Lrow5_a1).
  assert (Lrow6_a2 : live A2 (Z_to_bv 64 row6) = Some n6%Z) by (rewrite (LEQ1 _ (not_eq_sym NE_row1_row6)); exact Lrow6_a1).
  assert (Lrow7_a2 : live A2 (Z_to_bv 64 row7) = Some n7%Z) by (rewrite (LEQ1 _ (not_eq_sym NE_row1_row7)); exact Lrow7_a1).
  assert (Ldat_a2 : live A2 (Z_to_bv 64 dat) = Some 64%Z) by (rewrite (LEQ1 _ NE_dat_row1); exact Ldat_a1).
  assert (Lsel_a2 : live A2 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ1 _ NE_sel_row1); exact Lsel_a1).
  assert (Drow0_2 : live A2 (Z_to_bv 64 row0) = None) by (rewrite (LEQ1 _ NE_row0_row1); exact Drow0_1).
  assert (SUB1 : sub_live A2 A1).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row1) by (intros ->; rewrite Drow1_2 in Lq; discriminate Lq). rewrite <- (LEQ1 q NEq). exact Lq. }
  assert (PM2 : POSTM C A2 s m0 m2).
  { apply (POSTM_trans C A2 s m0 M1 m2); [apply (POSTM_sub C A2 A1 _ _ _ SUB1); exact (POSTM_trans _ _ _ _ _ _ PM1 PMs1)|].
    apply (POSTM_mono C A2 (s + OFF1) s); [unfold OFF1; lia | exact PMc1]. }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row1 :: [Z_to_bv 64 row0])) => eq_trans (LEQ1 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL1 q (fun XX => Hq (or_intror XX)))) as LDEL2.
  assert (KEPT1 : Forall (ex_region_kept E1 M1 m2) [(EVar 32, OFF1, 0%Z); (EVar 35, 0%Z, 8%Z); (EVar 36, 0%Z, 32%Z); (EVar 37, 0%Z, 64%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF1 1104 M1 m2 E1 (EVar 32) CK (proj1 PMc1) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (sd_kept_cell C (s + OFF1) psel M1 m2 E1 (EVar 35) CK (proj1 PMc1) ltac:(unfold OFF1; lia) ltac:(unfold OFF1; lia) RP eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A2 A1 M1 _ M1 m2 E1 (EVar 36) sel 32 CK HWs1 Lsel_a1 RRsel eq_refl (proj2 PMc1) Lsel_a2 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A2 A1 M1 _ M1 m2 E1 (EVar 37) dat 64 CK HWs1 Ldat_a1 RRdat eq_refl (proj2 PMc1) Ldat_a2 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E1 M1 m2 _ [] _ HKc1 KEPT1) as HKk1.
  match type of HKk1 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E1 m2 kk') in HKk1 end.
  pose proof (regs_ok_agree 79%nat E1 (ex_envL vals1 r2 [exW_canary SEGS 1410112 m2]) _ _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa1.
  pose proof (exW_regs_call _ _ _ _ _ HRa1 (ex_regs_ok_junk vals1 r2 [exW_canary SEGS 1410112 m2] 79%nat ltac:(vm_cast_no_check (eq_refl 79%nat))) CS1) as HRn2.
  clear HRa1.
  assert (HKa2 : know_ok SEGS (ex_envL vals1 r2 [exW_canary SEGS 1410112 m2]) m2 _) by (exact (know_ok_agree SEGS 79%nat E1 _ m2 _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk1)).
  rewrite (fr_denot_agree 79%nat E1 (ex_envL vals1 r2 [exW_canary SEGS 1410112 m2]) _ fr (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc1 HKk1 KEPT1 HC1 HWs1 PMs1 Q10_1 Q1_1 Q2_1 Q4_1 PM1 HW1 PMc1 CS1 SUB1 RM1 RT1 LEQ1 OFF1 LDEL1 Lrow1_a1 Lrow2_a1 Lrow3_a1 Lrow4_a1 Lrow5_a1 Lrow6_a1 Lrow7_a1 Ldat_a1 Lsel_a1 Drow0_1.
  subst M1. clear log1. clear E1. try clear Rc1. clear KN1.
  lazymatch type of HRn2 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn2 end.
  pose proof (W_sok_win C A2 m2 _ (s - 1104) (Z.to_nat 1104) CK HW2 GLO1 GLO2) as SOK2.
  pose proof (exW_canary_ok SEGS 1410112 m2 (canary_any m2)) as CANOK2.
  pose (vals2 := vals1 ++ map (getr r2) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m2]).
  pose proof (exW_kn_fixed SEGS C A2 m2 _ (ex_envL vals1 r2 [exW_canary SEGS 1410112 m2]) (EVar 111) (EVar 32) (exW_canary SEGS 1410112 m2) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW2 eq_refl (proj1 CANOK2) (proj2 CANOK2) eq_refl eq_refl eq_refl SOK2 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf2.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf2 HKa2)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn2 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN2 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf2 HKa2 SOK2 CANOK2.
  repeat match goal with H : getr r2 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc2 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E2 := EEx) in HR, Hlf, HK, Hms |- *; set (log2 := LLx) in Hms, Hlf; set (M2 := mem_denot E2 m2 log2) in Hms end.
  assert (WP2 : W C A2 M2 (with_vmmaps vm2 md) /\ POSTM C A2 s m2 M2).
  { subst M2. apply (exW_win C A2 A2 m2 _ E2 log2 (EVar 32) s 1104 CK HW2 (sub_live_refl A2) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi]. }
  destruct WP2 as [HWs2 PMs2].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log2 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC2 : carry log2 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc2 : know_ok SEGS E2 M2 kn1) by (apply (carry_after SEGS E2 m2 log2 kn0 [] kn1 scs hs HC2 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact Hms |].
  pose (BS2 := [(32%nat, s); (35%nat, psel); (36%nat, sel); (37%nat, dat); (38%nat, row0); (39%nat, row1); (40%nat, row2); (41%nat, row3); (42%nat, row4); (43%nat, row5); (44%nat, row6); (45%nat, row7)]).
  exW_regfactB BS2 HR ex_r10 Q10_2. exW_regfactB BS2 HR ex_r1 Q1_2. exW_regfactB BS2 HR ex_r2 Q2_2. exW_regfactB BS2 HR ex_r4 Q4_2.
  clear BS2.
  lazymatch type of Q2_2 with _ = Z_to_bv 64 (s + ?off) => pose (OFF2 := off) end.
  lazymatch type of Q1_2 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_2 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A2 M2 _ Rc2 (Z_to_bv 64 row2) (Z_to_bv 64 ret) n2 sp' S CK HWs2 Q10_2 Lrow2_a2 F0row2 Q1_2
             ltac:(red; apply bv_eq; reflexivity) Q4_2 Q2_2 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A3 m3 vm3 r3 HW3 CS2 Drow2_3 LEQ2 PMc2 RM2.
  rewrite with_vmmaps_twice in HW3 |- *. rewrite with_vmmaps_vmmaps in RM2.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT2 RM2 ltac:(lia) ltac:(lia)) as RT3. cbn [Z.add] in RT3.
  assert (Lrow3_a3 : live A3 (Z_to_bv 64 row3) = Some n3%Z) by (rewrite (LEQ2 _ (not_eq_sym NE_row2_row3)); exact Lrow3_a2).
  assert (Lrow4_a3 : live A3 (Z_to_bv 64 row4) = Some n4%Z) by (rewrite (LEQ2 _ (not_eq_sym NE_row2_row4)); exact Lrow4_a2).
  assert (Lrow5_a3 : live A3 (Z_to_bv 64 row5) = Some n5%Z) by (rewrite (LEQ2 _ (not_eq_sym NE_row2_row5)); exact Lrow5_a2).
  assert (Lrow6_a3 : live A3 (Z_to_bv 64 row6) = Some n6%Z) by (rewrite (LEQ2 _ (not_eq_sym NE_row2_row6)); exact Lrow6_a2).
  assert (Lrow7_a3 : live A3 (Z_to_bv 64 row7) = Some n7%Z) by (rewrite (LEQ2 _ (not_eq_sym NE_row2_row7)); exact Lrow7_a2).
  assert (Ldat_a3 : live A3 (Z_to_bv 64 dat) = Some 64%Z) by (rewrite (LEQ2 _ NE_dat_row2); exact Ldat_a2).
  assert (Lsel_a3 : live A3 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ2 _ NE_sel_row2); exact Lsel_a2).
  assert (Drow0_3 : live A3 (Z_to_bv 64 row0) = None) by (rewrite (LEQ2 _ NE_row0_row2); exact Drow0_2).
  assert (Drow1_3 : live A3 (Z_to_bv 64 row1) = None) by (rewrite (LEQ2 _ NE_row1_row2); exact Drow1_2).
  assert (SUB2 : sub_live A3 A2).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row2) by (intros ->; rewrite Drow2_3 in Lq; discriminate Lq). rewrite <- (LEQ2 q NEq). exact Lq. }
  assert (PM3 : POSTM C A3 s m0 m3).
  { apply (POSTM_trans C A3 s m0 M2 m3); [apply (POSTM_sub C A3 A2 _ _ _ SUB2); exact (POSTM_trans _ _ _ _ _ _ PM2 PMs2)|].
    apply (POSTM_mono C A3 (s + OFF2) s); [unfold OFF2; lia | exact PMc2]. }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row2 :: [Z_to_bv 64 row1; Z_to_bv 64 row0])) => eq_trans (LEQ2 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL2 q (fun XX => Hq (or_intror XX)))) as LDEL3.
  assert (KEPT2 : Forall (ex_region_kept E2 M2 m3) [(EVar 32, OFF2, 0%Z); (EVar 35, 0%Z, 8%Z); (EVar 36, 0%Z, 32%Z); (EVar 37, 0%Z, 64%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF2 1104 M2 m3 E2 (EVar 32) CK (proj1 PMc2) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (sd_kept_cell C (s + OFF2) psel M2 m3 E2 (EVar 35) CK (proj1 PMc2) ltac:(unfold OFF2; lia) ltac:(unfold OFF2; lia) RP eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A3 A2 M2 _ M2 m3 E2 (EVar 36) sel 32 CK HWs2 Lsel_a2 RRsel eq_refl (proj2 PMc2) Lsel_a3 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A3 A2 M2 _ M2 m3 E2 (EVar 37) dat 64 CK HWs2 Ldat_a2 RRdat eq_refl (proj2 PMc2) Ldat_a3 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E2 M2 m3 _ [] _ HKc2 KEPT2) as HKk2.
  match type of HKk2 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E2 m3 kk') in HKk2 end.
  pose proof (regs_ok_agree 112%nat E2 (ex_envL vals2 r3 [exW_canary SEGS 1410112 m3]) _ _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa2.
  pose proof (exW_regs_call _ _ _ _ _ HRa2 (ex_regs_ok_junk vals2 r3 [exW_canary SEGS 1410112 m3] 112%nat ltac:(vm_cast_no_check (eq_refl 112%nat))) CS2) as HRn3.
  clear HRa2.
  assert (HKa3 : know_ok SEGS (ex_envL vals2 r3 [exW_canary SEGS 1410112 m3]) m3 _) by (exact (know_ok_agree SEGS 112%nat E2 _ m3 _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk2)).
  rewrite (fr_denot_agree 112%nat E2 (ex_envL vals2 r3 [exW_canary SEGS 1410112 m3]) _ fr (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc2 HKk2 KEPT2 HC2 HWs2 PMs2 Q10_2 Q1_2 Q2_2 Q4_2 PM2 HW2 PMc2 CS2 SUB2 RM2 RT2 LEQ2 OFF2 LDEL2 Lrow2_a2 Lrow3_a2 Lrow4_a2 Lrow5_a2 Lrow6_a2 Lrow7_a2 Ldat_a2 Lsel_a2 Drow0_2 Drow1_2.
  subst M2. clear log2. clear E2. try clear Rc2. clear KN2.
  lazymatch type of HRn3 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn3 end.
  pose proof (W_sok_win C A3 m3 _ (s - 1104) (Z.to_nat 1104) CK HW3 GLO1 GLO2) as SOK3.
  pose proof (exW_canary_ok SEGS 1410112 m3 (canary_any m3)) as CANOK3.
  pose (vals3 := vals2 ++ map (getr r3) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m3]).
  pose proof (exW_kn_fixed SEGS C A3 m3 _ (ex_envL vals2 r3 [exW_canary SEGS 1410112 m3]) (EVar 144) (EVar 32) (exW_canary SEGS 1410112 m3) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW3 eq_refl (proj1 CANOK3) (proj2 CANOK3) eq_refl eq_refl eq_refl SOK3 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf3.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf3 HKa3)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn3 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN3 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf3 HKa3 SOK3 CANOK3.
  repeat match goal with H : getr r3 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc3 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E3 := EEx) in HR, Hlf, HK, Hms |- *; set (log3 := LLx) in Hms, Hlf; set (M3 := mem_denot E3 m3 log3) in Hms end.
  assert (WP3 : W C A3 M3 (with_vmmaps vm3 md) /\ POSTM C A3 s m3 M3).
  { subst M3. apply (exW_win C A3 A3 m3 _ E3 log3 (EVar 32) s 1104 CK HW3 (sub_live_refl A3) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi]. }
  destruct WP3 as [HWs3 PMs3].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log3 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC3 : carry log3 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc3 : know_ok SEGS E3 M3 kn1) by (apply (carry_after SEGS E3 m3 log3 kn0 [] kn1 scs hs HC3 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact Hms |].
  pose (BS3 := [(32%nat, s); (35%nat, psel); (36%nat, sel); (37%nat, dat); (38%nat, row0); (39%nat, row1); (40%nat, row2); (41%nat, row3); (42%nat, row4); (43%nat, row5); (44%nat, row6); (45%nat, row7)]).
  exW_regfactB BS3 HR ex_r10 Q10_3. exW_regfactB BS3 HR ex_r1 Q1_3. exW_regfactB BS3 HR ex_r2 Q2_3. exW_regfactB BS3 HR ex_r4 Q4_3.
  clear BS3.
  lazymatch type of Q2_3 with _ = Z_to_bv 64 (s + ?off) => pose (OFF3 := off) end.
  lazymatch type of Q1_3 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_3 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A3 M3 _ Rc3 (Z_to_bv 64 row3) (Z_to_bv 64 ret) n3 sp' S CK HWs3 Q10_3 Lrow3_a3 F0row3 Q1_3
             ltac:(red; apply bv_eq; reflexivity) Q4_3 Q2_3 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A4 m4 vm4 r4 HW4 CS3 Drow3_4 LEQ3 PMc3 RM3.
  rewrite with_vmmaps_twice in HW4 |- *. rewrite with_vmmaps_vmmaps in RM3.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT3 RM3 ltac:(lia) ltac:(lia)) as RT4. cbn [Z.add] in RT4.
  assert (Lrow4_a4 : live A4 (Z_to_bv 64 row4) = Some n4%Z) by (rewrite (LEQ3 _ (not_eq_sym NE_row3_row4)); exact Lrow4_a3).
  assert (Lrow5_a4 : live A4 (Z_to_bv 64 row5) = Some n5%Z) by (rewrite (LEQ3 _ (not_eq_sym NE_row3_row5)); exact Lrow5_a3).
  assert (Lrow6_a4 : live A4 (Z_to_bv 64 row6) = Some n6%Z) by (rewrite (LEQ3 _ (not_eq_sym NE_row3_row6)); exact Lrow6_a3).
  assert (Lrow7_a4 : live A4 (Z_to_bv 64 row7) = Some n7%Z) by (rewrite (LEQ3 _ (not_eq_sym NE_row3_row7)); exact Lrow7_a3).
  assert (Ldat_a4 : live A4 (Z_to_bv 64 dat) = Some 64%Z) by (rewrite (LEQ3 _ NE_dat_row3); exact Ldat_a3).
  assert (Lsel_a4 : live A4 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ3 _ NE_sel_row3); exact Lsel_a3).
  assert (Drow0_4 : live A4 (Z_to_bv 64 row0) = None) by (rewrite (LEQ3 _ NE_row0_row3); exact Drow0_3).
  assert (Drow1_4 : live A4 (Z_to_bv 64 row1) = None) by (rewrite (LEQ3 _ NE_row1_row3); exact Drow1_3).
  assert (Drow2_4 : live A4 (Z_to_bv 64 row2) = None) by (rewrite (LEQ3 _ NE_row2_row3); exact Drow2_3).
  assert (SUB3 : sub_live A4 A3).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row3) by (intros ->; rewrite Drow3_4 in Lq; discriminate Lq). rewrite <- (LEQ3 q NEq). exact Lq. }
  assert (PM4 : POSTM C A4 s m0 m4).
  { apply (POSTM_trans C A4 s m0 M3 m4); [apply (POSTM_sub C A4 A3 _ _ _ SUB3); exact (POSTM_trans _ _ _ _ _ _ PM3 PMs3)|].
    apply (POSTM_mono C A4 (s + OFF3) s); [unfold OFF3; lia | exact PMc3]. }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row3 :: [Z_to_bv 64 row2; Z_to_bv 64 row1; Z_to_bv 64 row0])) => eq_trans (LEQ3 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL3 q (fun XX => Hq (or_intror XX)))) as LDEL4.
  assert (KEPT3 : Forall (ex_region_kept E3 M3 m4) [(EVar 32, OFF3, 0%Z); (EVar 35, 0%Z, 8%Z); (EVar 36, 0%Z, 32%Z); (EVar 37, 0%Z, 64%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF3 1104 M3 m4 E3 (EVar 32) CK (proj1 PMc3) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (sd_kept_cell C (s + OFF3) psel M3 m4 E3 (EVar 35) CK (proj1 PMc3) ltac:(unfold OFF3; lia) ltac:(unfold OFF3; lia) RP eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A4 A3 M3 _ M3 m4 E3 (EVar 36) sel 32 CK HWs3 Lsel_a3 RRsel eq_refl (proj2 PMc3) Lsel_a4 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A4 A3 M3 _ M3 m4 E3 (EVar 37) dat 64 CK HWs3 Ldat_a3 RRdat eq_refl (proj2 PMc3) Ldat_a4 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E3 M3 m4 _ [] _ HKc3 KEPT3) as HKk3.
  match type of HKk3 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E3 m4 kk') in HKk3 end.
  pose proof (regs_ok_agree 145%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 1410112 m4]) _ _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa3.
  pose proof (exW_regs_call _ _ _ _ _ HRa3 (ex_regs_ok_junk vals3 r4 [exW_canary SEGS 1410112 m4] 145%nat ltac:(vm_cast_no_check (eq_refl 145%nat))) CS3) as HRn4.
  clear HRa3.
  assert (HKa4 : know_ok SEGS (ex_envL vals3 r4 [exW_canary SEGS 1410112 m4]) m4 _) by (exact (know_ok_agree SEGS 145%nat E3 _ m4 _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk3)).
  rewrite (fr_denot_agree 145%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 1410112 m4]) _ fr (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc3 HKk3 KEPT3 HC3 HWs3 PMs3 Q10_3 Q1_3 Q2_3 Q4_3 PM3 HW3 PMc3 CS3 SUB3 RM3 RT3 LEQ3 OFF3 LDEL3 Lrow3_a3 Lrow4_a3 Lrow5_a3 Lrow6_a3 Lrow7_a3 Ldat_a3 Lsel_a3 Drow0_3 Drow1_3 Drow2_3.
  subst M3. clear log3. clear E3. try clear Rc3. clear KN3.
  lazymatch type of HRn4 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn4 end.
  pose proof (W_sok_win C A4 m4 _ (s - 1104) (Z.to_nat 1104) CK HW4 GLO1 GLO2) as SOK4.
  pose proof (exW_canary_ok SEGS 1410112 m4 (canary_any m4)) as CANOK4.
  pose (vals4 := vals3 ++ map (getr r4) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m4]).
  pose proof (exW_kn_fixed SEGS C A4 m4 _ (ex_envL vals3 r4 [exW_canary SEGS 1410112 m4]) (EVar 177) (EVar 32) (exW_canary SEGS 1410112 m4) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW4 eq_refl (proj1 CANOK4) (proj2 CANOK4) eq_refl eq_refl eq_refl SOK4 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf4.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf4 HKa4)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn4 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN4 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf4 HKa4 SOK4 CANOK4.
  repeat match goal with H : getr r4 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc4 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E4 := EEx) in HR, Hlf, HK, Hms |- *; set (log4 := LLx) in Hms, Hlf; set (M4 := mem_denot E4 m4 log4) in Hms end.
  assert (WP4 : W C A4 M4 (with_vmmaps vm4 md) /\ POSTM C A4 s m4 M4).
  { subst M4. apply (exW_win C A4 A4 m4 _ E4 log4 (EVar 32) s 1104 CK HW4 (sub_live_refl A4) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi]. }
  destruct WP4 as [HWs4 PMs4].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log4 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC4 : carry log4 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc4 : know_ok SEGS E4 M4 kn1) by (apply (carry_after SEGS E4 m4 log4 kn0 [] kn1 scs hs HC4 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact Hms |].
  pose (BS4 := [(32%nat, s); (35%nat, psel); (36%nat, sel); (37%nat, dat); (38%nat, row0); (39%nat, row1); (40%nat, row2); (41%nat, row3); (42%nat, row4); (43%nat, row5); (44%nat, row6); (45%nat, row7)]).
  exW_regfactB BS4 HR ex_r10 Q10_4. exW_regfactB BS4 HR ex_r1 Q1_4. exW_regfactB BS4 HR ex_r2 Q2_4. exW_regfactB BS4 HR ex_r4 Q4_4.
  clear BS4.
  lazymatch type of Q2_4 with _ = Z_to_bv 64 (s + ?off) => pose (OFF4 := off) end.
  lazymatch type of Q1_4 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_4 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A4 M4 _ Rc4 (Z_to_bv 64 row4) (Z_to_bv 64 ret) n4 sp' S CK HWs4 Q10_4 Lrow4_a4 F0row4 Q1_4
             ltac:(red; apply bv_eq; reflexivity) Q4_4 Q2_4 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A5 m5 vm5 r5 HW5 CS4 Drow4_5 LEQ4 PMc4 RM4.
  rewrite with_vmmaps_twice in HW5 |- *. rewrite with_vmmaps_vmmaps in RM4.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT4 RM4 ltac:(lia) ltac:(lia)) as RT5. cbn [Z.add] in RT5.
  assert (Lrow5_a5 : live A5 (Z_to_bv 64 row5) = Some n5%Z) by (rewrite (LEQ4 _ (not_eq_sym NE_row4_row5)); exact Lrow5_a4).
  assert (Lrow6_a5 : live A5 (Z_to_bv 64 row6) = Some n6%Z) by (rewrite (LEQ4 _ (not_eq_sym NE_row4_row6)); exact Lrow6_a4).
  assert (Lrow7_a5 : live A5 (Z_to_bv 64 row7) = Some n7%Z) by (rewrite (LEQ4 _ (not_eq_sym NE_row4_row7)); exact Lrow7_a4).
  assert (Ldat_a5 : live A5 (Z_to_bv 64 dat) = Some 64%Z) by (rewrite (LEQ4 _ NE_dat_row4); exact Ldat_a4).
  assert (Lsel_a5 : live A5 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ4 _ NE_sel_row4); exact Lsel_a4).
  assert (Drow0_5 : live A5 (Z_to_bv 64 row0) = None) by (rewrite (LEQ4 _ NE_row0_row4); exact Drow0_4).
  assert (Drow1_5 : live A5 (Z_to_bv 64 row1) = None) by (rewrite (LEQ4 _ NE_row1_row4); exact Drow1_4).
  assert (Drow2_5 : live A5 (Z_to_bv 64 row2) = None) by (rewrite (LEQ4 _ NE_row2_row4); exact Drow2_4).
  assert (Drow3_5 : live A5 (Z_to_bv 64 row3) = None) by (rewrite (LEQ4 _ NE_row3_row4); exact Drow3_4).
  assert (SUB4 : sub_live A5 A4).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row4) by (intros ->; rewrite Drow4_5 in Lq; discriminate Lq). rewrite <- (LEQ4 q NEq). exact Lq. }
  assert (PM5 : POSTM C A5 s m0 m5).
  { apply (POSTM_trans C A5 s m0 M4 m5); [apply (POSTM_sub C A5 A4 _ _ _ SUB4); exact (POSTM_trans _ _ _ _ _ _ PM4 PMs4)|].
    apply (POSTM_mono C A5 (s + OFF4) s); [unfold OFF4; lia | exact PMc4]. }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row4 :: [Z_to_bv 64 row3; Z_to_bv 64 row2; Z_to_bv 64 row1; Z_to_bv 64 row0])) => eq_trans (LEQ4 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL4 q (fun XX => Hq (or_intror XX)))) as LDEL5.
  assert (KEPT4 : Forall (ex_region_kept E4 M4 m5) [(EVar 32, OFF4, 0%Z); (EVar 35, 0%Z, 8%Z); (EVar 36, 0%Z, 32%Z); (EVar 37, 0%Z, 64%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF4 1104 M4 m5 E4 (EVar 32) CK (proj1 PMc4) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (sd_kept_cell C (s + OFF4) psel M4 m5 E4 (EVar 35) CK (proj1 PMc4) ltac:(unfold OFF4; lia) ltac:(unfold OFF4; lia) RP eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A5 A4 M4 _ M4 m5 E4 (EVar 36) sel 32 CK HWs4 Lsel_a4 RRsel eq_refl (proj2 PMc4) Lsel_a5 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A5 A4 M4 _ M4 m5 E4 (EVar 37) dat 64 CK HWs4 Ldat_a4 RRdat eq_refl (proj2 PMc4) Ldat_a5 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E4 M4 m5 _ [] _ HKc4 KEPT4) as HKk4.
  match type of HKk4 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E4 m5 kk') in HKk4 end.
  pose proof (regs_ok_agree 178%nat E4 (ex_envL vals4 r5 [exW_canary SEGS 1410112 m5]) _ _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa4.
  pose proof (exW_regs_call _ _ _ _ _ HRa4 (ex_regs_ok_junk vals4 r5 [exW_canary SEGS 1410112 m5] 178%nat ltac:(vm_cast_no_check (eq_refl 178%nat))) CS4) as HRn5.
  clear HRa4.
  assert (HKa5 : know_ok SEGS (ex_envL vals4 r5 [exW_canary SEGS 1410112 m5]) m5 _) by (exact (know_ok_agree SEGS 178%nat E4 _ m5 _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk4)).
  rewrite (fr_denot_agree 178%nat E4 (ex_envL vals4 r5 [exW_canary SEGS 1410112 m5]) _ fr (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc4 HKk4 KEPT4 HC4 HWs4 PMs4 Q10_4 Q1_4 Q2_4 Q4_4 PM4 HW4 PMc4 CS4 SUB4 RM4 RT4 LEQ4 OFF4 LDEL4 Lrow4_a4 Lrow5_a4 Lrow6_a4 Lrow7_a4 Ldat_a4 Lsel_a4 Drow0_4 Drow1_4 Drow2_4 Drow3_4.
  subst M4. clear log4. clear E4. try clear Rc4. clear KN4.
  lazymatch type of HRn5 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn5 end.
  pose proof (W_sok_win C A5 m5 _ (s - 1104) (Z.to_nat 1104) CK HW5 GLO1 GLO2) as SOK5.
  pose proof (exW_canary_ok SEGS 1410112 m5 (canary_any m5)) as CANOK5.
  pose (vals5 := vals4 ++ map (getr r5) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m5]).
  pose proof (exW_kn_fixed SEGS C A5 m5 _ (ex_envL vals4 r5 [exW_canary SEGS 1410112 m5]) (EVar 210) (EVar 32) (exW_canary SEGS 1410112 m5) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW5 eq_refl (proj1 CANOK5) (proj2 CANOK5) eq_refl eq_refl eq_refl SOK5 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf5.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf5 HKa5)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn5 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN5 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf5 HKa5 SOK5 CANOK5.
  repeat match goal with H : getr r5 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc5 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E5 := EEx) in HR, Hlf, HK, Hms |- *; set (log5 := LLx) in Hms, Hlf; set (M5 := mem_denot E5 m5 log5) in Hms end.
  assert (WP5 : W C A5 M5 (with_vmmaps vm5 md) /\ POSTM C A5 s m5 M5).
  { subst M5. apply (exW_win C A5 A5 m5 _ E5 log5 (EVar 32) s 1104 CK HW5 (sub_live_refl A5) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi]. }
  destruct WP5 as [HWs5 PMs5].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log5 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC5 : carry log5 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc5 : know_ok SEGS E5 M5 kn1) by (apply (carry_after SEGS E5 m5 log5 kn0 [] kn1 scs hs HC5 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact Hms |].
  pose (BS5 := [(32%nat, s); (35%nat, psel); (36%nat, sel); (37%nat, dat); (38%nat, row0); (39%nat, row1); (40%nat, row2); (41%nat, row3); (42%nat, row4); (43%nat, row5); (44%nat, row6); (45%nat, row7)]).
  exW_regfactB BS5 HR ex_r10 Q10_5. exW_regfactB BS5 HR ex_r1 Q1_5. exW_regfactB BS5 HR ex_r2 Q2_5. exW_regfactB BS5 HR ex_r4 Q4_5.
  clear BS5.
  lazymatch type of Q2_5 with _ = Z_to_bv 64 (s + ?off) => pose (OFF5 := off) end.
  lazymatch type of Q1_5 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_5 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A5 M5 _ Rc5 (Z_to_bv 64 row5) (Z_to_bv 64 ret) n5 sp' S CK HWs5 Q10_5 Lrow5_a5 F0row5 Q1_5
             ltac:(red; apply bv_eq; reflexivity) Q4_5 Q2_5 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A6 m6 vm6 r6 HW6 CS5 Drow5_6 LEQ5 PMc5 RM5.
  rewrite with_vmmaps_twice in HW6 |- *. rewrite with_vmmaps_vmmaps in RM5.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT5 RM5 ltac:(lia) ltac:(lia)) as RT6. cbn [Z.add] in RT6.
  assert (Lrow6_a6 : live A6 (Z_to_bv 64 row6) = Some n6%Z) by (rewrite (LEQ5 _ (not_eq_sym NE_row5_row6)); exact Lrow6_a5).
  assert (Lrow7_a6 : live A6 (Z_to_bv 64 row7) = Some n7%Z) by (rewrite (LEQ5 _ (not_eq_sym NE_row5_row7)); exact Lrow7_a5).
  assert (Ldat_a6 : live A6 (Z_to_bv 64 dat) = Some 64%Z) by (rewrite (LEQ5 _ NE_dat_row5); exact Ldat_a5).
  assert (Lsel_a6 : live A6 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ5 _ NE_sel_row5); exact Lsel_a5).
  assert (Drow0_6 : live A6 (Z_to_bv 64 row0) = None) by (rewrite (LEQ5 _ NE_row0_row5); exact Drow0_5).
  assert (Drow1_6 : live A6 (Z_to_bv 64 row1) = None) by (rewrite (LEQ5 _ NE_row1_row5); exact Drow1_5).
  assert (Drow2_6 : live A6 (Z_to_bv 64 row2) = None) by (rewrite (LEQ5 _ NE_row2_row5); exact Drow2_5).
  assert (Drow3_6 : live A6 (Z_to_bv 64 row3) = None) by (rewrite (LEQ5 _ NE_row3_row5); exact Drow3_5).
  assert (Drow4_6 : live A6 (Z_to_bv 64 row4) = None) by (rewrite (LEQ5 _ NE_row4_row5); exact Drow4_5).
  assert (SUB5 : sub_live A6 A5).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row5) by (intros ->; rewrite Drow5_6 in Lq; discriminate Lq). rewrite <- (LEQ5 q NEq). exact Lq. }
  assert (PM6 : POSTM C A6 s m0 m6).
  { apply (POSTM_trans C A6 s m0 M5 m6); [apply (POSTM_sub C A6 A5 _ _ _ SUB5); exact (POSTM_trans _ _ _ _ _ _ PM5 PMs5)|].
    apply (POSTM_mono C A6 (s + OFF5) s); [unfold OFF5; lia | exact PMc5]. }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row5 :: [Z_to_bv 64 row4; Z_to_bv 64 row3; Z_to_bv 64 row2; Z_to_bv 64 row1; Z_to_bv 64 row0])) => eq_trans (LEQ5 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL5 q (fun XX => Hq (or_intror XX)))) as LDEL6.
  assert (KEPT5 : Forall (ex_region_kept E5 M5 m6) [(EVar 32, OFF5, 0%Z); (EVar 35, 0%Z, 8%Z); (EVar 36, 0%Z, 32%Z); (EVar 37, 0%Z, 64%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF5 1104 M5 m6 E5 (EVar 32) CK (proj1 PMc5) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (sd_kept_cell C (s + OFF5) psel M5 m6 E5 (EVar 35) CK (proj1 PMc5) ltac:(unfold OFF5; lia) ltac:(unfold OFF5; lia) RP eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A6 A5 M5 _ M5 m6 E5 (EVar 36) sel 32 CK HWs5 Lsel_a5 RRsel eq_refl (proj2 PMc5) Lsel_a6 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A6 A5 M5 _ M5 m6 E5 (EVar 37) dat 64 CK HWs5 Ldat_a5 RRdat eq_refl (proj2 PMc5) Ldat_a6 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E5 M5 m6 _ [] _ HKc5 KEPT5) as HKk5.
  match type of HKk5 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E5 m6 kk') in HKk5 end.
  pose proof (regs_ok_agree 211%nat E5 (ex_envL vals5 r6 [exW_canary SEGS 1410112 m6]) _ _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa5.
  pose proof (exW_regs_call _ _ _ _ _ HRa5 (ex_regs_ok_junk vals5 r6 [exW_canary SEGS 1410112 m6] 211%nat ltac:(vm_cast_no_check (eq_refl 211%nat))) CS5) as HRn6.
  clear HRa5.
  assert (HKa6 : know_ok SEGS (ex_envL vals5 r6 [exW_canary SEGS 1410112 m6]) m6 _) by (exact (know_ok_agree SEGS 211%nat E5 _ m6 _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk5)).
  rewrite (fr_denot_agree 211%nat E5 (ex_envL vals5 r6 [exW_canary SEGS 1410112 m6]) _ fr (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc5 HKk5 KEPT5 HC5 HWs5 PMs5 Q10_5 Q1_5 Q2_5 Q4_5 PM5 HW5 PMc5 CS5 SUB5 RM5 RT5 LEQ5 OFF5 LDEL5 Lrow5_a5 Lrow6_a5 Lrow7_a5 Ldat_a5 Lsel_a5 Drow0_5 Drow1_5 Drow2_5 Drow3_5 Drow4_5.
  subst M5. clear log5. clear E5. try clear Rc5. clear KN5.
  lazymatch type of HRn6 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn6 end.
  pose proof (W_sok_win C A6 m6 _ (s - 1104) (Z.to_nat 1104) CK HW6 GLO1 GLO2) as SOK6.
  pose proof (exW_canary_ok SEGS 1410112 m6 (canary_any m6)) as CANOK6.
  pose (vals6 := vals5 ++ map (getr r6) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m6]).
  pose proof (exW_kn_fixed SEGS C A6 m6 _ (ex_envL vals5 r6 [exW_canary SEGS 1410112 m6]) (EVar 243) (EVar 32) (exW_canary SEGS 1410112 m6) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW6 eq_refl (proj1 CANOK6) (proj2 CANOK6) eq_refl eq_refl eq_refl SOK6 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf6.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf6 HKa6)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn6 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN6 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf6 HKa6 SOK6 CANOK6.
  repeat match goal with H : getr r6 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc6 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E6 := EEx) in HR, Hlf, HK, Hms |- *; set (log6 := LLx) in Hms, Hlf; set (M6 := mem_denot E6 m6 log6) in Hms end.
  assert (WP6 : W C A6 M6 (with_vmmaps vm6 md) /\ POSTM C A6 s m6 M6).
  { subst M6. apply (exW_win C A6 A6 m6 _ E6 log6 (EVar 32) s 1104 CK HW6 (sub_live_refl A6) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi]. }
  destruct WP6 as [HWs6 PMs6].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log6 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC6 : carry log6 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc6 : know_ok SEGS E6 M6 kn1) by (apply (carry_after SEGS E6 m6 log6 kn0 [] kn1 scs hs HC6 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact Hms |].
  pose (BS6 := [(32%nat, s); (35%nat, psel); (36%nat, sel); (37%nat, dat); (38%nat, row0); (39%nat, row1); (40%nat, row2); (41%nat, row3); (42%nat, row4); (43%nat, row5); (44%nat, row6); (45%nat, row7)]).
  exW_regfactB BS6 HR ex_r10 Q10_6. exW_regfactB BS6 HR ex_r1 Q1_6. exW_regfactB BS6 HR ex_r2 Q2_6. exW_regfactB BS6 HR ex_r4 Q4_6.
  clear BS6.
  lazymatch type of Q2_6 with _ = Z_to_bv 64 (s + ?off) => pose (OFF6 := off) end.
  lazymatch type of Q1_6 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_6 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A6 M6 _ Rc6 (Z_to_bv 64 row6) (Z_to_bv 64 ret) n6 sp' S CK HWs6 Q10_6 Lrow6_a6 F0row6 Q1_6
             ltac:(red; apply bv_eq; reflexivity) Q4_6 Q2_6 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A7 m7 vm7 r7 HW7 CS6 Drow6_7 LEQ6 PMc6 RM6.
  rewrite with_vmmaps_twice in HW7 |- *. rewrite with_vmmaps_vmmaps in RM6.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT6 RM6 ltac:(lia) ltac:(lia)) as RT7. cbn [Z.add] in RT7.
  assert (Lrow7_a7 : live A7 (Z_to_bv 64 row7) = Some n7%Z) by (rewrite (LEQ6 _ (not_eq_sym NE_row6_row7)); exact Lrow7_a6).
  assert (Ldat_a7 : live A7 (Z_to_bv 64 dat) = Some 64%Z) by (rewrite (LEQ6 _ NE_dat_row6); exact Ldat_a6).
  assert (Lsel_a7 : live A7 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ6 _ NE_sel_row6); exact Lsel_a6).
  assert (Drow0_7 : live A7 (Z_to_bv 64 row0) = None) by (rewrite (LEQ6 _ NE_row0_row6); exact Drow0_6).
  assert (Drow1_7 : live A7 (Z_to_bv 64 row1) = None) by (rewrite (LEQ6 _ NE_row1_row6); exact Drow1_6).
  assert (Drow2_7 : live A7 (Z_to_bv 64 row2) = None) by (rewrite (LEQ6 _ NE_row2_row6); exact Drow2_6).
  assert (Drow3_7 : live A7 (Z_to_bv 64 row3) = None) by (rewrite (LEQ6 _ NE_row3_row6); exact Drow3_6).
  assert (Drow4_7 : live A7 (Z_to_bv 64 row4) = None) by (rewrite (LEQ6 _ NE_row4_row6); exact Drow4_6).
  assert (Drow5_7 : live A7 (Z_to_bv 64 row5) = None) by (rewrite (LEQ6 _ NE_row5_row6); exact Drow5_6).
  assert (SUB6 : sub_live A7 A6).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row6) by (intros ->; rewrite Drow6_7 in Lq; discriminate Lq). rewrite <- (LEQ6 q NEq). exact Lq. }
  assert (PM7 : POSTM C A7 s m0 m7).
  { apply (POSTM_trans C A7 s m0 M6 m7); [apply (POSTM_sub C A7 A6 _ _ _ SUB6); exact (POSTM_trans _ _ _ _ _ _ PM6 PMs6)|].
    apply (POSTM_mono C A7 (s + OFF6) s); [unfold OFF6; lia | exact PMc6]. }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row6 :: [Z_to_bv 64 row5; Z_to_bv 64 row4; Z_to_bv 64 row3; Z_to_bv 64 row2; Z_to_bv 64 row1; Z_to_bv 64 row0])) => eq_trans (LEQ6 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL6 q (fun XX => Hq (or_intror XX)))) as LDEL7.
  assert (KEPT6 : Forall (ex_region_kept E6 M6 m7) [(EVar 32, OFF6, 0%Z); (EVar 35, 0%Z, 8%Z); (EVar 36, 0%Z, 32%Z); (EVar 37, 0%Z, 64%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF6 1104 M6 m7 E6 (EVar 32) CK (proj1 PMc6) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (sd_kept_cell C (s + OFF6) psel M6 m7 E6 (EVar 35) CK (proj1 PMc6) ltac:(unfold OFF6; lia) ltac:(unfold OFF6; lia) RP eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A7 A6 M6 _ M6 m7 E6 (EVar 36) sel 32 CK HWs6 Lsel_a6 RRsel eq_refl (proj2 PMc6) Lsel_a7 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A7 A6 M6 _ M6 m7 E6 (EVar 37) dat 64 CK HWs6 Ldat_a6 RRdat eq_refl (proj2 PMc6) Ldat_a7 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E6 M6 m7 _ [] _ HKc6 KEPT6) as HKk6.
  match type of HKk6 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E6 m7 kk') in HKk6 end.
  pose proof (regs_ok_agree 244%nat E6 (ex_envL vals6 r7 [exW_canary SEGS 1410112 m7]) _ _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa6.
  pose proof (exW_regs_call _ _ _ _ _ HRa6 (ex_regs_ok_junk vals6 r7 [exW_canary SEGS 1410112 m7] 244%nat ltac:(vm_cast_no_check (eq_refl 244%nat))) CS6) as HRn7.
  clear HRa6.
  assert (HKa7 : know_ok SEGS (ex_envL vals6 r7 [exW_canary SEGS 1410112 m7]) m7 _) by (exact (know_ok_agree SEGS 244%nat E6 _ m7 _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk6)).
  rewrite (fr_denot_agree 244%nat E6 (ex_envL vals6 r7 [exW_canary SEGS 1410112 m7]) _ fr (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc6 HKk6 KEPT6 HC6 HWs6 PMs6 Q10_6 Q1_6 Q2_6 Q4_6 PM6 HW6 PMc6 CS6 SUB6 RM6 RT6 LEQ6 OFF6 LDEL6 Lrow6_a6 Lrow7_a6 Ldat_a6 Lsel_a6 Drow0_6 Drow1_6 Drow2_6 Drow3_6 Drow4_6 Drow5_6.
  subst M6. clear log6. clear E6. try clear Rc6. clear KN6.
  lazymatch type of HRn7 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn7 end.
  pose proof (W_sok_win C A7 m7 _ (s - 1104) (Z.to_nat 1104) CK HW7 GLO1 GLO2) as SOK7.
  pose proof (exW_canary_ok SEGS 1410112 m7 (canary_any m7)) as CANOK7.
  pose (vals7 := vals6 ++ map (getr r7) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m7]).
  pose proof (exW_kn_fixed SEGS C A7 m7 _ (ex_envL vals6 r7 [exW_canary SEGS 1410112 m7]) (EVar 276) (EVar 32) (exW_canary SEGS 1410112 m7) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW7 eq_refl (proj1 CANOK7) (proj2 CANOK7) eq_refl eq_refl eq_refl SOK7 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf7.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf7 HKa7)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn7 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN7 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf7 HKa7 SOK7 CANOK7.
  repeat match goal with H : getr r7 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc7 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E7 := EEx) in HR, Hlf, HK, Hms |- *; set (log7 := LLx) in Hms, Hlf; set (M7 := mem_denot E7 m7 log7) in Hms end.
  assert (WP7 : W C A7 M7 (with_vmmaps vm7 md) /\ POSTM C A7 s m7 M7).
  { subst M7. apply (exW_win C A7 A7 m7 _ E7 log7 (EVar 32) s 1104 CK HW7 (sub_live_refl A7) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi]. }
  destruct WP7 as [HWs7 PMs7].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log7 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC7 : carry log7 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc7 : know_ok SEGS E7 M7 kn1) by (apply (carry_after SEGS E7 m7 log7 kn0 [] kn1 scs hs HC7 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact Hms |].
  pose (BS7 := [(32%nat, s); (35%nat, psel); (36%nat, sel); (37%nat, dat); (38%nat, row0); (39%nat, row1); (40%nat, row2); (41%nat, row3); (42%nat, row4); (43%nat, row5); (44%nat, row6); (45%nat, row7)]).
  exW_regfactB BS7 HR ex_r10 Q10_7. exW_regfactB BS7 HR ex_r1 Q1_7. exW_regfactB BS7 HR ex_r2 Q2_7. exW_regfactB BS7 HR ex_r4 Q4_7.
  clear BS7.
  lazymatch type of Q2_7 with _ = Z_to_bv 64 (s + ?off) => pose (OFF7 := off) end.
  lazymatch type of Q1_7 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_7 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A7 M7 _ Rc7 (Z_to_bv 64 row7) (Z_to_bv 64 ret) n7 sp' S CK HWs7 Q10_7 Lrow7_a7 F0row7 Q1_7
             ltac:(red; apply bv_eq; reflexivity) Q4_7 Q2_7 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A8 m8 vm8 r8 HW8 CS7 Drow7_8 LEQ7 PMc7 RM7.
  rewrite with_vmmaps_twice in HW8 |- *. rewrite with_vmmaps_vmmaps in RM7.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT7 RM7 ltac:(lia) ltac:(lia)) as RT8. cbn [Z.add] in RT8.
  assert (Ldat_a8 : live A8 (Z_to_bv 64 dat) = Some 64%Z) by (rewrite (LEQ7 _ NE_dat_row7); exact Ldat_a7).
  assert (Lsel_a8 : live A8 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ7 _ NE_sel_row7); exact Lsel_a7).
  assert (Drow0_8 : live A8 (Z_to_bv 64 row0) = None) by (rewrite (LEQ7 _ NE_row0_row7); exact Drow0_7).
  assert (Drow1_8 : live A8 (Z_to_bv 64 row1) = None) by (rewrite (LEQ7 _ NE_row1_row7); exact Drow1_7).
  assert (Drow2_8 : live A8 (Z_to_bv 64 row2) = None) by (rewrite (LEQ7 _ NE_row2_row7); exact Drow2_7).
  assert (Drow3_8 : live A8 (Z_to_bv 64 row3) = None) by (rewrite (LEQ7 _ NE_row3_row7); exact Drow3_7).
  assert (Drow4_8 : live A8 (Z_to_bv 64 row4) = None) by (rewrite (LEQ7 _ NE_row4_row7); exact Drow4_7).
  assert (Drow5_8 : live A8 (Z_to_bv 64 row5) = None) by (rewrite (LEQ7 _ NE_row5_row7); exact Drow5_7).
  assert (Drow6_8 : live A8 (Z_to_bv 64 row6) = None) by (rewrite (LEQ7 _ NE_row6_row7); exact Drow6_7).
  assert (SUB7 : sub_live A8 A7).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row7) by (intros ->; rewrite Drow7_8 in Lq; discriminate Lq). rewrite <- (LEQ7 q NEq). exact Lq. }
  assert (PM8 : POSTM C A8 s m0 m8).
  { apply (POSTM_trans C A8 s m0 M7 m8); [apply (POSTM_sub C A8 A7 _ _ _ SUB7); exact (POSTM_trans _ _ _ _ _ _ PM7 PMs7)|].
    apply (POSTM_mono C A8 (s + OFF7) s); [unfold OFF7; lia | exact PMc7]. }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row7 :: [Z_to_bv 64 row6; Z_to_bv 64 row5; Z_to_bv 64 row4; Z_to_bv 64 row3; Z_to_bv 64 row2; Z_to_bv 64 row1; Z_to_bv 64 row0])) => eq_trans (LEQ7 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL7 q (fun XX => Hq (or_intror XX)))) as LDEL8.
  assert (KEPT7 : Forall (ex_region_kept E7 M7 m8) [(EVar 32, OFF7, 0%Z); (EVar 35, 0%Z, 8%Z); (EVar 36, 0%Z, 32%Z); (EVar 37, 0%Z, 64%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF7 1104 M7 m8 E7 (EVar 32) CK (proj1 PMc7) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (sd_kept_cell C (s + OFF7) psel M7 m8 E7 (EVar 35) CK (proj1 PMc7) ltac:(unfold OFF7; lia) ltac:(unfold OFF7; lia) RP eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A8 A7 M7 _ M7 m8 E7 (EVar 36) sel 32 CK HWs7 Lsel_a7 RRsel eq_refl (proj2 PMc7) Lsel_a8 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A8 A7 M7 _ M7 m8 E7 (EVar 37) dat 64 CK HWs7 Ldat_a7 RRdat eq_refl (proj2 PMc7) Ldat_a8 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E7 M7 m8 _ [] _ HKc7 KEPT7) as HKk7.
  match type of HKk7 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E7 m8 kk') in HKk7 end.
  pose proof (regs_ok_agree 277%nat E7 (ex_envL vals7 r8 [exW_canary SEGS 1410112 m8]) _ _ (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa7.
  pose proof (exW_regs_call _ _ _ _ _ HRa7 (ex_regs_ok_junk vals7 r8 [exW_canary SEGS 1410112 m8] 277%nat ltac:(vm_cast_no_check (eq_refl 277%nat))) CS7) as HRn8.
  clear HRa7.
  assert (HKa8 : know_ok SEGS (ex_envL vals7 r8 [exW_canary SEGS 1410112 m8]) m8 _) by (exact (know_ok_agree SEGS 277%nat E7 _ m8 _ (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk7)).
  rewrite (fr_denot_agree 277%nat E7 (ex_envL vals7 r8 [exW_canary SEGS 1410112 m8]) _ fr (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc7 HKk7 KEPT7 HC7 HWs7 PMs7 Q10_7 Q1_7 Q2_7 Q4_7 PM7 HW7 PMc7 CS7 SUB7 RM7 RT7 LEQ7 OFF7 LDEL7 Lrow7_a7 Ldat_a7 Lsel_a7 Drow0_7 Drow1_7 Drow2_7 Drow3_7 Drow4_7 Drow5_7 Drow6_7.
  subst M7. clear log7. clear E7. try clear Rc7. clear KN7.
  lazymatch type of HRn8 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn8 end.
  pose proof (W_sok_win C A8 m8 _ (s - 1104) (Z.to_nat 1104) CK HW8 GLO1 GLO2) as SOK8.
  pose proof (exW_canary_ok SEGS 1410112 m8 (canary_any m8)) as CANOK8.
  pose (vals8 := vals7 ++ map (getr r8) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m8]).
  pose proof (exW_kn_fixed SEGS C A8 m8 _ (ex_envL vals7 r8 [exW_canary SEGS 1410112 m8]) (EVar 309) (EVar 32) (exW_canary SEGS 1410112 m8) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW8 eq_refl (proj1 CANOK8) (proj2 CANOK8) eq_refl eq_refl eq_refl SOK8 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf8.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf8 HKa8)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn8 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN8 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf8 HKa8 SOK8 CANOK8.
  repeat match goal with H : getr r8 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc8 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E8 := EEx) in HR, Hlf, HK, Hms |- *; set (log8 := LLx) in Hms, Hlf; set (M8 := mem_denot E8 m8 log8) in Hms end.
  assert (WP8 : W C A8 M8 (with_vmmaps vm8 md) /\ POSTM C A8 s m8 M8).
  { subst M8. apply (exW_win C A8 A8 m8 _ E8 log8 (EVar 32) s 1104 CK HW8 (sub_live_refl A8) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi]. }
  destruct WP8 as [HWs8 PMs8].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log8 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC8 : carry log8 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc8 : know_ok SEGS E8 M8 kn1) by (apply (carry_after SEGS E8 m8 log8 kn0 [] kn1 scs hs HC8 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW8)) | exact (mp_lazy _ (w_pure _ _ _ _ HW8)) | exact Hms |].
  pose (BS8 := [(32%nat, s); (35%nat, psel); (36%nat, sel); (37%nat, dat); (38%nat, row0); (39%nat, row1); (40%nat, row2); (41%nat, row3); (42%nat, row4); (43%nat, row5); (44%nat, row6); (45%nat, row7)]).
  exW_regfactB BS8 HR ex_r10 Q10_8. exW_regfactB BS8 HR ex_r1 Q1_8. exW_regfactB BS8 HR ex_r2 Q2_8. exW_regfactB BS8 HR ex_r4 Q4_8.
  clear BS8.
  lazymatch type of Q2_8 with _ = Z_to_bv 64 (s + ?off) => pose (OFF8 := off) end.
  lazymatch type of Q1_8 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_8 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A8 M8 _ Rc8 (Z_to_bv 64 dat) (Z_to_bv 64 ret) 64 sp' S CK HWs8 Q10_8 Ldat_a8 F0dat Q1_8
             ltac:(red; apply bv_eq; reflexivity) Q4_8 Q2_8 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A9 m9 vm9 r9 HW9 CS8 Ddat_9 LEQ8 PMc8 RM8.
  rewrite with_vmmaps_twice in HW9 |- *. rewrite with_vmmaps_vmmaps in RM8.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT8 RM8 ltac:(lia) ltac:(lia)) as RT9. cbn [Z.add] in RT9.
  assert (Lsel_a9 : live A9 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ8 _ NE_sel_dat); exact Lsel_a8).
  assert (Drow0_9 : live A9 (Z_to_bv 64 row0) = None) by (rewrite (LEQ8 _ (not_eq_sym NE_dat_row0)); exact Drow0_8).
  assert (Drow1_9 : live A9 (Z_to_bv 64 row1) = None) by (rewrite (LEQ8 _ (not_eq_sym NE_dat_row1)); exact Drow1_8).
  assert (Drow2_9 : live A9 (Z_to_bv 64 row2) = None) by (rewrite (LEQ8 _ (not_eq_sym NE_dat_row2)); exact Drow2_8).
  assert (Drow3_9 : live A9 (Z_to_bv 64 row3) = None) by (rewrite (LEQ8 _ (not_eq_sym NE_dat_row3)); exact Drow3_8).
  assert (Drow4_9 : live A9 (Z_to_bv 64 row4) = None) by (rewrite (LEQ8 _ (not_eq_sym NE_dat_row4)); exact Drow4_8).
  assert (Drow5_9 : live A9 (Z_to_bv 64 row5) = None) by (rewrite (LEQ8 _ (not_eq_sym NE_dat_row5)); exact Drow5_8).
  assert (Drow6_9 : live A9 (Z_to_bv 64 row6) = None) by (rewrite (LEQ8 _ (not_eq_sym NE_dat_row6)); exact Drow6_8).
  assert (Drow7_9 : live A9 (Z_to_bv 64 row7) = None) by (rewrite (LEQ8 _ (not_eq_sym NE_dat_row7)); exact Drow7_8).
  assert (SUB8 : sub_live A9 A8).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 dat) by (intros ->; rewrite Ddat_9 in Lq; discriminate Lq). rewrite <- (LEQ8 q NEq). exact Lq. }
  assert (PM9 : POSTM C A9 s m0 m9).
  { apply (POSTM_trans C A9 s m0 M8 m9); [apply (POSTM_sub C A9 A8 _ _ _ SUB8); exact (POSTM_trans _ _ _ _ _ _ PM8 PMs8)|].
    apply (POSTM_mono C A9 (s + OFF8) s); [unfold OFF8; lia | exact PMc8]. }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 dat :: [Z_to_bv 64 row7; Z_to_bv 64 row6; Z_to_bv 64 row5; Z_to_bv 64 row4; Z_to_bv 64 row3; Z_to_bv 64 row2; Z_to_bv 64 row1; Z_to_bv 64 row0])) => eq_trans (LEQ8 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL8 q (fun XX => Hq (or_intror XX)))) as LDEL9.
  assert (KEPT8 : Forall (ex_region_kept E8 M8 m9) [(EVar 32, OFF8, 0%Z); (EVar 35, 0%Z, 8%Z); (EVar 36, 0%Z, 32%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF8 1104 M8 m9 E8 (EVar 32) CK (proj1 PMc8) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (sd_kept_cell C (s + OFF8) psel M8 m9 E8 (EVar 35) CK (proj1 PMc8) ltac:(unfold OFF8; lia) ltac:(unfold OFF8; lia) RP eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A9 A8 M8 _ M8 m9 E8 (EVar 36) sel 32 CK HWs8 Lsel_a8 RRsel eq_refl (proj2 PMc8) Lsel_a9 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E8 M8 m9 _ [] _ HKc8 KEPT8) as HKk8.
  match type of HKk8 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E8 m9 kk') in HKk8 end.
  pose proof (regs_ok_agree 310%nat E8 (ex_envL vals8 r9 [exW_canary SEGS 1410112 m9]) _ _ (vals_app_agree vals8 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa8.
  pose proof (exW_regs_call _ _ _ _ _ HRa8 (ex_regs_ok_junk vals8 r9 [exW_canary SEGS 1410112 m9] 310%nat ltac:(vm_cast_no_check (eq_refl 310%nat))) CS8) as HRn9.
  clear HRa8.
  assert (HKa9 : know_ok SEGS (ex_envL vals8 r9 [exW_canary SEGS 1410112 m9]) m9 _) by (exact (know_ok_agree SEGS 310%nat E8 _ m9 _ (vals_app_agree vals8 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk8)).
  rewrite (fr_denot_agree 310%nat E8 (ex_envL vals8 r9 [exW_canary SEGS 1410112 m9]) _ fr (vals_app_agree vals8 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc8 HKk8 KEPT8 HC8 HWs8 PMs8 Q10_8 Q1_8 Q2_8 Q4_8 PM8 HW8 PMc8 CS8 SUB8 RM8 RT8 LEQ8 OFF8 LDEL8 Ldat_a8 Lsel_a8 Drow0_8 Drow1_8 Drow2_8 Drow3_8 Drow4_8 Drow5_8 Drow6_8 Drow7_8.
  subst M8. clear log8. clear E8. try clear Rc8. clear KN8.
  lazymatch type of HRn9 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn9 end.
  pose proof (W_sok_win C A9 m9 _ (s - 1104) (Z.to_nat 1104) CK HW9 GLO1 GLO2) as SOK9.
  pose proof (exW_canary_ok SEGS 1410112 m9 (canary_any m9)) as CANOK9.
  pose (vals9 := vals8 ++ map (getr r9) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m9]).
  pose proof (exW_kn_fixed SEGS C A9 m9 _ (ex_envL vals8 r9 [exW_canary SEGS 1410112 m9]) (EVar 342) (EVar 32) (exW_canary SEGS 1410112 m9) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW9 eq_refl (proj1 CANOK9) (proj2 CANOK9) eq_refl eq_refl eq_refl SOK9 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf9.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf9 HKa9)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn9 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN9 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf9 HKa9 SOK9 CANOK9.
  repeat match goal with H : getr r9 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc9 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E9 := EEx) in HR, Hlf, HK, Hms |- *; set (log9 := LLx) in Hms, Hlf; set (M9 := mem_denot E9 m9 log9) in Hms end.
  assert (WP9 : W C A9 M9 (with_vmmaps vm9 md) /\ POSTM C A9 s m9 M9).
  { subst M9. apply (exW_win C A9 A9 m9 _ E9 log9 (EVar 32) s 1104 CK HW9 (sub_live_refl A9) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi]. }
  destruct WP9 as [HWs9 PMs9].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log9 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC9 : carry log9 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc9 : know_ok SEGS E9 M9 kn1) by (apply (carry_after SEGS E9 m9 log9 kn0 [] kn1 scs hs HC9 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW9)) | exact (mp_lazy _ (w_pure _ _ _ _ HW9)) | exact Hms |].
  pose (BS9 := [(32%nat, s); (35%nat, psel); (36%nat, sel); (37%nat, dat); (38%nat, row0); (39%nat, row1); (40%nat, row2); (41%nat, row3); (42%nat, row4); (43%nat, row5); (44%nat, row6); (45%nat, row7)]).
  exW_regfactB BS9 HR ex_r10 Q10_9. exW_regfactB BS9 HR ex_r1 Q1_9. exW_regfactB BS9 HR ex_r2 Q2_9. exW_regfactB BS9 HR ex_r4 Q4_9.
  clear BS9.
  lazymatch type of Q2_9 with _ = Z_to_bv 64 (s + ?off) => pose (OFF9 := off) end.
  lazymatch type of Q1_9 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_9 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A9 M9 _ Rc9 (Z_to_bv 64 sel) (Z_to_bv 64 ret) 32 sp' S CK HWs9 Q10_9 Lsel_a9 F0sel Q1_9
             ltac:(red; apply bv_eq; reflexivity) Q4_9 Q2_9 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A10 m10 vm10 r10 HW10 CS9 Dsel_10 LEQ9 PMc9 RM9.
  rewrite with_vmmaps_twice in HW10 |- *. rewrite with_vmmaps_vmmaps in RM9.
  pose proof (roomtr_trans _ _ _ _ _ _ 0 0 0 0 RT9 RM9 ltac:(lia) ltac:(lia)) as RT10. cbn [Z.add] in RT10.
  assert (Drow0_10 : live A10 (Z_to_bv 64 row0) = None) by (rewrite (LEQ9 _ (not_eq_sym NE_sel_row0)); exact Drow0_9).
  assert (Drow1_10 : live A10 (Z_to_bv 64 row1) = None) by (rewrite (LEQ9 _ (not_eq_sym NE_sel_row1)); exact Drow1_9).
  assert (Drow2_10 : live A10 (Z_to_bv 64 row2) = None) by (rewrite (LEQ9 _ (not_eq_sym NE_sel_row2)); exact Drow2_9).
  assert (Drow3_10 : live A10 (Z_to_bv 64 row3) = None) by (rewrite (LEQ9 _ (not_eq_sym NE_sel_row3)); exact Drow3_9).
  assert (Drow4_10 : live A10 (Z_to_bv 64 row4) = None) by (rewrite (LEQ9 _ (not_eq_sym NE_sel_row4)); exact Drow4_9).
  assert (Drow5_10 : live A10 (Z_to_bv 64 row5) = None) by (rewrite (LEQ9 _ (not_eq_sym NE_sel_row5)); exact Drow5_9).
  assert (Drow6_10 : live A10 (Z_to_bv 64 row6) = None) by (rewrite (LEQ9 _ (not_eq_sym NE_sel_row6)); exact Drow6_9).
  assert (Drow7_10 : live A10 (Z_to_bv 64 row7) = None) by (rewrite (LEQ9 _ (not_eq_sym NE_sel_row7)); exact Drow7_9).
  assert (Ddat_10 : live A10 (Z_to_bv 64 dat) = None) by (rewrite (LEQ9 _ (not_eq_sym NE_sel_dat)); exact Ddat_9).
  assert (SUB9 : sub_live A10 A9).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 sel) by (intros ->; rewrite Dsel_10 in Lq; discriminate Lq). rewrite <- (LEQ9 q NEq). exact Lq. }
  assert (PM10 : POSTM C A10 s m0 m10).
  { apply (POSTM_trans C A10 s m0 M9 m10); [apply (POSTM_sub C A10 A9 _ _ _ SUB9); exact (POSTM_trans _ _ _ _ _ _ PM9 PMs9)|].
    apply (POSTM_mono C A10 (s + OFF9) s); [unfold OFF9; lia | exact PMc9]. }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 sel :: [Z_to_bv 64 dat; Z_to_bv 64 row7; Z_to_bv 64 row6; Z_to_bv 64 row5; Z_to_bv 64 row4; Z_to_bv 64 row3; Z_to_bv 64 row2; Z_to_bv 64 row1; Z_to_bv 64 row0])) => eq_trans (LEQ9 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL9 q (fun XX => Hq (or_intror XX)))) as LDEL10.
  assert (KEPT9 : Forall (ex_region_kept E9 M9 m10) [(EVar 32, OFF9, 0%Z); (EVar 35, 0%Z, 8%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF9 1104 M9 m10 E9 (EVar 32) CK (proj1 PMc9) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (sd_kept_cell C (s + OFF9) psel M9 m10 E9 (EVar 35) CK (proj1 PMc9) ltac:(unfold OFF9; lia) ltac:(unfold OFF9; lia) RP eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E9 M9 m10 _ [] _ HKc9 KEPT9) as HKk9.
  match type of HKk9 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E9 m10 kk') in HKk9 end.
  pose proof (regs_ok_agree 343%nat E9 (ex_envL vals9 r10 [exW_canary SEGS 1410112 m10]) _ _ (vals_app_agree vals9 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa9.
  pose proof (exW_regs_call _ _ _ _ _ HRa9 (ex_regs_ok_junk vals9 r10 [exW_canary SEGS 1410112 m10] 343%nat ltac:(vm_cast_no_check (eq_refl 343%nat))) CS9) as HRn10.
  clear HRa9.
  assert (HKa10 : know_ok SEGS (ex_envL vals9 r10 [exW_canary SEGS 1410112 m10]) m10 _) by (exact (know_ok_agree SEGS 343%nat E9 _ m10 _ (vals_app_agree vals9 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk9)).
  rewrite (fr_denot_agree 343%nat E9 (ex_envL vals9 r10 [exW_canary SEGS 1410112 m10]) _ fr (vals_app_agree vals9 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc9 HKk9 KEPT9 HC9 HWs9 PMs9 Q10_9 Q1_9 Q2_9 Q4_9 PM9 HW9 PMc9 CS9 SUB9 RM9 RT9 LEQ9 OFF9 LDEL9 Lsel_a9 Drow0_9 Drow1_9 Drow2_9 Drow3_9 Drow4_9 Drow5_9 Drow6_9 Drow7_9 Ddat_9.
  subst M9. clear log9. clear E9. try clear Rc9. clear KN9.
  lazymatch type of HRn10 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn10 end.
  pose proof (W_sok_win C A10 m10 _ (s - 1104) (Z.to_nat 1104) CK HW10 GLO1 GLO2) as SOK10.
  pose proof (exW_canary_ok SEGS 1410112 m10 (canary_any m10)) as CANOK10.
  pose (vals10 := vals9 ++ map (getr r10) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m10]).
  pose proof (exW_kn_fixed SEGS C A10 m10 _ (ex_envL vals9 r10 [exW_canary SEGS 1410112 m10]) (EVar 375) (EVar 32) (exW_canary SEGS 1410112 m10) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW10 eq_refl (proj1 CANOK10) (proj2 CANOK10) eq_refl eq_refl eq_refl SOK10 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf10.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf10 HKa10)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn10 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN10 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf10 HKa10 SOK10 CANOK10.
  repeat match goal with H : getr r10 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E10 := EEx) in HR, Hlf, HK, Hms |- *; set (log10 := LLx) in Hms, Hlf; set (M10 := mem_denot E10 m10 log10) in Hms end.
  assert (WP10 : W C A10 M10 (with_vmmaps vm10 md) /\ POSTM C A10 (psel + 8) m10 M10 /\ (forall a : word, (s <= u a < psel)%Z -> M10 a = m10 a)).
  { subst M10. apply (sd_win_cell C A10 A10 m10 _ E10 log10 (EVar 32) (EVar 35) s 1104 psel CK HW10 (sub_live_refl A10) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | reflexivity | lia | exact GLO1 | exact Hsp | exact Hph]. }
  destruct WP10 as (HWs10 & PMs10 & BET10).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW10)) | exact (mp_lazy _ (w_pure _ _ _ _ HW10)) | exact Hms |].
  pose (BSF := [(32%nat, s); (35%nat, psel)]).
  exW_cellB HK Hlf r0 BSF (EVar 35) psel 0%Z 8%nat Cpsel.
  refine (HC A10 M10 vm10 RcF HWs10 _ Dsel_10 Ddat_10 Drow0_10 Drow1_10 Drow2_10 Drow3_10 Drow4_10 Drow5_10 Drow6_10 Drow7_10
            ltac:(intros q Hq; apply LDEL10; intros Hin; apply Hq; cbn [In] in Hin |- *; tauto)
            (POSTM_trans _ _ _ _ _ _ (POSTM_mono C A10 s (psel + 8) m0 m10 ltac:(lia) PM10) PMs10) Cpsel
            (fun a Ha => eq_trans (BET10 a Ha) (sd_frm_above C s m0 m10 a CK (proj1 PM10) ltac:(lia) ltac:(lia))) RT10).
  lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 RcF [(2%nat, EVar 32); (4%nat, ELit 1278416)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor; [symmetry; exact HTP | constructor]] | vm_compute; reflexivity] end.
Qed.

(* [comment removed for export] *)
Lemma seld_null : forall (fx : FPState) C A m md regs (s psel : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + O23LeptSelDC.SELD_WIN <= s)%Z -> (s <= psel)%Z -> (psel + 8 <= c_top C)%Z -> (psel mod 8 = 0)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 psel ->
  rdn SEGS m (Z_to_bv 64 (psel + 0)) 8 = Some (Z_to_le_bytes 8 0) ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 674932) m al_rom) md) S.
Proof using P16 PINS.
  intros fx C A0 m0 md r0 s psel ret S CK HW0 H2 Hs16 Hlo Hsp Hph Hpal H1 Hret H10 Mpsel HC.
  unfold O23LeptSelDC.SELD_WIN in *.
  assert (Hhi : (s <= c_top C)%Z) by lia.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  destruct fx as [fr cs]. pose proof I as FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  assert (GLO1 : (c_top C - LSTK <= s - 1104)%Z) by lia.
  assert (GLO2 : (s - 1104 + Z.of_nat (Z.to_nat 1104) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (1104 <= s)%Z) by lia.
  assert (RP : (0 <= psel < 2 ^ 64)%Z) by lia.
  pose (valsI := @nil word).
  pose proof (W_sok_win C A0 m0 _ (s - 1104) (Z.to_nat 1104) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 1410112 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0; psel]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0; psel]) (EVar 34) (EVar 32) (exW_canary SEGS 1410112 m0) s 1104 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0; psel]) m0 [KRange (EVar 32) 1422416 (2 ^ 63); KAlign (EVar 32) 16; KRange (EVar 35) 1422416 (2 ^ 63); KAlign (EVar 35) 8; KWord (SA (EVar 35) 0) 8 (ELit 0); KDisj (SA (EVar 32) (- 1104)) 1104 (SA (EVar 35) 0) 8]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 HKf0)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0; psel] HR.
  pose proof (ex_regs_ok_reexpr _ _ r0 ex_r10 (EVar 35) HR ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact H10)) as HRx. clear HR. rename HRx into HR.
  lazymatch type of HR with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HR end.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 md /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win C A0 A0 m0 _ E0 log0 (EVar 32) s 1104 CK HW0 (sub_live_refl A0) Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi]. }
  destruct WP0 as [HWs0 PMs0].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  refine (HC M0 RcF HWs0 _ PMs0).
  lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 RcF [(2%nat, EVar 32)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor] | vm_compute; reflexivity] end.
Qed.
End Chain.
