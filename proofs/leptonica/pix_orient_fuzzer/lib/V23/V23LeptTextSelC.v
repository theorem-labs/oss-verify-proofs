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
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase.
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
Definition SELSTR_WIN : Z := 1312.

(* [comment removed for export] *)
Lemma selstr_chain1 : forall (fx : FPState) C A m md regs (s : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELSTR_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 1278416 ->
  getr regs 10 = Z_to_bv 64 124731 -> getr regs 11 = Z_to_bv 64 5 -> getr regs 12 = Z_to_bv 64 6 -> getr regs 13 = Z_to_bv 64 0 ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (7 <= kR)%Z -> (7 * 2 ^ 17 <= bR)%Z ->
  (forall A' m' vm' regs' (sel arr row0 row1 row2 row3 row4 : Z),
     W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> sub_live A A' -> POSTM C A s m m' ->
     aroom A' vm' (kR - 7) (bR - 7 * 2 ^ 17) ->
     (forall q : word, ~ In q [Z_to_bv 64 row4; Z_to_bv 64 row3; Z_to_bv 64 row2; Z_to_bv 64 row1; Z_to_bv 64 row0; Z_to_bv 64 arr; Z_to_bv 64 sel] -> live A' q = live A q) ->
     getr regs' 10 = Z_to_bv 64 sel ->
     live A' (Z_to_bv 64 sel) = Some 32%Z -> live A (Z_to_bv 64 sel) = None -> live (c_A0 C) (Z_to_bv 64 sel) = None -> (0 <= sel < 2 ^ 64)%Z ->
     live A' (Z_to_bv 64 arr) = Some 40%Z -> live A (Z_to_bv 64 arr) = None -> live (c_A0 C) (Z_to_bv 64 arr) = None -> (0 <= arr < 2 ^ 64)%Z ->
     live A' (Z_to_bv 64 row0) = Some 24%Z -> live A (Z_to_bv 64 row0) = None -> live (c_A0 C) (Z_to_bv 64 row0) = None -> (0 <= row0 < 2 ^ 64)%Z ->
     live A' (Z_to_bv 64 row1) = Some 24%Z -> live A (Z_to_bv 64 row1) = None -> live (c_A0 C) (Z_to_bv 64 row1) = None -> (0 <= row1 < 2 ^ 64)%Z ->
     live A' (Z_to_bv 64 row2) = Some 24%Z -> live A (Z_to_bv 64 row2) = None -> live (c_A0 C) (Z_to_bv 64 row2) = None -> (0 <= row2 < 2 ^ 64)%Z ->
     live A' (Z_to_bv 64 row3) = Some 24%Z -> live A (Z_to_bv 64 row3) = None -> live (c_A0 C) (Z_to_bv 64 row3) = None -> (0 <= row3 < 2 ^ 64)%Z ->
     live A' (Z_to_bv 64 row4) = Some 24%Z -> live A (Z_to_bv 64 row4) = None -> live (c_A0 C) (Z_to_bv 64 row4) = None -> (0 <= row4 < 2 ^ 64)%Z ->
     Z_to_bv 64 sel <> Z_to_bv 64 arr ->
     Z_to_bv 64 sel <> Z_to_bv 64 row0 ->
     Z_to_bv 64 arr <> Z_to_bv 64 row0 ->
     Z_to_bv 64 sel <> Z_to_bv 64 row1 ->
     Z_to_bv 64 arr <> Z_to_bv 64 row1 ->
     Z_to_bv 64 row0 <> Z_to_bv 64 row1 ->
     Z_to_bv 64 sel <> Z_to_bv 64 row2 ->
     Z_to_bv 64 arr <> Z_to_bv 64 row2 ->
     Z_to_bv 64 row0 <> Z_to_bv 64 row2 ->
     Z_to_bv 64 row1 <> Z_to_bv 64 row2 ->
     Z_to_bv 64 sel <> Z_to_bv 64 row3 ->
     Z_to_bv 64 arr <> Z_to_bv 64 row3 ->
     Z_to_bv 64 row0 <> Z_to_bv 64 row3 ->
     Z_to_bv 64 row1 <> Z_to_bv 64 row3 ->
     Z_to_bv 64 row2 <> Z_to_bv 64 row3 ->
     Z_to_bv 64 sel <> Z_to_bv 64 row4 ->
     Z_to_bv 64 arr <> Z_to_bv 64 row4 ->
     Z_to_bv 64 row0 <> Z_to_bv 64 row4 ->
     Z_to_bv 64 row1 <> Z_to_bv 64 row4 ->
     Z_to_bv 64 row2 <> Z_to_bv 64 row4 ->
     Z_to_bv 64 row3 <> Z_to_bv 64 row4 ->
     rdn SEGS m' (Z_to_bv 64 (sel + 0)) 4 = Some (Z_to_le_bytes 4 5) ->
     rdn SEGS m' (Z_to_bv 64 (sel + 4)) 4 = Some (Z_to_le_bytes 4 6) ->
     rdn SEGS m' (Z_to_bv 64 (sel + 8)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (sel + 12)) 4 = Some (Z_to_le_bytes 4 3) ->
     rdn SEGS m' (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 arr) ->
     rdn SEGS m' (Z_to_bv 64 (sel + 24)) 8 = Some (Z_to_le_bytes 8 0) ->
     rdn SEGS m' (Z_to_bv 64 (arr + 0)) 8 = Some (Z_to_le_bytes 8 row0) ->
     rdn SEGS m' (Z_to_bv 64 (arr + 8)) 8 = Some (Z_to_le_bytes 8 row1) ->
     rdn SEGS m' (Z_to_bv 64 (arr + 16)) 8 = Some (Z_to_le_bytes 8 row2) ->
     rdn SEGS m' (Z_to_bv 64 (arr + 24)) 8 = Some (Z_to_le_bytes 8 row3) ->
     rdn SEGS m' (Z_to_bv 64 (arr + 32)) 8 = Some (Z_to_le_bytes 8 row4) ->
     rdn SEGS m' (Z_to_bv 64 (row0 + 0)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row0 + 4)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row0 + 8)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row0 + 12)) 4 = Some (Z_to_le_bytes 4 2) ->
     rdn SEGS m' (Z_to_bv 64 (row0 + 16)) 4 = Some (Z_to_le_bytes 4 2) ->
     rdn SEGS m' (Z_to_bv 64 (row0 + 20)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row1 + 0)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row1 + 4)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row1 + 8)) 4 = Some (Z_to_le_bytes 4 2) ->
     rdn SEGS m' (Z_to_bv 64 (row1 + 12)) 4 = Some (Z_to_le_bytes 4 2) ->
     rdn SEGS m' (Z_to_bv 64 (row1 + 16)) 4 = Some (Z_to_le_bytes 4 2) ->
     rdn SEGS m' (Z_to_bv 64 (row1 + 20)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row2 + 0)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row2 + 4)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row2 + 8)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row2 + 12)) 4 = Some (Z_to_le_bytes 4 2) ->
     rdn SEGS m' (Z_to_bv 64 (row2 + 16)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row2 + 20)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row3 + 0)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row3 + 4)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row3 + 8)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row3 + 12)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row3 + 16)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row3 + 20)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row4 + 0)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row4 + 4)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row4 + 8)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row4 + 12)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row4 + 16)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row4 + 20)) 4 = Some (Z_to_le_bytes 4 1) ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 678036) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 s ret S CK HW0 H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 H13 kR bR RM0 HkR HbR HC.
  unfold SELSTR_WIN in *.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  assert (HTP : ex_keep (getr r0 ex_r4 = Z_to_bv 64 1278416)) by exact H4.
  destruct fx as [fr cs]. pose proof I as FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  replace kR with (kR - 0)%Z in RM0 by lia. replace bR with (bR - 0 * 2 ^ 17)%Z in RM0 by lia.
  pose (valsI := @nil word).
  pose proof (fun (q : word) (_ : ~ In q []) => eq_refl (live A0 q)) as LDEL0.
  assert (GLO1 : (c_top C - LSTK <= s - 1312)%Z) by lia.
  assert (GLO2 : (s - 1312 + Z.of_nat (Z.to_nat 1312) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (1312 <= s)%Z) by lia.
  pose proof (W_sok_win C A0 m0 _ (s - 1312) (Z.to_nat 1312) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 1410112 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0]) (EVar 34) (EVar 32) (exW_canary SEGS 1410112 m0) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0]) m0 [KRange (EVar 32) 1422624 (2 ^ 63); KAlign (EVar 32) 16]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 HKf0)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 1312 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
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
  intros A1 m1 vm1 r1 res0 HW1 Hres0 CSx0 Hnz0 Fselx Lo0 F0sel LEQ0 ZERO0 ALsel TOP0 PMc0 RM1.
  pose proof CSx0 as CS0. clear CSx0.
  rewrite with_vmmaps_twice in HW1 |- *.
  assert (Eres0 : res0 = Z_to_bv 64 (u res0)) by (symmetry; apply zbv_self).
  pose proof (u64_range res0) as RRsel. set (sel := u res0) in *. clearbody sel. rewrite Eres0 in Hres0, Fselx, Lo0, F0sel, LEQ0, ZERO0. clear Eres0.
  change (1 * 32)%Z with 32%Z in *.
  pose proof (exW_blk_img_apart_h2 C A1 m1 _ sel 32 CK HW1 Lo0 RRsel eq_refl eq_refl) as IMGAPsel. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPsel.
  pose proof (exW_win_blk_apart_h C A1 m1 _ s 1312 sel 32 CK HW1 Lo0 eq_refl RRsel GLO1) as WAPsel.
  assert (Fsel : live A0 (Z_to_bv 64 sel) = None).
  { destruct (live A0 (Z_to_bv 64 sel)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB0 _ _ EE) as XX. first [discriminate Fselx | (rewrite Fselx in XX; discriminate XX)]. }
  pose proof Lo0 as Lsel_a1.
  assert (SUB1 : sub_live A0 A1).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 sel) by (intros ->; rewrite Fsel in Lq; discriminate Lq). rewrite (LEQ0 q NEq). exact (SUB0 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 sel :: [])) => eq_trans (LEQ0 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL0 q (fun XX => Hq (or_intror XX)))) as LDEL1.
  assert (PM1 : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|]. apply (POSTM_sub C A0 A0 _ _ _ SUB0).
    apply (POSTM_mono C A0 (s + OFF0) s); [unfold OFF0; lia | exact PMc0]. }
  replace (kR - 0 - 1)%Z with (kR - 1)%Z in RM1 by lia. rewrite MG0 in RM1. replace (bR - 0 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 1 * 2 ^ 17)%Z in RM1 by lia.
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, OFF0, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF0 1312 M0 m1 E0 (EVar 32) CK (proj1 PMc0) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E0 m1 kk') in HKk0 end.
  pose proof (regs_ok_agree 35%nat E0 (ex_envL vals0 r1 [sel; exW_canary SEGS 1410112 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [sel; exW_canary SEGS 1410112 m1] 35%nat ltac:(vm_cast_no_check (eq_refl 35%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [sel; exW_canary SEGS 1410112 m1]) m1 _) by (exact (know_ok_agree SEGS 35%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  rewrite (fr_denot_agree 35%nat E0 (ex_envL vals0 r1 [sel; exW_canary SEGS 1410112 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r1 ex_r10 (EVar 67) HRn1 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres0)) as HRx1. clear HRn1. rename HRx1 into HRn1.
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q11_0 Q1_0 Q2_0 Q4_0 PM0 HW0 PMc0 CS0 SUB0 RM0 MG0 TOP0 LEQ0 Hnz0 Fselx Lo0 OFF0 LDEL0.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  pose proof (exW_kn_blk SEGS C A1 m1 _ (ex_envL vals0 r1 [sel; exW_canary SEGS 1410112 m1]) (EVar 67) (EVar 32) sel 32 s 1312 65536 1347584 p16_segs CK HW1 Lsel_a1 RRsel eq_refl eq_refl eq_refl RS ALsel ZERO0 WAPsel IMGAPsel) as HKb1.
  pose proof (W_sok_win C A1 m1 _ (s - 1312) (Z.to_nat 1312) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 1410112 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [sel; exW_canary SEGS 1410112 m1]).
  pose proof (exW_kn_fixed SEGS C A1 m1 _ (ex_envL vals0 r1 [sel; exW_canary SEGS 1410112 m1]) (EVar 68) (EVar 32) (exW_canary SEGS 1410112 m1) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb1 (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb1 HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO0 ALsel.
  exb_exit ST Rc1 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A1 M1 (with_vmmaps vm1 md) /\ POSTM C A0 s m1 M1).
  { subst M1. apply (exW_win_blks C A1 A0 m1 _ E1 log1 (EVar 32) s 1312 [(EVar 67, sel, 32%Z)] CK HW1 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel (conj Lsel_a1 (conj Fsel F0sel))))|]. constructor. }
  destruct WP1 as [HWs1 PMs1].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log1 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC1 : carry log1 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc1 : know_ok SEGS E1 M1 kn1) by (apply (carry_after SEGS E1 m1 log1 kn0 [] kn1 scs hs HC1 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose (BS1 := [(32%nat, s); (67%nat, sel)]).
  exW_regfactB BS1 HR ex_r10 Q10_1. exW_regfactB BS1 HR ex_r11 Q11_1. exW_regfactB BS1 HR ex_r1 Q1_1. exW_regfactB BS1 HR ex_r2 Q2_1. exW_regfactB BS1 HR ex_r4 Q4_1.
  clear BS1.
  lazymatch type of Q2_1 with _ = Z_to_bv 64 (s + ?off) => pose (OFF1 := off) end.
  pose proof (alloc_margin_small (5 * 8) ltac:(exW_cmp)) as MG1.
  lazymatch type of Q1_1 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_1 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A1 M1 _ Rc1 5 8 (kR - 1) (bR - 1 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs1 Q10_1 Q11_1 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM1) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_1
             ltac:(red; apply bv_eq; reflexivity) Q4_1 Q2_1 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A2 m2 vm2 r2 res1 HW2 Hres1 CSx1 Hnz1 Farrx Lo1 F0arr LEQ1 ZERO1 ALarr TOP1 PMc1 RM2.
  pose proof CSx1 as CS1. clear CSx1.
  rewrite with_vmmaps_twice in HW2 |- *.
  assert (Eres1 : res1 = Z_to_bv 64 (u res1)) by (symmetry; apply zbv_self).
  pose proof (u64_range res1) as RRarr. set (arr := u res1) in *. clearbody arr. rewrite Eres1 in Hres1, Farrx, Lo1, F0arr, LEQ1, ZERO1. clear Eres1.
  change (5 * 8)%Z with 40%Z in *.
  pose proof (exW_blk_img_apart_h2 C A2 m2 _ arr 40 CK HW2 Lo1 RRarr eq_refl eq_refl) as IMGAParr. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAParr.
  pose proof (exW_win_blk_apart_h C A2 m2 _ s 1312 arr 40 CK HW2 Lo1 eq_refl RRarr GLO1) as WAParr.
  assert (Farr : live A0 (Z_to_bv 64 arr) = None).
  { destruct (live A0 (Z_to_bv 64 arr)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB1 _ _ EE) as XX. first [discriminate Farrx | (rewrite Farrx in XX; discriminate XX)]. }
  pose proof Lo1 as Larr_a2.
  assert (SUB2 : sub_live A0 A2).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 arr) by (intros ->; rewrite Farr in Lq; discriminate Lq). rewrite (LEQ1 q NEq). exact (SUB1 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 arr :: [Z_to_bv 64 sel])) => eq_trans (LEQ1 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL1 q (fun XX => Hq (or_intror XX)))) as LDEL2.
  assert (NE_sel_arr : Z_to_bv 64 sel <> Z_to_bv 64 arr) by (intros EE; rewrite EE in Lsel_a1; rewrite Farrx in Lsel_a1; discriminate Lsel_a1).
  assert (Lsel_a2 : live A2 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ1 _ NE_sel_arr); exact Lsel_a1).
  pose proof (exW_blk_apart_h C A2 m2 _ sel arr 32 40 CK HW2 Lsel_a2 Larr_a2 NE_sel_arr RRsel RRarr ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel_arr.
  assert (PM2 : POSTM C A0 s m0 m2).
  { eapply POSTM_trans; [exact PM1|]. eapply POSTM_trans; [exact PMs1|]. apply (POSTM_sub C A0 A1 _ _ _ SUB1).
    apply (POSTM_mono C A1 (s + OFF1) s); [unfold OFF1; lia | exact PMc1]. }
  replace (kR - 1 - 1)%Z with (kR - 2)%Z in RM2 by lia. rewrite MG1 in RM2. replace (bR - 1 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 2 * 2 ^ 17)%Z in RM2 by lia.
  assert (KEPT1 : Forall (ex_region_kept E1 M1 m2) [(EVar 32, OFF1, 0%Z); (EVar 67, 0%Z, 32%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF1 1312 M1 m2 E1 (EVar 32) CK (proj1 PMc1) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A1 A1 M1 _ M1 m2 E1 (EVar 67) sel 32 CK HWs1 Lsel_a1 RRsel eq_refl (proj2 PMc1) Lsel_a1 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E1 M1 m2 _ [] _ HKc1 KEPT1) as HKk1.
  match type of HKk1 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E1 m2 kk') in HKk1 end.
  pose proof (regs_ok_agree 69%nat E1 (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) _ _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa1.
  pose proof (exW_regs_call _ _ _ _ _ HRa1 (ex_regs_ok_junk vals1 r2 [arr; exW_canary SEGS 1410112 m2] 69%nat ltac:(vm_cast_no_check (eq_refl 69%nat))) CS1) as HRn2.
  clear HRa1.
  assert (HKa2 : know_ok SEGS (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) m2 _) by (exact (know_ok_agree SEGS 69%nat E1 _ m2 _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk1)).
  rewrite (fr_denot_agree 69%nat E1 (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) _ fr (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r2 ex_r10 (EVar 101) HRn2 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres1)) as HRx2. clear HRn2. rename HRx2 into HRn2.
  clear HR HK Hlf Hms HKc1 HKk1 KEPT1 HC1 HWs1 PMs1 Q10_1 Q11_1 Q1_1 Q2_1 Q4_1 PM1 HW1 PMc1 CS1 SUB1 RM1 MG1 TOP1 LEQ1 Hnz1 Farrx Lo1 OFF1 LDEL1 Lsel_a1.
  subst M1. clear log1. clear E1. try clear Rc1. clear KN1.
  lazymatch type of HRn2 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn2 end.
  pose proof (exW_kn_blk SEGS C A2 m2 _ (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) (EVar 101) (EVar 32) arr 40 s 1312 65536 1347584 p16_segs CK HW2 Larr_a2 RRarr eq_refl eq_refl eq_refl RS ALarr ZERO1 WAParr IMGAParr) as HKb2.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) m2) _ _ (ex_kdisj_apart SEGS (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) m2 (EVar 67) (EVar 101) sel arr 0 32 0 40 eq_refl eq_refl RRsel RRarr AP_sel_arr) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) m2))) as HKd2.
  pose proof (W_sok_win C A2 m2 _ (s - 1312) (Z.to_nat 1312) CK HW2 GLO1 GLO2) as SOK2.
  pose proof (exW_canary_ok SEGS 1410112 m2 (canary_any m2)) as CANOK2.
  pose (vals2 := vals1 ++ map (getr r2) ex_regs_list ++ map (Z_to_bv 64) [arr; exW_canary SEGS 1410112 m2]).
  pose proof (exW_kn_fixed SEGS C A2 m2 _ (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) (EVar 102) (EVar 32) (exW_canary SEGS 1410112 m2) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW2 eq_refl (proj1 CANOK2) (proj2 CANOK2) eq_refl eq_refl eq_refl SOK2 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf2.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb2 (proj2 (Forall_app _ _ _) (conj HKd2 (proj2 (Forall_app _ _ _) (conj HKf2 HKa2)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn2 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN2 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb2 HKd2 HKf2 HKa2 SOK2 CANOK2.
  repeat match goal with H : getr r2 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO1 ALarr.
  exb_exit ST Rc2 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E2 := EEx) in HR, Hlf, HK, Hms |- *; set (log2 := LLx) in Hms, Hlf; set (M2 := mem_denot E2 m2 log2) in Hms end.
  assert (WP2 : W C A2 M2 (with_vmmaps vm2 md) /\ POSTM C A0 s m2 M2).
  { subst M2. apply (exW_win_blks C A2 A0 m2 _ E2 log2 (EVar 32) s 1312 [(EVar 67, sel, 32%Z); (EVar 101, arr, 40%Z)] CK HW2 SUB2 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel (conj Lsel_a2 (conj Fsel F0sel))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a2 (conj Farr F0arr))))|]. constructor. }
  destruct WP2 as [HWs2 PMs2].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log2 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC2 : carry log2 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc2 : know_ok SEGS E2 M2 kn1) by (apply (carry_after SEGS E2 m2 log2 kn0 [] kn1 scs hs HC2 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact Hms |].
  pose (BS2 := [(32%nat, s); (67%nat, sel); (101%nat, arr)]).
  exW_regfactB BS2 HR ex_r10 Q10_2. exW_regfactB BS2 HR ex_r11 Q11_2. exW_regfactB BS2 HR ex_r1 Q1_2. exW_regfactB BS2 HR ex_r2 Q2_2. exW_regfactB BS2 HR ex_r4 Q4_2.
  clear BS2.
  lazymatch type of Q2_2 with _ = Z_to_bv 64 (s + ?off) => pose (OFF2 := off) end.
  pose proof (alloc_margin_small (6 * 4) ltac:(exW_cmp)) as MG2.
  lazymatch type of Q1_2 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_2 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A2 M2 _ Rc2 6 4 (kR - 2) (bR - 2 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs2 Q10_2 Q11_2 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM2) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_2
             ltac:(red; apply bv_eq; reflexivity) Q4_2 Q2_2 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A3 m3 vm3 r3 res2 HW3 Hres2 CSx2 Hnz2 Frow0x Lo2 F0row0 LEQ2 ZERO2 ALrow0 TOP2 PMc2 RM3.
  pose proof CSx2 as CS2. clear CSx2.
  rewrite with_vmmaps_twice in HW3 |- *.
  assert (Eres2 : res2 = Z_to_bv 64 (u res2)) by (symmetry; apply zbv_self).
  pose proof (u64_range res2) as RRrow0. set (row0 := u res2) in *. clearbody row0. rewrite Eres2 in Hres2, Frow0x, Lo2, F0row0, LEQ2, ZERO2. clear Eres2.
  change (6 * 4)%Z with 24%Z in *.
  pose proof (exW_blk_img_apart_h2 C A3 m3 _ row0 24 CK HW3 Lo2 RRrow0 eq_refl eq_refl) as IMGAProw0. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAProw0.
  pose proof (exW_win_blk_apart_h C A3 m3 _ s 1312 row0 24 CK HW3 Lo2 eq_refl RRrow0 GLO1) as WAProw0.
  assert (Frow0 : live A0 (Z_to_bv 64 row0) = None).
  { destruct (live A0 (Z_to_bv 64 row0)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB2 _ _ EE) as XX. first [discriminate Frow0x | (rewrite Frow0x in XX; discriminate XX)]. }
  pose proof Lo2 as Lrow0_a3.
  assert (SUB3 : sub_live A0 A3).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row0) by (intros ->; rewrite Frow0 in Lq; discriminate Lq). rewrite (LEQ2 q NEq). exact (SUB2 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row0 :: [Z_to_bv 64 arr; Z_to_bv 64 sel])) => eq_trans (LEQ2 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL2 q (fun XX => Hq (or_intror XX)))) as LDEL3.
  assert (NE_sel_row0 : Z_to_bv 64 sel <> Z_to_bv 64 row0) by (intros EE; rewrite EE in Lsel_a2; rewrite Frow0x in Lsel_a2; discriminate Lsel_a2).
  assert (Lsel_a3 : live A3 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ2 _ NE_sel_row0); exact Lsel_a2).
  pose proof (exW_blk_apart_h C A3 m3 _ sel row0 32 24 CK HW3 Lsel_a3 Lrow0_a3 NE_sel_row0 RRsel RRrow0 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel_row0.
  assert (NE_arr_row0 : Z_to_bv 64 arr <> Z_to_bv 64 row0) by (intros EE; rewrite EE in Larr_a2; rewrite Frow0x in Larr_a2; discriminate Larr_a2).
  assert (Larr_a3 : live A3 (Z_to_bv 64 arr) = Some 40%Z) by (rewrite (LEQ2 _ NE_arr_row0); exact Larr_a2).
  pose proof (exW_blk_apart_h C A3 m3 _ arr row0 40 24 CK HW3 Larr_a3 Lrow0_a3 NE_arr_row0 RRarr RRrow0 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_row0.
  assert (PM3 : POSTM C A0 s m0 m3).
  { eapply POSTM_trans; [exact PM2|]. eapply POSTM_trans; [exact PMs2|]. apply (POSTM_sub C A0 A2 _ _ _ SUB2).
    apply (POSTM_mono C A2 (s + OFF2) s); [unfold OFF2; lia | exact PMc2]. }
  replace (kR - 2 - 1)%Z with (kR - 3)%Z in RM3 by lia. rewrite MG2 in RM3. replace (bR - 2 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 3 * 2 ^ 17)%Z in RM3 by lia.
  assert (KEPT2 : Forall (ex_region_kept E2 M2 m3) [(EVar 32, OFF2, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 40%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF2 1312 M2 m3 E2 (EVar 32) CK (proj1 PMc2) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A2 A2 M2 _ M2 m3 E2 (EVar 67) sel 32 CK HWs2 Lsel_a2 RRsel eq_refl (proj2 PMc2) Lsel_a2 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A2 A2 M2 _ M2 m3 E2 (EVar 101) arr 40 CK HWs2 Larr_a2 RRarr eq_refl (proj2 PMc2) Larr_a2 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E2 M2 m3 _ [] _ HKc2 KEPT2) as HKk2.
  match type of HKk2 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E2 m3 kk') in HKk2 end.
  pose proof (regs_ok_agree 103%nat E2 (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) _ _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa2.
  pose proof (exW_regs_call _ _ _ _ _ HRa2 (ex_regs_ok_junk vals2 r3 [row0; exW_canary SEGS 1410112 m3] 103%nat ltac:(vm_cast_no_check (eq_refl 103%nat))) CS2) as HRn3.
  clear HRa2.
  assert (HKa3 : know_ok SEGS (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) m3 _) by (exact (know_ok_agree SEGS 103%nat E2 _ m3 _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk2)).
  rewrite (fr_denot_agree 103%nat E2 (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) _ fr (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r3 ex_r10 (EVar 135) HRn3 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres2)) as HRx3. clear HRn3. rename HRx3 into HRn3.
  clear HR HK Hlf Hms HKc2 HKk2 KEPT2 HC2 HWs2 PMs2 Q10_2 Q11_2 Q1_2 Q2_2 Q4_2 PM2 HW2 PMc2 CS2 SUB2 RM2 MG2 TOP2 LEQ2 Hnz2 Frow0x Lo2 OFF2 LDEL2 Lsel_a2 Larr_a2.
  subst M2. clear log2. clear E2. try clear Rc2. clear KN2.
  lazymatch type of HRn3 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn3 end.
  pose proof (exW_kn_blk SEGS C A3 m3 _ (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) (EVar 135) (EVar 32) row0 24 s 1312 65536 1347584 p16_segs CK HW3 Lrow0_a3 RRrow0 eq_refl eq_refl eq_refl RS ALrow0 ZERO2 WAProw0 IMGAProw0) as HKb3.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) m3) _ _ (ex_kdisj_apart SEGS (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) m3 (EVar 67) (EVar 135) sel row0 0 32 0 24 eq_refl eq_refl RRsel RRrow0 AP_sel_row0) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) m3) _ _ (ex_kdisj_apart SEGS (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) m3 (EVar 101) (EVar 135) arr row0 0 40 0 24 eq_refl eq_refl RRarr RRrow0 AP_arr_row0) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) m3)))) as HKd3.
  pose proof (W_sok_win C A3 m3 _ (s - 1312) (Z.to_nat 1312) CK HW3 GLO1 GLO2) as SOK3.
  pose proof (exW_canary_ok SEGS 1410112 m3 (canary_any m3)) as CANOK3.
  pose (vals3 := vals2 ++ map (getr r3) ex_regs_list ++ map (Z_to_bv 64) [row0; exW_canary SEGS 1410112 m3]).
  pose proof (exW_kn_fixed SEGS C A3 m3 _ (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) (EVar 136) (EVar 32) (exW_canary SEGS 1410112 m3) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW3 eq_refl (proj1 CANOK3) (proj2 CANOK3) eq_refl eq_refl eq_refl SOK3 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf3.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb3 (proj2 (Forall_app _ _ _) (conj HKd3 (proj2 (Forall_app _ _ _) (conj HKf3 HKa3)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn3 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN3 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb3 HKd3 HKf3 HKa3 SOK3 CANOK3.
  repeat match goal with H : getr r3 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO2 ALrow0.
  exb_exit ST Rc3 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E3 := EEx) in HR, Hlf, HK, Hms |- *; set (log3 := LLx) in Hms, Hlf; set (M3 := mem_denot E3 m3 log3) in Hms end.
  assert (WP3 : W C A3 M3 (with_vmmaps vm3 md) /\ POSTM C A0 s m3 M3).
  { subst M3. apply (exW_win_blks C A3 A0 m3 _ E3 log3 (EVar 32) s 1312 [(EVar 67, sel, 32%Z); (EVar 101, arr, 40%Z); (EVar 135, row0, 24%Z)] CK HW3 SUB3 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel (conj Lsel_a3 (conj Fsel F0sel))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a3 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRrow0 (conj Lrow0_a3 (conj Frow0 F0row0))))|]. constructor. }
  destruct WP3 as [HWs3 PMs3].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log3 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC3 : carry log3 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc3 : know_ok SEGS E3 M3 kn1) by (apply (carry_after SEGS E3 m3 log3 kn0 [] kn1 scs hs HC3 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact Hms |].
  pose (BS3 := [(32%nat, s); (67%nat, sel); (101%nat, arr); (135%nat, row0)]).
  exW_regfactB BS3 HR ex_r10 Q10_3. exW_regfactB BS3 HR ex_r11 Q11_3. exW_regfactB BS3 HR ex_r1 Q1_3. exW_regfactB BS3 HR ex_r2 Q2_3. exW_regfactB BS3 HR ex_r4 Q4_3.
  clear BS3.
  lazymatch type of Q2_3 with _ = Z_to_bv 64 (s + ?off) => pose (OFF3 := off) end.
  pose proof (alloc_margin_small (6 * 4) ltac:(exW_cmp)) as MG3.
  lazymatch type of Q1_3 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_3 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A3 M3 _ Rc3 6 4 (kR - 3) (bR - 3 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs3 Q10_3 Q11_3 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM3) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_3
             ltac:(red; apply bv_eq; reflexivity) Q4_3 Q2_3 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A4 m4 vm4 r4 res3 HW4 Hres3 CSx3 Hnz3 Frow1x Lo3 F0row1 LEQ3 ZERO3 ALrow1 TOP3 PMc3 RM4.
  pose proof CSx3 as CS3. clear CSx3.
  rewrite with_vmmaps_twice in HW4 |- *.
  assert (Eres3 : res3 = Z_to_bv 64 (u res3)) by (symmetry; apply zbv_self).
  pose proof (u64_range res3) as RRrow1. set (row1 := u res3) in *. clearbody row1. rewrite Eres3 in Hres3, Frow1x, Lo3, F0row1, LEQ3, ZERO3. clear Eres3.
  change (6 * 4)%Z with 24%Z in *.
  pose proof (exW_blk_img_apart_h2 C A4 m4 _ row1 24 CK HW4 Lo3 RRrow1 eq_refl eq_refl) as IMGAProw1. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAProw1.
  pose proof (exW_win_blk_apart_h C A4 m4 _ s 1312 row1 24 CK HW4 Lo3 eq_refl RRrow1 GLO1) as WAProw1.
  assert (Frow1 : live A0 (Z_to_bv 64 row1) = None).
  { destruct (live A0 (Z_to_bv 64 row1)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB3 _ _ EE) as XX. first [discriminate Frow1x | (rewrite Frow1x in XX; discriminate XX)]. }
  pose proof Lo3 as Lrow1_a4.
  assert (SUB4 : sub_live A0 A4).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row1) by (intros ->; rewrite Frow1 in Lq; discriminate Lq). rewrite (LEQ3 q NEq). exact (SUB3 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row1 :: [Z_to_bv 64 row0; Z_to_bv 64 arr; Z_to_bv 64 sel])) => eq_trans (LEQ3 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL3 q (fun XX => Hq (or_intror XX)))) as LDEL4.
  assert (NE_sel_row1 : Z_to_bv 64 sel <> Z_to_bv 64 row1) by (intros EE; rewrite EE in Lsel_a3; rewrite Frow1x in Lsel_a3; discriminate Lsel_a3).
  assert (Lsel_a4 : live A4 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ3 _ NE_sel_row1); exact Lsel_a3).
  pose proof (exW_blk_apart_h C A4 m4 _ sel row1 32 24 CK HW4 Lsel_a4 Lrow1_a4 NE_sel_row1 RRsel RRrow1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel_row1.
  assert (NE_arr_row1 : Z_to_bv 64 arr <> Z_to_bv 64 row1) by (intros EE; rewrite EE in Larr_a3; rewrite Frow1x in Larr_a3; discriminate Larr_a3).
  assert (Larr_a4 : live A4 (Z_to_bv 64 arr) = Some 40%Z) by (rewrite (LEQ3 _ NE_arr_row1); exact Larr_a3).
  pose proof (exW_blk_apart_h C A4 m4 _ arr row1 40 24 CK HW4 Larr_a4 Lrow1_a4 NE_arr_row1 RRarr RRrow1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_row1.
  assert (NE_row0_row1 : Z_to_bv 64 row0 <> Z_to_bv 64 row1) by (intros EE; rewrite EE in Lrow0_a3; rewrite Frow1x in Lrow0_a3; discriminate Lrow0_a3).
  assert (Lrow0_a4 : live A4 (Z_to_bv 64 row0) = Some 24%Z) by (rewrite (LEQ3 _ NE_row0_row1); exact Lrow0_a3).
  pose proof (exW_blk_apart_h C A4 m4 _ row0 row1 24 24 CK HW4 Lrow0_a4 Lrow1_a4 NE_row0_row1 RRrow0 RRrow1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row0_row1.
  assert (PM4 : POSTM C A0 s m0 m4).
  { eapply POSTM_trans; [exact PM3|]. eapply POSTM_trans; [exact PMs3|]. apply (POSTM_sub C A0 A3 _ _ _ SUB3).
    apply (POSTM_mono C A3 (s + OFF3) s); [unfold OFF3; lia | exact PMc3]. }
  replace (kR - 3 - 1)%Z with (kR - 4)%Z in RM4 by lia. rewrite MG3 in RM4. replace (bR - 3 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 4 * 2 ^ 17)%Z in RM4 by lia.
  assert (KEPT3 : Forall (ex_region_kept E3 M3 m4) [(EVar 32, OFF3, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 40%Z); (EVar 135, 0%Z, 24%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF3 1312 M3 m4 E3 (EVar 32) CK (proj1 PMc3) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A3 A3 M3 _ M3 m4 E3 (EVar 67) sel 32 CK HWs3 Lsel_a3 RRsel eq_refl (proj2 PMc3) Lsel_a3 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A3 A3 M3 _ M3 m4 E3 (EVar 101) arr 40 CK HWs3 Larr_a3 RRarr eq_refl (proj2 PMc3) Larr_a3 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A3 A3 M3 _ M3 m4 E3 (EVar 135) row0 24 CK HWs3 Lrow0_a3 RRrow0 eq_refl (proj2 PMc3) Lrow0_a3 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E3 M3 m4 _ [] _ HKc3 KEPT3) as HKk3.
  match type of HKk3 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E3 m4 kk') in HKk3 end.
  pose proof (regs_ok_agree 137%nat E3 (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) _ _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa3.
  pose proof (exW_regs_call _ _ _ _ _ HRa3 (ex_regs_ok_junk vals3 r4 [row1; exW_canary SEGS 1410112 m4] 137%nat ltac:(vm_cast_no_check (eq_refl 137%nat))) CS3) as HRn4.
  clear HRa3.
  assert (HKa4 : know_ok SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4 _) by (exact (know_ok_agree SEGS 137%nat E3 _ m4 _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk3)).
  rewrite (fr_denot_agree 137%nat E3 (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) _ fr (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r4 ex_r10 (EVar 169) HRn4 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres3)) as HRx4. clear HRn4. rename HRx4 into HRn4.
  clear HR HK Hlf Hms HKc3 HKk3 KEPT3 HC3 HWs3 PMs3 Q10_3 Q11_3 Q1_3 Q2_3 Q4_3 PM3 HW3 PMc3 CS3 SUB3 RM3 MG3 TOP3 LEQ3 Hnz3 Frow1x Lo3 OFF3 LDEL3 Lsel_a3 Larr_a3 Lrow0_a3.
  subst M3. clear log3. clear E3. try clear Rc3. clear KN3.
  lazymatch type of HRn4 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn4 end.
  pose proof (exW_kn_blk SEGS C A4 m4 _ (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) (EVar 169) (EVar 32) row1 24 s 1312 65536 1347584 p16_segs CK HW4 Lrow1_a4 RRrow1 eq_refl eq_refl eq_refl RS ALrow1 ZERO3 WAProw1 IMGAProw1) as HKb4.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4) _ _ (ex_kdisj_apart SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4 (EVar 67) (EVar 169) sel row1 0 32 0 24 eq_refl eq_refl RRsel RRrow1 AP_sel_row1) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4) _ _ (ex_kdisj_apart SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4 (EVar 101) (EVar 169) arr row1 0 40 0 24 eq_refl eq_refl RRarr RRrow1 AP_arr_row1) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4) _ _ (ex_kdisj_apart SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4 (EVar 135) (EVar 169) row0 row1 0 24 0 24 eq_refl eq_refl RRrow0 RRrow1 AP_row0_row1) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4))))) as HKd4.
  pose proof (W_sok_win C A4 m4 _ (s - 1312) (Z.to_nat 1312) CK HW4 GLO1 GLO2) as SOK4.
  pose proof (exW_canary_ok SEGS 1410112 m4 (canary_any m4)) as CANOK4.
  pose (vals4 := vals3 ++ map (getr r4) ex_regs_list ++ map (Z_to_bv 64) [row1; exW_canary SEGS 1410112 m4]).
  pose proof (exW_kn_fixed SEGS C A4 m4 _ (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) (EVar 170) (EVar 32) (exW_canary SEGS 1410112 m4) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW4 eq_refl (proj1 CANOK4) (proj2 CANOK4) eq_refl eq_refl eq_refl SOK4 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf4.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb4 (proj2 (Forall_app _ _ _) (conj HKd4 (proj2 (Forall_app _ _ _) (conj HKf4 HKa4)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn4 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN4 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb4 HKd4 HKf4 HKa4 SOK4 CANOK4.
  repeat match goal with H : getr r4 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO3 ALrow1.
  exb_exit ST Rc4 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E4 := EEx) in HR, Hlf, HK, Hms |- *; set (log4 := LLx) in Hms, Hlf; set (M4 := mem_denot E4 m4 log4) in Hms end.
  assert (WP4 : W C A4 M4 (with_vmmaps vm4 md) /\ POSTM C A0 s m4 M4).
  { subst M4. apply (exW_win_blks C A4 A0 m4 _ E4 log4 (EVar 32) s 1312 [(EVar 67, sel, 32%Z); (EVar 101, arr, 40%Z); (EVar 135, row0, 24%Z); (EVar 169, row1, 24%Z)] CK HW4 SUB4 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel (conj Lsel_a4 (conj Fsel F0sel))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a4 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRrow0 (conj Lrow0_a4 (conj Frow0 F0row0))))|]. constructor; [exact (conj eq_refl (conj RRrow1 (conj Lrow1_a4 (conj Frow1 F0row1))))|]. constructor. }
  destruct WP4 as [HWs4 PMs4].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log4 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC4 : carry log4 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc4 : know_ok SEGS E4 M4 kn1) by (apply (carry_after SEGS E4 m4 log4 kn0 [] kn1 scs hs HC4 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact Hms |].
  pose (BS4 := [(32%nat, s); (67%nat, sel); (101%nat, arr); (135%nat, row0); (169%nat, row1)]).
  exW_regfactB BS4 HR ex_r10 Q10_4. exW_regfactB BS4 HR ex_r11 Q11_4. exW_regfactB BS4 HR ex_r1 Q1_4. exW_regfactB BS4 HR ex_r2 Q2_4. exW_regfactB BS4 HR ex_r4 Q4_4.
  clear BS4.
  lazymatch type of Q2_4 with _ = Z_to_bv 64 (s + ?off) => pose (OFF4 := off) end.
  pose proof (alloc_margin_small (6 * 4) ltac:(exW_cmp)) as MG4.
  lazymatch type of Q1_4 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_4 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A4 M4 _ Rc4 6 4 (kR - 4) (bR - 4 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs4 Q10_4 Q11_4 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM4) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_4
             ltac:(red; apply bv_eq; reflexivity) Q4_4 Q2_4 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A5 m5 vm5 r5 res4 HW5 Hres4 CSx4 Hnz4 Frow2x Lo4 F0row2 LEQ4 ZERO4 ALrow2 TOP4 PMc4 RM5.
  pose proof CSx4 as CS4. clear CSx4.
  rewrite with_vmmaps_twice in HW5 |- *.
  assert (Eres4 : res4 = Z_to_bv 64 (u res4)) by (symmetry; apply zbv_self).
  pose proof (u64_range res4) as RRrow2. set (row2 := u res4) in *. clearbody row2. rewrite Eres4 in Hres4, Frow2x, Lo4, F0row2, LEQ4, ZERO4. clear Eres4.
  change (6 * 4)%Z with 24%Z in *.
  pose proof (exW_blk_img_apart_h2 C A5 m5 _ row2 24 CK HW5 Lo4 RRrow2 eq_refl eq_refl) as IMGAProw2. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAProw2.
  pose proof (exW_win_blk_apart_h C A5 m5 _ s 1312 row2 24 CK HW5 Lo4 eq_refl RRrow2 GLO1) as WAProw2.
  assert (Frow2 : live A0 (Z_to_bv 64 row2) = None).
  { destruct (live A0 (Z_to_bv 64 row2)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB4 _ _ EE) as XX. first [discriminate Frow2x | (rewrite Frow2x in XX; discriminate XX)]. }
  pose proof Lo4 as Lrow2_a5.
  assert (SUB5 : sub_live A0 A5).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row2) by (intros ->; rewrite Frow2 in Lq; discriminate Lq). rewrite (LEQ4 q NEq). exact (SUB4 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row2 :: [Z_to_bv 64 row1; Z_to_bv 64 row0; Z_to_bv 64 arr; Z_to_bv 64 sel])) => eq_trans (LEQ4 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL4 q (fun XX => Hq (or_intror XX)))) as LDEL5.
  assert (NE_sel_row2 : Z_to_bv 64 sel <> Z_to_bv 64 row2) by (intros EE; rewrite EE in Lsel_a4; rewrite Frow2x in Lsel_a4; discriminate Lsel_a4).
  assert (Lsel_a5 : live A5 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ4 _ NE_sel_row2); exact Lsel_a4).
  pose proof (exW_blk_apart_h C A5 m5 _ sel row2 32 24 CK HW5 Lsel_a5 Lrow2_a5 NE_sel_row2 RRsel RRrow2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel_row2.
  assert (NE_arr_row2 : Z_to_bv 64 arr <> Z_to_bv 64 row2) by (intros EE; rewrite EE in Larr_a4; rewrite Frow2x in Larr_a4; discriminate Larr_a4).
  assert (Larr_a5 : live A5 (Z_to_bv 64 arr) = Some 40%Z) by (rewrite (LEQ4 _ NE_arr_row2); exact Larr_a4).
  pose proof (exW_blk_apart_h C A5 m5 _ arr row2 40 24 CK HW5 Larr_a5 Lrow2_a5 NE_arr_row2 RRarr RRrow2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_row2.
  assert (NE_row0_row2 : Z_to_bv 64 row0 <> Z_to_bv 64 row2) by (intros EE; rewrite EE in Lrow0_a4; rewrite Frow2x in Lrow0_a4; discriminate Lrow0_a4).
  assert (Lrow0_a5 : live A5 (Z_to_bv 64 row0) = Some 24%Z) by (rewrite (LEQ4 _ NE_row0_row2); exact Lrow0_a4).
  pose proof (exW_blk_apart_h C A5 m5 _ row0 row2 24 24 CK HW5 Lrow0_a5 Lrow2_a5 NE_row0_row2 RRrow0 RRrow2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row0_row2.
  assert (NE_row1_row2 : Z_to_bv 64 row1 <> Z_to_bv 64 row2) by (intros EE; rewrite EE in Lrow1_a4; rewrite Frow2x in Lrow1_a4; discriminate Lrow1_a4).
  assert (Lrow1_a5 : live A5 (Z_to_bv 64 row1) = Some 24%Z) by (rewrite (LEQ4 _ NE_row1_row2); exact Lrow1_a4).
  pose proof (exW_blk_apart_h C A5 m5 _ row1 row2 24 24 CK HW5 Lrow1_a5 Lrow2_a5 NE_row1_row2 RRrow1 RRrow2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row1_row2.
  assert (PM5 : POSTM C A0 s m0 m5).
  { eapply POSTM_trans; [exact PM4|]. eapply POSTM_trans; [exact PMs4|]. apply (POSTM_sub C A0 A4 _ _ _ SUB4).
    apply (POSTM_mono C A4 (s + OFF4) s); [unfold OFF4; lia | exact PMc4]. }
  replace (kR - 4 - 1)%Z with (kR - 5)%Z in RM5 by lia. rewrite MG4 in RM5. replace (bR - 4 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 5 * 2 ^ 17)%Z in RM5 by lia.
  assert (KEPT4 : Forall (ex_region_kept E4 M4 m5) [(EVar 32, OFF4, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 40%Z); (EVar 135, 0%Z, 24%Z); (EVar 169, 0%Z, 24%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF4 1312 M4 m5 E4 (EVar 32) CK (proj1 PMc4) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 M4 _ M4 m5 E4 (EVar 67) sel 32 CK HWs4 Lsel_a4 RRsel eq_refl (proj2 PMc4) Lsel_a4 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 M4 _ M4 m5 E4 (EVar 101) arr 40 CK HWs4 Larr_a4 RRarr eq_refl (proj2 PMc4) Larr_a4 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 M4 _ M4 m5 E4 (EVar 135) row0 24 CK HWs4 Lrow0_a4 RRrow0 eq_refl (proj2 PMc4) Lrow0_a4 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 M4 _ M4 m5 E4 (EVar 169) row1 24 CK HWs4 Lrow1_a4 RRrow1 eq_refl (proj2 PMc4) Lrow1_a4 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E4 M4 m5 _ [] _ HKc4 KEPT4) as HKk4.
  match type of HKk4 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E4 m5 kk') in HKk4 end.
  pose proof (regs_ok_agree 171%nat E4 (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) _ _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa4.
  pose proof (exW_regs_call _ _ _ _ _ HRa4 (ex_regs_ok_junk vals4 r5 [row2; exW_canary SEGS 1410112 m5] 171%nat ltac:(vm_cast_no_check (eq_refl 171%nat))) CS4) as HRn5.
  clear HRa4.
  assert (HKa5 : know_ok SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5 _) by (exact (know_ok_agree SEGS 171%nat E4 _ m5 _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk4)).
  rewrite (fr_denot_agree 171%nat E4 (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) _ fr (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r5 ex_r10 (EVar 203) HRn5 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres4)) as HRx5. clear HRn5. rename HRx5 into HRn5.
  clear HR HK Hlf Hms HKc4 HKk4 KEPT4 HC4 HWs4 PMs4 Q10_4 Q11_4 Q1_4 Q2_4 Q4_4 PM4 HW4 PMc4 CS4 SUB4 RM4 MG4 TOP4 LEQ4 Hnz4 Frow2x Lo4 OFF4 LDEL4 Lsel_a4 Larr_a4 Lrow0_a4 Lrow1_a4.
  subst M4. clear log4. clear E4. try clear Rc4. clear KN4.
  lazymatch type of HRn5 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn5 end.
  pose proof (exW_kn_blk SEGS C A5 m5 _ (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) (EVar 203) (EVar 32) row2 24 s 1312 65536 1347584 p16_segs CK HW5 Lrow2_a5 RRrow2 eq_refl eq_refl eq_refl RS ALrow2 ZERO4 WAProw2 IMGAProw2) as HKb5.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5) _ _ (ex_kdisj_apart SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5 (EVar 67) (EVar 203) sel row2 0 32 0 24 eq_refl eq_refl RRsel RRrow2 AP_sel_row2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5) _ _ (ex_kdisj_apart SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5 (EVar 101) (EVar 203) arr row2 0 40 0 24 eq_refl eq_refl RRarr RRrow2 AP_arr_row2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5) _ _ (ex_kdisj_apart SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5 (EVar 135) (EVar 203) row0 row2 0 24 0 24 eq_refl eq_refl RRrow0 RRrow2 AP_row0_row2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5) _ _ (ex_kdisj_apart SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5 (EVar 169) (EVar 203) row1 row2 0 24 0 24 eq_refl eq_refl RRrow1 RRrow2 AP_row1_row2) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5)))))) as HKd5.
  pose proof (W_sok_win C A5 m5 _ (s - 1312) (Z.to_nat 1312) CK HW5 GLO1 GLO2) as SOK5.
  pose proof (exW_canary_ok SEGS 1410112 m5 (canary_any m5)) as CANOK5.
  pose (vals5 := vals4 ++ map (getr r5) ex_regs_list ++ map (Z_to_bv 64) [row2; exW_canary SEGS 1410112 m5]).
  pose proof (exW_kn_fixed SEGS C A5 m5 _ (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) (EVar 204) (EVar 32) (exW_canary SEGS 1410112 m5) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW5 eq_refl (proj1 CANOK5) (proj2 CANOK5) eq_refl eq_refl eq_refl SOK5 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf5.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb5 (proj2 (Forall_app _ _ _) (conj HKd5 (proj2 (Forall_app _ _ _) (conj HKf5 HKa5)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn5 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN5 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb5 HKd5 HKf5 HKa5 SOK5 CANOK5.
  repeat match goal with H : getr r5 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO4 ALrow2.
  exb_exit ST Rc5 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E5 := EEx) in HR, Hlf, HK, Hms |- *; set (log5 := LLx) in Hms, Hlf; set (M5 := mem_denot E5 m5 log5) in Hms end.
  assert (WP5 : W C A5 M5 (with_vmmaps vm5 md) /\ POSTM C A0 s m5 M5).
  { subst M5. apply (exW_win_blks C A5 A0 m5 _ E5 log5 (EVar 32) s 1312 [(EVar 67, sel, 32%Z); (EVar 101, arr, 40%Z); (EVar 135, row0, 24%Z); (EVar 169, row1, 24%Z); (EVar 203, row2, 24%Z)] CK HW5 SUB5 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel (conj Lsel_a5 (conj Fsel F0sel))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a5 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRrow0 (conj Lrow0_a5 (conj Frow0 F0row0))))|]. constructor; [exact (conj eq_refl (conj RRrow1 (conj Lrow1_a5 (conj Frow1 F0row1))))|]. constructor; [exact (conj eq_refl (conj RRrow2 (conj Lrow2_a5 (conj Frow2 F0row2))))|]. constructor. }
  destruct WP5 as [HWs5 PMs5].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log5 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC5 : carry log5 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc5 : know_ok SEGS E5 M5 kn1) by (apply (carry_after SEGS E5 m5 log5 kn0 [] kn1 scs hs HC5 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact Hms |].
  pose (BS5 := [(32%nat, s); (67%nat, sel); (101%nat, arr); (135%nat, row0); (169%nat, row1); (203%nat, row2)]).
  exW_regfactB BS5 HR ex_r10 Q10_5. exW_regfactB BS5 HR ex_r11 Q11_5. exW_regfactB BS5 HR ex_r1 Q1_5. exW_regfactB BS5 HR ex_r2 Q2_5. exW_regfactB BS5 HR ex_r4 Q4_5.
  clear BS5.
  lazymatch type of Q2_5 with _ = Z_to_bv 64 (s + ?off) => pose (OFF5 := off) end.
  pose proof (alloc_margin_small (6 * 4) ltac:(exW_cmp)) as MG5.
  lazymatch type of Q1_5 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_5 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A5 M5 _ Rc5 6 4 (kR - 5) (bR - 5 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs5 Q10_5 Q11_5 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM5) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_5
             ltac:(red; apply bv_eq; reflexivity) Q4_5 Q2_5 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A6 m6 vm6 r6 res5 HW6 Hres5 CSx5 Hnz5 Frow3x Lo5 F0row3 LEQ5 ZERO5 ALrow3 TOP5 PMc5 RM6.
  pose proof CSx5 as CS5. clear CSx5.
  rewrite with_vmmaps_twice in HW6 |- *.
  assert (Eres5 : res5 = Z_to_bv 64 (u res5)) by (symmetry; apply zbv_self).
  pose proof (u64_range res5) as RRrow3. set (row3 := u res5) in *. clearbody row3. rewrite Eres5 in Hres5, Frow3x, Lo5, F0row3, LEQ5, ZERO5. clear Eres5.
  change (6 * 4)%Z with 24%Z in *.
  pose proof (exW_blk_img_apart_h2 C A6 m6 _ row3 24 CK HW6 Lo5 RRrow3 eq_refl eq_refl) as IMGAProw3. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAProw3.
  pose proof (exW_win_blk_apart_h C A6 m6 _ s 1312 row3 24 CK HW6 Lo5 eq_refl RRrow3 GLO1) as WAProw3.
  assert (Frow3 : live A0 (Z_to_bv 64 row3) = None).
  { destruct (live A0 (Z_to_bv 64 row3)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB5 _ _ EE) as XX. first [discriminate Frow3x | (rewrite Frow3x in XX; discriminate XX)]. }
  pose proof Lo5 as Lrow3_a6.
  assert (SUB6 : sub_live A0 A6).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row3) by (intros ->; rewrite Frow3 in Lq; discriminate Lq). rewrite (LEQ5 q NEq). exact (SUB5 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row3 :: [Z_to_bv 64 row2; Z_to_bv 64 row1; Z_to_bv 64 row0; Z_to_bv 64 arr; Z_to_bv 64 sel])) => eq_trans (LEQ5 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL5 q (fun XX => Hq (or_intror XX)))) as LDEL6.
  assert (NE_sel_row3 : Z_to_bv 64 sel <> Z_to_bv 64 row3) by (intros EE; rewrite EE in Lsel_a5; rewrite Frow3x in Lsel_a5; discriminate Lsel_a5).
  assert (Lsel_a6 : live A6 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ5 _ NE_sel_row3); exact Lsel_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ sel row3 32 24 CK HW6 Lsel_a6 Lrow3_a6 NE_sel_row3 RRsel RRrow3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel_row3.
  assert (NE_arr_row3 : Z_to_bv 64 arr <> Z_to_bv 64 row3) by (intros EE; rewrite EE in Larr_a5; rewrite Frow3x in Larr_a5; discriminate Larr_a5).
  assert (Larr_a6 : live A6 (Z_to_bv 64 arr) = Some 40%Z) by (rewrite (LEQ5 _ NE_arr_row3); exact Larr_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ arr row3 40 24 CK HW6 Larr_a6 Lrow3_a6 NE_arr_row3 RRarr RRrow3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_row3.
  assert (NE_row0_row3 : Z_to_bv 64 row0 <> Z_to_bv 64 row3) by (intros EE; rewrite EE in Lrow0_a5; rewrite Frow3x in Lrow0_a5; discriminate Lrow0_a5).
  assert (Lrow0_a6 : live A6 (Z_to_bv 64 row0) = Some 24%Z) by (rewrite (LEQ5 _ NE_row0_row3); exact Lrow0_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ row0 row3 24 24 CK HW6 Lrow0_a6 Lrow3_a6 NE_row0_row3 RRrow0 RRrow3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row0_row3.
  assert (NE_row1_row3 : Z_to_bv 64 row1 <> Z_to_bv 64 row3) by (intros EE; rewrite EE in Lrow1_a5; rewrite Frow3x in Lrow1_a5; discriminate Lrow1_a5).
  assert (Lrow1_a6 : live A6 (Z_to_bv 64 row1) = Some 24%Z) by (rewrite (LEQ5 _ NE_row1_row3); exact Lrow1_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ row1 row3 24 24 CK HW6 Lrow1_a6 Lrow3_a6 NE_row1_row3 RRrow1 RRrow3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row1_row3.
  assert (NE_row2_row3 : Z_to_bv 64 row2 <> Z_to_bv 64 row3) by (intros EE; rewrite EE in Lrow2_a5; rewrite Frow3x in Lrow2_a5; discriminate Lrow2_a5).
  assert (Lrow2_a6 : live A6 (Z_to_bv 64 row2) = Some 24%Z) by (rewrite (LEQ5 _ NE_row2_row3); exact Lrow2_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ row2 row3 24 24 CK HW6 Lrow2_a6 Lrow3_a6 NE_row2_row3 RRrow2 RRrow3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row2_row3.
  assert (PM6 : POSTM C A0 s m0 m6).
  { eapply POSTM_trans; [exact PM5|]. eapply POSTM_trans; [exact PMs5|]. apply (POSTM_sub C A0 A5 _ _ _ SUB5).
    apply (POSTM_mono C A5 (s + OFF5) s); [unfold OFF5; lia | exact PMc5]. }
  replace (kR - 5 - 1)%Z with (kR - 6)%Z in RM6 by lia. rewrite MG5 in RM6. replace (bR - 5 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 6 * 2 ^ 17)%Z in RM6 by lia.
  assert (KEPT5 : Forall (ex_region_kept E5 M5 m6) [(EVar 32, OFF5, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 40%Z); (EVar 135, 0%Z, 24%Z); (EVar 169, 0%Z, 24%Z); (EVar 203, 0%Z, 24%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF5 1312 M5 m6 E5 (EVar 32) CK (proj1 PMc5) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 67) sel 32 CK HWs5 Lsel_a5 RRsel eq_refl (proj2 PMc5) Lsel_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 101) arr 40 CK HWs5 Larr_a5 RRarr eq_refl (proj2 PMc5) Larr_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 135) row0 24 CK HWs5 Lrow0_a5 RRrow0 eq_refl (proj2 PMc5) Lrow0_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 169) row1 24 CK HWs5 Lrow1_a5 RRrow1 eq_refl (proj2 PMc5) Lrow1_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 203) row2 24 CK HWs5 Lrow2_a5 RRrow2 eq_refl (proj2 PMc5) Lrow2_a5 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E5 M5 m6 _ [] _ HKc5 KEPT5) as HKk5.
  match type of HKk5 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E5 m6 kk') in HKk5 end.
  pose proof (regs_ok_agree 205%nat E5 (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) _ _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa5.
  pose proof (exW_regs_call _ _ _ _ _ HRa5 (ex_regs_ok_junk vals5 r6 [row3; exW_canary SEGS 1410112 m6] 205%nat ltac:(vm_cast_no_check (eq_refl 205%nat))) CS5) as HRn6.
  clear HRa5.
  assert (HKa6 : know_ok SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6 _) by (exact (know_ok_agree SEGS 205%nat E5 _ m6 _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk5)).
  rewrite (fr_denot_agree 205%nat E5 (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) _ fr (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r6 ex_r10 (EVar 237) HRn6 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres5)) as HRx6. clear HRn6. rename HRx6 into HRn6.
  clear HR HK Hlf Hms HKc5 HKk5 KEPT5 HC5 HWs5 PMs5 Q10_5 Q11_5 Q1_5 Q2_5 Q4_5 PM5 HW5 PMc5 CS5 SUB5 RM5 MG5 TOP5 LEQ5 Hnz5 Frow3x Lo5 OFF5 LDEL5 Lsel_a5 Larr_a5 Lrow0_a5 Lrow1_a5 Lrow2_a5.
  subst M5. clear log5. clear E5. try clear Rc5. clear KN5.
  lazymatch type of HRn6 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn6 end.
  pose proof (exW_kn_blk SEGS C A6 m6 _ (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) (EVar 237) (EVar 32) row3 24 s 1312 65536 1347584 p16_segs CK HW6 Lrow3_a6 RRrow3 eq_refl eq_refl eq_refl RS ALrow3 ZERO5 WAProw3 IMGAProw3) as HKb6.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6 (EVar 67) (EVar 237) sel row3 0 32 0 24 eq_refl eq_refl RRsel RRrow3 AP_sel_row3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6 (EVar 101) (EVar 237) arr row3 0 40 0 24 eq_refl eq_refl RRarr RRrow3 AP_arr_row3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6 (EVar 135) (EVar 237) row0 row3 0 24 0 24 eq_refl eq_refl RRrow0 RRrow3 AP_row0_row3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6 (EVar 169) (EVar 237) row1 row3 0 24 0 24 eq_refl eq_refl RRrow1 RRrow3 AP_row1_row3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6 (EVar 203) (EVar 237) row2 row3 0 24 0 24 eq_refl eq_refl RRrow2 RRrow3 AP_row2_row3) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6))))))) as HKd6.
  pose proof (W_sok_win C A6 m6 _ (s - 1312) (Z.to_nat 1312) CK HW6 GLO1 GLO2) as SOK6.
  pose proof (exW_canary_ok SEGS 1410112 m6 (canary_any m6)) as CANOK6.
  pose (vals6 := vals5 ++ map (getr r6) ex_regs_list ++ map (Z_to_bv 64) [row3; exW_canary SEGS 1410112 m6]).
  pose proof (exW_kn_fixed SEGS C A6 m6 _ (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) (EVar 238) (EVar 32) (exW_canary SEGS 1410112 m6) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW6 eq_refl (proj1 CANOK6) (proj2 CANOK6) eq_refl eq_refl eq_refl SOK6 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf6.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb6 (proj2 (Forall_app _ _ _) (conj HKd6 (proj2 (Forall_app _ _ _) (conj HKf6 HKa6)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn6 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN6 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb6 HKd6 HKf6 HKa6 SOK6 CANOK6.
  repeat match goal with H : getr r6 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO5 ALrow3.
  exb_exit ST Rc6 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E6 := EEx) in HR, Hlf, HK, Hms |- *; set (log6 := LLx) in Hms, Hlf; set (M6 := mem_denot E6 m6 log6) in Hms end.
  assert (WP6 : W C A6 M6 (with_vmmaps vm6 md) /\ POSTM C A0 s m6 M6).
  { subst M6. apply (exW_win_blks C A6 A0 m6 _ E6 log6 (EVar 32) s 1312 [(EVar 67, sel, 32%Z); (EVar 101, arr, 40%Z); (EVar 135, row0, 24%Z); (EVar 169, row1, 24%Z); (EVar 203, row2, 24%Z); (EVar 237, row3, 24%Z)] CK HW6 SUB6 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel (conj Lsel_a6 (conj Fsel F0sel))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a6 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRrow0 (conj Lrow0_a6 (conj Frow0 F0row0))))|]. constructor; [exact (conj eq_refl (conj RRrow1 (conj Lrow1_a6 (conj Frow1 F0row1))))|]. constructor; [exact (conj eq_refl (conj RRrow2 (conj Lrow2_a6 (conj Frow2 F0row2))))|]. constructor; [exact (conj eq_refl (conj RRrow3 (conj Lrow3_a6 (conj Frow3 F0row3))))|]. constructor. }
  destruct WP6 as [HWs6 PMs6].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log6 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC6 : carry log6 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc6 : know_ok SEGS E6 M6 kn1) by (apply (carry_after SEGS E6 m6 log6 kn0 [] kn1 scs hs HC6 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact Hms |].
  pose (BS6 := [(32%nat, s); (67%nat, sel); (101%nat, arr); (135%nat, row0); (169%nat, row1); (203%nat, row2); (237%nat, row3)]).
  exW_regfactB BS6 HR ex_r10 Q10_6. exW_regfactB BS6 HR ex_r11 Q11_6. exW_regfactB BS6 HR ex_r1 Q1_6. exW_regfactB BS6 HR ex_r2 Q2_6. exW_regfactB BS6 HR ex_r4 Q4_6.
  clear BS6.
  lazymatch type of Q2_6 with _ = Z_to_bv 64 (s + ?off) => pose (OFF6 := off) end.
  pose proof (alloc_margin_small (6 * 4) ltac:(exW_cmp)) as MG6.
  lazymatch type of Q1_6 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_6 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A6 M6 _ Rc6 6 4 (kR - 6) (bR - 6 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs6 Q10_6 Q11_6 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM6) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_6
             ltac:(red; apply bv_eq; reflexivity) Q4_6 Q2_6 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A7 m7 vm7 r7 res6 HW7 Hres6 CSx6 Hnz6 Frow4x Lo6 F0row4 LEQ6 ZERO6 ALrow4 TOP6 PMc6 RM7.
  pose proof CSx6 as CS6. clear CSx6.
  rewrite with_vmmaps_twice in HW7 |- *.
  assert (Eres6 : res6 = Z_to_bv 64 (u res6)) by (symmetry; apply zbv_self).
  pose proof (u64_range res6) as RRrow4. set (row4 := u res6) in *. clearbody row4. rewrite Eres6 in Hres6, Frow4x, Lo6, F0row4, LEQ6, ZERO6. clear Eres6.
  change (6 * 4)%Z with 24%Z in *.
  pose proof (exW_blk_img_apart_h2 C A7 m7 _ row4 24 CK HW7 Lo6 RRrow4 eq_refl eq_refl) as IMGAProw4. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAProw4.
  pose proof (exW_win_blk_apart_h C A7 m7 _ s 1312 row4 24 CK HW7 Lo6 eq_refl RRrow4 GLO1) as WAProw4.
  assert (Frow4 : live A0 (Z_to_bv 64 row4) = None).
  { destruct (live A0 (Z_to_bv 64 row4)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB6 _ _ EE) as XX. first [discriminate Frow4x | (rewrite Frow4x in XX; discriminate XX)]. }
  pose proof Lo6 as Lrow4_a7.
  assert (SUB7 : sub_live A0 A7).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row4) by (intros ->; rewrite Frow4 in Lq; discriminate Lq). rewrite (LEQ6 q NEq). exact (SUB6 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row4 :: [Z_to_bv 64 row3; Z_to_bv 64 row2; Z_to_bv 64 row1; Z_to_bv 64 row0; Z_to_bv 64 arr; Z_to_bv 64 sel])) => eq_trans (LEQ6 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL6 q (fun XX => Hq (or_intror XX)))) as LDEL7.
  assert (NE_sel_row4 : Z_to_bv 64 sel <> Z_to_bv 64 row4) by (intros EE; rewrite EE in Lsel_a6; rewrite Frow4x in Lsel_a6; discriminate Lsel_a6).
  assert (Lsel_a7 : live A7 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ6 _ NE_sel_row4); exact Lsel_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ sel row4 32 24 CK HW7 Lsel_a7 Lrow4_a7 NE_sel_row4 RRsel RRrow4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel_row4.
  assert (NE_arr_row4 : Z_to_bv 64 arr <> Z_to_bv 64 row4) by (intros EE; rewrite EE in Larr_a6; rewrite Frow4x in Larr_a6; discriminate Larr_a6).
  assert (Larr_a7 : live A7 (Z_to_bv 64 arr) = Some 40%Z) by (rewrite (LEQ6 _ NE_arr_row4); exact Larr_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ arr row4 40 24 CK HW7 Larr_a7 Lrow4_a7 NE_arr_row4 RRarr RRrow4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_row4.
  assert (NE_row0_row4 : Z_to_bv 64 row0 <> Z_to_bv 64 row4) by (intros EE; rewrite EE in Lrow0_a6; rewrite Frow4x in Lrow0_a6; discriminate Lrow0_a6).
  assert (Lrow0_a7 : live A7 (Z_to_bv 64 row0) = Some 24%Z) by (rewrite (LEQ6 _ NE_row0_row4); exact Lrow0_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ row0 row4 24 24 CK HW7 Lrow0_a7 Lrow4_a7 NE_row0_row4 RRrow0 RRrow4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row0_row4.
  assert (NE_row1_row4 : Z_to_bv 64 row1 <> Z_to_bv 64 row4) by (intros EE; rewrite EE in Lrow1_a6; rewrite Frow4x in Lrow1_a6; discriminate Lrow1_a6).
  assert (Lrow1_a7 : live A7 (Z_to_bv 64 row1) = Some 24%Z) by (rewrite (LEQ6 _ NE_row1_row4); exact Lrow1_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ row1 row4 24 24 CK HW7 Lrow1_a7 Lrow4_a7 NE_row1_row4 RRrow1 RRrow4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row1_row4.
  assert (NE_row2_row4 : Z_to_bv 64 row2 <> Z_to_bv 64 row4) by (intros EE; rewrite EE in Lrow2_a6; rewrite Frow4x in Lrow2_a6; discriminate Lrow2_a6).
  assert (Lrow2_a7 : live A7 (Z_to_bv 64 row2) = Some 24%Z) by (rewrite (LEQ6 _ NE_row2_row4); exact Lrow2_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ row2 row4 24 24 CK HW7 Lrow2_a7 Lrow4_a7 NE_row2_row4 RRrow2 RRrow4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row2_row4.
  assert (NE_row3_row4 : Z_to_bv 64 row3 <> Z_to_bv 64 row4) by (intros EE; rewrite EE in Lrow3_a6; rewrite Frow4x in Lrow3_a6; discriminate Lrow3_a6).
  assert (Lrow3_a7 : live A7 (Z_to_bv 64 row3) = Some 24%Z) by (rewrite (LEQ6 _ NE_row3_row4); exact Lrow3_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ row3 row4 24 24 CK HW7 Lrow3_a7 Lrow4_a7 NE_row3_row4 RRrow3 RRrow4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row3_row4.
  assert (PM7 : POSTM C A0 s m0 m7).
  { eapply POSTM_trans; [exact PM6|]. eapply POSTM_trans; [exact PMs6|]. apply (POSTM_sub C A0 A6 _ _ _ SUB6).
    apply (POSTM_mono C A6 (s + OFF6) s); [unfold OFF6; lia | exact PMc6]. }
  replace (kR - 6 - 1)%Z with (kR - 7)%Z in RM7 by lia. rewrite MG6 in RM7. replace (bR - 6 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 7 * 2 ^ 17)%Z in RM7 by lia.
  assert (KEPT6 : Forall (ex_region_kept E6 M6 m7) [(EVar 32, OFF6, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 40%Z); (EVar 135, 0%Z, 24%Z); (EVar 169, 0%Z, 24%Z); (EVar 203, 0%Z, 24%Z); (EVar 237, 0%Z, 24%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF6 1312 M6 m7 E6 (EVar 32) CK (proj1 PMc6) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 67) sel 32 CK HWs6 Lsel_a6 RRsel eq_refl (proj2 PMc6) Lsel_a6 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 101) arr 40 CK HWs6 Larr_a6 RRarr eq_refl (proj2 PMc6) Larr_a6 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 135) row0 24 CK HWs6 Lrow0_a6 RRrow0 eq_refl (proj2 PMc6) Lrow0_a6 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 169) row1 24 CK HWs6 Lrow1_a6 RRrow1 eq_refl (proj2 PMc6) Lrow1_a6 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 203) row2 24 CK HWs6 Lrow2_a6 RRrow2 eq_refl (proj2 PMc6) Lrow2_a6 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 237) row3 24 CK HWs6 Lrow3_a6 RRrow3 eq_refl (proj2 PMc6) Lrow3_a6 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E6 M6 m7 _ [] _ HKc6 KEPT6) as HKk6.
  match type of HKk6 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E6 m7 kk') in HKk6 end.
  pose proof (regs_ok_agree 239%nat E6 (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) _ _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa6.
  pose proof (exW_regs_call _ _ _ _ _ HRa6 (ex_regs_ok_junk vals6 r7 [row4; exW_canary SEGS 1410112 m7] 239%nat ltac:(vm_cast_no_check (eq_refl 239%nat))) CS6) as HRn7.
  clear HRa6.
  assert (HKa7 : know_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7 _) by (exact (know_ok_agree SEGS 239%nat E6 _ m7 _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk6)).
  rewrite (fr_denot_agree 239%nat E6 (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) _ fr (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r7 ex_r10 (EVar 271) HRn7 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres6)) as HRx7. clear HRn7. rename HRx7 into HRn7.
  clear HR HK Hlf Hms HKc6 HKk6 KEPT6 HC6 HWs6 PMs6 Q10_6 Q11_6 Q1_6 Q2_6 Q4_6 PM6 HW6 PMc6 CS6 SUB6 RM6 MG6 TOP6 LEQ6 Hnz6 Frow4x Lo6 OFF6 LDEL6 Lsel_a6 Larr_a6 Lrow0_a6 Lrow1_a6 Lrow2_a6 Lrow3_a6.
  subst M6. clear log6. clear E6. try clear Rc6. clear KN6.
  lazymatch type of HRn7 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn7 end.
  pose proof (exW_kn_blk SEGS C A7 m7 _ (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) (EVar 271) (EVar 32) row4 24 s 1312 65536 1347584 p16_segs CK HW7 Lrow4_a7 RRrow4 eq_refl eq_refl eq_refl RS ALrow4 ZERO6 WAProw4 IMGAProw4) as HKb7.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7 (EVar 67) (EVar 271) sel row4 0 32 0 24 eq_refl eq_refl RRsel RRrow4 AP_sel_row4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7 (EVar 101) (EVar 271) arr row4 0 40 0 24 eq_refl eq_refl RRarr RRrow4 AP_arr_row4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7 (EVar 135) (EVar 271) row0 row4 0 24 0 24 eq_refl eq_refl RRrow0 RRrow4 AP_row0_row4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7 (EVar 169) (EVar 271) row1 row4 0 24 0 24 eq_refl eq_refl RRrow1 RRrow4 AP_row1_row4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7 (EVar 203) (EVar 271) row2 row4 0 24 0 24 eq_refl eq_refl RRrow2 RRrow4 AP_row2_row4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7 (EVar 237) (EVar 271) row3 row4 0 24 0 24 eq_refl eq_refl RRrow3 RRrow4 AP_row3_row4) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7)))))))) as HKd7.
  pose proof (W_sok_win C A7 m7 _ (s - 1312) (Z.to_nat 1312) CK HW7 GLO1 GLO2) as SOK7.
  pose proof (exW_canary_ok SEGS 1410112 m7 (canary_any m7)) as CANOK7.
  pose (vals7 := vals6 ++ map (getr r7) ex_regs_list ++ map (Z_to_bv 64) [row4; exW_canary SEGS 1410112 m7]).
  pose proof (exW_kn_fixed SEGS C A7 m7 _ (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) (EVar 272) (EVar 32) (exW_canary SEGS 1410112 m7) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW7 eq_refl (proj1 CANOK7) (proj2 CANOK7) eq_refl eq_refl eq_refl SOK7 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf7.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb7 (proj2 (Forall_app _ _ _) (conj HKd7 (proj2 (Forall_app _ _ _) (conj HKf7 HKa7)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn7 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN7 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb7 HKd7 HKf7 HKa7 SOK7 CANOK7.
  repeat match goal with H : getr r7 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO6 ALrow4.
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E7 := EEx) in HR, Hlf, HK, Hms |- *; set (log7 := LLx) in Hms, Hlf; set (M7 := mem_denot E7 m7 log7) in Hms end.
  assert (WP7 : W C A7 M7 (with_vmmaps vm7 md) /\ POSTM C A0 s m7 M7).
  { subst M7. apply (exW_win_blks C A7 A0 m7 _ E7 log7 (EVar 32) s 1312 [(EVar 67, sel, 32%Z); (EVar 101, arr, 40%Z); (EVar 135, row0, 24%Z); (EVar 169, row1, 24%Z); (EVar 203, row2, 24%Z); (EVar 237, row3, 24%Z); (EVar 271, row4, 24%Z)] CK HW7 SUB7 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel (conj Lsel_a7 (conj Fsel F0sel))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a7 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRrow0 (conj Lrow0_a7 (conj Frow0 F0row0))))|]. constructor; [exact (conj eq_refl (conj RRrow1 (conj Lrow1_a7 (conj Frow1 F0row1))))|]. constructor; [exact (conj eq_refl (conj RRrow2 (conj Lrow2_a7 (conj Frow2 F0row2))))|]. constructor; [exact (conj eq_refl (conj RRrow3 (conj Lrow3_a7 (conj Frow3 F0row3))))|]. constructor; [exact (conj eq_refl (conj RRrow4 (conj Lrow4_a7 (conj Frow4 F0row4))))|]. constructor. }
  destruct WP7 as [HWs7 PMs7].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact Hms |].
  pose (BSF := [(32%nat, s); (67%nat, sel); (101%nat, arr); (135%nat, row0); (169%nat, row1); (203%nat, row2); (237%nat, row3); (271%nat, row4)]).
  exW_regfactB BSF HR ex_r10 G10.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel 0%Z 4%nat Csel_0.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel 4%Z 4%nat Csel_4.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel 8%Z 4%nat Csel_8.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel 12%Z 4%nat Csel_12.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel 16%Z 8%nat Csel_16.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel 24%Z 8%nat Csel_24.
  exW_cellB HK Hlf r0 BSF (EVar 101) arr 0%Z 8%nat Carr_0.
  exW_cellB HK Hlf r0 BSF (EVar 101) arr 8%Z 8%nat Carr_8.
  exW_cellB HK Hlf r0 BSF (EVar 101) arr 16%Z 8%nat Carr_16.
  exW_cellB HK Hlf r0 BSF (EVar 101) arr 24%Z 8%nat Carr_24.
  exW_cellB HK Hlf r0 BSF (EVar 101) arr 32%Z 8%nat Carr_32.
  exW_cellB HK Hlf r0 BSF (EVar 135) row0 0%Z 4%nat Crow0_0.
  exW_cellB HK Hlf r0 BSF (EVar 135) row0 4%Z 4%nat Crow0_4.
  exW_cellB HK Hlf r0 BSF (EVar 135) row0 8%Z 4%nat Crow0_8.
  exW_cellB HK Hlf r0 BSF (EVar 135) row0 12%Z 4%nat Crow0_12.
  exW_cellB HK Hlf r0 BSF (EVar 135) row0 16%Z 4%nat Crow0_16.
  exW_cellB HK Hlf r0 BSF (EVar 135) row0 20%Z 4%nat Crow0_20.
  exW_cellB HK Hlf r0 BSF (EVar 169) row1 0%Z 4%nat Crow1_0.
  exW_cellB HK Hlf r0 BSF (EVar 169) row1 4%Z 4%nat Crow1_4.
  exW_cellB HK Hlf r0 BSF (EVar 169) row1 8%Z 4%nat Crow1_8.
  exW_cellB HK Hlf r0 BSF (EVar 169) row1 12%Z 4%nat Crow1_12.
  exW_cellB HK Hlf r0 BSF (EVar 169) row1 16%Z 4%nat Crow1_16.
  exW_cellB HK Hlf r0 BSF (EVar 169) row1 20%Z 4%nat Crow1_20.
  exW_cellB HK Hlf r0 BSF (EVar 203) row2 0%Z 4%nat Crow2_0.
  exW_cellB HK Hlf r0 BSF (EVar 203) row2 4%Z 4%nat Crow2_4.
  exW_cellB HK Hlf r0 BSF (EVar 203) row2 8%Z 4%nat Crow2_8.
  exW_cellB HK Hlf r0 BSF (EVar 203) row2 12%Z 4%nat Crow2_12.
  exW_cellB HK Hlf r0 BSF (EVar 203) row2 16%Z 4%nat Crow2_16.
  exW_cellB HK Hlf r0 BSF (EVar 203) row2 20%Z 4%nat Crow2_20.
  exW_cellB HK Hlf r0 BSF (EVar 237) row3 0%Z 4%nat Crow3_0.
  exW_cellB HK Hlf r0 BSF (EVar 237) row3 4%Z 4%nat Crow3_4.
  exW_cellB HK Hlf r0 BSF (EVar 237) row3 8%Z 4%nat Crow3_8.
  exW_cellB HK Hlf r0 BSF (EVar 237) row3 12%Z 4%nat Crow3_12.
  exW_cellB HK Hlf r0 BSF (EVar 237) row3 16%Z 4%nat Crow3_16.
  exW_cellB HK Hlf r0 BSF (EVar 237) row3 20%Z 4%nat Crow3_20.
  exW_cellB HK Hlf r0 BSF (EVar 271) row4 0%Z 4%nat Crow4_0.
  exW_cellB HK Hlf r0 BSF (EVar 271) row4 4%Z 4%nat Crow4_4.
  exW_cellB HK Hlf r0 BSF (EVar 271) row4 8%Z 4%nat Crow4_8.
  exW_cellB HK Hlf r0 BSF (EVar 271) row4 12%Z 4%nat Crow4_12.
  exW_cellB HK Hlf r0 BSF (EVar 271) row4 16%Z 4%nat Crow4_16.
  exW_cellB HK Hlf r0 BSF (EVar 271) row4 20%Z 4%nat Crow4_20.
  refine (HC A7 M7 vm7 RcF sel arr row0 row1 row2 row3 row4 HWs7 _ SUB7 (POSTM_trans _ _ _ _ _ _ PM7 PMs7) RM7 LDEL7 G10
            Lsel_a7 Fsel F0sel RRsel Larr_a7 Farr F0arr RRarr Lrow0_a7 Frow0 F0row0 RRrow0 Lrow1_a7 Frow1 F0row1 RRrow1 Lrow2_a7 Frow2 F0row2 RRrow2 Lrow3_a7 Frow3 F0row3 RRrow3 Lrow4_a7 Frow4 F0row4 RRrow4
            NE_sel_arr NE_sel_row0 NE_arr_row0 NE_sel_row1 NE_arr_row1 NE_row0_row1 NE_sel_row2 NE_arr_row2 NE_row0_row2 NE_row1_row2 NE_sel_row3 NE_arr_row3 NE_row0_row3 NE_row1_row3 NE_row2_row3 NE_sel_row4 NE_arr_row4 NE_row0_row4 NE_row1_row4 NE_row2_row4 NE_row3_row4
            Csel_0 Csel_4 Csel_8 Csel_12 Csel_16 Csel_24 Carr_0 Carr_8 Carr_16 Carr_24 Carr_32 Crow0_0 Crow0_4 Crow0_8 Crow0_12 Crow0_16 Crow0_20 Crow1_0 Crow1_4 Crow1_8 Crow1_12 Crow1_16 Crow1_20 Crow2_0 Crow2_4 Crow2_8 Crow2_12 Crow2_16 Crow2_20 Crow3_0 Crow3_4 Crow3_8 Crow3_12 Crow3_16 Crow3_20 Crow4_0 Crow4_4 Crow4_8 Crow4_12 Crow4_16 Crow4_20).
  lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 RcF [(2%nat, EVar 32); (4%nat, ELit 1278416)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor; [symmetry; exact HTP | constructor]] | vm_compute; reflexivity] end.
Qed.

(* [comment removed for export] *)
Lemma selstr_chain2 : forall (fx : FPState) C A m md regs (s : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELSTR_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 1278416 ->
  getr regs 10 = Z_to_bv 64 68632 -> getr regs 11 = Z_to_bv 64 5 -> getr regs 12 = Z_to_bv 64 6 -> getr regs 13 = Z_to_bv 64 0 ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (7 <= kR)%Z -> (7 * 2 ^ 17 <= bR)%Z ->
  (forall A' m' vm' regs' (sel arr row0 row1 row2 row3 row4 : Z),
     W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> sub_live A A' -> POSTM C A s m m' ->
     aroom A' vm' (kR - 7) (bR - 7 * 2 ^ 17) ->
     (forall q : word, ~ In q [Z_to_bv 64 row4; Z_to_bv 64 row3; Z_to_bv 64 row2; Z_to_bv 64 row1; Z_to_bv 64 row0; Z_to_bv 64 arr; Z_to_bv 64 sel] -> live A' q = live A q) ->
     getr regs' 10 = Z_to_bv 64 sel ->
     live A' (Z_to_bv 64 sel) = Some 32%Z -> live A (Z_to_bv 64 sel) = None -> live (c_A0 C) (Z_to_bv 64 sel) = None -> (0 <= sel < 2 ^ 64)%Z ->
     live A' (Z_to_bv 64 arr) = Some 40%Z -> live A (Z_to_bv 64 arr) = None -> live (c_A0 C) (Z_to_bv 64 arr) = None -> (0 <= arr < 2 ^ 64)%Z ->
     live A' (Z_to_bv 64 row0) = Some 24%Z -> live A (Z_to_bv 64 row0) = None -> live (c_A0 C) (Z_to_bv 64 row0) = None -> (0 <= row0 < 2 ^ 64)%Z ->
     live A' (Z_to_bv 64 row1) = Some 24%Z -> live A (Z_to_bv 64 row1) = None -> live (c_A0 C) (Z_to_bv 64 row1) = None -> (0 <= row1 < 2 ^ 64)%Z ->
     live A' (Z_to_bv 64 row2) = Some 24%Z -> live A (Z_to_bv 64 row2) = None -> live (c_A0 C) (Z_to_bv 64 row2) = None -> (0 <= row2 < 2 ^ 64)%Z ->
     live A' (Z_to_bv 64 row3) = Some 24%Z -> live A (Z_to_bv 64 row3) = None -> live (c_A0 C) (Z_to_bv 64 row3) = None -> (0 <= row3 < 2 ^ 64)%Z ->
     live A' (Z_to_bv 64 row4) = Some 24%Z -> live A (Z_to_bv 64 row4) = None -> live (c_A0 C) (Z_to_bv 64 row4) = None -> (0 <= row4 < 2 ^ 64)%Z ->
     Z_to_bv 64 sel <> Z_to_bv 64 arr ->
     Z_to_bv 64 sel <> Z_to_bv 64 row0 ->
     Z_to_bv 64 arr <> Z_to_bv 64 row0 ->
     Z_to_bv 64 sel <> Z_to_bv 64 row1 ->
     Z_to_bv 64 arr <> Z_to_bv 64 row1 ->
     Z_to_bv 64 row0 <> Z_to_bv 64 row1 ->
     Z_to_bv 64 sel <> Z_to_bv 64 row2 ->
     Z_to_bv 64 arr <> Z_to_bv 64 row2 ->
     Z_to_bv 64 row0 <> Z_to_bv 64 row2 ->
     Z_to_bv 64 row1 <> Z_to_bv 64 row2 ->
     Z_to_bv 64 sel <> Z_to_bv 64 row3 ->
     Z_to_bv 64 arr <> Z_to_bv 64 row3 ->
     Z_to_bv 64 row0 <> Z_to_bv 64 row3 ->
     Z_to_bv 64 row1 <> Z_to_bv 64 row3 ->
     Z_to_bv 64 row2 <> Z_to_bv 64 row3 ->
     Z_to_bv 64 sel <> Z_to_bv 64 row4 ->
     Z_to_bv 64 arr <> Z_to_bv 64 row4 ->
     Z_to_bv 64 row0 <> Z_to_bv 64 row4 ->
     Z_to_bv 64 row1 <> Z_to_bv 64 row4 ->
     Z_to_bv 64 row2 <> Z_to_bv 64 row4 ->
     Z_to_bv 64 row3 <> Z_to_bv 64 row4 ->
     rdn SEGS m' (Z_to_bv 64 (sel + 0)) 4 = Some (Z_to_le_bytes 4 5) ->
     rdn SEGS m' (Z_to_bv 64 (sel + 4)) 4 = Some (Z_to_le_bytes 4 6) ->
     rdn SEGS m' (Z_to_bv 64 (sel + 8)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (sel + 12)) 4 = Some (Z_to_le_bytes 4 2) ->
     rdn SEGS m' (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 arr) ->
     rdn SEGS m' (Z_to_bv 64 (sel + 24)) 8 = Some (Z_to_le_bytes 8 0) ->
     rdn SEGS m' (Z_to_bv 64 (arr + 0)) 8 = Some (Z_to_le_bytes 8 row0) ->
     rdn SEGS m' (Z_to_bv 64 (arr + 8)) 8 = Some (Z_to_le_bytes 8 row1) ->
     rdn SEGS m' (Z_to_bv 64 (arr + 16)) 8 = Some (Z_to_le_bytes 8 row2) ->
     rdn SEGS m' (Z_to_bv 64 (arr + 24)) 8 = Some (Z_to_le_bytes 8 row3) ->
     rdn SEGS m' (Z_to_bv 64 (arr + 32)) 8 = Some (Z_to_le_bytes 8 row4) ->
     rdn SEGS m' (Z_to_bv 64 (row0 + 0)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row0 + 4)) 4 = Some (Z_to_le_bytes 4 2) ->
     rdn SEGS m' (Z_to_bv 64 (row0 + 8)) 4 = Some (Z_to_le_bytes 4 2) ->
     rdn SEGS m' (Z_to_bv 64 (row0 + 12)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row0 + 16)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row0 + 20)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row1 + 0)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row1 + 4)) 4 = Some (Z_to_le_bytes 4 2) ->
     rdn SEGS m' (Z_to_bv 64 (row1 + 8)) 4 = Some (Z_to_le_bytes 4 2) ->
     rdn SEGS m' (Z_to_bv 64 (row1 + 12)) 4 = Some (Z_to_le_bytes 4 2) ->
     rdn SEGS m' (Z_to_bv 64 (row1 + 16)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row1 + 20)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row2 + 0)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row2 + 4)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row2 + 8)) 4 = Some (Z_to_le_bytes 4 2) ->
     rdn SEGS m' (Z_to_bv 64 (row2 + 12)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row2 + 16)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row2 + 20)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row3 + 0)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row3 + 4)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row3 + 8)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row3 + 12)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row3 + 16)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row3 + 20)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row4 + 0)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row4 + 4)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row4 + 8)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row4 + 12)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row4 + 16)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row4 + 20)) 4 = Some (Z_to_le_bytes 4 1) ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 678036) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 s ret S CK HW0 H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 H13 kR bR RM0 HkR HbR HC.
  unfold SELSTR_WIN in *.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  assert (HTP : ex_keep (getr r0 ex_r4 = Z_to_bv 64 1278416)) by exact H4.
  destruct fx as [fr cs]. pose proof I as FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  replace kR with (kR - 0)%Z in RM0 by lia. replace bR with (bR - 0 * 2 ^ 17)%Z in RM0 by lia.
  pose (valsI := @nil word).
  pose proof (fun (q : word) (_ : ~ In q []) => eq_refl (live A0 q)) as LDEL0.
  assert (GLO1 : (c_top C - LSTK <= s - 1312)%Z) by lia.
  assert (GLO2 : (s - 1312 + Z.of_nat (Z.to_nat 1312) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (1312 <= s)%Z) by lia.
  pose proof (W_sok_win C A0 m0 _ (s - 1312) (Z.to_nat 1312) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 1410112 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0]) (EVar 34) (EVar 32) (exW_canary SEGS 1410112 m0) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0]) m0 [KRange (EVar 32) 1422624 (2 ^ 63); KAlign (EVar 32) 16]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 HKf0)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 1312 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
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
  intros A1 m1 vm1 r1 res0 HW1 Hres0 CSx0 Hnz0 Fselx Lo0 F0sel LEQ0 ZERO0 ALsel TOP0 PMc0 RM1.
  pose proof CSx0 as CS0. clear CSx0.
  rewrite with_vmmaps_twice in HW1 |- *.
  assert (Eres0 : res0 = Z_to_bv 64 (u res0)) by (symmetry; apply zbv_self).
  pose proof (u64_range res0) as RRsel. set (sel := u res0) in *. clearbody sel. rewrite Eres0 in Hres0, Fselx, Lo0, F0sel, LEQ0, ZERO0. clear Eres0.
  change (1 * 32)%Z with 32%Z in *.
  pose proof (exW_blk_img_apart_h2 C A1 m1 _ sel 32 CK HW1 Lo0 RRsel eq_refl eq_refl) as IMGAPsel. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPsel.
  pose proof (exW_win_blk_apart_h C A1 m1 _ s 1312 sel 32 CK HW1 Lo0 eq_refl RRsel GLO1) as WAPsel.
  assert (Fsel : live A0 (Z_to_bv 64 sel) = None).
  { destruct (live A0 (Z_to_bv 64 sel)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB0 _ _ EE) as XX. first [discriminate Fselx | (rewrite Fselx in XX; discriminate XX)]. }
  pose proof Lo0 as Lsel_a1.
  assert (SUB1 : sub_live A0 A1).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 sel) by (intros ->; rewrite Fsel in Lq; discriminate Lq). rewrite (LEQ0 q NEq). exact (SUB0 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 sel :: [])) => eq_trans (LEQ0 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL0 q (fun XX => Hq (or_intror XX)))) as LDEL1.
  assert (PM1 : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|]. apply (POSTM_sub C A0 A0 _ _ _ SUB0).
    apply (POSTM_mono C A0 (s + OFF0) s); [unfold OFF0; lia | exact PMc0]. }
  replace (kR - 0 - 1)%Z with (kR - 1)%Z in RM1 by lia. rewrite MG0 in RM1. replace (bR - 0 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 1 * 2 ^ 17)%Z in RM1 by lia.
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, OFF0, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF0 1312 M0 m1 E0 (EVar 32) CK (proj1 PMc0) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E0 m1 kk') in HKk0 end.
  pose proof (regs_ok_agree 35%nat E0 (ex_envL vals0 r1 [sel; exW_canary SEGS 1410112 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [sel; exW_canary SEGS 1410112 m1] 35%nat ltac:(vm_cast_no_check (eq_refl 35%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [sel; exW_canary SEGS 1410112 m1]) m1 _) by (exact (know_ok_agree SEGS 35%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  rewrite (fr_denot_agree 35%nat E0 (ex_envL vals0 r1 [sel; exW_canary SEGS 1410112 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r1 ex_r10 (EVar 67) HRn1 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres0)) as HRx1. clear HRn1. rename HRx1 into HRn1.
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q11_0 Q1_0 Q2_0 Q4_0 PM0 HW0 PMc0 CS0 SUB0 RM0 MG0 TOP0 LEQ0 Hnz0 Fselx Lo0 OFF0 LDEL0.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  pose proof (exW_kn_blk SEGS C A1 m1 _ (ex_envL vals0 r1 [sel; exW_canary SEGS 1410112 m1]) (EVar 67) (EVar 32) sel 32 s 1312 65536 1347584 p16_segs CK HW1 Lsel_a1 RRsel eq_refl eq_refl eq_refl RS ALsel ZERO0 WAPsel IMGAPsel) as HKb1.
  pose proof (W_sok_win C A1 m1 _ (s - 1312) (Z.to_nat 1312) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 1410112 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [sel; exW_canary SEGS 1410112 m1]).
  pose proof (exW_kn_fixed SEGS C A1 m1 _ (ex_envL vals0 r1 [sel; exW_canary SEGS 1410112 m1]) (EVar 68) (EVar 32) (exW_canary SEGS 1410112 m1) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb1 (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb1 HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO0 ALsel.
  exb_exit ST Rc1 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A1 M1 (with_vmmaps vm1 md) /\ POSTM C A0 s m1 M1).
  { subst M1. apply (exW_win_blks C A1 A0 m1 _ E1 log1 (EVar 32) s 1312 [(EVar 67, sel, 32%Z)] CK HW1 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel (conj Lsel_a1 (conj Fsel F0sel))))|]. constructor. }
  destruct WP1 as [HWs1 PMs1].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log1 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC1 : carry log1 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc1 : know_ok SEGS E1 M1 kn1) by (apply (carry_after SEGS E1 m1 log1 kn0 [] kn1 scs hs HC1 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose (BS1 := [(32%nat, s); (67%nat, sel)]).
  exW_regfactB BS1 HR ex_r10 Q10_1. exW_regfactB BS1 HR ex_r11 Q11_1. exW_regfactB BS1 HR ex_r1 Q1_1. exW_regfactB BS1 HR ex_r2 Q2_1. exW_regfactB BS1 HR ex_r4 Q4_1.
  clear BS1.
  lazymatch type of Q2_1 with _ = Z_to_bv 64 (s + ?off) => pose (OFF1 := off) end.
  pose proof (alloc_margin_small (5 * 8) ltac:(exW_cmp)) as MG1.
  lazymatch type of Q1_1 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_1 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A1 M1 _ Rc1 5 8 (kR - 1) (bR - 1 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs1 Q10_1 Q11_1 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM1) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_1
             ltac:(red; apply bv_eq; reflexivity) Q4_1 Q2_1 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A2 m2 vm2 r2 res1 HW2 Hres1 CSx1 Hnz1 Farrx Lo1 F0arr LEQ1 ZERO1 ALarr TOP1 PMc1 RM2.
  pose proof CSx1 as CS1. clear CSx1.
  rewrite with_vmmaps_twice in HW2 |- *.
  assert (Eres1 : res1 = Z_to_bv 64 (u res1)) by (symmetry; apply zbv_self).
  pose proof (u64_range res1) as RRarr. set (arr := u res1) in *. clearbody arr. rewrite Eres1 in Hres1, Farrx, Lo1, F0arr, LEQ1, ZERO1. clear Eres1.
  change (5 * 8)%Z with 40%Z in *.
  pose proof (exW_blk_img_apart_h2 C A2 m2 _ arr 40 CK HW2 Lo1 RRarr eq_refl eq_refl) as IMGAParr. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAParr.
  pose proof (exW_win_blk_apart_h C A2 m2 _ s 1312 arr 40 CK HW2 Lo1 eq_refl RRarr GLO1) as WAParr.
  assert (Farr : live A0 (Z_to_bv 64 arr) = None).
  { destruct (live A0 (Z_to_bv 64 arr)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB1 _ _ EE) as XX. first [discriminate Farrx | (rewrite Farrx in XX; discriminate XX)]. }
  pose proof Lo1 as Larr_a2.
  assert (SUB2 : sub_live A0 A2).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 arr) by (intros ->; rewrite Farr in Lq; discriminate Lq). rewrite (LEQ1 q NEq). exact (SUB1 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 arr :: [Z_to_bv 64 sel])) => eq_trans (LEQ1 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL1 q (fun XX => Hq (or_intror XX)))) as LDEL2.
  assert (NE_sel_arr : Z_to_bv 64 sel <> Z_to_bv 64 arr) by (intros EE; rewrite EE in Lsel_a1; rewrite Farrx in Lsel_a1; discriminate Lsel_a1).
  assert (Lsel_a2 : live A2 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ1 _ NE_sel_arr); exact Lsel_a1).
  pose proof (exW_blk_apart_h C A2 m2 _ sel arr 32 40 CK HW2 Lsel_a2 Larr_a2 NE_sel_arr RRsel RRarr ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel_arr.
  assert (PM2 : POSTM C A0 s m0 m2).
  { eapply POSTM_trans; [exact PM1|]. eapply POSTM_trans; [exact PMs1|]. apply (POSTM_sub C A0 A1 _ _ _ SUB1).
    apply (POSTM_mono C A1 (s + OFF1) s); [unfold OFF1; lia | exact PMc1]. }
  replace (kR - 1 - 1)%Z with (kR - 2)%Z in RM2 by lia. rewrite MG1 in RM2. replace (bR - 1 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 2 * 2 ^ 17)%Z in RM2 by lia.
  assert (KEPT1 : Forall (ex_region_kept E1 M1 m2) [(EVar 32, OFF1, 0%Z); (EVar 67, 0%Z, 32%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF1 1312 M1 m2 E1 (EVar 32) CK (proj1 PMc1) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A1 A1 M1 _ M1 m2 E1 (EVar 67) sel 32 CK HWs1 Lsel_a1 RRsel eq_refl (proj2 PMc1) Lsel_a1 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E1 M1 m2 _ [] _ HKc1 KEPT1) as HKk1.
  match type of HKk1 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E1 m2 kk') in HKk1 end.
  pose proof (regs_ok_agree 69%nat E1 (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) _ _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa1.
  pose proof (exW_regs_call _ _ _ _ _ HRa1 (ex_regs_ok_junk vals1 r2 [arr; exW_canary SEGS 1410112 m2] 69%nat ltac:(vm_cast_no_check (eq_refl 69%nat))) CS1) as HRn2.
  clear HRa1.
  assert (HKa2 : know_ok SEGS (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) m2 _) by (exact (know_ok_agree SEGS 69%nat E1 _ m2 _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk1)).
  rewrite (fr_denot_agree 69%nat E1 (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) _ fr (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r2 ex_r10 (EVar 101) HRn2 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres1)) as HRx2. clear HRn2. rename HRx2 into HRn2.
  clear HR HK Hlf Hms HKc1 HKk1 KEPT1 HC1 HWs1 PMs1 Q10_1 Q11_1 Q1_1 Q2_1 Q4_1 PM1 HW1 PMc1 CS1 SUB1 RM1 MG1 TOP1 LEQ1 Hnz1 Farrx Lo1 OFF1 LDEL1 Lsel_a1.
  subst M1. clear log1. clear E1. try clear Rc1. clear KN1.
  lazymatch type of HRn2 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn2 end.
  pose proof (exW_kn_blk SEGS C A2 m2 _ (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) (EVar 101) (EVar 32) arr 40 s 1312 65536 1347584 p16_segs CK HW2 Larr_a2 RRarr eq_refl eq_refl eq_refl RS ALarr ZERO1 WAParr IMGAParr) as HKb2.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) m2) _ _ (ex_kdisj_apart SEGS (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) m2 (EVar 67) (EVar 101) sel arr 0 32 0 40 eq_refl eq_refl RRsel RRarr AP_sel_arr) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) m2))) as HKd2.
  pose proof (W_sok_win C A2 m2 _ (s - 1312) (Z.to_nat 1312) CK HW2 GLO1 GLO2) as SOK2.
  pose proof (exW_canary_ok SEGS 1410112 m2 (canary_any m2)) as CANOK2.
  pose (vals2 := vals1 ++ map (getr r2) ex_regs_list ++ map (Z_to_bv 64) [arr; exW_canary SEGS 1410112 m2]).
  pose proof (exW_kn_fixed SEGS C A2 m2 _ (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) (EVar 102) (EVar 32) (exW_canary SEGS 1410112 m2) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW2 eq_refl (proj1 CANOK2) (proj2 CANOK2) eq_refl eq_refl eq_refl SOK2 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf2.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb2 (proj2 (Forall_app _ _ _) (conj HKd2 (proj2 (Forall_app _ _ _) (conj HKf2 HKa2)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn2 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN2 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb2 HKd2 HKf2 HKa2 SOK2 CANOK2.
  repeat match goal with H : getr r2 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO1 ALarr.
  exb_exit ST Rc2 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E2 := EEx) in HR, Hlf, HK, Hms |- *; set (log2 := LLx) in Hms, Hlf; set (M2 := mem_denot E2 m2 log2) in Hms end.
  assert (WP2 : W C A2 M2 (with_vmmaps vm2 md) /\ POSTM C A0 s m2 M2).
  { subst M2. apply (exW_win_blks C A2 A0 m2 _ E2 log2 (EVar 32) s 1312 [(EVar 67, sel, 32%Z); (EVar 101, arr, 40%Z)] CK HW2 SUB2 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel (conj Lsel_a2 (conj Fsel F0sel))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a2 (conj Farr F0arr))))|]. constructor. }
  destruct WP2 as [HWs2 PMs2].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log2 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC2 : carry log2 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc2 : know_ok SEGS E2 M2 kn1) by (apply (carry_after SEGS E2 m2 log2 kn0 [] kn1 scs hs HC2 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact Hms |].
  pose (BS2 := [(32%nat, s); (67%nat, sel); (101%nat, arr)]).
  exW_regfactB BS2 HR ex_r10 Q10_2. exW_regfactB BS2 HR ex_r11 Q11_2. exW_regfactB BS2 HR ex_r1 Q1_2. exW_regfactB BS2 HR ex_r2 Q2_2. exW_regfactB BS2 HR ex_r4 Q4_2.
  clear BS2.
  lazymatch type of Q2_2 with _ = Z_to_bv 64 (s + ?off) => pose (OFF2 := off) end.
  pose proof (alloc_margin_small (6 * 4) ltac:(exW_cmp)) as MG2.
  lazymatch type of Q1_2 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_2 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A2 M2 _ Rc2 6 4 (kR - 2) (bR - 2 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs2 Q10_2 Q11_2 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM2) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_2
             ltac:(red; apply bv_eq; reflexivity) Q4_2 Q2_2 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A3 m3 vm3 r3 res2 HW3 Hres2 CSx2 Hnz2 Frow0x Lo2 F0row0 LEQ2 ZERO2 ALrow0 TOP2 PMc2 RM3.
  pose proof CSx2 as CS2. clear CSx2.
  rewrite with_vmmaps_twice in HW3 |- *.
  assert (Eres2 : res2 = Z_to_bv 64 (u res2)) by (symmetry; apply zbv_self).
  pose proof (u64_range res2) as RRrow0. set (row0 := u res2) in *. clearbody row0. rewrite Eres2 in Hres2, Frow0x, Lo2, F0row0, LEQ2, ZERO2. clear Eres2.
  change (6 * 4)%Z with 24%Z in *.
  pose proof (exW_blk_img_apart_h2 C A3 m3 _ row0 24 CK HW3 Lo2 RRrow0 eq_refl eq_refl) as IMGAProw0. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAProw0.
  pose proof (exW_win_blk_apart_h C A3 m3 _ s 1312 row0 24 CK HW3 Lo2 eq_refl RRrow0 GLO1) as WAProw0.
  assert (Frow0 : live A0 (Z_to_bv 64 row0) = None).
  { destruct (live A0 (Z_to_bv 64 row0)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB2 _ _ EE) as XX. first [discriminate Frow0x | (rewrite Frow0x in XX; discriminate XX)]. }
  pose proof Lo2 as Lrow0_a3.
  assert (SUB3 : sub_live A0 A3).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row0) by (intros ->; rewrite Frow0 in Lq; discriminate Lq). rewrite (LEQ2 q NEq). exact (SUB2 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row0 :: [Z_to_bv 64 arr; Z_to_bv 64 sel])) => eq_trans (LEQ2 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL2 q (fun XX => Hq (or_intror XX)))) as LDEL3.
  assert (NE_sel_row0 : Z_to_bv 64 sel <> Z_to_bv 64 row0) by (intros EE; rewrite EE in Lsel_a2; rewrite Frow0x in Lsel_a2; discriminate Lsel_a2).
  assert (Lsel_a3 : live A3 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ2 _ NE_sel_row0); exact Lsel_a2).
  pose proof (exW_blk_apart_h C A3 m3 _ sel row0 32 24 CK HW3 Lsel_a3 Lrow0_a3 NE_sel_row0 RRsel RRrow0 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel_row0.
  assert (NE_arr_row0 : Z_to_bv 64 arr <> Z_to_bv 64 row0) by (intros EE; rewrite EE in Larr_a2; rewrite Frow0x in Larr_a2; discriminate Larr_a2).
  assert (Larr_a3 : live A3 (Z_to_bv 64 arr) = Some 40%Z) by (rewrite (LEQ2 _ NE_arr_row0); exact Larr_a2).
  pose proof (exW_blk_apart_h C A3 m3 _ arr row0 40 24 CK HW3 Larr_a3 Lrow0_a3 NE_arr_row0 RRarr RRrow0 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_row0.
  assert (PM3 : POSTM C A0 s m0 m3).
  { eapply POSTM_trans; [exact PM2|]. eapply POSTM_trans; [exact PMs2|]. apply (POSTM_sub C A0 A2 _ _ _ SUB2).
    apply (POSTM_mono C A2 (s + OFF2) s); [unfold OFF2; lia | exact PMc2]. }
  replace (kR - 2 - 1)%Z with (kR - 3)%Z in RM3 by lia. rewrite MG2 in RM3. replace (bR - 2 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 3 * 2 ^ 17)%Z in RM3 by lia.
  assert (KEPT2 : Forall (ex_region_kept E2 M2 m3) [(EVar 32, OFF2, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 40%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF2 1312 M2 m3 E2 (EVar 32) CK (proj1 PMc2) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A2 A2 M2 _ M2 m3 E2 (EVar 67) sel 32 CK HWs2 Lsel_a2 RRsel eq_refl (proj2 PMc2) Lsel_a2 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A2 A2 M2 _ M2 m3 E2 (EVar 101) arr 40 CK HWs2 Larr_a2 RRarr eq_refl (proj2 PMc2) Larr_a2 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E2 M2 m3 _ [] _ HKc2 KEPT2) as HKk2.
  match type of HKk2 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E2 m3 kk') in HKk2 end.
  pose proof (regs_ok_agree 103%nat E2 (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) _ _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa2.
  pose proof (exW_regs_call _ _ _ _ _ HRa2 (ex_regs_ok_junk vals2 r3 [row0; exW_canary SEGS 1410112 m3] 103%nat ltac:(vm_cast_no_check (eq_refl 103%nat))) CS2) as HRn3.
  clear HRa2.
  assert (HKa3 : know_ok SEGS (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) m3 _) by (exact (know_ok_agree SEGS 103%nat E2 _ m3 _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk2)).
  rewrite (fr_denot_agree 103%nat E2 (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) _ fr (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r3 ex_r10 (EVar 135) HRn3 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres2)) as HRx3. clear HRn3. rename HRx3 into HRn3.
  clear HR HK Hlf Hms HKc2 HKk2 KEPT2 HC2 HWs2 PMs2 Q10_2 Q11_2 Q1_2 Q2_2 Q4_2 PM2 HW2 PMc2 CS2 SUB2 RM2 MG2 TOP2 LEQ2 Hnz2 Frow0x Lo2 OFF2 LDEL2 Lsel_a2 Larr_a2.
  subst M2. clear log2. clear E2. try clear Rc2. clear KN2.
  lazymatch type of HRn3 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn3 end.
  pose proof (exW_kn_blk SEGS C A3 m3 _ (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) (EVar 135) (EVar 32) row0 24 s 1312 65536 1347584 p16_segs CK HW3 Lrow0_a3 RRrow0 eq_refl eq_refl eq_refl RS ALrow0 ZERO2 WAProw0 IMGAProw0) as HKb3.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) m3) _ _ (ex_kdisj_apart SEGS (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) m3 (EVar 67) (EVar 135) sel row0 0 32 0 24 eq_refl eq_refl RRsel RRrow0 AP_sel_row0) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) m3) _ _ (ex_kdisj_apart SEGS (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) m3 (EVar 101) (EVar 135) arr row0 0 40 0 24 eq_refl eq_refl RRarr RRrow0 AP_arr_row0) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) m3)))) as HKd3.
  pose proof (W_sok_win C A3 m3 _ (s - 1312) (Z.to_nat 1312) CK HW3 GLO1 GLO2) as SOK3.
  pose proof (exW_canary_ok SEGS 1410112 m3 (canary_any m3)) as CANOK3.
  pose (vals3 := vals2 ++ map (getr r3) ex_regs_list ++ map (Z_to_bv 64) [row0; exW_canary SEGS 1410112 m3]).
  pose proof (exW_kn_fixed SEGS C A3 m3 _ (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) (EVar 136) (EVar 32) (exW_canary SEGS 1410112 m3) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW3 eq_refl (proj1 CANOK3) (proj2 CANOK3) eq_refl eq_refl eq_refl SOK3 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf3.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb3 (proj2 (Forall_app _ _ _) (conj HKd3 (proj2 (Forall_app _ _ _) (conj HKf3 HKa3)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn3 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN3 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb3 HKd3 HKf3 HKa3 SOK3 CANOK3.
  repeat match goal with H : getr r3 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO2 ALrow0.
  exb_exit ST Rc3 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E3 := EEx) in HR, Hlf, HK, Hms |- *; set (log3 := LLx) in Hms, Hlf; set (M3 := mem_denot E3 m3 log3) in Hms end.
  assert (WP3 : W C A3 M3 (with_vmmaps vm3 md) /\ POSTM C A0 s m3 M3).
  { subst M3. apply (exW_win_blks C A3 A0 m3 _ E3 log3 (EVar 32) s 1312 [(EVar 67, sel, 32%Z); (EVar 101, arr, 40%Z); (EVar 135, row0, 24%Z)] CK HW3 SUB3 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel (conj Lsel_a3 (conj Fsel F0sel))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a3 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRrow0 (conj Lrow0_a3 (conj Frow0 F0row0))))|]. constructor. }
  destruct WP3 as [HWs3 PMs3].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log3 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC3 : carry log3 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc3 : know_ok SEGS E3 M3 kn1) by (apply (carry_after SEGS E3 m3 log3 kn0 [] kn1 scs hs HC3 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact Hms |].
  pose (BS3 := [(32%nat, s); (67%nat, sel); (101%nat, arr); (135%nat, row0)]).
  exW_regfactB BS3 HR ex_r10 Q10_3. exW_regfactB BS3 HR ex_r11 Q11_3. exW_regfactB BS3 HR ex_r1 Q1_3. exW_regfactB BS3 HR ex_r2 Q2_3. exW_regfactB BS3 HR ex_r4 Q4_3.
  clear BS3.
  lazymatch type of Q2_3 with _ = Z_to_bv 64 (s + ?off) => pose (OFF3 := off) end.
  pose proof (alloc_margin_small (6 * 4) ltac:(exW_cmp)) as MG3.
  lazymatch type of Q1_3 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_3 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A3 M3 _ Rc3 6 4 (kR - 3) (bR - 3 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs3 Q10_3 Q11_3 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM3) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_3
             ltac:(red; apply bv_eq; reflexivity) Q4_3 Q2_3 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A4 m4 vm4 r4 res3 HW4 Hres3 CSx3 Hnz3 Frow1x Lo3 F0row1 LEQ3 ZERO3 ALrow1 TOP3 PMc3 RM4.
  pose proof CSx3 as CS3. clear CSx3.
  rewrite with_vmmaps_twice in HW4 |- *.
  assert (Eres3 : res3 = Z_to_bv 64 (u res3)) by (symmetry; apply zbv_self).
  pose proof (u64_range res3) as RRrow1. set (row1 := u res3) in *. clearbody row1. rewrite Eres3 in Hres3, Frow1x, Lo3, F0row1, LEQ3, ZERO3. clear Eres3.
  change (6 * 4)%Z with 24%Z in *.
  pose proof (exW_blk_img_apart_h2 C A4 m4 _ row1 24 CK HW4 Lo3 RRrow1 eq_refl eq_refl) as IMGAProw1. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAProw1.
  pose proof (exW_win_blk_apart_h C A4 m4 _ s 1312 row1 24 CK HW4 Lo3 eq_refl RRrow1 GLO1) as WAProw1.
  assert (Frow1 : live A0 (Z_to_bv 64 row1) = None).
  { destruct (live A0 (Z_to_bv 64 row1)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB3 _ _ EE) as XX. first [discriminate Frow1x | (rewrite Frow1x in XX; discriminate XX)]. }
  pose proof Lo3 as Lrow1_a4.
  assert (SUB4 : sub_live A0 A4).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row1) by (intros ->; rewrite Frow1 in Lq; discriminate Lq). rewrite (LEQ3 q NEq). exact (SUB3 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row1 :: [Z_to_bv 64 row0; Z_to_bv 64 arr; Z_to_bv 64 sel])) => eq_trans (LEQ3 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL3 q (fun XX => Hq (or_intror XX)))) as LDEL4.
  assert (NE_sel_row1 : Z_to_bv 64 sel <> Z_to_bv 64 row1) by (intros EE; rewrite EE in Lsel_a3; rewrite Frow1x in Lsel_a3; discriminate Lsel_a3).
  assert (Lsel_a4 : live A4 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ3 _ NE_sel_row1); exact Lsel_a3).
  pose proof (exW_blk_apart_h C A4 m4 _ sel row1 32 24 CK HW4 Lsel_a4 Lrow1_a4 NE_sel_row1 RRsel RRrow1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel_row1.
  assert (NE_arr_row1 : Z_to_bv 64 arr <> Z_to_bv 64 row1) by (intros EE; rewrite EE in Larr_a3; rewrite Frow1x in Larr_a3; discriminate Larr_a3).
  assert (Larr_a4 : live A4 (Z_to_bv 64 arr) = Some 40%Z) by (rewrite (LEQ3 _ NE_arr_row1); exact Larr_a3).
  pose proof (exW_blk_apart_h C A4 m4 _ arr row1 40 24 CK HW4 Larr_a4 Lrow1_a4 NE_arr_row1 RRarr RRrow1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_row1.
  assert (NE_row0_row1 : Z_to_bv 64 row0 <> Z_to_bv 64 row1) by (intros EE; rewrite EE in Lrow0_a3; rewrite Frow1x in Lrow0_a3; discriminate Lrow0_a3).
  assert (Lrow0_a4 : live A4 (Z_to_bv 64 row0) = Some 24%Z) by (rewrite (LEQ3 _ NE_row0_row1); exact Lrow0_a3).
  pose proof (exW_blk_apart_h C A4 m4 _ row0 row1 24 24 CK HW4 Lrow0_a4 Lrow1_a4 NE_row0_row1 RRrow0 RRrow1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row0_row1.
  assert (PM4 : POSTM C A0 s m0 m4).
  { eapply POSTM_trans; [exact PM3|]. eapply POSTM_trans; [exact PMs3|]. apply (POSTM_sub C A0 A3 _ _ _ SUB3).
    apply (POSTM_mono C A3 (s + OFF3) s); [unfold OFF3; lia | exact PMc3]. }
  replace (kR - 3 - 1)%Z with (kR - 4)%Z in RM4 by lia. rewrite MG3 in RM4. replace (bR - 3 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 4 * 2 ^ 17)%Z in RM4 by lia.
  assert (KEPT3 : Forall (ex_region_kept E3 M3 m4) [(EVar 32, OFF3, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 40%Z); (EVar 135, 0%Z, 24%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF3 1312 M3 m4 E3 (EVar 32) CK (proj1 PMc3) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A3 A3 M3 _ M3 m4 E3 (EVar 67) sel 32 CK HWs3 Lsel_a3 RRsel eq_refl (proj2 PMc3) Lsel_a3 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A3 A3 M3 _ M3 m4 E3 (EVar 101) arr 40 CK HWs3 Larr_a3 RRarr eq_refl (proj2 PMc3) Larr_a3 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A3 A3 M3 _ M3 m4 E3 (EVar 135) row0 24 CK HWs3 Lrow0_a3 RRrow0 eq_refl (proj2 PMc3) Lrow0_a3 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E3 M3 m4 _ [] _ HKc3 KEPT3) as HKk3.
  match type of HKk3 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E3 m4 kk') in HKk3 end.
  pose proof (regs_ok_agree 137%nat E3 (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) _ _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa3.
  pose proof (exW_regs_call _ _ _ _ _ HRa3 (ex_regs_ok_junk vals3 r4 [row1; exW_canary SEGS 1410112 m4] 137%nat ltac:(vm_cast_no_check (eq_refl 137%nat))) CS3) as HRn4.
  clear HRa3.
  assert (HKa4 : know_ok SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4 _) by (exact (know_ok_agree SEGS 137%nat E3 _ m4 _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk3)).
  rewrite (fr_denot_agree 137%nat E3 (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) _ fr (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r4 ex_r10 (EVar 169) HRn4 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres3)) as HRx4. clear HRn4. rename HRx4 into HRn4.
  clear HR HK Hlf Hms HKc3 HKk3 KEPT3 HC3 HWs3 PMs3 Q10_3 Q11_3 Q1_3 Q2_3 Q4_3 PM3 HW3 PMc3 CS3 SUB3 RM3 MG3 TOP3 LEQ3 Hnz3 Frow1x Lo3 OFF3 LDEL3 Lsel_a3 Larr_a3 Lrow0_a3.
  subst M3. clear log3. clear E3. try clear Rc3. clear KN3.
  lazymatch type of HRn4 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn4 end.
  pose proof (exW_kn_blk SEGS C A4 m4 _ (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) (EVar 169) (EVar 32) row1 24 s 1312 65536 1347584 p16_segs CK HW4 Lrow1_a4 RRrow1 eq_refl eq_refl eq_refl RS ALrow1 ZERO3 WAProw1 IMGAProw1) as HKb4.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4) _ _ (ex_kdisj_apart SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4 (EVar 67) (EVar 169) sel row1 0 32 0 24 eq_refl eq_refl RRsel RRrow1 AP_sel_row1) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4) _ _ (ex_kdisj_apart SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4 (EVar 101) (EVar 169) arr row1 0 40 0 24 eq_refl eq_refl RRarr RRrow1 AP_arr_row1) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4) _ _ (ex_kdisj_apart SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4 (EVar 135) (EVar 169) row0 row1 0 24 0 24 eq_refl eq_refl RRrow0 RRrow1 AP_row0_row1) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4))))) as HKd4.
  pose proof (W_sok_win C A4 m4 _ (s - 1312) (Z.to_nat 1312) CK HW4 GLO1 GLO2) as SOK4.
  pose proof (exW_canary_ok SEGS 1410112 m4 (canary_any m4)) as CANOK4.
  pose (vals4 := vals3 ++ map (getr r4) ex_regs_list ++ map (Z_to_bv 64) [row1; exW_canary SEGS 1410112 m4]).
  pose proof (exW_kn_fixed SEGS C A4 m4 _ (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) (EVar 170) (EVar 32) (exW_canary SEGS 1410112 m4) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW4 eq_refl (proj1 CANOK4) (proj2 CANOK4) eq_refl eq_refl eq_refl SOK4 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf4.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb4 (proj2 (Forall_app _ _ _) (conj HKd4 (proj2 (Forall_app _ _ _) (conj HKf4 HKa4)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn4 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN4 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb4 HKd4 HKf4 HKa4 SOK4 CANOK4.
  repeat match goal with H : getr r4 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO3 ALrow1.
  exb_exit ST Rc4 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E4 := EEx) in HR, Hlf, HK, Hms |- *; set (log4 := LLx) in Hms, Hlf; set (M4 := mem_denot E4 m4 log4) in Hms end.
  assert (WP4 : W C A4 M4 (with_vmmaps vm4 md) /\ POSTM C A0 s m4 M4).
  { subst M4. apply (exW_win_blks C A4 A0 m4 _ E4 log4 (EVar 32) s 1312 [(EVar 67, sel, 32%Z); (EVar 101, arr, 40%Z); (EVar 135, row0, 24%Z); (EVar 169, row1, 24%Z)] CK HW4 SUB4 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel (conj Lsel_a4 (conj Fsel F0sel))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a4 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRrow0 (conj Lrow0_a4 (conj Frow0 F0row0))))|]. constructor; [exact (conj eq_refl (conj RRrow1 (conj Lrow1_a4 (conj Frow1 F0row1))))|]. constructor. }
  destruct WP4 as [HWs4 PMs4].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log4 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC4 : carry log4 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc4 : know_ok SEGS E4 M4 kn1) by (apply (carry_after SEGS E4 m4 log4 kn0 [] kn1 scs hs HC4 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact Hms |].
  pose (BS4 := [(32%nat, s); (67%nat, sel); (101%nat, arr); (135%nat, row0); (169%nat, row1)]).
  exW_regfactB BS4 HR ex_r10 Q10_4. exW_regfactB BS4 HR ex_r11 Q11_4. exW_regfactB BS4 HR ex_r1 Q1_4. exW_regfactB BS4 HR ex_r2 Q2_4. exW_regfactB BS4 HR ex_r4 Q4_4.
  clear BS4.
  lazymatch type of Q2_4 with _ = Z_to_bv 64 (s + ?off) => pose (OFF4 := off) end.
  pose proof (alloc_margin_small (6 * 4) ltac:(exW_cmp)) as MG4.
  lazymatch type of Q1_4 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_4 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A4 M4 _ Rc4 6 4 (kR - 4) (bR - 4 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs4 Q10_4 Q11_4 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM4) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_4
             ltac:(red; apply bv_eq; reflexivity) Q4_4 Q2_4 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A5 m5 vm5 r5 res4 HW5 Hres4 CSx4 Hnz4 Frow2x Lo4 F0row2 LEQ4 ZERO4 ALrow2 TOP4 PMc4 RM5.
  pose proof CSx4 as CS4. clear CSx4.
  rewrite with_vmmaps_twice in HW5 |- *.
  assert (Eres4 : res4 = Z_to_bv 64 (u res4)) by (symmetry; apply zbv_self).
  pose proof (u64_range res4) as RRrow2. set (row2 := u res4) in *. clearbody row2. rewrite Eres4 in Hres4, Frow2x, Lo4, F0row2, LEQ4, ZERO4. clear Eres4.
  change (6 * 4)%Z with 24%Z in *.
  pose proof (exW_blk_img_apart_h2 C A5 m5 _ row2 24 CK HW5 Lo4 RRrow2 eq_refl eq_refl) as IMGAProw2. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAProw2.
  pose proof (exW_win_blk_apart_h C A5 m5 _ s 1312 row2 24 CK HW5 Lo4 eq_refl RRrow2 GLO1) as WAProw2.
  assert (Frow2 : live A0 (Z_to_bv 64 row2) = None).
  { destruct (live A0 (Z_to_bv 64 row2)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB4 _ _ EE) as XX. first [discriminate Frow2x | (rewrite Frow2x in XX; discriminate XX)]. }
  pose proof Lo4 as Lrow2_a5.
  assert (SUB5 : sub_live A0 A5).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row2) by (intros ->; rewrite Frow2 in Lq; discriminate Lq). rewrite (LEQ4 q NEq). exact (SUB4 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row2 :: [Z_to_bv 64 row1; Z_to_bv 64 row0; Z_to_bv 64 arr; Z_to_bv 64 sel])) => eq_trans (LEQ4 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL4 q (fun XX => Hq (or_intror XX)))) as LDEL5.
  assert (NE_sel_row2 : Z_to_bv 64 sel <> Z_to_bv 64 row2) by (intros EE; rewrite EE in Lsel_a4; rewrite Frow2x in Lsel_a4; discriminate Lsel_a4).
  assert (Lsel_a5 : live A5 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ4 _ NE_sel_row2); exact Lsel_a4).
  pose proof (exW_blk_apart_h C A5 m5 _ sel row2 32 24 CK HW5 Lsel_a5 Lrow2_a5 NE_sel_row2 RRsel RRrow2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel_row2.
  assert (NE_arr_row2 : Z_to_bv 64 arr <> Z_to_bv 64 row2) by (intros EE; rewrite EE in Larr_a4; rewrite Frow2x in Larr_a4; discriminate Larr_a4).
  assert (Larr_a5 : live A5 (Z_to_bv 64 arr) = Some 40%Z) by (rewrite (LEQ4 _ NE_arr_row2); exact Larr_a4).
  pose proof (exW_blk_apart_h C A5 m5 _ arr row2 40 24 CK HW5 Larr_a5 Lrow2_a5 NE_arr_row2 RRarr RRrow2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_row2.
  assert (NE_row0_row2 : Z_to_bv 64 row0 <> Z_to_bv 64 row2) by (intros EE; rewrite EE in Lrow0_a4; rewrite Frow2x in Lrow0_a4; discriminate Lrow0_a4).
  assert (Lrow0_a5 : live A5 (Z_to_bv 64 row0) = Some 24%Z) by (rewrite (LEQ4 _ NE_row0_row2); exact Lrow0_a4).
  pose proof (exW_blk_apart_h C A5 m5 _ row0 row2 24 24 CK HW5 Lrow0_a5 Lrow2_a5 NE_row0_row2 RRrow0 RRrow2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row0_row2.
  assert (NE_row1_row2 : Z_to_bv 64 row1 <> Z_to_bv 64 row2) by (intros EE; rewrite EE in Lrow1_a4; rewrite Frow2x in Lrow1_a4; discriminate Lrow1_a4).
  assert (Lrow1_a5 : live A5 (Z_to_bv 64 row1) = Some 24%Z) by (rewrite (LEQ4 _ NE_row1_row2); exact Lrow1_a4).
  pose proof (exW_blk_apart_h C A5 m5 _ row1 row2 24 24 CK HW5 Lrow1_a5 Lrow2_a5 NE_row1_row2 RRrow1 RRrow2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row1_row2.
  assert (PM5 : POSTM C A0 s m0 m5).
  { eapply POSTM_trans; [exact PM4|]. eapply POSTM_trans; [exact PMs4|]. apply (POSTM_sub C A0 A4 _ _ _ SUB4).
    apply (POSTM_mono C A4 (s + OFF4) s); [unfold OFF4; lia | exact PMc4]. }
  replace (kR - 4 - 1)%Z with (kR - 5)%Z in RM5 by lia. rewrite MG4 in RM5. replace (bR - 4 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 5 * 2 ^ 17)%Z in RM5 by lia.
  assert (KEPT4 : Forall (ex_region_kept E4 M4 m5) [(EVar 32, OFF4, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 40%Z); (EVar 135, 0%Z, 24%Z); (EVar 169, 0%Z, 24%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF4 1312 M4 m5 E4 (EVar 32) CK (proj1 PMc4) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 M4 _ M4 m5 E4 (EVar 67) sel 32 CK HWs4 Lsel_a4 RRsel eq_refl (proj2 PMc4) Lsel_a4 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 M4 _ M4 m5 E4 (EVar 101) arr 40 CK HWs4 Larr_a4 RRarr eq_refl (proj2 PMc4) Larr_a4 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 M4 _ M4 m5 E4 (EVar 135) row0 24 CK HWs4 Lrow0_a4 RRrow0 eq_refl (proj2 PMc4) Lrow0_a4 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 M4 _ M4 m5 E4 (EVar 169) row1 24 CK HWs4 Lrow1_a4 RRrow1 eq_refl (proj2 PMc4) Lrow1_a4 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E4 M4 m5 _ [] _ HKc4 KEPT4) as HKk4.
  match type of HKk4 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E4 m5 kk') in HKk4 end.
  pose proof (regs_ok_agree 171%nat E4 (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) _ _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa4.
  pose proof (exW_regs_call _ _ _ _ _ HRa4 (ex_regs_ok_junk vals4 r5 [row2; exW_canary SEGS 1410112 m5] 171%nat ltac:(vm_cast_no_check (eq_refl 171%nat))) CS4) as HRn5.
  clear HRa4.
  assert (HKa5 : know_ok SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5 _) by (exact (know_ok_agree SEGS 171%nat E4 _ m5 _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk4)).
  rewrite (fr_denot_agree 171%nat E4 (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) _ fr (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r5 ex_r10 (EVar 203) HRn5 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres4)) as HRx5. clear HRn5. rename HRx5 into HRn5.
  clear HR HK Hlf Hms HKc4 HKk4 KEPT4 HC4 HWs4 PMs4 Q10_4 Q11_4 Q1_4 Q2_4 Q4_4 PM4 HW4 PMc4 CS4 SUB4 RM4 MG4 TOP4 LEQ4 Hnz4 Frow2x Lo4 OFF4 LDEL4 Lsel_a4 Larr_a4 Lrow0_a4 Lrow1_a4.
  subst M4. clear log4. clear E4. try clear Rc4. clear KN4.
  lazymatch type of HRn5 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn5 end.
  pose proof (exW_kn_blk SEGS C A5 m5 _ (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) (EVar 203) (EVar 32) row2 24 s 1312 65536 1347584 p16_segs CK HW5 Lrow2_a5 RRrow2 eq_refl eq_refl eq_refl RS ALrow2 ZERO4 WAProw2 IMGAProw2) as HKb5.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5) _ _ (ex_kdisj_apart SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5 (EVar 67) (EVar 203) sel row2 0 32 0 24 eq_refl eq_refl RRsel RRrow2 AP_sel_row2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5) _ _ (ex_kdisj_apart SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5 (EVar 101) (EVar 203) arr row2 0 40 0 24 eq_refl eq_refl RRarr RRrow2 AP_arr_row2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5) _ _ (ex_kdisj_apart SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5 (EVar 135) (EVar 203) row0 row2 0 24 0 24 eq_refl eq_refl RRrow0 RRrow2 AP_row0_row2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5) _ _ (ex_kdisj_apart SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5 (EVar 169) (EVar 203) row1 row2 0 24 0 24 eq_refl eq_refl RRrow1 RRrow2 AP_row1_row2) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5)))))) as HKd5.
  pose proof (W_sok_win C A5 m5 _ (s - 1312) (Z.to_nat 1312) CK HW5 GLO1 GLO2) as SOK5.
  pose proof (exW_canary_ok SEGS 1410112 m5 (canary_any m5)) as CANOK5.
  pose (vals5 := vals4 ++ map (getr r5) ex_regs_list ++ map (Z_to_bv 64) [row2; exW_canary SEGS 1410112 m5]).
  pose proof (exW_kn_fixed SEGS C A5 m5 _ (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) (EVar 204) (EVar 32) (exW_canary SEGS 1410112 m5) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW5 eq_refl (proj1 CANOK5) (proj2 CANOK5) eq_refl eq_refl eq_refl SOK5 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf5.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb5 (proj2 (Forall_app _ _ _) (conj HKd5 (proj2 (Forall_app _ _ _) (conj HKf5 HKa5)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn5 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN5 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb5 HKd5 HKf5 HKa5 SOK5 CANOK5.
  repeat match goal with H : getr r5 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO4 ALrow2.
  exb_exit ST Rc5 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E5 := EEx) in HR, Hlf, HK, Hms |- *; set (log5 := LLx) in Hms, Hlf; set (M5 := mem_denot E5 m5 log5) in Hms end.
  assert (WP5 : W C A5 M5 (with_vmmaps vm5 md) /\ POSTM C A0 s m5 M5).
  { subst M5. apply (exW_win_blks C A5 A0 m5 _ E5 log5 (EVar 32) s 1312 [(EVar 67, sel, 32%Z); (EVar 101, arr, 40%Z); (EVar 135, row0, 24%Z); (EVar 169, row1, 24%Z); (EVar 203, row2, 24%Z)] CK HW5 SUB5 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel (conj Lsel_a5 (conj Fsel F0sel))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a5 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRrow0 (conj Lrow0_a5 (conj Frow0 F0row0))))|]. constructor; [exact (conj eq_refl (conj RRrow1 (conj Lrow1_a5 (conj Frow1 F0row1))))|]. constructor; [exact (conj eq_refl (conj RRrow2 (conj Lrow2_a5 (conj Frow2 F0row2))))|]. constructor. }
  destruct WP5 as [HWs5 PMs5].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log5 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC5 : carry log5 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc5 : know_ok SEGS E5 M5 kn1) by (apply (carry_after SEGS E5 m5 log5 kn0 [] kn1 scs hs HC5 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact Hms |].
  pose (BS5 := [(32%nat, s); (67%nat, sel); (101%nat, arr); (135%nat, row0); (169%nat, row1); (203%nat, row2)]).
  exW_regfactB BS5 HR ex_r10 Q10_5. exW_regfactB BS5 HR ex_r11 Q11_5. exW_regfactB BS5 HR ex_r1 Q1_5. exW_regfactB BS5 HR ex_r2 Q2_5. exW_regfactB BS5 HR ex_r4 Q4_5.
  clear BS5.
  lazymatch type of Q2_5 with _ = Z_to_bv 64 (s + ?off) => pose (OFF5 := off) end.
  pose proof (alloc_margin_small (6 * 4) ltac:(exW_cmp)) as MG5.
  lazymatch type of Q1_5 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_5 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A5 M5 _ Rc5 6 4 (kR - 5) (bR - 5 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs5 Q10_5 Q11_5 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM5) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_5
             ltac:(red; apply bv_eq; reflexivity) Q4_5 Q2_5 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A6 m6 vm6 r6 res5 HW6 Hres5 CSx5 Hnz5 Frow3x Lo5 F0row3 LEQ5 ZERO5 ALrow3 TOP5 PMc5 RM6.
  pose proof CSx5 as CS5. clear CSx5.
  rewrite with_vmmaps_twice in HW6 |- *.
  assert (Eres5 : res5 = Z_to_bv 64 (u res5)) by (symmetry; apply zbv_self).
  pose proof (u64_range res5) as RRrow3. set (row3 := u res5) in *. clearbody row3. rewrite Eres5 in Hres5, Frow3x, Lo5, F0row3, LEQ5, ZERO5. clear Eres5.
  change (6 * 4)%Z with 24%Z in *.
  pose proof (exW_blk_img_apart_h2 C A6 m6 _ row3 24 CK HW6 Lo5 RRrow3 eq_refl eq_refl) as IMGAProw3. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAProw3.
  pose proof (exW_win_blk_apart_h C A6 m6 _ s 1312 row3 24 CK HW6 Lo5 eq_refl RRrow3 GLO1) as WAProw3.
  assert (Frow3 : live A0 (Z_to_bv 64 row3) = None).
  { destruct (live A0 (Z_to_bv 64 row3)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB5 _ _ EE) as XX. first [discriminate Frow3x | (rewrite Frow3x in XX; discriminate XX)]. }
  pose proof Lo5 as Lrow3_a6.
  assert (SUB6 : sub_live A0 A6).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row3) by (intros ->; rewrite Frow3 in Lq; discriminate Lq). rewrite (LEQ5 q NEq). exact (SUB5 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row3 :: [Z_to_bv 64 row2; Z_to_bv 64 row1; Z_to_bv 64 row0; Z_to_bv 64 arr; Z_to_bv 64 sel])) => eq_trans (LEQ5 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL5 q (fun XX => Hq (or_intror XX)))) as LDEL6.
  assert (NE_sel_row3 : Z_to_bv 64 sel <> Z_to_bv 64 row3) by (intros EE; rewrite EE in Lsel_a5; rewrite Frow3x in Lsel_a5; discriminate Lsel_a5).
  assert (Lsel_a6 : live A6 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ5 _ NE_sel_row3); exact Lsel_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ sel row3 32 24 CK HW6 Lsel_a6 Lrow3_a6 NE_sel_row3 RRsel RRrow3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel_row3.
  assert (NE_arr_row3 : Z_to_bv 64 arr <> Z_to_bv 64 row3) by (intros EE; rewrite EE in Larr_a5; rewrite Frow3x in Larr_a5; discriminate Larr_a5).
  assert (Larr_a6 : live A6 (Z_to_bv 64 arr) = Some 40%Z) by (rewrite (LEQ5 _ NE_arr_row3); exact Larr_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ arr row3 40 24 CK HW6 Larr_a6 Lrow3_a6 NE_arr_row3 RRarr RRrow3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_row3.
  assert (NE_row0_row3 : Z_to_bv 64 row0 <> Z_to_bv 64 row3) by (intros EE; rewrite EE in Lrow0_a5; rewrite Frow3x in Lrow0_a5; discriminate Lrow0_a5).
  assert (Lrow0_a6 : live A6 (Z_to_bv 64 row0) = Some 24%Z) by (rewrite (LEQ5 _ NE_row0_row3); exact Lrow0_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ row0 row3 24 24 CK HW6 Lrow0_a6 Lrow3_a6 NE_row0_row3 RRrow0 RRrow3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row0_row3.
  assert (NE_row1_row3 : Z_to_bv 64 row1 <> Z_to_bv 64 row3) by (intros EE; rewrite EE in Lrow1_a5; rewrite Frow3x in Lrow1_a5; discriminate Lrow1_a5).
  assert (Lrow1_a6 : live A6 (Z_to_bv 64 row1) = Some 24%Z) by (rewrite (LEQ5 _ NE_row1_row3); exact Lrow1_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ row1 row3 24 24 CK HW6 Lrow1_a6 Lrow3_a6 NE_row1_row3 RRrow1 RRrow3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row1_row3.
  assert (NE_row2_row3 : Z_to_bv 64 row2 <> Z_to_bv 64 row3) by (intros EE; rewrite EE in Lrow2_a5; rewrite Frow3x in Lrow2_a5; discriminate Lrow2_a5).
  assert (Lrow2_a6 : live A6 (Z_to_bv 64 row2) = Some 24%Z) by (rewrite (LEQ5 _ NE_row2_row3); exact Lrow2_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ row2 row3 24 24 CK HW6 Lrow2_a6 Lrow3_a6 NE_row2_row3 RRrow2 RRrow3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row2_row3.
  assert (PM6 : POSTM C A0 s m0 m6).
  { eapply POSTM_trans; [exact PM5|]. eapply POSTM_trans; [exact PMs5|]. apply (POSTM_sub C A0 A5 _ _ _ SUB5).
    apply (POSTM_mono C A5 (s + OFF5) s); [unfold OFF5; lia | exact PMc5]. }
  replace (kR - 5 - 1)%Z with (kR - 6)%Z in RM6 by lia. rewrite MG5 in RM6. replace (bR - 5 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 6 * 2 ^ 17)%Z in RM6 by lia.
  assert (KEPT5 : Forall (ex_region_kept E5 M5 m6) [(EVar 32, OFF5, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 40%Z); (EVar 135, 0%Z, 24%Z); (EVar 169, 0%Z, 24%Z); (EVar 203, 0%Z, 24%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF5 1312 M5 m6 E5 (EVar 32) CK (proj1 PMc5) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 67) sel 32 CK HWs5 Lsel_a5 RRsel eq_refl (proj2 PMc5) Lsel_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 101) arr 40 CK HWs5 Larr_a5 RRarr eq_refl (proj2 PMc5) Larr_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 135) row0 24 CK HWs5 Lrow0_a5 RRrow0 eq_refl (proj2 PMc5) Lrow0_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 169) row1 24 CK HWs5 Lrow1_a5 RRrow1 eq_refl (proj2 PMc5) Lrow1_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 203) row2 24 CK HWs5 Lrow2_a5 RRrow2 eq_refl (proj2 PMc5) Lrow2_a5 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E5 M5 m6 _ [] _ HKc5 KEPT5) as HKk5.
  match type of HKk5 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E5 m6 kk') in HKk5 end.
  pose proof (regs_ok_agree 205%nat E5 (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) _ _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa5.
  pose proof (exW_regs_call _ _ _ _ _ HRa5 (ex_regs_ok_junk vals5 r6 [row3; exW_canary SEGS 1410112 m6] 205%nat ltac:(vm_cast_no_check (eq_refl 205%nat))) CS5) as HRn6.
  clear HRa5.
  assert (HKa6 : know_ok SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6 _) by (exact (know_ok_agree SEGS 205%nat E5 _ m6 _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk5)).
  rewrite (fr_denot_agree 205%nat E5 (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) _ fr (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r6 ex_r10 (EVar 237) HRn6 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres5)) as HRx6. clear HRn6. rename HRx6 into HRn6.
  clear HR HK Hlf Hms HKc5 HKk5 KEPT5 HC5 HWs5 PMs5 Q10_5 Q11_5 Q1_5 Q2_5 Q4_5 PM5 HW5 PMc5 CS5 SUB5 RM5 MG5 TOP5 LEQ5 Hnz5 Frow3x Lo5 OFF5 LDEL5 Lsel_a5 Larr_a5 Lrow0_a5 Lrow1_a5 Lrow2_a5.
  subst M5. clear log5. clear E5. try clear Rc5. clear KN5.
  lazymatch type of HRn6 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn6 end.
  pose proof (exW_kn_blk SEGS C A6 m6 _ (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) (EVar 237) (EVar 32) row3 24 s 1312 65536 1347584 p16_segs CK HW6 Lrow3_a6 RRrow3 eq_refl eq_refl eq_refl RS ALrow3 ZERO5 WAProw3 IMGAProw3) as HKb6.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6 (EVar 67) (EVar 237) sel row3 0 32 0 24 eq_refl eq_refl RRsel RRrow3 AP_sel_row3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6 (EVar 101) (EVar 237) arr row3 0 40 0 24 eq_refl eq_refl RRarr RRrow3 AP_arr_row3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6 (EVar 135) (EVar 237) row0 row3 0 24 0 24 eq_refl eq_refl RRrow0 RRrow3 AP_row0_row3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6 (EVar 169) (EVar 237) row1 row3 0 24 0 24 eq_refl eq_refl RRrow1 RRrow3 AP_row1_row3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6 (EVar 203) (EVar 237) row2 row3 0 24 0 24 eq_refl eq_refl RRrow2 RRrow3 AP_row2_row3) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6))))))) as HKd6.
  pose proof (W_sok_win C A6 m6 _ (s - 1312) (Z.to_nat 1312) CK HW6 GLO1 GLO2) as SOK6.
  pose proof (exW_canary_ok SEGS 1410112 m6 (canary_any m6)) as CANOK6.
  pose (vals6 := vals5 ++ map (getr r6) ex_regs_list ++ map (Z_to_bv 64) [row3; exW_canary SEGS 1410112 m6]).
  pose proof (exW_kn_fixed SEGS C A6 m6 _ (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) (EVar 238) (EVar 32) (exW_canary SEGS 1410112 m6) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW6 eq_refl (proj1 CANOK6) (proj2 CANOK6) eq_refl eq_refl eq_refl SOK6 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf6.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb6 (proj2 (Forall_app _ _ _) (conj HKd6 (proj2 (Forall_app _ _ _) (conj HKf6 HKa6)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn6 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN6 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb6 HKd6 HKf6 HKa6 SOK6 CANOK6.
  repeat match goal with H : getr r6 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO5 ALrow3.
  exb_exit ST Rc6 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E6 := EEx) in HR, Hlf, HK, Hms |- *; set (log6 := LLx) in Hms, Hlf; set (M6 := mem_denot E6 m6 log6) in Hms end.
  assert (WP6 : W C A6 M6 (with_vmmaps vm6 md) /\ POSTM C A0 s m6 M6).
  { subst M6. apply (exW_win_blks C A6 A0 m6 _ E6 log6 (EVar 32) s 1312 [(EVar 67, sel, 32%Z); (EVar 101, arr, 40%Z); (EVar 135, row0, 24%Z); (EVar 169, row1, 24%Z); (EVar 203, row2, 24%Z); (EVar 237, row3, 24%Z)] CK HW6 SUB6 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel (conj Lsel_a6 (conj Fsel F0sel))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a6 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRrow0 (conj Lrow0_a6 (conj Frow0 F0row0))))|]. constructor; [exact (conj eq_refl (conj RRrow1 (conj Lrow1_a6 (conj Frow1 F0row1))))|]. constructor; [exact (conj eq_refl (conj RRrow2 (conj Lrow2_a6 (conj Frow2 F0row2))))|]. constructor; [exact (conj eq_refl (conj RRrow3 (conj Lrow3_a6 (conj Frow3 F0row3))))|]. constructor. }
  destruct WP6 as [HWs6 PMs6].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log6 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC6 : carry log6 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc6 : know_ok SEGS E6 M6 kn1) by (apply (carry_after SEGS E6 m6 log6 kn0 [] kn1 scs hs HC6 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact Hms |].
  pose (BS6 := [(32%nat, s); (67%nat, sel); (101%nat, arr); (135%nat, row0); (169%nat, row1); (203%nat, row2); (237%nat, row3)]).
  exW_regfactB BS6 HR ex_r10 Q10_6. exW_regfactB BS6 HR ex_r11 Q11_6. exW_regfactB BS6 HR ex_r1 Q1_6. exW_regfactB BS6 HR ex_r2 Q2_6. exW_regfactB BS6 HR ex_r4 Q4_6.
  clear BS6.
  lazymatch type of Q2_6 with _ = Z_to_bv 64 (s + ?off) => pose (OFF6 := off) end.
  pose proof (alloc_margin_small (6 * 4) ltac:(exW_cmp)) as MG6.
  lazymatch type of Q1_6 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_6 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A6 M6 _ Rc6 6 4 (kR - 6) (bR - 6 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs6 Q10_6 Q11_6 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM6) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_6
             ltac:(red; apply bv_eq; reflexivity) Q4_6 Q2_6 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A7 m7 vm7 r7 res6 HW7 Hres6 CSx6 Hnz6 Frow4x Lo6 F0row4 LEQ6 ZERO6 ALrow4 TOP6 PMc6 RM7.
  pose proof CSx6 as CS6. clear CSx6.
  rewrite with_vmmaps_twice in HW7 |- *.
  assert (Eres6 : res6 = Z_to_bv 64 (u res6)) by (symmetry; apply zbv_self).
  pose proof (u64_range res6) as RRrow4. set (row4 := u res6) in *. clearbody row4. rewrite Eres6 in Hres6, Frow4x, Lo6, F0row4, LEQ6, ZERO6. clear Eres6.
  change (6 * 4)%Z with 24%Z in *.
  pose proof (exW_blk_img_apart_h2 C A7 m7 _ row4 24 CK HW7 Lo6 RRrow4 eq_refl eq_refl) as IMGAProw4. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAProw4.
  pose proof (exW_win_blk_apart_h C A7 m7 _ s 1312 row4 24 CK HW7 Lo6 eq_refl RRrow4 GLO1) as WAProw4.
  assert (Frow4 : live A0 (Z_to_bv 64 row4) = None).
  { destruct (live A0 (Z_to_bv 64 row4)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB6 _ _ EE) as XX. first [discriminate Frow4x | (rewrite Frow4x in XX; discriminate XX)]. }
  pose proof Lo6 as Lrow4_a7.
  assert (SUB7 : sub_live A0 A7).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row4) by (intros ->; rewrite Frow4 in Lq; discriminate Lq). rewrite (LEQ6 q NEq). exact (SUB6 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row4 :: [Z_to_bv 64 row3; Z_to_bv 64 row2; Z_to_bv 64 row1; Z_to_bv 64 row0; Z_to_bv 64 arr; Z_to_bv 64 sel])) => eq_trans (LEQ6 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL6 q (fun XX => Hq (or_intror XX)))) as LDEL7.
  assert (NE_sel_row4 : Z_to_bv 64 sel <> Z_to_bv 64 row4) by (intros EE; rewrite EE in Lsel_a6; rewrite Frow4x in Lsel_a6; discriminate Lsel_a6).
  assert (Lsel_a7 : live A7 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ6 _ NE_sel_row4); exact Lsel_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ sel row4 32 24 CK HW7 Lsel_a7 Lrow4_a7 NE_sel_row4 RRsel RRrow4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel_row4.
  assert (NE_arr_row4 : Z_to_bv 64 arr <> Z_to_bv 64 row4) by (intros EE; rewrite EE in Larr_a6; rewrite Frow4x in Larr_a6; discriminate Larr_a6).
  assert (Larr_a7 : live A7 (Z_to_bv 64 arr) = Some 40%Z) by (rewrite (LEQ6 _ NE_arr_row4); exact Larr_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ arr row4 40 24 CK HW7 Larr_a7 Lrow4_a7 NE_arr_row4 RRarr RRrow4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_row4.
  assert (NE_row0_row4 : Z_to_bv 64 row0 <> Z_to_bv 64 row4) by (intros EE; rewrite EE in Lrow0_a6; rewrite Frow4x in Lrow0_a6; discriminate Lrow0_a6).
  assert (Lrow0_a7 : live A7 (Z_to_bv 64 row0) = Some 24%Z) by (rewrite (LEQ6 _ NE_row0_row4); exact Lrow0_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ row0 row4 24 24 CK HW7 Lrow0_a7 Lrow4_a7 NE_row0_row4 RRrow0 RRrow4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row0_row4.
  assert (NE_row1_row4 : Z_to_bv 64 row1 <> Z_to_bv 64 row4) by (intros EE; rewrite EE in Lrow1_a6; rewrite Frow4x in Lrow1_a6; discriminate Lrow1_a6).
  assert (Lrow1_a7 : live A7 (Z_to_bv 64 row1) = Some 24%Z) by (rewrite (LEQ6 _ NE_row1_row4); exact Lrow1_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ row1 row4 24 24 CK HW7 Lrow1_a7 Lrow4_a7 NE_row1_row4 RRrow1 RRrow4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row1_row4.
  assert (NE_row2_row4 : Z_to_bv 64 row2 <> Z_to_bv 64 row4) by (intros EE; rewrite EE in Lrow2_a6; rewrite Frow4x in Lrow2_a6; discriminate Lrow2_a6).
  assert (Lrow2_a7 : live A7 (Z_to_bv 64 row2) = Some 24%Z) by (rewrite (LEQ6 _ NE_row2_row4); exact Lrow2_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ row2 row4 24 24 CK HW7 Lrow2_a7 Lrow4_a7 NE_row2_row4 RRrow2 RRrow4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row2_row4.
  assert (NE_row3_row4 : Z_to_bv 64 row3 <> Z_to_bv 64 row4) by (intros EE; rewrite EE in Lrow3_a6; rewrite Frow4x in Lrow3_a6; discriminate Lrow3_a6).
  assert (Lrow3_a7 : live A7 (Z_to_bv 64 row3) = Some 24%Z) by (rewrite (LEQ6 _ NE_row3_row4); exact Lrow3_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ row3 row4 24 24 CK HW7 Lrow3_a7 Lrow4_a7 NE_row3_row4 RRrow3 RRrow4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row3_row4.
  assert (PM7 : POSTM C A0 s m0 m7).
  { eapply POSTM_trans; [exact PM6|]. eapply POSTM_trans; [exact PMs6|]. apply (POSTM_sub C A0 A6 _ _ _ SUB6).
    apply (POSTM_mono C A6 (s + OFF6) s); [unfold OFF6; lia | exact PMc6]. }
  replace (kR - 6 - 1)%Z with (kR - 7)%Z in RM7 by lia. rewrite MG6 in RM7. replace (bR - 6 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 7 * 2 ^ 17)%Z in RM7 by lia.
  assert (KEPT6 : Forall (ex_region_kept E6 M6 m7) [(EVar 32, OFF6, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 40%Z); (EVar 135, 0%Z, 24%Z); (EVar 169, 0%Z, 24%Z); (EVar 203, 0%Z, 24%Z); (EVar 237, 0%Z, 24%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF6 1312 M6 m7 E6 (EVar 32) CK (proj1 PMc6) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 67) sel 32 CK HWs6 Lsel_a6 RRsel eq_refl (proj2 PMc6) Lsel_a6 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 101) arr 40 CK HWs6 Larr_a6 RRarr eq_refl (proj2 PMc6) Larr_a6 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 135) row0 24 CK HWs6 Lrow0_a6 RRrow0 eq_refl (proj2 PMc6) Lrow0_a6 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 169) row1 24 CK HWs6 Lrow1_a6 RRrow1 eq_refl (proj2 PMc6) Lrow1_a6 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 203) row2 24 CK HWs6 Lrow2_a6 RRrow2 eq_refl (proj2 PMc6) Lrow2_a6 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 237) row3 24 CK HWs6 Lrow3_a6 RRrow3 eq_refl (proj2 PMc6) Lrow3_a6 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E6 M6 m7 _ [] _ HKc6 KEPT6) as HKk6.
  match type of HKk6 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E6 m7 kk') in HKk6 end.
  pose proof (regs_ok_agree 239%nat E6 (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) _ _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa6.
  pose proof (exW_regs_call _ _ _ _ _ HRa6 (ex_regs_ok_junk vals6 r7 [row4; exW_canary SEGS 1410112 m7] 239%nat ltac:(vm_cast_no_check (eq_refl 239%nat))) CS6) as HRn7.
  clear HRa6.
  assert (HKa7 : know_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7 _) by (exact (know_ok_agree SEGS 239%nat E6 _ m7 _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk6)).
  rewrite (fr_denot_agree 239%nat E6 (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) _ fr (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r7 ex_r10 (EVar 271) HRn7 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres6)) as HRx7. clear HRn7. rename HRx7 into HRn7.
  clear HR HK Hlf Hms HKc6 HKk6 KEPT6 HC6 HWs6 PMs6 Q10_6 Q11_6 Q1_6 Q2_6 Q4_6 PM6 HW6 PMc6 CS6 SUB6 RM6 MG6 TOP6 LEQ6 Hnz6 Frow4x Lo6 OFF6 LDEL6 Lsel_a6 Larr_a6 Lrow0_a6 Lrow1_a6 Lrow2_a6 Lrow3_a6.
  subst M6. clear log6. clear E6. try clear Rc6. clear KN6.
  lazymatch type of HRn7 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn7 end.
  pose proof (exW_kn_blk SEGS C A7 m7 _ (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) (EVar 271) (EVar 32) row4 24 s 1312 65536 1347584 p16_segs CK HW7 Lrow4_a7 RRrow4 eq_refl eq_refl eq_refl RS ALrow4 ZERO6 WAProw4 IMGAProw4) as HKb7.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7 (EVar 67) (EVar 271) sel row4 0 32 0 24 eq_refl eq_refl RRsel RRrow4 AP_sel_row4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7 (EVar 101) (EVar 271) arr row4 0 40 0 24 eq_refl eq_refl RRarr RRrow4 AP_arr_row4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7 (EVar 135) (EVar 271) row0 row4 0 24 0 24 eq_refl eq_refl RRrow0 RRrow4 AP_row0_row4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7 (EVar 169) (EVar 271) row1 row4 0 24 0 24 eq_refl eq_refl RRrow1 RRrow4 AP_row1_row4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7 (EVar 203) (EVar 271) row2 row4 0 24 0 24 eq_refl eq_refl RRrow2 RRrow4 AP_row2_row4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7 (EVar 237) (EVar 271) row3 row4 0 24 0 24 eq_refl eq_refl RRrow3 RRrow4 AP_row3_row4) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7)))))))) as HKd7.
  pose proof (W_sok_win C A7 m7 _ (s - 1312) (Z.to_nat 1312) CK HW7 GLO1 GLO2) as SOK7.
  pose proof (exW_canary_ok SEGS 1410112 m7 (canary_any m7)) as CANOK7.
  pose (vals7 := vals6 ++ map (getr r7) ex_regs_list ++ map (Z_to_bv 64) [row4; exW_canary SEGS 1410112 m7]).
  pose proof (exW_kn_fixed SEGS C A7 m7 _ (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) (EVar 272) (EVar 32) (exW_canary SEGS 1410112 m7) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW7 eq_refl (proj1 CANOK7) (proj2 CANOK7) eq_refl eq_refl eq_refl SOK7 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf7.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb7 (proj2 (Forall_app _ _ _) (conj HKd7 (proj2 (Forall_app _ _ _) (conj HKf7 HKa7)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn7 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN7 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb7 HKd7 HKf7 HKa7 SOK7 CANOK7.
  repeat match goal with H : getr r7 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO6 ALrow4.
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E7 := EEx) in HR, Hlf, HK, Hms |- *; set (log7 := LLx) in Hms, Hlf; set (M7 := mem_denot E7 m7 log7) in Hms end.
  assert (WP7 : W C A7 M7 (with_vmmaps vm7 md) /\ POSTM C A0 s m7 M7).
  { subst M7. apply (exW_win_blks C A7 A0 m7 _ E7 log7 (EVar 32) s 1312 [(EVar 67, sel, 32%Z); (EVar 101, arr, 40%Z); (EVar 135, row0, 24%Z); (EVar 169, row1, 24%Z); (EVar 203, row2, 24%Z); (EVar 237, row3, 24%Z); (EVar 271, row4, 24%Z)] CK HW7 SUB7 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel (conj Lsel_a7 (conj Fsel F0sel))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a7 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRrow0 (conj Lrow0_a7 (conj Frow0 F0row0))))|]. constructor; [exact (conj eq_refl (conj RRrow1 (conj Lrow1_a7 (conj Frow1 F0row1))))|]. constructor; [exact (conj eq_refl (conj RRrow2 (conj Lrow2_a7 (conj Frow2 F0row2))))|]. constructor; [exact (conj eq_refl (conj RRrow3 (conj Lrow3_a7 (conj Frow3 F0row3))))|]. constructor; [exact (conj eq_refl (conj RRrow4 (conj Lrow4_a7 (conj Frow4 F0row4))))|]. constructor. }
  destruct WP7 as [HWs7 PMs7].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact Hms |].
  pose (BSF := [(32%nat, s); (67%nat, sel); (101%nat, arr); (135%nat, row0); (169%nat, row1); (203%nat, row2); (237%nat, row3); (271%nat, row4)]).
  exW_regfactB BSF HR ex_r10 G10.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel 0%Z 4%nat Csel_0.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel 4%Z 4%nat Csel_4.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel 8%Z 4%nat Csel_8.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel 12%Z 4%nat Csel_12.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel 16%Z 8%nat Csel_16.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel 24%Z 8%nat Csel_24.
  exW_cellB HK Hlf r0 BSF (EVar 101) arr 0%Z 8%nat Carr_0.
  exW_cellB HK Hlf r0 BSF (EVar 101) arr 8%Z 8%nat Carr_8.
  exW_cellB HK Hlf r0 BSF (EVar 101) arr 16%Z 8%nat Carr_16.
  exW_cellB HK Hlf r0 BSF (EVar 101) arr 24%Z 8%nat Carr_24.
  exW_cellB HK Hlf r0 BSF (EVar 101) arr 32%Z 8%nat Carr_32.
  exW_cellB HK Hlf r0 BSF (EVar 135) row0 0%Z 4%nat Crow0_0.
  exW_cellB HK Hlf r0 BSF (EVar 135) row0 4%Z 4%nat Crow0_4.
  exW_cellB HK Hlf r0 BSF (EVar 135) row0 8%Z 4%nat Crow0_8.
  exW_cellB HK Hlf r0 BSF (EVar 135) row0 12%Z 4%nat Crow0_12.
  exW_cellB HK Hlf r0 BSF (EVar 135) row0 16%Z 4%nat Crow0_16.
  exW_cellB HK Hlf r0 BSF (EVar 135) row0 20%Z 4%nat Crow0_20.
  exW_cellB HK Hlf r0 BSF (EVar 169) row1 0%Z 4%nat Crow1_0.
  exW_cellB HK Hlf r0 BSF (EVar 169) row1 4%Z 4%nat Crow1_4.
  exW_cellB HK Hlf r0 BSF (EVar 169) row1 8%Z 4%nat Crow1_8.
  exW_cellB HK Hlf r0 BSF (EVar 169) row1 12%Z 4%nat Crow1_12.
  exW_cellB HK Hlf r0 BSF (EVar 169) row1 16%Z 4%nat Crow1_16.
  exW_cellB HK Hlf r0 BSF (EVar 169) row1 20%Z 4%nat Crow1_20.
  exW_cellB HK Hlf r0 BSF (EVar 203) row2 0%Z 4%nat Crow2_0.
  exW_cellB HK Hlf r0 BSF (EVar 203) row2 4%Z 4%nat Crow2_4.
  exW_cellB HK Hlf r0 BSF (EVar 203) row2 8%Z 4%nat Crow2_8.
  exW_cellB HK Hlf r0 BSF (EVar 203) row2 12%Z 4%nat Crow2_12.
  exW_cellB HK Hlf r0 BSF (EVar 203) row2 16%Z 4%nat Crow2_16.
  exW_cellB HK Hlf r0 BSF (EVar 203) row2 20%Z 4%nat Crow2_20.
  exW_cellB HK Hlf r0 BSF (EVar 237) row3 0%Z 4%nat Crow3_0.
  exW_cellB HK Hlf r0 BSF (EVar 237) row3 4%Z 4%nat Crow3_4.
  exW_cellB HK Hlf r0 BSF (EVar 237) row3 8%Z 4%nat Crow3_8.
  exW_cellB HK Hlf r0 BSF (EVar 237) row3 12%Z 4%nat Crow3_12.
  exW_cellB HK Hlf r0 BSF (EVar 237) row3 16%Z 4%nat Crow3_16.
  exW_cellB HK Hlf r0 BSF (EVar 237) row3 20%Z 4%nat Crow3_20.
  exW_cellB HK Hlf r0 BSF (EVar 271) row4 0%Z 4%nat Crow4_0.
  exW_cellB HK Hlf r0 BSF (EVar 271) row4 4%Z 4%nat Crow4_4.
  exW_cellB HK Hlf r0 BSF (EVar 271) row4 8%Z 4%nat Crow4_8.
  exW_cellB HK Hlf r0 BSF (EVar 271) row4 12%Z 4%nat Crow4_12.
  exW_cellB HK Hlf r0 BSF (EVar 271) row4 16%Z 4%nat Crow4_16.
  exW_cellB HK Hlf r0 BSF (EVar 271) row4 20%Z 4%nat Crow4_20.
  refine (HC A7 M7 vm7 RcF sel arr row0 row1 row2 row3 row4 HWs7 _ SUB7 (POSTM_trans _ _ _ _ _ _ PM7 PMs7) RM7 LDEL7 G10
            Lsel_a7 Fsel F0sel RRsel Larr_a7 Farr F0arr RRarr Lrow0_a7 Frow0 F0row0 RRrow0 Lrow1_a7 Frow1 F0row1 RRrow1 Lrow2_a7 Frow2 F0row2 RRrow2 Lrow3_a7 Frow3 F0row3 RRrow3 Lrow4_a7 Frow4 F0row4 RRrow4
            NE_sel_arr NE_sel_row0 NE_arr_row0 NE_sel_row1 NE_arr_row1 NE_row0_row1 NE_sel_row2 NE_arr_row2 NE_row0_row2 NE_row1_row2 NE_sel_row3 NE_arr_row3 NE_row0_row3 NE_row1_row3 NE_row2_row3 NE_sel_row4 NE_arr_row4 NE_row0_row4 NE_row1_row4 NE_row2_row4 NE_row3_row4
            Csel_0 Csel_4 Csel_8 Csel_12 Csel_16 Csel_24 Carr_0 Carr_8 Carr_16 Carr_24 Carr_32 Crow0_0 Crow0_4 Crow0_8 Crow0_12 Crow0_16 Crow0_20 Crow1_0 Crow1_4 Crow1_8 Crow1_12 Crow1_16 Crow1_20 Crow2_0 Crow2_4 Crow2_8 Crow2_12 Crow2_16 Crow2_20 Crow3_0 Crow3_4 Crow3_8 Crow3_12 Crow3_16 Crow3_20 Crow4_0 Crow4_4 Crow4_8 Crow4_12 Crow4_16 Crow4_20).
  lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 RcF [(2%nat, EVar 32); (4%nat, ELit 1278416)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor; [symmetry; exact HTP | constructor]] | vm_compute; reflexivity] end.
Qed.

(* [comment removed for export] *)
Lemma selstr_chain3 : forall (fx : FPState) C A m md regs (s : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELSTR_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 1278416 ->
  getr regs 10 = Z_to_bv 64 77900 -> getr regs 11 = Z_to_bv 64 5 -> getr regs 12 = Z_to_bv 64 6 -> getr regs 13 = Z_to_bv 64 0 ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (7 <= kR)%Z -> (7 * 2 ^ 17 <= bR)%Z ->
  (forall A' m' vm' regs' (sel arr row0 row1 row2 row3 row4 : Z),
     W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> sub_live A A' -> POSTM C A s m m' ->
     aroom A' vm' (kR - 7) (bR - 7 * 2 ^ 17) ->
     (forall q : word, ~ In q [Z_to_bv 64 row4; Z_to_bv 64 row3; Z_to_bv 64 row2; Z_to_bv 64 row1; Z_to_bv 64 row0; Z_to_bv 64 arr; Z_to_bv 64 sel] -> live A' q = live A q) ->
     getr regs' 10 = Z_to_bv 64 sel ->
     live A' (Z_to_bv 64 sel) = Some 32%Z -> live A (Z_to_bv 64 sel) = None -> live (c_A0 C) (Z_to_bv 64 sel) = None -> (0 <= sel < 2 ^ 64)%Z ->
     live A' (Z_to_bv 64 arr) = Some 40%Z -> live A (Z_to_bv 64 arr) = None -> live (c_A0 C) (Z_to_bv 64 arr) = None -> (0 <= arr < 2 ^ 64)%Z ->
     live A' (Z_to_bv 64 row0) = Some 24%Z -> live A (Z_to_bv 64 row0) = None -> live (c_A0 C) (Z_to_bv 64 row0) = None -> (0 <= row0 < 2 ^ 64)%Z ->
     live A' (Z_to_bv 64 row1) = Some 24%Z -> live A (Z_to_bv 64 row1) = None -> live (c_A0 C) (Z_to_bv 64 row1) = None -> (0 <= row1 < 2 ^ 64)%Z ->
     live A' (Z_to_bv 64 row2) = Some 24%Z -> live A (Z_to_bv 64 row2) = None -> live (c_A0 C) (Z_to_bv 64 row2) = None -> (0 <= row2 < 2 ^ 64)%Z ->
     live A' (Z_to_bv 64 row3) = Some 24%Z -> live A (Z_to_bv 64 row3) = None -> live (c_A0 C) (Z_to_bv 64 row3) = None -> (0 <= row3 < 2 ^ 64)%Z ->
     live A' (Z_to_bv 64 row4) = Some 24%Z -> live A (Z_to_bv 64 row4) = None -> live (c_A0 C) (Z_to_bv 64 row4) = None -> (0 <= row4 < 2 ^ 64)%Z ->
     Z_to_bv 64 sel <> Z_to_bv 64 arr ->
     Z_to_bv 64 sel <> Z_to_bv 64 row0 ->
     Z_to_bv 64 arr <> Z_to_bv 64 row0 ->
     Z_to_bv 64 sel <> Z_to_bv 64 row1 ->
     Z_to_bv 64 arr <> Z_to_bv 64 row1 ->
     Z_to_bv 64 row0 <> Z_to_bv 64 row1 ->
     Z_to_bv 64 sel <> Z_to_bv 64 row2 ->
     Z_to_bv 64 arr <> Z_to_bv 64 row2 ->
     Z_to_bv 64 row0 <> Z_to_bv 64 row2 ->
     Z_to_bv 64 row1 <> Z_to_bv 64 row2 ->
     Z_to_bv 64 sel <> Z_to_bv 64 row3 ->
     Z_to_bv 64 arr <> Z_to_bv 64 row3 ->
     Z_to_bv 64 row0 <> Z_to_bv 64 row3 ->
     Z_to_bv 64 row1 <> Z_to_bv 64 row3 ->
     Z_to_bv 64 row2 <> Z_to_bv 64 row3 ->
     Z_to_bv 64 sel <> Z_to_bv 64 row4 ->
     Z_to_bv 64 arr <> Z_to_bv 64 row4 ->
     Z_to_bv 64 row0 <> Z_to_bv 64 row4 ->
     Z_to_bv 64 row1 <> Z_to_bv 64 row4 ->
     Z_to_bv 64 row2 <> Z_to_bv 64 row4 ->
     Z_to_bv 64 row3 <> Z_to_bv 64 row4 ->
     rdn SEGS m' (Z_to_bv 64 (sel + 0)) 4 = Some (Z_to_le_bytes 4 5) ->
     rdn SEGS m' (Z_to_bv 64 (sel + 4)) 4 = Some (Z_to_le_bytes 4 6) ->
     rdn SEGS m' (Z_to_bv 64 (sel + 8)) 4 = Some (Z_to_le_bytes 4 3) ->
     rdn SEGS m' (Z_to_bv 64 (sel + 12)) 4 = Some (Z_to_le_bytes 4 3) ->
     rdn SEGS m' (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 arr) ->
     rdn SEGS m' (Z_to_bv 64 (sel + 24)) 8 = Some (Z_to_le_bytes 8 0) ->
     rdn SEGS m' (Z_to_bv 64 (arr + 0)) 8 = Some (Z_to_le_bytes 8 row0) ->
     rdn SEGS m' (Z_to_bv 64 (arr + 8)) 8 = Some (Z_to_le_bytes 8 row1) ->
     rdn SEGS m' (Z_to_bv 64 (arr + 16)) 8 = Some (Z_to_le_bytes 8 row2) ->
     rdn SEGS m' (Z_to_bv 64 (arr + 24)) 8 = Some (Z_to_le_bytes 8 row3) ->
     rdn SEGS m' (Z_to_bv 64 (arr + 32)) 8 = Some (Z_to_le_bytes 8 row4) ->
     rdn SEGS m' (Z_to_bv 64 (row0 + 0)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row0 + 4)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row0 + 8)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row0 + 12)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row0 + 16)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row0 + 20)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row1 + 0)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row1 + 4)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row1 + 8)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row1 + 12)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row1 + 16)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row1 + 20)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row2 + 0)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row2 + 4)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row2 + 8)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row2 + 12)) 4 = Some (Z_to_le_bytes 4 2) ->
     rdn SEGS m' (Z_to_bv 64 (row2 + 16)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row2 + 20)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row3 + 0)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row3 + 4)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row3 + 8)) 4 = Some (Z_to_le_bytes 4 2) ->
     rdn SEGS m' (Z_to_bv 64 (row3 + 12)) 4 = Some (Z_to_le_bytes 4 2) ->
     rdn SEGS m' (Z_to_bv 64 (row3 + 16)) 4 = Some (Z_to_le_bytes 4 2) ->
     rdn SEGS m' (Z_to_bv 64 (row3 + 20)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row4 + 0)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row4 + 4)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row4 + 8)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row4 + 12)) 4 = Some (Z_to_le_bytes 4 2) ->
     rdn SEGS m' (Z_to_bv 64 (row4 + 16)) 4 = Some (Z_to_le_bytes 4 2) ->
     rdn SEGS m' (Z_to_bv 64 (row4 + 20)) 4 = Some (Z_to_le_bytes 4 0) ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 678036) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 s ret S CK HW0 H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 H13 kR bR RM0 HkR HbR HC.
  unfold SELSTR_WIN in *.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  assert (HTP : ex_keep (getr r0 ex_r4 = Z_to_bv 64 1278416)) by exact H4.
  destruct fx as [fr cs]. pose proof I as FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  replace kR with (kR - 0)%Z in RM0 by lia. replace bR with (bR - 0 * 2 ^ 17)%Z in RM0 by lia.
  pose (valsI := @nil word).
  pose proof (fun (q : word) (_ : ~ In q []) => eq_refl (live A0 q)) as LDEL0.
  assert (GLO1 : (c_top C - LSTK <= s - 1312)%Z) by lia.
  assert (GLO2 : (s - 1312 + Z.of_nat (Z.to_nat 1312) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (1312 <= s)%Z) by lia.
  pose proof (W_sok_win C A0 m0 _ (s - 1312) (Z.to_nat 1312) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 1410112 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0]) (EVar 34) (EVar 32) (exW_canary SEGS 1410112 m0) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0]) m0 [KRange (EVar 32) 1422624 (2 ^ 63); KAlign (EVar 32) 16]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 HKf0)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 1312 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
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
  intros A1 m1 vm1 r1 res0 HW1 Hres0 CSx0 Hnz0 Fselx Lo0 F0sel LEQ0 ZERO0 ALsel TOP0 PMc0 RM1.
  pose proof CSx0 as CS0. clear CSx0.
  rewrite with_vmmaps_twice in HW1 |- *.
  assert (Eres0 : res0 = Z_to_bv 64 (u res0)) by (symmetry; apply zbv_self).
  pose proof (u64_range res0) as RRsel. set (sel := u res0) in *. clearbody sel. rewrite Eres0 in Hres0, Fselx, Lo0, F0sel, LEQ0, ZERO0. clear Eres0.
  change (1 * 32)%Z with 32%Z in *.
  pose proof (exW_blk_img_apart_h2 C A1 m1 _ sel 32 CK HW1 Lo0 RRsel eq_refl eq_refl) as IMGAPsel. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPsel.
  pose proof (exW_win_blk_apart_h C A1 m1 _ s 1312 sel 32 CK HW1 Lo0 eq_refl RRsel GLO1) as WAPsel.
  assert (Fsel : live A0 (Z_to_bv 64 sel) = None).
  { destruct (live A0 (Z_to_bv 64 sel)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB0 _ _ EE) as XX. first [discriminate Fselx | (rewrite Fselx in XX; discriminate XX)]. }
  pose proof Lo0 as Lsel_a1.
  assert (SUB1 : sub_live A0 A1).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 sel) by (intros ->; rewrite Fsel in Lq; discriminate Lq). rewrite (LEQ0 q NEq). exact (SUB0 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 sel :: [])) => eq_trans (LEQ0 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL0 q (fun XX => Hq (or_intror XX)))) as LDEL1.
  assert (PM1 : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|]. apply (POSTM_sub C A0 A0 _ _ _ SUB0).
    apply (POSTM_mono C A0 (s + OFF0) s); [unfold OFF0; lia | exact PMc0]. }
  replace (kR - 0 - 1)%Z with (kR - 1)%Z in RM1 by lia. rewrite MG0 in RM1. replace (bR - 0 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 1 * 2 ^ 17)%Z in RM1 by lia.
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, OFF0, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF0 1312 M0 m1 E0 (EVar 32) CK (proj1 PMc0) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E0 m1 kk') in HKk0 end.
  pose proof (regs_ok_agree 35%nat E0 (ex_envL vals0 r1 [sel; exW_canary SEGS 1410112 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [sel; exW_canary SEGS 1410112 m1] 35%nat ltac:(vm_cast_no_check (eq_refl 35%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [sel; exW_canary SEGS 1410112 m1]) m1 _) by (exact (know_ok_agree SEGS 35%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  rewrite (fr_denot_agree 35%nat E0 (ex_envL vals0 r1 [sel; exW_canary SEGS 1410112 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r1 ex_r10 (EVar 67) HRn1 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres0)) as HRx1. clear HRn1. rename HRx1 into HRn1.
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q11_0 Q1_0 Q2_0 Q4_0 PM0 HW0 PMc0 CS0 SUB0 RM0 MG0 TOP0 LEQ0 Hnz0 Fselx Lo0 OFF0 LDEL0.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  pose proof (exW_kn_blk SEGS C A1 m1 _ (ex_envL vals0 r1 [sel; exW_canary SEGS 1410112 m1]) (EVar 67) (EVar 32) sel 32 s 1312 65536 1347584 p16_segs CK HW1 Lsel_a1 RRsel eq_refl eq_refl eq_refl RS ALsel ZERO0 WAPsel IMGAPsel) as HKb1.
  pose proof (W_sok_win C A1 m1 _ (s - 1312) (Z.to_nat 1312) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 1410112 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [sel; exW_canary SEGS 1410112 m1]).
  pose proof (exW_kn_fixed SEGS C A1 m1 _ (ex_envL vals0 r1 [sel; exW_canary SEGS 1410112 m1]) (EVar 68) (EVar 32) (exW_canary SEGS 1410112 m1) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb1 (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb1 HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO0 ALsel.
  exb_exit ST Rc1 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A1 M1 (with_vmmaps vm1 md) /\ POSTM C A0 s m1 M1).
  { subst M1. apply (exW_win_blks C A1 A0 m1 _ E1 log1 (EVar 32) s 1312 [(EVar 67, sel, 32%Z)] CK HW1 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel (conj Lsel_a1 (conj Fsel F0sel))))|]. constructor. }
  destruct WP1 as [HWs1 PMs1].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log1 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC1 : carry log1 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc1 : know_ok SEGS E1 M1 kn1) by (apply (carry_after SEGS E1 m1 log1 kn0 [] kn1 scs hs HC1 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose (BS1 := [(32%nat, s); (67%nat, sel)]).
  exW_regfactB BS1 HR ex_r10 Q10_1. exW_regfactB BS1 HR ex_r11 Q11_1. exW_regfactB BS1 HR ex_r1 Q1_1. exW_regfactB BS1 HR ex_r2 Q2_1. exW_regfactB BS1 HR ex_r4 Q4_1.
  clear BS1.
  lazymatch type of Q2_1 with _ = Z_to_bv 64 (s + ?off) => pose (OFF1 := off) end.
  pose proof (alloc_margin_small (5 * 8) ltac:(exW_cmp)) as MG1.
  lazymatch type of Q1_1 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_1 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A1 M1 _ Rc1 5 8 (kR - 1) (bR - 1 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs1 Q10_1 Q11_1 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM1) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_1
             ltac:(red; apply bv_eq; reflexivity) Q4_1 Q2_1 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A2 m2 vm2 r2 res1 HW2 Hres1 CSx1 Hnz1 Farrx Lo1 F0arr LEQ1 ZERO1 ALarr TOP1 PMc1 RM2.
  pose proof CSx1 as CS1. clear CSx1.
  rewrite with_vmmaps_twice in HW2 |- *.
  assert (Eres1 : res1 = Z_to_bv 64 (u res1)) by (symmetry; apply zbv_self).
  pose proof (u64_range res1) as RRarr. set (arr := u res1) in *. clearbody arr. rewrite Eres1 in Hres1, Farrx, Lo1, F0arr, LEQ1, ZERO1. clear Eres1.
  change (5 * 8)%Z with 40%Z in *.
  pose proof (exW_blk_img_apart_h2 C A2 m2 _ arr 40 CK HW2 Lo1 RRarr eq_refl eq_refl) as IMGAParr. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAParr.
  pose proof (exW_win_blk_apart_h C A2 m2 _ s 1312 arr 40 CK HW2 Lo1 eq_refl RRarr GLO1) as WAParr.
  assert (Farr : live A0 (Z_to_bv 64 arr) = None).
  { destruct (live A0 (Z_to_bv 64 arr)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB1 _ _ EE) as XX. first [discriminate Farrx | (rewrite Farrx in XX; discriminate XX)]. }
  pose proof Lo1 as Larr_a2.
  assert (SUB2 : sub_live A0 A2).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 arr) by (intros ->; rewrite Farr in Lq; discriminate Lq). rewrite (LEQ1 q NEq). exact (SUB1 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 arr :: [Z_to_bv 64 sel])) => eq_trans (LEQ1 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL1 q (fun XX => Hq (or_intror XX)))) as LDEL2.
  assert (NE_sel_arr : Z_to_bv 64 sel <> Z_to_bv 64 arr) by (intros EE; rewrite EE in Lsel_a1; rewrite Farrx in Lsel_a1; discriminate Lsel_a1).
  assert (Lsel_a2 : live A2 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ1 _ NE_sel_arr); exact Lsel_a1).
  pose proof (exW_blk_apart_h C A2 m2 _ sel arr 32 40 CK HW2 Lsel_a2 Larr_a2 NE_sel_arr RRsel RRarr ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel_arr.
  assert (PM2 : POSTM C A0 s m0 m2).
  { eapply POSTM_trans; [exact PM1|]. eapply POSTM_trans; [exact PMs1|]. apply (POSTM_sub C A0 A1 _ _ _ SUB1).
    apply (POSTM_mono C A1 (s + OFF1) s); [unfold OFF1; lia | exact PMc1]. }
  replace (kR - 1 - 1)%Z with (kR - 2)%Z in RM2 by lia. rewrite MG1 in RM2. replace (bR - 1 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 2 * 2 ^ 17)%Z in RM2 by lia.
  assert (KEPT1 : Forall (ex_region_kept E1 M1 m2) [(EVar 32, OFF1, 0%Z); (EVar 67, 0%Z, 32%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF1 1312 M1 m2 E1 (EVar 32) CK (proj1 PMc1) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A1 A1 M1 _ M1 m2 E1 (EVar 67) sel 32 CK HWs1 Lsel_a1 RRsel eq_refl (proj2 PMc1) Lsel_a1 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E1 M1 m2 _ [] _ HKc1 KEPT1) as HKk1.
  match type of HKk1 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E1 m2 kk') in HKk1 end.
  pose proof (regs_ok_agree 69%nat E1 (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) _ _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa1.
  pose proof (exW_regs_call _ _ _ _ _ HRa1 (ex_regs_ok_junk vals1 r2 [arr; exW_canary SEGS 1410112 m2] 69%nat ltac:(vm_cast_no_check (eq_refl 69%nat))) CS1) as HRn2.
  clear HRa1.
  assert (HKa2 : know_ok SEGS (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) m2 _) by (exact (know_ok_agree SEGS 69%nat E1 _ m2 _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk1)).
  rewrite (fr_denot_agree 69%nat E1 (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) _ fr (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r2 ex_r10 (EVar 101) HRn2 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres1)) as HRx2. clear HRn2. rename HRx2 into HRn2.
  clear HR HK Hlf Hms HKc1 HKk1 KEPT1 HC1 HWs1 PMs1 Q10_1 Q11_1 Q1_1 Q2_1 Q4_1 PM1 HW1 PMc1 CS1 SUB1 RM1 MG1 TOP1 LEQ1 Hnz1 Farrx Lo1 OFF1 LDEL1 Lsel_a1.
  subst M1. clear log1. clear E1. try clear Rc1. clear KN1.
  lazymatch type of HRn2 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn2 end.
  pose proof (exW_kn_blk SEGS C A2 m2 _ (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) (EVar 101) (EVar 32) arr 40 s 1312 65536 1347584 p16_segs CK HW2 Larr_a2 RRarr eq_refl eq_refl eq_refl RS ALarr ZERO1 WAParr IMGAParr) as HKb2.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) m2) _ _ (ex_kdisj_apart SEGS (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) m2 (EVar 67) (EVar 101) sel arr 0 32 0 40 eq_refl eq_refl RRsel RRarr AP_sel_arr) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) m2))) as HKd2.
  pose proof (W_sok_win C A2 m2 _ (s - 1312) (Z.to_nat 1312) CK HW2 GLO1 GLO2) as SOK2.
  pose proof (exW_canary_ok SEGS 1410112 m2 (canary_any m2)) as CANOK2.
  pose (vals2 := vals1 ++ map (getr r2) ex_regs_list ++ map (Z_to_bv 64) [arr; exW_canary SEGS 1410112 m2]).
  pose proof (exW_kn_fixed SEGS C A2 m2 _ (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) (EVar 102) (EVar 32) (exW_canary SEGS 1410112 m2) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW2 eq_refl (proj1 CANOK2) (proj2 CANOK2) eq_refl eq_refl eq_refl SOK2 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf2.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb2 (proj2 (Forall_app _ _ _) (conj HKd2 (proj2 (Forall_app _ _ _) (conj HKf2 HKa2)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn2 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN2 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb2 HKd2 HKf2 HKa2 SOK2 CANOK2.
  repeat match goal with H : getr r2 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO1 ALarr.
  exb_exit ST Rc2 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E2 := EEx) in HR, Hlf, HK, Hms |- *; set (log2 := LLx) in Hms, Hlf; set (M2 := mem_denot E2 m2 log2) in Hms end.
  assert (WP2 : W C A2 M2 (with_vmmaps vm2 md) /\ POSTM C A0 s m2 M2).
  { subst M2. apply (exW_win_blks C A2 A0 m2 _ E2 log2 (EVar 32) s 1312 [(EVar 67, sel, 32%Z); (EVar 101, arr, 40%Z)] CK HW2 SUB2 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel (conj Lsel_a2 (conj Fsel F0sel))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a2 (conj Farr F0arr))))|]. constructor. }
  destruct WP2 as [HWs2 PMs2].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log2 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC2 : carry log2 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc2 : know_ok SEGS E2 M2 kn1) by (apply (carry_after SEGS E2 m2 log2 kn0 [] kn1 scs hs HC2 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact Hms |].
  pose (BS2 := [(32%nat, s); (67%nat, sel); (101%nat, arr)]).
  exW_regfactB BS2 HR ex_r10 Q10_2. exW_regfactB BS2 HR ex_r11 Q11_2. exW_regfactB BS2 HR ex_r1 Q1_2. exW_regfactB BS2 HR ex_r2 Q2_2. exW_regfactB BS2 HR ex_r4 Q4_2.
  clear BS2.
  lazymatch type of Q2_2 with _ = Z_to_bv 64 (s + ?off) => pose (OFF2 := off) end.
  pose proof (alloc_margin_small (6 * 4) ltac:(exW_cmp)) as MG2.
  lazymatch type of Q1_2 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_2 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A2 M2 _ Rc2 6 4 (kR - 2) (bR - 2 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs2 Q10_2 Q11_2 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM2) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_2
             ltac:(red; apply bv_eq; reflexivity) Q4_2 Q2_2 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A3 m3 vm3 r3 res2 HW3 Hres2 CSx2 Hnz2 Frow0x Lo2 F0row0 LEQ2 ZERO2 ALrow0 TOP2 PMc2 RM3.
  pose proof CSx2 as CS2. clear CSx2.
  rewrite with_vmmaps_twice in HW3 |- *.
  assert (Eres2 : res2 = Z_to_bv 64 (u res2)) by (symmetry; apply zbv_self).
  pose proof (u64_range res2) as RRrow0. set (row0 := u res2) in *. clearbody row0. rewrite Eres2 in Hres2, Frow0x, Lo2, F0row0, LEQ2, ZERO2. clear Eres2.
  change (6 * 4)%Z with 24%Z in *.
  pose proof (exW_blk_img_apart_h2 C A3 m3 _ row0 24 CK HW3 Lo2 RRrow0 eq_refl eq_refl) as IMGAProw0. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAProw0.
  pose proof (exW_win_blk_apart_h C A3 m3 _ s 1312 row0 24 CK HW3 Lo2 eq_refl RRrow0 GLO1) as WAProw0.
  assert (Frow0 : live A0 (Z_to_bv 64 row0) = None).
  { destruct (live A0 (Z_to_bv 64 row0)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB2 _ _ EE) as XX. first [discriminate Frow0x | (rewrite Frow0x in XX; discriminate XX)]. }
  pose proof Lo2 as Lrow0_a3.
  assert (SUB3 : sub_live A0 A3).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row0) by (intros ->; rewrite Frow0 in Lq; discriminate Lq). rewrite (LEQ2 q NEq). exact (SUB2 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row0 :: [Z_to_bv 64 arr; Z_to_bv 64 sel])) => eq_trans (LEQ2 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL2 q (fun XX => Hq (or_intror XX)))) as LDEL3.
  assert (NE_sel_row0 : Z_to_bv 64 sel <> Z_to_bv 64 row0) by (intros EE; rewrite EE in Lsel_a2; rewrite Frow0x in Lsel_a2; discriminate Lsel_a2).
  assert (Lsel_a3 : live A3 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ2 _ NE_sel_row0); exact Lsel_a2).
  pose proof (exW_blk_apart_h C A3 m3 _ sel row0 32 24 CK HW3 Lsel_a3 Lrow0_a3 NE_sel_row0 RRsel RRrow0 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel_row0.
  assert (NE_arr_row0 : Z_to_bv 64 arr <> Z_to_bv 64 row0) by (intros EE; rewrite EE in Larr_a2; rewrite Frow0x in Larr_a2; discriminate Larr_a2).
  assert (Larr_a3 : live A3 (Z_to_bv 64 arr) = Some 40%Z) by (rewrite (LEQ2 _ NE_arr_row0); exact Larr_a2).
  pose proof (exW_blk_apart_h C A3 m3 _ arr row0 40 24 CK HW3 Larr_a3 Lrow0_a3 NE_arr_row0 RRarr RRrow0 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_row0.
  assert (PM3 : POSTM C A0 s m0 m3).
  { eapply POSTM_trans; [exact PM2|]. eapply POSTM_trans; [exact PMs2|]. apply (POSTM_sub C A0 A2 _ _ _ SUB2).
    apply (POSTM_mono C A2 (s + OFF2) s); [unfold OFF2; lia | exact PMc2]. }
  replace (kR - 2 - 1)%Z with (kR - 3)%Z in RM3 by lia. rewrite MG2 in RM3. replace (bR - 2 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 3 * 2 ^ 17)%Z in RM3 by lia.
  assert (KEPT2 : Forall (ex_region_kept E2 M2 m3) [(EVar 32, OFF2, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 40%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF2 1312 M2 m3 E2 (EVar 32) CK (proj1 PMc2) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A2 A2 M2 _ M2 m3 E2 (EVar 67) sel 32 CK HWs2 Lsel_a2 RRsel eq_refl (proj2 PMc2) Lsel_a2 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A2 A2 M2 _ M2 m3 E2 (EVar 101) arr 40 CK HWs2 Larr_a2 RRarr eq_refl (proj2 PMc2) Larr_a2 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E2 M2 m3 _ [] _ HKc2 KEPT2) as HKk2.
  match type of HKk2 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E2 m3 kk') in HKk2 end.
  pose proof (regs_ok_agree 103%nat E2 (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) _ _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa2.
  pose proof (exW_regs_call _ _ _ _ _ HRa2 (ex_regs_ok_junk vals2 r3 [row0; exW_canary SEGS 1410112 m3] 103%nat ltac:(vm_cast_no_check (eq_refl 103%nat))) CS2) as HRn3.
  clear HRa2.
  assert (HKa3 : know_ok SEGS (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) m3 _) by (exact (know_ok_agree SEGS 103%nat E2 _ m3 _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk2)).
  rewrite (fr_denot_agree 103%nat E2 (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) _ fr (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r3 ex_r10 (EVar 135) HRn3 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres2)) as HRx3. clear HRn3. rename HRx3 into HRn3.
  clear HR HK Hlf Hms HKc2 HKk2 KEPT2 HC2 HWs2 PMs2 Q10_2 Q11_2 Q1_2 Q2_2 Q4_2 PM2 HW2 PMc2 CS2 SUB2 RM2 MG2 TOP2 LEQ2 Hnz2 Frow0x Lo2 OFF2 LDEL2 Lsel_a2 Larr_a2.
  subst M2. clear log2. clear E2. try clear Rc2. clear KN2.
  lazymatch type of HRn3 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn3 end.
  pose proof (exW_kn_blk SEGS C A3 m3 _ (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) (EVar 135) (EVar 32) row0 24 s 1312 65536 1347584 p16_segs CK HW3 Lrow0_a3 RRrow0 eq_refl eq_refl eq_refl RS ALrow0 ZERO2 WAProw0 IMGAProw0) as HKb3.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) m3) _ _ (ex_kdisj_apart SEGS (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) m3 (EVar 67) (EVar 135) sel row0 0 32 0 24 eq_refl eq_refl RRsel RRrow0 AP_sel_row0) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) m3) _ _ (ex_kdisj_apart SEGS (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) m3 (EVar 101) (EVar 135) arr row0 0 40 0 24 eq_refl eq_refl RRarr RRrow0 AP_arr_row0) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) m3)))) as HKd3.
  pose proof (W_sok_win C A3 m3 _ (s - 1312) (Z.to_nat 1312) CK HW3 GLO1 GLO2) as SOK3.
  pose proof (exW_canary_ok SEGS 1410112 m3 (canary_any m3)) as CANOK3.
  pose (vals3 := vals2 ++ map (getr r3) ex_regs_list ++ map (Z_to_bv 64) [row0; exW_canary SEGS 1410112 m3]).
  pose proof (exW_kn_fixed SEGS C A3 m3 _ (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) (EVar 136) (EVar 32) (exW_canary SEGS 1410112 m3) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW3 eq_refl (proj1 CANOK3) (proj2 CANOK3) eq_refl eq_refl eq_refl SOK3 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf3.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb3 (proj2 (Forall_app _ _ _) (conj HKd3 (proj2 (Forall_app _ _ _) (conj HKf3 HKa3)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn3 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN3 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb3 HKd3 HKf3 HKa3 SOK3 CANOK3.
  repeat match goal with H : getr r3 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO2 ALrow0.
  exb_exit ST Rc3 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E3 := EEx) in HR, Hlf, HK, Hms |- *; set (log3 := LLx) in Hms, Hlf; set (M3 := mem_denot E3 m3 log3) in Hms end.
  assert (WP3 : W C A3 M3 (with_vmmaps vm3 md) /\ POSTM C A0 s m3 M3).
  { subst M3. apply (exW_win_blks C A3 A0 m3 _ E3 log3 (EVar 32) s 1312 [(EVar 67, sel, 32%Z); (EVar 101, arr, 40%Z); (EVar 135, row0, 24%Z)] CK HW3 SUB3 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel (conj Lsel_a3 (conj Fsel F0sel))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a3 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRrow0 (conj Lrow0_a3 (conj Frow0 F0row0))))|]. constructor. }
  destruct WP3 as [HWs3 PMs3].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log3 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC3 : carry log3 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc3 : know_ok SEGS E3 M3 kn1) by (apply (carry_after SEGS E3 m3 log3 kn0 [] kn1 scs hs HC3 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact Hms |].
  pose (BS3 := [(32%nat, s); (67%nat, sel); (101%nat, arr); (135%nat, row0)]).
  exW_regfactB BS3 HR ex_r10 Q10_3. exW_regfactB BS3 HR ex_r11 Q11_3. exW_regfactB BS3 HR ex_r1 Q1_3. exW_regfactB BS3 HR ex_r2 Q2_3. exW_regfactB BS3 HR ex_r4 Q4_3.
  clear BS3.
  lazymatch type of Q2_3 with _ = Z_to_bv 64 (s + ?off) => pose (OFF3 := off) end.
  pose proof (alloc_margin_small (6 * 4) ltac:(exW_cmp)) as MG3.
  lazymatch type of Q1_3 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_3 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A3 M3 _ Rc3 6 4 (kR - 3) (bR - 3 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs3 Q10_3 Q11_3 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM3) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_3
             ltac:(red; apply bv_eq; reflexivity) Q4_3 Q2_3 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A4 m4 vm4 r4 res3 HW4 Hres3 CSx3 Hnz3 Frow1x Lo3 F0row1 LEQ3 ZERO3 ALrow1 TOP3 PMc3 RM4.
  pose proof CSx3 as CS3. clear CSx3.
  rewrite with_vmmaps_twice in HW4 |- *.
  assert (Eres3 : res3 = Z_to_bv 64 (u res3)) by (symmetry; apply zbv_self).
  pose proof (u64_range res3) as RRrow1. set (row1 := u res3) in *. clearbody row1. rewrite Eres3 in Hres3, Frow1x, Lo3, F0row1, LEQ3, ZERO3. clear Eres3.
  change (6 * 4)%Z with 24%Z in *.
  pose proof (exW_blk_img_apart_h2 C A4 m4 _ row1 24 CK HW4 Lo3 RRrow1 eq_refl eq_refl) as IMGAProw1. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAProw1.
  pose proof (exW_win_blk_apart_h C A4 m4 _ s 1312 row1 24 CK HW4 Lo3 eq_refl RRrow1 GLO1) as WAProw1.
  assert (Frow1 : live A0 (Z_to_bv 64 row1) = None).
  { destruct (live A0 (Z_to_bv 64 row1)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB3 _ _ EE) as XX. first [discriminate Frow1x | (rewrite Frow1x in XX; discriminate XX)]. }
  pose proof Lo3 as Lrow1_a4.
  assert (SUB4 : sub_live A0 A4).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row1) by (intros ->; rewrite Frow1 in Lq; discriminate Lq). rewrite (LEQ3 q NEq). exact (SUB3 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row1 :: [Z_to_bv 64 row0; Z_to_bv 64 arr; Z_to_bv 64 sel])) => eq_trans (LEQ3 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL3 q (fun XX => Hq (or_intror XX)))) as LDEL4.
  assert (NE_sel_row1 : Z_to_bv 64 sel <> Z_to_bv 64 row1) by (intros EE; rewrite EE in Lsel_a3; rewrite Frow1x in Lsel_a3; discriminate Lsel_a3).
  assert (Lsel_a4 : live A4 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ3 _ NE_sel_row1); exact Lsel_a3).
  pose proof (exW_blk_apart_h C A4 m4 _ sel row1 32 24 CK HW4 Lsel_a4 Lrow1_a4 NE_sel_row1 RRsel RRrow1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel_row1.
  assert (NE_arr_row1 : Z_to_bv 64 arr <> Z_to_bv 64 row1) by (intros EE; rewrite EE in Larr_a3; rewrite Frow1x in Larr_a3; discriminate Larr_a3).
  assert (Larr_a4 : live A4 (Z_to_bv 64 arr) = Some 40%Z) by (rewrite (LEQ3 _ NE_arr_row1); exact Larr_a3).
  pose proof (exW_blk_apart_h C A4 m4 _ arr row1 40 24 CK HW4 Larr_a4 Lrow1_a4 NE_arr_row1 RRarr RRrow1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_row1.
  assert (NE_row0_row1 : Z_to_bv 64 row0 <> Z_to_bv 64 row1) by (intros EE; rewrite EE in Lrow0_a3; rewrite Frow1x in Lrow0_a3; discriminate Lrow0_a3).
  assert (Lrow0_a4 : live A4 (Z_to_bv 64 row0) = Some 24%Z) by (rewrite (LEQ3 _ NE_row0_row1); exact Lrow0_a3).
  pose proof (exW_blk_apart_h C A4 m4 _ row0 row1 24 24 CK HW4 Lrow0_a4 Lrow1_a4 NE_row0_row1 RRrow0 RRrow1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row0_row1.
  assert (PM4 : POSTM C A0 s m0 m4).
  { eapply POSTM_trans; [exact PM3|]. eapply POSTM_trans; [exact PMs3|]. apply (POSTM_sub C A0 A3 _ _ _ SUB3).
    apply (POSTM_mono C A3 (s + OFF3) s); [unfold OFF3; lia | exact PMc3]. }
  replace (kR - 3 - 1)%Z with (kR - 4)%Z in RM4 by lia. rewrite MG3 in RM4. replace (bR - 3 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 4 * 2 ^ 17)%Z in RM4 by lia.
  assert (KEPT3 : Forall (ex_region_kept E3 M3 m4) [(EVar 32, OFF3, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 40%Z); (EVar 135, 0%Z, 24%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF3 1312 M3 m4 E3 (EVar 32) CK (proj1 PMc3) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A3 A3 M3 _ M3 m4 E3 (EVar 67) sel 32 CK HWs3 Lsel_a3 RRsel eq_refl (proj2 PMc3) Lsel_a3 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A3 A3 M3 _ M3 m4 E3 (EVar 101) arr 40 CK HWs3 Larr_a3 RRarr eq_refl (proj2 PMc3) Larr_a3 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A3 A3 M3 _ M3 m4 E3 (EVar 135) row0 24 CK HWs3 Lrow0_a3 RRrow0 eq_refl (proj2 PMc3) Lrow0_a3 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E3 M3 m4 _ [] _ HKc3 KEPT3) as HKk3.
  match type of HKk3 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E3 m4 kk') in HKk3 end.
  pose proof (regs_ok_agree 137%nat E3 (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) _ _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa3.
  pose proof (exW_regs_call _ _ _ _ _ HRa3 (ex_regs_ok_junk vals3 r4 [row1; exW_canary SEGS 1410112 m4] 137%nat ltac:(vm_cast_no_check (eq_refl 137%nat))) CS3) as HRn4.
  clear HRa3.
  assert (HKa4 : know_ok SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4 _) by (exact (know_ok_agree SEGS 137%nat E3 _ m4 _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk3)).
  rewrite (fr_denot_agree 137%nat E3 (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) _ fr (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r4 ex_r10 (EVar 169) HRn4 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres3)) as HRx4. clear HRn4. rename HRx4 into HRn4.
  clear HR HK Hlf Hms HKc3 HKk3 KEPT3 HC3 HWs3 PMs3 Q10_3 Q11_3 Q1_3 Q2_3 Q4_3 PM3 HW3 PMc3 CS3 SUB3 RM3 MG3 TOP3 LEQ3 Hnz3 Frow1x Lo3 OFF3 LDEL3 Lsel_a3 Larr_a3 Lrow0_a3.
  subst M3. clear log3. clear E3. try clear Rc3. clear KN3.
  lazymatch type of HRn4 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn4 end.
  pose proof (exW_kn_blk SEGS C A4 m4 _ (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) (EVar 169) (EVar 32) row1 24 s 1312 65536 1347584 p16_segs CK HW4 Lrow1_a4 RRrow1 eq_refl eq_refl eq_refl RS ALrow1 ZERO3 WAProw1 IMGAProw1) as HKb4.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4) _ _ (ex_kdisj_apart SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4 (EVar 67) (EVar 169) sel row1 0 32 0 24 eq_refl eq_refl RRsel RRrow1 AP_sel_row1) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4) _ _ (ex_kdisj_apart SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4 (EVar 101) (EVar 169) arr row1 0 40 0 24 eq_refl eq_refl RRarr RRrow1 AP_arr_row1) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4) _ _ (ex_kdisj_apart SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4 (EVar 135) (EVar 169) row0 row1 0 24 0 24 eq_refl eq_refl RRrow0 RRrow1 AP_row0_row1) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4))))) as HKd4.
  pose proof (W_sok_win C A4 m4 _ (s - 1312) (Z.to_nat 1312) CK HW4 GLO1 GLO2) as SOK4.
  pose proof (exW_canary_ok SEGS 1410112 m4 (canary_any m4)) as CANOK4.
  pose (vals4 := vals3 ++ map (getr r4) ex_regs_list ++ map (Z_to_bv 64) [row1; exW_canary SEGS 1410112 m4]).
  pose proof (exW_kn_fixed SEGS C A4 m4 _ (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) (EVar 170) (EVar 32) (exW_canary SEGS 1410112 m4) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW4 eq_refl (proj1 CANOK4) (proj2 CANOK4) eq_refl eq_refl eq_refl SOK4 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf4.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb4 (proj2 (Forall_app _ _ _) (conj HKd4 (proj2 (Forall_app _ _ _) (conj HKf4 HKa4)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn4 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN4 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb4 HKd4 HKf4 HKa4 SOK4 CANOK4.
  repeat match goal with H : getr r4 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO3 ALrow1.
  exb_exit ST Rc4 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E4 := EEx) in HR, Hlf, HK, Hms |- *; set (log4 := LLx) in Hms, Hlf; set (M4 := mem_denot E4 m4 log4) in Hms end.
  assert (WP4 : W C A4 M4 (with_vmmaps vm4 md) /\ POSTM C A0 s m4 M4).
  { subst M4. apply (exW_win_blks C A4 A0 m4 _ E4 log4 (EVar 32) s 1312 [(EVar 67, sel, 32%Z); (EVar 101, arr, 40%Z); (EVar 135, row0, 24%Z); (EVar 169, row1, 24%Z)] CK HW4 SUB4 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel (conj Lsel_a4 (conj Fsel F0sel))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a4 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRrow0 (conj Lrow0_a4 (conj Frow0 F0row0))))|]. constructor; [exact (conj eq_refl (conj RRrow1 (conj Lrow1_a4 (conj Frow1 F0row1))))|]. constructor. }
  destruct WP4 as [HWs4 PMs4].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log4 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC4 : carry log4 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc4 : know_ok SEGS E4 M4 kn1) by (apply (carry_after SEGS E4 m4 log4 kn0 [] kn1 scs hs HC4 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact Hms |].
  pose (BS4 := [(32%nat, s); (67%nat, sel); (101%nat, arr); (135%nat, row0); (169%nat, row1)]).
  exW_regfactB BS4 HR ex_r10 Q10_4. exW_regfactB BS4 HR ex_r11 Q11_4. exW_regfactB BS4 HR ex_r1 Q1_4. exW_regfactB BS4 HR ex_r2 Q2_4. exW_regfactB BS4 HR ex_r4 Q4_4.
  clear BS4.
  lazymatch type of Q2_4 with _ = Z_to_bv 64 (s + ?off) => pose (OFF4 := off) end.
  pose proof (alloc_margin_small (6 * 4) ltac:(exW_cmp)) as MG4.
  lazymatch type of Q1_4 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_4 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A4 M4 _ Rc4 6 4 (kR - 4) (bR - 4 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs4 Q10_4 Q11_4 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM4) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_4
             ltac:(red; apply bv_eq; reflexivity) Q4_4 Q2_4 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A5 m5 vm5 r5 res4 HW5 Hres4 CSx4 Hnz4 Frow2x Lo4 F0row2 LEQ4 ZERO4 ALrow2 TOP4 PMc4 RM5.
  pose proof CSx4 as CS4. clear CSx4.
  rewrite with_vmmaps_twice in HW5 |- *.
  assert (Eres4 : res4 = Z_to_bv 64 (u res4)) by (symmetry; apply zbv_self).
  pose proof (u64_range res4) as RRrow2. set (row2 := u res4) in *. clearbody row2. rewrite Eres4 in Hres4, Frow2x, Lo4, F0row2, LEQ4, ZERO4. clear Eres4.
  change (6 * 4)%Z with 24%Z in *.
  pose proof (exW_blk_img_apart_h2 C A5 m5 _ row2 24 CK HW5 Lo4 RRrow2 eq_refl eq_refl) as IMGAProw2. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAProw2.
  pose proof (exW_win_blk_apart_h C A5 m5 _ s 1312 row2 24 CK HW5 Lo4 eq_refl RRrow2 GLO1) as WAProw2.
  assert (Frow2 : live A0 (Z_to_bv 64 row2) = None).
  { destruct (live A0 (Z_to_bv 64 row2)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB4 _ _ EE) as XX. first [discriminate Frow2x | (rewrite Frow2x in XX; discriminate XX)]. }
  pose proof Lo4 as Lrow2_a5.
  assert (SUB5 : sub_live A0 A5).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row2) by (intros ->; rewrite Frow2 in Lq; discriminate Lq). rewrite (LEQ4 q NEq). exact (SUB4 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row2 :: [Z_to_bv 64 row1; Z_to_bv 64 row0; Z_to_bv 64 arr; Z_to_bv 64 sel])) => eq_trans (LEQ4 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL4 q (fun XX => Hq (or_intror XX)))) as LDEL5.
  assert (NE_sel_row2 : Z_to_bv 64 sel <> Z_to_bv 64 row2) by (intros EE; rewrite EE in Lsel_a4; rewrite Frow2x in Lsel_a4; discriminate Lsel_a4).
  assert (Lsel_a5 : live A5 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ4 _ NE_sel_row2); exact Lsel_a4).
  pose proof (exW_blk_apart_h C A5 m5 _ sel row2 32 24 CK HW5 Lsel_a5 Lrow2_a5 NE_sel_row2 RRsel RRrow2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel_row2.
  assert (NE_arr_row2 : Z_to_bv 64 arr <> Z_to_bv 64 row2) by (intros EE; rewrite EE in Larr_a4; rewrite Frow2x in Larr_a4; discriminate Larr_a4).
  assert (Larr_a5 : live A5 (Z_to_bv 64 arr) = Some 40%Z) by (rewrite (LEQ4 _ NE_arr_row2); exact Larr_a4).
  pose proof (exW_blk_apart_h C A5 m5 _ arr row2 40 24 CK HW5 Larr_a5 Lrow2_a5 NE_arr_row2 RRarr RRrow2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_row2.
  assert (NE_row0_row2 : Z_to_bv 64 row0 <> Z_to_bv 64 row2) by (intros EE; rewrite EE in Lrow0_a4; rewrite Frow2x in Lrow0_a4; discriminate Lrow0_a4).
  assert (Lrow0_a5 : live A5 (Z_to_bv 64 row0) = Some 24%Z) by (rewrite (LEQ4 _ NE_row0_row2); exact Lrow0_a4).
  pose proof (exW_blk_apart_h C A5 m5 _ row0 row2 24 24 CK HW5 Lrow0_a5 Lrow2_a5 NE_row0_row2 RRrow0 RRrow2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row0_row2.
  assert (NE_row1_row2 : Z_to_bv 64 row1 <> Z_to_bv 64 row2) by (intros EE; rewrite EE in Lrow1_a4; rewrite Frow2x in Lrow1_a4; discriminate Lrow1_a4).
  assert (Lrow1_a5 : live A5 (Z_to_bv 64 row1) = Some 24%Z) by (rewrite (LEQ4 _ NE_row1_row2); exact Lrow1_a4).
  pose proof (exW_blk_apart_h C A5 m5 _ row1 row2 24 24 CK HW5 Lrow1_a5 Lrow2_a5 NE_row1_row2 RRrow1 RRrow2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row1_row2.
  assert (PM5 : POSTM C A0 s m0 m5).
  { eapply POSTM_trans; [exact PM4|]. eapply POSTM_trans; [exact PMs4|]. apply (POSTM_sub C A0 A4 _ _ _ SUB4).
    apply (POSTM_mono C A4 (s + OFF4) s); [unfold OFF4; lia | exact PMc4]. }
  replace (kR - 4 - 1)%Z with (kR - 5)%Z in RM5 by lia. rewrite MG4 in RM5. replace (bR - 4 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 5 * 2 ^ 17)%Z in RM5 by lia.
  assert (KEPT4 : Forall (ex_region_kept E4 M4 m5) [(EVar 32, OFF4, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 40%Z); (EVar 135, 0%Z, 24%Z); (EVar 169, 0%Z, 24%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF4 1312 M4 m5 E4 (EVar 32) CK (proj1 PMc4) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 M4 _ M4 m5 E4 (EVar 67) sel 32 CK HWs4 Lsel_a4 RRsel eq_refl (proj2 PMc4) Lsel_a4 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 M4 _ M4 m5 E4 (EVar 101) arr 40 CK HWs4 Larr_a4 RRarr eq_refl (proj2 PMc4) Larr_a4 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 M4 _ M4 m5 E4 (EVar 135) row0 24 CK HWs4 Lrow0_a4 RRrow0 eq_refl (proj2 PMc4) Lrow0_a4 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 M4 _ M4 m5 E4 (EVar 169) row1 24 CK HWs4 Lrow1_a4 RRrow1 eq_refl (proj2 PMc4) Lrow1_a4 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E4 M4 m5 _ [] _ HKc4 KEPT4) as HKk4.
  match type of HKk4 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E4 m5 kk') in HKk4 end.
  pose proof (regs_ok_agree 171%nat E4 (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) _ _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa4.
  pose proof (exW_regs_call _ _ _ _ _ HRa4 (ex_regs_ok_junk vals4 r5 [row2; exW_canary SEGS 1410112 m5] 171%nat ltac:(vm_cast_no_check (eq_refl 171%nat))) CS4) as HRn5.
  clear HRa4.
  assert (HKa5 : know_ok SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5 _) by (exact (know_ok_agree SEGS 171%nat E4 _ m5 _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk4)).
  rewrite (fr_denot_agree 171%nat E4 (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) _ fr (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r5 ex_r10 (EVar 203) HRn5 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres4)) as HRx5. clear HRn5. rename HRx5 into HRn5.
  clear HR HK Hlf Hms HKc4 HKk4 KEPT4 HC4 HWs4 PMs4 Q10_4 Q11_4 Q1_4 Q2_4 Q4_4 PM4 HW4 PMc4 CS4 SUB4 RM4 MG4 TOP4 LEQ4 Hnz4 Frow2x Lo4 OFF4 LDEL4 Lsel_a4 Larr_a4 Lrow0_a4 Lrow1_a4.
  subst M4. clear log4. clear E4. try clear Rc4. clear KN4.
  lazymatch type of HRn5 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn5 end.
  pose proof (exW_kn_blk SEGS C A5 m5 _ (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) (EVar 203) (EVar 32) row2 24 s 1312 65536 1347584 p16_segs CK HW5 Lrow2_a5 RRrow2 eq_refl eq_refl eq_refl RS ALrow2 ZERO4 WAProw2 IMGAProw2) as HKb5.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5) _ _ (ex_kdisj_apart SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5 (EVar 67) (EVar 203) sel row2 0 32 0 24 eq_refl eq_refl RRsel RRrow2 AP_sel_row2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5) _ _ (ex_kdisj_apart SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5 (EVar 101) (EVar 203) arr row2 0 40 0 24 eq_refl eq_refl RRarr RRrow2 AP_arr_row2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5) _ _ (ex_kdisj_apart SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5 (EVar 135) (EVar 203) row0 row2 0 24 0 24 eq_refl eq_refl RRrow0 RRrow2 AP_row0_row2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5) _ _ (ex_kdisj_apart SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5 (EVar 169) (EVar 203) row1 row2 0 24 0 24 eq_refl eq_refl RRrow1 RRrow2 AP_row1_row2) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5)))))) as HKd5.
  pose proof (W_sok_win C A5 m5 _ (s - 1312) (Z.to_nat 1312) CK HW5 GLO1 GLO2) as SOK5.
  pose proof (exW_canary_ok SEGS 1410112 m5 (canary_any m5)) as CANOK5.
  pose (vals5 := vals4 ++ map (getr r5) ex_regs_list ++ map (Z_to_bv 64) [row2; exW_canary SEGS 1410112 m5]).
  pose proof (exW_kn_fixed SEGS C A5 m5 _ (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) (EVar 204) (EVar 32) (exW_canary SEGS 1410112 m5) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW5 eq_refl (proj1 CANOK5) (proj2 CANOK5) eq_refl eq_refl eq_refl SOK5 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf5.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb5 (proj2 (Forall_app _ _ _) (conj HKd5 (proj2 (Forall_app _ _ _) (conj HKf5 HKa5)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn5 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN5 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb5 HKd5 HKf5 HKa5 SOK5 CANOK5.
  repeat match goal with H : getr r5 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO4 ALrow2.
  exb_exit ST Rc5 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E5 := EEx) in HR, Hlf, HK, Hms |- *; set (log5 := LLx) in Hms, Hlf; set (M5 := mem_denot E5 m5 log5) in Hms end.
  assert (WP5 : W C A5 M5 (with_vmmaps vm5 md) /\ POSTM C A0 s m5 M5).
  { subst M5. apply (exW_win_blks C A5 A0 m5 _ E5 log5 (EVar 32) s 1312 [(EVar 67, sel, 32%Z); (EVar 101, arr, 40%Z); (EVar 135, row0, 24%Z); (EVar 169, row1, 24%Z); (EVar 203, row2, 24%Z)] CK HW5 SUB5 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel (conj Lsel_a5 (conj Fsel F0sel))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a5 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRrow0 (conj Lrow0_a5 (conj Frow0 F0row0))))|]. constructor; [exact (conj eq_refl (conj RRrow1 (conj Lrow1_a5 (conj Frow1 F0row1))))|]. constructor; [exact (conj eq_refl (conj RRrow2 (conj Lrow2_a5 (conj Frow2 F0row2))))|]. constructor. }
  destruct WP5 as [HWs5 PMs5].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log5 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC5 : carry log5 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc5 : know_ok SEGS E5 M5 kn1) by (apply (carry_after SEGS E5 m5 log5 kn0 [] kn1 scs hs HC5 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact Hms |].
  pose (BS5 := [(32%nat, s); (67%nat, sel); (101%nat, arr); (135%nat, row0); (169%nat, row1); (203%nat, row2)]).
  exW_regfactB BS5 HR ex_r10 Q10_5. exW_regfactB BS5 HR ex_r11 Q11_5. exW_regfactB BS5 HR ex_r1 Q1_5. exW_regfactB BS5 HR ex_r2 Q2_5. exW_regfactB BS5 HR ex_r4 Q4_5.
  clear BS5.
  lazymatch type of Q2_5 with _ = Z_to_bv 64 (s + ?off) => pose (OFF5 := off) end.
  pose proof (alloc_margin_small (6 * 4) ltac:(exW_cmp)) as MG5.
  lazymatch type of Q1_5 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_5 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A5 M5 _ Rc5 6 4 (kR - 5) (bR - 5 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs5 Q10_5 Q11_5 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM5) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_5
             ltac:(red; apply bv_eq; reflexivity) Q4_5 Q2_5 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A6 m6 vm6 r6 res5 HW6 Hres5 CSx5 Hnz5 Frow3x Lo5 F0row3 LEQ5 ZERO5 ALrow3 TOP5 PMc5 RM6.
  pose proof CSx5 as CS5. clear CSx5.
  rewrite with_vmmaps_twice in HW6 |- *.
  assert (Eres5 : res5 = Z_to_bv 64 (u res5)) by (symmetry; apply zbv_self).
  pose proof (u64_range res5) as RRrow3. set (row3 := u res5) in *. clearbody row3. rewrite Eres5 in Hres5, Frow3x, Lo5, F0row3, LEQ5, ZERO5. clear Eres5.
  change (6 * 4)%Z with 24%Z in *.
  pose proof (exW_blk_img_apart_h2 C A6 m6 _ row3 24 CK HW6 Lo5 RRrow3 eq_refl eq_refl) as IMGAProw3. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAProw3.
  pose proof (exW_win_blk_apart_h C A6 m6 _ s 1312 row3 24 CK HW6 Lo5 eq_refl RRrow3 GLO1) as WAProw3.
  assert (Frow3 : live A0 (Z_to_bv 64 row3) = None).
  { destruct (live A0 (Z_to_bv 64 row3)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB5 _ _ EE) as XX. first [discriminate Frow3x | (rewrite Frow3x in XX; discriminate XX)]. }
  pose proof Lo5 as Lrow3_a6.
  assert (SUB6 : sub_live A0 A6).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row3) by (intros ->; rewrite Frow3 in Lq; discriminate Lq). rewrite (LEQ5 q NEq). exact (SUB5 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row3 :: [Z_to_bv 64 row2; Z_to_bv 64 row1; Z_to_bv 64 row0; Z_to_bv 64 arr; Z_to_bv 64 sel])) => eq_trans (LEQ5 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL5 q (fun XX => Hq (or_intror XX)))) as LDEL6.
  assert (NE_sel_row3 : Z_to_bv 64 sel <> Z_to_bv 64 row3) by (intros EE; rewrite EE in Lsel_a5; rewrite Frow3x in Lsel_a5; discriminate Lsel_a5).
  assert (Lsel_a6 : live A6 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ5 _ NE_sel_row3); exact Lsel_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ sel row3 32 24 CK HW6 Lsel_a6 Lrow3_a6 NE_sel_row3 RRsel RRrow3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel_row3.
  assert (NE_arr_row3 : Z_to_bv 64 arr <> Z_to_bv 64 row3) by (intros EE; rewrite EE in Larr_a5; rewrite Frow3x in Larr_a5; discriminate Larr_a5).
  assert (Larr_a6 : live A6 (Z_to_bv 64 arr) = Some 40%Z) by (rewrite (LEQ5 _ NE_arr_row3); exact Larr_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ arr row3 40 24 CK HW6 Larr_a6 Lrow3_a6 NE_arr_row3 RRarr RRrow3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_row3.
  assert (NE_row0_row3 : Z_to_bv 64 row0 <> Z_to_bv 64 row3) by (intros EE; rewrite EE in Lrow0_a5; rewrite Frow3x in Lrow0_a5; discriminate Lrow0_a5).
  assert (Lrow0_a6 : live A6 (Z_to_bv 64 row0) = Some 24%Z) by (rewrite (LEQ5 _ NE_row0_row3); exact Lrow0_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ row0 row3 24 24 CK HW6 Lrow0_a6 Lrow3_a6 NE_row0_row3 RRrow0 RRrow3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row0_row3.
  assert (NE_row1_row3 : Z_to_bv 64 row1 <> Z_to_bv 64 row3) by (intros EE; rewrite EE in Lrow1_a5; rewrite Frow3x in Lrow1_a5; discriminate Lrow1_a5).
  assert (Lrow1_a6 : live A6 (Z_to_bv 64 row1) = Some 24%Z) by (rewrite (LEQ5 _ NE_row1_row3); exact Lrow1_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ row1 row3 24 24 CK HW6 Lrow1_a6 Lrow3_a6 NE_row1_row3 RRrow1 RRrow3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row1_row3.
  assert (NE_row2_row3 : Z_to_bv 64 row2 <> Z_to_bv 64 row3) by (intros EE; rewrite EE in Lrow2_a5; rewrite Frow3x in Lrow2_a5; discriminate Lrow2_a5).
  assert (Lrow2_a6 : live A6 (Z_to_bv 64 row2) = Some 24%Z) by (rewrite (LEQ5 _ NE_row2_row3); exact Lrow2_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ row2 row3 24 24 CK HW6 Lrow2_a6 Lrow3_a6 NE_row2_row3 RRrow2 RRrow3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row2_row3.
  assert (PM6 : POSTM C A0 s m0 m6).
  { eapply POSTM_trans; [exact PM5|]. eapply POSTM_trans; [exact PMs5|]. apply (POSTM_sub C A0 A5 _ _ _ SUB5).
    apply (POSTM_mono C A5 (s + OFF5) s); [unfold OFF5; lia | exact PMc5]. }
  replace (kR - 5 - 1)%Z with (kR - 6)%Z in RM6 by lia. rewrite MG5 in RM6. replace (bR - 5 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 6 * 2 ^ 17)%Z in RM6 by lia.
  assert (KEPT5 : Forall (ex_region_kept E5 M5 m6) [(EVar 32, OFF5, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 40%Z); (EVar 135, 0%Z, 24%Z); (EVar 169, 0%Z, 24%Z); (EVar 203, 0%Z, 24%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF5 1312 M5 m6 E5 (EVar 32) CK (proj1 PMc5) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 67) sel 32 CK HWs5 Lsel_a5 RRsel eq_refl (proj2 PMc5) Lsel_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 101) arr 40 CK HWs5 Larr_a5 RRarr eq_refl (proj2 PMc5) Larr_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 135) row0 24 CK HWs5 Lrow0_a5 RRrow0 eq_refl (proj2 PMc5) Lrow0_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 169) row1 24 CK HWs5 Lrow1_a5 RRrow1 eq_refl (proj2 PMc5) Lrow1_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 203) row2 24 CK HWs5 Lrow2_a5 RRrow2 eq_refl (proj2 PMc5) Lrow2_a5 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E5 M5 m6 _ [] _ HKc5 KEPT5) as HKk5.
  match type of HKk5 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E5 m6 kk') in HKk5 end.
  pose proof (regs_ok_agree 205%nat E5 (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) _ _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa5.
  pose proof (exW_regs_call _ _ _ _ _ HRa5 (ex_regs_ok_junk vals5 r6 [row3; exW_canary SEGS 1410112 m6] 205%nat ltac:(vm_cast_no_check (eq_refl 205%nat))) CS5) as HRn6.
  clear HRa5.
  assert (HKa6 : know_ok SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6 _) by (exact (know_ok_agree SEGS 205%nat E5 _ m6 _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk5)).
  rewrite (fr_denot_agree 205%nat E5 (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) _ fr (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r6 ex_r10 (EVar 237) HRn6 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres5)) as HRx6. clear HRn6. rename HRx6 into HRn6.
  clear HR HK Hlf Hms HKc5 HKk5 KEPT5 HC5 HWs5 PMs5 Q10_5 Q11_5 Q1_5 Q2_5 Q4_5 PM5 HW5 PMc5 CS5 SUB5 RM5 MG5 TOP5 LEQ5 Hnz5 Frow3x Lo5 OFF5 LDEL5 Lsel_a5 Larr_a5 Lrow0_a5 Lrow1_a5 Lrow2_a5.
  subst M5. clear log5. clear E5. try clear Rc5. clear KN5.
  lazymatch type of HRn6 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn6 end.
  pose proof (exW_kn_blk SEGS C A6 m6 _ (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) (EVar 237) (EVar 32) row3 24 s 1312 65536 1347584 p16_segs CK HW6 Lrow3_a6 RRrow3 eq_refl eq_refl eq_refl RS ALrow3 ZERO5 WAProw3 IMGAProw3) as HKb6.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6 (EVar 67) (EVar 237) sel row3 0 32 0 24 eq_refl eq_refl RRsel RRrow3 AP_sel_row3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6 (EVar 101) (EVar 237) arr row3 0 40 0 24 eq_refl eq_refl RRarr RRrow3 AP_arr_row3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6 (EVar 135) (EVar 237) row0 row3 0 24 0 24 eq_refl eq_refl RRrow0 RRrow3 AP_row0_row3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6 (EVar 169) (EVar 237) row1 row3 0 24 0 24 eq_refl eq_refl RRrow1 RRrow3 AP_row1_row3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6 (EVar 203) (EVar 237) row2 row3 0 24 0 24 eq_refl eq_refl RRrow2 RRrow3 AP_row2_row3) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6))))))) as HKd6.
  pose proof (W_sok_win C A6 m6 _ (s - 1312) (Z.to_nat 1312) CK HW6 GLO1 GLO2) as SOK6.
  pose proof (exW_canary_ok SEGS 1410112 m6 (canary_any m6)) as CANOK6.
  pose (vals6 := vals5 ++ map (getr r6) ex_regs_list ++ map (Z_to_bv 64) [row3; exW_canary SEGS 1410112 m6]).
  pose proof (exW_kn_fixed SEGS C A6 m6 _ (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) (EVar 238) (EVar 32) (exW_canary SEGS 1410112 m6) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW6 eq_refl (proj1 CANOK6) (proj2 CANOK6) eq_refl eq_refl eq_refl SOK6 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf6.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb6 (proj2 (Forall_app _ _ _) (conj HKd6 (proj2 (Forall_app _ _ _) (conj HKf6 HKa6)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn6 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN6 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb6 HKd6 HKf6 HKa6 SOK6 CANOK6.
  repeat match goal with H : getr r6 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO5 ALrow3.
  exb_exit ST Rc6 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E6 := EEx) in HR, Hlf, HK, Hms |- *; set (log6 := LLx) in Hms, Hlf; set (M6 := mem_denot E6 m6 log6) in Hms end.
  assert (WP6 : W C A6 M6 (with_vmmaps vm6 md) /\ POSTM C A0 s m6 M6).
  { subst M6. apply (exW_win_blks C A6 A0 m6 _ E6 log6 (EVar 32) s 1312 [(EVar 67, sel, 32%Z); (EVar 101, arr, 40%Z); (EVar 135, row0, 24%Z); (EVar 169, row1, 24%Z); (EVar 203, row2, 24%Z); (EVar 237, row3, 24%Z)] CK HW6 SUB6 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel (conj Lsel_a6 (conj Fsel F0sel))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a6 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRrow0 (conj Lrow0_a6 (conj Frow0 F0row0))))|]. constructor; [exact (conj eq_refl (conj RRrow1 (conj Lrow1_a6 (conj Frow1 F0row1))))|]. constructor; [exact (conj eq_refl (conj RRrow2 (conj Lrow2_a6 (conj Frow2 F0row2))))|]. constructor; [exact (conj eq_refl (conj RRrow3 (conj Lrow3_a6 (conj Frow3 F0row3))))|]. constructor. }
  destruct WP6 as [HWs6 PMs6].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log6 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC6 : carry log6 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc6 : know_ok SEGS E6 M6 kn1) by (apply (carry_after SEGS E6 m6 log6 kn0 [] kn1 scs hs HC6 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact Hms |].
  pose (BS6 := [(32%nat, s); (67%nat, sel); (101%nat, arr); (135%nat, row0); (169%nat, row1); (203%nat, row2); (237%nat, row3)]).
  exW_regfactB BS6 HR ex_r10 Q10_6. exW_regfactB BS6 HR ex_r11 Q11_6. exW_regfactB BS6 HR ex_r1 Q1_6. exW_regfactB BS6 HR ex_r2 Q2_6. exW_regfactB BS6 HR ex_r4 Q4_6.
  clear BS6.
  lazymatch type of Q2_6 with _ = Z_to_bv 64 (s + ?off) => pose (OFF6 := off) end.
  pose proof (alloc_margin_small (6 * 4) ltac:(exW_cmp)) as MG6.
  lazymatch type of Q1_6 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_6 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A6 M6 _ Rc6 6 4 (kR - 6) (bR - 6 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs6 Q10_6 Q11_6 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM6) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_6
             ltac:(red; apply bv_eq; reflexivity) Q4_6 Q2_6 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A7 m7 vm7 r7 res6 HW7 Hres6 CSx6 Hnz6 Frow4x Lo6 F0row4 LEQ6 ZERO6 ALrow4 TOP6 PMc6 RM7.
  pose proof CSx6 as CS6. clear CSx6.
  rewrite with_vmmaps_twice in HW7 |- *.
  assert (Eres6 : res6 = Z_to_bv 64 (u res6)) by (symmetry; apply zbv_self).
  pose proof (u64_range res6) as RRrow4. set (row4 := u res6) in *. clearbody row4. rewrite Eres6 in Hres6, Frow4x, Lo6, F0row4, LEQ6, ZERO6. clear Eres6.
  change (6 * 4)%Z with 24%Z in *.
  pose proof (exW_blk_img_apart_h2 C A7 m7 _ row4 24 CK HW7 Lo6 RRrow4 eq_refl eq_refl) as IMGAProw4. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAProw4.
  pose proof (exW_win_blk_apart_h C A7 m7 _ s 1312 row4 24 CK HW7 Lo6 eq_refl RRrow4 GLO1) as WAProw4.
  assert (Frow4 : live A0 (Z_to_bv 64 row4) = None).
  { destruct (live A0 (Z_to_bv 64 row4)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB6 _ _ EE) as XX. first [discriminate Frow4x | (rewrite Frow4x in XX; discriminate XX)]. }
  pose proof Lo6 as Lrow4_a7.
  assert (SUB7 : sub_live A0 A7).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row4) by (intros ->; rewrite Frow4 in Lq; discriminate Lq). rewrite (LEQ6 q NEq). exact (SUB6 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row4 :: [Z_to_bv 64 row3; Z_to_bv 64 row2; Z_to_bv 64 row1; Z_to_bv 64 row0; Z_to_bv 64 arr; Z_to_bv 64 sel])) => eq_trans (LEQ6 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL6 q (fun XX => Hq (or_intror XX)))) as LDEL7.
  assert (NE_sel_row4 : Z_to_bv 64 sel <> Z_to_bv 64 row4) by (intros EE; rewrite EE in Lsel_a6; rewrite Frow4x in Lsel_a6; discriminate Lsel_a6).
  assert (Lsel_a7 : live A7 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ6 _ NE_sel_row4); exact Lsel_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ sel row4 32 24 CK HW7 Lsel_a7 Lrow4_a7 NE_sel_row4 RRsel RRrow4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel_row4.
  assert (NE_arr_row4 : Z_to_bv 64 arr <> Z_to_bv 64 row4) by (intros EE; rewrite EE in Larr_a6; rewrite Frow4x in Larr_a6; discriminate Larr_a6).
  assert (Larr_a7 : live A7 (Z_to_bv 64 arr) = Some 40%Z) by (rewrite (LEQ6 _ NE_arr_row4); exact Larr_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ arr row4 40 24 CK HW7 Larr_a7 Lrow4_a7 NE_arr_row4 RRarr RRrow4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_row4.
  assert (NE_row0_row4 : Z_to_bv 64 row0 <> Z_to_bv 64 row4) by (intros EE; rewrite EE in Lrow0_a6; rewrite Frow4x in Lrow0_a6; discriminate Lrow0_a6).
  assert (Lrow0_a7 : live A7 (Z_to_bv 64 row0) = Some 24%Z) by (rewrite (LEQ6 _ NE_row0_row4); exact Lrow0_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ row0 row4 24 24 CK HW7 Lrow0_a7 Lrow4_a7 NE_row0_row4 RRrow0 RRrow4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row0_row4.
  assert (NE_row1_row4 : Z_to_bv 64 row1 <> Z_to_bv 64 row4) by (intros EE; rewrite EE in Lrow1_a6; rewrite Frow4x in Lrow1_a6; discriminate Lrow1_a6).
  assert (Lrow1_a7 : live A7 (Z_to_bv 64 row1) = Some 24%Z) by (rewrite (LEQ6 _ NE_row1_row4); exact Lrow1_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ row1 row4 24 24 CK HW7 Lrow1_a7 Lrow4_a7 NE_row1_row4 RRrow1 RRrow4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row1_row4.
  assert (NE_row2_row4 : Z_to_bv 64 row2 <> Z_to_bv 64 row4) by (intros EE; rewrite EE in Lrow2_a6; rewrite Frow4x in Lrow2_a6; discriminate Lrow2_a6).
  assert (Lrow2_a7 : live A7 (Z_to_bv 64 row2) = Some 24%Z) by (rewrite (LEQ6 _ NE_row2_row4); exact Lrow2_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ row2 row4 24 24 CK HW7 Lrow2_a7 Lrow4_a7 NE_row2_row4 RRrow2 RRrow4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row2_row4.
  assert (NE_row3_row4 : Z_to_bv 64 row3 <> Z_to_bv 64 row4) by (intros EE; rewrite EE in Lrow3_a6; rewrite Frow4x in Lrow3_a6; discriminate Lrow3_a6).
  assert (Lrow3_a7 : live A7 (Z_to_bv 64 row3) = Some 24%Z) by (rewrite (LEQ6 _ NE_row3_row4); exact Lrow3_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ row3 row4 24 24 CK HW7 Lrow3_a7 Lrow4_a7 NE_row3_row4 RRrow3 RRrow4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row3_row4.
  assert (PM7 : POSTM C A0 s m0 m7).
  { eapply POSTM_trans; [exact PM6|]. eapply POSTM_trans; [exact PMs6|]. apply (POSTM_sub C A0 A6 _ _ _ SUB6).
    apply (POSTM_mono C A6 (s + OFF6) s); [unfold OFF6; lia | exact PMc6]. }
  replace (kR - 6 - 1)%Z with (kR - 7)%Z in RM7 by lia. rewrite MG6 in RM7. replace (bR - 6 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 7 * 2 ^ 17)%Z in RM7 by lia.
  assert (KEPT6 : Forall (ex_region_kept E6 M6 m7) [(EVar 32, OFF6, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 40%Z); (EVar 135, 0%Z, 24%Z); (EVar 169, 0%Z, 24%Z); (EVar 203, 0%Z, 24%Z); (EVar 237, 0%Z, 24%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF6 1312 M6 m7 E6 (EVar 32) CK (proj1 PMc6) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 67) sel 32 CK HWs6 Lsel_a6 RRsel eq_refl (proj2 PMc6) Lsel_a6 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 101) arr 40 CK HWs6 Larr_a6 RRarr eq_refl (proj2 PMc6) Larr_a6 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 135) row0 24 CK HWs6 Lrow0_a6 RRrow0 eq_refl (proj2 PMc6) Lrow0_a6 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 169) row1 24 CK HWs6 Lrow1_a6 RRrow1 eq_refl (proj2 PMc6) Lrow1_a6 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 203) row2 24 CK HWs6 Lrow2_a6 RRrow2 eq_refl (proj2 PMc6) Lrow2_a6 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 237) row3 24 CK HWs6 Lrow3_a6 RRrow3 eq_refl (proj2 PMc6) Lrow3_a6 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E6 M6 m7 _ [] _ HKc6 KEPT6) as HKk6.
  match type of HKk6 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E6 m7 kk') in HKk6 end.
  pose proof (regs_ok_agree 239%nat E6 (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) _ _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa6.
  pose proof (exW_regs_call _ _ _ _ _ HRa6 (ex_regs_ok_junk vals6 r7 [row4; exW_canary SEGS 1410112 m7] 239%nat ltac:(vm_cast_no_check (eq_refl 239%nat))) CS6) as HRn7.
  clear HRa6.
  assert (HKa7 : know_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7 _) by (exact (know_ok_agree SEGS 239%nat E6 _ m7 _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk6)).
  rewrite (fr_denot_agree 239%nat E6 (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) _ fr (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r7 ex_r10 (EVar 271) HRn7 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres6)) as HRx7. clear HRn7. rename HRx7 into HRn7.
  clear HR HK Hlf Hms HKc6 HKk6 KEPT6 HC6 HWs6 PMs6 Q10_6 Q11_6 Q1_6 Q2_6 Q4_6 PM6 HW6 PMc6 CS6 SUB6 RM6 MG6 TOP6 LEQ6 Hnz6 Frow4x Lo6 OFF6 LDEL6 Lsel_a6 Larr_a6 Lrow0_a6 Lrow1_a6 Lrow2_a6 Lrow3_a6.
  subst M6. clear log6. clear E6. try clear Rc6. clear KN6.
  lazymatch type of HRn7 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn7 end.
  pose proof (exW_kn_blk SEGS C A7 m7 _ (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) (EVar 271) (EVar 32) row4 24 s 1312 65536 1347584 p16_segs CK HW7 Lrow4_a7 RRrow4 eq_refl eq_refl eq_refl RS ALrow4 ZERO6 WAProw4 IMGAProw4) as HKb7.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7 (EVar 67) (EVar 271) sel row4 0 32 0 24 eq_refl eq_refl RRsel RRrow4 AP_sel_row4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7 (EVar 101) (EVar 271) arr row4 0 40 0 24 eq_refl eq_refl RRarr RRrow4 AP_arr_row4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7 (EVar 135) (EVar 271) row0 row4 0 24 0 24 eq_refl eq_refl RRrow0 RRrow4 AP_row0_row4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7 (EVar 169) (EVar 271) row1 row4 0 24 0 24 eq_refl eq_refl RRrow1 RRrow4 AP_row1_row4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7 (EVar 203) (EVar 271) row2 row4 0 24 0 24 eq_refl eq_refl RRrow2 RRrow4 AP_row2_row4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7 (EVar 237) (EVar 271) row3 row4 0 24 0 24 eq_refl eq_refl RRrow3 RRrow4 AP_row3_row4) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7)))))))) as HKd7.
  pose proof (W_sok_win C A7 m7 _ (s - 1312) (Z.to_nat 1312) CK HW7 GLO1 GLO2) as SOK7.
  pose proof (exW_canary_ok SEGS 1410112 m7 (canary_any m7)) as CANOK7.
  pose (vals7 := vals6 ++ map (getr r7) ex_regs_list ++ map (Z_to_bv 64) [row4; exW_canary SEGS 1410112 m7]).
  pose proof (exW_kn_fixed SEGS C A7 m7 _ (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) (EVar 272) (EVar 32) (exW_canary SEGS 1410112 m7) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW7 eq_refl (proj1 CANOK7) (proj2 CANOK7) eq_refl eq_refl eq_refl SOK7 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf7.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb7 (proj2 (Forall_app _ _ _) (conj HKd7 (proj2 (Forall_app _ _ _) (conj HKf7 HKa7)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn7 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN7 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb7 HKd7 HKf7 HKa7 SOK7 CANOK7.
  repeat match goal with H : getr r7 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO6 ALrow4.
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E7 := EEx) in HR, Hlf, HK, Hms |- *; set (log7 := LLx) in Hms, Hlf; set (M7 := mem_denot E7 m7 log7) in Hms end.
  assert (WP7 : W C A7 M7 (with_vmmaps vm7 md) /\ POSTM C A0 s m7 M7).
  { subst M7. apply (exW_win_blks C A7 A0 m7 _ E7 log7 (EVar 32) s 1312 [(EVar 67, sel, 32%Z); (EVar 101, arr, 40%Z); (EVar 135, row0, 24%Z); (EVar 169, row1, 24%Z); (EVar 203, row2, 24%Z); (EVar 237, row3, 24%Z); (EVar 271, row4, 24%Z)] CK HW7 SUB7 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel (conj Lsel_a7 (conj Fsel F0sel))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a7 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRrow0 (conj Lrow0_a7 (conj Frow0 F0row0))))|]. constructor; [exact (conj eq_refl (conj RRrow1 (conj Lrow1_a7 (conj Frow1 F0row1))))|]. constructor; [exact (conj eq_refl (conj RRrow2 (conj Lrow2_a7 (conj Frow2 F0row2))))|]. constructor; [exact (conj eq_refl (conj RRrow3 (conj Lrow3_a7 (conj Frow3 F0row3))))|]. constructor; [exact (conj eq_refl (conj RRrow4 (conj Lrow4_a7 (conj Frow4 F0row4))))|]. constructor. }
  destruct WP7 as [HWs7 PMs7].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact Hms |].
  pose (BSF := [(32%nat, s); (67%nat, sel); (101%nat, arr); (135%nat, row0); (169%nat, row1); (203%nat, row2); (237%nat, row3); (271%nat, row4)]).
  exW_regfactB BSF HR ex_r10 G10.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel 0%Z 4%nat Csel_0.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel 4%Z 4%nat Csel_4.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel 8%Z 4%nat Csel_8.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel 12%Z 4%nat Csel_12.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel 16%Z 8%nat Csel_16.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel 24%Z 8%nat Csel_24.
  exW_cellB HK Hlf r0 BSF (EVar 101) arr 0%Z 8%nat Carr_0.
  exW_cellB HK Hlf r0 BSF (EVar 101) arr 8%Z 8%nat Carr_8.
  exW_cellB HK Hlf r0 BSF (EVar 101) arr 16%Z 8%nat Carr_16.
  exW_cellB HK Hlf r0 BSF (EVar 101) arr 24%Z 8%nat Carr_24.
  exW_cellB HK Hlf r0 BSF (EVar 101) arr 32%Z 8%nat Carr_32.
  exW_cellB HK Hlf r0 BSF (EVar 135) row0 0%Z 4%nat Crow0_0.
  exW_cellB HK Hlf r0 BSF (EVar 135) row0 4%Z 4%nat Crow0_4.
  exW_cellB HK Hlf r0 BSF (EVar 135) row0 8%Z 4%nat Crow0_8.
  exW_cellB HK Hlf r0 BSF (EVar 135) row0 12%Z 4%nat Crow0_12.
  exW_cellB HK Hlf r0 BSF (EVar 135) row0 16%Z 4%nat Crow0_16.
  exW_cellB HK Hlf r0 BSF (EVar 135) row0 20%Z 4%nat Crow0_20.
  exW_cellB HK Hlf r0 BSF (EVar 169) row1 0%Z 4%nat Crow1_0.
  exW_cellB HK Hlf r0 BSF (EVar 169) row1 4%Z 4%nat Crow1_4.
  exW_cellB HK Hlf r0 BSF (EVar 169) row1 8%Z 4%nat Crow1_8.
  exW_cellB HK Hlf r0 BSF (EVar 169) row1 12%Z 4%nat Crow1_12.
  exW_cellB HK Hlf r0 BSF (EVar 169) row1 16%Z 4%nat Crow1_16.
  exW_cellB HK Hlf r0 BSF (EVar 169) row1 20%Z 4%nat Crow1_20.
  exW_cellB HK Hlf r0 BSF (EVar 203) row2 0%Z 4%nat Crow2_0.
  exW_cellB HK Hlf r0 BSF (EVar 203) row2 4%Z 4%nat Crow2_4.
  exW_cellB HK Hlf r0 BSF (EVar 203) row2 8%Z 4%nat Crow2_8.
  exW_cellB HK Hlf r0 BSF (EVar 203) row2 12%Z 4%nat Crow2_12.
  exW_cellB HK Hlf r0 BSF (EVar 203) row2 16%Z 4%nat Crow2_16.
  exW_cellB HK Hlf r0 BSF (EVar 203) row2 20%Z 4%nat Crow2_20.
  exW_cellB HK Hlf r0 BSF (EVar 237) row3 0%Z 4%nat Crow3_0.
  exW_cellB HK Hlf r0 BSF (EVar 237) row3 4%Z 4%nat Crow3_4.
  exW_cellB HK Hlf r0 BSF (EVar 237) row3 8%Z 4%nat Crow3_8.
  exW_cellB HK Hlf r0 BSF (EVar 237) row3 12%Z 4%nat Crow3_12.
  exW_cellB HK Hlf r0 BSF (EVar 237) row3 16%Z 4%nat Crow3_16.
  exW_cellB HK Hlf r0 BSF (EVar 237) row3 20%Z 4%nat Crow3_20.
  exW_cellB HK Hlf r0 BSF (EVar 271) row4 0%Z 4%nat Crow4_0.
  exW_cellB HK Hlf r0 BSF (EVar 271) row4 4%Z 4%nat Crow4_4.
  exW_cellB HK Hlf r0 BSF (EVar 271) row4 8%Z 4%nat Crow4_8.
  exW_cellB HK Hlf r0 BSF (EVar 271) row4 12%Z 4%nat Crow4_12.
  exW_cellB HK Hlf r0 BSF (EVar 271) row4 16%Z 4%nat Crow4_16.
  exW_cellB HK Hlf r0 BSF (EVar 271) row4 20%Z 4%nat Crow4_20.
  refine (HC A7 M7 vm7 RcF sel arr row0 row1 row2 row3 row4 HWs7 _ SUB7 (POSTM_trans _ _ _ _ _ _ PM7 PMs7) RM7 LDEL7 G10
            Lsel_a7 Fsel F0sel RRsel Larr_a7 Farr F0arr RRarr Lrow0_a7 Frow0 F0row0 RRrow0 Lrow1_a7 Frow1 F0row1 RRrow1 Lrow2_a7 Frow2 F0row2 RRrow2 Lrow3_a7 Frow3 F0row3 RRrow3 Lrow4_a7 Frow4 F0row4 RRrow4
            NE_sel_arr NE_sel_row0 NE_arr_row0 NE_sel_row1 NE_arr_row1 NE_row0_row1 NE_sel_row2 NE_arr_row2 NE_row0_row2 NE_row1_row2 NE_sel_row3 NE_arr_row3 NE_row0_row3 NE_row1_row3 NE_row2_row3 NE_sel_row4 NE_arr_row4 NE_row0_row4 NE_row1_row4 NE_row2_row4 NE_row3_row4
            Csel_0 Csel_4 Csel_8 Csel_12 Csel_16 Csel_24 Carr_0 Carr_8 Carr_16 Carr_24 Carr_32 Crow0_0 Crow0_4 Crow0_8 Crow0_12 Crow0_16 Crow0_20 Crow1_0 Crow1_4 Crow1_8 Crow1_12 Crow1_16 Crow1_20 Crow2_0 Crow2_4 Crow2_8 Crow2_12 Crow2_16 Crow2_20 Crow3_0 Crow3_4 Crow3_8 Crow3_12 Crow3_16 Crow3_20 Crow4_0 Crow4_4 Crow4_8 Crow4_12 Crow4_16 Crow4_20).
  lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 RcF [(2%nat, EVar 32); (4%nat, ELit 1278416)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor; [symmetry; exact HTP | constructor]] | vm_compute; reflexivity] end.
Qed.

(* [comment removed for export] *)
Lemma selstr_chain4 : forall (fx : FPState) C A m md regs (s : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELSTR_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 1278416 ->
  getr regs 10 = Z_to_bv 64 94849 -> getr regs 11 = Z_to_bv 64 5 -> getr regs 12 = Z_to_bv 64 6 -> getr regs 13 = Z_to_bv 64 0 ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (7 <= kR)%Z -> (7 * 2 ^ 17 <= bR)%Z ->
  (forall A' m' vm' regs' (sel arr row0 row1 row2 row3 row4 : Z),
     W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> sub_live A A' -> POSTM C A s m m' ->
     aroom A' vm' (kR - 7) (bR - 7 * 2 ^ 17) ->
     (forall q : word, ~ In q [Z_to_bv 64 row4; Z_to_bv 64 row3; Z_to_bv 64 row2; Z_to_bv 64 row1; Z_to_bv 64 row0; Z_to_bv 64 arr; Z_to_bv 64 sel] -> live A' q = live A q) ->
     getr regs' 10 = Z_to_bv 64 sel ->
     live A' (Z_to_bv 64 sel) = Some 32%Z -> live A (Z_to_bv 64 sel) = None -> live (c_A0 C) (Z_to_bv 64 sel) = None -> (0 <= sel < 2 ^ 64)%Z ->
     live A' (Z_to_bv 64 arr) = Some 40%Z -> live A (Z_to_bv 64 arr) = None -> live (c_A0 C) (Z_to_bv 64 arr) = None -> (0 <= arr < 2 ^ 64)%Z ->
     live A' (Z_to_bv 64 row0) = Some 24%Z -> live A (Z_to_bv 64 row0) = None -> live (c_A0 C) (Z_to_bv 64 row0) = None -> (0 <= row0 < 2 ^ 64)%Z ->
     live A' (Z_to_bv 64 row1) = Some 24%Z -> live A (Z_to_bv 64 row1) = None -> live (c_A0 C) (Z_to_bv 64 row1) = None -> (0 <= row1 < 2 ^ 64)%Z ->
     live A' (Z_to_bv 64 row2) = Some 24%Z -> live A (Z_to_bv 64 row2) = None -> live (c_A0 C) (Z_to_bv 64 row2) = None -> (0 <= row2 < 2 ^ 64)%Z ->
     live A' (Z_to_bv 64 row3) = Some 24%Z -> live A (Z_to_bv 64 row3) = None -> live (c_A0 C) (Z_to_bv 64 row3) = None -> (0 <= row3 < 2 ^ 64)%Z ->
     live A' (Z_to_bv 64 row4) = Some 24%Z -> live A (Z_to_bv 64 row4) = None -> live (c_A0 C) (Z_to_bv 64 row4) = None -> (0 <= row4 < 2 ^ 64)%Z ->
     Z_to_bv 64 sel <> Z_to_bv 64 arr ->
     Z_to_bv 64 sel <> Z_to_bv 64 row0 ->
     Z_to_bv 64 arr <> Z_to_bv 64 row0 ->
     Z_to_bv 64 sel <> Z_to_bv 64 row1 ->
     Z_to_bv 64 arr <> Z_to_bv 64 row1 ->
     Z_to_bv 64 row0 <> Z_to_bv 64 row1 ->
     Z_to_bv 64 sel <> Z_to_bv 64 row2 ->
     Z_to_bv 64 arr <> Z_to_bv 64 row2 ->
     Z_to_bv 64 row0 <> Z_to_bv 64 row2 ->
     Z_to_bv 64 row1 <> Z_to_bv 64 row2 ->
     Z_to_bv 64 sel <> Z_to_bv 64 row3 ->
     Z_to_bv 64 arr <> Z_to_bv 64 row3 ->
     Z_to_bv 64 row0 <> Z_to_bv 64 row3 ->
     Z_to_bv 64 row1 <> Z_to_bv 64 row3 ->
     Z_to_bv 64 row2 <> Z_to_bv 64 row3 ->
     Z_to_bv 64 sel <> Z_to_bv 64 row4 ->
     Z_to_bv 64 arr <> Z_to_bv 64 row4 ->
     Z_to_bv 64 row0 <> Z_to_bv 64 row4 ->
     Z_to_bv 64 row1 <> Z_to_bv 64 row4 ->
     Z_to_bv 64 row2 <> Z_to_bv 64 row4 ->
     Z_to_bv 64 row3 <> Z_to_bv 64 row4 ->
     rdn SEGS m' (Z_to_bv 64 (sel + 0)) 4 = Some (Z_to_le_bytes 4 5) ->
     rdn SEGS m' (Z_to_bv 64 (sel + 4)) 4 = Some (Z_to_le_bytes 4 6) ->
     rdn SEGS m' (Z_to_bv 64 (sel + 8)) 4 = Some (Z_to_le_bytes 4 3) ->
     rdn SEGS m' (Z_to_bv 64 (sel + 12)) 4 = Some (Z_to_le_bytes 4 2) ->
     rdn SEGS m' (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 arr) ->
     rdn SEGS m' (Z_to_bv 64 (sel + 24)) 8 = Some (Z_to_le_bytes 8 0) ->
     rdn SEGS m' (Z_to_bv 64 (arr + 0)) 8 = Some (Z_to_le_bytes 8 row0) ->
     rdn SEGS m' (Z_to_bv 64 (arr + 8)) 8 = Some (Z_to_le_bytes 8 row1) ->
     rdn SEGS m' (Z_to_bv 64 (arr + 16)) 8 = Some (Z_to_le_bytes 8 row2) ->
     rdn SEGS m' (Z_to_bv 64 (arr + 24)) 8 = Some (Z_to_le_bytes 8 row3) ->
     rdn SEGS m' (Z_to_bv 64 (arr + 32)) 8 = Some (Z_to_le_bytes 8 row4) ->
     rdn SEGS m' (Z_to_bv 64 (row0 + 0)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row0 + 4)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row0 + 8)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row0 + 12)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row0 + 16)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row0 + 20)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row1 + 0)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row1 + 4)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row1 + 8)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row1 + 12)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row1 + 16)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row1 + 20)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row2 + 0)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row2 + 4)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row2 + 8)) 4 = Some (Z_to_le_bytes 4 2) ->
     rdn SEGS m' (Z_to_bv 64 (row2 + 12)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row2 + 16)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row2 + 20)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row3 + 0)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row3 + 4)) 4 = Some (Z_to_le_bytes 4 2) ->
     rdn SEGS m' (Z_to_bv 64 (row3 + 8)) 4 = Some (Z_to_le_bytes 4 2) ->
     rdn SEGS m' (Z_to_bv 64 (row3 + 12)) 4 = Some (Z_to_le_bytes 4 2) ->
     rdn SEGS m' (Z_to_bv 64 (row3 + 16)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row3 + 20)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (row4 + 0)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row4 + 4)) 4 = Some (Z_to_le_bytes 4 2) ->
     rdn SEGS m' (Z_to_bv 64 (row4 + 8)) 4 = Some (Z_to_le_bytes 4 2) ->
     rdn SEGS m' (Z_to_bv 64 (row4 + 12)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row4 + 16)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (row4 + 20)) 4 = Some (Z_to_le_bytes 4 1) ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 678036) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 s ret S CK HW0 H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 H13 kR bR RM0 HkR HbR HC.
  unfold SELSTR_WIN in *.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  assert (HTP : ex_keep (getr r0 ex_r4 = Z_to_bv 64 1278416)) by exact H4.
  destruct fx as [fr cs]. pose proof I as FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  replace kR with (kR - 0)%Z in RM0 by lia. replace bR with (bR - 0 * 2 ^ 17)%Z in RM0 by lia.
  pose (valsI := @nil word).
  pose proof (fun (q : word) (_ : ~ In q []) => eq_refl (live A0 q)) as LDEL0.
  assert (GLO1 : (c_top C - LSTK <= s - 1312)%Z) by lia.
  assert (GLO2 : (s - 1312 + Z.of_nat (Z.to_nat 1312) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (1312 <= s)%Z) by lia.
  pose proof (W_sok_win C A0 m0 _ (s - 1312) (Z.to_nat 1312) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 1410112 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0]) (EVar 34) (EVar 32) (exW_canary SEGS 1410112 m0) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0]) m0 [KRange (EVar 32) 1422624 (2 ^ 63); KAlign (EVar 32) 16]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 HKf0)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); exW_canary SEGS 1410112 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 1312 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
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
  intros A1 m1 vm1 r1 res0 HW1 Hres0 CSx0 Hnz0 Fselx Lo0 F0sel LEQ0 ZERO0 ALsel TOP0 PMc0 RM1.
  pose proof CSx0 as CS0. clear CSx0.
  rewrite with_vmmaps_twice in HW1 |- *.
  assert (Eres0 : res0 = Z_to_bv 64 (u res0)) by (symmetry; apply zbv_self).
  pose proof (u64_range res0) as RRsel. set (sel := u res0) in *. clearbody sel. rewrite Eres0 in Hres0, Fselx, Lo0, F0sel, LEQ0, ZERO0. clear Eres0.
  change (1 * 32)%Z with 32%Z in *.
  pose proof (exW_blk_img_apart_h2 C A1 m1 _ sel 32 CK HW1 Lo0 RRsel eq_refl eq_refl) as IMGAPsel. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPsel.
  pose proof (exW_win_blk_apart_h C A1 m1 _ s 1312 sel 32 CK HW1 Lo0 eq_refl RRsel GLO1) as WAPsel.
  assert (Fsel : live A0 (Z_to_bv 64 sel) = None).
  { destruct (live A0 (Z_to_bv 64 sel)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB0 _ _ EE) as XX. first [discriminate Fselx | (rewrite Fselx in XX; discriminate XX)]. }
  pose proof Lo0 as Lsel_a1.
  assert (SUB1 : sub_live A0 A1).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 sel) by (intros ->; rewrite Fsel in Lq; discriminate Lq). rewrite (LEQ0 q NEq). exact (SUB0 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 sel :: [])) => eq_trans (LEQ0 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL0 q (fun XX => Hq (or_intror XX)))) as LDEL1.
  assert (PM1 : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|]. apply (POSTM_sub C A0 A0 _ _ _ SUB0).
    apply (POSTM_mono C A0 (s + OFF0) s); [unfold OFF0; lia | exact PMc0]. }
  replace (kR - 0 - 1)%Z with (kR - 1)%Z in RM1 by lia. rewrite MG0 in RM1. replace (bR - 0 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 1 * 2 ^ 17)%Z in RM1 by lia.
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, OFF0, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF0 1312 M0 m1 E0 (EVar 32) CK (proj1 PMc0) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E0 m1 kk') in HKk0 end.
  pose proof (regs_ok_agree 35%nat E0 (ex_envL vals0 r1 [sel; exW_canary SEGS 1410112 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [sel; exW_canary SEGS 1410112 m1] 35%nat ltac:(vm_cast_no_check (eq_refl 35%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [sel; exW_canary SEGS 1410112 m1]) m1 _) by (exact (know_ok_agree SEGS 35%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  rewrite (fr_denot_agree 35%nat E0 (ex_envL vals0 r1 [sel; exW_canary SEGS 1410112 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r1 ex_r10 (EVar 67) HRn1 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres0)) as HRx1. clear HRn1. rename HRx1 into HRn1.
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q11_0 Q1_0 Q2_0 Q4_0 PM0 HW0 PMc0 CS0 SUB0 RM0 MG0 TOP0 LEQ0 Hnz0 Fselx Lo0 OFF0 LDEL0.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  pose proof (exW_kn_blk SEGS C A1 m1 _ (ex_envL vals0 r1 [sel; exW_canary SEGS 1410112 m1]) (EVar 67) (EVar 32) sel 32 s 1312 65536 1347584 p16_segs CK HW1 Lsel_a1 RRsel eq_refl eq_refl eq_refl RS ALsel ZERO0 WAPsel IMGAPsel) as HKb1.
  pose proof (W_sok_win C A1 m1 _ (s - 1312) (Z.to_nat 1312) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 1410112 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [sel; exW_canary SEGS 1410112 m1]).
  pose proof (exW_kn_fixed SEGS C A1 m1 _ (ex_envL vals0 r1 [sel; exW_canary SEGS 1410112 m1]) (EVar 68) (EVar 32) (exW_canary SEGS 1410112 m1) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb1 (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb1 HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO0 ALsel.
  exb_exit ST Rc1 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A1 M1 (with_vmmaps vm1 md) /\ POSTM C A0 s m1 M1).
  { subst M1. apply (exW_win_blks C A1 A0 m1 _ E1 log1 (EVar 32) s 1312 [(EVar 67, sel, 32%Z)] CK HW1 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel (conj Lsel_a1 (conj Fsel F0sel))))|]. constructor. }
  destruct WP1 as [HWs1 PMs1].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log1 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC1 : carry log1 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc1 : know_ok SEGS E1 M1 kn1) by (apply (carry_after SEGS E1 m1 log1 kn0 [] kn1 scs hs HC1 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose (BS1 := [(32%nat, s); (67%nat, sel)]).
  exW_regfactB BS1 HR ex_r10 Q10_1. exW_regfactB BS1 HR ex_r11 Q11_1. exW_regfactB BS1 HR ex_r1 Q1_1. exW_regfactB BS1 HR ex_r2 Q2_1. exW_regfactB BS1 HR ex_r4 Q4_1.
  clear BS1.
  lazymatch type of Q2_1 with _ = Z_to_bv 64 (s + ?off) => pose (OFF1 := off) end.
  pose proof (alloc_margin_small (5 * 8) ltac:(exW_cmp)) as MG1.
  lazymatch type of Q1_1 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_1 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A1 M1 _ Rc1 5 8 (kR - 1) (bR - 1 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs1 Q10_1 Q11_1 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM1) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_1
             ltac:(red; apply bv_eq; reflexivity) Q4_1 Q2_1 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A2 m2 vm2 r2 res1 HW2 Hres1 CSx1 Hnz1 Farrx Lo1 F0arr LEQ1 ZERO1 ALarr TOP1 PMc1 RM2.
  pose proof CSx1 as CS1. clear CSx1.
  rewrite with_vmmaps_twice in HW2 |- *.
  assert (Eres1 : res1 = Z_to_bv 64 (u res1)) by (symmetry; apply zbv_self).
  pose proof (u64_range res1) as RRarr. set (arr := u res1) in *. clearbody arr. rewrite Eres1 in Hres1, Farrx, Lo1, F0arr, LEQ1, ZERO1. clear Eres1.
  change (5 * 8)%Z with 40%Z in *.
  pose proof (exW_blk_img_apart_h2 C A2 m2 _ arr 40 CK HW2 Lo1 RRarr eq_refl eq_refl) as IMGAParr. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAParr.
  pose proof (exW_win_blk_apart_h C A2 m2 _ s 1312 arr 40 CK HW2 Lo1 eq_refl RRarr GLO1) as WAParr.
  assert (Farr : live A0 (Z_to_bv 64 arr) = None).
  { destruct (live A0 (Z_to_bv 64 arr)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB1 _ _ EE) as XX. first [discriminate Farrx | (rewrite Farrx in XX; discriminate XX)]. }
  pose proof Lo1 as Larr_a2.
  assert (SUB2 : sub_live A0 A2).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 arr) by (intros ->; rewrite Farr in Lq; discriminate Lq). rewrite (LEQ1 q NEq). exact (SUB1 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 arr :: [Z_to_bv 64 sel])) => eq_trans (LEQ1 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL1 q (fun XX => Hq (or_intror XX)))) as LDEL2.
  assert (NE_sel_arr : Z_to_bv 64 sel <> Z_to_bv 64 arr) by (intros EE; rewrite EE in Lsel_a1; rewrite Farrx in Lsel_a1; discriminate Lsel_a1).
  assert (Lsel_a2 : live A2 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ1 _ NE_sel_arr); exact Lsel_a1).
  pose proof (exW_blk_apart_h C A2 m2 _ sel arr 32 40 CK HW2 Lsel_a2 Larr_a2 NE_sel_arr RRsel RRarr ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel_arr.
  assert (PM2 : POSTM C A0 s m0 m2).
  { eapply POSTM_trans; [exact PM1|]. eapply POSTM_trans; [exact PMs1|]. apply (POSTM_sub C A0 A1 _ _ _ SUB1).
    apply (POSTM_mono C A1 (s + OFF1) s); [unfold OFF1; lia | exact PMc1]. }
  replace (kR - 1 - 1)%Z with (kR - 2)%Z in RM2 by lia. rewrite MG1 in RM2. replace (bR - 1 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 2 * 2 ^ 17)%Z in RM2 by lia.
  assert (KEPT1 : Forall (ex_region_kept E1 M1 m2) [(EVar 32, OFF1, 0%Z); (EVar 67, 0%Z, 32%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF1 1312 M1 m2 E1 (EVar 32) CK (proj1 PMc1) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A1 A1 M1 _ M1 m2 E1 (EVar 67) sel 32 CK HWs1 Lsel_a1 RRsel eq_refl (proj2 PMc1) Lsel_a1 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E1 M1 m2 _ [] _ HKc1 KEPT1) as HKk1.
  match type of HKk1 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E1 m2 kk') in HKk1 end.
  pose proof (regs_ok_agree 69%nat E1 (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) _ _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa1.
  pose proof (exW_regs_call _ _ _ _ _ HRa1 (ex_regs_ok_junk vals1 r2 [arr; exW_canary SEGS 1410112 m2] 69%nat ltac:(vm_cast_no_check (eq_refl 69%nat))) CS1) as HRn2.
  clear HRa1.
  assert (HKa2 : know_ok SEGS (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) m2 _) by (exact (know_ok_agree SEGS 69%nat E1 _ m2 _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk1)).
  rewrite (fr_denot_agree 69%nat E1 (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) _ fr (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r2 ex_r10 (EVar 101) HRn2 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres1)) as HRx2. clear HRn2. rename HRx2 into HRn2.
  clear HR HK Hlf Hms HKc1 HKk1 KEPT1 HC1 HWs1 PMs1 Q10_1 Q11_1 Q1_1 Q2_1 Q4_1 PM1 HW1 PMc1 CS1 SUB1 RM1 MG1 TOP1 LEQ1 Hnz1 Farrx Lo1 OFF1 LDEL1 Lsel_a1.
  subst M1. clear log1. clear E1. try clear Rc1. clear KN1.
  lazymatch type of HRn2 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn2 end.
  pose proof (exW_kn_blk SEGS C A2 m2 _ (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) (EVar 101) (EVar 32) arr 40 s 1312 65536 1347584 p16_segs CK HW2 Larr_a2 RRarr eq_refl eq_refl eq_refl RS ALarr ZERO1 WAParr IMGAParr) as HKb2.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) m2) _ _ (ex_kdisj_apart SEGS (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) m2 (EVar 67) (EVar 101) sel arr 0 32 0 40 eq_refl eq_refl RRsel RRarr AP_sel_arr) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) m2))) as HKd2.
  pose proof (W_sok_win C A2 m2 _ (s - 1312) (Z.to_nat 1312) CK HW2 GLO1 GLO2) as SOK2.
  pose proof (exW_canary_ok SEGS 1410112 m2 (canary_any m2)) as CANOK2.
  pose (vals2 := vals1 ++ map (getr r2) ex_regs_list ++ map (Z_to_bv 64) [arr; exW_canary SEGS 1410112 m2]).
  pose proof (exW_kn_fixed SEGS C A2 m2 _ (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) (EVar 102) (EVar 32) (exW_canary SEGS 1410112 m2) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW2 eq_refl (proj1 CANOK2) (proj2 CANOK2) eq_refl eq_refl eq_refl SOK2 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf2.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb2 (proj2 (Forall_app _ _ _) (conj HKd2 (proj2 (Forall_app _ _ _) (conj HKf2 HKa2)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn2 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN2 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb2 HKd2 HKf2 HKa2 SOK2 CANOK2.
  repeat match goal with H : getr r2 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO1 ALarr.
  exb_exit ST Rc2 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E2 := EEx) in HR, Hlf, HK, Hms |- *; set (log2 := LLx) in Hms, Hlf; set (M2 := mem_denot E2 m2 log2) in Hms end.
  assert (WP2 : W C A2 M2 (with_vmmaps vm2 md) /\ POSTM C A0 s m2 M2).
  { subst M2. apply (exW_win_blks C A2 A0 m2 _ E2 log2 (EVar 32) s 1312 [(EVar 67, sel, 32%Z); (EVar 101, arr, 40%Z)] CK HW2 SUB2 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel (conj Lsel_a2 (conj Fsel F0sel))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a2 (conj Farr F0arr))))|]. constructor. }
  destruct WP2 as [HWs2 PMs2].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log2 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC2 : carry log2 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc2 : know_ok SEGS E2 M2 kn1) by (apply (carry_after SEGS E2 m2 log2 kn0 [] kn1 scs hs HC2 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact Hms |].
  pose (BS2 := [(32%nat, s); (67%nat, sel); (101%nat, arr)]).
  exW_regfactB BS2 HR ex_r10 Q10_2. exW_regfactB BS2 HR ex_r11 Q11_2. exW_regfactB BS2 HR ex_r1 Q1_2. exW_regfactB BS2 HR ex_r2 Q2_2. exW_regfactB BS2 HR ex_r4 Q4_2.
  clear BS2.
  lazymatch type of Q2_2 with _ = Z_to_bv 64 (s + ?off) => pose (OFF2 := off) end.
  pose proof (alloc_margin_small (6 * 4) ltac:(exW_cmp)) as MG2.
  lazymatch type of Q1_2 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_2 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A2 M2 _ Rc2 6 4 (kR - 2) (bR - 2 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs2 Q10_2 Q11_2 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM2) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_2
             ltac:(red; apply bv_eq; reflexivity) Q4_2 Q2_2 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A3 m3 vm3 r3 res2 HW3 Hres2 CSx2 Hnz2 Frow0x Lo2 F0row0 LEQ2 ZERO2 ALrow0 TOP2 PMc2 RM3.
  pose proof CSx2 as CS2. clear CSx2.
  rewrite with_vmmaps_twice in HW3 |- *.
  assert (Eres2 : res2 = Z_to_bv 64 (u res2)) by (symmetry; apply zbv_self).
  pose proof (u64_range res2) as RRrow0. set (row0 := u res2) in *. clearbody row0. rewrite Eres2 in Hres2, Frow0x, Lo2, F0row0, LEQ2, ZERO2. clear Eres2.
  change (6 * 4)%Z with 24%Z in *.
  pose proof (exW_blk_img_apart_h2 C A3 m3 _ row0 24 CK HW3 Lo2 RRrow0 eq_refl eq_refl) as IMGAProw0. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAProw0.
  pose proof (exW_win_blk_apart_h C A3 m3 _ s 1312 row0 24 CK HW3 Lo2 eq_refl RRrow0 GLO1) as WAProw0.
  assert (Frow0 : live A0 (Z_to_bv 64 row0) = None).
  { destruct (live A0 (Z_to_bv 64 row0)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB2 _ _ EE) as XX. first [discriminate Frow0x | (rewrite Frow0x in XX; discriminate XX)]. }
  pose proof Lo2 as Lrow0_a3.
  assert (SUB3 : sub_live A0 A3).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row0) by (intros ->; rewrite Frow0 in Lq; discriminate Lq). rewrite (LEQ2 q NEq). exact (SUB2 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row0 :: [Z_to_bv 64 arr; Z_to_bv 64 sel])) => eq_trans (LEQ2 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL2 q (fun XX => Hq (or_intror XX)))) as LDEL3.
  assert (NE_sel_row0 : Z_to_bv 64 sel <> Z_to_bv 64 row0) by (intros EE; rewrite EE in Lsel_a2; rewrite Frow0x in Lsel_a2; discriminate Lsel_a2).
  assert (Lsel_a3 : live A3 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ2 _ NE_sel_row0); exact Lsel_a2).
  pose proof (exW_blk_apart_h C A3 m3 _ sel row0 32 24 CK HW3 Lsel_a3 Lrow0_a3 NE_sel_row0 RRsel RRrow0 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel_row0.
  assert (NE_arr_row0 : Z_to_bv 64 arr <> Z_to_bv 64 row0) by (intros EE; rewrite EE in Larr_a2; rewrite Frow0x in Larr_a2; discriminate Larr_a2).
  assert (Larr_a3 : live A3 (Z_to_bv 64 arr) = Some 40%Z) by (rewrite (LEQ2 _ NE_arr_row0); exact Larr_a2).
  pose proof (exW_blk_apart_h C A3 m3 _ arr row0 40 24 CK HW3 Larr_a3 Lrow0_a3 NE_arr_row0 RRarr RRrow0 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_row0.
  assert (PM3 : POSTM C A0 s m0 m3).
  { eapply POSTM_trans; [exact PM2|]. eapply POSTM_trans; [exact PMs2|]. apply (POSTM_sub C A0 A2 _ _ _ SUB2).
    apply (POSTM_mono C A2 (s + OFF2) s); [unfold OFF2; lia | exact PMc2]. }
  replace (kR - 2 - 1)%Z with (kR - 3)%Z in RM3 by lia. rewrite MG2 in RM3. replace (bR - 2 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 3 * 2 ^ 17)%Z in RM3 by lia.
  assert (KEPT2 : Forall (ex_region_kept E2 M2 m3) [(EVar 32, OFF2, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 40%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF2 1312 M2 m3 E2 (EVar 32) CK (proj1 PMc2) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A2 A2 M2 _ M2 m3 E2 (EVar 67) sel 32 CK HWs2 Lsel_a2 RRsel eq_refl (proj2 PMc2) Lsel_a2 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A2 A2 M2 _ M2 m3 E2 (EVar 101) arr 40 CK HWs2 Larr_a2 RRarr eq_refl (proj2 PMc2) Larr_a2 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E2 M2 m3 _ [] _ HKc2 KEPT2) as HKk2.
  match type of HKk2 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E2 m3 kk') in HKk2 end.
  pose proof (regs_ok_agree 103%nat E2 (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) _ _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa2.
  pose proof (exW_regs_call _ _ _ _ _ HRa2 (ex_regs_ok_junk vals2 r3 [row0; exW_canary SEGS 1410112 m3] 103%nat ltac:(vm_cast_no_check (eq_refl 103%nat))) CS2) as HRn3.
  clear HRa2.
  assert (HKa3 : know_ok SEGS (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) m3 _) by (exact (know_ok_agree SEGS 103%nat E2 _ m3 _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk2)).
  rewrite (fr_denot_agree 103%nat E2 (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) _ fr (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r3 ex_r10 (EVar 135) HRn3 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres2)) as HRx3. clear HRn3. rename HRx3 into HRn3.
  clear HR HK Hlf Hms HKc2 HKk2 KEPT2 HC2 HWs2 PMs2 Q10_2 Q11_2 Q1_2 Q2_2 Q4_2 PM2 HW2 PMc2 CS2 SUB2 RM2 MG2 TOP2 LEQ2 Hnz2 Frow0x Lo2 OFF2 LDEL2 Lsel_a2 Larr_a2.
  subst M2. clear log2. clear E2. try clear Rc2. clear KN2.
  lazymatch type of HRn3 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn3 end.
  pose proof (exW_kn_blk SEGS C A3 m3 _ (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) (EVar 135) (EVar 32) row0 24 s 1312 65536 1347584 p16_segs CK HW3 Lrow0_a3 RRrow0 eq_refl eq_refl eq_refl RS ALrow0 ZERO2 WAProw0 IMGAProw0) as HKb3.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) m3) _ _ (ex_kdisj_apart SEGS (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) m3 (EVar 67) (EVar 135) sel row0 0 32 0 24 eq_refl eq_refl RRsel RRrow0 AP_sel_row0) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) m3) _ _ (ex_kdisj_apart SEGS (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) m3 (EVar 101) (EVar 135) arr row0 0 40 0 24 eq_refl eq_refl RRarr RRrow0 AP_arr_row0) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) m3)))) as HKd3.
  pose proof (W_sok_win C A3 m3 _ (s - 1312) (Z.to_nat 1312) CK HW3 GLO1 GLO2) as SOK3.
  pose proof (exW_canary_ok SEGS 1410112 m3 (canary_any m3)) as CANOK3.
  pose (vals3 := vals2 ++ map (getr r3) ex_regs_list ++ map (Z_to_bv 64) [row0; exW_canary SEGS 1410112 m3]).
  pose proof (exW_kn_fixed SEGS C A3 m3 _ (ex_envL vals2 r3 [row0; exW_canary SEGS 1410112 m3]) (EVar 136) (EVar 32) (exW_canary SEGS 1410112 m3) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW3 eq_refl (proj1 CANOK3) (proj2 CANOK3) eq_refl eq_refl eq_refl SOK3 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf3.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb3 (proj2 (Forall_app _ _ _) (conj HKd3 (proj2 (Forall_app _ _ _) (conj HKf3 HKa3)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn3 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN3 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb3 HKd3 HKf3 HKa3 SOK3 CANOK3.
  repeat match goal with H : getr r3 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO2 ALrow0.
  exb_exit ST Rc3 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E3 := EEx) in HR, Hlf, HK, Hms |- *; set (log3 := LLx) in Hms, Hlf; set (M3 := mem_denot E3 m3 log3) in Hms end.
  assert (WP3 : W C A3 M3 (with_vmmaps vm3 md) /\ POSTM C A0 s m3 M3).
  { subst M3. apply (exW_win_blks C A3 A0 m3 _ E3 log3 (EVar 32) s 1312 [(EVar 67, sel, 32%Z); (EVar 101, arr, 40%Z); (EVar 135, row0, 24%Z)] CK HW3 SUB3 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel (conj Lsel_a3 (conj Fsel F0sel))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a3 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRrow0 (conj Lrow0_a3 (conj Frow0 F0row0))))|]. constructor. }
  destruct WP3 as [HWs3 PMs3].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log3 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC3 : carry log3 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc3 : know_ok SEGS E3 M3 kn1) by (apply (carry_after SEGS E3 m3 log3 kn0 [] kn1 scs hs HC3 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact Hms |].
  pose (BS3 := [(32%nat, s); (67%nat, sel); (101%nat, arr); (135%nat, row0)]).
  exW_regfactB BS3 HR ex_r10 Q10_3. exW_regfactB BS3 HR ex_r11 Q11_3. exW_regfactB BS3 HR ex_r1 Q1_3. exW_regfactB BS3 HR ex_r2 Q2_3. exW_regfactB BS3 HR ex_r4 Q4_3.
  clear BS3.
  lazymatch type of Q2_3 with _ = Z_to_bv 64 (s + ?off) => pose (OFF3 := off) end.
  pose proof (alloc_margin_small (6 * 4) ltac:(exW_cmp)) as MG3.
  lazymatch type of Q1_3 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_3 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A3 M3 _ Rc3 6 4 (kR - 3) (bR - 3 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs3 Q10_3 Q11_3 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM3) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_3
             ltac:(red; apply bv_eq; reflexivity) Q4_3 Q2_3 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A4 m4 vm4 r4 res3 HW4 Hres3 CSx3 Hnz3 Frow1x Lo3 F0row1 LEQ3 ZERO3 ALrow1 TOP3 PMc3 RM4.
  pose proof CSx3 as CS3. clear CSx3.
  rewrite with_vmmaps_twice in HW4 |- *.
  assert (Eres3 : res3 = Z_to_bv 64 (u res3)) by (symmetry; apply zbv_self).
  pose proof (u64_range res3) as RRrow1. set (row1 := u res3) in *. clearbody row1. rewrite Eres3 in Hres3, Frow1x, Lo3, F0row1, LEQ3, ZERO3. clear Eres3.
  change (6 * 4)%Z with 24%Z in *.
  pose proof (exW_blk_img_apart_h2 C A4 m4 _ row1 24 CK HW4 Lo3 RRrow1 eq_refl eq_refl) as IMGAProw1. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAProw1.
  pose proof (exW_win_blk_apart_h C A4 m4 _ s 1312 row1 24 CK HW4 Lo3 eq_refl RRrow1 GLO1) as WAProw1.
  assert (Frow1 : live A0 (Z_to_bv 64 row1) = None).
  { destruct (live A0 (Z_to_bv 64 row1)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB3 _ _ EE) as XX. first [discriminate Frow1x | (rewrite Frow1x in XX; discriminate XX)]. }
  pose proof Lo3 as Lrow1_a4.
  assert (SUB4 : sub_live A0 A4).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row1) by (intros ->; rewrite Frow1 in Lq; discriminate Lq). rewrite (LEQ3 q NEq). exact (SUB3 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row1 :: [Z_to_bv 64 row0; Z_to_bv 64 arr; Z_to_bv 64 sel])) => eq_trans (LEQ3 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL3 q (fun XX => Hq (or_intror XX)))) as LDEL4.
  assert (NE_sel_row1 : Z_to_bv 64 sel <> Z_to_bv 64 row1) by (intros EE; rewrite EE in Lsel_a3; rewrite Frow1x in Lsel_a3; discriminate Lsel_a3).
  assert (Lsel_a4 : live A4 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ3 _ NE_sel_row1); exact Lsel_a3).
  pose proof (exW_blk_apart_h C A4 m4 _ sel row1 32 24 CK HW4 Lsel_a4 Lrow1_a4 NE_sel_row1 RRsel RRrow1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel_row1.
  assert (NE_arr_row1 : Z_to_bv 64 arr <> Z_to_bv 64 row1) by (intros EE; rewrite EE in Larr_a3; rewrite Frow1x in Larr_a3; discriminate Larr_a3).
  assert (Larr_a4 : live A4 (Z_to_bv 64 arr) = Some 40%Z) by (rewrite (LEQ3 _ NE_arr_row1); exact Larr_a3).
  pose proof (exW_blk_apart_h C A4 m4 _ arr row1 40 24 CK HW4 Larr_a4 Lrow1_a4 NE_arr_row1 RRarr RRrow1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_row1.
  assert (NE_row0_row1 : Z_to_bv 64 row0 <> Z_to_bv 64 row1) by (intros EE; rewrite EE in Lrow0_a3; rewrite Frow1x in Lrow0_a3; discriminate Lrow0_a3).
  assert (Lrow0_a4 : live A4 (Z_to_bv 64 row0) = Some 24%Z) by (rewrite (LEQ3 _ NE_row0_row1); exact Lrow0_a3).
  pose proof (exW_blk_apart_h C A4 m4 _ row0 row1 24 24 CK HW4 Lrow0_a4 Lrow1_a4 NE_row0_row1 RRrow0 RRrow1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row0_row1.
  assert (PM4 : POSTM C A0 s m0 m4).
  { eapply POSTM_trans; [exact PM3|]. eapply POSTM_trans; [exact PMs3|]. apply (POSTM_sub C A0 A3 _ _ _ SUB3).
    apply (POSTM_mono C A3 (s + OFF3) s); [unfold OFF3; lia | exact PMc3]. }
  replace (kR - 3 - 1)%Z with (kR - 4)%Z in RM4 by lia. rewrite MG3 in RM4. replace (bR - 3 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 4 * 2 ^ 17)%Z in RM4 by lia.
  assert (KEPT3 : Forall (ex_region_kept E3 M3 m4) [(EVar 32, OFF3, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 40%Z); (EVar 135, 0%Z, 24%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF3 1312 M3 m4 E3 (EVar 32) CK (proj1 PMc3) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A3 A3 M3 _ M3 m4 E3 (EVar 67) sel 32 CK HWs3 Lsel_a3 RRsel eq_refl (proj2 PMc3) Lsel_a3 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A3 A3 M3 _ M3 m4 E3 (EVar 101) arr 40 CK HWs3 Larr_a3 RRarr eq_refl (proj2 PMc3) Larr_a3 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A3 A3 M3 _ M3 m4 E3 (EVar 135) row0 24 CK HWs3 Lrow0_a3 RRrow0 eq_refl (proj2 PMc3) Lrow0_a3 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E3 M3 m4 _ [] _ HKc3 KEPT3) as HKk3.
  match type of HKk3 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E3 m4 kk') in HKk3 end.
  pose proof (regs_ok_agree 137%nat E3 (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) _ _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa3.
  pose proof (exW_regs_call _ _ _ _ _ HRa3 (ex_regs_ok_junk vals3 r4 [row1; exW_canary SEGS 1410112 m4] 137%nat ltac:(vm_cast_no_check (eq_refl 137%nat))) CS3) as HRn4.
  clear HRa3.
  assert (HKa4 : know_ok SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4 _) by (exact (know_ok_agree SEGS 137%nat E3 _ m4 _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk3)).
  rewrite (fr_denot_agree 137%nat E3 (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) _ fr (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r4 ex_r10 (EVar 169) HRn4 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres3)) as HRx4. clear HRn4. rename HRx4 into HRn4.
  clear HR HK Hlf Hms HKc3 HKk3 KEPT3 HC3 HWs3 PMs3 Q10_3 Q11_3 Q1_3 Q2_3 Q4_3 PM3 HW3 PMc3 CS3 SUB3 RM3 MG3 TOP3 LEQ3 Hnz3 Frow1x Lo3 OFF3 LDEL3 Lsel_a3 Larr_a3 Lrow0_a3.
  subst M3. clear log3. clear E3. try clear Rc3. clear KN3.
  lazymatch type of HRn4 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn4 end.
  pose proof (exW_kn_blk SEGS C A4 m4 _ (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) (EVar 169) (EVar 32) row1 24 s 1312 65536 1347584 p16_segs CK HW4 Lrow1_a4 RRrow1 eq_refl eq_refl eq_refl RS ALrow1 ZERO3 WAProw1 IMGAProw1) as HKb4.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4) _ _ (ex_kdisj_apart SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4 (EVar 67) (EVar 169) sel row1 0 32 0 24 eq_refl eq_refl RRsel RRrow1 AP_sel_row1) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4) _ _ (ex_kdisj_apart SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4 (EVar 101) (EVar 169) arr row1 0 40 0 24 eq_refl eq_refl RRarr RRrow1 AP_arr_row1) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4) _ _ (ex_kdisj_apart SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4 (EVar 135) (EVar 169) row0 row1 0 24 0 24 eq_refl eq_refl RRrow0 RRrow1 AP_row0_row1) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) m4))))) as HKd4.
  pose proof (W_sok_win C A4 m4 _ (s - 1312) (Z.to_nat 1312) CK HW4 GLO1 GLO2) as SOK4.
  pose proof (exW_canary_ok SEGS 1410112 m4 (canary_any m4)) as CANOK4.
  pose (vals4 := vals3 ++ map (getr r4) ex_regs_list ++ map (Z_to_bv 64) [row1; exW_canary SEGS 1410112 m4]).
  pose proof (exW_kn_fixed SEGS C A4 m4 _ (ex_envL vals3 r4 [row1; exW_canary SEGS 1410112 m4]) (EVar 170) (EVar 32) (exW_canary SEGS 1410112 m4) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW4 eq_refl (proj1 CANOK4) (proj2 CANOK4) eq_refl eq_refl eq_refl SOK4 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf4.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb4 (proj2 (Forall_app _ _ _) (conj HKd4 (proj2 (Forall_app _ _ _) (conj HKf4 HKa4)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn4 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN4 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb4 HKd4 HKf4 HKa4 SOK4 CANOK4.
  repeat match goal with H : getr r4 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO3 ALrow1.
  exb_exit ST Rc4 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E4 := EEx) in HR, Hlf, HK, Hms |- *; set (log4 := LLx) in Hms, Hlf; set (M4 := mem_denot E4 m4 log4) in Hms end.
  assert (WP4 : W C A4 M4 (with_vmmaps vm4 md) /\ POSTM C A0 s m4 M4).
  { subst M4. apply (exW_win_blks C A4 A0 m4 _ E4 log4 (EVar 32) s 1312 [(EVar 67, sel, 32%Z); (EVar 101, arr, 40%Z); (EVar 135, row0, 24%Z); (EVar 169, row1, 24%Z)] CK HW4 SUB4 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel (conj Lsel_a4 (conj Fsel F0sel))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a4 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRrow0 (conj Lrow0_a4 (conj Frow0 F0row0))))|]. constructor; [exact (conj eq_refl (conj RRrow1 (conj Lrow1_a4 (conj Frow1 F0row1))))|]. constructor. }
  destruct WP4 as [HWs4 PMs4].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log4 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC4 : carry log4 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc4 : know_ok SEGS E4 M4 kn1) by (apply (carry_after SEGS E4 m4 log4 kn0 [] kn1 scs hs HC4 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact Hms |].
  pose (BS4 := [(32%nat, s); (67%nat, sel); (101%nat, arr); (135%nat, row0); (169%nat, row1)]).
  exW_regfactB BS4 HR ex_r10 Q10_4. exW_regfactB BS4 HR ex_r11 Q11_4. exW_regfactB BS4 HR ex_r1 Q1_4. exW_regfactB BS4 HR ex_r2 Q2_4. exW_regfactB BS4 HR ex_r4 Q4_4.
  clear BS4.
  lazymatch type of Q2_4 with _ = Z_to_bv 64 (s + ?off) => pose (OFF4 := off) end.
  pose proof (alloc_margin_small (6 * 4) ltac:(exW_cmp)) as MG4.
  lazymatch type of Q1_4 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_4 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A4 M4 _ Rc4 6 4 (kR - 4) (bR - 4 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs4 Q10_4 Q11_4 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM4) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_4
             ltac:(red; apply bv_eq; reflexivity) Q4_4 Q2_4 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A5 m5 vm5 r5 res4 HW5 Hres4 CSx4 Hnz4 Frow2x Lo4 F0row2 LEQ4 ZERO4 ALrow2 TOP4 PMc4 RM5.
  pose proof CSx4 as CS4. clear CSx4.
  rewrite with_vmmaps_twice in HW5 |- *.
  assert (Eres4 : res4 = Z_to_bv 64 (u res4)) by (symmetry; apply zbv_self).
  pose proof (u64_range res4) as RRrow2. set (row2 := u res4) in *. clearbody row2. rewrite Eres4 in Hres4, Frow2x, Lo4, F0row2, LEQ4, ZERO4. clear Eres4.
  change (6 * 4)%Z with 24%Z in *.
  pose proof (exW_blk_img_apart_h2 C A5 m5 _ row2 24 CK HW5 Lo4 RRrow2 eq_refl eq_refl) as IMGAProw2. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAProw2.
  pose proof (exW_win_blk_apart_h C A5 m5 _ s 1312 row2 24 CK HW5 Lo4 eq_refl RRrow2 GLO1) as WAProw2.
  assert (Frow2 : live A0 (Z_to_bv 64 row2) = None).
  { destruct (live A0 (Z_to_bv 64 row2)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB4 _ _ EE) as XX. first [discriminate Frow2x | (rewrite Frow2x in XX; discriminate XX)]. }
  pose proof Lo4 as Lrow2_a5.
  assert (SUB5 : sub_live A0 A5).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row2) by (intros ->; rewrite Frow2 in Lq; discriminate Lq). rewrite (LEQ4 q NEq). exact (SUB4 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row2 :: [Z_to_bv 64 row1; Z_to_bv 64 row0; Z_to_bv 64 arr; Z_to_bv 64 sel])) => eq_trans (LEQ4 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL4 q (fun XX => Hq (or_intror XX)))) as LDEL5.
  assert (NE_sel_row2 : Z_to_bv 64 sel <> Z_to_bv 64 row2) by (intros EE; rewrite EE in Lsel_a4; rewrite Frow2x in Lsel_a4; discriminate Lsel_a4).
  assert (Lsel_a5 : live A5 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ4 _ NE_sel_row2); exact Lsel_a4).
  pose proof (exW_blk_apart_h C A5 m5 _ sel row2 32 24 CK HW5 Lsel_a5 Lrow2_a5 NE_sel_row2 RRsel RRrow2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel_row2.
  assert (NE_arr_row2 : Z_to_bv 64 arr <> Z_to_bv 64 row2) by (intros EE; rewrite EE in Larr_a4; rewrite Frow2x in Larr_a4; discriminate Larr_a4).
  assert (Larr_a5 : live A5 (Z_to_bv 64 arr) = Some 40%Z) by (rewrite (LEQ4 _ NE_arr_row2); exact Larr_a4).
  pose proof (exW_blk_apart_h C A5 m5 _ arr row2 40 24 CK HW5 Larr_a5 Lrow2_a5 NE_arr_row2 RRarr RRrow2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_row2.
  assert (NE_row0_row2 : Z_to_bv 64 row0 <> Z_to_bv 64 row2) by (intros EE; rewrite EE in Lrow0_a4; rewrite Frow2x in Lrow0_a4; discriminate Lrow0_a4).
  assert (Lrow0_a5 : live A5 (Z_to_bv 64 row0) = Some 24%Z) by (rewrite (LEQ4 _ NE_row0_row2); exact Lrow0_a4).
  pose proof (exW_blk_apart_h C A5 m5 _ row0 row2 24 24 CK HW5 Lrow0_a5 Lrow2_a5 NE_row0_row2 RRrow0 RRrow2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row0_row2.
  assert (NE_row1_row2 : Z_to_bv 64 row1 <> Z_to_bv 64 row2) by (intros EE; rewrite EE in Lrow1_a4; rewrite Frow2x in Lrow1_a4; discriminate Lrow1_a4).
  assert (Lrow1_a5 : live A5 (Z_to_bv 64 row1) = Some 24%Z) by (rewrite (LEQ4 _ NE_row1_row2); exact Lrow1_a4).
  pose proof (exW_blk_apart_h C A5 m5 _ row1 row2 24 24 CK HW5 Lrow1_a5 Lrow2_a5 NE_row1_row2 RRrow1 RRrow2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row1_row2.
  assert (PM5 : POSTM C A0 s m0 m5).
  { eapply POSTM_trans; [exact PM4|]. eapply POSTM_trans; [exact PMs4|]. apply (POSTM_sub C A0 A4 _ _ _ SUB4).
    apply (POSTM_mono C A4 (s + OFF4) s); [unfold OFF4; lia | exact PMc4]. }
  replace (kR - 4 - 1)%Z with (kR - 5)%Z in RM5 by lia. rewrite MG4 in RM5. replace (bR - 4 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 5 * 2 ^ 17)%Z in RM5 by lia.
  assert (KEPT4 : Forall (ex_region_kept E4 M4 m5) [(EVar 32, OFF4, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 40%Z); (EVar 135, 0%Z, 24%Z); (EVar 169, 0%Z, 24%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF4 1312 M4 m5 E4 (EVar 32) CK (proj1 PMc4) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 M4 _ M4 m5 E4 (EVar 67) sel 32 CK HWs4 Lsel_a4 RRsel eq_refl (proj2 PMc4) Lsel_a4 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 M4 _ M4 m5 E4 (EVar 101) arr 40 CK HWs4 Larr_a4 RRarr eq_refl (proj2 PMc4) Larr_a4 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 M4 _ M4 m5 E4 (EVar 135) row0 24 CK HWs4 Lrow0_a4 RRrow0 eq_refl (proj2 PMc4) Lrow0_a4 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 M4 _ M4 m5 E4 (EVar 169) row1 24 CK HWs4 Lrow1_a4 RRrow1 eq_refl (proj2 PMc4) Lrow1_a4 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E4 M4 m5 _ [] _ HKc4 KEPT4) as HKk4.
  match type of HKk4 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E4 m5 kk') in HKk4 end.
  pose proof (regs_ok_agree 171%nat E4 (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) _ _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa4.
  pose proof (exW_regs_call _ _ _ _ _ HRa4 (ex_regs_ok_junk vals4 r5 [row2; exW_canary SEGS 1410112 m5] 171%nat ltac:(vm_cast_no_check (eq_refl 171%nat))) CS4) as HRn5.
  clear HRa4.
  assert (HKa5 : know_ok SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5 _) by (exact (know_ok_agree SEGS 171%nat E4 _ m5 _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk4)).
  rewrite (fr_denot_agree 171%nat E4 (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) _ fr (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r5 ex_r10 (EVar 203) HRn5 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres4)) as HRx5. clear HRn5. rename HRx5 into HRn5.
  clear HR HK Hlf Hms HKc4 HKk4 KEPT4 HC4 HWs4 PMs4 Q10_4 Q11_4 Q1_4 Q2_4 Q4_4 PM4 HW4 PMc4 CS4 SUB4 RM4 MG4 TOP4 LEQ4 Hnz4 Frow2x Lo4 OFF4 LDEL4 Lsel_a4 Larr_a4 Lrow0_a4 Lrow1_a4.
  subst M4. clear log4. clear E4. try clear Rc4. clear KN4.
  lazymatch type of HRn5 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn5 end.
  pose proof (exW_kn_blk SEGS C A5 m5 _ (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) (EVar 203) (EVar 32) row2 24 s 1312 65536 1347584 p16_segs CK HW5 Lrow2_a5 RRrow2 eq_refl eq_refl eq_refl RS ALrow2 ZERO4 WAProw2 IMGAProw2) as HKb5.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5) _ _ (ex_kdisj_apart SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5 (EVar 67) (EVar 203) sel row2 0 32 0 24 eq_refl eq_refl RRsel RRrow2 AP_sel_row2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5) _ _ (ex_kdisj_apart SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5 (EVar 101) (EVar 203) arr row2 0 40 0 24 eq_refl eq_refl RRarr RRrow2 AP_arr_row2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5) _ _ (ex_kdisj_apart SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5 (EVar 135) (EVar 203) row0 row2 0 24 0 24 eq_refl eq_refl RRrow0 RRrow2 AP_row0_row2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5) _ _ (ex_kdisj_apart SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5 (EVar 169) (EVar 203) row1 row2 0 24 0 24 eq_refl eq_refl RRrow1 RRrow2 AP_row1_row2) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) m5)))))) as HKd5.
  pose proof (W_sok_win C A5 m5 _ (s - 1312) (Z.to_nat 1312) CK HW5 GLO1 GLO2) as SOK5.
  pose proof (exW_canary_ok SEGS 1410112 m5 (canary_any m5)) as CANOK5.
  pose (vals5 := vals4 ++ map (getr r5) ex_regs_list ++ map (Z_to_bv 64) [row2; exW_canary SEGS 1410112 m5]).
  pose proof (exW_kn_fixed SEGS C A5 m5 _ (ex_envL vals4 r5 [row2; exW_canary SEGS 1410112 m5]) (EVar 204) (EVar 32) (exW_canary SEGS 1410112 m5) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW5 eq_refl (proj1 CANOK5) (proj2 CANOK5) eq_refl eq_refl eq_refl SOK5 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf5.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb5 (proj2 (Forall_app _ _ _) (conj HKd5 (proj2 (Forall_app _ _ _) (conj HKf5 HKa5)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn5 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN5 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb5 HKd5 HKf5 HKa5 SOK5 CANOK5.
  repeat match goal with H : getr r5 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO4 ALrow2.
  exb_exit ST Rc5 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E5 := EEx) in HR, Hlf, HK, Hms |- *; set (log5 := LLx) in Hms, Hlf; set (M5 := mem_denot E5 m5 log5) in Hms end.
  assert (WP5 : W C A5 M5 (with_vmmaps vm5 md) /\ POSTM C A0 s m5 M5).
  { subst M5. apply (exW_win_blks C A5 A0 m5 _ E5 log5 (EVar 32) s 1312 [(EVar 67, sel, 32%Z); (EVar 101, arr, 40%Z); (EVar 135, row0, 24%Z); (EVar 169, row1, 24%Z); (EVar 203, row2, 24%Z)] CK HW5 SUB5 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel (conj Lsel_a5 (conj Fsel F0sel))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a5 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRrow0 (conj Lrow0_a5 (conj Frow0 F0row0))))|]. constructor; [exact (conj eq_refl (conj RRrow1 (conj Lrow1_a5 (conj Frow1 F0row1))))|]. constructor; [exact (conj eq_refl (conj RRrow2 (conj Lrow2_a5 (conj Frow2 F0row2))))|]. constructor. }
  destruct WP5 as [HWs5 PMs5].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log5 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC5 : carry log5 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc5 : know_ok SEGS E5 M5 kn1) by (apply (carry_after SEGS E5 m5 log5 kn0 [] kn1 scs hs HC5 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact Hms |].
  pose (BS5 := [(32%nat, s); (67%nat, sel); (101%nat, arr); (135%nat, row0); (169%nat, row1); (203%nat, row2)]).
  exW_regfactB BS5 HR ex_r10 Q10_5. exW_regfactB BS5 HR ex_r11 Q11_5. exW_regfactB BS5 HR ex_r1 Q1_5. exW_regfactB BS5 HR ex_r2 Q2_5. exW_regfactB BS5 HR ex_r4 Q4_5.
  clear BS5.
  lazymatch type of Q2_5 with _ = Z_to_bv 64 (s + ?off) => pose (OFF5 := off) end.
  pose proof (alloc_margin_small (6 * 4) ltac:(exW_cmp)) as MG5.
  lazymatch type of Q1_5 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_5 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A5 M5 _ Rc5 6 4 (kR - 5) (bR - 5 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs5 Q10_5 Q11_5 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM5) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_5
             ltac:(red; apply bv_eq; reflexivity) Q4_5 Q2_5 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A6 m6 vm6 r6 res5 HW6 Hres5 CSx5 Hnz5 Frow3x Lo5 F0row3 LEQ5 ZERO5 ALrow3 TOP5 PMc5 RM6.
  pose proof CSx5 as CS5. clear CSx5.
  rewrite with_vmmaps_twice in HW6 |- *.
  assert (Eres5 : res5 = Z_to_bv 64 (u res5)) by (symmetry; apply zbv_self).
  pose proof (u64_range res5) as RRrow3. set (row3 := u res5) in *. clearbody row3. rewrite Eres5 in Hres5, Frow3x, Lo5, F0row3, LEQ5, ZERO5. clear Eres5.
  change (6 * 4)%Z with 24%Z in *.
  pose proof (exW_blk_img_apart_h2 C A6 m6 _ row3 24 CK HW6 Lo5 RRrow3 eq_refl eq_refl) as IMGAProw3. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAProw3.
  pose proof (exW_win_blk_apart_h C A6 m6 _ s 1312 row3 24 CK HW6 Lo5 eq_refl RRrow3 GLO1) as WAProw3.
  assert (Frow3 : live A0 (Z_to_bv 64 row3) = None).
  { destruct (live A0 (Z_to_bv 64 row3)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB5 _ _ EE) as XX. first [discriminate Frow3x | (rewrite Frow3x in XX; discriminate XX)]. }
  pose proof Lo5 as Lrow3_a6.
  assert (SUB6 : sub_live A0 A6).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row3) by (intros ->; rewrite Frow3 in Lq; discriminate Lq). rewrite (LEQ5 q NEq). exact (SUB5 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row3 :: [Z_to_bv 64 row2; Z_to_bv 64 row1; Z_to_bv 64 row0; Z_to_bv 64 arr; Z_to_bv 64 sel])) => eq_trans (LEQ5 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL5 q (fun XX => Hq (or_intror XX)))) as LDEL6.
  assert (NE_sel_row3 : Z_to_bv 64 sel <> Z_to_bv 64 row3) by (intros EE; rewrite EE in Lsel_a5; rewrite Frow3x in Lsel_a5; discriminate Lsel_a5).
  assert (Lsel_a6 : live A6 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ5 _ NE_sel_row3); exact Lsel_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ sel row3 32 24 CK HW6 Lsel_a6 Lrow3_a6 NE_sel_row3 RRsel RRrow3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel_row3.
  assert (NE_arr_row3 : Z_to_bv 64 arr <> Z_to_bv 64 row3) by (intros EE; rewrite EE in Larr_a5; rewrite Frow3x in Larr_a5; discriminate Larr_a5).
  assert (Larr_a6 : live A6 (Z_to_bv 64 arr) = Some 40%Z) by (rewrite (LEQ5 _ NE_arr_row3); exact Larr_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ arr row3 40 24 CK HW6 Larr_a6 Lrow3_a6 NE_arr_row3 RRarr RRrow3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_row3.
  assert (NE_row0_row3 : Z_to_bv 64 row0 <> Z_to_bv 64 row3) by (intros EE; rewrite EE in Lrow0_a5; rewrite Frow3x in Lrow0_a5; discriminate Lrow0_a5).
  assert (Lrow0_a6 : live A6 (Z_to_bv 64 row0) = Some 24%Z) by (rewrite (LEQ5 _ NE_row0_row3); exact Lrow0_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ row0 row3 24 24 CK HW6 Lrow0_a6 Lrow3_a6 NE_row0_row3 RRrow0 RRrow3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row0_row3.
  assert (NE_row1_row3 : Z_to_bv 64 row1 <> Z_to_bv 64 row3) by (intros EE; rewrite EE in Lrow1_a5; rewrite Frow3x in Lrow1_a5; discriminate Lrow1_a5).
  assert (Lrow1_a6 : live A6 (Z_to_bv 64 row1) = Some 24%Z) by (rewrite (LEQ5 _ NE_row1_row3); exact Lrow1_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ row1 row3 24 24 CK HW6 Lrow1_a6 Lrow3_a6 NE_row1_row3 RRrow1 RRrow3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row1_row3.
  assert (NE_row2_row3 : Z_to_bv 64 row2 <> Z_to_bv 64 row3) by (intros EE; rewrite EE in Lrow2_a5; rewrite Frow3x in Lrow2_a5; discriminate Lrow2_a5).
  assert (Lrow2_a6 : live A6 (Z_to_bv 64 row2) = Some 24%Z) by (rewrite (LEQ5 _ NE_row2_row3); exact Lrow2_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ row2 row3 24 24 CK HW6 Lrow2_a6 Lrow3_a6 NE_row2_row3 RRrow2 RRrow3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row2_row3.
  assert (PM6 : POSTM C A0 s m0 m6).
  { eapply POSTM_trans; [exact PM5|]. eapply POSTM_trans; [exact PMs5|]. apply (POSTM_sub C A0 A5 _ _ _ SUB5).
    apply (POSTM_mono C A5 (s + OFF5) s); [unfold OFF5; lia | exact PMc5]. }
  replace (kR - 5 - 1)%Z with (kR - 6)%Z in RM6 by lia. rewrite MG5 in RM6. replace (bR - 5 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 6 * 2 ^ 17)%Z in RM6 by lia.
  assert (KEPT5 : Forall (ex_region_kept E5 M5 m6) [(EVar 32, OFF5, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 40%Z); (EVar 135, 0%Z, 24%Z); (EVar 169, 0%Z, 24%Z); (EVar 203, 0%Z, 24%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF5 1312 M5 m6 E5 (EVar 32) CK (proj1 PMc5) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 67) sel 32 CK HWs5 Lsel_a5 RRsel eq_refl (proj2 PMc5) Lsel_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 101) arr 40 CK HWs5 Larr_a5 RRarr eq_refl (proj2 PMc5) Larr_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 135) row0 24 CK HWs5 Lrow0_a5 RRrow0 eq_refl (proj2 PMc5) Lrow0_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 169) row1 24 CK HWs5 Lrow1_a5 RRrow1 eq_refl (proj2 PMc5) Lrow1_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 203) row2 24 CK HWs5 Lrow2_a5 RRrow2 eq_refl (proj2 PMc5) Lrow2_a5 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E5 M5 m6 _ [] _ HKc5 KEPT5) as HKk5.
  match type of HKk5 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E5 m6 kk') in HKk5 end.
  pose proof (regs_ok_agree 205%nat E5 (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) _ _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa5.
  pose proof (exW_regs_call _ _ _ _ _ HRa5 (ex_regs_ok_junk vals5 r6 [row3; exW_canary SEGS 1410112 m6] 205%nat ltac:(vm_cast_no_check (eq_refl 205%nat))) CS5) as HRn6.
  clear HRa5.
  assert (HKa6 : know_ok SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6 _) by (exact (know_ok_agree SEGS 205%nat E5 _ m6 _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk5)).
  rewrite (fr_denot_agree 205%nat E5 (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) _ fr (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r6 ex_r10 (EVar 237) HRn6 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres5)) as HRx6. clear HRn6. rename HRx6 into HRn6.
  clear HR HK Hlf Hms HKc5 HKk5 KEPT5 HC5 HWs5 PMs5 Q10_5 Q11_5 Q1_5 Q2_5 Q4_5 PM5 HW5 PMc5 CS5 SUB5 RM5 MG5 TOP5 LEQ5 Hnz5 Frow3x Lo5 OFF5 LDEL5 Lsel_a5 Larr_a5 Lrow0_a5 Lrow1_a5 Lrow2_a5.
  subst M5. clear log5. clear E5. try clear Rc5. clear KN5.
  lazymatch type of HRn6 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn6 end.
  pose proof (exW_kn_blk SEGS C A6 m6 _ (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) (EVar 237) (EVar 32) row3 24 s 1312 65536 1347584 p16_segs CK HW6 Lrow3_a6 RRrow3 eq_refl eq_refl eq_refl RS ALrow3 ZERO5 WAProw3 IMGAProw3) as HKb6.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6 (EVar 67) (EVar 237) sel row3 0 32 0 24 eq_refl eq_refl RRsel RRrow3 AP_sel_row3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6 (EVar 101) (EVar 237) arr row3 0 40 0 24 eq_refl eq_refl RRarr RRrow3 AP_arr_row3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6 (EVar 135) (EVar 237) row0 row3 0 24 0 24 eq_refl eq_refl RRrow0 RRrow3 AP_row0_row3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6 (EVar 169) (EVar 237) row1 row3 0 24 0 24 eq_refl eq_refl RRrow1 RRrow3 AP_row1_row3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6 (EVar 203) (EVar 237) row2 row3 0 24 0 24 eq_refl eq_refl RRrow2 RRrow3 AP_row2_row3) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) m6))))))) as HKd6.
  pose proof (W_sok_win C A6 m6 _ (s - 1312) (Z.to_nat 1312) CK HW6 GLO1 GLO2) as SOK6.
  pose proof (exW_canary_ok SEGS 1410112 m6 (canary_any m6)) as CANOK6.
  pose (vals6 := vals5 ++ map (getr r6) ex_regs_list ++ map (Z_to_bv 64) [row3; exW_canary SEGS 1410112 m6]).
  pose proof (exW_kn_fixed SEGS C A6 m6 _ (ex_envL vals5 r6 [row3; exW_canary SEGS 1410112 m6]) (EVar 238) (EVar 32) (exW_canary SEGS 1410112 m6) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW6 eq_refl (proj1 CANOK6) (proj2 CANOK6) eq_refl eq_refl eq_refl SOK6 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf6.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb6 (proj2 (Forall_app _ _ _) (conj HKd6 (proj2 (Forall_app _ _ _) (conj HKf6 HKa6)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn6 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN6 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb6 HKd6 HKf6 HKa6 SOK6 CANOK6.
  repeat match goal with H : getr r6 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO5 ALrow3.
  exb_exit ST Rc6 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E6 := EEx) in HR, Hlf, HK, Hms |- *; set (log6 := LLx) in Hms, Hlf; set (M6 := mem_denot E6 m6 log6) in Hms end.
  assert (WP6 : W C A6 M6 (with_vmmaps vm6 md) /\ POSTM C A0 s m6 M6).
  { subst M6. apply (exW_win_blks C A6 A0 m6 _ E6 log6 (EVar 32) s 1312 [(EVar 67, sel, 32%Z); (EVar 101, arr, 40%Z); (EVar 135, row0, 24%Z); (EVar 169, row1, 24%Z); (EVar 203, row2, 24%Z); (EVar 237, row3, 24%Z)] CK HW6 SUB6 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel (conj Lsel_a6 (conj Fsel F0sel))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a6 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRrow0 (conj Lrow0_a6 (conj Frow0 F0row0))))|]. constructor; [exact (conj eq_refl (conj RRrow1 (conj Lrow1_a6 (conj Frow1 F0row1))))|]. constructor; [exact (conj eq_refl (conj RRrow2 (conj Lrow2_a6 (conj Frow2 F0row2))))|]. constructor; [exact (conj eq_refl (conj RRrow3 (conj Lrow3_a6 (conj Frow3 F0row3))))|]. constructor. }
  destruct WP6 as [HWs6 PMs6].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log6 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC6 : carry log6 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc6 : know_ok SEGS E6 M6 kn1) by (apply (carry_after SEGS E6 m6 log6 kn0 [] kn1 scs hs HC6 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact Hms |].
  pose (BS6 := [(32%nat, s); (67%nat, sel); (101%nat, arr); (135%nat, row0); (169%nat, row1); (203%nat, row2); (237%nat, row3)]).
  exW_regfactB BS6 HR ex_r10 Q10_6. exW_regfactB BS6 HR ex_r11 Q11_6. exW_regfactB BS6 HR ex_r1 Q1_6. exW_regfactB BS6 HR ex_r2 Q2_6. exW_regfactB BS6 HR ex_r4 Q4_6.
  clear BS6.
  lazymatch type of Q2_6 with _ = Z_to_bv 64 (s + ?off) => pose (OFF6 := off) end.
  pose proof (alloc_margin_small (6 * 4) ltac:(exW_cmp)) as MG6.
  lazymatch type of Q1_6 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_6 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A6 M6 _ Rc6 6 4 (kR - 6) (bR - 6 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs6 Q10_6 Q11_6 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM6) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_6
             ltac:(red; apply bv_eq; reflexivity) Q4_6 Q2_6 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A7 m7 vm7 r7 res6 HW7 Hres6 CSx6 Hnz6 Frow4x Lo6 F0row4 LEQ6 ZERO6 ALrow4 TOP6 PMc6 RM7.
  pose proof CSx6 as CS6. clear CSx6.
  rewrite with_vmmaps_twice in HW7 |- *.
  assert (Eres6 : res6 = Z_to_bv 64 (u res6)) by (symmetry; apply zbv_self).
  pose proof (u64_range res6) as RRrow4. set (row4 := u res6) in *. clearbody row4. rewrite Eres6 in Hres6, Frow4x, Lo6, F0row4, LEQ6, ZERO6. clear Eres6.
  change (6 * 4)%Z with 24%Z in *.
  pose proof (exW_blk_img_apart_h2 C A7 m7 _ row4 24 CK HW7 Lo6 RRrow4 eq_refl eq_refl) as IMGAProw4. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAProw4.
  pose proof (exW_win_blk_apart_h C A7 m7 _ s 1312 row4 24 CK HW7 Lo6 eq_refl RRrow4 GLO1) as WAProw4.
  assert (Frow4 : live A0 (Z_to_bv 64 row4) = None).
  { destruct (live A0 (Z_to_bv 64 row4)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB6 _ _ EE) as XX. first [discriminate Frow4x | (rewrite Frow4x in XX; discriminate XX)]. }
  pose proof Lo6 as Lrow4_a7.
  assert (SUB7 : sub_live A0 A7).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 row4) by (intros ->; rewrite Frow4 in Lq; discriminate Lq). rewrite (LEQ6 q NEq). exact (SUB6 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 row4 :: [Z_to_bv 64 row3; Z_to_bv 64 row2; Z_to_bv 64 row1; Z_to_bv 64 row0; Z_to_bv 64 arr; Z_to_bv 64 sel])) => eq_trans (LEQ6 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL6 q (fun XX => Hq (or_intror XX)))) as LDEL7.
  assert (NE_sel_row4 : Z_to_bv 64 sel <> Z_to_bv 64 row4) by (intros EE; rewrite EE in Lsel_a6; rewrite Frow4x in Lsel_a6; discriminate Lsel_a6).
  assert (Lsel_a7 : live A7 (Z_to_bv 64 sel) = Some 32%Z) by (rewrite (LEQ6 _ NE_sel_row4); exact Lsel_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ sel row4 32 24 CK HW7 Lsel_a7 Lrow4_a7 NE_sel_row4 RRsel RRrow4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sel_row4.
  assert (NE_arr_row4 : Z_to_bv 64 arr <> Z_to_bv 64 row4) by (intros EE; rewrite EE in Larr_a6; rewrite Frow4x in Larr_a6; discriminate Larr_a6).
  assert (Larr_a7 : live A7 (Z_to_bv 64 arr) = Some 40%Z) by (rewrite (LEQ6 _ NE_arr_row4); exact Larr_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ arr row4 40 24 CK HW7 Larr_a7 Lrow4_a7 NE_arr_row4 RRarr RRrow4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_row4.
  assert (NE_row0_row4 : Z_to_bv 64 row0 <> Z_to_bv 64 row4) by (intros EE; rewrite EE in Lrow0_a6; rewrite Frow4x in Lrow0_a6; discriminate Lrow0_a6).
  assert (Lrow0_a7 : live A7 (Z_to_bv 64 row0) = Some 24%Z) by (rewrite (LEQ6 _ NE_row0_row4); exact Lrow0_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ row0 row4 24 24 CK HW7 Lrow0_a7 Lrow4_a7 NE_row0_row4 RRrow0 RRrow4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row0_row4.
  assert (NE_row1_row4 : Z_to_bv 64 row1 <> Z_to_bv 64 row4) by (intros EE; rewrite EE in Lrow1_a6; rewrite Frow4x in Lrow1_a6; discriminate Lrow1_a6).
  assert (Lrow1_a7 : live A7 (Z_to_bv 64 row1) = Some 24%Z) by (rewrite (LEQ6 _ NE_row1_row4); exact Lrow1_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ row1 row4 24 24 CK HW7 Lrow1_a7 Lrow4_a7 NE_row1_row4 RRrow1 RRrow4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row1_row4.
  assert (NE_row2_row4 : Z_to_bv 64 row2 <> Z_to_bv 64 row4) by (intros EE; rewrite EE in Lrow2_a6; rewrite Frow4x in Lrow2_a6; discriminate Lrow2_a6).
  assert (Lrow2_a7 : live A7 (Z_to_bv 64 row2) = Some 24%Z) by (rewrite (LEQ6 _ NE_row2_row4); exact Lrow2_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ row2 row4 24 24 CK HW7 Lrow2_a7 Lrow4_a7 NE_row2_row4 RRrow2 RRrow4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row2_row4.
  assert (NE_row3_row4 : Z_to_bv 64 row3 <> Z_to_bv 64 row4) by (intros EE; rewrite EE in Lrow3_a6; rewrite Frow4x in Lrow3_a6; discriminate Lrow3_a6).
  assert (Lrow3_a7 : live A7 (Z_to_bv 64 row3) = Some 24%Z) by (rewrite (LEQ6 _ NE_row3_row4); exact Lrow3_a6).
  pose proof (exW_blk_apart_h C A7 m7 _ row3 row4 24 24 CK HW7 Lrow3_a7 Lrow4_a7 NE_row3_row4 RRrow3 RRrow4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_row3_row4.
  assert (PM7 : POSTM C A0 s m0 m7).
  { eapply POSTM_trans; [exact PM6|]. eapply POSTM_trans; [exact PMs6|]. apply (POSTM_sub C A0 A6 _ _ _ SUB6).
    apply (POSTM_mono C A6 (s + OFF6) s); [unfold OFF6; lia | exact PMc6]. }
  replace (kR - 6 - 1)%Z with (kR - 7)%Z in RM7 by lia. rewrite MG6 in RM7. replace (bR - 6 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 7 * 2 ^ 17)%Z in RM7 by lia.
  assert (KEPT6 : Forall (ex_region_kept E6 M6 m7) [(EVar 32, OFF6, 0%Z); (EVar 67, 0%Z, 32%Z); (EVar 101, 0%Z, 40%Z); (EVar 135, 0%Z, 24%Z); (EVar 169, 0%Z, 24%Z); (EVar 203, 0%Z, 24%Z); (EVar 237, 0%Z, 24%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF6 1312 M6 m7 E6 (EVar 32) CK (proj1 PMc6) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 67) sel 32 CK HWs6 Lsel_a6 RRsel eq_refl (proj2 PMc6) Lsel_a6 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 101) arr 40 CK HWs6 Larr_a6 RRarr eq_refl (proj2 PMc6) Larr_a6 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 135) row0 24 CK HWs6 Lrow0_a6 RRrow0 eq_refl (proj2 PMc6) Lrow0_a6 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 169) row1 24 CK HWs6 Lrow1_a6 RRrow1 eq_refl (proj2 PMc6) Lrow1_a6 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 203) row2 24 CK HWs6 Lrow2_a6 RRrow2 eq_refl (proj2 PMc6) Lrow2_a6 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A6 A6 M6 _ M6 m7 E6 (EVar 237) row3 24 CK HWs6 Lrow3_a6 RRrow3 eq_refl (proj2 PMc6) Lrow3_a6 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E6 M6 m7 _ [] _ HKc6 KEPT6) as HKk6.
  match type of HKk6 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E6 m7 kk') in HKk6 end.
  pose proof (regs_ok_agree 239%nat E6 (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) _ _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa6.
  pose proof (exW_regs_call _ _ _ _ _ HRa6 (ex_regs_ok_junk vals6 r7 [row4; exW_canary SEGS 1410112 m7] 239%nat ltac:(vm_cast_no_check (eq_refl 239%nat))) CS6) as HRn7.
  clear HRa6.
  assert (HKa7 : know_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7 _) by (exact (know_ok_agree SEGS 239%nat E6 _ m7 _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk6)).
  rewrite (fr_denot_agree 239%nat E6 (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) _ fr (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r7 ex_r10 (EVar 271) HRn7 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres6)) as HRx7. clear HRn7. rename HRx7 into HRn7.
  clear HR HK Hlf Hms HKc6 HKk6 KEPT6 HC6 HWs6 PMs6 Q10_6 Q11_6 Q1_6 Q2_6 Q4_6 PM6 HW6 PMc6 CS6 SUB6 RM6 MG6 TOP6 LEQ6 Hnz6 Frow4x Lo6 OFF6 LDEL6 Lsel_a6 Larr_a6 Lrow0_a6 Lrow1_a6 Lrow2_a6 Lrow3_a6.
  subst M6. clear log6. clear E6. try clear Rc6. clear KN6.
  lazymatch type of HRn7 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn7 end.
  pose proof (exW_kn_blk SEGS C A7 m7 _ (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) (EVar 271) (EVar 32) row4 24 s 1312 65536 1347584 p16_segs CK HW7 Lrow4_a7 RRrow4 eq_refl eq_refl eq_refl RS ALrow4 ZERO6 WAProw4 IMGAProw4) as HKb7.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7 (EVar 67) (EVar 271) sel row4 0 32 0 24 eq_refl eq_refl RRsel RRrow4 AP_sel_row4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7 (EVar 101) (EVar 271) arr row4 0 40 0 24 eq_refl eq_refl RRarr RRrow4 AP_arr_row4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7 (EVar 135) (EVar 271) row0 row4 0 24 0 24 eq_refl eq_refl RRrow0 RRrow4 AP_row0_row4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7 (EVar 169) (EVar 271) row1 row4 0 24 0 24 eq_refl eq_refl RRrow1 RRrow4 AP_row1_row4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7 (EVar 203) (EVar 271) row2 row4 0 24 0 24 eq_refl eq_refl RRrow2 RRrow4 AP_row2_row4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7) _ _ (ex_kdisj_apart SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7 (EVar 237) (EVar 271) row3 row4 0 24 0 24 eq_refl eq_refl RRrow3 RRrow4 AP_row3_row4) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) m7)))))))) as HKd7.
  pose proof (W_sok_win C A7 m7 _ (s - 1312) (Z.to_nat 1312) CK HW7 GLO1 GLO2) as SOK7.
  pose proof (exW_canary_ok SEGS 1410112 m7 (canary_any m7)) as CANOK7.
  pose (vals7 := vals6 ++ map (getr r7) ex_regs_list ++ map (Z_to_bv 64) [row4; exW_canary SEGS 1410112 m7]).
  pose proof (exW_kn_fixed SEGS C A7 m7 _ (ex_envL vals6 r7 [row4; exW_canary SEGS 1410112 m7]) (EVar 272) (EVar 32) (exW_canary SEGS 1410112 m7) s 1312 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW7 eq_refl (proj1 CANOK7) (proj2 CANOK7) eq_refl eq_refl eq_refl SOK7 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf7.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb7 (proj2 (Forall_app _ _ _) (conj HKd7 (proj2 (Forall_app _ _ _) (conj HKf7 HKa7)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn7 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN7 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb7 HKd7 HKf7 HKa7 SOK7 CANOK7.
  repeat match goal with H : getr r7 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO6 ALrow4.
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E7 := EEx) in HR, Hlf, HK, Hms |- *; set (log7 := LLx) in Hms, Hlf; set (M7 := mem_denot E7 m7 log7) in Hms end.
  assert (WP7 : W C A7 M7 (with_vmmaps vm7 md) /\ POSTM C A0 s m7 M7).
  { subst M7. apply (exW_win_blks C A7 A0 m7 _ E7 log7 (EVar 32) s 1312 [(EVar 67, sel, 32%Z); (EVar 101, arr, 40%Z); (EVar 135, row0, 24%Z); (EVar 169, row1, 24%Z); (EVar 203, row2, 24%Z); (EVar 237, row3, 24%Z); (EVar 271, row4, 24%Z)] CK HW7 SUB7 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRsel (conj Lsel_a7 (conj Fsel F0sel))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a7 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRrow0 (conj Lrow0_a7 (conj Frow0 F0row0))))|]. constructor; [exact (conj eq_refl (conj RRrow1 (conj Lrow1_a7 (conj Frow1 F0row1))))|]. constructor; [exact (conj eq_refl (conj RRrow2 (conj Lrow2_a7 (conj Frow2 F0row2))))|]. constructor; [exact (conj eq_refl (conj RRrow3 (conj Lrow3_a7 (conj Frow3 F0row3))))|]. constructor; [exact (conj eq_refl (conj RRrow4 (conj Lrow4_a7 (conj Frow4 F0row4))))|]. constructor. }
  destruct WP7 as [HWs7 PMs7].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact Hms |].
  pose (BSF := [(32%nat, s); (67%nat, sel); (101%nat, arr); (135%nat, row0); (169%nat, row1); (203%nat, row2); (237%nat, row3); (271%nat, row4)]).
  exW_regfactB BSF HR ex_r10 G10.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel 0%Z 4%nat Csel_0.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel 4%Z 4%nat Csel_4.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel 8%Z 4%nat Csel_8.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel 12%Z 4%nat Csel_12.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel 16%Z 8%nat Csel_16.
  exW_cellB HK Hlf r0 BSF (EVar 67) sel 24%Z 8%nat Csel_24.
  exW_cellB HK Hlf r0 BSF (EVar 101) arr 0%Z 8%nat Carr_0.
  exW_cellB HK Hlf r0 BSF (EVar 101) arr 8%Z 8%nat Carr_8.
  exW_cellB HK Hlf r0 BSF (EVar 101) arr 16%Z 8%nat Carr_16.
  exW_cellB HK Hlf r0 BSF (EVar 101) arr 24%Z 8%nat Carr_24.
  exW_cellB HK Hlf r0 BSF (EVar 101) arr 32%Z 8%nat Carr_32.
  exW_cellB HK Hlf r0 BSF (EVar 135) row0 0%Z 4%nat Crow0_0.
  exW_cellB HK Hlf r0 BSF (EVar 135) row0 4%Z 4%nat Crow0_4.
  exW_cellB HK Hlf r0 BSF (EVar 135) row0 8%Z 4%nat Crow0_8.
  exW_cellB HK Hlf r0 BSF (EVar 135) row0 12%Z 4%nat Crow0_12.
  exW_cellB HK Hlf r0 BSF (EVar 135) row0 16%Z 4%nat Crow0_16.
  exW_cellB HK Hlf r0 BSF (EVar 135) row0 20%Z 4%nat Crow0_20.
  exW_cellB HK Hlf r0 BSF (EVar 169) row1 0%Z 4%nat Crow1_0.
  exW_cellB HK Hlf r0 BSF (EVar 169) row1 4%Z 4%nat Crow1_4.
  exW_cellB HK Hlf r0 BSF (EVar 169) row1 8%Z 4%nat Crow1_8.
  exW_cellB HK Hlf r0 BSF (EVar 169) row1 12%Z 4%nat Crow1_12.
  exW_cellB HK Hlf r0 BSF (EVar 169) row1 16%Z 4%nat Crow1_16.
  exW_cellB HK Hlf r0 BSF (EVar 169) row1 20%Z 4%nat Crow1_20.
  exW_cellB HK Hlf r0 BSF (EVar 203) row2 0%Z 4%nat Crow2_0.
  exW_cellB HK Hlf r0 BSF (EVar 203) row2 4%Z 4%nat Crow2_4.
  exW_cellB HK Hlf r0 BSF (EVar 203) row2 8%Z 4%nat Crow2_8.
  exW_cellB HK Hlf r0 BSF (EVar 203) row2 12%Z 4%nat Crow2_12.
  exW_cellB HK Hlf r0 BSF (EVar 203) row2 16%Z 4%nat Crow2_16.
  exW_cellB HK Hlf r0 BSF (EVar 203) row2 20%Z 4%nat Crow2_20.
  exW_cellB HK Hlf r0 BSF (EVar 237) row3 0%Z 4%nat Crow3_0.
  exW_cellB HK Hlf r0 BSF (EVar 237) row3 4%Z 4%nat Crow3_4.
  exW_cellB HK Hlf r0 BSF (EVar 237) row3 8%Z 4%nat Crow3_8.
  exW_cellB HK Hlf r0 BSF (EVar 237) row3 12%Z 4%nat Crow3_12.
  exW_cellB HK Hlf r0 BSF (EVar 237) row3 16%Z 4%nat Crow3_16.
  exW_cellB HK Hlf r0 BSF (EVar 237) row3 20%Z 4%nat Crow3_20.
  exW_cellB HK Hlf r0 BSF (EVar 271) row4 0%Z 4%nat Crow4_0.
  exW_cellB HK Hlf r0 BSF (EVar 271) row4 4%Z 4%nat Crow4_4.
  exW_cellB HK Hlf r0 BSF (EVar 271) row4 8%Z 4%nat Crow4_8.
  exW_cellB HK Hlf r0 BSF (EVar 271) row4 12%Z 4%nat Crow4_12.
  exW_cellB HK Hlf r0 BSF (EVar 271) row4 16%Z 4%nat Crow4_16.
  exW_cellB HK Hlf r0 BSF (EVar 271) row4 20%Z 4%nat Crow4_20.
  refine (HC A7 M7 vm7 RcF sel arr row0 row1 row2 row3 row4 HWs7 _ SUB7 (POSTM_trans _ _ _ _ _ _ PM7 PMs7) RM7 LDEL7 G10
            Lsel_a7 Fsel F0sel RRsel Larr_a7 Farr F0arr RRarr Lrow0_a7 Frow0 F0row0 RRrow0 Lrow1_a7 Frow1 F0row1 RRrow1 Lrow2_a7 Frow2 F0row2 RRrow2 Lrow3_a7 Frow3 F0row3 RRrow3 Lrow4_a7 Frow4 F0row4 RRrow4
            NE_sel_arr NE_sel_row0 NE_arr_row0 NE_sel_row1 NE_arr_row1 NE_row0_row1 NE_sel_row2 NE_arr_row2 NE_row0_row2 NE_row1_row2 NE_sel_row3 NE_arr_row3 NE_row0_row3 NE_row1_row3 NE_row2_row3 NE_sel_row4 NE_arr_row4 NE_row0_row4 NE_row1_row4 NE_row2_row4 NE_row3_row4
            Csel_0 Csel_4 Csel_8 Csel_12 Csel_16 Csel_24 Carr_0 Carr_8 Carr_16 Carr_24 Carr_32 Crow0_0 Crow0_4 Crow0_8 Crow0_12 Crow0_16 Crow0_20 Crow1_0 Crow1_4 Crow1_8 Crow1_12 Crow1_16 Crow1_20 Crow2_0 Crow2_4 Crow2_8 Crow2_12 Crow2_16 Crow2_20 Crow3_0 Crow3_4 Crow3_8 Crow3_12 Crow3_16 Crow3_20 Crow4_0 Crow4_4 Crow4_8 Crow4_12 Crow4_16 Crow4_20).
  lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 RcF [(2%nat, EVar 32); (4%nat, ELit 1278416)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor; [symmetry; exact HTP | constructor]] | vm_compute; reflexivity] end.
Qed.
End Chain.
