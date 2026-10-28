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
Import V15CL7a.V15LeptQFill.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Parse.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
(* [comment removed for export] *)
#[local] Existing Instance exf_fxd | 100.


Definition PARSE_WIN : Z := 12288.
Definition STOPS : list Z := [166172; 166484; 93000; QFA_HEAD; QFB_HEAD]%Z.
Definition FDEF : list (nat * nat) := [(8%nat, 33%nat)].   (* [comment removed for export] *)

Lemma thr_chain : forall (fx : FPState) C A m md regs (s pixs w h : Z) (S : TSet),
  Cok C -> W C A m md -> frm_zero (@fp_csr fx) ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + PARSE_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 4 = Z_to_bv 64 284096 -> getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 66371 ->
  getr regs 12 = Z_to_bv 64 8 -> getr regs 13 = Z_to_bv 64 0 -> getr regs 14 = Z_to_bv 64 0 -> getr regs 15 = Z_to_bv 64 0 ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> (0 <= pixs < 2 ^ 64)%Z -> (pixs <> 0)%Z -> (pixs mod 16 = 0)%Z -> (0 <= w < 2 ^ 31)%Z -> (0 <= h < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (pixs + 0)) 4 = Some (Z_to_le_bytes 4 w) -> rdn SEGS m (Z_to_bv 64 (pixs + 4)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 8)) 4 = Some (Z_to_le_bytes 4 8) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (10 <= kR)%Z -> (10 * 2 ^ 17 <= bR)%Z ->
  (forall (fx' : FPState) A' m' vm' regs' (qtab cmap cmaparr : Z),
      frm_zero (@fp_csr fx') -> W C A' m' (with_vmmaps vm' md) -> sub_live A A' -> POSTM C A s m m' ->
      aroom A' vm' (kR - 10) (bR - 10 * 2 ^ 17) ->
      (forall q : word, ~ In q [Z_to_bv 64 qtab; Z_to_bv 64 cmaparr; Z_to_bv 64 cmap] -> live A' q = live A q) ->
      live A' (Z_to_bv 64 qtab) = Some 1024%Z -> live A (Z_to_bv 64 qtab) = None -> live (c_A0 C) (Z_to_bv 64 qtab) = None -> (0 <= qtab < 2 ^ 64)%Z ->
      Z_to_bv 64 cmaparr <> Z_to_bv 64 qtab ->
      live A' (Z_to_bv 64 cmap) = Some 24%Z -> live A (Z_to_bv 64 cmap) = None -> live (c_A0 C) (Z_to_bv 64 cmap) = None -> (0 <= cmap < 2 ^ 64)%Z ->
      live A' (Z_to_bv 64 cmaparr) = Some 1024%Z -> live A (Z_to_bv 64 cmaparr) = None -> live (c_A0 C) (Z_to_bv 64 cmaparr) = None -> (0 <= cmaparr < 2 ^ 64)%Z ->
      rdn SEGS m' (Z_to_bv 64 (cmap + 0)) 8 = Some (Z_to_le_bytes 8 cmaparr) -> rdn SEGS m' (Z_to_bv 64 (cmap + 8)) 4 = Some (Z_to_le_bytes 4 8) ->
      rdn SEGS m' (Z_to_bv 64 (cmap + 12)) 4 = Some (Z_to_le_bytes 4 256) -> rdn SEGS m' (Z_to_bv 64 (cmap + 16)) 4 = Some (Z_to_le_bytes 4 5) ->
      rdn SEGS m' (Z_to_bv 64 (cmap + 20)) 4 = Some (Z_to_le_bytes 4 0) ->
      getr regs' 1 = Z_to_bv 64 121728 -> getr regs' 2 = Z_to_bv 64 (s + -208) -> getr regs' 3 = getr regs 3 -> getr regs' 4 = Z_to_bv 64 284096 ->
      getr regs' 8 = Z_to_bv 64 8 -> getr regs' 9 = Z_to_bv 64 pixs -> getr regs' 10 = Z_to_bv 64 w -> getr regs' 11 = Z_to_bv 64 h -> getr regs' 12 = Z_to_bv 64 8 ->
      rdn SEGS m' (Z_to_bv 64 (s + -8)) 8 = Some (word_to_le_bytes 8 (getr regs 1)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -32)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -40)) 8 = Some (word_to_le_bytes 8 (getr regs 19)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -48)) 8 = Some (word_to_le_bytes 8 (getr regs 20)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -56)) 8 = Some (word_to_le_bytes 8 (getr regs 21)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -64)) 8 = Some (word_to_le_bytes 8 (getr regs 22)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -72)) 8 = Some (word_to_le_bytes 8 (getr regs 23)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -80)) 8 = Some (word_to_le_bytes 8 (getr regs 24)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -88)) 8 = Some (word_to_le_bytes 8 (getr regs 25)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -96)) 8 = Some (word_to_le_bytes 8 (getr regs 26)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -104)) 8 = Some (word_to_le_bytes 8 (getr regs 27)) ->
      rdn SEGS m' (Z_to_bv 64 (s + -160)) 8 = Some (Z_to_le_bytes 8 cmap) ->
      rdn SEGS m' (Z_to_bv 64 (s + -128)) 4 = Some (Z_to_le_bytes 4 h) ->
      rdn SEGS m' (Z_to_bv 64 (s + -124)) 4 = Some (Z_to_le_bytes 4 w) ->
      rdn SEGS m' (Z_to_bv 64 (s + -120)) 8 = Some (Z_to_le_bytes 8 qtab) ->
      realizes SEGS (mkCfg (@mkst fx' regs' (Z_to_bv 64 93000) m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 119812) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 s pixs w h S CK HW0 FZ H2 Hs16 Hlo Hhi H4 H10 H11 H12 H13 H14 H15 Lpixs_a0 Rpixs NZpixs ALpixs Rw Rh Cw Ch Cd kR bR RM0 HkR HbR HC.
  destruct fx as [fr cs]. cbn [fp_csr] in FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. unfold PARSE_WIN in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  replace kR with (kR - 0)%Z in RM0 by lia. replace bR with (bR - 0 * 2 ^ 17)%Z in RM0 by lia.
  pose (valsI := @nil word).
  pose proof (fun (q : word) (_ : ~ In q []) => eq_refl (live A0 q)) as LDEL0.
  assert (GLO1 : (c_top C - LSTK <= s - 12288)%Z) by lia.
  assert (GLO2 : (s - 12288 + Z.of_nat (Z.to_nat 12288) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (12288 <= s)%Z) by lia.
  pose proof Rpixs as RRpixs.
  pose proof (exW_win_blk_apart_h C A0 m0 _ s 12288 pixs 64 CK HW0 Lpixs_a0 ltac:(lia) Rpixs ltac:(lia)) as WAPpixs.
  assert (Rpixs2 : (4096 <= pixs)%Z /\ (pixs + 64 <= alloc_top (c_vm C))%Z).
  { destruct (blk_range C A0 m0 _ (Z_to_bv 64 pixs) 64 CK HW0 Lpixs_a0 ltac:(lia)) as [G1 G2]. rewrite u_Z2bv in G1, G2 by lia. split; [exact G1 | lia]. }
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 12288) (Z.to_nat 12288) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; exW_canary SEGS 415784 m0]) (EVar 37) (EVar 32) (exW_canary SEGS 415784 m0) s 12288 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 442368 (2 ^ 63); KAlign (EVar 32) 16; KRange (EVar 34) 1 (2 ^ 47); KAlign (EVar 34) 16; KDisj (SA (EVar 32) (-12288)) 12288 (SA (EVar 34) 0) 64; KWord (SA (EVar 34) 0) 4 (EVar 35); KWord (SA (EVar 34) 4) 4 (EVar 36); KWord (SA (EVar 34) 8) 4 (ELit 8); KRange (EVar 35) 0 (2 ^ 31 - 1); KRange (EVar 36) 0 (2 ^ 31 - 1)]).
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
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 12288 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r1 Q1_0. exW_regfactB BS0 HR ex_r2 Q2_0. exW_regfactB BS0 HR ex_r4 Q4_0.
  clear BS0.
  lazymatch type of Q2_0 with _ = Z_to_bv 64 (s + ?off) => pose (OFF0 := off) end.
  (* [comment removed for export] *)
  pose proof (alloc_margin_small (14 * 1) ltac:(exW_cmp)) as MG0.
  lazymatch type of Q1_0 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_0 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A0 M0 _ Rc0 14 1 (kR - 0) (bR - 0 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs0 Q10_0 Q11_0 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM0) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_0
             ltac:(red; apply bv_eq; reflexivity) Q4_0 Q2_0 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A1 m1 vm1 r1 res0 HW1 Hres0 CSx0 Hnz0 Fnewstrx Lo0 F0newstr LEQ0 ZERO0 ALnewstr TOP0 PMc0 RM1.
  pose proof CSx0 as CS0. clear CSx0.
  rewrite with_vmmaps_twice in HW1 |- *.
  assert (Eres0 : res0 = Z_to_bv 64 (u res0)) by (symmetry; apply zbv_self).
  pose proof (u64_range res0) as RRnewstr. set (newstr := u res0) in *. clearbody newstr. rewrite Eres0 in Hres0, Fnewstrx, Lo0, F0newstr, LEQ0, ZERO0. clear Eres0.
  change (14 * 1)%Z with 14%Z in *.
  pose proof (exW_blk_img_apart_h2 C A1 m1 _ newstr 14 CK HW1 Lo0 RRnewstr eq_refl eq_refl) as IMGAPnewstr. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPnewstr.
  pose proof (exW_win_blk_apart_h C A1 m1 _ s 12288 newstr 14 CK HW1 Lo0 eq_refl RRnewstr GLO1) as WAPnewstr.
  assert (Fnewstr : live A0 (Z_to_bv 64 newstr) = None).
  { destruct (live A0 (Z_to_bv 64 newstr)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB0 _ _ EE) as XX. first [discriminate Fnewstrx | (rewrite Fnewstrx in XX; discriminate XX)]. }
  pose proof Lo0 as Lnewstr_a1.
  assert (SUB1 : sub_live A0 A1).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 newstr) by (intros ->; rewrite Fnewstr in Lq; discriminate Lq). rewrite (LEQ0 q NEq). exact (SUB0 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 newstr :: [])) => eq_trans (LEQ0 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL0 q (fun XX => Hq (or_intror XX)))) as LDEL1.
  assert (NE_pixs_newstr : Z_to_bv 64 pixs <> Z_to_bv 64 newstr) by (intros EE; rewrite EE in Lpixs_a0; rewrite Fnewstrx in Lpixs_a0; discriminate Lpixs_a0).
  assert (Lpixs_a1 : live A1 (Z_to_bv 64 pixs) = Some 64%Z) by (rewrite (LEQ0 _ NE_pixs_newstr); exact Lpixs_a0).
  pose proof (exW_blk_apart_h C A1 m1 _ pixs newstr 64 14 CK HW1 Lpixs_a1 Lnewstr_a1 NE_pixs_newstr RRpixs RRnewstr ltac:(exW_cmp) ltac:(exW_cmp)) as AP_pixs_newstr.
  assert (PM1 : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|]. apply (POSTM_sub C A0 A0 _ _ _ SUB0).
    apply (POSTM_mono C A0 (s + OFF0) s); [unfold OFF0; lia | exact PMc0]. }
  replace (kR - 0 - 1)%Z with (kR - 1)%Z in RM1 by lia. rewrite MG0 in RM1. replace (bR - 0 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 1 * 2 ^ 17)%Z in RM1 by lia.
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, OFF0, 0%Z); (EVar 34, 0%Z, 64%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF0 12288 M0 m1 E0 (EVar 32) CK (proj1 PMc0) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A0 A0 M0 _ M0 m1 E0 (EVar 34) pixs 64 CK HWs0 Lpixs_a0 RRpixs eq_refl (proj2 PMc0) Lpixs_a0 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E0 m1 kk') in HKk0 end.
  pose proof (regs_ok_agree 38%nat E0 (ex_envL vals0 r1 [newstr; exW_canary SEGS 415784 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [newstr; exW_canary SEGS 415784 m1] 38%nat ltac:(vm_cast_no_check (eq_refl 38%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [newstr; exW_canary SEGS 415784 m1]) m1 _) by (exact (know_ok_agree SEGS 38%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  rewrite (fr_denot_agree 38%nat E0 (ex_envL vals0 r1 [newstr; exW_canary SEGS 415784 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r1 ex_r10 (EVar 70) HRn1 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres0)) as HRx1. clear HRn1. rename HRx1 into HRn1.
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q11_0 Q1_0 Q2_0 Q4_0 PM0 HW0 PMc0 CS0 SUB0 RM0 MG0 TOP0 LEQ0 Hnz0 Fnewstrx Lo0 OFF0 LDEL0 Lpixs_a0.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  pose proof (exW_kn_blk SEGS C A1 m1 _ (ex_envL vals0 r1 [newstr; exW_canary SEGS 415784 m1]) (EVar 70) (EVar 32) newstr 14 s 12288 65536 356352 p16_segs CK HW1 Lnewstr_a1 RRnewstr eq_refl eq_refl eq_refl RS ALnewstr ZERO0 WAPnewstr IMGAPnewstr) as HKb1.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals0 r1 [newstr; exW_canary SEGS 415784 m1]) m1) _ _ (ex_kdisj_apart SEGS (ex_envL vals0 r1 [newstr; exW_canary SEGS 415784 m1]) m1 (EVar 34) (EVar 70) pixs newstr 0 64 0 14 eq_refl eq_refl RRpixs RRnewstr AP_pixs_newstr) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals0 r1 [newstr; exW_canary SEGS 415784 m1]) m1))) as HKd1.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m1 _ (s - 12288) (Z.to_nat 12288) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 415784 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [newstr; exW_canary SEGS 415784 m1]).
  pose proof (exW_kn_fixed SEGS C A1 m1 _ (ex_envL vals0 r1 [newstr; exW_canary SEGS 415784 m1]) (EVar 71) (EVar 32) (exW_canary SEGS 415784 m1) s 12288 415784 65536 212992 213416 213568 213416 213568
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb1 (proj2 (Forall_app _ _ _) (conj HKd1 (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb1 HKd1 HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO0 ALnewstr.
  (* [comment removed for export] *)
  exb_exit ST Rc1 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A1 M1 (with_vmmaps vm1 md) /\ POSTM C A0 s m1 M1).
  { subst M1. apply (exW_win_blks C A1 A0 m1 _ E1 log1 (EVar 32) s 12288 [(EVar 70, newstr, 14%Z)] CK HW1 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRnewstr (conj Lnewstr_a1 (conj Fnewstr F0newstr))))|]. constructor. }
  destruct WP1 as [HWs1 PMs1].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log1 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC1 : carry log1 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc1 : know_ok SEGS E1 M1 kn1) by (apply (carry_after SEGS E1 m1 log1 kn0 [] kn1 scs hs HC1 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose (BS1 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, newstr)]).
  exW_regfactB BS1 HR ex_r10 Q10_1. exW_regfactB BS1 HR ex_r11 Q11_1. exW_regfactB BS1 HR ex_r1 Q1_1. exW_regfactB BS1 HR ex_r2 Q2_1. exW_regfactB BS1 HR ex_r4 Q4_1.
  clear BS1.
  lazymatch type of Q2_1 with _ = Z_to_bv 64 (s + ?off) => pose (OFF1 := off) end.
  (* [comment removed for export] *)
  pose proof (alloc_margin_small (1 * 32) ltac:(exW_cmp)) as MG1.
  lazymatch type of Q1_1 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_1 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A1 M1 _ Rc1 1 32 (kR - 1) (bR - 1 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs1 Q10_1 Q11_1 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM1) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_1
             ltac:(red; apply bv_eq; reflexivity) Q4_1 Q2_1 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A2 m2 vm2 r2 res1 HW2 Hres1 CSx1 Hnz1 Fnax Lo1 F0na LEQ1 ZERO1 ALna TOP1 PMc1 RM2.
  pose proof CSx1 as CS1. clear CSx1.
  rewrite with_vmmaps_twice in HW2 |- *.
  assert (Eres1 : res1 = Z_to_bv 64 (u res1)) by (symmetry; apply zbv_self).
  pose proof (u64_range res1) as RRna. set (na := u res1) in *. clearbody na. rewrite Eres1 in Hres1, Fnax, Lo1, F0na, LEQ1, ZERO1. clear Eres1.
  change (1 * 32)%Z with 32%Z in *.
  pose proof (exW_blk_img_apart_h2 C A2 m2 _ na 32 CK HW2 Lo1 RRna eq_refl eq_refl) as IMGAPna. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPna.
  pose proof (exW_win_blk_apart_h C A2 m2 _ s 12288 na 32 CK HW2 Lo1 eq_refl RRna GLO1) as WAPna.
  assert (Fna : live A0 (Z_to_bv 64 na) = None).
  { destruct (live A0 (Z_to_bv 64 na)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB1 _ _ EE) as XX. first [discriminate Fnax | (rewrite Fnax in XX; discriminate XX)]. }
  pose proof Lo1 as Lna_a2.
  assert (SUB2 : sub_live A0 A2).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 na) by (intros ->; rewrite Fna in Lq; discriminate Lq). rewrite (LEQ1 q NEq). exact (SUB1 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 na :: [Z_to_bv 64 newstr])) => eq_trans (LEQ1 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL1 q (fun XX => Hq (or_intror XX)))) as LDEL2.
  assert (NE_pixs_na : Z_to_bv 64 pixs <> Z_to_bv 64 na) by (intros EE; rewrite EE in Lpixs_a1; rewrite Fnax in Lpixs_a1; discriminate Lpixs_a1).
  assert (Lpixs_a2 : live A2 (Z_to_bv 64 pixs) = Some 64%Z) by (rewrite (LEQ1 _ NE_pixs_na); exact Lpixs_a1).
  pose proof (exW_blk_apart_h C A2 m2 _ pixs na 64 32 CK HW2 Lpixs_a2 Lna_a2 NE_pixs_na RRpixs RRna ltac:(exW_cmp) ltac:(exW_cmp)) as AP_pixs_na.
  assert (NE_newstr_na : Z_to_bv 64 newstr <> Z_to_bv 64 na) by (intros EE; rewrite EE in Lnewstr_a1; rewrite Fnax in Lnewstr_a1; discriminate Lnewstr_a1).
  assert (Lnewstr_a2 : live A2 (Z_to_bv 64 newstr) = Some 14%Z) by (rewrite (LEQ1 _ NE_newstr_na); exact Lnewstr_a1).
  pose proof (exW_blk_apart_h C A2 m2 _ newstr na 14 32 CK HW2 Lnewstr_a2 Lna_a2 NE_newstr_na RRnewstr RRna ltac:(exW_cmp) ltac:(exW_cmp)) as AP_newstr_na.
  assert (PM2 : POSTM C A0 s m0 m2).
  { eapply POSTM_trans; [exact PM1|]. eapply POSTM_trans; [exact PMs1|]. apply (POSTM_sub C A0 A1 _ _ _ SUB1).
    apply (POSTM_mono C A1 (s + OFF1) s); [unfold OFF1; lia | exact PMc1]. }
  replace (kR - 1 - 1)%Z with (kR - 2)%Z in RM2 by lia. rewrite MG1 in RM2. replace (bR - 1 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 2 * 2 ^ 17)%Z in RM2 by lia.
  assert (KEPT1 : Forall (ex_region_kept E1 M1 m2) [(EVar 32, OFF1, 0%Z); (EVar 34, 0%Z, 64%Z); (EVar 70, 0%Z, 14%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF1 12288 M1 m2 E1 (EVar 32) CK (proj1 PMc1) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A1 A1 M1 _ M1 m2 E1 (EVar 34) pixs 64 CK HWs1 Lpixs_a1 RRpixs eq_refl (proj2 PMc1) Lpixs_a1 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A1 A1 M1 _ M1 m2 E1 (EVar 70) newstr 14 CK HWs1 Lnewstr_a1 RRnewstr eq_refl (proj2 PMc1) Lnewstr_a1 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E1 M1 m2 _ [] _ HKc1 KEPT1) as HKk1.
  match type of HKk1 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E1 m2 kk') in HKk1 end.
  pose proof (regs_ok_agree 72%nat E1 (ex_envL vals1 r2 [na; exW_canary SEGS 415784 m2]) _ _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa1.
  pose proof (exW_regs_call _ _ _ _ _ HRa1 (ex_regs_ok_junk vals1 r2 [na; exW_canary SEGS 415784 m2] 72%nat ltac:(vm_cast_no_check (eq_refl 72%nat))) CS1) as HRn2.
  clear HRa1.
  assert (HKa2 : know_ok SEGS (ex_envL vals1 r2 [na; exW_canary SEGS 415784 m2]) m2 _) by (exact (know_ok_agree SEGS 72%nat E1 _ m2 _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk1)).
  rewrite (fr_denot_agree 72%nat E1 (ex_envL vals1 r2 [na; exW_canary SEGS 415784 m2]) _ fr (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r2 ex_r10 (EVar 104) HRn2 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres1)) as HRx2. clear HRn2. rename HRx2 into HRn2.
  clear HR HK Hlf Hms HKc1 HKk1 KEPT1 HC1 HWs1 PMs1 Q10_1 Q11_1 Q1_1 Q2_1 Q4_1 PM1 HW1 PMc1 CS1 SUB1 RM1 MG1 TOP1 LEQ1 Hnz1 Fnax Lo1 OFF1 LDEL1 Lpixs_a1 Lnewstr_a1.
  subst M1. clear log1. clear E1. try clear Rc1. clear KN1.
  lazymatch type of HRn2 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn2 end.
  pose proof (exW_kn_blk SEGS C A2 m2 _ (ex_envL vals1 r2 [na; exW_canary SEGS 415784 m2]) (EVar 104) (EVar 32) na 32 s 12288 65536 356352 p16_segs CK HW2 Lna_a2 RRna eq_refl eq_refl eq_refl RS ALna ZERO1 WAPna IMGAPna) as HKb2.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals1 r2 [na; exW_canary SEGS 415784 m2]) m2) _ _ (ex_kdisj_apart SEGS (ex_envL vals1 r2 [na; exW_canary SEGS 415784 m2]) m2 (EVar 34) (EVar 104) pixs na 0 64 0 32 eq_refl eq_refl RRpixs RRna AP_pixs_na) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals1 r2 [na; exW_canary SEGS 415784 m2]) m2) _ _ (ex_kdisj_apart SEGS (ex_envL vals1 r2 [na; exW_canary SEGS 415784 m2]) m2 (EVar 70) (EVar 104) newstr na 0 14 0 32 eq_refl eq_refl RRnewstr RRna AP_newstr_na) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals1 r2 [na; exW_canary SEGS 415784 m2]) m2)))) as HKd2.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A2 m2 _ (s - 12288) (Z.to_nat 12288) CK HW2 GLO1 GLO2) as SOK2.
  pose proof (exW_canary_ok SEGS 415784 m2 (canary_any m2)) as CANOK2.
  pose (vals2 := vals1 ++ map (getr r2) ex_regs_list ++ map (Z_to_bv 64) [na; exW_canary SEGS 415784 m2]).
  pose proof (exW_kn_fixed SEGS C A2 m2 _ (ex_envL vals1 r2 [na; exW_canary SEGS 415784 m2]) (EVar 105) (EVar 32) (exW_canary SEGS 415784 m2) s 12288 415784 65536 212992 213416 213568 213416 213568
                HW2 eq_refl (proj1 CANOK2) (proj2 CANOK2) eq_refl eq_refl eq_refl SOK2 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf2.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb2 (proj2 (Forall_app _ _ _) (conj HKd2 (proj2 (Forall_app _ _ _) (conj HKf2 HKa2)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn2 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN2 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb2 HKd2 HKf2 HKa2 SOK2 CANOK2.
  repeat match goal with H : getr r2 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO1 ALna.
  (* [comment removed for export] *)
  exb_exit ST Rc2 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E2 := EEx) in HR, Hlf, HK, Hms |- *; set (log2 := LLx) in Hms, Hlf; set (M2 := mem_denot E2 m2 log2) in Hms end.
  assert (WP2 : W C A2 M2 (with_vmmaps vm2 md) /\ POSTM C A0 s m2 M2).
  { subst M2. apply (exW_win_blks C A2 A0 m2 _ E2 log2 (EVar 32) s 12288 [(EVar 70, newstr, 14%Z); (EVar 104, na, 32%Z)] CK HW2 SUB2 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRnewstr (conj Lnewstr_a2 (conj Fnewstr F0newstr))))|]. constructor; [exact (conj eq_refl (conj RRna (conj Lna_a2 (conj Fna F0na))))|]. constructor. }
  destruct WP2 as [HWs2 PMs2].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log2 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC2 : carry log2 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc2 : know_ok SEGS E2 M2 kn1) by (apply (carry_after SEGS E2 m2 log2 kn0 [] kn1 scs hs HC2 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact Hms |].
  pose (BS2 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, newstr); (104%nat, na)]).
  exW_regfactB BS2 HR ex_r10 Q10_2. exW_regfactB BS2 HR ex_r11 Q11_2. exW_regfactB BS2 HR ex_r1 Q1_2. exW_regfactB BS2 HR ex_r2 Q2_2. exW_regfactB BS2 HR ex_r4 Q4_2.
  clear BS2.
  lazymatch type of Q2_2 with _ = Z_to_bv 64 (s + ?off) => pose (OFF2 := off) end.
  (* [comment removed for export] *)
  pose proof (alloc_margin_small (50 * 4) ltac:(exW_cmp)) as MG2.
  lazymatch type of Q1_2 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_2 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A2 M2 _ Rc2 50 4 (kR - 2) (bR - 2 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs2 Q10_2 Q11_2 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM2) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_2
             ltac:(red; apply bv_eq; reflexivity) Q4_2 Q2_2 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A3 m3 vm3 r3 res2 HW3 Hres2 CSx2 Hnz2 Farrx Lo2 F0arr LEQ2 ZERO2 ALarr TOP2 PMc2 RM3.
  pose proof CSx2 as CS2. clear CSx2.
  rewrite with_vmmaps_twice in HW3 |- *.
  assert (Eres2 : res2 = Z_to_bv 64 (u res2)) by (symmetry; apply zbv_self).
  pose proof (u64_range res2) as RRarr. set (arr := u res2) in *. clearbody arr. rewrite Eres2 in Hres2, Farrx, Lo2, F0arr, LEQ2, ZERO2. clear Eres2.
  change (50 * 4)%Z with 200%Z in *.
  pose proof (exW_blk_img_apart_h2 C A3 m3 _ arr 200 CK HW3 Lo2 RRarr eq_refl eq_refl) as IMGAParr. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAParr.
  pose proof (exW_win_blk_apart_h C A3 m3 _ s 12288 arr 200 CK HW3 Lo2 eq_refl RRarr GLO1) as WAParr.
  assert (Farr : live A0 (Z_to_bv 64 arr) = None).
  { destruct (live A0 (Z_to_bv 64 arr)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB2 _ _ EE) as XX. first [discriminate Farrx | (rewrite Farrx in XX; discriminate XX)]. }
  pose proof Lo2 as Larr_a3.
  assert (SUB3 : sub_live A0 A3).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 arr) by (intros ->; rewrite Farr in Lq; discriminate Lq). rewrite (LEQ2 q NEq). exact (SUB2 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 arr :: [Z_to_bv 64 na; Z_to_bv 64 newstr])) => eq_trans (LEQ2 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL2 q (fun XX => Hq (or_intror XX)))) as LDEL3.
  assert (NE_pixs_arr : Z_to_bv 64 pixs <> Z_to_bv 64 arr) by (intros EE; rewrite EE in Lpixs_a2; rewrite Farrx in Lpixs_a2; discriminate Lpixs_a2).
  assert (Lpixs_a3 : live A3 (Z_to_bv 64 pixs) = Some 64%Z) by (rewrite (LEQ2 _ NE_pixs_arr); exact Lpixs_a2).
  pose proof (exW_blk_apart_h C A3 m3 _ pixs arr 64 200 CK HW3 Lpixs_a3 Larr_a3 NE_pixs_arr RRpixs RRarr ltac:(exW_cmp) ltac:(exW_cmp)) as AP_pixs_arr.
  assert (NE_newstr_arr : Z_to_bv 64 newstr <> Z_to_bv 64 arr) by (intros EE; rewrite EE in Lnewstr_a2; rewrite Farrx in Lnewstr_a2; discriminate Lnewstr_a2).
  assert (Lnewstr_a3 : live A3 (Z_to_bv 64 newstr) = Some 14%Z) by (rewrite (LEQ2 _ NE_newstr_arr); exact Lnewstr_a2).
  pose proof (exW_blk_apart_h C A3 m3 _ newstr arr 14 200 CK HW3 Lnewstr_a3 Larr_a3 NE_newstr_arr RRnewstr RRarr ltac:(exW_cmp) ltac:(exW_cmp)) as AP_newstr_arr.
  assert (NE_na_arr : Z_to_bv 64 na <> Z_to_bv 64 arr) by (intros EE; rewrite EE in Lna_a2; rewrite Farrx in Lna_a2; discriminate Lna_a2).
  assert (Lna_a3 : live A3 (Z_to_bv 64 na) = Some 32%Z) by (rewrite (LEQ2 _ NE_na_arr); exact Lna_a2).
  pose proof (exW_blk_apart_h C A3 m3 _ na arr 32 200 CK HW3 Lna_a3 Larr_a3 NE_na_arr RRna RRarr ltac:(exW_cmp) ltac:(exW_cmp)) as AP_na_arr.
  assert (PM3 : POSTM C A0 s m0 m3).
  { eapply POSTM_trans; [exact PM2|]. eapply POSTM_trans; [exact PMs2|]. apply (POSTM_sub C A0 A2 _ _ _ SUB2).
    apply (POSTM_mono C A2 (s + OFF2) s); [unfold OFF2; lia | exact PMc2]. }
  replace (kR - 2 - 1)%Z with (kR - 3)%Z in RM3 by lia. rewrite MG2 in RM3. replace (bR - 2 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 3 * 2 ^ 17)%Z in RM3 by lia.
  assert (KEPT2 : Forall (ex_region_kept E2 M2 m3) [(EVar 32, OFF2, 0%Z); (EVar 34, 0%Z, 64%Z); (EVar 70, 0%Z, 14%Z); (EVar 104, 0%Z, 32%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF2 12288 M2 m3 E2 (EVar 32) CK (proj1 PMc2) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A2 A2 M2 _ M2 m3 E2 (EVar 34) pixs 64 CK HWs2 Lpixs_a2 RRpixs eq_refl (proj2 PMc2) Lpixs_a2 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A2 A2 M2 _ M2 m3 E2 (EVar 70) newstr 14 CK HWs2 Lnewstr_a2 RRnewstr eq_refl (proj2 PMc2) Lnewstr_a2 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A2 A2 M2 _ M2 m3 E2 (EVar 104) na 32 CK HWs2 Lna_a2 RRna eq_refl (proj2 PMc2) Lna_a2 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E2 M2 m3 _ [] _ HKc2 KEPT2) as HKk2.
  match type of HKk2 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E2 m3 kk') in HKk2 end.
  pose proof (regs_ok_agree 106%nat E2 (ex_envL vals2 r3 [arr; exW_canary SEGS 415784 m3]) _ _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa2.
  pose proof (exW_regs_call _ _ _ _ _ HRa2 (ex_regs_ok_junk vals2 r3 [arr; exW_canary SEGS 415784 m3] 106%nat ltac:(vm_cast_no_check (eq_refl 106%nat))) CS2) as HRn3.
  clear HRa2.
  assert (HKa3 : know_ok SEGS (ex_envL vals2 r3 [arr; exW_canary SEGS 415784 m3]) m3 _) by (exact (know_ok_agree SEGS 106%nat E2 _ m3 _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk2)).
  rewrite (fr_denot_agree 106%nat E2 (ex_envL vals2 r3 [arr; exW_canary SEGS 415784 m3]) _ fr (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r3 ex_r10 (EVar 138) HRn3 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres2)) as HRx3. clear HRn3. rename HRx3 into HRn3.
  clear HR HK Hlf Hms HKc2 HKk2 KEPT2 HC2 HWs2 PMs2 Q10_2 Q11_2 Q1_2 Q2_2 Q4_2 PM2 HW2 PMc2 CS2 SUB2 RM2 MG2 TOP2 LEQ2 Hnz2 Farrx Lo2 OFF2 LDEL2 Lpixs_a2 Lnewstr_a2 Lna_a2.
  subst M2. clear log2. clear E2. try clear Rc2. clear KN2.
  lazymatch type of HRn3 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn3 end.
  pose proof (exW_kn_blk SEGS C A3 m3 _ (ex_envL vals2 r3 [arr; exW_canary SEGS 415784 m3]) (EVar 138) (EVar 32) arr 200 s 12288 65536 356352 p16_segs CK HW3 Larr_a3 RRarr eq_refl eq_refl eq_refl RS ALarr ZERO2 WAParr IMGAParr) as HKb3.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals2 r3 [arr; exW_canary SEGS 415784 m3]) m3) _ _ (ex_kdisj_apart SEGS (ex_envL vals2 r3 [arr; exW_canary SEGS 415784 m3]) m3 (EVar 34) (EVar 138) pixs arr 0 64 0 200 eq_refl eq_refl RRpixs RRarr AP_pixs_arr) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals2 r3 [arr; exW_canary SEGS 415784 m3]) m3) _ _ (ex_kdisj_apart SEGS (ex_envL vals2 r3 [arr; exW_canary SEGS 415784 m3]) m3 (EVar 70) (EVar 138) newstr arr 0 14 0 200 eq_refl eq_refl RRnewstr RRarr AP_newstr_arr) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals2 r3 [arr; exW_canary SEGS 415784 m3]) m3) _ _ (ex_kdisj_apart SEGS (ex_envL vals2 r3 [arr; exW_canary SEGS 415784 m3]) m3 (EVar 104) (EVar 138) na arr 0 32 0 200 eq_refl eq_refl RRna RRarr AP_na_arr) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals2 r3 [arr; exW_canary SEGS 415784 m3]) m3))))) as HKd3.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A3 m3 _ (s - 12288) (Z.to_nat 12288) CK HW3 GLO1 GLO2) as SOK3.
  pose proof (exW_canary_ok SEGS 415784 m3 (canary_any m3)) as CANOK3.
  pose (vals3 := vals2 ++ map (getr r3) ex_regs_list ++ map (Z_to_bv 64) [arr; exW_canary SEGS 415784 m3]).
  pose proof (exW_kn_fixed SEGS C A3 m3 _ (ex_envL vals2 r3 [arr; exW_canary SEGS 415784 m3]) (EVar 139) (EVar 32) (exW_canary SEGS 415784 m3) s 12288 415784 65536 212992 213416 213568 213416 213568
                HW3 eq_refl (proj1 CANOK3) (proj2 CANOK3) eq_refl eq_refl eq_refl SOK3 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf3.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb3 (proj2 (Forall_app _ _ _) (conj HKd3 (proj2 (Forall_app _ _ _) (conj HKf3 HKa3)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn3 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN3 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb3 HKd3 HKf3 HKa3 SOK3 CANOK3.
  repeat match goal with H : getr r3 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO2 ALarr.
  (* [comment removed for export] *)
  exb_exit ST Rc3 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E3 := EEx) in HR, Hlf, HK, Hms |- *; set (log3 := LLx) in Hms, Hlf; set (M3 := mem_denot E3 m3 log3) in Hms end.
  assert (WP3 : W C A3 M3 (with_vmmaps vm3 md) /\ POSTM C A0 s m3 M3).
  { subst M3. apply (exW_win_blks C A3 A0 m3 _ E3 log3 (EVar 32) s 12288 [(EVar 70, newstr, 14%Z); (EVar 104, na, 32%Z); (EVar 138, arr, 200%Z)] CK HW3 SUB3 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRnewstr (conj Lnewstr_a3 (conj Fnewstr F0newstr))))|]. constructor; [exact (conj eq_refl (conj RRna (conj Lna_a3 (conj Fna F0na))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a3 (conj Farr F0arr))))|]. constructor. }
  destruct WP3 as [HWs3 PMs3].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log3 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC3 : carry log3 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc3 : know_ok SEGS E3 M3 kn1) by (apply (carry_after SEGS E3 m3 log3 kn0 [] kn1 scs hs HC3 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact Hms |].
  pose (BS3 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, newstr); (104%nat, na); (138%nat, arr)]).
  exW_regfactB BS3 HR ex_r10 Q10_3. exW_regfactB BS3 HR ex_r11 Q11_3. exW_regfactB BS3 HR ex_r1 Q1_3. exW_regfactB BS3 HR ex_r2 Q2_3. exW_regfactB BS3 HR ex_r4 Q4_3.
  clear BS3.
  lazymatch type of Q2_3 with _ = Z_to_bv 64 (s + ?off) => pose (OFF3 := off) end.
  (* [comment removed for export] *)
  pose proof (alloc_margin_small (3 * 1) ltac:(exW_cmp)) as MG3.
  lazymatch type of Q1_3 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_3 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A3 M3 _ Rc3 3 1 (kR - 3) (bR - 3 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs3 Q10_3 Q11_3 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM3) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_3
             ltac:(red; apply bv_eq; reflexivity) Q4_3 Q2_3 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A4 m4 vm4 r4 res3 HW4 Hres3 CSx3 Hnz3 Ftok1x Lo3 F0tok1 LEQ3 ZERO3 ALtok1 TOP3 PMc3 RM4.
  pose proof CSx3 as CS3. clear CSx3.
  rewrite with_vmmaps_twice in HW4 |- *.
  assert (Eres3 : res3 = Z_to_bv 64 (u res3)) by (symmetry; apply zbv_self).
  pose proof (u64_range res3) as RRtok1. set (tok1 := u res3) in *. clearbody tok1. rewrite Eres3 in Hres3, Ftok1x, Lo3, F0tok1, LEQ3, ZERO3. clear Eres3.
  change (3 * 1)%Z with 3%Z in *.
  pose proof (exW_blk_img_apart_h2 C A4 m4 _ tok1 3 CK HW4 Lo3 RRtok1 eq_refl eq_refl) as IMGAPtok1. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPtok1.
  pose proof (exW_win_blk_apart_h C A4 m4 _ s 12288 tok1 3 CK HW4 Lo3 eq_refl RRtok1 GLO1) as WAPtok1.
  assert (Ftok1 : live A0 (Z_to_bv 64 tok1) = None).
  { destruct (live A0 (Z_to_bv 64 tok1)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB3 _ _ EE) as XX. first [discriminate Ftok1x | (rewrite Ftok1x in XX; discriminate XX)]. }
  pose proof Lo3 as Ltok1_a4.
  assert (SUB4 : sub_live A0 A4).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 tok1) by (intros ->; rewrite Ftok1 in Lq; discriminate Lq). rewrite (LEQ3 q NEq). exact (SUB3 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 tok1 :: [Z_to_bv 64 arr; Z_to_bv 64 na; Z_to_bv 64 newstr])) => eq_trans (LEQ3 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL3 q (fun XX => Hq (or_intror XX)))) as LDEL4.
  assert (NE_pixs_tok1 : Z_to_bv 64 pixs <> Z_to_bv 64 tok1) by (intros EE; rewrite EE in Lpixs_a3; rewrite Ftok1x in Lpixs_a3; discriminate Lpixs_a3).
  assert (Lpixs_a4 : live A4 (Z_to_bv 64 pixs) = Some 64%Z) by (rewrite (LEQ3 _ NE_pixs_tok1); exact Lpixs_a3).
  pose proof (exW_blk_apart_h C A4 m4 _ pixs tok1 64 3 CK HW4 Lpixs_a4 Ltok1_a4 NE_pixs_tok1 RRpixs RRtok1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_pixs_tok1.
  assert (NE_newstr_tok1 : Z_to_bv 64 newstr <> Z_to_bv 64 tok1) by (intros EE; rewrite EE in Lnewstr_a3; rewrite Ftok1x in Lnewstr_a3; discriminate Lnewstr_a3).
  assert (Lnewstr_a4 : live A4 (Z_to_bv 64 newstr) = Some 14%Z) by (rewrite (LEQ3 _ NE_newstr_tok1); exact Lnewstr_a3).
  pose proof (exW_blk_apart_h C A4 m4 _ newstr tok1 14 3 CK HW4 Lnewstr_a4 Ltok1_a4 NE_newstr_tok1 RRnewstr RRtok1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_newstr_tok1.
  assert (NE_na_tok1 : Z_to_bv 64 na <> Z_to_bv 64 tok1) by (intros EE; rewrite EE in Lna_a3; rewrite Ftok1x in Lna_a3; discriminate Lna_a3).
  assert (Lna_a4 : live A4 (Z_to_bv 64 na) = Some 32%Z) by (rewrite (LEQ3 _ NE_na_tok1); exact Lna_a3).
  pose proof (exW_blk_apart_h C A4 m4 _ na tok1 32 3 CK HW4 Lna_a4 Ltok1_a4 NE_na_tok1 RRna RRtok1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_na_tok1.
  assert (NE_arr_tok1 : Z_to_bv 64 arr <> Z_to_bv 64 tok1) by (intros EE; rewrite EE in Larr_a3; rewrite Ftok1x in Larr_a3; discriminate Larr_a3).
  assert (Larr_a4 : live A4 (Z_to_bv 64 arr) = Some 200%Z) by (rewrite (LEQ3 _ NE_arr_tok1); exact Larr_a3).
  pose proof (exW_blk_apart_h C A4 m4 _ arr tok1 200 3 CK HW4 Larr_a4 Ltok1_a4 NE_arr_tok1 RRarr RRtok1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_tok1.
  assert (PM4 : POSTM C A0 s m0 m4).
  { eapply POSTM_trans; [exact PM3|]. eapply POSTM_trans; [exact PMs3|]. apply (POSTM_sub C A0 A3 _ _ _ SUB3).
    apply (POSTM_mono C A3 (s + OFF3) s); [unfold OFF3; lia | exact PMc3]. }
  replace (kR - 3 - 1)%Z with (kR - 4)%Z in RM4 by lia. rewrite MG3 in RM4. replace (bR - 3 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 4 * 2 ^ 17)%Z in RM4 by lia.
  assert (KEPT3 : Forall (ex_region_kept E3 M3 m4) [(EVar 32, OFF3, 0%Z); (EVar 34, 0%Z, 64%Z); (EVar 70, 0%Z, 14%Z); (EVar 104, 0%Z, 32%Z); (EVar 138, 0%Z, 200%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF3 12288 M3 m4 E3 (EVar 32) CK (proj1 PMc3) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A3 A3 M3 _ M3 m4 E3 (EVar 34) pixs 64 CK HWs3 Lpixs_a3 RRpixs eq_refl (proj2 PMc3) Lpixs_a3 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A3 A3 M3 _ M3 m4 E3 (EVar 70) newstr 14 CK HWs3 Lnewstr_a3 RRnewstr eq_refl (proj2 PMc3) Lnewstr_a3 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A3 A3 M3 _ M3 m4 E3 (EVar 104) na 32 CK HWs3 Lna_a3 RRna eq_refl (proj2 PMc3) Lna_a3 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A3 A3 M3 _ M3 m4 E3 (EVar 138) arr 200 CK HWs3 Larr_a3 RRarr eq_refl (proj2 PMc3) Larr_a3 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E3 M3 m4 _ [] _ HKc3 KEPT3) as HKk3.
  match type of HKk3 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E3 m4 kk') in HKk3 end.
  pose proof (regs_ok_agree 140%nat E3 (ex_envL vals3 r4 [tok1; exW_canary SEGS 415784 m4]) _ _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa3.
  pose proof (exW_regs_call _ _ _ _ _ HRa3 (ex_regs_ok_junk vals3 r4 [tok1; exW_canary SEGS 415784 m4] 140%nat ltac:(vm_cast_no_check (eq_refl 140%nat))) CS3) as HRn4.
  clear HRa3.
  assert (HKa4 : know_ok SEGS (ex_envL vals3 r4 [tok1; exW_canary SEGS 415784 m4]) m4 _) by (exact (know_ok_agree SEGS 140%nat E3 _ m4 _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk3)).
  rewrite (fr_denot_agree 140%nat E3 (ex_envL vals3 r4 [tok1; exW_canary SEGS 415784 m4]) _ fr (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r4 ex_r10 (EVar 172) HRn4 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres3)) as HRx4. clear HRn4. rename HRx4 into HRn4.
  clear HR HK Hlf Hms HKc3 HKk3 KEPT3 HC3 HWs3 PMs3 Q10_3 Q11_3 Q1_3 Q2_3 Q4_3 PM3 HW3 PMc3 CS3 SUB3 RM3 MG3 TOP3 LEQ3 Hnz3 Ftok1x Lo3 OFF3 LDEL3 Lpixs_a3 Lnewstr_a3 Lna_a3 Larr_a3.
  subst M3. clear log3. clear E3. try clear Rc3. clear KN3.
  lazymatch type of HRn4 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn4 end.
  pose proof (exW_kn_blk SEGS C A4 m4 _ (ex_envL vals3 r4 [tok1; exW_canary SEGS 415784 m4]) (EVar 172) (EVar 32) tok1 3 s 12288 65536 356352 p16_segs CK HW4 Ltok1_a4 RRtok1 eq_refl eq_refl eq_refl RS ALtok1 ZERO3 WAPtok1 IMGAPtok1) as HKb4.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals3 r4 [tok1; exW_canary SEGS 415784 m4]) m4) _ _ (ex_kdisj_apart SEGS (ex_envL vals3 r4 [tok1; exW_canary SEGS 415784 m4]) m4 (EVar 34) (EVar 172) pixs tok1 0 64 0 3 eq_refl eq_refl RRpixs RRtok1 AP_pixs_tok1) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals3 r4 [tok1; exW_canary SEGS 415784 m4]) m4) _ _ (ex_kdisj_apart SEGS (ex_envL vals3 r4 [tok1; exW_canary SEGS 415784 m4]) m4 (EVar 70) (EVar 172) newstr tok1 0 14 0 3 eq_refl eq_refl RRnewstr RRtok1 AP_newstr_tok1) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals3 r4 [tok1; exW_canary SEGS 415784 m4]) m4) _ _ (ex_kdisj_apart SEGS (ex_envL vals3 r4 [tok1; exW_canary SEGS 415784 m4]) m4 (EVar 104) (EVar 172) na tok1 0 32 0 3 eq_refl eq_refl RRna RRtok1 AP_na_tok1) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals3 r4 [tok1; exW_canary SEGS 415784 m4]) m4) _ _ (ex_kdisj_apart SEGS (ex_envL vals3 r4 [tok1; exW_canary SEGS 415784 m4]) m4 (EVar 138) (EVar 172) arr tok1 0 200 0 3 eq_refl eq_refl RRarr RRtok1 AP_arr_tok1) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals3 r4 [tok1; exW_canary SEGS 415784 m4]) m4)))))) as HKd4.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A4 m4 _ (s - 12288) (Z.to_nat 12288) CK HW4 GLO1 GLO2) as SOK4.
  pose proof (exW_canary_ok SEGS 415784 m4 (canary_any m4)) as CANOK4.
  pose (vals4 := vals3 ++ map (getr r4) ex_regs_list ++ map (Z_to_bv 64) [tok1; exW_canary SEGS 415784 m4]).
  pose proof (exW_kn_fixed SEGS C A4 m4 _ (ex_envL vals3 r4 [tok1; exW_canary SEGS 415784 m4]) (EVar 173) (EVar 32) (exW_canary SEGS 415784 m4) s 12288 415784 65536 212992 213416 213568 213416 213568
                HW4 eq_refl (proj1 CANOK4) (proj2 CANOK4) eq_refl eq_refl eq_refl SOK4 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf4.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb4 (proj2 (Forall_app _ _ _) (conj HKd4 (proj2 (Forall_app _ _ _) (conj HKf4 HKa4)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn4 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN4 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb4 HKd4 HKf4 HKa4 SOK4 CANOK4.
  repeat match goal with H : getr r4 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO3 ALtok1.
  (* [comment removed for export] *)
  exb_exit ST Rc4 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E4 := EEx) in HR, Hlf, HK, Hms |- *; set (log4 := LLx) in Hms, Hlf; set (M4 := mem_denot E4 m4 log4) in Hms end.
  assert (WP4 : W C A4 M4 (with_vmmaps vm4 md) /\ POSTM C A0 s m4 M4).
  { subst M4. apply (exW_win_blks C A4 A0 m4 _ E4 log4 (EVar 32) s 12288 [(EVar 70, newstr, 14%Z); (EVar 104, na, 32%Z); (EVar 138, arr, 200%Z); (EVar 172, tok1, 3%Z)] CK HW4 SUB4 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRnewstr (conj Lnewstr_a4 (conj Fnewstr F0newstr))))|]. constructor; [exact (conj eq_refl (conj RRna (conj Lna_a4 (conj Fna F0na))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a4 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRtok1 (conj Ltok1_a4 (conj Ftok1 F0tok1))))|]. constructor. }
  destruct WP4 as [HWs4 PMs4].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log4 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC4 : carry log4 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc4 : know_ok SEGS E4 M4 kn1) by (apply (carry_after SEGS E4 m4 log4 kn0 [] kn1 scs hs HC4 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact Hms |].
  pose (BS4 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, newstr); (104%nat, na); (138%nat, arr); (172%nat, tok1)]).
  exW_regfactB BS4 HR ex_r10 Q10_4. exW_regfactB BS4 HR ex_r1 Q1_4. exW_regfactB BS4 HR ex_r2 Q2_4. exW_regfactB BS4 HR ex_r4 Q4_4.
  clear BS4.
  lazymatch type of Q2_4 with _ = Z_to_bv 64 (s + ?off) => pose (OFF4 := off) end.
  (* [comment removed for export] *)
  lazymatch type of Q1_4 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_4 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A4 M4 _ Rc4 (Z_to_bv 64 tok1) (Z_to_bv 64 ret) 3 sp' S CK HWs4 Q10_4 Ltok1_a4 F0tok1 Q1_4
             ltac:(red; apply bv_eq; reflexivity) Q4_4 Q2_4 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A5 m5 vm5 r5 HW5 CSx4 Ldead4 LEQ4 PMc4 RTR4.
  pose proof CSx4 as CS4. clear CSx4.
  rewrite with_vmmaps_twice in HW5 |- *.
  assert (SUB5 : sub_live A0 A5).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 tok1) by (intros ->; rewrite Ftok1 in Lq; discriminate Lq). rewrite (LEQ4 q NEq). exact (SUB4 q kq Lq). }
  assert (LDEL5 : forall q : word, ~ In q [Z_to_bv 64 arr; Z_to_bv 64 na; Z_to_bv 64 newstr] -> live A5 q = live A0 q).
  { intros q Hq. destruct (decide (Z_to_bv 64 tok1 = q)) as [<-|NEq]; [rewrite Ldead4, Ftok1; reflexivity|]. rewrite (LEQ4 q (fun EE => NEq (eq_sym EE))). apply LDEL4. clear - Hq NEq. cbn [In] in *. tauto. }
  assert (Lpixs_a5 : live A5 (Z_to_bv 64 pixs) = Some 64%Z) by (rewrite (LEQ4 _ NE_pixs_tok1); exact Lpixs_a4).
  assert (Lnewstr_a5 : live A5 (Z_to_bv 64 newstr) = Some 14%Z) by (rewrite (LEQ4 _ NE_newstr_tok1); exact Lnewstr_a4).
  assert (Lna_a5 : live A5 (Z_to_bv 64 na) = Some 32%Z) by (rewrite (LEQ4 _ NE_na_tok1); exact Lna_a4).
  assert (Larr_a5 : live A5 (Z_to_bv 64 arr) = Some 200%Z) by (rewrite (LEQ4 _ NE_arr_tok1); exact Larr_a4).
  assert (PM5 : POSTM C A0 s m0 m5).
  { eapply POSTM_trans; [exact PM4|]. eapply POSTM_trans; [exact PMs4|]. apply (POSTM_sub C A0 A5 _ _ _ SUB5).
    apply (POSTM_mono C A5 (s + OFF4) s); [unfold OFF4; lia | exact PMc4]. }
  pose proof (RTR4 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM4) ltac:(lia) ltac:(lia)) as RM5. rewrite !Z.sub_0_r in RM5.
  assert (KEPT4 : Forall (ex_region_kept E4 M4 m5) [(EVar 32, OFF4, 0%Z); (EVar 34, 0%Z, 64%Z); (EVar 70, 0%Z, 14%Z); (EVar 104, 0%Z, 32%Z); (EVar 138, 0%Z, 200%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF4 12288 M4 m5 E4 (EVar 32) CK (proj1 PMc4) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 m5 _ M4 m5 E4 (EVar 34) pixs 64 CK HW5 Lpixs_a5 RRpixs eq_refl (proj2 PMc4) Lpixs_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 m5 _ M4 m5 E4 (EVar 70) newstr 14 CK HW5 Lnewstr_a5 RRnewstr eq_refl (proj2 PMc4) Lnewstr_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 m5 _ M4 m5 E4 (EVar 104) na 32 CK HW5 Lna_a5 RRna eq_refl (proj2 PMc4) Lna_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 m5 _ M4 m5 E4 (EVar 138) arr 200 CK HW5 Larr_a5 RRarr eq_refl (proj2 PMc4) Larr_a5 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E4 M4 m5 _ [172%nat] _ HKc4 KEPT4) as HKk4.
  match type of HKk4 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E4 m5 kk') in HKk4 end.
  pose proof (regs_ok_agree 174%nat E4 (ex_envL vals4 r5 [exW_canary SEGS 415784 m5]) _ _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa4.
  pose proof (exW_regs_call _ _ _ _ _ HRa4 (ex_regs_ok_junk vals4 r5 [exW_canary SEGS 415784 m5] 174%nat ltac:(vm_cast_no_check (eq_refl 174%nat))) CS4) as HRn5.
  clear HRa4.
  assert (HKa5 : know_ok SEGS (ex_envL vals4 r5 [exW_canary SEGS 415784 m5]) m5 _) by (exact (know_ok_agree SEGS 174%nat E4 _ m5 _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk4)).
  rewrite (fr_denot_agree 174%nat E4 (ex_envL vals4 r5 [exW_canary SEGS 415784 m5]) _ fr (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc4 HKk4 KEPT4 HC4 HWs4 PMs4 Q10_4 Q1_4 Q2_4 Q4_4 PM4 HW4 PMc4 CS4 SUB4 RM4 Ldead4 LEQ4 RTR4 Ltok1_a4 OFF4 LDEL4 Lpixs_a4 Lnewstr_a4 Lna_a4 Larr_a4.
  subst M4. clear log4. clear E4. try clear Rc4. clear KN4.
  lazymatch type of HRn5 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn5 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A5 m5 _ (s - 12288) (Z.to_nat 12288) CK HW5 GLO1 GLO2) as SOK5.
  pose proof (exW_canary_ok SEGS 415784 m5 (canary_any m5)) as CANOK5.
  pose (vals5 := vals4 ++ map (getr r5) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m5]).
  pose proof (exW_kn_fixed SEGS C A5 m5 _ (ex_envL vals4 r5 [exW_canary SEGS 415784 m5]) (EVar 206) (EVar 32) (exW_canary SEGS 415784 m5) s 12288 415784 65536 212992 213416 213568 213416 213568
                HW5 eq_refl (proj1 CANOK5) (proj2 CANOK5) eq_refl eq_refl eq_refl SOK5 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf5.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf5 HKa5)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn5 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN5 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf5 HKa5 SOK5 CANOK5.
  repeat match goal with H : getr r5 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc5 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E5 := EEx) in HR, Hlf, HK, Hms |- *; set (log5 := LLx) in Hms, Hlf; set (M5 := mem_denot E5 m5 log5) in Hms end.
  assert (WP5 : W C A5 M5 (with_vmmaps vm5 md) /\ POSTM C A0 s m5 M5).
  { subst M5. apply (exW_win_blks C A5 A0 m5 _ E5 log5 (EVar 32) s 12288 [(EVar 70, newstr, 14%Z); (EVar 104, na, 32%Z); (EVar 138, arr, 200%Z)] CK HW5 SUB5 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRnewstr (conj Lnewstr_a5 (conj Fnewstr F0newstr))))|]. constructor; [exact (conj eq_refl (conj RRna (conj Lna_a5 (conj Fna F0na))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a5 (conj Farr F0arr))))|]. constructor. }
  destruct WP5 as [HWs5 PMs5].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log5 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC5 : carry log5 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc5 : know_ok SEGS E5 M5 kn1) by (apply (carry_after SEGS E5 m5 log5 kn0 [] kn1 scs hs HC5 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact Hms |].
  pose (BS5 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, newstr); (104%nat, na); (138%nat, arr)]).
  exW_regfactB BS5 HR ex_r10 Q10_5. exW_regfactB BS5 HR ex_r11 Q11_5. exW_regfactB BS5 HR ex_r1 Q1_5. exW_regfactB BS5 HR ex_r2 Q2_5. exW_regfactB BS5 HR ex_r4 Q4_5.
  clear BS5.
  lazymatch type of Q2_5 with _ = Z_to_bv 64 (s + ?off) => pose (OFF5 := off) end.
  (* [comment removed for export] *)
  pose proof (alloc_margin_small (3 * 1) ltac:(exW_cmp)) as MG5.
  lazymatch type of Q1_5 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_5 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A5 M5 _ Rc5 3 1 (kR - 4) (bR - 4 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs5 Q10_5 Q11_5 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM5) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_5
             ltac:(red; apply bv_eq; reflexivity) Q4_5 Q2_5 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A6 m6 vm6 r6 res5 HW6 Hres5 CSx5 Hnz5 Ftok2x Lo5 F0tok2 LEQ5 ZERO5 ALtok2 TOP5 PMc5 RM6.
  pose proof CSx5 as CS5. clear CSx5.
  rewrite with_vmmaps_twice in HW6 |- *.
  assert (Eres5 : res5 = Z_to_bv 64 (u res5)) by (symmetry; apply zbv_self).
  pose proof (u64_range res5) as RRtok2. set (tok2 := u res5) in *. clearbody tok2. rewrite Eres5 in Hres5, Ftok2x, Lo5, F0tok2, LEQ5, ZERO5. clear Eres5.
  change (3 * 1)%Z with 3%Z in *.
  pose proof (exW_blk_img_apart_h2 C A6 m6 _ tok2 3 CK HW6 Lo5 RRtok2 eq_refl eq_refl) as IMGAPtok2. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPtok2.
  pose proof (exW_win_blk_apart_h C A6 m6 _ s 12288 tok2 3 CK HW6 Lo5 eq_refl RRtok2 GLO1) as WAPtok2.
  assert (Ftok2 : live A0 (Z_to_bv 64 tok2) = None).
  { destruct (live A0 (Z_to_bv 64 tok2)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB5 _ _ EE) as XX. first [discriminate Ftok2x | (rewrite Ftok2x in XX; discriminate XX)]. }
  pose proof Lo5 as Ltok2_a6.
  assert (SUB6 : sub_live A0 A6).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 tok2) by (intros ->; rewrite Ftok2 in Lq; discriminate Lq). rewrite (LEQ5 q NEq). exact (SUB5 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 tok2 :: [Z_to_bv 64 arr; Z_to_bv 64 na; Z_to_bv 64 newstr])) => eq_trans (LEQ5 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL5 q (fun XX => Hq (or_intror XX)))) as LDEL6.
  assert (NE_pixs_tok2 : Z_to_bv 64 pixs <> Z_to_bv 64 tok2) by (intros EE; rewrite EE in Lpixs_a5; rewrite Ftok2x in Lpixs_a5; discriminate Lpixs_a5).
  assert (Lpixs_a6 : live A6 (Z_to_bv 64 pixs) = Some 64%Z) by (rewrite (LEQ5 _ NE_pixs_tok2); exact Lpixs_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ pixs tok2 64 3 CK HW6 Lpixs_a6 Ltok2_a6 NE_pixs_tok2 RRpixs RRtok2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_pixs_tok2.
  assert (NE_newstr_tok2 : Z_to_bv 64 newstr <> Z_to_bv 64 tok2) by (intros EE; rewrite EE in Lnewstr_a5; rewrite Ftok2x in Lnewstr_a5; discriminate Lnewstr_a5).
  assert (Lnewstr_a6 : live A6 (Z_to_bv 64 newstr) = Some 14%Z) by (rewrite (LEQ5 _ NE_newstr_tok2); exact Lnewstr_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ newstr tok2 14 3 CK HW6 Lnewstr_a6 Ltok2_a6 NE_newstr_tok2 RRnewstr RRtok2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_newstr_tok2.
  assert (NE_na_tok2 : Z_to_bv 64 na <> Z_to_bv 64 tok2) by (intros EE; rewrite EE in Lna_a5; rewrite Ftok2x in Lna_a5; discriminate Lna_a5).
  assert (Lna_a6 : live A6 (Z_to_bv 64 na) = Some 32%Z) by (rewrite (LEQ5 _ NE_na_tok2); exact Lna_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ na tok2 32 3 CK HW6 Lna_a6 Ltok2_a6 NE_na_tok2 RRna RRtok2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_na_tok2.
  assert (NE_arr_tok2 : Z_to_bv 64 arr <> Z_to_bv 64 tok2) by (intros EE; rewrite EE in Larr_a5; rewrite Ftok2x in Larr_a5; discriminate Larr_a5).
  assert (Larr_a6 : live A6 (Z_to_bv 64 arr) = Some 200%Z) by (rewrite (LEQ5 _ NE_arr_tok2); exact Larr_a5).
  pose proof (exW_blk_apart_h C A6 m6 _ arr tok2 200 3 CK HW6 Larr_a6 Ltok2_a6 NE_arr_tok2 RRarr RRtok2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_tok2.
  assert (PM6 : POSTM C A0 s m0 m6).
  { eapply POSTM_trans; [exact PM5|]. eapply POSTM_trans; [exact PMs5|]. apply (POSTM_sub C A0 A5 _ _ _ SUB5).
    apply (POSTM_mono C A5 (s + OFF5) s); [unfold OFF5; lia | exact PMc5]. }
  replace (kR - 4 - 1)%Z with (kR - 5)%Z in RM6 by lia. rewrite MG5 in RM6. replace (bR - 4 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 5 * 2 ^ 17)%Z in RM6 by lia.
  assert (KEPT5 : Forall (ex_region_kept E5 M5 m6) [(EVar 32, OFF5, 0%Z); (EVar 34, 0%Z, 64%Z); (EVar 70, 0%Z, 14%Z); (EVar 104, 0%Z, 32%Z); (EVar 138, 0%Z, 200%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF5 12288 M5 m6 E5 (EVar 32) CK (proj1 PMc5) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 34) pixs 64 CK HWs5 Lpixs_a5 RRpixs eq_refl (proj2 PMc5) Lpixs_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 70) newstr 14 CK HWs5 Lnewstr_a5 RRnewstr eq_refl (proj2 PMc5) Lnewstr_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 104) na 32 CK HWs5 Lna_a5 RRna eq_refl (proj2 PMc5) Lna_a5 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A5 A5 M5 _ M5 m6 E5 (EVar 138) arr 200 CK HWs5 Larr_a5 RRarr eq_refl (proj2 PMc5) Larr_a5 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E5 M5 m6 _ [172%nat] _ HKc5 KEPT5) as HKk5.
  match type of HKk5 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E5 m6 kk') in HKk5 end.
  pose proof (regs_ok_agree 207%nat E5 (ex_envL vals5 r6 [tok2; exW_canary SEGS 415784 m6]) _ _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa5.
  pose proof (exW_regs_call _ _ _ _ _ HRa5 (ex_regs_ok_junk vals5 r6 [tok2; exW_canary SEGS 415784 m6] 207%nat ltac:(vm_cast_no_check (eq_refl 207%nat))) CS5) as HRn6.
  clear HRa5.
  assert (HKa6 : know_ok SEGS (ex_envL vals5 r6 [tok2; exW_canary SEGS 415784 m6]) m6 _) by (exact (know_ok_agree SEGS 207%nat E5 _ m6 _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk5)).
  rewrite (fr_denot_agree 207%nat E5 (ex_envL vals5 r6 [tok2; exW_canary SEGS 415784 m6]) _ fr (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r6 ex_r10 (EVar 239) HRn6 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres5)) as HRx6. clear HRn6. rename HRx6 into HRn6.
  clear HR HK Hlf Hms HKc5 HKk5 KEPT5 HC5 HWs5 PMs5 Q10_5 Q11_5 Q1_5 Q2_5 Q4_5 PM5 HW5 PMc5 CS5 SUB5 RM5 MG5 TOP5 LEQ5 Hnz5 Ftok2x Lo5 OFF5 LDEL5 Lpixs_a5 Lnewstr_a5 Lna_a5 Larr_a5.
  subst M5. clear log5. clear E5. try clear Rc5. clear KN5.
  lazymatch type of HRn6 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn6 end.
  pose proof (exW_kn_blk SEGS C A6 m6 _ (ex_envL vals5 r6 [tok2; exW_canary SEGS 415784 m6]) (EVar 239) (EVar 32) tok2 3 s 12288 65536 356352 p16_segs CK HW6 Ltok2_a6 RRtok2 eq_refl eq_refl eq_refl RS ALtok2 ZERO5 WAPtok2 IMGAPtok2) as HKb6.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [tok2; exW_canary SEGS 415784 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [tok2; exW_canary SEGS 415784 m6]) m6 (EVar 34) (EVar 239) pixs tok2 0 64 0 3 eq_refl eq_refl RRpixs RRtok2 AP_pixs_tok2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [tok2; exW_canary SEGS 415784 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [tok2; exW_canary SEGS 415784 m6]) m6 (EVar 70) (EVar 239) newstr tok2 0 14 0 3 eq_refl eq_refl RRnewstr RRtok2 AP_newstr_tok2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [tok2; exW_canary SEGS 415784 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [tok2; exW_canary SEGS 415784 m6]) m6 (EVar 104) (EVar 239) na tok2 0 32 0 3 eq_refl eq_refl RRna RRtok2 AP_na_tok2) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals5 r6 [tok2; exW_canary SEGS 415784 m6]) m6) _ _ (ex_kdisj_apart SEGS (ex_envL vals5 r6 [tok2; exW_canary SEGS 415784 m6]) m6 (EVar 138) (EVar 239) arr tok2 0 200 0 3 eq_refl eq_refl RRarr RRtok2 AP_arr_tok2) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals5 r6 [tok2; exW_canary SEGS 415784 m6]) m6)))))) as HKd6.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A6 m6 _ (s - 12288) (Z.to_nat 12288) CK HW6 GLO1 GLO2) as SOK6.
  pose proof (exW_canary_ok SEGS 415784 m6 (canary_any m6)) as CANOK6.
  pose (vals6 := vals5 ++ map (getr r6) ex_regs_list ++ map (Z_to_bv 64) [tok2; exW_canary SEGS 415784 m6]).
  pose proof (exW_kn_fixed SEGS C A6 m6 _ (ex_envL vals5 r6 [tok2; exW_canary SEGS 415784 m6]) (EVar 240) (EVar 32) (exW_canary SEGS 415784 m6) s 12288 415784 65536 212992 213416 213568 213416 213568
                HW6 eq_refl (proj1 CANOK6) (proj2 CANOK6) eq_refl eq_refl eq_refl SOK6 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf6.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb6 (proj2 (Forall_app _ _ _) (conj HKd6 (proj2 (Forall_app _ _ _) (conj HKf6 HKa6)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn6 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN6 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb6 HKd6 HKf6 HKa6 SOK6 CANOK6.
  repeat match goal with H : getr r6 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO5 ALtok2.
  (* [comment removed for export] *)
  exb_exit ST Rc6 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E6 := EEx) in HR, Hlf, HK, Hms |- *; set (log6 := LLx) in Hms, Hlf; set (M6 := mem_denot E6 m6 log6) in Hms end.
  assert (WP6 : W C A6 M6 (with_vmmaps vm6 md) /\ POSTM C A0 s m6 M6).
  { subst M6. apply (exW_win_blks C A6 A0 m6 _ E6 log6 (EVar 32) s 12288 [(EVar 70, newstr, 14%Z); (EVar 104, na, 32%Z); (EVar 138, arr, 200%Z); (EVar 239, tok2, 3%Z)] CK HW6 SUB6 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRnewstr (conj Lnewstr_a6 (conj Fnewstr F0newstr))))|]. constructor; [exact (conj eq_refl (conj RRna (conj Lna_a6 (conj Fna F0na))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a6 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRtok2 (conj Ltok2_a6 (conj Ftok2 F0tok2))))|]. constructor. }
  destruct WP6 as [HWs6 PMs6].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log6 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC6 : carry log6 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc6 : know_ok SEGS E6 M6 kn1) by (apply (carry_after SEGS E6 m6 log6 kn0 [] kn1 scs hs HC6 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact Hms |].
  pose (BS6 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, newstr); (104%nat, na); (138%nat, arr); (239%nat, tok2)]).
  exW_regfactB BS6 HR ex_r10 Q10_6. exW_regfactB BS6 HR ex_r1 Q1_6. exW_regfactB BS6 HR ex_r2 Q2_6. exW_regfactB BS6 HR ex_r4 Q4_6.
  clear BS6.
  lazymatch type of Q2_6 with _ = Z_to_bv 64 (s + ?off) => pose (OFF6 := off) end.
  (* [comment removed for export] *)
  lazymatch type of Q1_6 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_6 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A6 M6 _ Rc6 (Z_to_bv 64 tok2) (Z_to_bv 64 ret) 3 sp' S CK HWs6 Q10_6 Ltok2_a6 F0tok2 Q1_6
             ltac:(red; apply bv_eq; reflexivity) Q4_6 Q2_6 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A7 m7 vm7 r7 HW7 CSx6 Ldead6 LEQ6 PMc6 RTR6.
  pose proof CSx6 as CS6. clear CSx6.
  rewrite with_vmmaps_twice in HW7 |- *.
  assert (SUB7 : sub_live A0 A7).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 tok2) by (intros ->; rewrite Ftok2 in Lq; discriminate Lq). rewrite (LEQ6 q NEq). exact (SUB6 q kq Lq). }
  assert (LDEL7 : forall q : word, ~ In q [Z_to_bv 64 arr; Z_to_bv 64 na; Z_to_bv 64 newstr] -> live A7 q = live A0 q).
  { intros q Hq. destruct (decide (Z_to_bv 64 tok2 = q)) as [<-|NEq]; [rewrite Ldead6, Ftok2; reflexivity|]. rewrite (LEQ6 q (fun EE => NEq (eq_sym EE))). apply LDEL6. clear - Hq NEq. cbn [In] in *. tauto. }
  assert (Lpixs_a7 : live A7 (Z_to_bv 64 pixs) = Some 64%Z) by (rewrite (LEQ6 _ NE_pixs_tok2); exact Lpixs_a6).
  assert (Lnewstr_a7 : live A7 (Z_to_bv 64 newstr) = Some 14%Z) by (rewrite (LEQ6 _ NE_newstr_tok2); exact Lnewstr_a6).
  assert (Lna_a7 : live A7 (Z_to_bv 64 na) = Some 32%Z) by (rewrite (LEQ6 _ NE_na_tok2); exact Lna_a6).
  assert (Larr_a7 : live A7 (Z_to_bv 64 arr) = Some 200%Z) by (rewrite (LEQ6 _ NE_arr_tok2); exact Larr_a6).
  assert (PM7 : POSTM C A0 s m0 m7).
  { eapply POSTM_trans; [exact PM6|]. eapply POSTM_trans; [exact PMs6|]. apply (POSTM_sub C A0 A7 _ _ _ SUB7).
    apply (POSTM_mono C A7 (s + OFF6) s); [unfold OFF6; lia | exact PMc6]. }
  pose proof (RTR6 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM6) ltac:(lia) ltac:(lia)) as RM7. rewrite !Z.sub_0_r in RM7.
  assert (KEPT6 : Forall (ex_region_kept E6 M6 m7) [(EVar 32, OFF6, 0%Z); (EVar 34, 0%Z, 64%Z); (EVar 70, 0%Z, 14%Z); (EVar 104, 0%Z, 32%Z); (EVar 138, 0%Z, 200%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF6 12288 M6 m7 E6 (EVar 32) CK (proj1 PMc6) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A7 A7 m7 _ M6 m7 E6 (EVar 34) pixs 64 CK HW7 Lpixs_a7 RRpixs eq_refl (proj2 PMc6) Lpixs_a7 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A7 A7 m7 _ M6 m7 E6 (EVar 70) newstr 14 CK HW7 Lnewstr_a7 RRnewstr eq_refl (proj2 PMc6) Lnewstr_a7 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A7 A7 m7 _ M6 m7 E6 (EVar 104) na 32 CK HW7 Lna_a7 RRna eq_refl (proj2 PMc6) Lna_a7 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A7 A7 m7 _ M6 m7 E6 (EVar 138) arr 200 CK HW7 Larr_a7 RRarr eq_refl (proj2 PMc6) Larr_a7 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E6 M6 m7 _ [172%nat; 239%nat] _ HKc6 KEPT6) as HKk6.
  match type of HKk6 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E6 m7 kk') in HKk6 end.
  pose proof (regs_ok_agree 241%nat E6 (ex_envL vals6 r7 [exW_canary SEGS 415784 m7]) _ _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa6.
  pose proof (exW_regs_call _ _ _ _ _ HRa6 (ex_regs_ok_junk vals6 r7 [exW_canary SEGS 415784 m7] 241%nat ltac:(vm_cast_no_check (eq_refl 241%nat))) CS6) as HRn7.
  clear HRa6.
  assert (HKa7 : know_ok SEGS (ex_envL vals6 r7 [exW_canary SEGS 415784 m7]) m7 _) by (exact (know_ok_agree SEGS 241%nat E6 _ m7 _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk6)).
  rewrite (fr_denot_agree 241%nat E6 (ex_envL vals6 r7 [exW_canary SEGS 415784 m7]) _ fr (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc6 HKk6 KEPT6 HC6 HWs6 PMs6 Q10_6 Q1_6 Q2_6 Q4_6 PM6 HW6 PMc6 CS6 SUB6 RM6 Ldead6 LEQ6 RTR6 Ltok2_a6 OFF6 LDEL6 Lpixs_a6 Lnewstr_a6 Lna_a6 Larr_a6.
  subst M6. clear log6. clear E6. try clear Rc6. clear KN6.
  lazymatch type of HRn7 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn7 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A7 m7 _ (s - 12288) (Z.to_nat 12288) CK HW7 GLO1 GLO2) as SOK7.
  pose proof (exW_canary_ok SEGS 415784 m7 (canary_any m7)) as CANOK7.
  pose (vals7 := vals6 ++ map (getr r7) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m7]).
  pose proof (exW_kn_fixed SEGS C A7 m7 _ (ex_envL vals6 r7 [exW_canary SEGS 415784 m7]) (EVar 273) (EVar 32) (exW_canary SEGS 415784 m7) s 12288 415784 65536 212992 213416 213568 213416 213568
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
  assert (WP7 : W C A7 M7 (with_vmmaps vm7 md) /\ POSTM C A0 s m7 M7).
  { subst M7. apply (exW_win_blks C A7 A0 m7 _ E7 log7 (EVar 32) s 12288 [(EVar 70, newstr, 14%Z); (EVar 104, na, 32%Z); (EVar 138, arr, 200%Z)] CK HW7 SUB7 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRnewstr (conj Lnewstr_a7 (conj Fnewstr F0newstr))))|]. constructor; [exact (conj eq_refl (conj RRna (conj Lna_a7 (conj Fna F0na))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a7 (conj Farr F0arr))))|]. constructor. }
  destruct WP7 as [HWs7 PMs7].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log7 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC7 : carry log7 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc7 : know_ok SEGS E7 M7 kn1) by (apply (carry_after SEGS E7 m7 log7 kn0 [] kn1 scs hs HC7 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact Hms |].
  pose (BS7 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, newstr); (104%nat, na); (138%nat, arr)]).
  exW_regfactB BS7 HR ex_r10 Q10_7. exW_regfactB BS7 HR ex_r11 Q11_7. exW_regfactB BS7 HR ex_r1 Q1_7. exW_regfactB BS7 HR ex_r2 Q2_7. exW_regfactB BS7 HR ex_r4 Q4_7.
  clear BS7.
  lazymatch type of Q2_7 with _ = Z_to_bv 64 (s + ?off) => pose (OFF7 := off) end.
  (* [comment removed for export] *)
  pose proof (alloc_margin_small (4 * 1) ltac:(exW_cmp)) as MG7.
  lazymatch type of Q1_7 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_7 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A7 M7 _ Rc7 4 1 (kR - 5) (bR - 5 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs7 Q10_7 Q11_7 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM7) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_7
             ltac:(red; apply bv_eq; reflexivity) Q4_7 Q2_7 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A8 m8 vm8 r8 res7 HW8 Hres7 CSx7 Hnz7 Ftok3x Lo7 F0tok3 LEQ7 ZERO7 ALtok3 TOP7 PMc7 RM8.
  pose proof CSx7 as CS7. clear CSx7.
  rewrite with_vmmaps_twice in HW8 |- *.
  assert (Eres7 : res7 = Z_to_bv 64 (u res7)) by (symmetry; apply zbv_self).
  pose proof (u64_range res7) as RRtok3. set (tok3 := u res7) in *. clearbody tok3. rewrite Eres7 in Hres7, Ftok3x, Lo7, F0tok3, LEQ7, ZERO7. clear Eres7.
  change (4 * 1)%Z with 4%Z in *.
  pose proof (exW_blk_img_apart_h2 C A8 m8 _ tok3 4 CK HW8 Lo7 RRtok3 eq_refl eq_refl) as IMGAPtok3. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPtok3.
  pose proof (exW_win_blk_apart_h C A8 m8 _ s 12288 tok3 4 CK HW8 Lo7 eq_refl RRtok3 GLO1) as WAPtok3.
  assert (Ftok3 : live A0 (Z_to_bv 64 tok3) = None).
  { destruct (live A0 (Z_to_bv 64 tok3)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB7 _ _ EE) as XX. first [discriminate Ftok3x | (rewrite Ftok3x in XX; discriminate XX)]. }
  pose proof Lo7 as Ltok3_a8.
  assert (SUB8 : sub_live A0 A8).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 tok3) by (intros ->; rewrite Ftok3 in Lq; discriminate Lq). rewrite (LEQ7 q NEq). exact (SUB7 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 tok3 :: [Z_to_bv 64 arr; Z_to_bv 64 na; Z_to_bv 64 newstr])) => eq_trans (LEQ7 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL7 q (fun XX => Hq (or_intror XX)))) as LDEL8.
  assert (NE_pixs_tok3 : Z_to_bv 64 pixs <> Z_to_bv 64 tok3) by (intros EE; rewrite EE in Lpixs_a7; rewrite Ftok3x in Lpixs_a7; discriminate Lpixs_a7).
  assert (Lpixs_a8 : live A8 (Z_to_bv 64 pixs) = Some 64%Z) by (rewrite (LEQ7 _ NE_pixs_tok3); exact Lpixs_a7).
  pose proof (exW_blk_apart_h C A8 m8 _ pixs tok3 64 4 CK HW8 Lpixs_a8 Ltok3_a8 NE_pixs_tok3 RRpixs RRtok3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_pixs_tok3.
  assert (NE_newstr_tok3 : Z_to_bv 64 newstr <> Z_to_bv 64 tok3) by (intros EE; rewrite EE in Lnewstr_a7; rewrite Ftok3x in Lnewstr_a7; discriminate Lnewstr_a7).
  assert (Lnewstr_a8 : live A8 (Z_to_bv 64 newstr) = Some 14%Z) by (rewrite (LEQ7 _ NE_newstr_tok3); exact Lnewstr_a7).
  pose proof (exW_blk_apart_h C A8 m8 _ newstr tok3 14 4 CK HW8 Lnewstr_a8 Ltok3_a8 NE_newstr_tok3 RRnewstr RRtok3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_newstr_tok3.
  assert (NE_na_tok3 : Z_to_bv 64 na <> Z_to_bv 64 tok3) by (intros EE; rewrite EE in Lna_a7; rewrite Ftok3x in Lna_a7; discriminate Lna_a7).
  assert (Lna_a8 : live A8 (Z_to_bv 64 na) = Some 32%Z) by (rewrite (LEQ7 _ NE_na_tok3); exact Lna_a7).
  pose proof (exW_blk_apart_h C A8 m8 _ na tok3 32 4 CK HW8 Lna_a8 Ltok3_a8 NE_na_tok3 RRna RRtok3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_na_tok3.
  assert (NE_arr_tok3 : Z_to_bv 64 arr <> Z_to_bv 64 tok3) by (intros EE; rewrite EE in Larr_a7; rewrite Ftok3x in Larr_a7; discriminate Larr_a7).
  assert (Larr_a8 : live A8 (Z_to_bv 64 arr) = Some 200%Z) by (rewrite (LEQ7 _ NE_arr_tok3); exact Larr_a7).
  pose proof (exW_blk_apart_h C A8 m8 _ arr tok3 200 4 CK HW8 Larr_a8 Ltok3_a8 NE_arr_tok3 RRarr RRtok3 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_tok3.
  assert (PM8 : POSTM C A0 s m0 m8).
  { eapply POSTM_trans; [exact PM7|]. eapply POSTM_trans; [exact PMs7|]. apply (POSTM_sub C A0 A7 _ _ _ SUB7).
    apply (POSTM_mono C A7 (s + OFF7) s); [unfold OFF7; lia | exact PMc7]. }
  replace (kR - 5 - 1)%Z with (kR - 6)%Z in RM8 by lia. rewrite MG7 in RM8. replace (bR - 5 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 6 * 2 ^ 17)%Z in RM8 by lia.
  assert (KEPT7 : Forall (ex_region_kept E7 M7 m8) [(EVar 32, OFF7, 0%Z); (EVar 34, 0%Z, 64%Z); (EVar 70, 0%Z, 14%Z); (EVar 104, 0%Z, 32%Z); (EVar 138, 0%Z, 200%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF7 12288 M7 m8 E7 (EVar 32) CK (proj1 PMc7) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A7 A7 M7 _ M7 m8 E7 (EVar 34) pixs 64 CK HWs7 Lpixs_a7 RRpixs eq_refl (proj2 PMc7) Lpixs_a7 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A7 A7 M7 _ M7 m8 E7 (EVar 70) newstr 14 CK HWs7 Lnewstr_a7 RRnewstr eq_refl (proj2 PMc7) Lnewstr_a7 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A7 A7 M7 _ M7 m8 E7 (EVar 104) na 32 CK HWs7 Lna_a7 RRna eq_refl (proj2 PMc7) Lna_a7 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A7 A7 M7 _ M7 m8 E7 (EVar 138) arr 200 CK HWs7 Larr_a7 RRarr eq_refl (proj2 PMc7) Larr_a7 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E7 M7 m8 _ [172%nat; 239%nat] _ HKc7 KEPT7) as HKk7.
  match type of HKk7 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E7 m8 kk') in HKk7 end.
  pose proof (regs_ok_agree 274%nat E7 (ex_envL vals7 r8 [tok3; exW_canary SEGS 415784 m8]) _ _ (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa7.
  pose proof (exW_regs_call _ _ _ _ _ HRa7 (ex_regs_ok_junk vals7 r8 [tok3; exW_canary SEGS 415784 m8] 274%nat ltac:(vm_cast_no_check (eq_refl 274%nat))) CS7) as HRn8.
  clear HRa7.
  assert (HKa8 : know_ok SEGS (ex_envL vals7 r8 [tok3; exW_canary SEGS 415784 m8]) m8 _) by (exact (know_ok_agree SEGS 274%nat E7 _ m8 _ (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk7)).
  rewrite (fr_denot_agree 274%nat E7 (ex_envL vals7 r8 [tok3; exW_canary SEGS 415784 m8]) _ fr (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r8 ex_r10 (EVar 306) HRn8 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres7)) as HRx8. clear HRn8. rename HRx8 into HRn8.
  clear HR HK Hlf Hms HKc7 HKk7 KEPT7 HC7 HWs7 PMs7 Q10_7 Q11_7 Q1_7 Q2_7 Q4_7 PM7 HW7 PMc7 CS7 SUB7 RM7 MG7 TOP7 LEQ7 Hnz7 Ftok3x Lo7 OFF7 LDEL7 Lpixs_a7 Lnewstr_a7 Lna_a7 Larr_a7.
  subst M7. clear log7. clear E7. try clear Rc7. clear KN7.
  lazymatch type of HRn8 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn8 end.
  pose proof (exW_kn_blk SEGS C A8 m8 _ (ex_envL vals7 r8 [tok3; exW_canary SEGS 415784 m8]) (EVar 306) (EVar 32) tok3 4 s 12288 65536 356352 p16_segs CK HW8 Ltok3_a8 RRtok3 eq_refl eq_refl eq_refl RS ALtok3 ZERO7 WAPtok3 IMGAPtok3) as HKb8.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals7 r8 [tok3; exW_canary SEGS 415784 m8]) m8) _ _ (ex_kdisj_apart SEGS (ex_envL vals7 r8 [tok3; exW_canary SEGS 415784 m8]) m8 (EVar 34) (EVar 306) pixs tok3 0 64 0 4 eq_refl eq_refl RRpixs RRtok3 AP_pixs_tok3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals7 r8 [tok3; exW_canary SEGS 415784 m8]) m8) _ _ (ex_kdisj_apart SEGS (ex_envL vals7 r8 [tok3; exW_canary SEGS 415784 m8]) m8 (EVar 70) (EVar 306) newstr tok3 0 14 0 4 eq_refl eq_refl RRnewstr RRtok3 AP_newstr_tok3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals7 r8 [tok3; exW_canary SEGS 415784 m8]) m8) _ _ (ex_kdisj_apart SEGS (ex_envL vals7 r8 [tok3; exW_canary SEGS 415784 m8]) m8 (EVar 104) (EVar 306) na tok3 0 32 0 4 eq_refl eq_refl RRna RRtok3 AP_na_tok3) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals7 r8 [tok3; exW_canary SEGS 415784 m8]) m8) _ _ (ex_kdisj_apart SEGS (ex_envL vals7 r8 [tok3; exW_canary SEGS 415784 m8]) m8 (EVar 138) (EVar 306) arr tok3 0 200 0 4 eq_refl eq_refl RRarr RRtok3 AP_arr_tok3) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals7 r8 [tok3; exW_canary SEGS 415784 m8]) m8)))))) as HKd8.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A8 m8 _ (s - 12288) (Z.to_nat 12288) CK HW8 GLO1 GLO2) as SOK8.
  pose proof (exW_canary_ok SEGS 415784 m8 (canary_any m8)) as CANOK8.
  pose (vals8 := vals7 ++ map (getr r8) ex_regs_list ++ map (Z_to_bv 64) [tok3; exW_canary SEGS 415784 m8]).
  pose proof (exW_kn_fixed SEGS C A8 m8 _ (ex_envL vals7 r8 [tok3; exW_canary SEGS 415784 m8]) (EVar 307) (EVar 32) (exW_canary SEGS 415784 m8) s 12288 415784 65536 212992 213416 213568 213416 213568
                HW8 eq_refl (proj1 CANOK8) (proj2 CANOK8) eq_refl eq_refl eq_refl SOK8 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf8.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb8 (proj2 (Forall_app _ _ _) (conj HKd8 (proj2 (Forall_app _ _ _) (conj HKf8 HKa8)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn8 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN8 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb8 HKd8 HKf8 HKa8 SOK8 CANOK8.
  repeat match goal with H : getr r8 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO7 ALtok3.
  (* [comment removed for export] *)
  exb_exit ST Rc8 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E8 := EEx) in HR, Hlf, HK, Hms |- *; set (log8 := LLx) in Hms, Hlf; set (M8 := mem_denot E8 m8 log8) in Hms end.
  assert (WP8 : W C A8 M8 (with_vmmaps vm8 md) /\ POSTM C A0 s m8 M8).
  { subst M8. apply (exW_win_blks C A8 A0 m8 _ E8 log8 (EVar 32) s 12288 [(EVar 70, newstr, 14%Z); (EVar 104, na, 32%Z); (EVar 138, arr, 200%Z); (EVar 306, tok3, 4%Z)] CK HW8 SUB8 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRnewstr (conj Lnewstr_a8 (conj Fnewstr F0newstr))))|]. constructor; [exact (conj eq_refl (conj RRna (conj Lna_a8 (conj Fna F0na))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a8 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRtok3 (conj Ltok3_a8 (conj Ftok3 F0tok3))))|]. constructor. }
  destruct WP8 as [HWs8 PMs8].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log8 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC8 : carry log8 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc8 : know_ok SEGS E8 M8 kn1) by (apply (carry_after SEGS E8 m8 log8 kn0 [] kn1 scs hs HC8 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW8)) | exact (mp_lazy _ (w_pure _ _ _ _ HW8)) | exact Hms |].
  pose (BS8 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, newstr); (104%nat, na); (138%nat, arr); (306%nat, tok3)]).
  exW_regfactB BS8 HR ex_r10 Q10_8. exW_regfactB BS8 HR ex_r1 Q1_8. exW_regfactB BS8 HR ex_r2 Q2_8. exW_regfactB BS8 HR ex_r4 Q4_8.
  clear BS8.
  lazymatch type of Q2_8 with _ = Z_to_bv 64 (s + ?off) => pose (OFF8 := off) end.
  (* [comment removed for export] *)
  lazymatch type of Q1_8 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_8 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A8 M8 _ Rc8 (Z_to_bv 64 tok3) (Z_to_bv 64 ret) 4 sp' S CK HWs8 Q10_8 Ltok3_a8 F0tok3 Q1_8
             ltac:(red; apply bv_eq; reflexivity) Q4_8 Q2_8 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A9 m9 vm9 r9 HW9 CSx8 Ldead8 LEQ8 PMc8 RTR8.
  pose proof CSx8 as CS8. clear CSx8.
  rewrite with_vmmaps_twice in HW9 |- *.
  assert (SUB9 : sub_live A0 A9).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 tok3) by (intros ->; rewrite Ftok3 in Lq; discriminate Lq). rewrite (LEQ8 q NEq). exact (SUB8 q kq Lq). }
  assert (LDEL9 : forall q : word, ~ In q [Z_to_bv 64 arr; Z_to_bv 64 na; Z_to_bv 64 newstr] -> live A9 q = live A0 q).
  { intros q Hq. destruct (decide (Z_to_bv 64 tok3 = q)) as [<-|NEq]; [rewrite Ldead8, Ftok3; reflexivity|]. rewrite (LEQ8 q (fun EE => NEq (eq_sym EE))). apply LDEL8. clear - Hq NEq. cbn [In] in *. tauto. }
  assert (Lpixs_a9 : live A9 (Z_to_bv 64 pixs) = Some 64%Z) by (rewrite (LEQ8 _ NE_pixs_tok3); exact Lpixs_a8).
  assert (Lnewstr_a9 : live A9 (Z_to_bv 64 newstr) = Some 14%Z) by (rewrite (LEQ8 _ NE_newstr_tok3); exact Lnewstr_a8).
  assert (Lna_a9 : live A9 (Z_to_bv 64 na) = Some 32%Z) by (rewrite (LEQ8 _ NE_na_tok3); exact Lna_a8).
  assert (Larr_a9 : live A9 (Z_to_bv 64 arr) = Some 200%Z) by (rewrite (LEQ8 _ NE_arr_tok3); exact Larr_a8).
  assert (PM9 : POSTM C A0 s m0 m9).
  { eapply POSTM_trans; [exact PM8|]. eapply POSTM_trans; [exact PMs8|]. apply (POSTM_sub C A0 A9 _ _ _ SUB9).
    apply (POSTM_mono C A9 (s + OFF8) s); [unfold OFF8; lia | exact PMc8]. }
  pose proof (RTR8 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM8) ltac:(lia) ltac:(lia)) as RM9. rewrite !Z.sub_0_r in RM9.
  assert (KEPT8 : Forall (ex_region_kept E8 M8 m9) [(EVar 32, OFF8, 0%Z); (EVar 34, 0%Z, 64%Z); (EVar 70, 0%Z, 14%Z); (EVar 104, 0%Z, 32%Z); (EVar 138, 0%Z, 200%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF8 12288 M8 m9 E8 (EVar 32) CK (proj1 PMc8) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A9 A9 m9 _ M8 m9 E8 (EVar 34) pixs 64 CK HW9 Lpixs_a9 RRpixs eq_refl (proj2 PMc8) Lpixs_a9 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A9 A9 m9 _ M8 m9 E8 (EVar 70) newstr 14 CK HW9 Lnewstr_a9 RRnewstr eq_refl (proj2 PMc8) Lnewstr_a9 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A9 A9 m9 _ M8 m9 E8 (EVar 104) na 32 CK HW9 Lna_a9 RRna eq_refl (proj2 PMc8) Lna_a9 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A9 A9 m9 _ M8 m9 E8 (EVar 138) arr 200 CK HW9 Larr_a9 RRarr eq_refl (proj2 PMc8) Larr_a9 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E8 M8 m9 _ [172%nat; 239%nat; 306%nat] _ HKc8 KEPT8) as HKk8.
  match type of HKk8 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E8 m9 kk') in HKk8 end.
  pose proof (regs_ok_agree 308%nat E8 (ex_envL vals8 r9 [exW_canary SEGS 415784 m9]) _ _ (vals_app_agree vals8 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa8.
  pose proof (exW_regs_call _ _ _ _ _ HRa8 (ex_regs_ok_junk vals8 r9 [exW_canary SEGS 415784 m9] 308%nat ltac:(vm_cast_no_check (eq_refl 308%nat))) CS8) as HRn9.
  clear HRa8.
  assert (HKa9 : know_ok SEGS (ex_envL vals8 r9 [exW_canary SEGS 415784 m9]) m9 _) by (exact (know_ok_agree SEGS 308%nat E8 _ m9 _ (vals_app_agree vals8 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk8)).
  rewrite (fr_denot_agree 308%nat E8 (ex_envL vals8 r9 [exW_canary SEGS 415784 m9]) _ fr (vals_app_agree vals8 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc8 HKk8 KEPT8 HC8 HWs8 PMs8 Q10_8 Q1_8 Q2_8 Q4_8 PM8 HW8 PMc8 CS8 SUB8 RM8 Ldead8 LEQ8 RTR8 Ltok3_a8 OFF8 LDEL8 Lpixs_a8 Lnewstr_a8 Lna_a8 Larr_a8.
  subst M8. clear log8. clear E8. try clear Rc8. clear KN8.
  lazymatch type of HRn9 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn9 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A9 m9 _ (s - 12288) (Z.to_nat 12288) CK HW9 GLO1 GLO2) as SOK9.
  pose proof (exW_canary_ok SEGS 415784 m9 (canary_any m9)) as CANOK9.
  pose (vals9 := vals8 ++ map (getr r9) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m9]).
  pose proof (exW_kn_fixed SEGS C A9 m9 _ (ex_envL vals8 r9 [exW_canary SEGS 415784 m9]) (EVar 340) (EVar 32) (exW_canary SEGS 415784 m9) s 12288 415784 65536 212992 213416 213568 213416 213568
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
  assert (WP9 : W C A9 M9 (with_vmmaps vm9 md) /\ POSTM C A0 s m9 M9).
  { subst M9. apply (exW_win_blks C A9 A0 m9 _ E9 log9 (EVar 32) s 12288 [(EVar 70, newstr, 14%Z); (EVar 104, na, 32%Z); (EVar 138, arr, 200%Z)] CK HW9 SUB9 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRnewstr (conj Lnewstr_a9 (conj Fnewstr F0newstr))))|]. constructor; [exact (conj eq_refl (conj RRna (conj Lna_a9 (conj Fna F0na))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a9 (conj Farr F0arr))))|]. constructor. }
  destruct WP9 as [HWs9 PMs9].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log9 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC9 : carry log9 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc9 : know_ok SEGS E9 M9 kn1) by (apply (carry_after SEGS E9 m9 log9 kn0 [] kn1 scs hs HC9 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW9)) | exact (mp_lazy _ (w_pure _ _ _ _ HW9)) | exact Hms |].
  pose (BS9 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, newstr); (104%nat, na); (138%nat, arr)]).
  exW_regfactB BS9 HR ex_r10 Q10_9. exW_regfactB BS9 HR ex_r11 Q11_9. exW_regfactB BS9 HR ex_r1 Q1_9. exW_regfactB BS9 HR ex_r2 Q2_9. exW_regfactB BS9 HR ex_r4 Q4_9.
  clear BS9.
  lazymatch type of Q2_9 with _ = Z_to_bv 64 (s + ?off) => pose (OFF9 := off) end.
  (* [comment removed for export] *)
  pose proof (alloc_margin_small (4 * 1) ltac:(exW_cmp)) as MG9.
  lazymatch type of Q1_9 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_9 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A9 M9 _ Rc9 4 1 (kR - 6) (bR - 6 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs9 Q10_9 Q11_9 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM9) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_9
             ltac:(red; apply bv_eq; reflexivity) Q4_9 Q2_9 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A10 m10 vm10 r10 res9 HW10 Hres9 CSx9 Hnz9 Ftok4x Lo9 F0tok4 LEQ9 ZERO9 ALtok4 TOP9 PMc9 RM10.
  pose proof CSx9 as CS9. clear CSx9.
  rewrite with_vmmaps_twice in HW10 |- *.
  assert (Eres9 : res9 = Z_to_bv 64 (u res9)) by (symmetry; apply zbv_self).
  pose proof (u64_range res9) as RRtok4. set (tok4 := u res9) in *. clearbody tok4. rewrite Eres9 in Hres9, Ftok4x, Lo9, F0tok4, LEQ9, ZERO9. clear Eres9.
  change (4 * 1)%Z with 4%Z in *.
  pose proof (exW_blk_img_apart_h2 C A10 m10 _ tok4 4 CK HW10 Lo9 RRtok4 eq_refl eq_refl) as IMGAPtok4. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPtok4.
  pose proof (exW_win_blk_apart_h C A10 m10 _ s 12288 tok4 4 CK HW10 Lo9 eq_refl RRtok4 GLO1) as WAPtok4.
  assert (Ftok4 : live A0 (Z_to_bv 64 tok4) = None).
  { destruct (live A0 (Z_to_bv 64 tok4)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB9 _ _ EE) as XX. first [discriminate Ftok4x | (rewrite Ftok4x in XX; discriminate XX)]. }
  pose proof Lo9 as Ltok4_a10.
  assert (SUB10 : sub_live A0 A10).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 tok4) by (intros ->; rewrite Ftok4 in Lq; discriminate Lq). rewrite (LEQ9 q NEq). exact (SUB9 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 tok4 :: [Z_to_bv 64 arr; Z_to_bv 64 na; Z_to_bv 64 newstr])) => eq_trans (LEQ9 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL9 q (fun XX => Hq (or_intror XX)))) as LDEL10.
  assert (NE_pixs_tok4 : Z_to_bv 64 pixs <> Z_to_bv 64 tok4) by (intros EE; rewrite EE in Lpixs_a9; rewrite Ftok4x in Lpixs_a9; discriminate Lpixs_a9).
  assert (Lpixs_a10 : live A10 (Z_to_bv 64 pixs) = Some 64%Z) by (rewrite (LEQ9 _ NE_pixs_tok4); exact Lpixs_a9).
  pose proof (exW_blk_apart_h C A10 m10 _ pixs tok4 64 4 CK HW10 Lpixs_a10 Ltok4_a10 NE_pixs_tok4 RRpixs RRtok4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_pixs_tok4.
  assert (NE_newstr_tok4 : Z_to_bv 64 newstr <> Z_to_bv 64 tok4) by (intros EE; rewrite EE in Lnewstr_a9; rewrite Ftok4x in Lnewstr_a9; discriminate Lnewstr_a9).
  assert (Lnewstr_a10 : live A10 (Z_to_bv 64 newstr) = Some 14%Z) by (rewrite (LEQ9 _ NE_newstr_tok4); exact Lnewstr_a9).
  pose proof (exW_blk_apart_h C A10 m10 _ newstr tok4 14 4 CK HW10 Lnewstr_a10 Ltok4_a10 NE_newstr_tok4 RRnewstr RRtok4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_newstr_tok4.
  assert (NE_na_tok4 : Z_to_bv 64 na <> Z_to_bv 64 tok4) by (intros EE; rewrite EE in Lna_a9; rewrite Ftok4x in Lna_a9; discriminate Lna_a9).
  assert (Lna_a10 : live A10 (Z_to_bv 64 na) = Some 32%Z) by (rewrite (LEQ9 _ NE_na_tok4); exact Lna_a9).
  pose proof (exW_blk_apart_h C A10 m10 _ na tok4 32 4 CK HW10 Lna_a10 Ltok4_a10 NE_na_tok4 RRna RRtok4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_na_tok4.
  assert (NE_arr_tok4 : Z_to_bv 64 arr <> Z_to_bv 64 tok4) by (intros EE; rewrite EE in Larr_a9; rewrite Ftok4x in Larr_a9; discriminate Larr_a9).
  assert (Larr_a10 : live A10 (Z_to_bv 64 arr) = Some 200%Z) by (rewrite (LEQ9 _ NE_arr_tok4); exact Larr_a9).
  pose proof (exW_blk_apart_h C A10 m10 _ arr tok4 200 4 CK HW10 Larr_a10 Ltok4_a10 NE_arr_tok4 RRarr RRtok4 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_tok4.
  assert (PM10 : POSTM C A0 s m0 m10).
  { eapply POSTM_trans; [exact PM9|]. eapply POSTM_trans; [exact PMs9|]. apply (POSTM_sub C A0 A9 _ _ _ SUB9).
    apply (POSTM_mono C A9 (s + OFF9) s); [unfold OFF9; lia | exact PMc9]. }
  replace (kR - 6 - 1)%Z with (kR - 7)%Z in RM10 by lia. rewrite MG9 in RM10. replace (bR - 6 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 7 * 2 ^ 17)%Z in RM10 by lia.
  assert (KEPT9 : Forall (ex_region_kept E9 M9 m10) [(EVar 32, OFF9, 0%Z); (EVar 34, 0%Z, 64%Z); (EVar 70, 0%Z, 14%Z); (EVar 104, 0%Z, 32%Z); (EVar 138, 0%Z, 200%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF9 12288 M9 m10 E9 (EVar 32) CK (proj1 PMc9) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A9 A9 M9 _ M9 m10 E9 (EVar 34) pixs 64 CK HWs9 Lpixs_a9 RRpixs eq_refl (proj2 PMc9) Lpixs_a9 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A9 A9 M9 _ M9 m10 E9 (EVar 70) newstr 14 CK HWs9 Lnewstr_a9 RRnewstr eq_refl (proj2 PMc9) Lnewstr_a9 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A9 A9 M9 _ M9 m10 E9 (EVar 104) na 32 CK HWs9 Lna_a9 RRna eq_refl (proj2 PMc9) Lna_a9 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A9 A9 M9 _ M9 m10 E9 (EVar 138) arr 200 CK HWs9 Larr_a9 RRarr eq_refl (proj2 PMc9) Larr_a9 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E9 M9 m10 _ [172%nat; 239%nat; 306%nat] _ HKc9 KEPT9) as HKk9.
  match type of HKk9 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E9 m10 kk') in HKk9 end.
  pose proof (regs_ok_agree 341%nat E9 (ex_envL vals9 r10 [tok4; exW_canary SEGS 415784 m10]) _ _ (vals_app_agree vals9 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa9.
  pose proof (exW_regs_call _ _ _ _ _ HRa9 (ex_regs_ok_junk vals9 r10 [tok4; exW_canary SEGS 415784 m10] 341%nat ltac:(vm_cast_no_check (eq_refl 341%nat))) CS9) as HRn10.
  clear HRa9.
  assert (HKa10 : know_ok SEGS (ex_envL vals9 r10 [tok4; exW_canary SEGS 415784 m10]) m10 _) by (exact (know_ok_agree SEGS 341%nat E9 _ m10 _ (vals_app_agree vals9 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk9)).
  rewrite (fr_denot_agree 341%nat E9 (ex_envL vals9 r10 [tok4; exW_canary SEGS 415784 m10]) _ fr (vals_app_agree vals9 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r10 ex_r10 (EVar 373) HRn10 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres9)) as HRx10. clear HRn10. rename HRx10 into HRn10.
  clear HR HK Hlf Hms HKc9 HKk9 KEPT9 HC9 HWs9 PMs9 Q10_9 Q11_9 Q1_9 Q2_9 Q4_9 PM9 HW9 PMc9 CS9 SUB9 RM9 MG9 TOP9 LEQ9 Hnz9 Ftok4x Lo9 OFF9 LDEL9 Lpixs_a9 Lnewstr_a9 Lna_a9 Larr_a9.
  subst M9. clear log9. clear E9. try clear Rc9. clear KN9.
  lazymatch type of HRn10 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn10 end.
  pose proof (exW_kn_blk SEGS C A10 m10 _ (ex_envL vals9 r10 [tok4; exW_canary SEGS 415784 m10]) (EVar 373) (EVar 32) tok4 4 s 12288 65536 356352 p16_segs CK HW10 Ltok4_a10 RRtok4 eq_refl eq_refl eq_refl RS ALtok4 ZERO9 WAPtok4 IMGAPtok4) as HKb10.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals9 r10 [tok4; exW_canary SEGS 415784 m10]) m10) _ _ (ex_kdisj_apart SEGS (ex_envL vals9 r10 [tok4; exW_canary SEGS 415784 m10]) m10 (EVar 34) (EVar 373) pixs tok4 0 64 0 4 eq_refl eq_refl RRpixs RRtok4 AP_pixs_tok4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals9 r10 [tok4; exW_canary SEGS 415784 m10]) m10) _ _ (ex_kdisj_apart SEGS (ex_envL vals9 r10 [tok4; exW_canary SEGS 415784 m10]) m10 (EVar 70) (EVar 373) newstr tok4 0 14 0 4 eq_refl eq_refl RRnewstr RRtok4 AP_newstr_tok4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals9 r10 [tok4; exW_canary SEGS 415784 m10]) m10) _ _ (ex_kdisj_apart SEGS (ex_envL vals9 r10 [tok4; exW_canary SEGS 415784 m10]) m10 (EVar 104) (EVar 373) na tok4 0 32 0 4 eq_refl eq_refl RRna RRtok4 AP_na_tok4) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals9 r10 [tok4; exW_canary SEGS 415784 m10]) m10) _ _ (ex_kdisj_apart SEGS (ex_envL vals9 r10 [tok4; exW_canary SEGS 415784 m10]) m10 (EVar 138) (EVar 373) arr tok4 0 200 0 4 eq_refl eq_refl RRarr RRtok4 AP_arr_tok4) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals9 r10 [tok4; exW_canary SEGS 415784 m10]) m10)))))) as HKd10.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A10 m10 _ (s - 12288) (Z.to_nat 12288) CK HW10 GLO1 GLO2) as SOK10.
  pose proof (exW_canary_ok SEGS 415784 m10 (canary_any m10)) as CANOK10.
  pose (vals10 := vals9 ++ map (getr r10) ex_regs_list ++ map (Z_to_bv 64) [tok4; exW_canary SEGS 415784 m10]).
  pose proof (exW_kn_fixed SEGS C A10 m10 _ (ex_envL vals9 r10 [tok4; exW_canary SEGS 415784 m10]) (EVar 374) (EVar 32) (exW_canary SEGS 415784 m10) s 12288 415784 65536 212992 213416 213568 213416 213568
                HW10 eq_refl (proj1 CANOK10) (proj2 CANOK10) eq_refl eq_refl eq_refl SOK10 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf10.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb10 (proj2 (Forall_app _ _ _) (conj HKd10 (proj2 (Forall_app _ _ _) (conj HKf10 HKa10)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn10 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN10 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb10 HKd10 HKf10 HKa10 SOK10 CANOK10.
  repeat match goal with H : getr r10 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO9 ALtok4.
  (* [comment removed for export] *)
  exb_exit ST Rc10 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E10 := EEx) in HR, Hlf, HK, Hms |- *; set (log10 := LLx) in Hms, Hlf; set (M10 := mem_denot E10 m10 log10) in Hms end.
  assert (WP10 : W C A10 M10 (with_vmmaps vm10 md) /\ POSTM C A0 s m10 M10).
  { subst M10. apply (exW_win_blks C A10 A0 m10 _ E10 log10 (EVar 32) s 12288 [(EVar 70, newstr, 14%Z); (EVar 104, na, 32%Z); (EVar 138, arr, 200%Z); (EVar 373, tok4, 4%Z)] CK HW10 SUB10 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRnewstr (conj Lnewstr_a10 (conj Fnewstr F0newstr))))|]. constructor; [exact (conj eq_refl (conj RRna (conj Lna_a10 (conj Fna F0na))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a10 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRtok4 (conj Ltok4_a10 (conj Ftok4 F0tok4))))|]. constructor. }
  destruct WP10 as [HWs10 PMs10].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log10 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC10 : carry log10 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc10 : know_ok SEGS E10 M10 kn1) by (apply (carry_after SEGS E10 m10 log10 kn0 [] kn1 scs hs HC10 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW10)) | exact (mp_lazy _ (w_pure _ _ _ _ HW10)) | exact Hms |].
  pose (BS10 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, newstr); (104%nat, na); (138%nat, arr); (373%nat, tok4)]).
  exW_regfactB BS10 HR ex_r10 Q10_10. exW_regfactB BS10 HR ex_r1 Q1_10. exW_regfactB BS10 HR ex_r2 Q2_10. exW_regfactB BS10 HR ex_r4 Q4_10.
  clear BS10.
  lazymatch type of Q2_10 with _ = Z_to_bv 64 (s + ?off) => pose (OFF10 := off) end.
  (* [comment removed for export] *)
  lazymatch type of Q1_10 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_10 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A10 M10 _ Rc10 (Z_to_bv 64 tok4) (Z_to_bv 64 ret) 4 sp' S CK HWs10 Q10_10 Ltok4_a10 F0tok4 Q1_10
             ltac:(red; apply bv_eq; reflexivity) Q4_10 Q2_10 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A11 m11 vm11 r11 HW11 CSx10 Ldead10 LEQ10 PMc10 RTR10.
  pose proof CSx10 as CS10. clear CSx10.
  rewrite with_vmmaps_twice in HW11 |- *.
  assert (SUB11 : sub_live A0 A11).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 tok4) by (intros ->; rewrite Ftok4 in Lq; discriminate Lq). rewrite (LEQ10 q NEq). exact (SUB10 q kq Lq). }
  assert (LDEL11 : forall q : word, ~ In q [Z_to_bv 64 arr; Z_to_bv 64 na; Z_to_bv 64 newstr] -> live A11 q = live A0 q).
  { intros q Hq. destruct (decide (Z_to_bv 64 tok4 = q)) as [<-|NEq]; [rewrite Ldead10, Ftok4; reflexivity|]. rewrite (LEQ10 q (fun EE => NEq (eq_sym EE))). apply LDEL10. clear - Hq NEq. cbn [In] in *. tauto. }
  assert (Lpixs_a11 : live A11 (Z_to_bv 64 pixs) = Some 64%Z) by (rewrite (LEQ10 _ NE_pixs_tok4); exact Lpixs_a10).
  assert (Lnewstr_a11 : live A11 (Z_to_bv 64 newstr) = Some 14%Z) by (rewrite (LEQ10 _ NE_newstr_tok4); exact Lnewstr_a10).
  assert (Lna_a11 : live A11 (Z_to_bv 64 na) = Some 32%Z) by (rewrite (LEQ10 _ NE_na_tok4); exact Lna_a10).
  assert (Larr_a11 : live A11 (Z_to_bv 64 arr) = Some 200%Z) by (rewrite (LEQ10 _ NE_arr_tok4); exact Larr_a10).
  assert (PM11 : POSTM C A0 s m0 m11).
  { eapply POSTM_trans; [exact PM10|]. eapply POSTM_trans; [exact PMs10|]. apply (POSTM_sub C A0 A11 _ _ _ SUB11).
    apply (POSTM_mono C A11 (s + OFF10) s); [unfold OFF10; lia | exact PMc10]. }
  pose proof (RTR10 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM10) ltac:(lia) ltac:(lia)) as RM11. rewrite !Z.sub_0_r in RM11.
  assert (KEPT10 : Forall (ex_region_kept E10 M10 m11) [(EVar 32, OFF10, 0%Z); (EVar 34, 0%Z, 64%Z); (EVar 70, 0%Z, 14%Z); (EVar 104, 0%Z, 32%Z); (EVar 138, 0%Z, 200%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF10 12288 M10 m11 E10 (EVar 32) CK (proj1 PMc10) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A11 A11 m11 _ M10 m11 E10 (EVar 34) pixs 64 CK HW11 Lpixs_a11 RRpixs eq_refl (proj2 PMc10) Lpixs_a11 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A11 A11 m11 _ M10 m11 E10 (EVar 70) newstr 14 CK HW11 Lnewstr_a11 RRnewstr eq_refl (proj2 PMc10) Lnewstr_a11 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A11 A11 m11 _ M10 m11 E10 (EVar 104) na 32 CK HW11 Lna_a11 RRna eq_refl (proj2 PMc10) Lna_a11 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A11 A11 m11 _ M10 m11 E10 (EVar 138) arr 200 CK HW11 Larr_a11 RRarr eq_refl (proj2 PMc10) Larr_a11 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E10 M10 m11 _ [172%nat; 239%nat; 306%nat; 373%nat] _ HKc10 KEPT10) as HKk10.
  match type of HKk10 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E10 m11 kk') in HKk10 end.
  pose proof (regs_ok_agree 375%nat E10 (ex_envL vals10 r11 [exW_canary SEGS 415784 m11]) _ _ (vals_app_agree vals10 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa10.
  pose proof (exW_regs_call _ _ _ _ _ HRa10 (ex_regs_ok_junk vals10 r11 [exW_canary SEGS 415784 m11] 375%nat ltac:(vm_cast_no_check (eq_refl 375%nat))) CS10) as HRn11.
  clear HRa10.
  assert (HKa11 : know_ok SEGS (ex_envL vals10 r11 [exW_canary SEGS 415784 m11]) m11 _) by (exact (know_ok_agree SEGS 375%nat E10 _ m11 _ (vals_app_agree vals10 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk10)).
  rewrite (fr_denot_agree 375%nat E10 (ex_envL vals10 r11 [exW_canary SEGS 415784 m11]) _ fr (vals_app_agree vals10 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc10 HKk10 KEPT10 HC10 HWs10 PMs10 Q10_10 Q1_10 Q2_10 Q4_10 PM10 HW10 PMc10 CS10 SUB10 RM10 Ldead10 LEQ10 RTR10 Ltok4_a10 OFF10 LDEL10 Lpixs_a10 Lnewstr_a10 Lna_a10 Larr_a10.
  subst M10. clear log10. clear E10. try clear Rc10. clear KN10.
  lazymatch type of HRn11 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn11 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A11 m11 _ (s - 12288) (Z.to_nat 12288) CK HW11 GLO1 GLO2) as SOK11.
  pose proof (exW_canary_ok SEGS 415784 m11 (canary_any m11)) as CANOK11.
  pose (vals11 := vals10 ++ map (getr r11) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m11]).
  pose proof (exW_kn_fixed SEGS C A11 m11 _ (ex_envL vals10 r11 [exW_canary SEGS 415784 m11]) (EVar 407) (EVar 32) (exW_canary SEGS 415784 m11) s 12288 415784 65536 212992 213416 213568 213416 213568
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
  assert (WP11 : W C A11 M11 (with_vmmaps vm11 md) /\ POSTM C A0 s m11 M11).
  { subst M11. apply (exW_win_blks C A11 A0 m11 _ E11 log11 (EVar 32) s 12288 [(EVar 70, newstr, 14%Z); (EVar 104, na, 32%Z); (EVar 138, arr, 200%Z)] CK HW11 SUB11 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRnewstr (conj Lnewstr_a11 (conj Fnewstr F0newstr))))|]. constructor; [exact (conj eq_refl (conj RRna (conj Lna_a11 (conj Fna F0na))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a11 (conj Farr F0arr))))|]. constructor. }
  destruct WP11 as [HWs11 PMs11].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log11 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC11 : carry log11 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc11 : know_ok SEGS E11 M11 kn1) by (apply (carry_after SEGS E11 m11 log11 kn0 [] kn1 scs hs HC11 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW11)) | exact (mp_lazy _ (w_pure _ _ _ _ HW11)) | exact Hms |].
  pose (BS11 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (70%nat, newstr); (104%nat, na); (138%nat, arr)]).
  exW_regfactB BS11 HR ex_r10 Q10_11. exW_regfactB BS11 HR ex_r1 Q1_11. exW_regfactB BS11 HR ex_r2 Q2_11. exW_regfactB BS11 HR ex_r4 Q4_11.
  clear BS11.
  lazymatch type of Q2_11 with _ = Z_to_bv 64 (s + ?off) => pose (OFF11 := off) end.
  (* [comment removed for export] *)
  lazymatch type of Q1_11 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_11 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A11 M11 _ Rc11 (Z_to_bv 64 newstr) (Z_to_bv 64 ret) 14 sp' S CK HWs11 Q10_11 Lnewstr_a11 F0newstr Q1_11
             ltac:(red; apply bv_eq; reflexivity) Q4_11 Q2_11 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A12 m12 vm12 r12 HW12 CSx11 Ldead11 LEQ11 PMc11 RTR11.
  pose proof CSx11 as CS11. clear CSx11.
  rewrite with_vmmaps_twice in HW12 |- *.
  assert (SUB12 : sub_live A0 A12).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 newstr) by (intros ->; rewrite Fnewstr in Lq; discriminate Lq). rewrite (LEQ11 q NEq). exact (SUB11 q kq Lq). }
  assert (LDEL12 : forall q : word, ~ In q [Z_to_bv 64 arr; Z_to_bv 64 na] -> live A12 q = live A0 q).
  { intros q Hq. destruct (decide (Z_to_bv 64 newstr = q)) as [<-|NEq]; [rewrite Ldead11, Fnewstr; reflexivity|]. rewrite (LEQ11 q (fun EE => NEq (eq_sym EE))). apply LDEL11. clear - Hq NEq. cbn [In] in *. tauto. }
  assert (Lpixs_a12 : live A12 (Z_to_bv 64 pixs) = Some 64%Z) by (rewrite (LEQ11 _ NE_pixs_newstr); exact Lpixs_a11).
  assert (Lna_a12 : live A12 (Z_to_bv 64 na) = Some 32%Z) by (rewrite (LEQ11 _ (fun EE => NE_newstr_na (eq_sym EE))); exact Lna_a11).
  assert (Larr_a12 : live A12 (Z_to_bv 64 arr) = Some 200%Z) by (rewrite (LEQ11 _ (fun EE => NE_newstr_arr (eq_sym EE))); exact Larr_a11).
  assert (PM12 : POSTM C A0 s m0 m12).
  { eapply POSTM_trans; [exact PM11|]. eapply POSTM_trans; [exact PMs11|]. apply (POSTM_sub C A0 A12 _ _ _ SUB12).
    apply (POSTM_mono C A12 (s + OFF11) s); [unfold OFF11; lia | exact PMc11]. }
  pose proof (RTR11 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM11) ltac:(lia) ltac:(lia)) as RM12. rewrite !Z.sub_0_r in RM12.
  assert (KEPT11 : Forall (ex_region_kept E11 M11 m12) [(EVar 32, OFF11, 0%Z); (EVar 34, 0%Z, 64%Z); (EVar 104, 0%Z, 32%Z); (EVar 138, 0%Z, 200%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF11 12288 M11 m12 E11 (EVar 32) CK (proj1 PMc11) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A12 A12 m12 _ M11 m12 E11 (EVar 34) pixs 64 CK HW12 Lpixs_a12 RRpixs eq_refl (proj2 PMc11) Lpixs_a12 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A12 A12 m12 _ M11 m12 E11 (EVar 104) na 32 CK HW12 Lna_a12 RRna eq_refl (proj2 PMc11) Lna_a12 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A12 A12 m12 _ M11 m12 E11 (EVar 138) arr 200 CK HW12 Larr_a12 RRarr eq_refl (proj2 PMc11) Larr_a12 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E11 M11 m12 _ [172%nat; 239%nat; 306%nat; 373%nat; 70%nat] _ HKc11 KEPT11) as HKk11.
  match type of HKk11 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E11 m12 kk') in HKk11 end.
  pose proof (regs_ok_agree 408%nat E11 (ex_envL vals11 r12 [exW_canary SEGS 415784 m12]) _ _ (vals_app_agree vals11 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa11.
  pose proof (exW_regs_call _ _ _ _ _ HRa11 (ex_regs_ok_junk vals11 r12 [exW_canary SEGS 415784 m12] 408%nat ltac:(vm_cast_no_check (eq_refl 408%nat))) CS11) as HRn12.
  clear HRa11.
  assert (HKa12 : know_ok SEGS (ex_envL vals11 r12 [exW_canary SEGS 415784 m12]) m12 _) by (exact (know_ok_agree SEGS 408%nat E11 _ m12 _ (vals_app_agree vals11 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk11)).
  rewrite (fr_denot_agree 408%nat E11 (ex_envL vals11 r12 [exW_canary SEGS 415784 m12]) _ fr (vals_app_agree vals11 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc11 HKk11 KEPT11 HC11 HWs11 PMs11 Q10_11 Q1_11 Q2_11 Q4_11 PM11 HW11 PMc11 CS11 SUB11 RM11 Ldead11 LEQ11 RTR11 Lnewstr_a11 OFF11 LDEL11 Lpixs_a11 Lna_a11 Larr_a11.
  subst M11. clear log11. clear E11. try clear Rc11. clear KN11.
  lazymatch type of HRn12 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn12 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A12 m12 _ (s - 12288) (Z.to_nat 12288) CK HW12 GLO1 GLO2) as SOK12.
  pose proof (exW_canary_ok SEGS 415784 m12 (canary_any m12)) as CANOK12.
  pose (vals12 := vals11 ++ map (getr r12) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m12]).
  pose proof (exW_kn_fixed SEGS C A12 m12 _ (ex_envL vals11 r12 [exW_canary SEGS 415784 m12]) (EVar 440) (EVar 32) (exW_canary SEGS 415784 m12) s 12288 415784 65536 212992 213416 213568 213416 213568
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
  assert (WP12 : W C A12 M12 (with_vmmaps vm12 md) /\ POSTM C A0 s m12 M12).
  { subst M12. apply (exW_win_blks C A12 A0 m12 _ E12 log12 (EVar 32) s 12288 [(EVar 104, na, 32%Z); (EVar 138, arr, 200%Z)] CK HW12 SUB12 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRna (conj Lna_a12 (conj Fna F0na))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a12 (conj Farr F0arr))))|]. constructor. }
  destruct WP12 as [HWs12 PMs12].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log12 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC12 : carry log12 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc12 : know_ok SEGS E12 M12 kn1) by (apply (carry_after SEGS E12 m12 log12 kn0 [] kn1 scs hs HC12 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW12)) | exact (mp_lazy _ (w_pure _ _ _ _ HW12)) | exact Hms |].
  pose (BS12 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (104%nat, na); (138%nat, arr)]).
  exW_regfactB BS12 HR ex_r10 Q10_12. exW_regfactB BS12 HR ex_r11 Q11_12. exW_regfactB BS12 HR ex_r1 Q1_12. exW_regfactB BS12 HR ex_r2 Q2_12. exW_regfactB BS12 HR ex_r4 Q4_12.
  clear BS12.
  lazymatch type of Q2_12 with _ = Z_to_bv 64 (s + ?off) => pose (OFF12 := off) end.
  (* [comment removed for export] *)
  pose proof (alloc_margin_small (1 * 24) ltac:(exW_cmp)) as MG12.
  lazymatch type of Q1_12 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_12 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A12 M12 _ Rc12 1 24 (kR - 7) (bR - 7 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs12 Q10_12 Q11_12 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM12) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_12
             ltac:(red; apply bv_eq; reflexivity) Q4_12 Q2_12 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A13 m13 vm13 r13 res12 HW13 Hres12 CSx12 Hnz12 Fcmapx Lo12 F0cmap LEQ12 ZERO12 ALcmap TOP12 PMc12 RM13.
  pose proof CSx12 as CS12. clear CSx12.
  rewrite with_vmmaps_twice in HW13 |- *.
  assert (Eres12 : res12 = Z_to_bv 64 (u res12)) by (symmetry; apply zbv_self).
  pose proof (u64_range res12) as RRcmap. set (cmap := u res12) in *. clearbody cmap. rewrite Eres12 in Hres12, Fcmapx, Lo12, F0cmap, LEQ12, ZERO12. clear Eres12.
  change (1 * 24)%Z with 24%Z in *.
  pose proof (exW_blk_img_apart_h2 C A13 m13 _ cmap 24 CK HW13 Lo12 RRcmap eq_refl eq_refl) as IMGAPcmap. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPcmap.
  pose proof (exW_win_blk_apart_h C A13 m13 _ s 12288 cmap 24 CK HW13 Lo12 eq_refl RRcmap GLO1) as WAPcmap.
  assert (Fcmap : live A0 (Z_to_bv 64 cmap) = None).
  { destruct (live A0 (Z_to_bv 64 cmap)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB12 _ _ EE) as XX. first [discriminate Fcmapx | (rewrite Fcmapx in XX; discriminate XX)]. }
  pose proof Lo12 as Lcmap_a13.
  assert (SUB13 : sub_live A0 A13).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 cmap) by (intros ->; rewrite Fcmap in Lq; discriminate Lq). rewrite (LEQ12 q NEq). exact (SUB12 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 cmap :: [Z_to_bv 64 arr; Z_to_bv 64 na])) => eq_trans (LEQ12 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL12 q (fun XX => Hq (or_intror XX)))) as LDEL13.
  assert (NE_pixs_cmap : Z_to_bv 64 pixs <> Z_to_bv 64 cmap) by (intros EE; rewrite EE in Lpixs_a12; rewrite Fcmapx in Lpixs_a12; discriminate Lpixs_a12).
  assert (Lpixs_a13 : live A13 (Z_to_bv 64 pixs) = Some 64%Z) by (rewrite (LEQ12 _ NE_pixs_cmap); exact Lpixs_a12).
  pose proof (exW_blk_apart_h C A13 m13 _ pixs cmap 64 24 CK HW13 Lpixs_a13 Lcmap_a13 NE_pixs_cmap RRpixs RRcmap ltac:(exW_cmp) ltac:(exW_cmp)) as AP_pixs_cmap.
  assert (NE_na_cmap : Z_to_bv 64 na <> Z_to_bv 64 cmap) by (intros EE; rewrite EE in Lna_a12; rewrite Fcmapx in Lna_a12; discriminate Lna_a12).
  assert (Lna_a13 : live A13 (Z_to_bv 64 na) = Some 32%Z) by (rewrite (LEQ12 _ NE_na_cmap); exact Lna_a12).
  pose proof (exW_blk_apart_h C A13 m13 _ na cmap 32 24 CK HW13 Lna_a13 Lcmap_a13 NE_na_cmap RRna RRcmap ltac:(exW_cmp) ltac:(exW_cmp)) as AP_na_cmap.
  assert (NE_arr_cmap : Z_to_bv 64 arr <> Z_to_bv 64 cmap) by (intros EE; rewrite EE in Larr_a12; rewrite Fcmapx in Larr_a12; discriminate Larr_a12).
  assert (Larr_a13 : live A13 (Z_to_bv 64 arr) = Some 200%Z) by (rewrite (LEQ12 _ NE_arr_cmap); exact Larr_a12).
  pose proof (exW_blk_apart_h C A13 m13 _ arr cmap 200 24 CK HW13 Larr_a13 Lcmap_a13 NE_arr_cmap RRarr RRcmap ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_cmap.
  assert (PM13 : POSTM C A0 s m0 m13).
  { eapply POSTM_trans; [exact PM12|]. eapply POSTM_trans; [exact PMs12|]. apply (POSTM_sub C A0 A12 _ _ _ SUB12).
    apply (POSTM_mono C A12 (s + OFF12) s); [unfold OFF12; lia | exact PMc12]. }
  replace (kR - 7 - 1)%Z with (kR - 8)%Z in RM13 by lia. rewrite MG12 in RM13. replace (bR - 7 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 8 * 2 ^ 17)%Z in RM13 by lia.
  assert (KEPT12 : Forall (ex_region_kept E12 M12 m13) [(EVar 32, OFF12, 0%Z); (EVar 34, 0%Z, 64%Z); (EVar 104, 0%Z, 32%Z); (EVar 138, 0%Z, 200%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF12 12288 M12 m13 E12 (EVar 32) CK (proj1 PMc12) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A12 A12 M12 _ M12 m13 E12 (EVar 34) pixs 64 CK HWs12 Lpixs_a12 RRpixs eq_refl (proj2 PMc12) Lpixs_a12 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A12 A12 M12 _ M12 m13 E12 (EVar 104) na 32 CK HWs12 Lna_a12 RRna eq_refl (proj2 PMc12) Lna_a12 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A12 A12 M12 _ M12 m13 E12 (EVar 138) arr 200 CK HWs12 Larr_a12 RRarr eq_refl (proj2 PMc12) Larr_a12 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E12 M12 m13 _ [172%nat; 239%nat; 306%nat; 373%nat; 70%nat] _ HKc12 KEPT12) as HKk12.
  match type of HKk12 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E12 m13 kk') in HKk12 end.
  pose proof (regs_ok_agree 441%nat E12 (ex_envL vals12 r13 [cmap; exW_canary SEGS 415784 m13]) _ _ (vals_app_agree vals12 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa12.
  pose proof (exW_regs_call _ _ _ _ _ HRa12 (ex_regs_ok_junk vals12 r13 [cmap; exW_canary SEGS 415784 m13] 441%nat ltac:(vm_cast_no_check (eq_refl 441%nat))) CS12) as HRn13.
  clear HRa12.
  assert (HKa13 : know_ok SEGS (ex_envL vals12 r13 [cmap; exW_canary SEGS 415784 m13]) m13 _) by (exact (know_ok_agree SEGS 441%nat E12 _ m13 _ (vals_app_agree vals12 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk12)).
  rewrite (fr_denot_agree 441%nat E12 (ex_envL vals12 r13 [cmap; exW_canary SEGS 415784 m13]) _ fr (vals_app_agree vals12 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r13 ex_r10 (EVar 473) HRn13 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres12)) as HRx13. clear HRn13. rename HRx13 into HRn13.
  clear HR HK Hlf Hms HKc12 HKk12 KEPT12 HC12 HWs12 PMs12 Q10_12 Q11_12 Q1_12 Q2_12 Q4_12 PM12 HW12 PMc12 CS12 SUB12 RM12 MG12 TOP12 LEQ12 Hnz12 Fcmapx Lo12 OFF12 LDEL12 Lpixs_a12 Lna_a12 Larr_a12.
  subst M12. clear log12. clear E12. try clear Rc12. clear KN12.
  lazymatch type of HRn13 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn13 end.
  pose proof (exW_kn_blk SEGS C A13 m13 _ (ex_envL vals12 r13 [cmap; exW_canary SEGS 415784 m13]) (EVar 473) (EVar 32) cmap 24 s 12288 65536 356352 p16_segs CK HW13 Lcmap_a13 RRcmap eq_refl eq_refl eq_refl RS ALcmap ZERO12 WAPcmap IMGAPcmap) as HKb13.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals12 r13 [cmap; exW_canary SEGS 415784 m13]) m13) _ _ (ex_kdisj_apart SEGS (ex_envL vals12 r13 [cmap; exW_canary SEGS 415784 m13]) m13 (EVar 34) (EVar 473) pixs cmap 0 64 0 24 eq_refl eq_refl RRpixs RRcmap AP_pixs_cmap) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals12 r13 [cmap; exW_canary SEGS 415784 m13]) m13) _ _ (ex_kdisj_apart SEGS (ex_envL vals12 r13 [cmap; exW_canary SEGS 415784 m13]) m13 (EVar 104) (EVar 473) na cmap 0 32 0 24 eq_refl eq_refl RRna RRcmap AP_na_cmap) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals12 r13 [cmap; exW_canary SEGS 415784 m13]) m13) _ _ (ex_kdisj_apart SEGS (ex_envL vals12 r13 [cmap; exW_canary SEGS 415784 m13]) m13 (EVar 138) (EVar 473) arr cmap 0 200 0 24 eq_refl eq_refl RRarr RRcmap AP_arr_cmap) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals12 r13 [cmap; exW_canary SEGS 415784 m13]) m13))))) as HKd13.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A13 m13 _ (s - 12288) (Z.to_nat 12288) CK HW13 GLO1 GLO2) as SOK13.
  pose proof (exW_canary_ok SEGS 415784 m13 (canary_any m13)) as CANOK13.
  pose (vals13 := vals12 ++ map (getr r13) ex_regs_list ++ map (Z_to_bv 64) [cmap; exW_canary SEGS 415784 m13]).
  pose proof (exW_kn_fixed SEGS C A13 m13 _ (ex_envL vals12 r13 [cmap; exW_canary SEGS 415784 m13]) (EVar 474) (EVar 32) (exW_canary SEGS 415784 m13) s 12288 415784 65536 212992 213416 213568 213416 213568
                HW13 eq_refl (proj1 CANOK13) (proj2 CANOK13) eq_refl eq_refl eq_refl SOK13 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf13.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb13 (proj2 (Forall_app _ _ _) (conj HKd13 (proj2 (Forall_app _ _ _) (conj HKf13 HKa13)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn13 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN13 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb13 HKd13 HKf13 HKa13 SOK13 CANOK13.
  repeat match goal with H : getr r13 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO12 ALcmap.
  (* [comment removed for export] *)
  exb_exit ST Rc13 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E13 := EEx) in HR, Hlf, HK, Hms |- *; set (log13 := LLx) in Hms, Hlf; set (M13 := mem_denot E13 m13 log13) in Hms end.
  assert (WP13 : W C A13 M13 (with_vmmaps vm13 md) /\ POSTM C A0 s m13 M13).
  { subst M13. apply (exW_win_blks C A13 A0 m13 _ E13 log13 (EVar 32) s 12288 [(EVar 104, na, 32%Z); (EVar 138, arr, 200%Z); (EVar 473, cmap, 24%Z)] CK HW13 SUB13 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRna (conj Lna_a13 (conj Fna F0na))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a13 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRcmap (conj Lcmap_a13 (conj Fcmap F0cmap))))|]. constructor. }
  destruct WP13 as [HWs13 PMs13].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log13 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC13 : carry log13 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc13 : know_ok SEGS E13 M13 kn1) by (apply (carry_after SEGS E13 m13 log13 kn0 [] kn1 scs hs HC13 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW13)) | exact (mp_lazy _ (w_pure _ _ _ _ HW13)) | exact Hms |].
  pose (BS13 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (104%nat, na); (138%nat, arr); (473%nat, cmap)]).
  exW_regfactB BS13 HR ex_r10 Q10_13. exW_regfactB BS13 HR ex_r11 Q11_13. exW_regfactB BS13 HR ex_r1 Q1_13. exW_regfactB BS13 HR ex_r2 Q2_13. exW_regfactB BS13 HR ex_r4 Q4_13.
  clear BS13.
  lazymatch type of Q2_13 with _ = Z_to_bv 64 (s + ?off) => pose (OFF13 := off) end.
  (* [comment removed for export] *)
  pose proof (alloc_margin_small (256 * 4) ltac:(exW_cmp)) as MG13.
  lazymatch type of Q1_13 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_13 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A13 M13 _ Rc13 256 4 (kR - 8) (bR - 8 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs13 Q10_13 Q11_13 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM13) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_13
             ltac:(red; apply bv_eq; reflexivity) Q4_13 Q2_13 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A14 m14 vm14 r14 res13 HW14 Hres13 CSx13 Hnz13 Fcmaparrx Lo13 F0cmaparr LEQ13 ZERO13 ALcmaparr TOP13 PMc13 RM14.
  pose proof CSx13 as CS13. clear CSx13.
  rewrite with_vmmaps_twice in HW14 |- *.
  assert (Eres13 : res13 = Z_to_bv 64 (u res13)) by (symmetry; apply zbv_self).
  pose proof (u64_range res13) as RRcmaparr. set (cmaparr := u res13) in *. clearbody cmaparr. rewrite Eres13 in Hres13, Fcmaparrx, Lo13, F0cmaparr, LEQ13, ZERO13. clear Eres13.
  change (256 * 4)%Z with 1024%Z in *.
  pose proof (exW_blk_img_apart_h2 C A14 m14 _ cmaparr 1024 CK HW14 Lo13 RRcmaparr eq_refl eq_refl) as IMGAPcmaparr. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPcmaparr.
  pose proof (exW_win_blk_apart_h C A14 m14 _ s 12288 cmaparr 1024 CK HW14 Lo13 eq_refl RRcmaparr GLO1) as WAPcmaparr.
  assert (Fcmaparr : live A0 (Z_to_bv 64 cmaparr) = None).
  { destruct (live A0 (Z_to_bv 64 cmaparr)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB13 _ _ EE) as XX. first [discriminate Fcmaparrx | (rewrite Fcmaparrx in XX; discriminate XX)]. }
  pose proof Lo13 as Lcmaparr_a14.
  assert (SUB14 : sub_live A0 A14).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 cmaparr) by (intros ->; rewrite Fcmaparr in Lq; discriminate Lq). rewrite (LEQ13 q NEq). exact (SUB13 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 cmaparr :: [Z_to_bv 64 cmap; Z_to_bv 64 arr; Z_to_bv 64 na])) => eq_trans (LEQ13 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL13 q (fun XX => Hq (or_intror XX)))) as LDEL14.
  assert (NE_pixs_cmaparr : Z_to_bv 64 pixs <> Z_to_bv 64 cmaparr) by (intros EE; rewrite EE in Lpixs_a13; rewrite Fcmaparrx in Lpixs_a13; discriminate Lpixs_a13).
  assert (Lpixs_a14 : live A14 (Z_to_bv 64 pixs) = Some 64%Z) by (rewrite (LEQ13 _ NE_pixs_cmaparr); exact Lpixs_a13).
  pose proof (exW_blk_apart_h C A14 m14 _ pixs cmaparr 64 1024 CK HW14 Lpixs_a14 Lcmaparr_a14 NE_pixs_cmaparr RRpixs RRcmaparr ltac:(exW_cmp) ltac:(exW_cmp)) as AP_pixs_cmaparr.
  assert (NE_na_cmaparr : Z_to_bv 64 na <> Z_to_bv 64 cmaparr) by (intros EE; rewrite EE in Lna_a13; rewrite Fcmaparrx in Lna_a13; discriminate Lna_a13).
  assert (Lna_a14 : live A14 (Z_to_bv 64 na) = Some 32%Z) by (rewrite (LEQ13 _ NE_na_cmaparr); exact Lna_a13).
  pose proof (exW_blk_apart_h C A14 m14 _ na cmaparr 32 1024 CK HW14 Lna_a14 Lcmaparr_a14 NE_na_cmaparr RRna RRcmaparr ltac:(exW_cmp) ltac:(exW_cmp)) as AP_na_cmaparr.
  assert (NE_arr_cmaparr : Z_to_bv 64 arr <> Z_to_bv 64 cmaparr) by (intros EE; rewrite EE in Larr_a13; rewrite Fcmaparrx in Larr_a13; discriminate Larr_a13).
  assert (Larr_a14 : live A14 (Z_to_bv 64 arr) = Some 200%Z) by (rewrite (LEQ13 _ NE_arr_cmaparr); exact Larr_a13).
  pose proof (exW_blk_apart_h C A14 m14 _ arr cmaparr 200 1024 CK HW14 Larr_a14 Lcmaparr_a14 NE_arr_cmaparr RRarr RRcmaparr ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_cmaparr.
  assert (NE_cmap_cmaparr : Z_to_bv 64 cmap <> Z_to_bv 64 cmaparr) by (intros EE; rewrite EE in Lcmap_a13; rewrite Fcmaparrx in Lcmap_a13; discriminate Lcmap_a13).
  assert (Lcmap_a14 : live A14 (Z_to_bv 64 cmap) = Some 24%Z) by (rewrite (LEQ13 _ NE_cmap_cmaparr); exact Lcmap_a13).
  pose proof (exW_blk_apart_h C A14 m14 _ cmap cmaparr 24 1024 CK HW14 Lcmap_a14 Lcmaparr_a14 NE_cmap_cmaparr RRcmap RRcmaparr ltac:(exW_cmp) ltac:(exW_cmp)) as AP_cmap_cmaparr.
  assert (PM14 : POSTM C A0 s m0 m14).
  { eapply POSTM_trans; [exact PM13|]. eapply POSTM_trans; [exact PMs13|]. apply (POSTM_sub C A0 A13 _ _ _ SUB13).
    apply (POSTM_mono C A13 (s + OFF13) s); [unfold OFF13; lia | exact PMc13]. }
  replace (kR - 8 - 1)%Z with (kR - 9)%Z in RM14 by lia. rewrite MG13 in RM14. replace (bR - 8 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 9 * 2 ^ 17)%Z in RM14 by lia.
  assert (KEPT13 : Forall (ex_region_kept E13 M13 m14) [(EVar 32, OFF13, 0%Z); (EVar 34, 0%Z, 64%Z); (EVar 104, 0%Z, 32%Z); (EVar 138, 0%Z, 200%Z); (EVar 473, 0%Z, 24%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF13 12288 M13 m14 E13 (EVar 32) CK (proj1 PMc13) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A13 A13 M13 _ M13 m14 E13 (EVar 34) pixs 64 CK HWs13 Lpixs_a13 RRpixs eq_refl (proj2 PMc13) Lpixs_a13 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A13 A13 M13 _ M13 m14 E13 (EVar 104) na 32 CK HWs13 Lna_a13 RRna eq_refl (proj2 PMc13) Lna_a13 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A13 A13 M13 _ M13 m14 E13 (EVar 138) arr 200 CK HWs13 Larr_a13 RRarr eq_refl (proj2 PMc13) Larr_a13 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A13 A13 M13 _ M13 m14 E13 (EVar 473) cmap 24 CK HWs13 Lcmap_a13 RRcmap eq_refl (proj2 PMc13) Lcmap_a13 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E13 M13 m14 _ [172%nat; 239%nat; 306%nat; 373%nat; 70%nat] _ HKc13 KEPT13) as HKk13.
  match type of HKk13 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E13 m14 kk') in HKk13 end.
  pose proof (regs_ok_agree 475%nat E13 (ex_envL vals13 r14 [cmaparr; exW_canary SEGS 415784 m14]) _ _ (vals_app_agree vals13 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa13.
  pose proof (exW_regs_call _ _ _ _ _ HRa13 (ex_regs_ok_junk vals13 r14 [cmaparr; exW_canary SEGS 415784 m14] 475%nat ltac:(vm_cast_no_check (eq_refl 475%nat))) CS13) as HRn14.
  clear HRa13.
  assert (HKa14 : know_ok SEGS (ex_envL vals13 r14 [cmaparr; exW_canary SEGS 415784 m14]) m14 _) by (exact (know_ok_agree SEGS 475%nat E13 _ m14 _ (vals_app_agree vals13 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk13)).
  rewrite (fr_denot_agree 475%nat E13 (ex_envL vals13 r14 [cmaparr; exW_canary SEGS 415784 m14]) _ fr (vals_app_agree vals13 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r14 ex_r10 (EVar 507) HRn14 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres13)) as HRx14. clear HRn14. rename HRx14 into HRn14.
  clear HR HK Hlf Hms HKc13 HKk13 KEPT13 HC13 HWs13 PMs13 Q10_13 Q11_13 Q1_13 Q2_13 Q4_13 PM13 HW13 PMc13 CS13 SUB13 RM13 MG13 TOP13 LEQ13 Hnz13 Fcmaparrx Lo13 OFF13 LDEL13 Lpixs_a13 Lna_a13 Larr_a13 Lcmap_a13.
  subst M13. clear log13. clear E13. try clear Rc13. clear KN13.
  lazymatch type of HRn14 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn14 end.
  pose proof (exW_kn_blk SEGS C A14 m14 _ (ex_envL vals13 r14 [cmaparr; exW_canary SEGS 415784 m14]) (EVar 507) (EVar 32) cmaparr 1024 s 12288 65536 356352 p16_segs CK HW14 Lcmaparr_a14 RRcmaparr eq_refl eq_refl eq_refl RS ALcmaparr ZERO13 WAPcmaparr IMGAPcmaparr) as HKb14.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals13 r14 [cmaparr; exW_canary SEGS 415784 m14]) m14) _ _ (ex_kdisj_apart SEGS (ex_envL vals13 r14 [cmaparr; exW_canary SEGS 415784 m14]) m14 (EVar 34) (EVar 507) pixs cmaparr 0 64 0 1024 eq_refl eq_refl RRpixs RRcmaparr AP_pixs_cmaparr) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals13 r14 [cmaparr; exW_canary SEGS 415784 m14]) m14) _ _ (ex_kdisj_apart SEGS (ex_envL vals13 r14 [cmaparr; exW_canary SEGS 415784 m14]) m14 (EVar 104) (EVar 507) na cmaparr 0 32 0 1024 eq_refl eq_refl RRna RRcmaparr AP_na_cmaparr) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals13 r14 [cmaparr; exW_canary SEGS 415784 m14]) m14) _ _ (ex_kdisj_apart SEGS (ex_envL vals13 r14 [cmaparr; exW_canary SEGS 415784 m14]) m14 (EVar 138) (EVar 507) arr cmaparr 0 200 0 1024 eq_refl eq_refl RRarr RRcmaparr AP_arr_cmaparr) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals13 r14 [cmaparr; exW_canary SEGS 415784 m14]) m14) _ _ (ex_kdisj_apart SEGS (ex_envL vals13 r14 [cmaparr; exW_canary SEGS 415784 m14]) m14 (EVar 473) (EVar 507) cmap cmaparr 0 24 0 1024 eq_refl eq_refl RRcmap RRcmaparr AP_cmap_cmaparr) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals13 r14 [cmaparr; exW_canary SEGS 415784 m14]) m14)))))) as HKd14.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A14 m14 _ (s - 12288) (Z.to_nat 12288) CK HW14 GLO1 GLO2) as SOK14.
  pose proof (exW_canary_ok SEGS 415784 m14 (canary_any m14)) as CANOK14.
  pose (vals14 := vals13 ++ map (getr r14) ex_regs_list ++ map (Z_to_bv 64) [cmaparr; exW_canary SEGS 415784 m14]).
  pose proof (exW_kn_fixed SEGS C A14 m14 _ (ex_envL vals13 r14 [cmaparr; exW_canary SEGS 415784 m14]) (EVar 508) (EVar 32) (exW_canary SEGS 415784 m14) s 12288 415784 65536 212992 213416 213568 213416 213568
                HW14 eq_refl (proj1 CANOK14) (proj2 CANOK14) eq_refl eq_refl eq_refl SOK14 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf14.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb14 (proj2 (Forall_app _ _ _) (conj HKd14 (proj2 (Forall_app _ _ _) (conj HKf14 HKa14)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn14 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN14 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb14 HKd14 HKf14 HKa14 SOK14 CANOK14.
  repeat match goal with H : getr r14 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO13 ALcmaparr.
  (* [comment removed for export] *)
  exb_exit ST Rc14 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E14 := EEx) in HR, Hlf, HK, Hms |- *; set (log14 := LLx) in Hms, Hlf; set (M14 := mem_denot E14 m14 log14) in Hms end.
  assert (WP14 : W C A14 M14 (with_vmmaps vm14 md) /\ POSTM C A0 s m14 M14).
  { subst M14. apply (exW_win_blks C A14 A0 m14 _ E14 log14 (EVar 32) s 12288 [(EVar 104, na, 32%Z); (EVar 138, arr, 200%Z); (EVar 473, cmap, 24%Z); (EVar 507, cmaparr, 1024%Z)] CK HW14 SUB14 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRna (conj Lna_a14 (conj Fna F0na))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a14 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRcmap (conj Lcmap_a14 (conj Fcmap F0cmap))))|]. constructor; [exact (conj eq_refl (conj RRcmaparr (conj Lcmaparr_a14 (conj Fcmaparr F0cmaparr))))|]. constructor. }
  destruct WP14 as [HWs14 PMs14].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log14 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC14 : carry log14 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc14 : know_ok SEGS E14 M14 kn1) by (apply (carry_after SEGS E14 m14 log14 kn0 [] kn1 scs hs HC14 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW14)) | exact (mp_lazy _ (w_pure _ _ _ _ HW14)) | exact Hms |].
  pose (BS14 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (104%nat, na); (138%nat, arr); (473%nat, cmap); (507%nat, cmaparr)]).
  exW_regfactB BS14 HR ex_r10 Q10_14. exW_regfactB BS14 HR ex_r11 Q11_14. exW_regfactB BS14 HR ex_r1 Q1_14. exW_regfactB BS14 HR ex_r2 Q2_14. exW_regfactB BS14 HR ex_r4 Q4_14.
  clear BS14.
  lazymatch type of Q2_14 with _ = Z_to_bv 64 (s + ?off) => pose (OFF14 := off) end.
  (* [comment removed for export] *)
  pose proof (alloc_margin_small (256 * 4) ltac:(exW_cmp)) as MG14.
  lazymatch type of Q1_14 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_14 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A14 M14 _ Rc14 256 4 (kR - 9) (bR - 9 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs14 Q10_14 Q11_14 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM14) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_14
             ltac:(red; apply bv_eq; reflexivity) Q4_14 Q2_14 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A15 m15 vm15 r15 res14 HW15 Hres14 CSx14 Hnz14 Fqtabx Lo14 F0qtab LEQ14 ZERO14 ALqtab TOP14 PMc14 RM15.
  pose proof CSx14 as CS14. clear CSx14.
  rewrite with_vmmaps_twice in HW15 |- *.
  assert (Eres14 : res14 = Z_to_bv 64 (u res14)) by (symmetry; apply zbv_self).
  pose proof (u64_range res14) as RRqtab. set (qtab := u res14) in *. clearbody qtab. rewrite Eres14 in Hres14, Fqtabx, Lo14, F0qtab, LEQ14, ZERO14. clear Eres14.
  change (256 * 4)%Z with 1024%Z in *.
  pose proof (exW_blk_img_apart_h2 C A15 m15 _ qtab 1024 CK HW15 Lo14 RRqtab eq_refl eq_refl) as IMGAPqtab. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPqtab.
  pose proof (exW_win_blk_apart_h C A15 m15 _ s 12288 qtab 1024 CK HW15 Lo14 eq_refl RRqtab GLO1) as WAPqtab.
  assert (Fqtab : live A0 (Z_to_bv 64 qtab) = None).
  { destruct (live A0 (Z_to_bv 64 qtab)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB14 _ _ EE) as XX. first [discriminate Fqtabx | (rewrite Fqtabx in XX; discriminate XX)]. }
  pose proof Lo14 as Lqtab_a15.
  assert (SUB15 : sub_live A0 A15).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 qtab) by (intros ->; rewrite Fqtab in Lq; discriminate Lq). rewrite (LEQ14 q NEq). exact (SUB14 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 qtab :: [Z_to_bv 64 cmaparr; Z_to_bv 64 cmap; Z_to_bv 64 arr; Z_to_bv 64 na])) => eq_trans (LEQ14 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL14 q (fun XX => Hq (or_intror XX)))) as LDEL15.
  assert (NE_pixs_qtab : Z_to_bv 64 pixs <> Z_to_bv 64 qtab) by (intros EE; rewrite EE in Lpixs_a14; rewrite Fqtabx in Lpixs_a14; discriminate Lpixs_a14).
  assert (Lpixs_a15 : live A15 (Z_to_bv 64 pixs) = Some 64%Z) by (rewrite (LEQ14 _ NE_pixs_qtab); exact Lpixs_a14).
  pose proof (exW_blk_apart_h C A15 m15 _ pixs qtab 64 1024 CK HW15 Lpixs_a15 Lqtab_a15 NE_pixs_qtab RRpixs RRqtab ltac:(exW_cmp) ltac:(exW_cmp)) as AP_pixs_qtab.
  assert (NE_na_qtab : Z_to_bv 64 na <> Z_to_bv 64 qtab) by (intros EE; rewrite EE in Lna_a14; rewrite Fqtabx in Lna_a14; discriminate Lna_a14).
  assert (Lna_a15 : live A15 (Z_to_bv 64 na) = Some 32%Z) by (rewrite (LEQ14 _ NE_na_qtab); exact Lna_a14).
  pose proof (exW_blk_apart_h C A15 m15 _ na qtab 32 1024 CK HW15 Lna_a15 Lqtab_a15 NE_na_qtab RRna RRqtab ltac:(exW_cmp) ltac:(exW_cmp)) as AP_na_qtab.
  assert (NE_arr_qtab : Z_to_bv 64 arr <> Z_to_bv 64 qtab) by (intros EE; rewrite EE in Larr_a14; rewrite Fqtabx in Larr_a14; discriminate Larr_a14).
  assert (Larr_a15 : live A15 (Z_to_bv 64 arr) = Some 200%Z) by (rewrite (LEQ14 _ NE_arr_qtab); exact Larr_a14).
  pose proof (exW_blk_apart_h C A15 m15 _ arr qtab 200 1024 CK HW15 Larr_a15 Lqtab_a15 NE_arr_qtab RRarr RRqtab ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_qtab.
  assert (NE_cmap_qtab : Z_to_bv 64 cmap <> Z_to_bv 64 qtab) by (intros EE; rewrite EE in Lcmap_a14; rewrite Fqtabx in Lcmap_a14; discriminate Lcmap_a14).
  assert (Lcmap_a15 : live A15 (Z_to_bv 64 cmap) = Some 24%Z) by (rewrite (LEQ14 _ NE_cmap_qtab); exact Lcmap_a14).
  pose proof (exW_blk_apart_h C A15 m15 _ cmap qtab 24 1024 CK HW15 Lcmap_a15 Lqtab_a15 NE_cmap_qtab RRcmap RRqtab ltac:(exW_cmp) ltac:(exW_cmp)) as AP_cmap_qtab.
  assert (NE_cmaparr_qtab : Z_to_bv 64 cmaparr <> Z_to_bv 64 qtab) by (intros EE; rewrite EE in Lcmaparr_a14; rewrite Fqtabx in Lcmaparr_a14; discriminate Lcmaparr_a14).
  assert (Lcmaparr_a15 : live A15 (Z_to_bv 64 cmaparr) = Some 1024%Z) by (rewrite (LEQ14 _ NE_cmaparr_qtab); exact Lcmaparr_a14).
  pose proof (exW_blk_apart_h C A15 m15 _ cmaparr qtab 1024 1024 CK HW15 Lcmaparr_a15 Lqtab_a15 NE_cmaparr_qtab RRcmaparr RRqtab ltac:(exW_cmp) ltac:(exW_cmp)) as AP_cmaparr_qtab.
  assert (PM15 : POSTM C A0 s m0 m15).
  { eapply POSTM_trans; [exact PM14|]. eapply POSTM_trans; [exact PMs14|]. apply (POSTM_sub C A0 A14 _ _ _ SUB14).
    apply (POSTM_mono C A14 (s + OFF14) s); [unfold OFF14; lia | exact PMc14]. }
  replace (kR - 9 - 1)%Z with (kR - 10)%Z in RM15 by lia. rewrite MG14 in RM15. replace (bR - 9 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 10 * 2 ^ 17)%Z in RM15 by lia.
  assert (KEPT14 : Forall (ex_region_kept E14 M14 m15) [(EVar 32, OFF14, 0%Z); (EVar 34, 0%Z, 64%Z); (EVar 104, 0%Z, 32%Z); (EVar 138, 0%Z, 200%Z); (EVar 473, 0%Z, 24%Z); (EVar 507, 0%Z, 1024%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF14 12288 M14 m15 E14 (EVar 32) CK (proj1 PMc14) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A14 A14 M14 _ M14 m15 E14 (EVar 34) pixs 64 CK HWs14 Lpixs_a14 RRpixs eq_refl (proj2 PMc14) Lpixs_a14 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A14 A14 M14 _ M14 m15 E14 (EVar 104) na 32 CK HWs14 Lna_a14 RRna eq_refl (proj2 PMc14) Lna_a14 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A14 A14 M14 _ M14 m15 E14 (EVar 138) arr 200 CK HWs14 Larr_a14 RRarr eq_refl (proj2 PMc14) Larr_a14 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A14 A14 M14 _ M14 m15 E14 (EVar 473) cmap 24 CK HWs14 Lcmap_a14 RRcmap eq_refl (proj2 PMc14) Lcmap_a14 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A14 A14 M14 _ M14 m15 E14 (EVar 507) cmaparr 1024 CK HWs14 Lcmaparr_a14 RRcmaparr eq_refl (proj2 PMc14) Lcmaparr_a14 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E14 M14 m15 _ [172%nat; 239%nat; 306%nat; 373%nat; 70%nat] _ HKc14 KEPT14) as HKk14.
  match type of HKk14 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E14 m15 kk') in HKk14 end.
  pose proof (regs_ok_agree 509%nat E14 (ex_envL vals14 r15 [qtab; exW_canary SEGS 415784 m15]) _ _ (vals_app_agree vals14 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa14.
  pose proof (exW_regs_call _ _ _ _ _ HRa14 (ex_regs_ok_junk vals14 r15 [qtab; exW_canary SEGS 415784 m15] 509%nat ltac:(vm_cast_no_check (eq_refl 509%nat))) CS14) as HRn15.
  clear HRa14.
  assert (HKa15 : know_ok SEGS (ex_envL vals14 r15 [qtab; exW_canary SEGS 415784 m15]) m15 _) by (exact (know_ok_agree SEGS 509%nat E14 _ m15 _ (vals_app_agree vals14 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk14)).
  rewrite (fr_denot_agree 509%nat E14 (ex_envL vals14 r15 [qtab; exW_canary SEGS 415784 m15]) _ fr (vals_app_agree vals14 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r15 ex_r10 (EVar 541) HRn15 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres14)) as HRx15. clear HRn15. rename HRx15 into HRn15.
  clear HR HK Hlf Hms HKc14 HKk14 KEPT14 HC14 HWs14 PMs14 Q10_14 Q11_14 Q1_14 Q2_14 Q4_14 PM14 HW14 PMc14 CS14 SUB14 RM14 MG14 TOP14 LEQ14 Hnz14 Fqtabx Lo14 OFF14 LDEL14 Lpixs_a14 Lna_a14 Larr_a14 Lcmap_a14 Lcmaparr_a14.
  subst M14. clear log14. clear E14. try clear Rc14. clear KN14.
  lazymatch type of HRn15 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn15 end.
  pose proof (exW_kn_blk SEGS C A15 m15 _ (ex_envL vals14 r15 [qtab; exW_canary SEGS 415784 m15]) (EVar 541) (EVar 32) qtab 1024 s 12288 65536 356352 p16_segs CK HW15 Lqtab_a15 RRqtab eq_refl eq_refl eq_refl RS ALqtab ZERO14 WAPqtab IMGAPqtab) as HKb15.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals14 r15 [qtab; exW_canary SEGS 415784 m15]) m15) _ _ (ex_kdisj_apart SEGS (ex_envL vals14 r15 [qtab; exW_canary SEGS 415784 m15]) m15 (EVar 34) (EVar 541) pixs qtab 0 64 0 1024 eq_refl eq_refl RRpixs RRqtab AP_pixs_qtab) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals14 r15 [qtab; exW_canary SEGS 415784 m15]) m15) _ _ (ex_kdisj_apart SEGS (ex_envL vals14 r15 [qtab; exW_canary SEGS 415784 m15]) m15 (EVar 104) (EVar 541) na qtab 0 32 0 1024 eq_refl eq_refl RRna RRqtab AP_na_qtab) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals14 r15 [qtab; exW_canary SEGS 415784 m15]) m15) _ _ (ex_kdisj_apart SEGS (ex_envL vals14 r15 [qtab; exW_canary SEGS 415784 m15]) m15 (EVar 138) (EVar 541) arr qtab 0 200 0 1024 eq_refl eq_refl RRarr RRqtab AP_arr_qtab) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals14 r15 [qtab; exW_canary SEGS 415784 m15]) m15) _ _ (ex_kdisj_apart SEGS (ex_envL vals14 r15 [qtab; exW_canary SEGS 415784 m15]) m15 (EVar 473) (EVar 541) cmap qtab 0 24 0 1024 eq_refl eq_refl RRcmap RRqtab AP_cmap_qtab) (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals14 r15 [qtab; exW_canary SEGS 415784 m15]) m15) _ _ (ex_kdisj_apart SEGS (ex_envL vals14 r15 [qtab; exW_canary SEGS 415784 m15]) m15 (EVar 507) (EVar 541) cmaparr qtab 0 1024 0 1024 eq_refl eq_refl RRcmaparr RRqtab AP_cmaparr_qtab) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals14 r15 [qtab; exW_canary SEGS 415784 m15]) m15))))))) as HKd15.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A15 m15 _ (s - 12288) (Z.to_nat 12288) CK HW15 GLO1 GLO2) as SOK15.
  pose proof (exW_canary_ok SEGS 415784 m15 (canary_any m15)) as CANOK15.
  pose (vals15 := vals14 ++ map (getr r15) ex_regs_list ++ map (Z_to_bv 64) [qtab; exW_canary SEGS 415784 m15]).
  pose proof (exW_kn_fixed SEGS C A15 m15 _ (ex_envL vals14 r15 [qtab; exW_canary SEGS 415784 m15]) (EVar 542) (EVar 32) (exW_canary SEGS 415784 m15) s 12288 415784 65536 212992 213416 213568 213416 213568
                HW15 eq_refl (proj1 CANOK15) (proj2 CANOK15) eq_refl eq_refl eq_refl SOK15 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf15.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb15 (proj2 (Forall_app _ _ _) (conj HKd15 (proj2 (Forall_app _ _ _) (conj HKf15 HKa15)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn15 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN15 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb15 HKd15 HKf15 HKa15 SOK15 CANOK15.
  repeat match goal with H : getr r15 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  clear ZERO14 ALqtab.
  (* [comment removed for export] *)
  exb_exit ST Rc15 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E15 := EEx) in HR, Hlf, HK, Hms |- *; set (log15 := LLx) in Hms, Hlf; set (M15 := mem_denot E15 m15 log15) in Hms end.
  assert (WP15 : W C A15 M15 (with_vmmaps vm15 md) /\ POSTM C A0 s m15 M15).
  { subst M15. apply (exW_win_blks C A15 A0 m15 _ E15 log15 (EVar 32) s 12288 [(EVar 104, na, 32%Z); (EVar 138, arr, 200%Z); (EVar 473, cmap, 24%Z); (EVar 507, cmaparr, 1024%Z); (EVar 541, qtab, 1024%Z)] CK HW15 SUB15 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRna (conj Lna_a15 (conj Fna F0na))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a15 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRcmap (conj Lcmap_a15 (conj Fcmap F0cmap))))|]. constructor; [exact (conj eq_refl (conj RRcmaparr (conj Lcmaparr_a15 (conj Fcmaparr F0cmaparr))))|]. constructor; [exact (conj eq_refl (conj RRqtab (conj Lqtab_a15 (conj Fqtab F0qtab))))|]. constructor. }
  destruct WP15 as [HWs15 PMs15].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log15 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC15 : carry log15 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc15 : know_ok SEGS E15 M15 kn1) by (apply (carry_after SEGS E15 m15 log15 kn0 [] kn1 scs hs HC15 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW15)) | exact (mp_lazy _ (w_pure _ _ _ _ HW15)) | exact Hms |].
  pose (BS15 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (104%nat, na); (138%nat, arr); (473%nat, cmap); (507%nat, cmaparr); (541%nat, qtab)]).
  exW_regfactB BS15 HR ex_r9 Q9_15. exW_regfactB BS15 HR ex_r10 Q10_15. exW_regfactB BS15 HR ex_r11 Q11_15. exW_regfactB BS15 HR ex_r23 Q23_15. exW_regfactB BS15 HR ex_r25 Q25_15.
  clear BS15.
  assert (Q21_15 : getr Rc15 ex_r21 = alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 qtab)) by (exact (reg_val _ _ _ ex_r21 HR)).
  assert (Q24_15 : getr Rc15 ex_r24 = alu64 ALU_AND (alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 qtab)) (Z_to_bv 64 1)) by (exact (reg_val _ _ _ ex_r24 HR)).
  (* [comment removed for export] *)
  lazymatch type of Q10_15 with _ = Z_to_bv 64 ?a0 => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (qfillA_hop fxk C A15 A0 M15 _ Rc15 qtab 1024 0 45 a0 s S CK HWs15 SUB15 Hhi Lqtab_a15 Fqtab F0qtab RRqtab eq_refl (eq_sym (Z.add_0_r qtab)) Q9_15 Q10_15 Q11_15 Q21_15 Q23_15 Q24_15 Q25_15) end end.
  intros r16 m16 HW16 PMl15 AGR15 FRM15.
  assert (PM16 : POSTM C A0 s m0 m16).
  { eapply POSTM_trans; [exact PM15|]. eapply POSTM_trans; [exact PMs15 | exact PMl15]. }
  assert (KEPT15 : Forall (ex_region_kept E15 M15 m16) [(EVar 32, (-12288)%Z, (-12288 + 12288)%Z); (EVar 34, 0%Z, (0 + 64)%Z); (EVar 104, 0%Z, (0 + 32)%Z); (EVar 138, 0%Z, (0 + 200)%Z); (EVar 473, 0%Z, (0 + 24)%Z); (EVar 507, 0%Z, (0 + 1024)%Z)]).
  { constructor; [exact (exW_kept_frame E15 M15 m16 (EVar 32) s (-12288) 12288 qtab 1024 qtab (qtab + 1024) FRM15 eq_refl RS WAPqtab (Z.le_refl _) (Z.le_refl _))|]. constructor; [exact (exW_kept_frame E15 M15 m16 (EVar 34) pixs 0 64 qtab 1024 qtab (qtab + 1024) FRM15 eq_refl RRpixs AP_pixs_qtab (Z.le_refl _) (Z.le_refl _))|]. constructor; [exact (exW_kept_frame E15 M15 m16 (EVar 104) na 0 32 qtab 1024 qtab (qtab + 1024) FRM15 eq_refl RRna AP_na_qtab (Z.le_refl _) (Z.le_refl _))|]. constructor; [exact (exW_kept_frame E15 M15 m16 (EVar 138) arr 0 200 qtab 1024 qtab (qtab + 1024) FRM15 eq_refl RRarr AP_arr_qtab (Z.le_refl _) (Z.le_refl _))|]. constructor; [exact (exW_kept_frame E15 M15 m16 (EVar 473) cmap 0 24 qtab 1024 qtab (qtab + 1024) FRM15 eq_refl RRcmap AP_cmap_qtab (Z.le_refl _) (Z.le_refl _))|]. constructor; [exact (exW_kept_frame E15 M15 m16 (EVar 507) cmaparr 0 1024 qtab 1024 qtab (qtab + 1024) FRM15 eq_refl RRcmaparr AP_cmaparr_qtab (Z.le_refl _) (Z.le_refl _))|]. constructor. }
  pose proof (ex_know_keepD SEGS E15 M15 m16 _ [172%nat; 239%nat; 306%nat; 373%nat; 70%nat] _ HKc15 KEPT15) as HKk15.
  match type of HKk15 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E15 m16 kk') in HKk15 end.
  pose proof (regs_ok_agree 543%nat E15 (ex_envL vals15 r16 [exW_canary SEGS 415784 m16]) _ _ (vals_app_agree vals15 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa15.
  pose proof (exW_regs_keep _ _ _ _ _ [10%nat; 11%nat; 12%nat; 13%nat; 25%nat] HRa15 (ex_regs_ok_junk vals15 r16 [exW_canary SEGS 415784 m16] 543%nat ltac:(vm_cast_no_check (eq_refl 543%nat))) (exW_agree_keep _ _ _ AGR15)) as HRn16.
  clear HRa15.
  assert (HKa16 : know_ok SEGS (ex_envL vals15 r16 [exW_canary SEGS 415784 m16]) m16 _) by (exact (know_ok_agree SEGS 543%nat E15 _ m16 _ (vals_app_agree vals15 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk15)).
  rewrite (fr_denot_agree 543%nat E15 (ex_envL vals15 r16 [exW_canary SEGS 415784 m16]) _ fr (vals_app_agree vals15 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc15 HKk15 KEPT15 HC15 HWs15 PMs15 Q9_15 Q10_15 Q11_15 Q23_15 Q25_15 PM15 HW15 AGR15 FRM15 PMl15 Q21_15 Q24_15.
  subst M15. clear log15. clear E15. try clear Rc15. clear KN15.
  lazymatch type of HRn16 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn16 end.
  pose proof (exW_kwr_blk2 SEGS C A15 m16 _ (ex_envL vals15 r16 [exW_canary SEGS 415784 m16]) (EVar 541) qtab 1024 p16_segs CK HW16 Lqtab_a15 RRqtab eq_refl eq_refl) as HKb16.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A15 m16 _ (s - 12288) (Z.to_nat 12288) CK HW16 GLO1 GLO2) as SOK16.
  pose proof (exW_canary_ok SEGS 415784 m16 (canary_any m16)) as CANOK16.
  pose (vals16 := vals15 ++ map (getr r16) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m16]).
  pose proof (exW_kn_fixed SEGS C A15 m16 _ (ex_envL vals15 r16 [exW_canary SEGS 415784 m16]) (EVar 575) (EVar 32) (exW_canary SEGS 415784 m16) s 12288 415784 65536 212992 213416 213568 213416 213568
                HW16 eq_refl (proj1 CANOK16) (proj2 CANOK16) eq_refl eq_refl eq_refl SOK16 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf16.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb16 (proj2 (Forall_app _ _ _) (conj HKf16 HKa16)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn16 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN16 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb16 HKf16 HKa16 SOK16 CANOK16.
  repeat match goal with H : getr r16 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc16 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E16 := EEx) in HR, Hlf, HK, Hms |- *; set (log16 := LLx) in Hms, Hlf; set (M16 := mem_denot E16 m16 log16) in Hms end.
  assert (WP16 : W C A15 M16 (with_vmmaps vm15 md) /\ POSTM C A0 s m16 M16).
  { subst M16. apply (exW_win_blks C A15 A0 m16 _ E16 log16 (EVar 32) s 12288 [(EVar 104, na, 32%Z); (EVar 138, arr, 200%Z); (EVar 473, cmap, 24%Z); (EVar 507, cmaparr, 1024%Z); (EVar 541, qtab, 1024%Z)] CK HW16 SUB15 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRna (conj Lna_a15 (conj Fna F0na))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a15 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRcmap (conj Lcmap_a15 (conj Fcmap F0cmap))))|]. constructor; [exact (conj eq_refl (conj RRcmaparr (conj Lcmaparr_a15 (conj Fcmaparr F0cmaparr))))|]. constructor; [exact (conj eq_refl (conj RRqtab (conj Lqtab_a15 (conj Fqtab F0qtab))))|]. constructor. }
  destruct WP16 as [HWs16 PMs16].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log16 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC16 : carry log16 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc16 : know_ok SEGS E16 M16 kn1) by (apply (carry_after SEGS E16 m16 log16 kn0 [] kn1 scs hs HC16 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW16)) | exact (mp_lazy _ (w_pure _ _ _ _ HW16)) | exact Hms |].
  pose (BS16 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (104%nat, na); (138%nat, arr); (473%nat, cmap); (507%nat, cmaparr); (541%nat, qtab)]).
  exW_regfactB BS16 HR ex_r9 Q9_16. exW_regfactB BS16 HR ex_r10 Q10_16. exW_regfactB BS16 HR ex_r11 Q11_16. exW_regfactB BS16 HR ex_r23 Q23_16. exW_regfactB BS16 HR ex_r25 Q25_16.
  clear BS16.
  assert (Q21_16 : getr Rc16 ex_r21 = alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 qtab)) by (exact (reg_val _ _ _ ex_r21 HR)).
  assert (Q24_16 : getr Rc16 ex_r24 = alu64 ALU_AND (alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 qtab)) (Z_to_bv 64 1)) by (exact (reg_val _ _ _ ex_r24 HR)).
  (* [comment removed for export] *)
  lazymatch type of Q10_16 with _ = Z_to_bv 64 ?a0 => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (qfillA_hop fxk C A15 A0 M16 _ Rc16 qtab 1024 45 75 a0 s S CK HWs16 SUB15 Hhi Lqtab_a15 Fqtab F0qtab RRqtab eq_refl eq_refl Q9_16 Q10_16 Q11_16 Q21_16 Q23_16 Q24_16 Q25_16) end end.
  intros r17 m17 HW17 PMl16 AGR16 FRM16.
  assert (PM17 : POSTM C A0 s m0 m17).
  { eapply POSTM_trans; [exact PM16|]. eapply POSTM_trans; [exact PMs16 | exact PMl16]. }
  assert (KEPT16 : Forall (ex_region_kept E16 M16 m17) [(EVar 32, (-12288)%Z, (-12288 + 12288)%Z); (EVar 34, 0%Z, (0 + 64)%Z); (EVar 104, 0%Z, (0 + 32)%Z); (EVar 138, 0%Z, (0 + 200)%Z); (EVar 473, 0%Z, (0 + 24)%Z); (EVar 507, 0%Z, (0 + 1024)%Z)]).
  { constructor; [exact (exW_kept_frame E16 M16 m17 (EVar 32) s (-12288) 12288 qtab 1024 qtab (qtab + 1024) FRM16 eq_refl RS WAPqtab (Z.le_refl _) (Z.le_refl _))|]. constructor; [exact (exW_kept_frame E16 M16 m17 (EVar 34) pixs 0 64 qtab 1024 qtab (qtab + 1024) FRM16 eq_refl RRpixs AP_pixs_qtab (Z.le_refl _) (Z.le_refl _))|]. constructor; [exact (exW_kept_frame E16 M16 m17 (EVar 104) na 0 32 qtab 1024 qtab (qtab + 1024) FRM16 eq_refl RRna AP_na_qtab (Z.le_refl _) (Z.le_refl _))|]. constructor; [exact (exW_kept_frame E16 M16 m17 (EVar 138) arr 0 200 qtab 1024 qtab (qtab + 1024) FRM16 eq_refl RRarr AP_arr_qtab (Z.le_refl _) (Z.le_refl _))|]. constructor; [exact (exW_kept_frame E16 M16 m17 (EVar 473) cmap 0 24 qtab 1024 qtab (qtab + 1024) FRM16 eq_refl RRcmap AP_cmap_qtab (Z.le_refl _) (Z.le_refl _))|]. constructor; [exact (exW_kept_frame E16 M16 m17 (EVar 507) cmaparr 0 1024 qtab 1024 qtab (qtab + 1024) FRM16 eq_refl RRcmaparr AP_cmaparr_qtab (Z.le_refl _) (Z.le_refl _))|]. constructor. }
  pose proof (ex_know_keepD SEGS E16 M16 m17 _ [172%nat; 239%nat; 306%nat; 373%nat; 70%nat] _ HKc16 KEPT16) as HKk16.
  match type of HKk16 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E16 m17 kk') in HKk16 end.
  pose proof (regs_ok_agree 576%nat E16 (ex_envL vals16 r17 [exW_canary SEGS 415784 m17]) _ _ (vals_app_agree vals16 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa16.
  pose proof (exW_regs_keep _ _ _ _ _ [10%nat; 11%nat; 12%nat; 13%nat; 25%nat] HRa16 (ex_regs_ok_junk vals16 r17 [exW_canary SEGS 415784 m17] 576%nat ltac:(vm_cast_no_check (eq_refl 576%nat))) (exW_agree_keep _ _ _ AGR16)) as HRn17.
  clear HRa16.
  assert (HKa17 : know_ok SEGS (ex_envL vals16 r17 [exW_canary SEGS 415784 m17]) m17 _) by (exact (know_ok_agree SEGS 576%nat E16 _ m17 _ (vals_app_agree vals16 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk16)).
  rewrite (fr_denot_agree 576%nat E16 (ex_envL vals16 r17 [exW_canary SEGS 415784 m17]) _ fr (vals_app_agree vals16 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc16 HKk16 KEPT16 HC16 HWs16 PMs16 Q9_16 Q10_16 Q11_16 Q23_16 Q25_16 PM16 HW16 AGR16 FRM16 PMl16 Q21_16 Q24_16.
  subst M16. clear log16. clear E16. try clear Rc16. clear KN16.
  lazymatch type of HRn17 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn17 end.
  pose proof (exW_kwr_blk2 SEGS C A15 m17 _ (ex_envL vals16 r17 [exW_canary SEGS 415784 m17]) (EVar 541) qtab 1024 p16_segs CK HW17 Lqtab_a15 RRqtab eq_refl eq_refl) as HKb17.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A15 m17 _ (s - 12288) (Z.to_nat 12288) CK HW17 GLO1 GLO2) as SOK17.
  pose proof (exW_canary_ok SEGS 415784 m17 (canary_any m17)) as CANOK17.
  pose (vals17 := vals16 ++ map (getr r17) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m17]).
  pose proof (exW_kn_fixed SEGS C A15 m17 _ (ex_envL vals16 r17 [exW_canary SEGS 415784 m17]) (EVar 608) (EVar 32) (exW_canary SEGS 415784 m17) s 12288 415784 65536 212992 213416 213568 213416 213568
                HW17 eq_refl (proj1 CANOK17) (proj2 CANOK17) eq_refl eq_refl eq_refl SOK17 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf17.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb17 (proj2 (Forall_app _ _ _) (conj HKf17 HKa17)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn17 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN17 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb17 HKf17 HKa17 SOK17 CANOK17.
  repeat match goal with H : getr r17 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc17 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E17 := EEx) in HR, Hlf, HK, Hms |- *; set (log17 := LLx) in Hms, Hlf; set (M17 := mem_denot E17 m17 log17) in Hms end.
  assert (WP17 : W C A15 M17 (with_vmmaps vm15 md) /\ POSTM C A0 s m17 M17).
  { subst M17. apply (exW_win_blks C A15 A0 m17 _ E17 log17 (EVar 32) s 12288 [(EVar 104, na, 32%Z); (EVar 138, arr, 200%Z); (EVar 473, cmap, 24%Z); (EVar 507, cmaparr, 1024%Z); (EVar 541, qtab, 1024%Z)] CK HW17 SUB15 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRna (conj Lna_a15 (conj Fna F0na))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a15 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRcmap (conj Lcmap_a15 (conj Fcmap F0cmap))))|]. constructor; [exact (conj eq_refl (conj RRcmaparr (conj Lcmaparr_a15 (conj Fcmaparr F0cmaparr))))|]. constructor; [exact (conj eq_refl (conj RRqtab (conj Lqtab_a15 (conj Fqtab F0qtab))))|]. constructor. }
  destruct WP17 as [HWs17 PMs17].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log17 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC17 : carry log17 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc17 : know_ok SEGS E17 M17 kn1) by (apply (carry_after SEGS E17 m17 log17 kn0 [] kn1 scs hs HC17 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW17)) | exact (mp_lazy _ (w_pure _ _ _ _ HW17)) | exact Hms |].
  pose (BS17 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (104%nat, na); (138%nat, arr); (473%nat, cmap); (507%nat, cmaparr); (541%nat, qtab)]).
  exW_regfactB BS17 HR ex_r9 Q9_17. exW_regfactB BS17 HR ex_r10 Q10_17. exW_regfactB BS17 HR ex_r11 Q11_17. exW_regfactB BS17 HR ex_r23 Q23_17. exW_regfactB BS17 HR ex_r25 Q25_17.
  clear BS17.
  assert (Q21_17 : getr Rc17 ex_r21 = alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 qtab)) by (exact (reg_val _ _ _ ex_r21 HR)).
  assert (Q24_17 : getr Rc17 ex_r24 = alu64 ALU_AND (alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 qtab)) (Z_to_bv 64 1)) by (exact (reg_val _ _ _ ex_r24 HR)).
  (* [comment removed for export] *)
  lazymatch type of Q10_17 with _ = Z_to_bv 64 ?a0 => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (qfillA_hop fxk C A15 A0 M17 _ Rc17 qtab 1024 75 115 a0 s S CK HWs17 SUB15 Hhi Lqtab_a15 Fqtab F0qtab RRqtab eq_refl eq_refl Q9_17 Q10_17 Q11_17 Q21_17 Q23_17 Q24_17 Q25_17) end end.
  intros r18 m18 HW18 PMl17 AGR17 FRM17.
  assert (PM18 : POSTM C A0 s m0 m18).
  { eapply POSTM_trans; [exact PM17|]. eapply POSTM_trans; [exact PMs17 | exact PMl17]. }
  assert (KEPT17 : Forall (ex_region_kept E17 M17 m18) [(EVar 32, (-12288)%Z, (-12288 + 12288)%Z); (EVar 34, 0%Z, (0 + 64)%Z); (EVar 104, 0%Z, (0 + 32)%Z); (EVar 138, 0%Z, (0 + 200)%Z); (EVar 473, 0%Z, (0 + 24)%Z); (EVar 507, 0%Z, (0 + 1024)%Z)]).
  { constructor; [exact (exW_kept_frame E17 M17 m18 (EVar 32) s (-12288) 12288 qtab 1024 qtab (qtab + 1024) FRM17 eq_refl RS WAPqtab (Z.le_refl _) (Z.le_refl _))|]. constructor; [exact (exW_kept_frame E17 M17 m18 (EVar 34) pixs 0 64 qtab 1024 qtab (qtab + 1024) FRM17 eq_refl RRpixs AP_pixs_qtab (Z.le_refl _) (Z.le_refl _))|]. constructor; [exact (exW_kept_frame E17 M17 m18 (EVar 104) na 0 32 qtab 1024 qtab (qtab + 1024) FRM17 eq_refl RRna AP_na_qtab (Z.le_refl _) (Z.le_refl _))|]. constructor; [exact (exW_kept_frame E17 M17 m18 (EVar 138) arr 0 200 qtab 1024 qtab (qtab + 1024) FRM17 eq_refl RRarr AP_arr_qtab (Z.le_refl _) (Z.le_refl _))|]. constructor; [exact (exW_kept_frame E17 M17 m18 (EVar 473) cmap 0 24 qtab 1024 qtab (qtab + 1024) FRM17 eq_refl RRcmap AP_cmap_qtab (Z.le_refl _) (Z.le_refl _))|]. constructor; [exact (exW_kept_frame E17 M17 m18 (EVar 507) cmaparr 0 1024 qtab 1024 qtab (qtab + 1024) FRM17 eq_refl RRcmaparr AP_cmaparr_qtab (Z.le_refl _) (Z.le_refl _))|]. constructor. }
  pose proof (ex_know_keepD SEGS E17 M17 m18 _ [172%nat; 239%nat; 306%nat; 373%nat; 70%nat] _ HKc17 KEPT17) as HKk17.
  match type of HKk17 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E17 m18 kk') in HKk17 end.
  pose proof (regs_ok_agree 609%nat E17 (ex_envL vals17 r18 [exW_canary SEGS 415784 m18]) _ _ (vals_app_agree vals17 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa17.
  pose proof (exW_regs_keep _ _ _ _ _ [10%nat; 11%nat; 12%nat; 13%nat; 25%nat] HRa17 (ex_regs_ok_junk vals17 r18 [exW_canary SEGS 415784 m18] 609%nat ltac:(vm_cast_no_check (eq_refl 609%nat))) (exW_agree_keep _ _ _ AGR17)) as HRn18.
  clear HRa17.
  assert (HKa18 : know_ok SEGS (ex_envL vals17 r18 [exW_canary SEGS 415784 m18]) m18 _) by (exact (know_ok_agree SEGS 609%nat E17 _ m18 _ (vals_app_agree vals17 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk17)).
  rewrite (fr_denot_agree 609%nat E17 (ex_envL vals17 r18 [exW_canary SEGS 415784 m18]) _ fr (vals_app_agree vals17 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc17 HKk17 KEPT17 HC17 HWs17 PMs17 Q9_17 Q10_17 Q11_17 Q23_17 Q25_17 PM17 HW17 AGR17 FRM17 PMl17 Q21_17 Q24_17.
  subst M17. clear log17. clear E17. try clear Rc17. clear KN17.
  lazymatch type of HRn18 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn18 end.
  pose proof (exW_kwr_blk2 SEGS C A15 m18 _ (ex_envL vals17 r18 [exW_canary SEGS 415784 m18]) (EVar 541) qtab 1024 p16_segs CK HW18 Lqtab_a15 RRqtab eq_refl eq_refl) as HKb18.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A15 m18 _ (s - 12288) (Z.to_nat 12288) CK HW18 GLO1 GLO2) as SOK18.
  pose proof (exW_canary_ok SEGS 415784 m18 (canary_any m18)) as CANOK18.
  pose (vals18 := vals17 ++ map (getr r18) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m18]).
  pose proof (exW_kn_fixed SEGS C A15 m18 _ (ex_envL vals17 r18 [exW_canary SEGS 415784 m18]) (EVar 641) (EVar 32) (exW_canary SEGS 415784 m18) s 12288 415784 65536 212992 213416 213568 213416 213568
                HW18 eq_refl (proj1 CANOK18) (proj2 CANOK18) eq_refl eq_refl eq_refl SOK18 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf18.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb18 (proj2 (Forall_app _ _ _) (conj HKf18 HKa18)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn18 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN18 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb18 HKf18 HKa18 SOK18 CANOK18.
  repeat match goal with H : getr r18 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc18 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E18 := EEx) in HR, Hlf, HK, Hms |- *; set (log18 := LLx) in Hms, Hlf; set (M18 := mem_denot E18 m18 log18) in Hms end.
  assert (WP18 : W C A15 M18 (with_vmmaps vm15 md) /\ POSTM C A0 s m18 M18).
  { subst M18. apply (exW_win_blks C A15 A0 m18 _ E18 log18 (EVar 32) s 12288 [(EVar 104, na, 32%Z); (EVar 138, arr, 200%Z); (EVar 473, cmap, 24%Z); (EVar 507, cmaparr, 1024%Z); (EVar 541, qtab, 1024%Z)] CK HW18 SUB15 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRna (conj Lna_a15 (conj Fna F0na))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a15 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRcmap (conj Lcmap_a15 (conj Fcmap F0cmap))))|]. constructor; [exact (conj eq_refl (conj RRcmaparr (conj Lcmaparr_a15 (conj Fcmaparr F0cmaparr))))|]. constructor; [exact (conj eq_refl (conj RRqtab (conj Lqtab_a15 (conj Fqtab F0qtab))))|]. constructor. }
  destruct WP18 as [HWs18 PMs18].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log18 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC18 : carry log18 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc18 : know_ok SEGS E18 M18 kn1) by (apply (carry_after SEGS E18 m18 log18 kn0 [] kn1 scs hs HC18 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW18)) | exact (mp_lazy _ (w_pure _ _ _ _ HW18)) | exact Hms |].
  pose (BS18 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (104%nat, na); (138%nat, arr); (473%nat, cmap); (507%nat, cmaparr); (541%nat, qtab)]).
  exW_regfactB BS18 HR ex_r9 Q9_18. exW_regfactB BS18 HR ex_r10 Q10_18. exW_regfactB BS18 HR ex_r11 Q11_18. exW_regfactB BS18 HR ex_r23 Q23_18. exW_regfactB BS18 HR ex_r25 Q25_18.
  clear BS18.
  assert (Q21_18 : getr Rc18 ex_r21 = alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 qtab)) by (exact (reg_val _ _ _ ex_r21 HR)).
  assert (Q24_18 : getr Rc18 ex_r24 = alu64 ALU_AND (alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 qtab)) (Z_to_bv 64 1)) by (exact (reg_val _ _ _ ex_r24 HR)).
  (* [comment removed for export] *)
  lazymatch type of Q10_18 with _ = Z_to_bv 64 ?a0 => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (qfillA_hop fxk C A15 A0 M18 _ Rc18 qtab 1024 115 185 a0 s S CK HWs18 SUB15 Hhi Lqtab_a15 Fqtab F0qtab RRqtab eq_refl eq_refl Q9_18 Q10_18 Q11_18 Q21_18 Q23_18 Q24_18 Q25_18) end end.
  intros r19 m19 HW19 PMl18 AGR18 FRM18.
  assert (PM19 : POSTM C A0 s m0 m19).
  { eapply POSTM_trans; [exact PM18|]. eapply POSTM_trans; [exact PMs18 | exact PMl18]. }
  assert (KEPT18 : Forall (ex_region_kept E18 M18 m19) [(EVar 32, (-12288)%Z, (-12288 + 12288)%Z); (EVar 34, 0%Z, (0 + 64)%Z); (EVar 104, 0%Z, (0 + 32)%Z); (EVar 138, 0%Z, (0 + 200)%Z); (EVar 473, 0%Z, (0 + 24)%Z); (EVar 507, 0%Z, (0 + 1024)%Z)]).
  { constructor; [exact (exW_kept_frame E18 M18 m19 (EVar 32) s (-12288) 12288 qtab 1024 qtab (qtab + 1024) FRM18 eq_refl RS WAPqtab (Z.le_refl _) (Z.le_refl _))|]. constructor; [exact (exW_kept_frame E18 M18 m19 (EVar 34) pixs 0 64 qtab 1024 qtab (qtab + 1024) FRM18 eq_refl RRpixs AP_pixs_qtab (Z.le_refl _) (Z.le_refl _))|]. constructor; [exact (exW_kept_frame E18 M18 m19 (EVar 104) na 0 32 qtab 1024 qtab (qtab + 1024) FRM18 eq_refl RRna AP_na_qtab (Z.le_refl _) (Z.le_refl _))|]. constructor; [exact (exW_kept_frame E18 M18 m19 (EVar 138) arr 0 200 qtab 1024 qtab (qtab + 1024) FRM18 eq_refl RRarr AP_arr_qtab (Z.le_refl _) (Z.le_refl _))|]. constructor; [exact (exW_kept_frame E18 M18 m19 (EVar 473) cmap 0 24 qtab 1024 qtab (qtab + 1024) FRM18 eq_refl RRcmap AP_cmap_qtab (Z.le_refl _) (Z.le_refl _))|]. constructor; [exact (exW_kept_frame E18 M18 m19 (EVar 507) cmaparr 0 1024 qtab 1024 qtab (qtab + 1024) FRM18 eq_refl RRcmaparr AP_cmaparr_qtab (Z.le_refl _) (Z.le_refl _))|]. constructor. }
  pose proof (ex_know_keepD SEGS E18 M18 m19 _ [172%nat; 239%nat; 306%nat; 373%nat; 70%nat] _ HKc18 KEPT18) as HKk18.
  match type of HKk18 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E18 m19 kk') in HKk18 end.
  pose proof (regs_ok_agree 642%nat E18 (ex_envL vals18 r19 [exW_canary SEGS 415784 m19]) _ _ (vals_app_agree vals18 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa18.
  pose proof (exW_regs_keep _ _ _ _ _ [10%nat; 11%nat; 12%nat; 13%nat; 25%nat] HRa18 (ex_regs_ok_junk vals18 r19 [exW_canary SEGS 415784 m19] 642%nat ltac:(vm_cast_no_check (eq_refl 642%nat))) (exW_agree_keep _ _ _ AGR18)) as HRn19.
  clear HRa18.
  assert (HKa19 : know_ok SEGS (ex_envL vals18 r19 [exW_canary SEGS 415784 m19]) m19 _) by (exact (know_ok_agree SEGS 642%nat E18 _ m19 _ (vals_app_agree vals18 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk18)).
  rewrite (fr_denot_agree 642%nat E18 (ex_envL vals18 r19 [exW_canary SEGS 415784 m19]) _ fr (vals_app_agree vals18 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc18 HKk18 KEPT18 HC18 HWs18 PMs18 Q9_18 Q10_18 Q11_18 Q23_18 Q25_18 PM18 HW18 AGR18 FRM18 PMl18 Q21_18 Q24_18.
  subst M18. clear log18. clear E18. try clear Rc18. clear KN18.
  lazymatch type of HRn19 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn19 end.
  pose proof (exW_kwr_blk2 SEGS C A15 m19 _ (ex_envL vals18 r19 [exW_canary SEGS 415784 m19]) (EVar 541) qtab 1024 p16_segs CK HW19 Lqtab_a15 RRqtab eq_refl eq_refl) as HKb19.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A15 m19 _ (s - 12288) (Z.to_nat 12288) CK HW19 GLO1 GLO2) as SOK19.
  pose proof (exW_canary_ok SEGS 415784 m19 (canary_any m19)) as CANOK19.
  pose (vals19 := vals18 ++ map (getr r19) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m19]).
  pose proof (exW_kn_fixed SEGS C A15 m19 _ (ex_envL vals18 r19 [exW_canary SEGS 415784 m19]) (EVar 674) (EVar 32) (exW_canary SEGS 415784 m19) s 12288 415784 65536 212992 213416 213568 213416 213568
                HW19 eq_refl (proj1 CANOK19) (proj2 CANOK19) eq_refl eq_refl eq_refl SOK19 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf19.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb19 (proj2 (Forall_app _ _ _) (conj HKf19 HKa19)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn19 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN19 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb19 HKf19 HKa19 SOK19 CANOK19.
  repeat match goal with H : getr r19 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc19 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E19 := EEx) in HR, Hlf, HK, Hms |- *; set (log19 := LLx) in Hms, Hlf; set (M19 := mem_denot E19 m19 log19) in Hms end.
  assert (WP19 : W C A15 M19 (with_vmmaps vm15 md) /\ POSTM C A0 s m19 M19).
  { subst M19. apply (exW_win_blks C A15 A0 m19 _ E19 log19 (EVar 32) s 12288 [(EVar 104, na, 32%Z); (EVar 138, arr, 200%Z); (EVar 473, cmap, 24%Z); (EVar 507, cmaparr, 1024%Z); (EVar 541, qtab, 1024%Z)] CK HW19 SUB15 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRna (conj Lna_a15 (conj Fna F0na))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a15 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRcmap (conj Lcmap_a15 (conj Fcmap F0cmap))))|]. constructor; [exact (conj eq_refl (conj RRcmaparr (conj Lcmaparr_a15 (conj Fcmaparr F0cmaparr))))|]. constructor; [exact (conj eq_refl (conj RRqtab (conj Lqtab_a15 (conj Fqtab F0qtab))))|]. constructor. }
  destruct WP19 as [HWs19 PMs19].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log19 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC19 : carry log19 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc19 : know_ok SEGS E19 M19 kn1) by (apply (carry_after SEGS E19 m19 log19 kn0 [] kn1 scs hs HC19 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW19)) | exact (mp_lazy _ (w_pure _ _ _ _ HW19)) | exact Hms |].
  pose (BS19 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (104%nat, na); (138%nat, arr); (473%nat, cmap); (507%nat, cmaparr); (541%nat, qtab)]).
  exW_regfactB BS19 HR ex_r9 Q9_19. exW_regfactB BS19 HR ex_r11 Q11_19. exW_regfactB BS19 HR ex_r12 Q12_19. exW_regfactB BS19 HR ex_r13 Q13_19. exW_regfactB BS19 HR ex_r23 Q23_19.
  clear BS19.
  assert (Q10_19 : getr Rc19 ex_r10 = alu64 ALU_AND (alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 qtab)) (Z_to_bv 64 1)) by (exact (reg_val _ _ _ ex_r10 HR)).
  assert (Q21_19 : getr Rc19 ex_r21 = alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 qtab)) by (exact (reg_val _ _ _ ex_r21 HR)).
  (* [comment removed for export] *)
  lazymatch type of Q11_19 with _ = Z_to_bv 64 ?a0 => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (qfillB_hop fxk C A15 A0 M19 _ Rc19 qtab 1024 185 a0 s S CK HWs19 SUB15 Hhi Lqtab_a15 Fqtab F0qtab RRqtab eq_refl eq_refl Q9_19 Q10_19 Q11_19 Q12_19 Q13_19 Q21_19 Q23_19) end end.
  intros r20 m20 HW20 PMl19 AGR19 FRM19.
  assert (PM20 : POSTM C A0 s m0 m20).
  { eapply POSTM_trans; [exact PM19|]. eapply POSTM_trans; [exact PMs19 | exact PMl19]. }
  assert (KEPT19 : Forall (ex_region_kept E19 M19 m20) [(EVar 32, (-12288)%Z, (-12288 + 12288)%Z); (EVar 34, 0%Z, (0 + 64)%Z); (EVar 104, 0%Z, (0 + 32)%Z); (EVar 138, 0%Z, (0 + 200)%Z); (EVar 473, 0%Z, (0 + 24)%Z); (EVar 507, 0%Z, (0 + 1024)%Z)]).
  { constructor; [exact (exW_kept_frame E19 M19 m20 (EVar 32) s (-12288) 12288 qtab 1024 qtab (qtab + 1024) FRM19 eq_refl RS WAPqtab (Z.le_refl _) (Z.le_refl _))|]. constructor; [exact (exW_kept_frame E19 M19 m20 (EVar 34) pixs 0 64 qtab 1024 qtab (qtab + 1024) FRM19 eq_refl RRpixs AP_pixs_qtab (Z.le_refl _) (Z.le_refl _))|]. constructor; [exact (exW_kept_frame E19 M19 m20 (EVar 104) na 0 32 qtab 1024 qtab (qtab + 1024) FRM19 eq_refl RRna AP_na_qtab (Z.le_refl _) (Z.le_refl _))|]. constructor; [exact (exW_kept_frame E19 M19 m20 (EVar 138) arr 0 200 qtab 1024 qtab (qtab + 1024) FRM19 eq_refl RRarr AP_arr_qtab (Z.le_refl _) (Z.le_refl _))|]. constructor; [exact (exW_kept_frame E19 M19 m20 (EVar 473) cmap 0 24 qtab 1024 qtab (qtab + 1024) FRM19 eq_refl RRcmap AP_cmap_qtab (Z.le_refl _) (Z.le_refl _))|]. constructor; [exact (exW_kept_frame E19 M19 m20 (EVar 507) cmaparr 0 1024 qtab 1024 qtab (qtab + 1024) FRM19 eq_refl RRcmaparr AP_cmaparr_qtab (Z.le_refl _) (Z.le_refl _))|]. constructor. }
  pose proof (ex_know_keepD SEGS E19 M19 m20 _ [172%nat; 239%nat; 306%nat; 373%nat; 70%nat] _ HKc19 KEPT19) as HKk19.
  match type of HKk19 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E19 m20 kk') in HKk19 end.
  pose proof (regs_ok_agree 675%nat E19 (ex_envL vals19 r20 [exW_canary SEGS 415784 m20]) _ _ (vals_app_agree vals19 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa19.
  pose proof (exW_regs_keep _ _ _ _ _ [11%nat; 13%nat; 14%nat; 15%nat; 23%nat] HRa19 (ex_regs_ok_junk vals19 r20 [exW_canary SEGS 415784 m20] 675%nat ltac:(vm_cast_no_check (eq_refl 675%nat))) (exW_agree_keep _ _ _ AGR19)) as HRn20.
  clear HRa19.
  assert (HKa20 : know_ok SEGS (ex_envL vals19 r20 [exW_canary SEGS 415784 m20]) m20 _) by (exact (know_ok_agree SEGS 675%nat E19 _ m20 _ (vals_app_agree vals19 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk19)).
  rewrite (fr_denot_agree 675%nat E19 (ex_envL vals19 r20 [exW_canary SEGS 415784 m20]) _ fr (vals_app_agree vals19 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc19 HKk19 KEPT19 HC19 HWs19 PMs19 Q9_19 Q11_19 Q12_19 Q13_19 Q23_19 PM19 HW19 AGR19 FRM19 PMl19 Q10_19 Q21_19.
  subst M19. clear log19. clear E19. try clear Rc19. clear KN19.
  lazymatch type of HRn20 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn20 end.
  pose proof (exW_kwr_blk2 SEGS C A15 m20 _ (ex_envL vals19 r20 [exW_canary SEGS 415784 m20]) (EVar 541) qtab 1024 p16_segs CK HW20 Lqtab_a15 RRqtab eq_refl eq_refl) as HKb20.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A15 m20 _ (s - 12288) (Z.to_nat 12288) CK HW20 GLO1 GLO2) as SOK20.
  pose proof (exW_canary_ok SEGS 415784 m20 (canary_any m20)) as CANOK20.
  pose (vals20 := vals19 ++ map (getr r20) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m20]).
  pose proof (exW_kn_fixed SEGS C A15 m20 _ (ex_envL vals19 r20 [exW_canary SEGS 415784 m20]) (EVar 707) (EVar 32) (exW_canary SEGS 415784 m20) s 12288 415784 65536 212992 213416 213568 213416 213568
                HW20 eq_refl (proj1 CANOK20) (proj2 CANOK20) eq_refl eq_refl eq_refl SOK20 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf20.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb20 (proj2 (Forall_app _ _ _) (conj HKf20 HKa20)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn20 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN20 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb20 HKf20 HKa20 SOK20 CANOK20.
  repeat match goal with H : getr r20 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc20 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E20 := EEx) in HR, Hlf, HK, Hms |- *; set (log20 := LLx) in Hms, Hlf; set (M20 := mem_denot E20 m20 log20) in Hms end.
  assert (WP20 : W C A15 M20 (with_vmmaps vm15 md) /\ POSTM C A0 s m20 M20).
  { subst M20. apply (exW_win_blks C A15 A0 m20 _ E20 log20 (EVar 32) s 12288 [(EVar 104, na, 32%Z); (EVar 138, arr, 200%Z); (EVar 473, cmap, 24%Z); (EVar 507, cmaparr, 1024%Z); (EVar 541, qtab, 1024%Z)] CK HW20 SUB15 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRna (conj Lna_a15 (conj Fna F0na))))|]. constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a15 (conj Farr F0arr))))|]. constructor; [exact (conj eq_refl (conj RRcmap (conj Lcmap_a15 (conj Fcmap F0cmap))))|]. constructor; [exact (conj eq_refl (conj RRcmaparr (conj Lcmaparr_a15 (conj Fcmaparr F0cmaparr))))|]. constructor; [exact (conj eq_refl (conj RRqtab (conj Lqtab_a15 (conj Fqtab F0qtab))))|]. constructor. }
  destruct WP20 as [HWs20 PMs20].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log20 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC20 : carry log20 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc20 : know_ok SEGS E20 M20 kn1) by (apply (carry_after SEGS E20 m20 log20 kn0 [] kn1 scs hs HC20 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW20)) | exact (mp_lazy _ (w_pure _ _ _ _ HW20)) | exact Hms |].
  pose (BS20 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (104%nat, na); (138%nat, arr); (473%nat, cmap); (507%nat, cmaparr); (541%nat, qtab)]).
  exW_regfactB BS20 HR ex_r10 Q10_20. exW_regfactB BS20 HR ex_r1 Q1_20. exW_regfactB BS20 HR ex_r2 Q2_20. exW_regfactB BS20 HR ex_r4 Q4_20.
  clear BS20.
  lazymatch type of Q2_20 with _ = Z_to_bv 64 (s + ?off) => pose (OFF20 := off) end.
  (* [comment removed for export] *)
  lazymatch type of Q1_20 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_20 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A15 M20 _ Rc20 (Z_to_bv 64 arr) (Z_to_bv 64 ret) 200 sp' S CK HWs20 Q10_20 Larr_a15 F0arr Q1_20
             ltac:(red; apply bv_eq; reflexivity) Q4_20 Q2_20 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A16 m21 vm16 r21 HW21 CSx20 Ldead20 LEQ20 PMc20 RTR20.
  pose proof CSx20 as CS20. clear CSx20.
  rewrite with_vmmaps_twice in HW21 |- *.
  assert (SUB16 : sub_live A0 A16).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 arr) by (intros ->; rewrite Farr in Lq; discriminate Lq). rewrite (LEQ20 q NEq). exact (SUB15 q kq Lq). }
  assert (LDEL16 : forall q : word, ~ In q [Z_to_bv 64 qtab; Z_to_bv 64 cmaparr; Z_to_bv 64 cmap; Z_to_bv 64 na] -> live A16 q = live A0 q).
  { intros q Hq. destruct (decide (Z_to_bv 64 arr = q)) as [<-|NEq]; [rewrite Ldead20, Farr; reflexivity|]. rewrite (LEQ20 q (fun EE => NEq (eq_sym EE))). apply LDEL15. clear - Hq NEq. cbn [In] in *. tauto. }
  assert (Lpixs_a16 : live A16 (Z_to_bv 64 pixs) = Some 64%Z) by (rewrite (LEQ20 _ NE_pixs_arr); exact Lpixs_a15).
  assert (Lna_a16 : live A16 (Z_to_bv 64 na) = Some 32%Z) by (rewrite (LEQ20 _ NE_na_arr); exact Lna_a15).
  assert (Lcmap_a16 : live A16 (Z_to_bv 64 cmap) = Some 24%Z) by (rewrite (LEQ20 _ (fun EE => NE_arr_cmap (eq_sym EE))); exact Lcmap_a15).
  assert (Lcmaparr_a16 : live A16 (Z_to_bv 64 cmaparr) = Some 1024%Z) by (rewrite (LEQ20 _ (fun EE => NE_arr_cmaparr (eq_sym EE))); exact Lcmaparr_a15).
  assert (Lqtab_a16 : live A16 (Z_to_bv 64 qtab) = Some 1024%Z) by (rewrite (LEQ20 _ (fun EE => NE_arr_qtab (eq_sym EE))); exact Lqtab_a15).
  assert (PM21 : POSTM C A0 s m0 m21).
  { eapply POSTM_trans; [exact PM20|]. eapply POSTM_trans; [exact PMs20|]. apply (POSTM_sub C A0 A16 _ _ _ SUB16).
    apply (POSTM_mono C A16 (s + OFF20) s); [unfold OFF20; lia | exact PMc20]. }
  pose proof (RTR20 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM15) ltac:(lia) ltac:(lia)) as RM16. rewrite !Z.sub_0_r in RM16.
  assert (KEPT20 : Forall (ex_region_kept E20 M20 m21) [(EVar 32, OFF20, 0%Z); (EVar 34, 0%Z, 64%Z); (EVar 104, 0%Z, 32%Z); (EVar 473, 0%Z, 24%Z); (EVar 507, 0%Z, 1024%Z); (EVar 541, 0%Z, 1024%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF20 12288 M20 m21 E20 (EVar 32) CK (proj1 PMc20) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A16 A16 m21 _ M20 m21 E20 (EVar 34) pixs 64 CK HW21 Lpixs_a16 RRpixs eq_refl (proj2 PMc20) Lpixs_a16 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A16 A16 m21 _ M20 m21 E20 (EVar 104) na 32 CK HW21 Lna_a16 RRna eq_refl (proj2 PMc20) Lna_a16 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A16 A16 m21 _ M20 m21 E20 (EVar 473) cmap 24 CK HW21 Lcmap_a16 RRcmap eq_refl (proj2 PMc20) Lcmap_a16 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A16 A16 m21 _ M20 m21 E20 (EVar 507) cmaparr 1024 CK HW21 Lcmaparr_a16 RRcmaparr eq_refl (proj2 PMc20) Lcmaparr_a16 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A16 A16 m21 _ M20 m21 E20 (EVar 541) qtab 1024 CK HW21 Lqtab_a16 RRqtab eq_refl (proj2 PMc20) Lqtab_a16 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E20 M20 m21 _ [172%nat; 239%nat; 306%nat; 373%nat; 70%nat; 138%nat] _ HKc20 KEPT20) as HKk20.
  match type of HKk20 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E20 m21 kk') in HKk20 end.
  pose proof (regs_ok_agree 708%nat E20 (ex_envL vals20 r21 [exW_canary SEGS 415784 m21]) _ _ (vals_app_agree vals20 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa20.
  pose proof (exW_regs_call _ _ _ _ _ HRa20 (ex_regs_ok_junk vals20 r21 [exW_canary SEGS 415784 m21] 708%nat ltac:(vm_cast_no_check (eq_refl 708%nat))) CS20) as HRn21.
  clear HRa20.
  assert (HKa21 : know_ok SEGS (ex_envL vals20 r21 [exW_canary SEGS 415784 m21]) m21 _) by (exact (know_ok_agree SEGS 708%nat E20 _ m21 _ (vals_app_agree vals20 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk20)).
  rewrite (fr_denot_agree 708%nat E20 (ex_envL vals20 r21 [exW_canary SEGS 415784 m21]) _ fr (vals_app_agree vals20 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc20 HKk20 KEPT20 HC20 HWs20 PMs20 Q10_20 Q1_20 Q2_20 Q4_20 PM20 HW20 PMc20 CS20 SUB15 RM15 Ldead20 LEQ20 RTR20 Larr_a15 OFF20 LDEL15 Lpixs_a15 Lna_a15 Lcmap_a15 Lcmaparr_a15 Lqtab_a15.
  subst M20. clear log20. clear E20. try clear Rc20. clear KN20.
  lazymatch type of HRn21 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn21 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A16 m21 _ (s - 12288) (Z.to_nat 12288) CK HW21 GLO1 GLO2) as SOK21.
  pose proof (exW_canary_ok SEGS 415784 m21 (canary_any m21)) as CANOK21.
  pose (vals21 := vals20 ++ map (getr r21) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m21]).
  pose proof (exW_kn_fixed SEGS C A16 m21 _ (ex_envL vals20 r21 [exW_canary SEGS 415784 m21]) (EVar 740) (EVar 32) (exW_canary SEGS 415784 m21) s 12288 415784 65536 212992 213416 213568 213416 213568
                HW21 eq_refl (proj1 CANOK21) (proj2 CANOK21) eq_refl eq_refl eq_refl SOK21 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf21.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf21 HKa21)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn21 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN21 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf21 HKa21 SOK21 CANOK21.
  repeat match goal with H : getr r21 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc21 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E21 := EEx) in HR, Hlf, HK, Hms |- *; set (log21 := LLx) in Hms, Hlf; set (M21 := mem_denot E21 m21 log21) in Hms end.
  assert (WP21 : W C A16 M21 (with_vmmaps vm16 md) /\ POSTM C A0 s m21 M21).
  { subst M21. apply (exW_win_blks C A16 A0 m21 _ E21 log21 (EVar 32) s 12288 [(EVar 104, na, 32%Z); (EVar 473, cmap, 24%Z); (EVar 507, cmaparr, 1024%Z); (EVar 541, qtab, 1024%Z)] CK HW21 SUB16 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRna (conj Lna_a16 (conj Fna F0na))))|]. constructor; [exact (conj eq_refl (conj RRcmap (conj Lcmap_a16 (conj Fcmap F0cmap))))|]. constructor; [exact (conj eq_refl (conj RRcmaparr (conj Lcmaparr_a16 (conj Fcmaparr F0cmaparr))))|]. constructor; [exact (conj eq_refl (conj RRqtab (conj Lqtab_a16 (conj Fqtab F0qtab))))|]. constructor. }
  destruct WP21 as [HWs21 PMs21].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log21 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC21 : carry log21 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc21 : know_ok SEGS E21 M21 kn1) by (apply (carry_after SEGS E21 m21 log21 kn0 [] kn1 scs hs HC21 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW21)) | exact (mp_lazy _ (w_pure _ _ _ _ HW21)) | exact Hms |].
  pose (BS21 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (104%nat, na); (473%nat, cmap); (507%nat, cmaparr); (541%nat, qtab)]).
  exW_regfactB BS21 HR ex_r10 Q10_21. exW_regfactB BS21 HR ex_r1 Q1_21. exW_regfactB BS21 HR ex_r2 Q2_21. exW_regfactB BS21 HR ex_r4 Q4_21.
  clear BS21.
  lazymatch type of Q2_21 with _ = Z_to_bv 64 (s + ?off) => pose (OFF21 := off) end.
  (* [comment removed for export] *)
  lazymatch type of Q1_21 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_21 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A16 M21 _ Rc21 (Z_to_bv 64 na) (Z_to_bv 64 ret) 32 sp' S CK HWs21 Q10_21 Lna_a16 F0na Q1_21
             ltac:(red; apply bv_eq; reflexivity) Q4_21 Q2_21 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A17 m22 vm17 r22 HW22 CSx21 Ldead21 LEQ21 PMc21 RTR21.
  pose proof CSx21 as CS21. clear CSx21.
  rewrite with_vmmaps_twice in HW22 |- *.
  assert (SUB17 : sub_live A0 A17).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 na) by (intros ->; rewrite Fna in Lq; discriminate Lq). rewrite (LEQ21 q NEq). exact (SUB16 q kq Lq). }
  assert (LDEL17 : forall q : word, ~ In q [Z_to_bv 64 qtab; Z_to_bv 64 cmaparr; Z_to_bv 64 cmap] -> live A17 q = live A0 q).
  { intros q Hq. destruct (decide (Z_to_bv 64 na = q)) as [<-|NEq]; [rewrite Ldead21, Fna; reflexivity|]. rewrite (LEQ21 q (fun EE => NEq (eq_sym EE))). apply LDEL16. clear - Hq NEq. cbn [In] in *. tauto. }
  assert (Lpixs_a17 : live A17 (Z_to_bv 64 pixs) = Some 64%Z) by (rewrite (LEQ21 _ NE_pixs_na); exact Lpixs_a16).
  assert (Lcmap_a17 : live A17 (Z_to_bv 64 cmap) = Some 24%Z) by (rewrite (LEQ21 _ (fun EE => NE_na_cmap (eq_sym EE))); exact Lcmap_a16).
  assert (Lcmaparr_a17 : live A17 (Z_to_bv 64 cmaparr) = Some 1024%Z) by (rewrite (LEQ21 _ (fun EE => NE_na_cmaparr (eq_sym EE))); exact Lcmaparr_a16).
  assert (Lqtab_a17 : live A17 (Z_to_bv 64 qtab) = Some 1024%Z) by (rewrite (LEQ21 _ (fun EE => NE_na_qtab (eq_sym EE))); exact Lqtab_a16).
  assert (PM22 : POSTM C A0 s m0 m22).
  { eapply POSTM_trans; [exact PM21|]. eapply POSTM_trans; [exact PMs21|]. apply (POSTM_sub C A0 A17 _ _ _ SUB17).
    apply (POSTM_mono C A17 (s + OFF21) s); [unfold OFF21; lia | exact PMc21]. }
  pose proof (RTR21 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM16) ltac:(lia) ltac:(lia)) as RM17. rewrite !Z.sub_0_r in RM17.
  assert (KEPT21 : Forall (ex_region_kept E21 M21 m22) [(EVar 32, OFF21, 0%Z); (EVar 34, 0%Z, 64%Z); (EVar 473, 0%Z, 24%Z); (EVar 507, 0%Z, 1024%Z); (EVar 541, 0%Z, 1024%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF21 12288 M21 m22 E21 (EVar 32) CK (proj1 PMc21) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A17 A17 m22 _ M21 m22 E21 (EVar 34) pixs 64 CK HW22 Lpixs_a17 RRpixs eq_refl (proj2 PMc21) Lpixs_a17 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A17 A17 m22 _ M21 m22 E21 (EVar 473) cmap 24 CK HW22 Lcmap_a17 RRcmap eq_refl (proj2 PMc21) Lcmap_a17 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A17 A17 m22 _ M21 m22 E21 (EVar 507) cmaparr 1024 CK HW22 Lcmaparr_a17 RRcmaparr eq_refl (proj2 PMc21) Lcmaparr_a17 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A17 A17 m22 _ M21 m22 E21 (EVar 541) qtab 1024 CK HW22 Lqtab_a17 RRqtab eq_refl (proj2 PMc21) Lqtab_a17 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E21 M21 m22 _ [172%nat; 239%nat; 306%nat; 373%nat; 70%nat; 138%nat; 104%nat] _ HKc21 KEPT21) as HKk21.
  match type of HKk21 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E21 m22 kk') in HKk21 end.
  pose proof (regs_ok_agree 741%nat E21 (ex_envL vals21 r22 [exW_canary SEGS 415784 m22]) _ _ (vals_app_agree vals21 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa21.
  pose proof (exW_regs_call _ _ _ _ _ HRa21 (ex_regs_ok_junk vals21 r22 [exW_canary SEGS 415784 m22] 741%nat ltac:(vm_cast_no_check (eq_refl 741%nat))) CS21) as HRn22.
  clear HRa21.
  assert (HKa22 : know_ok SEGS (ex_envL vals21 r22 [exW_canary SEGS 415784 m22]) m22 _) by (exact (know_ok_agree SEGS 741%nat E21 _ m22 _ (vals_app_agree vals21 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk21)).
  rewrite (fr_denot_agree 741%nat E21 (ex_envL vals21 r22 [exW_canary SEGS 415784 m22]) _ fr (vals_app_agree vals21 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc21 HKk21 KEPT21 HC21 HWs21 PMs21 Q10_21 Q1_21 Q2_21 Q4_21 PM21 HW21 PMc21 CS21 SUB16 RM16 Ldead21 LEQ21 RTR21 Lna_a16 OFF21 LDEL16 Lpixs_a16 Lcmap_a16 Lcmaparr_a16 Lqtab_a16.
  subst M21. clear log21. clear E21. try clear Rc21. clear KN21.
  lazymatch type of HRn22 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn22 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A17 m22 _ (s - 12288) (Z.to_nat 12288) CK HW22 GLO1 GLO2) as SOK22.
  pose proof (exW_canary_ok SEGS 415784 m22 (canary_any m22)) as CANOK22.
  pose (vals22 := vals21 ++ map (getr r22) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m22]).
  pose proof (exW_kn_fixed SEGS C A17 m22 _ (ex_envL vals21 r22 [exW_canary SEGS 415784 m22]) (EVar 773) (EVar 32) (exW_canary SEGS 415784 m22) s 12288 415784 65536 212992 213416 213568 213416 213568
                HW22 eq_refl (proj1 CANOK22) (proj2 CANOK22) eq_refl eq_refl eq_refl SOK22 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf22.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf22 HKa22)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn22 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN22 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf22 HKa22 SOK22 CANOK22.
  repeat match goal with H : getr r22 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  match type of ST with ex_st _ _ _ _ _ _ ?pc _ _ => idtac "stopped at" pc end.
  exb_exit ST RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E22 := EEx) in HR, Hlf, HK, Hms |- *; set (log22 := LLx) in Hms, Hlf; set (M22 := mem_denot E22 m22 log22) in Hms end.
  assert (WP22 : W C A17 M22 (with_vmmaps vm17 md) /\ POSTM C A0 s m22 M22).
  { subst M22. apply (exW_win_blks C A17 A0 m22 _ E22 log22 (EVar 32) s 12288 [(EVar 473, cmap, 24%Z); (EVar 507, cmaparr, 1024%Z); (EVar 541, qtab, 1024%Z)] CK HW22 SUB17 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor; [exact (conj eq_refl (conj RRcmap (conj Lcmap_a17 (conj Fcmap F0cmap))))|]. constructor; [exact (conj eq_refl (conj RRcmaparr (conj Lcmaparr_a17 (conj Fcmaparr F0cmaparr))))|]. constructor; [exact (conj eq_refl (conj RRqtab (conj Lqtab_a17 (conj Fqtab F0qtab))))|]. constructor. }
  destruct WP22 as [HWs22 PMs22].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW22)) | exact (mp_lazy _ (w_pure _ _ _ _ HW22)) | exact Hms |].
  pose (BSF := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (473%nat, cmap); (507%nat, cmaparr); (541%nat, qtab)]).
  exW_regfactW r0 HR ex_r3 G3.
  exW_regfactB BSF HR ex_r1 G1. exW_regfactB BSF HR ex_r2 G2. exW_regfactB BSF HR ex_r4 G4. exW_regfactB BSF HR ex_r8 G8.
  exW_regfactB BSF HR ex_r9 G9. exW_regfactB BSF HR ex_r10 G10. exW_regfactB BSF HR ex_r11 G11. exW_regfactB BSF HR ex_r12 G12.
  exW_cellB HK Hlf r0 BSF (EVar 473) cmap 0%Z 8%nat CM0. exW_cellB HK Hlf r0 BSF (EVar 473) cmap 8%Z 4%nat CM8. exW_cellB HK Hlf r0 BSF (EVar 473) cmap 12%Z 4%nat CM12.
  exW_cellB HK Hlf r0 BSF (EVar 473) cmap 16%Z 4%nat CM16. exW_cellB HK Hlf r0 BSF (EVar 473) cmap 20%Z 4%nat CM20.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-8)%Z 8%nat SV1.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-16)%Z 8%nat SV8.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-24)%Z 8%nat SV9.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-32)%Z 8%nat SV18.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-40)%Z 8%nat SV19.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-48)%Z 8%nat SV20.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-56)%Z 8%nat SV21.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-64)%Z 8%nat SV22.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-72)%Z 8%nat SV23.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-80)%Z 8%nat SV24.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-88)%Z 8%nat SV25.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-96)%Z 8%nat SV26.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-104)%Z 8%nat SV27.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-160)%Z 8%nat LCcmap.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-128)%Z 4%nat LCh.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-124)%Z 4%nat LCw.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-120)%Z 8%nat LCqtab.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (HC fxk A17 M22 vm17 RcF qtab cmap cmaparr FZ HWs22 SUB17 (POSTM_trans _ _ _ _ _ _ PM22 PMs22) RM17 LDEL17
             Lqtab_a17 Fqtab F0qtab RRqtab NE_cmaparr_qtab Lcmap_a17 Fcmap F0cmap RRcmap Lcmaparr_a17 Fcmaparr F0cmaparr RRcmaparr CM0 CM8 CM12 CM16 CM20 G1 G2 G3 G4 G8 G9 G10 G11 G12 SV1 SV8 SV9 SV18 SV19 SV20 SV21 SV22 SV23 SV24 SV25 SV26 SV27 LCcmap LCh LCw LCqtab) end.
Qed.
End Parse.
