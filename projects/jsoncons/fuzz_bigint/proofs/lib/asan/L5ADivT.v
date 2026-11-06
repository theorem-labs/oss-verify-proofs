(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlanSoundSums SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ADetailH L5AFrameK L5DivKitA L5ADivH L5ADivPT As0Sums As0_code_92368_93368.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVT.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADIVPT.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac sc := first [ asm | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].

(* [comment removed for export] *)
Lemma kept_reg regs regs' (k : nat) : APSX.kept_ok regs regs' -> (0 < k < 32)%nat -> ~ In k APC.caller_saved -> getr regs' (reg k) = getr regs (reg k).
Proof.
  intros H Hk NI. apply H.
  - intros E. apply (f_equal bv_unsigned) in E. rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 5) with 32 in E.
    rewrite Z.mod_small in E by lia. change (bv_unsigned (0%bv : bv 5)) with 0 in E. lia.
  - unfold AX2.ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. rewrite Nat2Z.id. exact NI.
Qed.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.

Section DIV.
Variables (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z))
          (E SCRD F fl ro r : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr2 : credit).
Local Notation SPA := (E - 352).
Hypothesis G : L5AFK.gctx L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2.
Hypothesis ER : 140735332487680 <= E <= 140737488355328.
Hypothesis EA : aligned E 32.
Hypothesis HK : K [].
Hypothesis RA : L5.ra_ok r.
Hypothesis UR1 : U R 1 = r.
Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 E.
Local Notation binv := (L5AFK.binv L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3).
Local Notation FF' := ((F, 3, SPA + 32) :: FF).

Lemma dtail_run (fx : FPState) Rc MV : rinvD R E Rc ->
  getr Rc (reg 18) = Z_to_bv 64 (F / 8 + 2147450880) -> getr Rc (reg 19) = Z_to_bv 64 18446744073709551608 -> getr Rc (reg 24) = Z_to_bv 64 F -> getr Rc (reg 27) = Z_to_bv 64 F ->
  L5.writable RSEGS MV SPA (E - SPA) -> L5.img_clear MV 860160 880640 -> L5.u64_at RSEGS MV 908088 2147450880 -> L5.u32_at RSEGS MV 908096 1 ->
  L5.u64_at RSEGS MV 882712 834348 -> down E F ro R MV ->
  L5.defined MV F 512 -> L5.writable RSEGS MV F 512 -> L5.writable RSEGS MV (F / 8 + SB) 64 -> L5.u64_at RSEGS MV (F + 504) fl -> L5.writable RSEGS MV fl 1 ->
  exists (fx9 : FPState) R9 M9v, msteps RSEGS (st fx Rc 0x92c90 MV) (st fx9 R9 r M9v) /\ mem_grows MV M9v
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ L5AFK.Wret F fl 3 a -> M9v (Z_to_bv 64 a) = MV (Z_to_bv 64 a))
    /\ L5.u8_at RSEGS M9v fl 0 /\ regs_preserved R R9.
Proof.
  intros RI X18 X19 X24 X27 WSv IMGC CSB CUAR RMS OWNv FDEFv FWv FSHWv FLCv FLWv.
  destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  pose proof RI as (X2 & X8 & X9 & X3 & X4).
  assert (ALF : aligned F 32) by exact F32.
  assert (FRG : 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64 /\ 0 <= E < 2 ^ 64) by (clear - FR FLR ER; lia). destruct FRG as (FRG & FLRG & ERG).
  assert (SFB : F + 512 <= E - 352 /\ fl + 1 <= E - 352) by (clear - FCEIL FLR SPC SLO; lia).
  assert (SFA : E - 352 + 352 <= F \/ F + 512 <= E - 352) by (clear - SFB; lia).
  assert (SFLA : E - 352 + 352 <= fl \/ fl + 1 <= E - 352) by (clear - FLR SPC SLO; lia).
  assert (W352 : L5.writable RSEGS MV (E - 352) 352). { eapply L5.writable_sub. exact WSv. clear; lia. clear; lia. }
  (* [comment removed for export] *)
  pose proof (v5T3_conc fx Rc MV (fun j => match j with 2%nat => E | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & MG1 & qFR & qFZ & (qMS & qKS & qR1 & qR10 & qR11 & _)).
  assert (RI1 : rinvD R E R1). { apply (rinvD_ks R E Rc R1 KS_v5T3 RI qKS). vm_compute; reflexivity. }
  assert (Q24 : getr R1 (reg 24) = Z_to_bv 64 F). { rewrite (qKS 24%nat) by inl. exact X24. }
  (* [comment removed for export] *)
  assert (RMS1 : L5.u64_at RSEGS M1v 882712 834348).
  { eapply L5C.u64_at_agree. 4: exact RMS. 2: clear; lia. 2: clear; lia. intros i Hi. apply qFZ. clear - Hi; lia. all: clear - Hi FR F8; unfold SB; lia. }
  assert (AG1 : forall i, 65536 <= i < 6500352 -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
  { intros i Hi. apply qFZ. clear - Hi; lia. all: clear - Hi FR F8; unfold SB; lia. }
  assert (IMGC1 : L5.img_clear M1v 860160 880640). { intros i Hi. rewrite AG1 by (clear - Hi; lia). apply IMGC. exact Hi. }
  assert (CSB1 : L5.u64_at RSEGS M1v 908088 2147450880). { eapply L5C.u64_at_agree. 4: exact CSB. 2: clear; lia. 2: clear; lia. intros i Hi. apply AG1. clear - Hi; lia. }
  assert (CUAR1 : L5.u32_at RSEGS M1v 908096 1).
  { unfold L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS MV M1v 4 908096 ltac:(clear; lia) ltac:(cbn; clear; lia)). exact CUAR. intros i Hi. apply AG1. cbn in Hi. clear - Hi; lia. }
  pose proof (tpQt_conc fx1 R1 M1v (fun j => match j with 2%nat => U R1 2 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx2 & R2 & M2v & _ & tFR & _ & (tMS & tKS & tR6 & tR11 & tR12)).
  assert (E2 : M2v = M1v) by (apply mem_eq_of_agree; intros a Ha; apply tFR). subst M2v.
  (* [comment removed for export] *)
  set (sh := F / 8 + 2147450880) in *.
  assert (SHR : 2147450880 <= sh /\ sh + 64 <= 17594333495296).
  { subst sh. clear - FR. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono F (2 ^ 47 - 512) 8 ltac:(lia) ltac:(lia)). change ((2 ^ 47 - 512) / 8) with 17592186044352 in H0. lia. }
  assert (FSHW1 : L5.writable RSEGS M1v sh 64). { eapply L5.writable_grows. exact MG1. exact FSHWv. }
  destruct (as0_fill_spec_memset fx2 M1v (Z_to_bv 64 sh) (Z_to_bv 64 245) 64 R2 (Z_to_bv 64 601276)) as (R3 & MS3 & KO3 & _).
  { clear; lia. }
  { rewrite L5.unsigned_lit by (clear - SHR; lia). clear - SHR; lia. }
  { pose proof (FSHW1 0 64%nat ltac:(clear; lia) ltac:(clear; lia)) as X. rewrite Z.add_0_r in X. exact X. }
  { rewrite L5.unsigned_lit by (clear; lia). unfold AX2.two64. clear; lia. }
  { apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity. }
  { rewrite r1, (tKS 1%nat) by inl. exact qR1. }
  { rewrite r10, (tKS 10%nat) by inl. exact qR10. }
  { rewrite r11. exact tR11. }
  { rewrite r12, tR12. exact qR11. }
  set (M3v := wbytes M1v (Z_to_bv 64 sh) (repeat (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 245))) (Z.to_nat 64))) in *.
  assert (MG3 : mem_grows M1v M3v) by (apply wbytes_grows).
  assert (AG3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sh <= a < sh + 64) -> M3v (Z_to_bv 64 a) = M1v (Z_to_bv 64 a)).
  { intros a Ha Hn. subst M3v. apply AX2S.wbytes_out. rewrite repeat_length, L5.unsigned_lit by (clear - SHR; lia). clear - SHR; lia.
    rewrite repeat_length, !L5.unsigned_lit by (clear - SHR Ha; lia). clear - Hn. lia. }
  assert (KP3 : forall j, In j [2; 3; 4; 8; 9; 24]%nat -> getr R3 (reg j) = getr R1 (reg j)).
  { intros j Hj. rewrite (kept_reg R2 R3 j KO3). apply tKS. revert Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 24]%nat KS_tpQt). vm_compute; reflexivity.
    cbn [In] in Hj; clear - Hj; lia. cbn [In] in Hj. unfold APC.caller_saved. cbn [In]. clear - Hj. lia. }
  assert (RI3 : rinvD R E R3). { apply (rinvD_keep R E R1 R3 RI1). intros j Hj. apply KP3. unfold DIDX in Hj. cbn [In] in Hj |- *. clear - Hj. tauto. }
  assert (Y24 : getr R3 (reg 24) = Z_to_bv 64 F). { rewrite (KP3 24%nat) by (cbn [In]; tauto). exact Q24. }
  (* [comment removed for export] *)
  assert (AGS : forall a, E - 352 <= a < E -> M3v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)).
  { intros a Ha. rewrite AG3. apply qFZ. clear - Ha ER; lia. clear - Ha SFB; lia. clear - Ha SHR ER; subst sh; unfold SB; lia.
    clear - Ha ER; lia. clear - Ha SHR ER; lia. }
  assert (OWN3 : down E F ro R M3v).
  { apply (down_agree E F ro R MV M3v ltac:(clear - ER; lia) ltac:(clear - ER; lia) OWNv). intros a Ha. apply AGS. unfold docell in Ha. clear - Ha; lia. }
  destruct OWN3 as ((C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13) & _).
  assert (FDEF3 : L5.defined M3v F 512). { eapply L5.defined_grows. exact MG3. eapply L5.defined_grows. exact MG1. exact FDEFv. }
  assert (FW3 : L5.writable RSEGS M3v F 512). { eapply L5.writable_grows. exact MG3. eapply L5.writable_grows. exact MG1. exact FWv. }
  assert (FSHW3 : L5.writable RSEGS M3v (F / 8 + 2147450880) 64). { eapply L5.writable_grows. exact MG3. exact FSHW1. }
  assert (FLW3 : L5.writable RSEGS M3v fl 1). { eapply L5.writable_grows. exact MG3. eapply L5.writable_grows. exact MG1. exact FLWv. }
  assert (FLC3 : L5.u64_at RSEGS M3v (F + 504) fl).
  { eapply L5C.u64_at_agree. 4: exact FLCv. 2: clear - FR; lia. 2: clear - FR; lia. intros i Hi. rewrite AG3. apply qFZ. clear - Hi FR; lia. clear - Hi; lia.
    clear - Hi FR FBIG SHR; subst sh; unfold SB; lia. clear - Hi FR; lia. clear - Hi FR FBIG SHR; lia. }
  assert (AGI3 : forall i, 65536 <= i < 6500352 -> M3v (Z_to_bv 64 i) = M1v (Z_to_bv 64 i)) by (intros i Hi; apply AG3; [clear - Hi; lia | clear - Hi SHR; lia]).
  assert (IMGC3 : L5.img_clear M3v 860160 880640). { intros i Hi. rewrite AGI3 by (clear - Hi; lia). apply IMGC1. exact Hi. }
  assert (CSB3 : L5.u64_at RSEGS M3v 908088 2147450880). { eapply L5C.u64_at_agree. 4: exact CSB1. 2: clear; lia. 2: clear; lia. intros i Hi. apply AGI3. clear - Hi; lia. }
  assert (CUAR3 : L5.u32_at RSEGS M3v 908096 1).
  { unfold L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS M1v M3v 4 908096 ltac:(clear; lia) ltac:(cbn; clear; lia)). exact CUAR1. intros i Hi. apply AGI3. cbn in Hi. clear - Hi; lia. }
  pose proof RI3 as (Y2 & Y8 & Y9 & Y3 & Y4).
  assert (V0R : forall k, 0 <= U R k < 2 ^ 64) by (intros k; apply UR).
  assert (WSc : L5.writable RSEGS M3v (E - 352) 352). { eapply L5.writable_grows. exact MG3. eapply L5.writable_grows. exact MG1. exact W352. }
  pose proof (v5T4_conc fx2 R3 M3v (fun j => match j with 2%nat => E | 40%nat => F | 41%nat => fl
                | 42%nat => U R 1 | 43%nat => U R 8 | 44%nat => U R 9 | 45%nat => U R 18 | 46%nat => U R 19 | 47%nat => U R 20 | 48%nat => U R 21
                | 49%nat => U R 22 | 50%nat => U R 23 | 51%nat => U R 24 | 52%nat => U R 25 | 53%nat => U R 26 | 54%nat => U R 27 | 58%nat => U R3 1 | _ => 0 end)) as P.
  cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx9 & R9 & M9v & MG9 & eFR & eFZ & (eMS & eKS & eR1 & eR2 & eR8 & eR9 & eR10 & eR18 & eR19 & eR20 & eR21 & eR22 & eR23 & eR24 & eR25 & eR26 & eR27 & eFL0)).
  pose proof (ret_to fx9 R9 M9v 0x92dd4 W_92dd4 r F_92dd4 eq_refl D_92dd4 ltac:(rewrite eR1, UR1; reflexivity) (proj1 RA) (proj2 RA)) as RET.
  exists fx9, R9, M9v. split. { eapply msteps_trans. exact qMS. eapply msteps_trans. exact tMS. eapply msteps_trans. exact MS3. eapply msteps_trans. exact eMS. exact RET. }
  split. { eapply mem_grows_trans. exact MG1. eapply mem_grows_trans. exact MG3. exact MG9. }
  split. { intros a Ha Hw. unfold L5AFK.Wret in Hw. change (ff_bytes 3 / 8) with 64 in Hw. rewrite eFZ. rewrite AG3. apply qFZ. exact Ha.
           - clear - Hw; lia.
           - clear - Hw; unfold SB in Hw; lia.
           - exact Ha.
           - clear - Hw; subst sh; unfold SB in Hw; lia.
           - exact Ha.
           - clear - Hw; lia. }
  split. exact eFL0.
  apply preserved_by_index. intros j Hj. unfold cs_all in Hj. cbn [In] in Hj.
  destruct Hj as [<-|Hj]. { rewrite eR2. symmetry. exact G2. }
  destruct Hj as [<-|Hj]. { rewrite (eKS 3%nat) by inl. exact Y3. }
  destruct Hj as [<-|Hj]. { rewrite (eKS 4%nat) by inl. exact Y4. }
  repeat (destruct Hj as [<-|Hj]; [first [rewrite eR8 | rewrite eR9 | rewrite eR18 | rewrite eR19 | rewrite eR20 | rewrite eR21 | rewrite eR22 | rewrite eR23 | rewrite eR24 | rewrite eR25 | rewrite eR26 | rewrite eR27]; symmetry; apply U_to |]). destruct Hj.
Qed.

(* [comment removed for export] *)
Lemma div_tail (fx : FPState) Rc Mc modelc W BX LKc crc Ac : binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc ->
  getr Rc (reg 18) = Z_to_bv 64 (F / 8 + 2147450880) -> getr Rc (reg 19) = Z_to_bv 64 18446744073709551608 -> getr Rc (reg 24) = Z_to_bv 64 F -> getr Rc (reg 27) = Z_to_bv 64 F ->
  (forall (fxf : FPState) Rf Mf modelf,
      regs_preserved R Rf ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ L5AFK.Wret F fl 3 a -> Mf (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      ahpres L ar LB FF E SCRD W M Mf ->
      model_rt model modelf -> amodel_ok Ac modelf ->
      ri_inv HI (BX ++ LB) FF LKc crc Ac Mf (vml_of modelf) ->
      srealizes RSEGS SCFG (cfg (fx:=fxf) Rf r Mf modelf) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x92c90 Mc modelc) K.
Proof.
  intros BI RI X18 X19 X24 X27 KF.
  destruct (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac BI)
    as ((WSv & IMGC & CSB & CUAR & RMS) & OWNv & (FDEFv & FWv & FSHWv & FLCv & FLWv) & _).
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *. replace (F + 512 - 8) with (F + 504) in FLCv by (clear; lia).
  destruct (dtail_run fx Rc _ RI X18 X19 X24 X27 WSv IMGC CSB CUAR RMS OWNv FDEFv FWv FSHWv FLCv FLWv) as (fx9 & R9 & M9v & MS9 & MG9 & FZ9 & FL9 & RP9).
  apply (L5AFK.retire_core L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac fx fx9 Rc 0x92c90 R9 r M9v K BI MS9 MG9 FZ9 FL9).
  intros Mf modelf FRMf AHf RTf AMf HHf. apply (KF fx9 R9 Mf modelf RP9 FRMf AHf RTf AMf HHf).
Qed.

End DIV.
End WithIface.
End SCFG_1.
End L5ADVT.
