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
     L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ADetailH L5AFrameK L5ATopP2 L5ATopH As0Sums L5AUnwK3 L5AE2PP.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5AE2PD.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ATP2. Import L5ADH. Import L5AUK3. Import L5AE2PP.L5AE2PP.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac sc := first [ asm | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].
Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
Lemma UR R k : 0 <= U R k < 2 ^ 64. Proof. unfold U. apply BL.bvu_range. Qed.
Lemma U_to R k : getr R (reg k) = Z_to_bv 64 (U R k). Proof. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.


(* [comment removed for export] *)
Lemma pad1_run (fx : FPState) Rc MV (E F fl fden : Z) :
  getr Rc (reg 2) = Z_to_bv 64 (E - 352) -> getr Rc (reg 8) = Z_to_bv 64 E -> getr Rc (reg 9) = Z_to_bv 64 (E - 352) ->
  140735332487584 <= E <= 140737488355328 -> aligned E 32 -> L5.writable RSEGS MV (E - 352) 352 ->
  L5.img_clear MV 860160 880640 -> L5.u64_at RSEGS MV 908088 2147450880 -> L5.u32_at RSEGS MV 908096 1 -> L5.u64_at RSEGS MV 882712 834348 ->
  4096 <= F <= 140737488354816 -> aligned F 32 -> L5.defined MV F 512 -> L5.writable RSEGS MV F 512 ->
  (2147446784 + 17592186048512 <= F \/ F + 512 <= 2147446784) -> L5.writable RSEGS MV (F / 8 + 2147450880) 64 -> L5.u64_at RSEGS MV (F + 504) fl ->
  4096 <= fl <= 140737488355327 -> L5.writable RSEGS MV fl 1 -> (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784) -> (F + 512 <= fl \/ fl + 1 <= F) ->
  (E - 352 + 352 <= F \/ F + 512 <= E - 352) -> (E - 352 + 352 <= fl \/ fl + 1 <= E - 352) -> (65536 + 6434816 <= F \/ F + 512 <= 65536) -> (65536 + 6434816 <= fl \/ fl + 1 <= 65536) ->
  L5.u64_at RSEGS MV (E - 264) (F + 32) -> L5.u64_at RSEGS MV (E - 240) (F / 8 + 2147450880) -> L5.u64_at RSEGS MV (E - 296) F -> L5.u64_at RSEGS MV (E - 280) F ->
  L5.u8_at RSEGS MV (F + 32) fden -> 0 <= fden <= 255 -> Z.testbit fden 0 = false ->
  exists (fx9 : FPState) R9 M9v, msteps RSEGS (st fx Rc 0x9309c MV) (st fx9 R9 0x9329c M9v) /\ mem_grows MV M9v
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ Wpad F 512 fl a -> M9v (Z_to_bv 64 a) = MV (Z_to_bv 64 a))
    /\ L5.u8_at RSEGS M9v fl 0 /\ getr R9 (reg 10) = getr Rc (reg 10)
    /\ (forall k, In k [2; 3; 4; 8; 9]%nat -> getr R9 (reg k) = getr Rc (reg k)).
Proof.
  intros G2 G8 G9 ER EA WSv IMGC CSB CUAR RMS FR FA FDEFv FWv FBIG FSHWv FLCv FLR FLWv FLBIG FLA SFA SFLA IFA IFLA C264 C240 C296 C280 CDEN DENR DENT.
  assert (RG : 0 <= E < 2 ^ 64 /\ 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64 /\ 0 <= fden < 2 ^ 64) by (clear - ER FR FLR DENR; lia). destruct RG as (ERG & FRG & FLRG & DENRG).
  (* [comment removed for export] *)
  pose proof (ue2p1a_conc fx Rc MV (fun j => match j with 2%nat => E | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 60%nat => fden | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & MG1 & qFR & qFZ & (qMS & qKS & qR1 & qR10 & qR11 & qR24 & _)).
  (* [comment removed for export] *)
  assert (AG1 : forall i, 65536 <= i < 6500352 -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
  { intros i Hi. apply qFZ. clear - Hi; lia. clear - Hi IFA; lia. clear - Hi FR FBIG; lia. }
  assert (RMS1 : L5.u64_at RSEGS M1v 882712 834348). { eapply L5C.u64_at_agree. 4: exact RMS. 2: clear; lia. 2: clear; lia. intros i Hi. apply AG1. clear - Hi; lia. }
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
  destruct (as0_fill_spec_memset fx2 M1v (Z_to_bv 64 sh) (Z_to_bv 64 245) 64 R2 (Z_to_bv 64 602548)) as (R3 & MS3 & KO3 & _).
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
  assert (KR3 : forall j, (0 < j < 32)%nat -> ~ In j APC.caller_saved -> In j KS_tpQt -> In j KS_ue2p1a -> getr R3 (reg j) = getr Rc (reg j)).
  { intros j Hj Hc H1 H2. rewrite (L5ATH.kept_reg R2 R3 j KO3 Hj Hc). rewrite (tKS j H1). apply qKS. exact H2. }
  (* [comment removed for export] *)
  assert (WS3 : L5.writable RSEGS M3v (E - 352) 352). { eapply L5.writable_grows. exact MG3. eapply L5.writable_grows. exact MG1. exact WSv. }
  assert (AGI3 : forall i, 65536 <= i < 6500352 -> M3v (Z_to_bv 64 i) = M1v (Z_to_bv 64 i)) by (intros i Hi; apply AG3; [clear - Hi; lia | clear - Hi SHR; lia]).
  assert (IMGC3 : L5.img_clear M3v 860160 880640). { intros i Hi. rewrite AGI3 by (clear - Hi; lia). apply IMGC1. exact Hi. }
  assert (CSB3 : L5.u64_at RSEGS M3v 908088 2147450880). { eapply L5C.u64_at_agree. 4: exact CSB1. 2: clear; lia. 2: clear; lia. intros i Hi. apply AGI3. clear - Hi; lia. }
  assert (CUAR3 : L5.u32_at RSEGS M3v 908096 1).
  { unfold L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS M1v M3v 4 908096 ltac:(clear; lia) ltac:(cbn; clear; lia)). exact CUAR1. intros i Hi. apply AGI3. cbn in Hi. clear - Hi; lia. }
  assert (FDEF3 : L5.defined M3v F 512). { eapply L5.defined_grows. exact MG3. eapply L5.defined_grows. exact MG1. exact FDEFv. }
  assert (FW3 : L5.writable RSEGS M3v F 512). { eapply L5.writable_grows. exact MG3. eapply L5.writable_grows. exact MG1. exact FWv. }
  assert (FSHW3 : L5.writable RSEGS M3v (F / 8 + 2147450880) 64). { eapply L5.writable_grows. exact MG3. exact FSHW1. }
  assert (FLW3 : L5.writable RSEGS M3v fl 1). { eapply L5.writable_grows. exact MG3. eapply L5.writable_grows. exact MG1. exact FLWv. }
  assert (FLC3 : L5.u64_at RSEGS M3v (F + 504) fl).
  { eapply L5C.u64_at_agree. 4: exact FLCv. 2: clear - FR; lia. 2: clear - FR; lia. intros i Hi. rewrite AG3. apply qFZ. clear - Hi FR; lia. clear - Hi; lia.
    clear - Hi FR FBIG SHR; subst sh; lia. clear - Hi FR; lia. clear - Hi FR FBIG SHR; lia. }
  assert (C280_3 : L5.u64_at RSEGS M3v (E - 280) F).
  { eapply L5C.u64_at_agree. 4: exact C280. 2: clear - ER; lia. 2: clear - ER; lia. intros i Hi. rewrite AG3. apply qFZ. clear - Hi ER; lia. clear - Hi SFA; lia.
    clear - Hi ER SHR; subst sh; lia. clear - Hi ER; lia. clear - Hi ER SHR; lia. }
  assert (Y2 : getr R3 (reg 2) = Z_to_bv 64 (E - 352)). { rewrite KR3. exact G2. clear; lia. unfold APC.caller_saved; cbn [In]; clear; lia. inl. inl. }
  assert (Y8 : getr R3 (reg 8) = Z_to_bv 64 E). { rewrite KR3. exact G8. clear; lia. unfold APC.caller_saved; cbn [In]; clear; lia. inl. inl. }
  assert (Y9 : getr R3 (reg 9) = Z_to_bv 64 (E - 352)). { rewrite KR3. exact G9. clear; lia. unfold APC.caller_saved; cbn [In]; clear; lia. inl. inl. }
  pose proof (ue2p1b_conc fx2 R3 M3v (fun j => match j with 2%nat => E | 40%nat => F | 41%nat => fl | 58%nat => U R3 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx9 & R9 & M9v & MG9 & eFR & eFZ & (eMS & eKS & eR10 & eFL0)).
  exists fx9, R9, M9v.
  split. { eapply msteps_trans. exact qMS. eapply msteps_trans. exact tMS. eapply msteps_trans. exact MS3. exact eMS. }
  split. { eapply mem_grows_trans. exact MG1. eapply mem_grows_trans. exact MG3. exact MG9. }
  split. { intros a Ha Hw. unfold Wpad in Hw. change (512 / 8) with 64 in Hw. rewrite eFZ. rewrite AG3. apply qFZ. exact Ha.
           - clear - Hw; lia.
           - clear - Hw; unfold SB in Hw; lia.
           - exact Ha.
           - clear - Hw; subst sh; unfold SB in Hw; lia.
           - exact Ha.
           - clear - Hw; lia. }
  split. exact eFL0.
  split. { rewrite eR10. rewrite (L5ATH.kept_reg R2 R3 24 KO3) by (first [clear; lia | unfold APC.caller_saved; cbn [In]; clear; lia]). rewrite (tKS 24%nat) by inl. exact qR24. }
  intros j Hj. rewrite (eKS j) by (revert j Hj; apply L5K.incl_b; vm_compute; reflexivity).
  apply KR3. cbn [In] in Hj; clear - Hj; lia. unfold APC.caller_saved. cbn [In] in Hj |- *. clear - Hj. lia.
  revert j Hj; apply L5K.incl_b; vm_compute; reflexivity. revert j Hj; apply L5K.incl_b; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pad2_run (fx : FPState) Rc MV (E F fl fq : Z) :
  getr Rc (reg 2) = Z_to_bv 64 (E - 96) -> getr Rc (reg 8) = Z_to_bv 64 E -> getr Rc (reg 9) = Z_to_bv 64 (E - 96) ->
  getr Rc (reg 18) = Z_to_bv 64 F -> getr Rc (reg 21) = Z_to_bv 64 (F + 32) -> getr Rc (reg 22) = Z_to_bv 64 (F / 8 + 2147450880) -> getr Rc (reg 23) = Z_to_bv 64 F ->
  getr Rc (reg 24) = Z_to_bv 64 1172321806 ->
  140735332487328 <= E <= 140737488355328 -> aligned E 32 -> L5.writable RSEGS MV (E - 96) 96 ->
  L5.img_clear MV 860160 880640 -> L5.u64_at RSEGS MV 908088 2147450880 -> L5.u32_at RSEGS MV 908096 1 ->
  4096 <= F <= 140737488355200 -> aligned F 32 -> L5.defined MV F 128 -> L5.writable RSEGS MV F 128 ->
  (2147446784 + 17592186048512 <= F \/ F + 128 <= 2147446784) -> L5.writable RSEGS MV (F / 8 + 2147450880) 16 -> L5.u64_at RSEGS MV (F + 120) fl ->
  4096 <= fl <= 140737488355327 -> L5.writable RSEGS MV fl 1 -> (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784) -> (F + 128 <= fl \/ fl + 1 <= F) ->
  (E - 96 + 96 <= F \/ F + 128 <= E - 96) -> (E - 96 + 96 <= fl \/ fl + 1 <= E - 96) -> (65536 + 6434816 <= F \/ F + 128 <= 65536) -> (65536 + 6434816 <= fl \/ fl + 1 <= 65536) ->
  L5.u8_at RSEGS MV (F + 32) fq -> 0 <= fq <= 255 -> Z.testbit fq 0 = false ->
  exists (fx9 : FPState) R9 M9v, msteps RSEGS (st fx Rc 0x92024 MV) (st fx9 R9 0x920e8 M9v) /\ mem_grows MV M9v
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ Wpad F 128 fl a -> M9v (Z_to_bv 64 a) = MV (Z_to_bv 64 a))
    /\ L5.u8_at RSEGS M9v fl 0
    /\ (forall k, In k [1; 2; 3; 4; 8; 9; 10; 25; 26; 27]%nat -> getr R9 (reg k) = getr Rc (reg k)).
Proof.
  intros G2 G8 G9 G18 G21 G22 G23 G24 ER EA WSv IMGC CSB CUAR FR FA FDEFv FWv FBIG FSHWv FLCv FLR FLWv FLBIG FLA SFA SFLA IFA IFLA CQ QR QT.
  assert (RG : 0 <= E < 2 ^ 64 /\ 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64 /\ 0 <= fq < 2 ^ 64) by (clear - ER FR FLR QR; lia). destruct RG as (ERG & FRG & FLRG & QRG).
  pose proof (ue2p2_conc fx Rc MV (fun j => match j with 2%nat => E | 40%nat => F | 41%nat => fl | 60%nat => fq | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx9 & R9 & M9v & MG9 & eFR & eFZ & (eMS & eKS & _ & _ & eFL0 & _)).
  exists fx9, R9, M9v. split. exact eMS. split. exact MG9.
  split. { intros a Ha Hw. unfold Wpad in Hw. change (128 / 8) with 16 in Hw. apply eFZ. exact Ha. clear - Hw; lia. clear - Hw; unfold SB in Hw; lia. clear - Hw; lia. }
  split. exact eFL0.
  intros j Hj. apply eKS. revert j Hj; apply L5K.incl_b; vm_compute; reflexivity.
Qed.

End SCFG_1.
End L5AE2PD.
