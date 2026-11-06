(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlanSoundSums SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5BDetailG L5BFrameK L5BTopP2 Bo0Sums L5BUnwK3 L5BE2PP.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5AE3PD.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ATP2. Import L5ADH. Import L5AUK3. Import L5BE2PP.L5BE2PP.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac in_tac := solve [ repeat first [ left; reflexivity | right ] ].
Local Ltac sc := first [ asm | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].
Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
Lemma UR R k : 0 <= U R k < 2 ^ 64. Proof. unfold U. apply BL.bvu_range. Qed.
Lemma U_to R k : getr R (reg k) = Z_to_bv 64 (U R k). Proof. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
(* [comment removed for export] *)
Lemma kept_reg regs regs' (k : nat) : APSX.kept_ok regs regs' -> (0 < k < 32)%nat -> ~ In k APC.caller_saved -> getr regs' (reg k) = getr regs (reg k).
Proof.
  intros H Hk NI. apply H.
  - intros E. apply (f_equal bv_unsigned) in E. rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 5) with 32 in E.
    rewrite Z.mod_small in E by lia. change (bv_unsigned (0%bv : bv 5)) with 0 in E. lia.
  - unfold AX2.ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. rewrite Nat2Z.id. exact NI.
Qed.


(* [comment removed for export] *)
Lemma div_pad_tail (fx fx1 : FPState) Rc R1 MV M1v (E F fl pc0 : Z) (w24 : word) :
  msteps RSEGS (st fx Rc pc0 MV) (st fx1 R1 0x61fcc M1v) -> mem_grows MV M1v ->
  (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (F <= i < F + 8) -> ~ (F / 8 + 2147450880 <= i < F / 8 + 2147450880 + 64) -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i)) ->
  (forall j, In j [2; 3; 4; 8; 9; 18; 23]%nat -> getr R1 (reg j) = getr Rc (reg j)) ->
  getr R1 (reg 1) = Z_to_bv 64 605356 -> getr R1 (reg 10) = Z_to_bv 64 (F / 8 + 2147450880) -> getr R1 (reg 11) = Z_to_bv 64 64 -> getr R1 (reg 22) = w24 ->
  getr Rc (reg 2) = Z_to_bv 64 (E - 384) -> getr Rc (reg 8) = Z_to_bv 64 E -> getr Rc (reg 9) = Z_to_bv 64 (E - 384) ->
  getr Rc (reg 18) = Z_to_bv 64 (F / 8 + 2147450880) -> getr Rc (reg 23) = Z_to_bv 64 2147450880 ->          (* [comment removed for export] *)
  140735332487616 <= E <= 140737488355328 -> aligned E 32 -> L5.writable RSEGS MV (E - 384) 384 ->
  L5.img_clear MV 860160 884736 -> L5.u64_at RSEGS MV 911160 2147450880 -> L5.u32_at RSEGS MV 911168 1 -> L5.u64_at RSEGS MV 885800 837440 ->
  4096 <= F <= 140737488354816 -> aligned F 32 -> L5.defined MV F 512 -> L5.writable RSEGS MV F 512 ->
  (2147446784 + 17592186048512 <= F \/ F + 512 <= 2147446784) -> L5.writable RSEGS MV (F / 8 + 2147450880) 64 -> L5.u64_at RSEGS MV (F + 504) fl ->
  4096 <= fl <= 140737488355327 -> L5.writable RSEGS MV fl 1 -> (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784) -> (F + 512 <= fl \/ fl + 1 <= F) ->
  (E - 384 + 384 <= F \/ F + 512 <= E - 384) -> (E - 384 + 384 <= fl \/ fl + 1 <= E - 384) -> (65536 + 6438912 <= F \/ F + 512 <= 65536) -> (65536 + 6438912 <= fl \/ fl + 1 <= 65536) ->
  L5.u64_at RSEGS MV (E - 360) F ->          (* [comment removed for export] *)
  exists (fx9 : FPState) R9 M9v, msteps RSEGS (st fx Rc pc0 MV) (st fx9 R9 0x93d90 M9v) /\ mem_grows MV M9v
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ Wpad F 512 fl a -> M9v (Z_to_bv 64 a) = MV (Z_to_bv 64 a))
    /\ L5.u8_at RSEGS M9v fl 0 /\ getr R9 (reg 10) = w24
    /\ (forall k, In k [2; 3; 4; 8; 9]%nat -> getr R9 (reg k) = getr Rc (reg k)).
Proof.
  intros qMS MG1 qFZ qKS qR1 qR10 qR11 qR22 G2 G8 G9 G18 G23 ER EA WSv IMGC CSB CUAR RMS FR FA FDEFv FWv FBIG FSHWv FLCv FLR FLWv FLBIG FLA SFA SFLA IFA IFLA C360.
  assert (RG : 0 <= E < 2 ^ 64 /\ 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64) by (clear - ER FR FLR; lia). destruct RG as (ERG & FRG & FLRG).
  (* [comment removed for export] *)
  assert (AG1 : forall i, 65536 <= i < 6504448 -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
  { intros i Hi. apply qFZ. clear - Hi; lia. clear - Hi IFA; lia. clear - Hi FR FBIG; lia. }
  assert (RMS1 : L5.u64_at RSEGS M1v 885800 837440). { eapply L5C.u64_at_agree. 4: exact RMS. 2: clear; lia. 2: clear; lia. intros i Hi. apply AG1. clear - Hi; lia. }
  assert (IMGC1 : L5.img_clear M1v 860160 884736). { intros i Hi. rewrite AG1 by (clear - Hi; lia). apply IMGC. exact Hi. }
  assert (CSB1 : L5.u64_at RSEGS M1v 911160 2147450880). { eapply L5C.u64_at_agree. 4: exact CSB. 2: clear; lia. 2: clear; lia. intros i Hi. apply AG1. clear - Hi; lia. }
  assert (CUAR1 : L5.u32_at RSEGS M1v 911168 1).
  { unfold L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS MV M1v 4 911168 ltac:(clear; lia) ltac:(cbn; clear; lia)). exact CUAR. intros i Hi. apply AG1. cbn in Hi. clear - Hi; lia. }
  pose proof (tpQt_conc fx1 R1 M1v (fun j => match j with 2%nat => U R1 2 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx2 & R2 & M2v & _ & tFR & _ & (tMS & tKS & tR6 & tR11 & tR12)).
  assert (E2 : M2v = M1v) by (apply mem_eq_of_agree; intros a Ha; apply tFR). subst M2v.
  (* [comment removed for export] *)
  set (sh := F / 8 + 2147450880) in *.
  assert (SHR : 2147450880 <= sh /\ sh + 64 <= 17594333495296).
  { subst sh. clear - FR. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono F (2 ^ 47 - 512) 8 ltac:(lia) ltac:(lia)). change ((2 ^ 47 - 512) / 8) with 17592186044352 in H0. lia. }
  assert (FSHW1 : L5.writable RSEGS M1v sh 64). { eapply L5.writable_grows. exact MG1. exact FSHWv. }
  destruct (as0_fill_spec_memset fx2 M1v (Z_to_bv 64 sh) (Z_to_bv 64 245) 64 R2 (Z_to_bv 64 605356)) as (R3 & MS3 & KO3 & _).
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
  assert (KR3 : forall j, (0 < j < 32)%nat -> ~ In j APC.caller_saved -> In j KS_tpQt -> In j [2; 3; 4; 8; 9; 18; 23]%nat -> getr R3 (reg j) = getr Rc (reg j)).
  { intros j Hj Hc H1 H2. rewrite (kept_reg R2 R3 j KO3 Hj Hc). rewrite (tKS j H1). apply qKS. exact H2. }
  (* [comment removed for export] *)
  assert (WS3 : L5.writable RSEGS M3v (E - 384) 384). { eapply L5.writable_grows. exact MG3. eapply L5.writable_grows. exact MG1. exact WSv. }
  assert (AGI3 : forall i, 65536 <= i < 6504448 -> M3v (Z_to_bv 64 i) = M1v (Z_to_bv 64 i)) by (intros i Hi; apply AG3; [clear - Hi; lia | clear - Hi SHR; lia]).
  assert (IMGC3 : L5.img_clear M3v 860160 884736). { intros i Hi. rewrite AGI3 by (clear - Hi; lia). apply IMGC1. exact Hi. }
  assert (CSB3 : L5.u64_at RSEGS M3v 911160 2147450880). { eapply L5C.u64_at_agree. 4: exact CSB1. 2: clear; lia. 2: clear; lia. intros i Hi. apply AGI3. clear - Hi; lia. }
  assert (CUAR3 : L5.u32_at RSEGS M3v 911168 1).
  { unfold L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS M1v M3v 4 911168 ltac:(clear; lia) ltac:(cbn; clear; lia)). exact CUAR1. intros i Hi. apply AGI3. cbn in Hi. clear - Hi; lia. }
  assert (FDEF3 : L5.defined M3v F 512). { eapply L5.defined_grows. exact MG3. eapply L5.defined_grows. exact MG1. exact FDEFv. }
  assert (FW3 : L5.writable RSEGS M3v F 512). { eapply L5.writable_grows. exact MG3. eapply L5.writable_grows. exact MG1. exact FWv. }
  assert (FSHW3 : L5.writable RSEGS M3v (F / 8 + 2147450880) 64). { eapply L5.writable_grows. exact MG3. exact FSHW1. }
  assert (FLW3 : L5.writable RSEGS M3v fl 1). { eapply L5.writable_grows. exact MG3. eapply L5.writable_grows. exact MG1. exact FLWv. }
  assert (FLC3 : L5.u64_at RSEGS M3v (F + 504) fl).
  { eapply L5C.u64_at_agree. 4: exact FLCv. 2: clear - FR; lia. 2: clear - FR; lia. intros i Hi. rewrite AG3. apply qFZ. clear - Hi FR; lia. clear - Hi; lia.
    clear - Hi FR FBIG SHR; subst sh; lia. clear - Hi FR; lia. clear - Hi FR FBIG SHR; lia. }
  assert (C360_3 : L5.u64_at RSEGS M3v (E - 360) F).
  { eapply L5C.u64_at_agree. 4: exact C360. 2: clear - ER; lia. 2: clear - ER; lia. intros i Hi. rewrite AG3. apply qFZ. clear - Hi ER; lia. clear - Hi SFA; lia.
    clear - Hi ER SHR; subst sh; lia. clear - Hi ER; lia. clear - Hi ER SHR; lia. }
  assert (Y2 : getr R3 (reg 2) = Z_to_bv 64 (E - 384)). { rewrite KR3. exact G2. clear; lia. unfold APC.caller_saved; cbn [In]; clear; lia. inl. in_tac. }
  assert (Y8 : getr R3 (reg 8) = Z_to_bv 64 E). { rewrite KR3. exact G8. clear; lia. unfold APC.caller_saved; cbn [In]; clear; lia. inl. in_tac. }
  assert (Y9 : getr R3 (reg 9) = Z_to_bv 64 (E - 384)). { rewrite KR3. exact G9. clear; lia. unfold APC.caller_saved; cbn [In]; clear; lia. inl. in_tac. }
  assert (Y18 : getr R3 (reg 18) = Z_to_bv 64 (F / 8 + 2147450880)). { rewrite KR3. exact G18. clear; lia. unfold APC.caller_saved; cbn [In]; clear; lia. inl. in_tac. }
  assert (Y23 : getr R3 (reg 23) = Z_to_bv 64 2147450880). { rewrite KR3. exact G23. clear; lia. unfold APC.caller_saved; cbn [In]; clear; lia. inl. in_tac. }
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
  split. { rewrite eR10. rewrite (kept_reg R2 R3 22 KO3) by (first [clear; lia | unfold APC.caller_saved; cbn [In]; clear; lia]). rewrite (tKS 22%nat) by inl. exact qR22. }
  intros j Hj. rewrite (eKS j) by (revert j Hj; apply L5K.incl_b; vm_compute; reflexivity).
  apply KR3. cbn [In] in Hj; clear - Hj; lia. unfold APC.caller_saved. cbn [In] in Hj |- *. clear - Hj. lia.
  revert j Hj; apply L5K.incl_b; vm_compute; reflexivity. revert j Hj; apply L5K.incl_b; vm_compute; reflexivity.
Qed.


End SCFG_1.
End L5AE3PD.
