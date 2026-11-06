(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnArith BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr ShiftPure.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR2 Require W_rshift1.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitAF BnCallAF W_callsAF.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import UbStructF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2316824 => 2
  | 2316828 => 1
  | 2316832 => 2
  | 2316900 => 2
  | 2316904 => 1
  | 2316908 => 2
  | 2316960 => 1
  | 2316968 => 1
  | 2316972 => 1
  | 2316976 => 2
  | 2316980 => 2
  | 2317032 => 2
  | 2317044 => 1
  | 2317048 => 1
  | 2317052 => 2
  | 2317056 => 1
  | 2317060 => 1
  | 2317064 => 1
  | 2317068 => 1
  | 2317072 => 2
  | 2317076 => 2
  | 2317080 => 1
  | 2317084 => 2
  | 2317108 => 1
  | 2317112 => 1
  | 2317116 => 2
  | 2317120 => 1
  | 2317124 => 1
  | 2317128 => 1
  | 2317132 => 2
  | 2317136 => 2
  | 2317140 => 1
  | 2317144 => 2
  | 2317204 => 1
  | 2317208 => 1
  | 2317240 => 2
  | 2317244 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Ltac hide_ors := repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
Ltac unhide := repeat match goal with H : hide _ |- _ => apply hide_elim in H end.
Definition BN_RSHIFT1 : Z := 0x2359c4.
Definition BN_RSHIFT1_STACK : Z := 80.

Local Notation rs1_res := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_rshift1.rs1_res.
Local Notation rs1_top := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_rshift1.rs1_top.
Local Notation rs1_bn := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_rshift1.rs1_bn.
Local Notation rs1_mix := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_rshift1.rs1_mix.
Local Notation wlimbs_upd := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_rshift1.wlimbs_upd.
Local Notation wlimbs_nth := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_rshift1.wlimbs_nth.
Local Notation rs1_res_length := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_rshift1.rs1_res_length.
Local Notation rs1_res_limbs := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_rshift1.rs1_res_limbs.
Local Notation rs1_res_mid := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_rshift1.rs1_res_mid.
Local Notation rs1_mix_length := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_rshift1.rs1_mix_length.
Local Notation rs1_mix_nth_lo := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_rshift1.rs1_mix_nth_lo.
Local Notation rs1_mix_step := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_rshift1.rs1_mix_step.
Local Notation rs1_mix_init := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_rshift1.rs1_mix_init.
Local Notation rs1_mix_0 := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_rshift1.rs1_mix_0.
Local Notation rs1_or_machine := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_rshift1.rs1_or_machine.
Local Notation rs1_shr_machine := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_rshift1.rs1_shr_machine.
Local Notation rs1_top_machine := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_rshift1.rs1_top_machine.
Local Notation rs1_top_Z := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_rshift1.rs1_top_Z.
Local Notation rs1_top_le := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_rshift1.rs1_top_le.

Lemma rs1_bodyA : forall (Q : machine_state -> Prop) (buf : list Z) (top : nat) (D : Z) (F : bvmap 5 word) (fc : bv 32)
    (x1 x2 gp tp x8 x9 x12 x18 x19 s6 s7 s8 s9 s10 s11 x29 x30 x31 : word)
    (k : nat) (m0 m1 : mem) (x7 x28 : word),
  limbs buf -> (top <= length buf)%nat -> (k + 2 <= top)%nat -> Z.of_nat (length buf) < 2 ^ 31 ->
  acc bgbsegs m0 D (8 * Z.of_nat (length buf)) -> D mod 8 = 0 -> (0 <= D /\ D + 8 * Z.of_nat (length buf) <= 140737488355328) -> 8 <= D ->
  offshW [(D, D + 8 * Z.of_nat (length buf))] ->
  munch [(D, D + 8 * Z.of_nat (length buf))] m0 m1 -> wmono bgbsegs m0 m1 ->
  u64arr bgbsegs m1 D (wlimbs (rs1_mix buf top (S k))) -> mem_inv bgbsegs m1 ->
  (forall (m' : mem) (y7 y28 : word),
      u64arr bgbsegs m' D (wlimbs (rs1_mix buf top k)) -> munch [(D, D + 8 * Z.of_nat (length buf))] m0 m' -> wmono bgbsegs m0 m' -> mem_inv bgbsegs m' ->
      evt bgbsegs Q (MS (mkR x1 x2 gp tp (Z_to_bv 64 (nth k buf 0)) (Z_to_bv 64 1) y7 x8 x9 (Z_to_bv 64 (D + 8 * (Z.of_nat k - 1))) (Z_to_bv 64 (D + 8 * (Z.of_nat k - 1))) x12
                              (Z_to_bv 64 (D + 8 * (Z.of_nat k - 1))) (Z_to_bv 64 (Z.of_nat k + 1)) (Z_to_bv 64 (8 * (Z.of_nat k - 1)))
                              (Z_to_bv 64 (18446744073709551615 - D)) (Z_to_bv 64 (18446744073709551615 - D)) x18 x19
                              (Z_to_bv 64 SHB) (Z_to_bv 64 (D + 8 * (Z.of_nat k - 1))) s6 s7 s8 s9 s10 s11 y28 x29 x30 x31)
                         F (Z_to_bv 64 0x235c10) fc None m' (seg_rom bgbsegs))) ->
  evt bgbsegs Q (MS (mkR x1 x2 gp tp (Z_to_bv 64 (nth (S k) buf 0)) (Z_to_bv 64 1) x7 x8 x9 (Z_to_bv 64 (D + 8 * Z.of_nat k)) (Z_to_bv 64 (D + 8 * Z.of_nat k)) x12
                          (Z_to_bv 64 (D + 8 * Z.of_nat k)) (Z_to_bv 64 (Z.of_nat k + 2)) (Z_to_bv 64 (8 * Z.of_nat k))
                          (Z_to_bv 64 (18446744073709551615 - D)) (Z_to_bv 64 (18446744073709551615 - D)) x18 x19
                          (Z_to_bv 64 SHB) (Z_to_bv 64 (D + 8 * Z.of_nat k)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x235bb8) fc None m1 (seg_rom bgbsegs)).
Proof.
  intros Q buf top D F fc x1 x2 gp tp x8 x9 x12 x18 x19 s6 s7 s8 s9 s10 s11 x29 x30 x31 k m0 m1 x7 x28 LBF HT HK L31 ACC AL BD D8 OFF MU WM U MI K.
  pose proof (u64arr_bound bgbsegs _ _ _ U) as UB. rewrite wlimbs_len, rs1_mix_length in UB by lia.
  assert (LM : Z.of_nat (length (wlimbs (rs1_mix buf top (S k)))) = Z.of_nat (length buf)) by (rewrite wlimbs_len, rs1_mix_length by lia; reflexivity).
  pose proof (limbs_nth buf k LBF) as Lk. pose proof (limbs_nth buf (S k) LBF) as LSk. unfold limb in Lk, LSk. rewrite BW_lit in Lk, LSk.
  assert (NTH : nth_error (wlimbs (rs1_mix buf top (S k))) (Z.to_nat (Z.of_nat k)) = Some (Z_to_bv 64 (nth k buf 0))).
  { rewrite <- (rs1_mix_nth_lo buf top (S k) k) by lia. apply wlimbs_nth. rewrite rs1_mix_length; lia. }
  pose proof (u64arr_read bgbsegs m1 D _ (Z.of_nat k) _ (wa (D + 8 * Z.of_nat k)) U NTH ltac:(lia) eq_refl) as RD.
  unfold SHLO, SHHI in OFF.
  assert (KR : 0 <= 8 * Z.of_nat k /\ D + 8 * Z.of_nat k + 8 <= D + 8 * Z.of_nat (length buf)) by lia.

  ub.
  do 2 step. shl_limb ACC AL BD (Z.of_nat k). chk0.
  do 2 step. shl_limb ACC AL BD (Z.of_nat k). chk0.

  step. step. clear RD. step. step. step. step. step. step. rewrite rs1_or_machine by lia. rewrite <- (rs1_res_mid buf top k) by lia.

  assert (IDX : 0 <= Z.of_nat k < Z.of_nat (length (wlimbs (rs1_mix buf top (S k))))) by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (u64arr_store_ok bgbsegs mx D _ (Z.of_nat k) (wa (D + 8 * Z.of_nat k)) U IDX eq_refl) as SOKW;
    pose proof (u64arr_write bgbsegs mx D _ (Z.of_nat k) (Z_to_bv 64 (nth k (rs1_res buf top) 0)) U IDX) as U2 end.
  rewrite Nat2Z.id, wlimbs_upd, rs1_mix_step in U2 by (rewrite ?rs1_mix_length; lia).
  clear U. step. store_done.

  step. step. step.
  setreg 10%Z (Z_to_bv 64 (D + 8 * (Z.of_nat k - 1))) ltac:(f_equal; lia).
  setreg 14%Z (Z_to_bv 64 (Z.of_nat k + 1)) ltac:(f_equal; lia).
  setreg 15%Z (Z_to_bv 64 (8 * (Z.of_nat k - 1))) ltac:(f_equal; lia).

  eapply K; [exact U2 | exact MU | assumption | assumption].
Qed.

Lemma rs1_loopA : forall (Q : machine_state -> Prop) (buf : list Z) (top : nat) (D : Z) (F : bvmap 5 word) (fc : bv 32)
    (x1 x2 gp tp x8 x9 x12 x18 x19 s6 s7 s8 s9 s10 s11 x29 x30 x31 : word)
    (k : nat) (m0 m1 : mem) (x7 x28 : word),
  limbs buf -> (top <= length buf)%nat -> (k + 2 <= top)%nat -> Z.of_nat (length buf) < 2 ^ 31 ->
  acc bgbsegs m0 D (8 * Z.of_nat (length buf)) -> D mod 8 = 0 -> (0 <= D /\ D + 8 * Z.of_nat (length buf) <= 140737488355328) -> 8 <= D ->
  offshW [(D, D + 8 * Z.of_nat (length buf))] ->
  munch [(D, D + 8 * Z.of_nat (length buf))] m0 m1 -> wmono bgbsegs m0 m1 ->
  u64arr bgbsegs m1 D (wlimbs (rs1_mix buf top (S k))) -> mem_inv bgbsegs m1 ->
  (forall (m' : mem) (y7 y15 y28 : word),
      u64arr bgbsegs m' D (wlimbs (rs1_res buf top)) -> munch [(D, D + 8 * Z.of_nat (length buf))] m0 m' -> wmono bgbsegs m0 m' -> mem_inv bgbsegs m' ->
      evt bgbsegs Q (MS (mkR x1 x2 gp tp (Z_to_bv 64 (nth 0 buf 0)) (Z_to_bv 64 1) y7 x8 x9 (Z_to_bv 64 (D - 8)) (Z_to_bv 64 (D - 8)) x12
                              (Z_to_bv 64 (D - 8)) (Z_to_bv 64 1) y15
                              (Z_to_bv 64 (18446744073709551615 - D)) (Z_to_bv 64 (18446744073709551615 - D)) x18 x19
                              (Z_to_bv 64 SHB) (Z_to_bv 64 (D - 8)) s6 s7 s8 s9 s10 s11 y28 x29 x30 x31)
                         F (Z_to_bv 64 0x235c14) fc None m' (seg_rom bgbsegs))) ->
  evt bgbsegs Q (MS (mkR x1 x2 gp tp (Z_to_bv 64 (nth (S k) buf 0)) (Z_to_bv 64 1) x7 x8 x9 (Z_to_bv 64 (D + 8 * Z.of_nat k)) (Z_to_bv 64 (D + 8 * Z.of_nat k)) x12
                          (Z_to_bv 64 (D + 8 * Z.of_nat k)) (Z_to_bv 64 (Z.of_nat k + 2)) (Z_to_bv 64 (8 * Z.of_nat k))
                          (Z_to_bv 64 (18446744073709551615 - D)) (Z_to_bv 64 (18446744073709551615 - D)) x18 x19
                          (Z_to_bv 64 SHB) (Z_to_bv 64 (D + 8 * Z.of_nat k)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x235bb8) fc None m1 (seg_rom bgbsegs)).
Proof.
  intros Q buf top D F fc x1 x2 gp tp x8 x9 x12 x18 x19 s6 s7 s8 s9 s10 s11 x29 x30 x31 k.
  induction k as [|k IH]; intros m0 m1 x7 x28 LBF HT HK L31 ACC AL BD D8 OFF MU WM U MI K.
  - eapply rs1_bodyA; [exact LBF| exact HT| exact HK| exact L31| exact ACC| exact AL| exact BD| exact D8| exact OFF| exact MU| exact WM| exact U| exact MI|].
    intros m' y7 y28 U' MU' WM' MI'.
    step. if_cases KE; zify_cond KE; [exfalso; rewrite ?unsigned_lit in KE by lia; lia|]. clear KE.
    setreg 10%Z (Z_to_bv 64 (D - 8)) ltac:(f_equal; lia).
    setreg 14%Z (Z_to_bv 64 1) ltac:(f_equal; lia).
    rewrite rs1_mix_0 in U'. eapply K; [exact U'| exact MU'| exact WM'| exact MI'].
  - eapply rs1_bodyA; [exact LBF| exact HT| exact HK| exact L31| exact ACC| exact AL| exact BD| exact D8| exact OFF| exact MU| exact WM| exact U| exact MI|].
    intros m' y7 y28 U' MU' WM' MI'.
    step. if_cases KE; zify_cond KE; [| exfalso; rewrite ?unsigned_lit in KE by lia; lia]. clear KE.
    setreg 10%Z (Z_to_bv 64 (D + 8 * Z.of_nat k)) ltac:(f_equal; lia).
    setreg 14%Z (Z_to_bv 64 (Z.of_nat k + 2)) ltac:(f_equal; lia).
    setreg 15%Z (Z_to_bv 64 (8 * Z.of_nat k)) ltac:(f_equal; lia).
    eapply (IH m0 m'); [exact LBF| exact HT| lia| exact L31| exact ACC| exact AL| exact BD| exact D8| exact OFF| exact MU'| exact WM'| exact U'| exact MI'|].
    intros m'' z7 z15 z28 U'' MU'' WM'' MI''. eapply K; [exact U''| exact MU''| exact WM''| exact MI''].
Qed.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma BN_rshift1_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (rx : bnref) (ax : Z),
  bn_preA Σ ls m OW LB PL EA sp lo BN_RSHIFT1_STACK MC ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_RSHIFT1 (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> ref_at ls OW PL rx ax -> wref PL rx -> a0 = wz ax -> a1 = wz ax ->
  implA (BN_rshift1 (tree_ops bptr) rx rx ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC
              (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = wz 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx ls) <> Some q -> In (q, A, n) OW')))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_RSHIFT1) fc None m (seg_rom bgbsegs)).
Proof.
  intros until ax. intros PRE UW CTX -> HAx WRx -> ->.
  pose proof (proj1 WRx : not_one rx) as NROx.
  pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
  pose proof LO as LO'. unfold BN_RSHIFT1_STACK in LO'.
  unfold BN_RSHIFT1, MallocRep.wz.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1' & C2' & C3'). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 64, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HAx) as HVx.
  set (bx := getbn rx ls) in *.
  assert (LBX : length (bn_buf bx) = bn_dmax bx) by reflexivity.
  unfold BN_rshift1, BN_zero, bbind, bget, bset, bret. rewrite Nat.eqb_refl. cbn [bind ret tree_ops tbind fst snd]. fold bx.
  apply implA_from_evt.
  carve_frame 64%nat ST.

  do 9 step. do 6 step. step.

  lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j :: _) => set (jfr := j) in *; clearbody jfr end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -64, bv_unsigned sp)]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
  pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
  assert (EV : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MC Σ ls OW m
                 [CB 8 jfr; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] 0 Σ ls m1 OW).
  { unfold cenvA, cenv_ok.
    split; [split; [exact CEIL|]; split; [lia|]; split; [lia|]; split; [unfold USTACK_TOP; lia|]; split; [exact SP16|];
            split; [clear - SP16; Z.div_mod_to_equations; lia|]; split; [exact CNT|]; split; [exact CRED|]; split; [exact FROK|]; split; [exact FAL| exact NOFR]|].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))|].
    split; [exact ST|]. split; [exact MI|].
    split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU HWL CEIL ltac:(lia))|].
    split; [lia|]. split; [apply cnt_eq_refl|]. split; [apply refs_stable_refl|].
    split; [cbn [app]; exact FR|]. split; [cbn; lia|]. unfold uw_opt.
    eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
  pose proof EV as (OK & HEAP1 & _).

  assert (EPI : forall (Σ1 : rts RT) (ls1 : bstate bptr) (m2 : mem) (OW2 : list block) (used : Z) (FT : bvmap 5 word) (fcT : bv 32)
                       (q1 q5 q6 q7 q9 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q28 q29 q30 q31 : word),
      cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MC Σ ls OW m
            [CB 8 jfr; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] used Σ1 ls1 m2 OW2 ->
      lib_state ls1 m2 OW2 PL EA -> used <= MC ->
      (forall q A n, In (q, A, n) OW -> bn_d bx <> Some q -> In (q, A, n) OW2) ->
      implA (TRet (tt, ls1)) Σ1
        (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC
                  (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = Z_to_bv 64 1 /\ (forall q A n, In (q, A, n) OW -> bn_d bx <> Some q -> In (q, A, n) OW')))
        (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 TP_A) q5 q6 q7 sp q9 (Z_to_bv 64 1) q11 q12 q13 q14 q15 q16 q17
                 q18 q19 q20 q21 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
            FT (Z_to_bv 64 0x235c34) fcT None m2 (seg_rom bgbsegs))).
  { intros Σ1 ls1 m2 OW2 used FT fcT q1 q5 q6 q7 q9 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q28 q29 q30 q31 EV1 LS2 USED BST.
    clear MU WM ST MI FR HWL WOK LS1 HEAP1 EV OK OFF SHB1 SHB2 HEAP LS PARTS PRE UW HVx.
    pose proof EV1 as (OK1 & HEAP2 & ST2 & MI2 & AXP2 & CR2 & CNT2 & RS2 & FR2 & FSZ2 & UW2).
    cbn [app] in FR2.
    apply implA_ret_evt.
    do 7 step. release_frame FR2 ST2 (bv_unsigned sp). step. step.
    apply evt_done.
    unfold bn_postA. do 17 eexists. exists m2, OW2, PL. split; [reflexivity|]. cbn [fst snd].
    split; [exact HEAP2|]. split; [exact LS2|]. split; [exact ST2|]. split; [exact MI2|]. split; [exact AXP2|].
    split; [clear - CR2 USED; lia|]. split; [exact CNT2|]. split; [exact RS2|].
    split; [reflexivity|]. split; [reflexivity| exact BST]. }

  assert (LOF16 : lo <= bv_unsigned sp + -64 - 16) by (clear - LO'; lia).
  eapply (is_zero_callA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MC Σ ls OW m LOF16) with (r := rx) (ar := ax);
    [exact EV | exact LS1 | exact HAx | exact NROx |].
  intros m2 y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 EV2 LS2.
  rewrite (ret_pc_even 2316804) by (clear; lia).
  fold bx.

  clear MU WM OFF SHB1 SHB2 HEAP LS PARTS ST MI FR HWL WOK LS1 HEAP1 EV OK.
  pose proof EV2 as (OK2 & HEAP2 & ST2 & MI2 & _ & _ & _ & _ & FR2 & FSZ2 & _). cbn [app] in FR2.
  pose proof (AH_nodup_l _ _ _ _ HEAP2) as ND.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
  destruct (lib_state_open [] ls m2 OW PL EA rx ax LS2 ND HAx ltac:(intros []) NROx) as ((Dx & BNx & ARRx) & (OKx1 & OKx2 & OKx3 & OKx4) & LSH).
  destruct (bn_arr_facts_w ls OW PL EA (bv_unsigned sp) USTACK_TOP Σ LB m2 rx Dx HEAP2 PARTS FROK HVx WRx ARRx) as (Ux & LENx & Dx0' & DxC & DxI & DSEPx).
  fold bx in BNx, ARRx, Ux, LENx, DxC, DxI, DSEPx, OKx1, OKx2, OKx3, OKx4.
  pose proof (DSEPx rx ax HAx) as SEPxx.
  destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP2 PARTS NOFR HAx NROx) as (qx & Ax & nx & Hinx & Rx1 & Rx2).
  pose proof (AH_range_in _ _ _ _ _ _ _ HEAP2 Hinx) as (AX0 & _ & _ & AXC & _).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP2 LS2 NOFR HAx NROx) as (ACX & ALX & OFX).
  pose proof ARRx as ARRo. apply (fun ARRnb__ => bn_arr_nofr PL rx m2 OW Dx _ PWF NOFR NROx ARRnb__ ltac:(solve_nbuf)) in ARRo.
  destruct (arr_shA _ _ _ _ _ _ HEAP2 ARRo) as (ACDX & ALDX & OFDX).
  unfold bn_cells, BnRepDefs.bn_cells, MallocRep.wz in BNx. unfold SHLO, SHHI in *. unfold BG_DMAX in OKx3.
  assert (X0 : 0 < ax) by (clear - AX0 Rx1; lia).
  assert (XC : ax + 24 <= BnHeapA.ACEIL) by (clear - AXC Rx2; lia).
  destruct (AH_shb _ _ _ _ HEAP2) as (SHB1 & SHB2).

  destruct (bn_top bx =? 0)%nat eqn:ET; cbv beta; fold bx; step; if_cases KT; zify_cond KT; try (exfalso; rewrite ?unsigned_lit in KT by (clear; cbn; lia); cbn in KT; clear - KT; lia).
  -
    apply Nat.eqb_eq in ET. clear KT.
    step. step.

    eapply evt_cut.
    { eapply (BN_zero_ex_specA (Z_to_bv 64 2316816) (Z_to_bv 64 (bv_unsigned sp + -64))) with (A := ax) (D := Dx) (b := bx) (lo := lo);
        [ unfold bn_cells, BnRepDefs.bn_cells, MallocRep.wz; exact BNx | rewrite ESP; exact ST2 | rewrite ESP; clear - LO'; lia | exact MI2
        | rewrite ESP; unfold BnHeapA.ACEIL in *; clear - XC CEIL LO'; lia
        | exact (AH_shb _ _ _ _ HEAP2) | exact ACX | exact ALX | unfold SHHI, BnHeapA.ACEIL in *; clear - CEIL C1' C2' C3'; lia | exact OFX | reflexivity | exact X0]. }
    intros ms' (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m3 & -> & MUz & WMz & MIz & STz & SRz).
    rewrite ESP in MUz, STz.
    rewrite (ret_pc_even 2316816) by (clear; lia).
    assert (FR3 : rw_cells bgbsegs m3 (bv_unsigned sp + -64) ([CB 8 jfr; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] ++ [C8 s0; C8 ra])).
    { eapply rw_cells_transport; [exact FR2 | exact MUz | exact WMz |]. cbn. unfold BnHeapA.ACEIL in *. clear - XC CEIL LO'. lia. }
    step. step. apply evt_done.

    assert (HWLz : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -64 - 16, bv_unsigned sp + -64); (ax, ax + 24)]).
    { constructor; [left; cbn [fst snd]; clear - LO'; lia|]. constructor; [|constructor].
      w_lib_ref HAx NROx. }
    assert (WOKz : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) [rx]) [(bv_unsigned sp + -64 - 16, bv_unsigned sp + -64); (ax, ax + 24)]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; clear - CEIL LO'; lia|]. constructor; [|constructor].
      eapply (w_struct OW LB ls PL EA (bv_unsigned sp) false [rx] _ rx ax); [left; reflexivity | exact HAx | exact NROx | cbn; clear; lia | cbn; clear; lia]. }
    eapply (EPI Σ (setbn rx (bn_zero_pure bx) ls) m3 OW 0);
      [ apply cenv_setbnA; [| exact HVx | reflexivity];
        eapply cenv_silentA; [exact EV2 | exact LS2 | exact MUz | exact WMz | exact HWLz | exact STz | exact MIz | exact FR3 | exact FSZ2]
      | | unfold MC; clear; lia | intros q0 A0 n0 Hq0 _; exact Hq0 ].
    unfold lib_state. eapply (lib_state_close [] ls m3 OW PL EA rx ax); [| exact ND | exact HAx | exact NROx | | |].
    + eapply (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP); [exact HEAP2 | exact LSH | exact MUz | exact WMz | exact FROK | exact WOKz].
    + exists Dx. split; [exact SRz|]. eapply bn_arr_of_u64arr; [exact ARRx|].
      eapply u64arr_transport; [exact Ux | exact MUz | exact WMz |]. cbn [disjoint_from]. rewrite LENx. unfold BnHeapA.ACEIL in *. clear - SEPxx DxC Dx0' CEIL LO'. lia.
    + unfold bg_ok, bn_zero_pure, bn_dmax in *. cbn [bn_top bn_buf bn_flags]. unfold BG_DMAX. repeat split; [exact OKx1 | clear; lia | exact OKx3 | exact OKx4].
    + apply ids_ok_setbn_same; [exact IDS | exact HVx | reflexivity].
  -
    apply Nat.eqb_neq in ET. clear KT.

    assert (HDx : exists px, bn_d bx = Some px /\ In (px, Dx, 8 * Z.of_nat (bn_dmax bx)) OW).
    { unfold BnRepDefs.bn_arr in ARRo. destruct (bn_d bx) as [px|]; [exists px; split; [reflexivity| exact (proj1 ARRo)]|].
      exfalso. destruct ARRo as [_ E]. unfold bn_dmax in OKx2. rewrite E in OKx2. cbn in OKx2. clear - OKx2 ET. lia. }
    destruct HDx as (px & Edx & Hinpx).
    assert (TOPZ : 0 < Z.of_nat (bn_top bx) <= Z.of_nat (bn_dmax bx) /\ Z.of_nat (bn_dmax bx) <= 512) by (clear - ET OKx2 OKx3; unfold bn_dmax in *; lia).
    assert (BDX : 0 <= Dx /\ Dx + 8 * Z.of_nat (bn_dmax bx) <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - Dx0' DxC C1' C2' C3'; lia).
    pose proof (AH_range _ _ _ _ _ _ _ HEAP2 Hinpx) as (PX0 & PX16 & _).
    assert (PX8 : 8 <= Dx) by (clear - PX0 PX16; Z.div_mod_to_equations; lia).
    pose proof (limbs_nth (bn_buf bx) (bn_top bx - 1) OKx1) as LT. unfold limb in LT. rewrite BW_lit in LT.
    set (t := nth (bn_top bx - 1) (bn_buf bx) 0) in *.
    pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp); (ax, ax + 24); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]%Z m2) as MU3.
    pose proof (wmono_refl bgbsegs m2) as WM3.
    assert (OFF3 : offshW [(bv_unsigned sp + -64, bv_unsigned sp); (ax, ax + 24); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]).
    { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. clear - OFX OFDX SPR LO' CEIL C1' C2' C3'. lia. }

    ub.
    do 3 step. shl_with ACX ALX. chk0.
    do 2 step. shl_with ACX ALX. chk0.
    step. step. rewrite (sx32_small (Z.of_nat (bn_top bx))) by (clear - TOPZ; lia).

    step. if_cases KE; zify_cond KE; [| exfalso; clear - KE; lia]. clear KE.

    ub.
    do 2 step. shl_with ACX ALX. chk0.
    do 3 step. shl_with ACX ALX. step. chk0.
    step.
    setreg 14%Z (Z_to_bv 64 (Z.of_nat (bn_top bx) - 1)) ltac:(f_equal; rewrite (unsigned_lit (Z.of_nat (bn_top bx))) by (clear - TOPZ; lia); rewrite bn_swrap32_small by (clear - TOPZ; lia); clear; lia).
    step.

    ub.

    step. step.
    setreg 15%Z (Z_to_bv 64 (8 * (Z.of_nat (bn_top bx) - 1))) ltac:(f_equal; rewrite (unsigned_lit (Z.of_nat (bn_top bx) - 1)) by (clear - TOPZ; lia); rewrite Z.shiftl_mul_pow2 by (clear; lia); clear; lia).
    setreg 11%Z (Z_to_bv 64 (Dx + 8 * (Z.of_nat (bn_top bx) - 1))) ltac:(f_equal; rewrite ?unsigned_lit by (clear - TOPZ BDX; lia); rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; lia).

    hide_ors. ub. unhide.
    do 2 step. shl_limb ACDX ALDX BDX (Z.of_nat (bn_top bx) - 1). chk0.
    step.
    setreg 12%Z (Z_to_bv 64 (Dx + 8 * (Z.of_nat (bn_top bx) - 1))) ltac:(f_equal; rewrite ?unsigned_lit by (clear - TOPZ BDX; lia); clear; lia).

    hide_ors. ub. unhide.
    do 2 step. shl_limb ACDX ALDX BDX (Z.of_nat (bn_top bx) - 1). chk0.

    assert (NTH : nth_error (wlimbs (bn_buf bx)) (Z.to_nat (Z.of_nat (bn_top bx) - 1)) = Some (Z_to_bv 64 t)).
    { replace (Z.of_nat (bn_top bx) - 1) with (Z.of_nat (bn_top bx - 1)) by (clear - TOPZ; lia). apply wlimbs_nth. unfold bn_dmax in OKx2. clear - OKx2 TOPZ. lia. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (u64arr_read bgbsegs mx Dx (wlimbs (bn_buf bx)) (Z.of_nat (bn_top bx) - 1) (Z_to_bv 64 t) (wa (Dx + 8 * (Z.of_nat (bn_top bx) - 1))) Ux NTH ltac:(clear - TOPZ; lia) eq_refl) as RD end.
    step. clear RD.
    step. rewrite rs1_shr_machine by (clear - LT; lia).

    assert (IDX : 0 <= Z.of_nat (bn_top bx) - 1 < Z.of_nat (length (wlimbs (bn_buf bx)))) by (rewrite LENx; clear - TOPZ; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (u64arr_store_ok bgbsegs mx Dx _ (Z.of_nat (bn_top bx) - 1) (wa (Dx + 8 * (Z.of_nat (bn_top bx) - 1))) Ux IDX eq_refl) as SOKW;
      pose proof (u64arr_write bgbsegs mx Dx _ (Z.of_nat (bn_top bx) - 1) (Z_to_bv 64 (shrw t 1)) Ux IDX) as U2 end.
    replace (Z.to_nat (Z.of_nat (bn_top bx) - 1)) with (bn_top bx - 1)%nat in U2 by (clear - TOPZ; lia).
    rewrite wlimbs_upd in U2 by (rewrite LBX; clear - TOPZ; lia).
    replace (upd (bn_buf bx) (bn_top bx - 1) (shrw t 1)) with (rs1_mix (bn_buf bx) (bn_top bx) (bn_top bx - 1)) in U2
      by (unfold t; symmetry; apply rs1_mix_init; rewrite ?LBX; clear - TOPZ; lia).
    assert (LM1 : Z.of_nat (length (wlimbs (rs1_mix (bn_buf bx) (bn_top bx) (bn_top bx - 1)))) = Z.of_nat (bn_dmax bx)).
    { rewrite wlimbs_len, rs1_mix_length, LBX by (rewrite ?LBX; clear - TOPZ; lia). reflexivity. }
    clear Ux. step. store_done.

    shl_with ACX ALX. chk0.
    step. step. step. rewrite rs1_top_machine, <- (rs1_top_Z (bn_buf bx) (bn_top bx)) by (clear - TOPZ LT; lia).
    pose proof (rs1_top_le (bn_buf bx) (bn_top bx)) as TLE.
    step.

    lazymatch goal with |- evt _ ?Q _ =>
      assert (TAIL : forall (m4 : mem) (q5 q6 q7 q10 q11 q13 q14 q15 q16 q17 q21 q28 : word),
        u64arr bgbsegs m4 Dx (wlimbs (rs1_res (bn_buf bx) (bn_top bx))) ->
        rw_cells bgbsegs m4 ax [C8 (Z_to_bv 64 Dx); C4 (Z_to_bv 64 (Z.of_nat (rs1_top (bn_buf bx) (bn_top bx)))); C4 (Z_to_bv 64 (Z.of_nat (bn_dmax bx)));
                                C4 (Z_to_bv 64 (Z.b2z (bn_neg bx))); C4 (Z_to_bv 64 (bn_flags bx))] ->
        rw_cells bgbsegs m4 (bv_unsigned sp + -64) [CB 8 jfr; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        stk bgbsegs m4 lo (bv_unsigned sp + -64) -> mem_inv bgbsegs m4 ->
        munch [(bv_unsigned sp + -64, bv_unsigned sp); (ax, ax + 24); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]%Z m2 m4 -> wmono bgbsegs m2 m4 ->
        evt bgbsegs Q (MS (mkR (Z_to_bv 64 2316804) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 TP_A) q5 q6 q7 sp (Z_to_bv 64 ax) q10
                                q11 (Z_to_bv 64 (Z.of_nat (rs1_top (bn_buf bx) (bn_top bx)))) q13 q14 q15 q16 q17 (Z_to_bv 64 (Z.of_nat (bn_top bx))) (Z_to_bv 64 ax)
                                (Z_to_bv 64 SHB) q21 s6 s7 s8 s9 s10 s11 q28 y12 y13 y14) F (Z_to_bv 64 0x235c14) fc None m4 (seg_rom bgbsegs)))
    end.
    { intros m4 q5 q6 q7 q10 q11 q13 q14 q15 q16 q17 q21 q28 UR BNr FR3 ST3 MI3 MU4 WM4.
      clear U2 BNx FR2 ST2 MI2 MU3 WM3.
      assert (LRES : length (rs1_res (bn_buf bx) (bn_top bx)) = bn_dmax bx) by (rewrite rs1_res_length; [exact LBX| rewrite LBX; clear - TOPZ; lia]).
      assert (LMR : Z.of_nat (length (wlimbs (rs1_res (bn_buf bx) (bn_top bx)))) = Z.of_nat (bn_dmax bx)) by (rewrite wlimbs_len, LRES; reflexivity).
      assert (HWL3 : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp); (ax, ax + 24); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]).
      { constructor; [left; cbn; clear - LO'; lia|]. constructor; [w_lib_ref HAx NROx|].
        constructor; [right; left; exists (px, Dx, 8 * Z.of_nat (bn_dmax bx)); cbn [blk_addr blk_size fst snd]; split; [exact Hinpx| clear; lia]| constructor]. }
      assert (WOK3 : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) [rx]) [(bv_unsigned sp + -64, bv_unsigned sp); (ax, ax + 24); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]).
      { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; clear - LO' CEIL; lia|].
        constructor; [eapply (w_struct OW LB ls PL EA (bv_unsigned sp) false [rx] _ rx ax); [left; reflexivity| exact HAx| exact NROx| cbn; clear; lia| cbn; clear; lia]|].
        constructor; [eapply (w_limbs OW LB ls PL EA (bv_unsigned sp) false [rx] _ rx px Dx); [left; reflexivity| exact HVx| exact Edx| exact Hinpx| cbn [fst snd]; clear; lia| cbn [fst snd]; fold bx; clear; lia]| constructor]. }
      assert (EBL : length (bn_blocks (rs1_bn bx)) = length (bn_blocks (getbn rx ls))).
      { fold bx. unfold bn_blocks, bn_dmax, rs1_bn, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_rshift1.rs1_bn. cbn [bn_d bn_buf]. rewrite Edx. reflexivity. }

      assert (ENVF : forall m5, munch [(bv_unsigned sp + -64, bv_unsigned sp); (ax, ax + 24); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]%Z m2 m5 -> wmono bgbsegs m2 m5 ->
                       stk bgbsegs m5 lo (bv_unsigned sp + -64) -> mem_inv bgbsegs m5 ->
                       rw_cells bgbsegs m5 (bv_unsigned sp + -64) [CB 8 jfr; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
                       cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MC Σ ls OW m
                             [CB 8 jfr; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] 0 Σ (setbn rx (rs1_bn bx) ls) m5 OW).
      { intros m5 MU5 WM5 ST5 MI5 FR5. apply cenv_setbnA; [| exact HVx | exact EBL].
        eapply cenv_silentA; [exact EV2 | exact LS2 | exact MU5 | exact WM5 | exact HWL3 | exact ST5 | exact MI5 | cbn [app]; exact FR5 | exact FSZ2]. }
      assert (CLOSE : forall m5, rw_cells bgbsegs m5 ax (bn_cells Dx (rs1_bn bx)) -> u64arr bgbsegs m5 Dx (wlimbs (rs1_res (bn_buf bx) (bn_top bx))) ->
                       munch [(bv_unsigned sp + -64, bv_unsigned sp); (ax, ax + 24); (Dx, Dx + 8 * Z.of_nat (bn_dmax bx))]%Z m2 m5 -> wmono bgbsegs m2 m5 ->
                       lib_state (setbn rx (rs1_bn bx) ls) m5 OW PL EA).
      { intros m5 BN5 U5 MU5 WM5. unfold lib_state. eapply (lib_state_close [] ls m5 OW PL EA rx ax); [| exact ND| exact HAx| exact NROx| | |].
        - eapply (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP); [exact HEAP2 | exact LSH | exact MU5 | exact WM5 | exact FROK | exact WOK3].
        - exists Dx. split; [exact BN5|].
          apply (fun ARRnb__ => bn_arr_of_nofr PL rx m5 OW Dx _ PWF NOFR NROx ARRnb__ ltac:(solve_nbuf)).
          unfold BnRepDefs.bn_arr, bn_dmax, rs1_bn, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_rshift1.rs1_bn. cbn [bn_d bn_buf]. rewrite Edx, LRES. split; [exact Hinpx| exact U5].
        - unfold bg_ok, bn_dmax, rs1_bn, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_rshift1.rs1_bn in *. cbn [bn_buf bn_top bn_flags]. rewrite LRES. unfold BG_DMAX.
          split; [apply rs1_res_limbs; exact OKx1|]. split; [clear - TLE OKx2; lia|]. split; [exact OKx3| exact OKx4].
        - apply ids_ok_setbn_same; [exact IDS| exact HVx|]. unfold bn_blocks, bn_dmax, rs1_bn, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_rshift1.rs1_bn. cbn [bn_d bn_buf]. rewrite LRES. reflexivity. }

      step. step. if_cases KN; zify_cond KN.
      -
        apply evt_done.
        eapply (EPI Σ (setbn rx (rs1_bn bx) ls) m4 OW 0);
          [ apply ENVF; [exact MU4 | exact WM4 | exact ST3 | exact MI3 | exact FR3]
          | apply CLOSE; [| exact UR | exact MU4 | exact WM4]
          | unfold MC; clear; lia | intros q0 A0 n0 Hq0 _; exact Hq0 ].
        unfold bn_cells, BnRepDefs.bn_cells, rs1_bn, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_rshift1.rs1_bn, bn_dmax, MallocRep.wz. cbn [bn_d bn_buf bn_top bn_neg bn_flags]. rewrite LRES.
        replace (rs1_top (bn_buf bx) (bn_top bx) =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; rewrite ?unsigned_lit in KN by (clear - TLE TOPZ; lia); clear - KN; lia). exact BNr.
      -
        do 3 step. shl_with ACX ALX. chk0. step.

        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        apply evt_done.
        eapply (EPI Σ (setbn rx (rs1_bn bx) ls) m5 OW 0);
          [ apply ENVF; [exact MU4 | exact WM4 | assumption | assumption | exact FR3]
          | apply CLOSE; [| assumption | exact MU4 | exact WM4]
          | unfold MC; clear; lia | intros q0 A0 n0 Hq0 _; exact Hq0 ].
        unfold bn_cells, BnRepDefs.bn_cells, rs1_bn, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_rshift1.rs1_bn, bn_dmax, MallocRep.wz. cbn [bn_d bn_buf bn_top bn_neg bn_flags]. rewrite LRES.
        replace (rs1_top (bn_buf bx) (bn_top bx) =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; rewrite ?unsigned_lit in KN by (clear - TLE TOPZ; lia); clear - KN; lia). cbn [Z.b2z]. exact BNr. }

    step. rewrite (lts_signed 0 (Z.of_nat (bn_top bx) - 1)) by (clear - TOPZ; lia).
    if_cases K2; zify_cond K2.
    +
      replace (bn_top bx - 1)%nat with 0%nat in U2 by (clear - K2 TOPZ; lia). rewrite rs1_mix_0 in U2.
      eapply TAIL; [exact U2 | exact BNx | exact FR2 | exact ST2 | exact MI2 | exact MU3 | exact WM3].
    +

      ub. do 7 step.

      setreg 14%Z (Z_to_bv 64 (Z.of_nat (bn_top bx - 2) + 2)) ltac:(f_equal; rewrite ?unsigned_lit by (clear - TOPZ; lia); clear - K2; lia).
      setreg 15%Z (Z_to_bv 64 (8 * Z.of_nat (bn_top bx - 2))) ltac:(f_equal; rewrite ?unsigned_lit by (clear - TOPZ; lia); clear - K2; lia).
      setreg 10%Z (Z_to_bv 64 (Dx + 8 * Z.of_nat (bn_top bx - 2))) ltac:(f_equal; rewrite ?unsigned_lit by (clear - TOPZ BDX K2; lia); clear - K2; lia).
      setreg 5%Z (Z_to_bv 64 (nth (S (bn_top bx - 2)) (bn_buf bx) 0)) ltac:(unfold t; f_equal; f_equal; clear - K2; lia).
      setreg 16%Z (Z_to_bv 64 (18446744073709551615 - Dx)) ltac:(f_equal; symmetry; apply zb_lxor_ones; clear - BDX; lia).

      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      replace (bn_top bx - 1)%nat with (S (bn_top bx - 2)) in U2 by (clear - K2; lia).
      assert (ACD3 : acc bgbsegs m3 Dx (8 * Z.of_nat (length (bn_buf bx)))).
      { rewrite LBX. eapply (acc_munch bgbsegs); [exact ACDX | exact MU3 | exact OFF3 | clear - BDX; lia | clear - BDX; lia]. }
      assert (OFFD : offshW [(Dx, Dx + 8 * Z.of_nat (length (bn_buf bx)))]) by (rewrite LBX; cbn [offshW]; unfold SHLO, SHHI; clear - OFDX; lia).
      pose proof (munch_refl [(Dx, Dx + 8 * Z.of_nat (length (bn_buf bx)))]%Z m3) as MUL. pose proof (wmono_refl bgbsegs m3) as WML.

      eapply (rs1_loopA _ (bn_buf bx) (bn_top bx) Dx) with (k := (bn_top bx - 2)%nat) (m0 := m3);
        [exact OKx1 | rewrite LBX; clear - TOPZ; lia | clear - K2; lia | rewrite LBX; clear - TOPZ; lia | exact ACD3 | exact ALDX | rewrite LBX; exact BDX | exact PX8
        | exact OFFD | exact MUL | exact WML | exact U2 | exact MI2 |].
      intros m4 y7' y15' y28' U4 MU4 WM4 MI4.
      rewrite LBX in MU4.
      eapply (rw_cells_transport bgbsegs _ _ m4) in FR2; [| exact MU4 | exact WM4 | cbn; unfold BnHeapA.ACEIL in *; clear - DxC CEIL LO'; lia].
      eapply (rw_cells_transport bgbsegs _ _ m4) in BNx; [| exact MU4 | exact WM4 | cbn; clear - SEPxx; lia].

      eapply TAIL; [exact U4 | exact BNx | exact FR2 | | exact MI4 | | eapply wmono_trans; [exact WM3| exact WM4]].
      * eapply (stk_transport_disjoint bgbsegs _ _ m4); [exact ST2 | exact MU4 | exact WM4 |]. cbn [disjoint_from]. unfold BnHeapA.ACEIL in *. clear - DxC CEIL LO'. lia.
      * eapply munch_trans; [exact MU3|]. eapply munch_weaken; [| exact MU4]. unfold sub_fp; cbn [outside]; intros x Hx. clear - Hx. lia.
Qed.

End WithRT.
