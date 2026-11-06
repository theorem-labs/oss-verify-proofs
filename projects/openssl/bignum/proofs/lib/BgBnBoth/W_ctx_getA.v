(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnModel BnTree BnInv BnSpecs BnMInv.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require StrFun.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA BnRepX ImplA BnIfaceA UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA W_ctxA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2260128 => 2
  | 2260136 => 1
  | 2260140 => 2
  | 2260388 => 1
  | 2260392 => 2
  | 2260404 => 1
  | 2260436 => 2
  | 2260548 => 2
  | 2260552 => 1
  | 2260556 => 2
  | 2260660 => 2
  | 2260664 => 1
  | 2260668 => 2
  | 2260832 => 2
  | 2260836 => 1
  | 2260840 => 2
  | 2260880 => 2
  | 2260988 => 1
  | 2260992 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Open Scope Z_scope.

Definition BN_INIT : Z := 0x2227dc.
Definition BN_INIT_STACK : Z := 16 + RT_STACK.
Definition BN_CTX_GET : Z := 0x227c64.
Definition BN_CTX_GET_STACK : Z := 112 + CRYPTO_MALLOC_STACK.

Lemma nondecr_last_incr : forall (l : list nat) x y, nondecr (l ++ [x]) -> (x <= y)%nat -> nondecr (l ++ [y]).
Proof.
  induction l as [|z l IH]; intros x y H Hxy; cbn [app nondecr] in *; [tauto|].
  destruct H as [Hz H]. split; [|eapply IH; eassumption]. destruct l as [|w l]; cbn [app] in *; lia.
Qed.

Lemma dv_ble_range : forall bs : list byte, 0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with (2 ^ 8) in Hb.
  assert (Hs : 0 <= Z.shiftl (bytes_le_to_Z bs) 8) by (apply Z.shiftl_nonneg; lia).
  split. { apply Z.lor_nonneg. lia. }
  pose proof (Z.add_lor_land (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as E.
  pose proof (Z.land_nonneg (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as L.
  rewrite Z.shiftl_mul_pow2 in * by lia.
  assert (LD : Z.land (bv_unsigned b) (bytes_le_to_Z bs * 2 ^ 8) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases n 8) as [Hlt|Hge].
    - rewrite (Z.mul_pow2_bits_low _ 8 n) by lia. apply andb_false_r.
    - replace (Z.testbit (bv_unsigned b) n) with false; [reflexivity|]. symmetry. apply Z.bits_above_log2; [lia|].
      assert (Z.log2 (bv_unsigned b) < 8); [|lia]. destruct (Z.eq_dec (bv_unsigned b) 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  rewrite LD in E. replace (8 * Z.of_nat (S (length bs))) with (8 + 8 * Z.of_nat (length bs)) by lia. rewrite Z.pow_add_r by lia. nia.
Qed.
Lemma dv_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (dv_ble_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply StrFun.Z_to_le_bytes_to_Z.
Qed.
Lemma rw_cells_CB8_hd : forall segs m A bs rest, rw_cells segs m A (CB 8 bs :: rest) -> rw_cells segs m A (C8 (le_bytes_to_word bs) :: rest).
Proof.
  intros segs m A bs rest H. pose proof H as [[[L W] _] _].
  eapply bk_rw_cells_recast; [exact H | cbn; split; [exact I | exact W] | cbn [cells_bytes cbytes]; rewrite dv_le8_of_bytes by exact L; reflexivity | reflexivity].
Qed.

Lemma lxor_ones64 : forall a, 0 <= a < 2^64 -> Z.lxor a 18446744073709551615 = 18446744073709551615 - a.
Proof.
  intros a Ha. change 18446744073709551615 with (Z.ones 64).
  destruct (Z.eq_dec a 0) as [->|NZ]. { rewrite Z.lxor_0_l. reflexivity. }
  rewrite <- (Z.ldiff_ones_l_low a 64); [| lia | apply Z.log2_lt_pow2; lia].
  symmetry. apply Z.sub_nocarry_ldiff.
  apply Z.bits_inj'. intros n Hn. rewrite Z.ldiff_spec, Z.bits_0.
  destruct (Z.lt_ge_cases n 64) as [Hlt|Hge].
  - rewrite Z.ones_spec_low by lia. destruct (Z.testbit a n); reflexivity.
  - rewrite (Z.bits_above_log2 a n); [reflexivity| lia|]. apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia| lia].
Qed.

Definition get_tail_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo CTX A D : Z) (b : bignum bptr) (c0 c1 c2 c3 c4 c5 c6 c7 c9 c10 c11 c12 : word) (used : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bgbsegs)
    /\ munch [(bv_unsigned sp - 128, bv_unsigned sp); (A, A + 24); (CTX, CTX + 72)] m m' /\ wmono bgbsegs m m' /\ mem_inv bgbsegs m'
    /\ stk bgbsegs m' lo (bv_unsigned sp)
    /\ rw_cells bgbsegs m' A (bn_cells D (bn_zero_pure b))
    /\ rw_cells bgbsegs m' CTX [C8 c0; C8 c1; C8 c2; C4 c3; C4 c4; C8 c5; C4 c6; C4 c7; C4 (Z_to_bv 64 (used + 1)); C4 c9; C4 c10; C4 c11; C8 c12].

Lemma get_tailA : forall (x1 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x20 x21 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w0 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo CTX A D : Z) (b : bignum bptr)
    (c0 c1 c2 c3 c4 c5 c6 c7 c9 c10 c11 c12 : word) (used : Z),
  rw_cells bgbsegs m A (bn_cells D b) -> 0 <= bn_flags b <= 1 ->
  rw_cells bgbsegs m CTX [C8 c0; C8 c1; C8 c2; C4 c3; C4 c4; C8 c5; C4 c6; C4 c7; C4 (Z_to_bv 64 used); C4 c9; C4 c10; C4 c11; C8 c12] ->
  0 <= used < 2^31 - 1 ->
  rw_cells bgbsegs m (bv_unsigned sp + -112) [C8 w0; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk bgbsegs m lo (bv_unsigned sp + -112) -> lo <= bv_unsigned sp - 128 -> mem_inv bgbsegs m ->
  (A + 24 <= bv_unsigned sp - 128 \/ bv_unsigned sp <= A) -> (CTX + 72 <= bv_unsigned sp - 128 \/ bv_unsigned sp <= CTX) ->
  (A + 24 <= CTX \/ CTX + 72 <= A) -> 0 <= lo ->
  shb_cells bgbsegs 6147864 6945336 m -> acc bgbsegs m A 24 -> A mod 8 = 0 -> acc bgbsegs m CTX 72 -> CTX mod 8 = 0 ->
  SHHI <= lo -> (A + 24 <= SHLO \/ SHHI <= A) -> (CTX + 72 <= SHLO \/ SHHI <= CTX) -> 0 < A ->
  evt bgbsegs (get_tail_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo CTX A D b c0 c1 c2 c3 c4 c5 c6 c7 c9 c10 c11 c12 used)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 sp (Z_to_bv 64 CTX) a0 a1 a2 a3 a4 a5 a6 a7
             x18 (Z_to_bv 64 A) x20 x21 (Z_to_bv 64 SHB) x23 x24 x25 x26 x27 t3 t4 t5 t6)
        F (Z_to_bv 64 0x227ff4) fc None m (seg_rom bgbsegs)).
Proof.
  intros until used. intros BN FLR CX USED FR ST LO MI SEPA SEPC SEPAC LO0 SHBC ACCA ALA ACCC ALC SLO OFA OFC PA.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (bn_cells_bound47 m A _ BN MI ltac:(cbn; lia)) as B47. cbn [bn_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in B47.
  pose proof (bn_cells_bound47 m CTX _ CX MI ltac:(cbn; lia)) as C47. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in C47.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (A, A + 24); (CTX, CTX + 72)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 128, bv_unsigned sp); (A, A + 24); (CTX, CTX + 72)]) by (cbn [offshW]; unfold SHLO, SHHI in *; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; unfold SHHI in *; lia).
  unfold SHLO, SHHI in *.
  step. step.
  eapply evt_cut.
  { eapply (BN_zero_ex_specA) with (lo := lo) (A := A) (D := D) (b := b); rewrite ?ESP;
      [exact BN| exact ST| lia| exact MI| lia| exact SHBC| exact ACCA| exact ALA| unfold SHHI; lia| unfold SHLO, SHHI; lia| reflexivity| exact PA]. }
  rewrite ?ESP. post_call bgbsegs m.
  rewrite ESP in PC. unfold bn_cells in POST.
  replace (bn_flags (bn_zero_pure b)) with (bn_flags b) in POST by reflexivity.
  ub.
  do 3 step. ub; shl. ub; chk0.
  ub; step. unfold wz at 1. rewrite (zx32_small (bn_flags b)) by lia.
  ub; step. ub; step.
  replace (Z.land (bv_unsigned (Z_to_bv 64 (bn_flags b))) 18446744073709551611) with (bn_flags b)
    by (assert (bn_flags b = 0 \/ bn_flags b = 1) as [E|E] by lia; rewrite E; reflexivity).
  ub; step. do 2 (ub; step). ub; shl. ub; chk0.
  ub; step. rewrite (sx32_small used) by lia.
  ub; step. ub; step. ub; step.
  ub; step.
  do 13 (ub; step). release_frame FR PC (bv_unsigned sp). ub; step. ub; step.
  finish.
Qed.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma cps_done : forall Σ ms (R : machine_state -> Prop), R ms -> cps bgbsegs (ASTA RT Σ PMc (eq ms)) (ASTA RT Σ PMc R).
Proof.
  intros Σ ms R HR. eapply cps_conseq; [apply cps_refl | intros c Hc; exact Hc |].
  intros c Hc. eapply ASTA_conseq; [exact Hc|]. intros ms0 <-. exact HR.
Qed.

Lemma bn_init_cpsA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo A : Z) (bd : block),
  AHEAP Σ OW LB m ->
  stk bgbsegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - BN_INIT_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv bgbsegs m -> tp = wz TP_A ->
  In bd (OW ++ LB) -> blk_addr bd <= A -> A + 24 <= blk_addr bd + blk_size bd ->
  a0 = wz A ->
  cps bgbsegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz BN_INIT) fc None m (seg_rom bgbsegs))))
            (ASTA RT Σ PMc (icall_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz A) Σ OW LB lo A 24 m
                              (fun m' => rw_cells bgbsegs m' A (bn_cells 0 (bn_nil 0))))).
Proof.
  intros until bd. intros HEAP ST CEIL LO SPT SP16 MI -> IND D1 D2 ->.
  unfold BN_INIT_STACK, RT_STACK, BN_INIT, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_range_gen _ _ _ _ bd HEAP IND) as (BD0 & _ & _ & BDC & _).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  apply cps_from_evt'.
  carve_frame 16%nat ST. do 6 (ub; step). ub; step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply (seg_heap Σ OW LB m m1 _ lo (bv_unsigned sp) HEAP MU WM); [| exact CEIL | unfold USTACK_TOP; lia].
    constructor; [left; cbn; lia | constructor]. }
  assert (AG1 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m1).
  { eapply (stack_munch_agree Σ OW LB m m1 _ (OW ++ LB) (bv_unsigned sp) HEAP MU); [| auto].
    constructor; [cbn; unfold BnHeapA.ACEIL in *; lia | constructor]. }
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
  apply evt_done.
  eapply cps_step_same.
  - eapply (asan_memset_cpsA) with (d := A) (n := 24) (c := Z_to_bv 8 0) (bd := bd) (lo := lo) (OW := OW) (LB := LB); try reflexivity.
    + exact HEAP1.
    + rewrite ESP. exact ST.
    + exact CEIL.
    + rewrite ESP. unfold RT_STACK. lia.
    + rewrite ESP. unfold USTACK_TOP. lia.
    + rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia.
    + exact MI.
    + exact IND.
    + exact D1.
    + exact D2.
    + lia.
  - intros ms2 PO. unfold icall_post in PO. rewrite ?ESP in PO.
    destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F2 & fc2 & m2 & -> & MI2 & ST2 & HEAP2 & WM2 & AG2 & BZ & WR2).
    rewrite (ret_pc_even 2238456) by lia. unfold MallocRep.wz.
    apply (rw_cells_agree _ _ _ _ _ AG2) in FR; [| intros x Hx; cbn in Hx; split; [left; unfold USTACK_TOP; lia | unfold BnHeapA.ACEIL in *; lia]].
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m2) as MU2. pose proof (wmono_refl bgbsegs m2) as WMr.
    apply cps_from_evt'.
    do 2 (ub; step). release_frame FR ST2 (bv_unsigned sp). ub; step. ub; step.
    apply evt_done. apply cps_done.
    unfold icall_post, MallocRep.wz. do 16 eexists. exists m2. split; [reflexivity|].
    split; [exact MI2|]. split; [exact ST2|]. split; [exact HEAP2|].
    split; [eapply wmono_trans; [exact WM | exact WM2]|].
    split. { eapply agree_on_trans.
             - eapply agree_on_mono; [exact AG1|]. intros x [Hx _]. exact Hx.
             - eapply agree_on_mono; [exact AG2|]. intros x [Hx Hd]. split; [|exact Hd].
               destruct Hx as [Hx|[Hx|Hx]]; [left; lia | right; left; exact Hx | right; right; exact Hx]. }
    eapply bk_rw_cells_recast with (cs := [CB 24 (repeat (Z_to_bv 8 0) 24)]).
    + split; [split; [cbn; tauto | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BZ] | exact WR2].
    + cbn; tauto.
    + reflexivity.
    + reflexivity.
Qed.

Definition init_loop_postA (sp gp s0 s1 s2 s3 s4 s6 s7 s8 : word) (Σ : rts RT) (OW LB : list block) (lo P : Z) (n : nat) (m : mem) : machine_state -> Prop :=
  fun ms' => exists ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra' sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (P + 24 * Z.of_nat n)) s6 s7 s8
                  (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 18446744073709551592) t3 t4 t5 t6)
             F' (Z_to_bv 64 0x227de4) fc' None m' (seg_rom bgbsegs)
    /\ mem_inv bgbsegs m' /\ stk bgbsegs m' lo (bv_unsigned sp) /\ AHEAP Σ OW LB m' /\ wmono bgbsegs m m'
    /\ agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ ~ (P <= a < P + 24 * Z.of_nat n)) m m'
    /\ rw_cells bgbsegs m' P [CB (24 * n) (repeat (Z_to_bv 8 0) (24 * n))].

Lemma get_init_loopA : forall (n : nat)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo P : Z) (bd : block),
  AHEAP Σ OW LB m ->
  stk bgbsegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - BN_INIT_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv bgbsegs m -> tp = wz TP_A ->
  In bd (OW ++ LB) -> blk_addr bd <= P -> P + 24 * Z.of_nat (S n) <= blk_addr bd + blk_size bd -> (n <= 15)%nat ->
  cps bgbsegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 P) s6 s7 s8
                                        (Z_to_bv 64 0) (Z_to_bv 64 (Z.of_nat (S n))) (Z_to_bv 64 18446744073709551592) t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x227dbc) fc None m (seg_rom bgbsegs))))
            (ASTA RT Σ PMc (init_loop_postA sp gp s0 s1 s2 s3 s4 s6 s7 s8 Σ OW LB lo P (S n) m)).
Proof.
  induction n as [|n IH]; intros until bd; intros HEAP ST CEIL LO SPT SP16 MI -> IND D1 D2 HN.
  -
    unfold BN_INIT_STACK, RT_STACK, MallocRep.wz in *.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
    pose proof (AH_range_gen _ _ _ _ bd HEAP IND) as (BD0 & _ & _ & BDC & _).
    change (24 * Z.of_nat 1) with 24 in *.
    apply cps_from_evt'. do 2 step. apply evt_done.
    eapply cps_step_same.
    + eapply (bn_init_cpsA) with (A := P) (bd := bd) (lo := lo) (OW := OW) (LB := LB); try reflexivity;
        [exact HEAP | exact ST | exact CEIL | unfold BN_INIT_STACK, RT_STACK; lia | unfold USTACK_TOP; lia | exact SP16 | exact MI | exact IND | exact D1 | lia].
    + intros ms2 PO. unfold icall_post in PO.
      destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F2 & fc2 & m2 & -> & MI2 & ST2 & HEAP2 & WM2 & AG2 & BNZ).
      rewrite (ret_pc_even 2260420) by lia. unfold MallocRep.wz.
      apply cps_from_evt'.
      step. if_true.
      zstep. if_cases CT; zify_cond CT. { exfalso. rewrite ?unsigned_lit in CT by (unfold BnHeapA.ACEIL in *; lia). unfold BnHeapA.ACEIL in *. lia. }
      clear CT.
      zstep. zstep. change (bv_swrap 32 (Z.of_nat 1 + -1)) with 0.
      step. if_cases KB; zify_cond KB; [exfalso; apply KB; reflexivity|]. clear KB.
      apply evt_done. apply cps_done.
      unfold init_loop_postA, MallocRep.wz. change (24 * Z.of_nat 1) with 24. do 18 eexists. exists m2. split; [reflexivity|].
      split; [exact MI2|]. split; [exact ST2|]. split; [exact HEAP2|]. split; [exact WM2|]. split; [exact AG2|].
      eapply bk_rw_cells_recast; [exact BNZ| cbn; split; [reflexivity| exact I]| reflexivity| reflexivity].
  -
    unfold BN_INIT_STACK, RT_STACK, MallocRep.wz in *.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
    pose proof (AH_range_gen _ _ _ _ bd HEAP IND) as (BD0 & _ & _ & BDC & _).
    apply cps_from_evt'. do 2 step. apply evt_done.
    eapply cps_step_same.
    + eapply (bn_init_cpsA) with (A := P) (bd := bd) (lo := lo) (OW := OW) (LB := LB); try reflexivity;
        [exact HEAP | exact ST | exact CEIL | unfold BN_INIT_STACK, RT_STACK; lia | unfold USTACK_TOP; lia | exact SP16 | exact MI | exact IND | exact D1 | lia].
    + intros ms2 PO. unfold icall_post in PO.
      destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F2 & fc2 & m2 & -> & MI2 & ST2 & HEAP2 & WM2 & AG2 & BNZ).
      rewrite (ret_pc_even 2260420) by lia. unfold MallocRep.wz.
      apply cps_from_evt'.
      step. if_true.
      zstep. if_cases CT; zify_cond CT. { exfalso. rewrite ?unsigned_lit in CT by (unfold BnHeapA.ACEIL in *; lia). unfold BnHeapA.ACEIL in *. lia. }
      clear CT.
      zstep. rewrite (bn_swrap32_small (Z.of_nat (S (S n)) + -1)) by lia.
      replace (Z.of_nat (S (S n)) + -1) with (Z.of_nat (S n)) by lia.
      zstep.
      step. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia; [|exfalso; lia]. clear KB.
      apply evt_done.
      eapply cps_step_same.
      * eapply (IH) with (P := P + 24) (bd := bd) (lo := lo) (OW := OW) (LB := LB); try reflexivity;
          [exact HEAP2 | exact ST2 | exact CEIL | unfold BN_INIT_STACK, RT_STACK; lia | unfold USTACK_TOP; lia | exact SP16 | exact MI2 | exact IND | lia | lia | lia].
      * intros ms3 PO. unfold init_loop_postA in PO.
        destruct PO as (ra3 & w0 & w1 & w2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F3 & fc3 & m3 & -> & MI3 & ST3 & HEAP3 & WM3 & AG3 & ZR).
        apply cps_done.
        unfold init_loop_postA, MallocRep.wz. do 18 eexists. exists m3.
        split. { replace (P + 24 + 24 * Z.of_nat (S n)) with (P + 24 * Z.of_nat (S (S n))) by lia. reflexivity. }
        split; [exact MI3|]. split; [exact ST3|]. split; [exact HEAP3|]. split; [eapply wmono_trans; [exact WM2 | exact WM3]|].
        split. { eapply agree_on_trans.
                 - eapply agree_on_mono; [exact AG2|]. intros x [Hx Hd]. split; [exact Hx | lia].
                 - eapply agree_on_mono; [exact AG3|]. intros x [Hx Hd]. split; [exact Hx | lia]. }
        assert (BNZ3 : rw_cells bgbsegs m3 P (bn_cells 0 (bn_nil 0))).
        { eapply (rw_cells_agree _ _ _ _ _ AG3); [exact BNZ|]. intros x Hx. cbn in Hx.
          split; [right; right; exists bd; split; [exact IND | lia] | lia]. }
        assert (JOIN : rw_cells bgbsegs m3 P (bn_cells 0 (bn_nil 0) ++ [CB (24 * S n) (repeat (Z_to_bv 8 0) (24 * S n))])).
        { apply bk_rw_cells_app. split; [exact BNZ3|]. cbn [bn_cells cells_size csize Nat.add]. change (Z.of_nat 24) with 24. exact ZR. }
        eapply bk_rw_cells_recast; [exact JOIN| | |].
        -- cbn [cells_wf cell_wf]. rewrite repeat_length. tauto.
        -- cbn [bn_cells cells_bytes cbytes app]. rewrite !app_nil_r.
           replace (24 * S (S n))%nat with (24 + 24 * S n)%nat by lia. rewrite repeat_app. reflexivity.
        -- cbn [bn_cells cells_size csize app]. lia.
Qed.

Local Notation E_cg_malloc := (E_BN_CTX_get_227bb4 : uk_call BN_CTX_GET 0x227d9c CRYPTO_MALLOC).

End WithRT.
