(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA ZBridge RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Malloc Prog BnBase BnModel BnTree BnInv BnSpecs BnMInv.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require StrFun.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA BnRepX ImplA BnIfaceA UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA W_ctxA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2409732 => 2
  | 2409740 => 1
  | 2409744 => 2
  | 2409992 => 1
  | 2409996 => 2
  | 2410008 => 1
  | 2410040 => 2
  | 2410152 => 2
  | 2410156 => 1
  | 2410160 => 2
  | 2410264 => 2
  | 2410268 => 1
  | 2410272 => 2
  | 2410436 => 2
  | 2410440 => 1
  | 2410444 => 2
  | 2410484 => 2
  | 2410592 => 1
  | 2410596 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Open Scope Z_scope.

Definition BN_INIT : Z := 0x1ef090.
Definition BN_INIT_STACK : Z := 16 + RT_STACK.
Definition BN_CTX_GET : Z := 0x24c4c8.
Definition BN_CTX_GET_STACK : Z := 112 + CRYPTO_MALLOC_STACK.

(* [comment removed for export] *)
Lemma bns_gen_zeros : forall (n : nat) (m : mem) (OW : list block) A i,
  rw_cells bsegs m A [CB (24 * n) (repeat (Z_to_bv 8 0) (24 * n))] -> bns_gen (repR m OW) A (repeat (bn_nil 0) n) i.
Proof.
  induction n as [|n IH]; intros m OW A i HZ; cbn [repeat bns_gen]; [exact I|].
  assert (SPLIT : rw_cells bsegs m A (bn_cells 0 (bn_nil 0) ++ [CB (24 * n) (repeat (Z_to_bv 8 0) (24 * n))])).
  { eapply bk_rw_cells_recast; [exact HZ| | |].
    - cbn [bn_cells app cells_wf cell_wf]. rewrite repeat_length. tauto.
    - cbn [bn_cells cells_bytes cbytes app]. rewrite !app_nil_r.
      replace (24 * S n)%nat with (24 + 24 * n)%nat by lia. rewrite repeat_app. reflexivity.
    - cbn [bn_cells cells_size csize app]. lia. }
  apply bk_rw_cells_app in SPLIT. destruct SPLIT as [B1 B2]. cbn [bn_cells cells_size csize Nat.add] in B2. change (Z.of_nat 24) with 24 in B2.
  split.
  - unfold repR, bn_rep. exists 0. split; [exact B1|]. unfold bn_arr. cbn [bn_nil bn_d bn_buf]. auto.
  - apply IH. exact B2.
Qed.

Lemma nondecr_last_incr : forall (l : list nat) x y, nondecr (l ++ [x]) -> (x <= y)%nat -> nondecr (l ++ [y]).
Proof.
  induction l as [|z l IH]; intros x y H Hxy; cbn [app nondecr] in *; [tauto|].
  destruct H as [Hz H]. split; [|eapply IH; eassumption]. destruct l as [|w l]; cbn [app] in *; lia.
Qed.

Lemma ad_pc_in : forall AD, In (ad_pc AD) (ad_ids AD).
Proof. intros AD. unfold ad_ids. do 5 right. left. reflexivity. Qed.

(* [comment removed for export] *)
Lemma cx_head_vals : forall cxo hs ls m OW AD EA, lib_state_hc cxo hs ls m OW AD EA ->
  cx_head (ls_ctx ls) = None -> cx_vals (ls_ctx ls) = [].
Proof.
  intros cxo hs ls m OW AD EA (_ & _ & _ & (_ & _ & (_ & _ & _ & _ & _ & _ & _ & (H' & Cu' & I' & _ & HPool & _)))) E.
  rewrite E in HPool. exact (proj2 HPool).
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

(* [comment removed for export] *)
Definition get_tail_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo CTX A D : Z) (b : bignum bptr) (c0 c1 c2 c3 c4 c5 c6 c7 c9 c10 c11 c12 : word) (used : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 128, bv_unsigned sp); (A, A + 24); (CTX, CTX + 72)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' A (bn_cells D (bn_zero_pure b))
    /\ rw_cells bsegs m' CTX [C8 c0; C8 c1; C8 c2; C4 c3; C4 c4; C8 c5; C4 c6; C4 c7; C4 (Z_to_bv 64 (used + 1)); C4 c9; C4 c10; C4 c11; C8 c12].

Lemma get_tailA : forall (x1 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x20 x21 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w0 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo CTX A D : Z) (b : bignum bptr)
    (c0 c1 c2 c3 c4 c5 c6 c7 c9 c10 c11 c12 : word) (used : Z),
  rw_cells bsegs m A (bn_cells D b) -> 0 <= bn_flags b <= 1 ->
  rw_cells bsegs m CTX [C8 c0; C8 c1; C8 c2; C4 c3; C4 c4; C8 c5; C4 c6; C4 c7; C4 (Z_to_bv 64 used); C4 c9; C4 c10; C4 c11; C8 c12] ->
  0 <= used < 2^31 - 1 ->
  rw_cells bsegs m (bv_unsigned sp + -112) [C8 w0; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk bsegs m lo (bv_unsigned sp + -112) -> lo <= bv_unsigned sp - 128 -> mem_inv bsegs m ->
  (A + 24 <= bv_unsigned sp - 128 \/ bv_unsigned sp <= A) -> (CTX + 72 <= bv_unsigned sp - 128 \/ bv_unsigned sp <= CTX) ->
  (A + 24 <= CTX \/ CTX + 72 <= A) -> 0 <= lo ->
  shb_cells bsegs 6163672 6961656 m -> acc bsegs m A 24 -> A mod 8 = 0 -> acc bsegs m CTX 72 -> CTX mod 8 = 0 ->
  SHHI <= lo -> (A + 24 <= SHLO \/ SHHI <= A) -> (CTX + 72 <= SHLO \/ SHHI <= CTX) -> 0 < A ->
  evt bsegs (get_tail_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo CTX A D b c0 c1 c2 c3 c4 c5 c6 c7 c9 c10 c11 c12 used)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 sp (Z_to_bv 64 CTX) a0 a1 a2 a3 a4 a5 a6 a7
             x18 (Z_to_bv 64 A) x20 x21 (Z_to_bv 64 SHB) x23 x24 x25 x26 x27 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24c858) fc None m (seg_rom bsegs)).
Proof.
  intros until used. intros BN FLR CX USED FR ST LO MI SEPA SEPC SEPAC LO0 SHBC ACCA ALA ACCC ALC SLO OFA OFC PA.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (bn_cells_bound47 m A _ BN MI ltac:(cbn; lia)) as B47. cbn [bn_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in B47.
  pose proof (bn_cells_bound47 m CTX _ CX MI ltac:(cbn; lia)) as C47. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in C47.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (A, A + 24); (CTX, CTX + 72)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 128, bv_unsigned sp); (A, A + 24); (CTX, CTX + 72)]) by (cbn [offshW]; unfold SHLO, SHHI in *; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; unfold SHHI in *; lia).
  unfold SHLO, SHHI in *.
  step. step.
  eapply evt_cut.
  { eapply (BN_zero_ex_specA) with (lo := lo) (A := A) (D := D) (b := b); rewrite ?ESP;
      [exact BN| exact ST| lia| exact MI| lia| exact SHBC| exact ACCA| exact ALA| unfold SHHI; lia| unfold SHLO, SHHI; lia| reflexivity| exact PA]. }
  rewrite ?ESP. post_call bsegs m.
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

Lemma cx_vals_head : forall cxo hs ls m OW AD EA, lib_state_hc cxo hs ls m OW AD EA ->
  cx_vals (ls_ctx ls) = [] -> cx_head (ls_ctx ls) = None.
Proof.
  intros cxo hs ls m OW AD EA (_ & _ & _ & (_ & _ & (_ & _ & _ & _ & _ & _ & _ & (H' & Cu' & I' & _ & HPool & _)))) E.
  destruct (cx_head (ls_ctx ls)) as [p|]; [|reflexivity]. destruct HPool as (_ & HL & _). rewrite E in HL. discriminate.
Qed.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma cps_done : forall Σ ms (R : machine_state -> Prop), R ms -> cps bsegs (ASTA RT Σ PMc (eq ms)) (ASTA RT Σ PMc R).
Proof.
  intros Σ ms R HR. eapply cps_conseq; [apply cps_refl | intros c Hc; exact Hc |].
  intros c Hc. eapply ASTA_conseq; [exact Hc|]. intros ms0 <-. exact HR.
Qed.

(* [comment removed for export] *)
Lemma bn_init_cpsA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo A : Z) (bd : block),
  AHEAP Σ OW LB m ->
  stk bsegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - BN_INIT_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv bsegs m -> tp = wz TP_A ->
  In bd (OW ++ LB) -> blk_addr bd <= A -> A + 24 <= blk_addr bd + blk_size bd ->
  a0 = wz A ->
  cps bsegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz BN_INIT) fc None m (seg_rom bsegs))))
            (ASTA RT Σ PMc (icall_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz A) Σ OW LB lo A 24 m
                              (fun m' => rw_cells bsegs m' A (bn_cells 0 (bn_nil 0))))).
Proof.
  intros until bd. intros HEAP ST CEIL LO SPT SP16 MI -> IND D1 D2 ->.
  unfold BN_INIT_STACK, RT_STACK, BN_INIT, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_range_gen _ _ _ _ bd HEAP IND) as (BD0 & _ & _ & BDC & _).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
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
    rewrite (ret_pc_even 2027692) by lia. unfold MallocRep.wz.
    apply (rw_cells_agree _ _ _ _ _ AG2) in FR; [| intros x Hx; cbn in Hx; split; [left; unfold USTACK_TOP; lia | unfold BnHeapA.ACEIL in *; lia]].
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m2) as MU2. pose proof (wmono_refl bsegs m2) as WMr.
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


(* [comment removed for export] *)
Definition init_loop_postA (sp gp s0 s1 s2 s3 s4 s6 s7 s8 : word) (Σ : rts RT) (OW LB : list block) (lo P : Z) (n : nat) (m : mem) : machine_state -> Prop :=
  fun ms' => exists ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra' sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (P + 24 * Z.of_nat n)) s6 s7 s8
                  (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 18446744073709551592) t3 t4 t5 t6)
             F' (Z_to_bv 64 0x24c648) fc' None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp) /\ AHEAP Σ OW LB m' /\ wmono bsegs m m'
    /\ agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ ~ (P <= a < P + 24 * Z.of_nat n)) m m'
    /\ rw_cells bsegs m' P [CB (24 * n) (repeat (Z_to_bv 8 0) (24 * n))].

Lemma get_init_loopA : forall (n : nat)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo P : Z) (bd : block),
  AHEAP Σ OW LB m ->
  stk bsegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - BN_INIT_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv bsegs m -> tp = wz TP_A ->
  In bd (OW ++ LB) -> blk_addr bd <= P -> P + 24 * Z.of_nat (S n) <= blk_addr bd + blk_size bd -> (n <= 15)%nat ->
  cps bsegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 P) s6 s7 s8
                                        (Z_to_bv 64 0) (Z_to_bv 64 (Z.of_nat (S n))) (Z_to_bv 64 18446744073709551592) t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x24c620) fc None m (seg_rom bsegs))))
            (ASTA RT Σ PMc (init_loop_postA sp gp s0 s1 s2 s3 s4 s6 s7 s8 Σ OW LB lo P (S n) m)).
Proof.
  induction n as [|n IH]; intros until bd; intros HEAP ST CEIL LO SPT SP16 MI -> IND D1 D2 HN.
  - (* [comment removed for export] *)
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
      rewrite (ret_pc_even 2410024) by lia. unfold MallocRep.wz.
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
  - (* [comment removed for export] *)
    unfold BN_INIT_STACK, RT_STACK, MallocRep.wz in *.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
    pose proof (AH_range_gen _ _ _ _ bd HEAP IND) as (BD0 & _ & _ & BDC & _).
    apply cps_from_evt'. do 2 step. apply evt_done.
    eapply cps_step_same.
    + eapply (bn_init_cpsA) with (A := P) (bd := bd) (lo := lo) (OW := OW) (LB := LB); try reflexivity;
        [exact HEAP | exact ST | exact CEIL | unfold BN_INIT_STACK, RT_STACK; lia | unfold USTACK_TOP; lia | exact SP16 | exact MI | exact IND | exact D1 | lia].
    + intros ms2 PO. unfold icall_post in PO.
      destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F2 & fc2 & m2 & -> & MI2 & ST2 & HEAP2 & WM2 & AG2 & BNZ).
      rewrite (ret_pc_even 2410024) by lia. unfold MallocRep.wz.
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
        assert (BNZ3 : rw_cells bsegs m3 P (bn_cells 0 (bn_nil 0))).
        { eapply (rw_cells_agree _ _ _ _ _ AG3); [exact BNZ|]. intros x Hx. cbn in Hx.
          split; [right; right; exists bd; split; [exact IND | lia] | lia]. }
        assert (JOIN : rw_cells bsegs m3 P (bn_cells 0 (bn_nil 0) ++ [CB (24 * S n) (repeat (Z_to_bv 8 0) (24 * S n))])).
        { apply bk_rw_cells_app. split; [exact BNZ3|]. cbn [bn_cells cells_size csize Nat.add]. change (Z.of_nat 24) with 24. exact ZR. }
        eapply bk_rw_cells_recast; [exact JOIN| | |].
        -- cbn [cells_wf cell_wf]. rewrite repeat_length. tauto.
        -- cbn [bn_cells cells_bytes cbytes app]. rewrite !app_nil_r.
           replace (24 * S (S n))%nat with (24 + 24 * S n)%nat by lia. rewrite repeat_app. reflexivity.
        -- cbn [bn_cells cells_size csize app]. lia.
Qed.


(* [comment removed for export] *)
Lemma stack_rep_munch : forall Σ OW LB m m' ls AD EA IX W,
  AHEAP Σ OW LB m -> ids_ok ls AD EA -> ad_blocks OW AD ->
  stack_rep m OW IX (ls_ctx ls) -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv : Z * Z => ACEIL <= fst iv \/ (ad_ctx AD <= fst iv /\ snd iv <= ad_ctx AD + 72)
                            \/ (exists q A n, In (q, A, n) (OW ++ LB) /\ A <= fst iv /\ snd iv <= A + n /\ Some q <> cx_indexes (ls_ctx ls))) W ->
  stack_rep m' OW IX (ls_ctx ls).
Proof.
  intros Σ OW LB m m' ls AD EA IX W HEAP IDS ADB STK MU WM HW. unfold stack_rep in *.
  destruct (cx_indexes (ls_ctx ls)) as [q|] eqn:EI; [|exact STK].
  destruct STK as (HinI & SZ32 & stale & LEN & ARRI). split; [exact HinI|]. split; [exact SZ32|]. exists stale. split; [exact LEN|].
  pose proof (AH_range _ _ _ _ _ _ _ HEAP HinI) as (IA0 & IA16 & _ & IAC & IAI).
  destruct ADB as (_ & _ & _ & _ & _ & BC).
  assert (NEI : ad_pc AD <> q) by (eapply ids_ad_m; [exact IDS| apply ad_pc_in| apply idx_in_m; exact EI]).
  pose proof (AH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP BC HinI NEI) as CXI.
  assert (LWS : Z.of_nat (length (map (fun k : nat => wz (Z.of_nat k)) (cx_frames (ls_ctx ls)) ++ stale)) = 32) by (rewrite length_app, length_map; lia).
  eapply u32arr_transport; [exact ARRI| exact MU| exact WM|]. rewrite LWS. clear MU ARRI.
  induction HW as [|[x y] W Hiv HW IH]; [exact I|]. cbn [disjoint_from]. split; [|exact IH].
  cbn [fst snd] in Hiv. destruct Hiv as [Hs|[Hc|(q' & A & n & Hq & H1 & H2 & NE)]]; [lia| lia|].
  assert (NEq : q' <> q) by congruence.
  pose proof (AH_disjoint_gen _ _ _ _ (q', A, n) (q, IX, 128) HEAP Hq ltac:(apply in_or_app; left; exact HinI) NEq) as DJ.
  cbn [blk_addr blk_size fst snd] in DJ. lia.
Qed.

Lemma stack_rep_agree : forall (OW : list block) L SP (P : Z -> Prop) m m' IX (c : bn_ctx bptr),
  (forall b, In b OW -> In b L) -> stack_rep m OW IX c -> agree_on P m m' ->
  (forall q, cx_indexes c = Some q -> In (q, IX, 128) OW -> forall x, aclient_addr L SP x -> IX <= x < IX + 128 -> P x) ->
  stack_rep m' OW IX c.
Proof.
  intros OW L SP P m m' IX c HI STK HP HPx. unfold stack_rep in *. destruct (cx_indexes c) as [q|] eqn:EI; [|exact STK].
  destruct STK as (HinI & SZ32 & stale & LEN & ARRI). split; [exact HinI|]. split; [exact SZ32|]. exists stale. split; [exact LEN|].
  eapply u32arr_agree; [exact HP| exact ARRI|]. intros x Hx. rewrite length_app, length_map in Hx. apply (HPx q eq_refl HinI); [|lia].
  right; right. exists (q, IX, 128). split; [apply HI; exact HinI|]. cbn [blk_addr blk_size fst snd]. lia.
Qed.

Lemma stack_rep_ow : forall (OW OW' : list block) m IX (c : bn_ctx bptr),
  (forall b, In b OW -> In b OW') -> stack_rep m OW IX c -> stack_rep m OW' IX c.
Proof.
  intros OW OW' m IX c HI STK. unfold stack_rep in *. destruct (cx_indexes c) as [q|]; [|exact STK].
  destruct STK as (HinI & REST). split; [apply HI; exact HinI| exact REST].
Qed.

Local Notation E_cg_malloc := (E_BN_CTX_get_24a0b4 : uk_call BN_CTX_GET 0x24c600 CRYPTO_MALLOC).

Lemma BN_CTX_get_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
    (lo : Z) (ras : list Z),
  bn_preA Σ ls m OW LB AD EA sp lo BN_CTX_GET_STACK MC ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_CTX_GET (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> a0 = wz (ad_ctx AD) ->
  implA (BN_CTX_get (tree_ops bptr) ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA MC
              (fun r ls' OW' a0' => (exists a, ref_at ls' OW' AD r a /\ a0' = wz a) /\ (forall q A n, In (q, A, n) OW -> In (q, A, n) OW')))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_CTX_GET) fc None m (seg_rom bsegs)).
Proof.
  intros until ras. intros (HEAP & LS & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED) UW CTX -> ->.
  unfold BN_CTX_GET_STACK, CRYPTO_MALLOC_STACK, RT_STACK, BN_CTX_GET, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  pose proof SOK as (_ & _ & _ & _ & _ & POK & (CK1 & CK2 & CK3 & CK4 & CK5 & CK6 & CK7)).
  destruct (lib_state_cx_open [] ls m OW AD EA LS) as (H & Cu & IX & CX & STK & PM & HH & LSC).
  pose proof ADB as (_ & _ & _ & _ & _ & BC). pose proof (AH_range _ _ _ _ _ _ _ HEAP BC) as (CA0 & CA16 & _ & CAC & CAI).
  set (c := ls_ctx ls) in *.
  unfold ctx_cells in CX. rewrite CK7 in CX. change (Z.of_nat 0) with 0 in CX.
  assert (INC : In (ad_pc AD, ad_ctx AD, 72) (OW ++ LB)) by (apply in_or_app; left; exact BC).
  pose proof (AH_acc_in _ _ _ _ (ad_pc AD, ad_ctx AD, 72) (ad_ctx AD) 72 HEAP INC ltac:(cbn; lia) ltac:(cbn; lia)) as ACC.
  assert (AL : ad_ctx AD mod 8 = 0) by (clear - CA16; Z.div_mod_to_equations; lia).
  pose proof (AH_offsh _ _ _ _ (ad_pc AD, ad_ctx AD, 72) HEAP INC) as OC. cbn [blk_addr blk_size fst snd] in OC. unfold SHLO, SHHI in OC.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  unfold BN_CTX_get, bbind, bgetctx, bret, bunr, bmalloc, bsetctx, bget, bset.
  cbn [bind ret unreachable lib_malloc lib_free tree_ops tbind fst snd]. fold c.
  rewrite CK7. cbn [Nat.eqb negb orb].
  assert (PSZ : cx_psize c = 0%nat \/ cx_psize c = 16%nat).
  { rewrite CK3. destruct POK as [EV|[EV _]]; [left; rewrite EV; reflexivity| right; exact EV]. }
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 112, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72)]).
  { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. lia. }
  assert (CA47 : 0 < ad_ctx AD /\ ad_ctx AD + 72 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; lia).
  apply implA_from_evt.
  carve_frame 112%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 112 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 15 step.
  ub. step. ub.
  do 3 step.
  do 3 step. ub; shl. ub; chk0.
  ub; step. unfold MallocRep.wz at 1. rewrite (sx32_small 0) by lia.
  ub; step. if_false.
  do 3 (ub; step). ub; shl. ub; chk0.
  ub; step.
  destruct (cx_too_many c) eqn:ETM.
  { apply evt_done. apply implA_unr. }
  cbn [Z.b2z] in *. unfold MallocRep.wz at 1. rewrite (sx32_small 0) by lia.
  ub; step. if_true.
  do 3 (ub; step). ub; shl. ub; chk0.
  do 3 (ub; step). ub; shl.
  ub; step. unfold MallocRep.wz at 1. rewrite (sx32_small 0) by lia.
  ub; chk0.
  do 3 (ub; step). ub; shl.
  ub; step. unfold MallocRep.wz at 1. rewrite (zx32_small (Z.of_nat (cx_pused c))) by lia.
  ub; chk0.
  ub; step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (cx_psize c))) by lia.
  ub; zstep. rewrite ?Z.add_0_r. rewrite (bn_swrap32_small (Z.of_nat (cx_pused c))) by lia.
  lazymatch type of FR with rw_cells _ _ _ (CB 8 ?jb :: _) => set (jbv := jb) in FR end.
  ub; step. if_cases KP; zify_cond KP; rewrite ?unsigned_lit in KP by lia.
  - (* [comment removed for export] *)
    replace (cx_pused c =? cx_psize c)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
    cbn [tbind fst snd].
    assert (PS16 : cx_psize c = 16%nat) by lia.
    destruct (cx_head c) as [ph|] eqn:Eh.
    2:{ exfalso. pose proof (cx_head_vals _ _ _ _ _ _ _ LSC Eh) as EV. fold c in EV. rewrite EV in CK3. cbn in CK3. lia. }
    pose proof (AH_range _ _ _ _ _ _ _ HEAP HH) as (HA0 & HA16 & _ & HAC & HAI).
    assert (NEH : ad_pc AD <> ph) by (eapply ids_ad_m; [exact IDS| apply ad_pc_in| apply head_in_m; exact Eh]).
    pose proof (AH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP BC HH NEH) as CXH.
    assert (INH : In (ph, H, 400) (OW ++ LB)) by (apply in_or_app; left; exact HH).
    pose proof (AH_offsh _ _ _ _ (ph, H, 400) HEAP INH) as OH. cbn [blk_addr blk_size fst snd] in OH. unfold SHLO, SHHI in OH.
    set (i := cx_pused c) in *.
    assert (IR : (i < 16)%nat) by lia.
    assert (IU : i = cx_used c) by exact CK1.
    assert (HA : ref_at ls OW AD (RPool i) (H + 24 * Z.of_nat i)).
    { cbn [ref_at]. exists ph, H. fold c. split; [exact Eh|]. split; [exact HH|]. split; [lia| reflexivity]. }
    destruct (lib_state_open [] ls m OW AD EA (RPool i) _ LSC ND HA ltac:(intros [])) as ((D & BN & ARR) & (OK1 & OK2 & OK3 & OK4) & LSH).
    set (b := getbn (RPool i) ls) in *.
    assert (FLR : 0 <= bn_flags b <= 1) by (destruct OK4 as [E|E]; rewrite E; lia).
    pose proof (AH_acc_in _ _ _ _ (ph, H, 400) (H + 24 * Z.of_nat i) 24 HEAP INH ltac:(cbn; lia) ltac:(cbn; lia)) as ACCB.
    assert (ALB : (H + 24 * Z.of_nat i) mod 8 = 0) by (clear - HA16; Z.div_mod_to_equations; lia).
    assert (H47 : 0 < H /\ H + 400 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; lia).
    lazymatch goal with |- evt _ ?Q _ => remember Q as QQ eqn:EQQ end.
    lazymatch goal with |- evt _ ?Q (MS _ _ _ _ _ ?mx _) =>
      assert (CONT : forall (mX : mem) (x11 x13 x14 : word),
        rw_cells bsegs mX (ad_ctx AD)
          [C8 (wz H); C8 (wz H); C8 (wz H); C4 (wz (Z.of_nat i)); C4 (wz (Z.of_nat (cx_psize c))); C8 (wz IX);
           C4 (wz (Z.of_nat (length (cx_frames c)))); C4 (wz (Z.of_nat (cx_ssize c))); C4 (wz (Z.of_nat (cx_used c)));
           C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0)] ->
        rw_cells bsegs mX (bv_unsigned sp + -112) [CB 8 jbv; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        stk bsegs mX lo (bv_unsigned sp + -112) ->
        munch [(bv_unsigned sp + -112, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72)]%Z m mX -> wmono bsegs m mX -> mem_inv bsegs mX ->
        shb_cells bsegs 6163672 6961656 mX ->
        evt bsegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 (ad_ctx AD))
                             (Z_to_bv 64 (ad_ctx AD + 8)) x11 (Z_to_bv 64 (Z.of_nat i)) x13 x14 a5 a6 a7
                             (Z_to_bv 64 (ad_ctx AD + 24)) s3 (Z_to_bv 64 (ad_ctx AD + 28)) (Z_to_bv 64 (ad_ctx AD + 56)) (Z_to_bv 64 SHB)
                             (Z_to_bv 64 ((ad_ctx AD + 24) ≫ 3 + SHB)) (Z_to_bv 64 ((ad_ctx AD + 28) ≫ 3 + SHB)) (Z_to_bv 64 ((ad_ctx AD + 56) ≫ 3 + SHB))
                             (Z_to_bv 64 0) s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x24c7b0) fc None mX (seg_rom bsegs))) end.
    { intros mX x11 x13 x14 CXX FRX STX MUX WMX MIX (SHX1 & SHX2).
      clear MU WM MI ST FR CX SHB1 SHB2.
      unfold MallocRep.wz in CXX.
      do 2 step. ub; shl. ub; chk0.
      ub; step.
      ub.
      ub; shl. ub; chk0.
      do 5 (ub; zstep).
      replace (Z.land (Z.of_nat i) 15) with (Z.of_nat i)
        by (change 15 with (Z.ones 4); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
      rewrite !Z.shiftl_mul_pow2 by lia. change 18446744073709551615 with (Z.ones 64). rewrite !Z.land_ones by lia.
      rewrite (Z.mod_small (Z.of_nat i * 2 ^ 3) (2 ^ 64)) by lia.
      setreg 10%Z (Z_to_bv 64 (24 * Z.of_nat i)) ltac:(f_equal; lia).
      ub; zstep.
      ub; step.
      zstep. if_cases CT; zify_cond CT.
      { exfalso. rewrite lxor_ones64 in CT by lia. clear - CT H47 IR. lia. }
      clear CT.
      ub; zstep.
      ub; step.
      unfold bn_cells in BN.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?my _) => rename my into m2 end.
      apply rw_cells_CB8_hd in FRX.
      lazymatch type of MUX with munch ?W0 _ _ =>
        apply (rw_cells_transport bsegs W0 m m2 (H + 24 * Z.of_nat i)) in BN; [| exact MUX| exact WMX| cbn [disjoint_from cells_size csize Nat.add]; unfold BnHeapA.ACEIL in *; lia] end.
      assert (ACCB2 : acc bsegs m2 (H + 24 * Z.of_nat i) 24) by (eapply (acc_munch bsegs _ m m2 _ _ ACCB MUX OFF); unfold BnHeapA.ACEIL in *; lia).
      assert (ACCC2 : acc bsegs m2 (ad_ctx AD) 72) by (eapply (acc_munch bsegs _ m m2 _ _ ACC MUX OFF); unfold BnHeapA.ACEIL in *; lia).
      eapply evt_cut.
      { eapply (get_tailA) with (lo := lo) (CTX := ad_ctx AD) (A := H + 24 * Z.of_nat i) (D := D) (b := b) (used := Z.of_nat (cx_used c));
          [exact BN | exact FLR | exact CXX | lia | exact FRX | exact STX | unfold BnHeapA.ACEIL in *; lia | exact MIX
          | unfold BnHeapA.ACEIL in *; lia | unfold BnHeapA.ACEIL in *; lia | lia | unfold BnHeapA.ACEIL in *; lia
          | exact (conj SHX1 SHX2) | exact ACCB2 | exact ALB | exact ACCC2 | exact AL
          | unfold SHHI, BnHeapA.ACEIL in *; lia | unfold SHLO, SHHI; lia | unfold SHLO, SHHI; lia | lia ]. }
      intros ms' PO. unfold get_tail_postA in PO.
      destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & mF & -> & MUt & WMt & MIt & STt & BNt & CXt).
      subst QQ. apply evt_done. apply implA_ret.
      set (bz := bn_zero_pure b).
      set (cur := if (i =? 0)%nat then Some ph else cx_current c).
      set (c2 := mkCtx (Some ph) cur (list_set (cx_vals c) i bz) (S i) (cx_psize c) (cx_indexes c) (cx_frames c) (cx_ssize c)
                       (S (cx_used c)) 0 false).
      lazymatch goal with |- context [(RPool i, ?lsM)] =>
        change lsM with (set_ctx c2 (setbn (RPool i) bz ls)) end.
      set (WF := [(bv_unsigned sp - 128, bv_unsigned sp); (H + 24 * Z.of_nat i, H + 24 * Z.of_nat i + 24); (ad_ctx AD, ad_ctx AD + 72)]%Z).
      assert (MUF : munch WF m mF).
      { eapply munch_trans; [eapply munch_weaken; [|exact MUX]| exact MUt].
        intros x Hx. subst WF. cbn [outside] in *. clear - Hx. intuition lia. }
      assert (WMF : wmono bsegs m mF) by (eapply wmono_trans; eassumption).
      assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) WF).
      { subst WF. constructor; [left; cbn; lia|]. constructor; [right; exists (ph, H, 400); cbn; split; [exact HH| lia]|].
        constructor; [right; exists (ad_pc AD, ad_ctx AD, 72); cbn; auto with zarith| constructor]. }
      pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSC HA) as HV.
      assert (VLEN : length (cx_vals c) = 16%nat) by lia.
      assert (ECUR : cur = Some ph /\ (Cu = H \/ i = 0%nat)).
      { subst cur. destruct (Nat.eqb_spec i 0) as [E0|E0]; [split; [reflexivity| right; exact E0]|].
        pose proof (CK6 E0) as EC. split; [rewrite EC; reflexivity|]. left.
        unfold pool_mem in PM. rewrite Eh in PM. destruct PM as [_ [[E1 _]|[_ E2]]]; [congruence| exact E2]. }
      destruct (bn_arr_facts Σ OW LB m HEAP ls AD EA IDS ADB (RPool i) D HV ARR) as (U & LENW & D0 & DC & DI & DSEP).
      specialize (DSEP (RPool i) _ HA). fold b in U, LENW, DC, DI, DSEP.
      assert (DCX : ad_ctx AD + 72 <= D \/ D + 8 * Z.of_nat (bn_dmax b) <= ad_ctx AD).
      { unfold bn_arr in ARR. destruct (bn_d b) as [pd|] eqn:Ed.
        - destruct ARR as [Hin _]. assert (NE : ad_pc AD <> pd) by (eapply ids_ad_m; [exact IDS| apply ad_pc_in| eapply bn_in_m; [exact HV| exact Ed]]).
          exact (AH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP BC Hin NE).
        - destruct ARR as [-> Eb]. unfold bn_dmax. rewrite Eb. cbn. lia. }
      assert (LSF : lib_state (set_ctx c2 (setbn (RPool i) bz ls)) mF OW AD EA).
      { unfold lib_state.
        assert (IDS1 : ids_ok (setbn (RPool i) bz ls) AD EA) by (apply ids_ok_setbn_same; [exact IDS| exact HV| reflexivity]).
        assert (LS1 : lib_state_hc true [] (setbn (RPool i) bz ls) mF OW AD EA).
        { eapply (lib_state_close [] ls mF OW AD EA (RPool i) (H + 24 * Z.of_nat i) bz); [| exact ND| exact HA| | | exact IDS1].
          - eapply (lib_state_frame Σ LB); [exact HEAP| exact LSH| exact MUF| exact WMF|]. subst WF.
            constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|].
            constructor; [eapply (w_struct OW LB ls AD EA true [RPool i] _ (RPool i) (H + 24 * Z.of_nat i)); [left; reflexivity| exact HA| cbn; lia| cbn; lia]|].
            constructor; [apply w_cx; [reflexivity| intros x Hx; left; cbn in Hx; lia]| constructor].
          - exists D. split; [exact BNt|]. change (bn_arr mF OW D b).
            eapply bn_arr_of_u64arr; [exact ARR|]. eapply u64arr_transport; [exact U| exact MUF| exact WMF|].
            subst WF. cbn [disjoint_from]. rewrite LENW. clear - DSEP DCX DC CEIL LO SPR. unfold BnHeapA.ACEIL in *. lia.
          - subst bz. unfold bn_okm, bn_zero_pure, bn_dmax in *. cbn [bn_buf bn_top bn_flags]. split; [exact OK1|]. split; [lia|]. split; [exact OK3| exact OK4]. }
        eapply (lib_state_cx_close [] (setbn (RPool i) bz ls) mF OW AD EA c2 H H IX); [exact LS1| exact ND| | | | | | | |].
        - cbn. symmetry. exact Eh.
        - reflexivity.
        - cbn [c2 cx_head]. exact HH.
        - unfold ctx_cells, c2. cbn [cx_pused cx_psize cx_frames cx_ssize cx_used cx_err_stack cx_too_many Z.b2z]. unfold MallocRep.wz.
          rewrite !Nat2Z.inj_succ. unfold Z.succ. exact CXt.
        - change (stack_rep mF OW IX c). unfold stack_rep in *. destruct (cx_indexes c) as [q|] eqn:EI; [|exact STK].
          destruct STK as (HinI & SZ32 & stale & LEN & ARRI). split; [exact HinI|]. split; [exact SZ32|]. exists stale. split; [exact LEN|].
          pose proof (AH_range _ _ _ _ _ _ _ HEAP HinI) as (IA0 & IA16 & _ & IAC & IAI).
          assert (NEI : ad_pc AD <> q) by (eapply ids_ad_m; [exact IDS| apply ad_pc_in| apply idx_in_m; exact EI]).
          pose proof (AH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP BC HinI NEI) as CXI.
          assert (NEHI : ph <> q) by (eapply (ids_head_idx_neq ls ph q); eauto using ids_m_nodup).
          pose proof (AH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP HH HinI NEHI) as HXI.
          eapply u32arr_transport; [exact ARRI| exact MUF| exact WMF|]. subst WF. cbn [disjoint_from].
          rewrite length_app, length_map. clear - LEN CXI HXI IAC CEIL LO SPR IR. unfold BnHeapA.ACEIL in *. lia.
        - unfold pool_mem in *. cbn [c2 cx_head cx_current]. rewrite Eh in PM. destruct PM as [PN _]. split.
          + eapply rw_cells_transport; [exact PN| exact MUF| exact WMF|]. subst WF. cbn [disjoint_from cells_size csize Nat.add].
            clear - CXH HAC CEIL LO SPR IR. unfold BnHeapA.ACEIL in *. lia.
          + right. split; [exact (proj1 ECUR)| reflexivity].
        - unfold ctx_okm, c2. cbn [cx_pused cx_used cx_psize cx_vals cx_frames cx_ssize cx_current cx_head cx_err_stack].
          split; [lia|]. split; [lia|]. split; [rewrite list_set_length; exact CK3|].
          split; [eapply nondecr_last_incr; [exact CK4| lia]|]. split; [exact CK5|]. split; [intros _; exact (proj1 ECUR)| reflexivity].
        - apply ids_ok_set_ctx_same; [exact IDS1| cbn; symmetry; exact Eh| reflexivity| reflexivity]. }
      unfold bn_postA. do 17 eexists. exists mF, OW. split; [reflexivity|]. cbn [fst snd].
      split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MUF WMF HWL CEIL ltac:(unfold USTACK_TOP; lia))|]. split; [exact LSF|].
      split; [exact STt|]. split; [exact MIt|].
      split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP MUF HWL CEIL ltac:(lia))|].
      split; [unfold MC; lia|].
      split. { unfold cnt_eq, cnt_bal. rewrite (blocks_of_set_ctx c2 (setbn (RPool i) bz ls)).
               - pose proof (cnt_bal_setbn (RPool i) bz ls OW OW HV) as CB. unfold cnt_bal in CB. fold b in CB.
                 assert (EBL : bn_blocks bz = bn_blocks b) by reflexivity. rewrite EBL in CB. lia.
               - reflexivity.
               - cbn. symmetry. exact Eh.
               - reflexivity. }
      split. { intros r' a' HA'. destruct r' as [| | | | |j]; cbn [ref_at] in HA' |- *; try exact HA'.
               destruct HA' as (p0 & H0 & E0 & I0 & R0). exists p0, H0. split; [|split; [exact I0| exact R0]].
               cbn. fold c in E0. rewrite Eh in E0. exact E0. }
      split; [|intros q0 A0 n0 Hq0; exact Hq0].
      exists (H + 24 * Z.of_nat i). split; [|reflexivity].
      cbn [ref_at]. exists ph, H. split; [reflexivity|]. split; [exact HH|]. split; [exact IR| reflexivity]. }
    ub; step.
    ub; step. if_cases KU; zify_cond KU; rewrite ?unsigned_lit in KU by lia.
    + (* [comment removed for export] *)
      do 2 (ub; step). ub; shl. ub; chk0. do 2 (ub; step). ub; shl. ub; chk0.
      ub; step. ub; step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        eapply evt_eq; [| eapply (CONT mx); [exact CX| exact FR| exact ST| exact MU| exact WM| exact MI| exact (conj SHB1 SHB2)] ] end.
      replace (Z.of_nat i) with 0 by lia. reflexivity.
    + (* [comment removed for export] *)
      assert (ECu : Cu = H).
      { assert (E0 : i <> 0%nat) by lia. pose proof (CK6 E0) as EC.
        unfold pool_mem in PM. rewrite Eh in PM. destruct PM as [_ [[E1 _]|[_ E2]]]; [congruence| exact E2]. }
      subst Cu.
      ub; zstep.
      rewrite ?(unsigned_lit (Z.of_nat i)) by lia.
      replace (Z.land (Z.of_nat i) 15) with (Z.of_nat i)
        by (change 15 with (Z.ones 4); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
      ub; step. if_cases KA; zify_cond KA; rewrite ?unsigned_lit in KA by lia; [|exfalso; lia]. clear KA.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        eapply evt_eq; [| eapply (CONT mx); [exact CX| exact FR| exact ST| exact MU| exact WM| exact MI| exact (conj SHB1 SHB2)] ] end.
      reflexivity.
  - (* [comment removed for export] *)
    replace (cx_pused c =? cx_psize c)%nat with true by (symmetry; apply Nat.eqb_eq; lia).
    destruct (cx_psize c =? 0)%nat eqn:EPZ; cbn [negb tbind fst snd].
    2:{ apply evt_done. apply implA_unr. }
    apply Nat.eqb_eq in EPZ.
    assert (EV0 : cx_vals c = []) by (apply length_zero_iff_nil; lia).
    pose proof (cx_vals_head _ _ _ _ _ _ _ LSC EV0) as Eh. fold c in Eh.
    rewrite Eh in HH. subst H.
    unfold pool_mem in PM. rewrite Eh in PM. destruct PM as [-> ECUR0].
    assert (EU0 : cx_used c = 0%nat) by lia.
    assert (EP0 : cx_pused c = 0%nat) by lia.
    do 4 (ub; step). ub; step.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -112, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72)]).
    { constructor; [left; cbn; lia|]. constructor; [right; exists (ad_pc AD, ad_ctx AD, 72); cbn; auto with zarith| constructor]. }
    assert (HEAP1 : AHEAP Σ OW LB m1) by (exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))).
    assert (AXP1 : ax_pres LB (bv_unsigned sp) LIBW_A m m1) by (exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP MU HWL CEIL ltac:(lia))).
    assert (LSC1 : lib_state_hc true [] ls m1 OW AD EA).
    { eapply (lib_state_frame Σ LB); [exact HEAP| exact LSC| exact MU| exact WM|].
      constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|].
      constructor; [apply w_cx; [reflexivity| intros x Hx; left; cbn in Hx; lia]| constructor]. }
    assert (STK1 : stack_rep m1 OW IX c).
    { eapply (stack_rep_munch Σ OW LB m m1 ls AD EA IX); [exact HEAP| exact IDS| exact ADB| exact STK| exact MU| exact WM|].
      constructor; [left; cbn; unfold BnHeapA.ACEIL in *; lia|]. constructor; [right; left; cbn; lia| constructor]. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
    assert (UW1 : uw_chain USTACK_TOP m1 (bv_unsigned sp + -112) (bv_unsigned sp) (bv_unsigned ra :: ras)).
    { apply (uw_push_frame m1 _ (bv_unsigned sp) 112 [CB 8 jbv; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] (bv_unsigned ra) (bv_unsigned s0) ras);
        [reflexivity | lia | clear - SP16; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | apply bv_unsigned_in_range | |].
      - rewrite !Z_to_bv_bv_unsigned. exact FR.
      - eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia |]. constructor; [|constructor].
        cbn. unfold BnHeapA.ACEIL in *. lia. }
    apply evt_done. unfold POOL_ITEM_BYTES.
    eapply (CRYPTO_malloc_walkA) with (n := 400) (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW) (LB := LB); try reflexivity.
    + exact HEAP1.
    + rewrite ESP. exact ST.
    + exact CEIL.
    + rewrite ESP. unfold CRYPTO_MALLOC_STACK, RT_STACK. lia.
    + rewrite ESP. unfold USTACK_TOP. lia.
    + rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia.
    + exact MI.
    + exact (proj1 LSC1).
    + lia.
    + pose proof (cnt_ok_live ls OW LB OW 0 SOK CNT ltac:(lia) ltac:(lia)) as HL. rewrite length_map in HL. exact HL.
    + exact CRED.
    + rewrite ESP. exact UW1.
    + rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_cg_malloc CTX).
    + intros pn Σ1 ms1 FRESH PO. unfold calloc_postA in PO. rewrite ?ESP in PO.
      destruct PO as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & F1 & fc1 & m3 & An & -> & MI3 & ST3 & AG3 & CR3 & BR & HEAP3 & ACCN & (junkA & BLK)).
      rewrite (ret_pc_even 2409984) by lia.
      apply (rw_cells_agree _ _ _ _ _ AG3) in FR; [| intros x Hx; left; cbn in Hx; unfold USTACK_TOP; lia].
      apply (rw_cells_agree _ _ _ _ _ AG3) in CX; [| intros x Hx; right; right; exists (ad_pc AD, ad_ctx AD, 72); split; [exact INC| cbn in Hx |- *; lia]].
      assert (LSC3 : lib_state_hc true [] ls m3 OW AD EA).
      { eapply lib_state_h_heap_pres; [exact LSC1| exact AG3|]. intros b0 Hb0. apply in_or_app. left. exact Hb0. }
      assert (STK3 : stack_rep m3 OW IX c).
      { eapply (stack_rep_agree OW (OW ++ LB) (bv_unsigned sp + -112)); [| exact STK1| exact AG3|].
        - intros b0 Hb0. apply in_or_app. left. exact Hb0.
        - intros q _ _ x Hx _. exact Hx. }
      assert (AXP3 : ax_pres LB (bv_unsigned sp) LIBW_A m m3).
      { eapply ax_pres_trans; [exact AXP1|]. eapply agree_on_mono; [exact AG3|]. intros x [_ [Hx|[Hx|(b0 & Hb0 & Hr)]]];
          [left; lia | right; left; exact Hx | right; right; exists b0; split; [apply in_or_app; right; exact Hb0 | exact Hr]]. }
      pose proof BR as (BA0 & BA16 & _ & BAC & BAI).
      assert (EAn : bv_unsigned (Z_to_bv 64 An) = An) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
      set (OW1 := (pn, An, 400) :: OW) in *.
      assert (ND1 : List.NoDup (map blk_id OW1)) by (exact (AH_nodup_l _ _ _ _ HEAP3)).
      assert (FRESHA : ~ In pn (all_ids ls AD EA)).
      { intros Hin. apply FRESH. rewrite map_app. apply in_or_app. left. eapply all_ids_owned; eauto. }
      assert (NEWSEP : forall q A n, In (q, A, n) OW -> An + 400 <= A \/ A + n <= An).
      { intros q A n Hq. assert (NE : pn <> q) by (intros ->; apply FRESH; rewrite map_app; apply in_or_app; left; apply (in_map blk_id) in Hq; exact Hq).
        exact (AH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP3 ltac:(left; reflexivity) ltac:(right; exact Hq) NE). }
      pose proof (NEWSEP _ _ _ BC) as SEPc.
      assert (LSC3' : lib_state_hc true [] ls m3 OW1 AD EA) by (eapply lib_state_h_ow; [exact LSC3|]; intros q A n _ Hq; right; exact Hq).
      assert (INC1 : In (ad_pc AD, ad_ctx AD, 72) (OW1 ++ LB)) by (apply in_or_app; left; right; exact BC).
      assert (INN1 : In (pn, An, 400) (OW1 ++ LB)) by (apply in_or_app; left; left; reflexivity).
      (* [comment removed for export] *)
      assert (SPLIT : rw_cells bsegs m3 An ([CB 384 (firstn 384 junkA)] ++ [CB 16 (skipn 384 junkA)])).
      { pose proof BLK as [[[LJ _] _] _]. cbn in LJ.
        eapply bk_rw_cells_recast; [exact BLK| | |].
        - cbn. rewrite length_firstn, length_skipn. lia.
        - cbn. rewrite !app_nil_r. apply firstn_skipn.
        - cbn. lia. }
      apply bk_rw_cells_app in SPLIT. destruct SPLIT as [B1 B2]. cbn [cells_size csize Nat.add] in B2. change (Z.of_nat 384) with 384 in B2. clear BLK B1.
      clear ACC MU WM OFF SHB1 SHB2.
      unfold MallocRep.wz in *.
      apply implA_from_evt.
      ub; step. if_cases KA; zify_cond KA; [exfalso; rewrite ?EAn in KA; lia|]. clear KA.
      ub; step.
      ub.
      ub; zstep. rewrite ?(unsigned_lit 0) by lia. change (Z.land 0 8) with 0.
      ub; zstep.
      ub.
      ub; zstep.
      setreg 27%Z (Z_to_bv 64 18446744073709551592) ltac:(apply Z_to_bv_eqm; reflexivity).
      setreg 26%Z (Z_to_bv 64 (Z.of_nat 16)) ltac:(reflexivity).
      apply evt_done.
      eapply implA_step_same.
      { eapply (get_init_loopA 15) with (P := An) (bd := (pn, An, 400)) (lo := lo) (OW := OW1) (LB := LB); try reflexivity.
        - exact HEAP3.
        - rewrite ESP. exact ST3.
        - exact CEIL.
        - rewrite ESP. unfold BN_INIT_STACK, RT_STACK. lia.
        - rewrite ESP. unfold USTACK_TOP. lia.
        - rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia.
        - exact MI3.
        - exact INN1.
        - cbn [blk_addr blk_size fst snd]. lia. }
      intros ms5 PO. unfold init_loop_postA in PO. rewrite ?ESP in PO.
      destruct PO as (ra5 & w0 & w1 & w2 & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & F5 & fc5 & m5 & -> & MI5 & ST5 & HEAP5 & WM5 & AG5 & ZR16).
      change (24 * Z.of_nat 16) with 384 in *. change (24 * 16)%nat with 384%nat in ZR16. unfold MallocRep.wz.
      apply (rw_cells_agree _ _ _ _ _ AG5) in FR; [| intros x Hx; cbn in Hx; split; [left; unfold USTACK_TOP; lia | unfold BnHeapA.ACEIL in *; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG5) in CX; [| intros x Hx; cbn in Hx; split; [right; right; exists (ad_pc AD, ad_ctx AD, 72); split; [exact INC1| cbn; lia] | lia]].
      apply (rw_cells_agree _ _ _ _ _ AG5) in B2; [| intros x Hx; cbn in Hx; split; [right; right; exists (pn, An, 400); split; [exact INN1| cbn; lia] | lia]].
      assert (LSC5 : lib_state_hc true [] ls m5 OW1 AD EA).
      { eapply (lib_state_h_icall Σ1 LB true [] ls m3 m5 OW1 AD EA _ An 384 HEAP3 LSC3' AG5).
        eapply (w_foreign OW1 LB ls AD EA true [] _ pn An 400); [exact INN1 | exact FRESHA | cbn; lia | cbn; lia]. }
      assert (STK5 : stack_rep m5 OW1 IX c).
      { eapply (stack_rep_agree OW1 (OW1 ++ LB) (bv_unsigned sp + -112)); [| eapply stack_rep_ow; [|exact STK3]; intros b0 Hb0; right; exact Hb0 | exact AG5 |].
        - intros b0 Hb0. apply in_or_app. left. exact Hb0.
        - intros q _ HinI x Hx HI. split; [exact Hx|]. intros HAn.
          destruct HinI as [E|HinI]; [injection E as -> -> ; lia|]. pose proof (NEWSEP _ _ _ HinI) as SEPi. lia. }
      assert (AXP5 : ax_pres LB (bv_unsigned sp) LIBW_A m m5).
      { eapply ax_pres_trans; [exact AXP3|]. eapply agree_on_mono; [exact AG5|]. intros x [_ Hc]. split.
        - destruct Hc as [Hc|[Hc|(b0 & Hb0 & Hr)]]; [left; lia | right; left; exact Hc | right; right; exists b0; split; [apply in_or_app; right; exact Hb0 | exact Hr]].
        - intros HAr. destruct Hc as [Hc|[Hc|(b0 & Hb0 & Hr)]].
          + unfold BnHeapA.ACEIL in *. lia.
          + eapply (blk_not_static Σ1 OW1 LB m3 (pn, An, 400) x HEAP3 ltac:(left; reflexivity)); [cbn; lia | exact Hc].
          + assert (NE : blk_id b0 <> pn).
            { intros E. apply FRESH. rewrite <- E. apply in_map. apply in_or_app. right. exact Hb0. }
            pose proof (AH_disjoint_gen _ _ _ _ b0 (pn, An, 400) HEAP3 (in_or_app _ _ _ (or_intror Hb0)) INN1 NE) as DJ. cbn in DJ. lia. }
      assert (SPLZ : rw_cells bsegs m5 An (bn_cells 0 (bn_nil 0) ++ [CB 360 (repeat (Z_to_bv 8 0) 360)])).
      { eapply bk_rw_cells_recast; [exact ZR16| | |].
        - cbn [bn_cells app cells_wf cell_wf]. rewrite repeat_length. tauto.
        - vm_compute. reflexivity.
        - reflexivity. }
      apply bk_rw_cells_app in SPLZ. destruct SPLZ as [BN0 ZR]. cbn [bn_cells cells_size csize Nat.add] in ZR. change (Z.of_nat 24) with 24 in ZR.
      unfold bn_cells in BN0. clear ZR16.
      pose proof (AH_acc_in _ _ _ _ (ad_pc AD, ad_ctx AD, 72) (ad_ctx AD) 72 HEAP5 INC1 ltac:(cbn; lia) ltac:(cbn; lia)) as ACC5.
      pose proof (AH_acc_in _ _ _ _ (pn, An, 400) An 400 HEAP5 INN1 ltac:(cbn; lia) ltac:(cbn; lia)) as ACCN5.
      assert (ALN : An mod 8 = 0) by (clear - BA16; Z.div_mod_to_equations; lia).
      pose proof (AH_offsh _ _ _ _ (pn, An, 400) HEAP5 INN1) as ON. cbn [blk_addr blk_size fst snd] in ON. unfold SHLO, SHHI in ON.
      destruct (AH_shb _ _ _ _ HEAP5) as (SHB51 & SHB52).
      assert (N47 : 0 < An /\ An + 400 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; lia).
      pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72); (An, An + 400)]%Z m5) as MU5.
      pose proof (wmono_refl bsegs m5) as WMr5.
      assert (OFF5 : offshW [(bv_unsigned sp + -112, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72); (An, An + 400)]).
      { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. lia. }
      unfold MallocRep.wz in *.
      apply implA_from_evt.
      do 3 (ub; step). ub; shl. ub; chk0.
      do 3 (ub; step). rewrite ?(unsigned_lit (An + 384)) by (unfold BnHeapA.ACEIL in *; lia).
      ub; shl. ub; chk0.
      ub; step.
      do 2 (ub; step). rewrite ?(unsigned_lit (An + 392)) by (unfold BnHeapA.ACEIL in *; lia).
      ub; step.
      ub; step. ub; shl. ub; chk0.
      ub; step.
      do 2 (ub; step). ub; shl. ub; chk0.
      ub; step.
      ub; step. first [ if_true | let K := fresh "KH" in if_cases K; zify_cond K; [ clear K | exfalso; rewrite ?unsigned_lit in K by lia; lia ] ].
      ub; shl. ub; chk0. ub; step.
      do 3 (ub; step). ub; shl. ub; chk0. ub; step.
      ub; shl. ub; chk0. ub; step.
      ub; shl. ub; chk0. ub; step. rewrite (sx32_small (Z.of_nat (cx_psize c))) by lia. do 2 (ub; step).
      ub; shl. ub; chk0. ub; step. rewrite (sx32_small (Z.of_nat (cx_pused c))) by lia. do 2 (ub; step).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
      assert (ACCN7 : acc bsegs m7 An 24).
      { eapply (acc_munch bsegs _ m5 m7 _ _ (acc_sub bsegs m5 An 400 An 24 ACCN5 ltac:(lia) ltac:(lia)) MU5 OFF5); unfold BnHeapA.ACEIL in *; lia. }
      assert (ACCC7 : acc bsegs m7 (ad_ctx AD) 72) by (eapply (acc_munch bsegs _ m5 m7 _ _ ACC5 MU5 OFF5); unfold BnHeapA.ACEIL in *; lia).
      apply rw_cells_CB8_hd in FR.
      eapply evt_cut.
      { eapply (get_tailA) with (lo := lo) (CTX := ad_ctx AD) (A := An) (D := 0) (b := bn_nil 0) (used := Z.of_nat (cx_used c));
          [exact BN0 | cbn; lia | exact CX | lia | exact FR | exact ST5 | unfold BnHeapA.ACEIL in *; lia | eassumption
          | unfold BnHeapA.ACEIL in *; lia | unfold BnHeapA.ACEIL in *; lia | lia | unfold BnHeapA.ACEIL in *; lia
          | exact (conj SHB51 SHB52) | exact ACCN7 | exact ALN | exact ACCC7 | exact AL
          | unfold SHHI, BnHeapA.ACEIL in *; lia | unfold SHLO, SHHI; lia | unfold SHLO, SHHI; lia | unfold BnHeapA.ACEIL in *; lia ]. }
      intros ms' PO. unfold get_tail_postA in PO.
      destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & mF & -> & MUt & WMt & MIt & STt & BNt & CXt).
      apply evt_done. cbn [tbind fst snd]. apply implA_ret.
      set (c2 := mkCtx (Some pn) (Some pn) (repeat (bn_nil 0) 16) 1 16 (cx_indexes c) (cx_frames c) (cx_ssize c) (S (cx_used c)) 0 false).
      lazymatch goal with |- context [(RPool 0, ?lsM)] => change lsM with (set_ctx c2 ls) end.
      set (WF := [(bv_unsigned sp - 128, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72); (An, An + 400)]%Z).
      assert (MUF : munch WF m5 mF).
      { eapply munch_trans; [eapply munch_weaken; [|exact MU5]| eapply munch_weaken; [|exact MUt]];
          intros xx Hx; subst WF; cbn [outside] in *; clear - Hx; intuition lia. }
      assert (WMF : wmono bsegs m5 mF) by (eapply wmono_trans; eassumption).
      assert (HinN : In (pn, An, 400) OW1) by (left; reflexivity).
      assert (BC1 : In (ad_pc AD, ad_ctx AD, 72) OW1) by (right; exact BC).
      assert (HWL5 : Forall (w_lib OW1 lo (bv_unsigned sp)) WF).
      { subst WF. constructor; [left; cbn; lia|]. constructor; [right; exists (ad_pc AD, ad_ctx AD, 72); cbn; auto with zarith|].
        constructor; [right; exists (pn, An, 400); cbn; auto with zarith| constructor]. }
      assert (LSF : lib_state (set_ctx c2 ls) mF OW1 AD EA).
      { unfold lib_state. eapply (lib_state_cx_close_newpool [] ls mF OW1 AD EA c2 pn An An IX); [| exact Eh| reflexivity| reflexivity| exact HinN| | | | | |].
        - eapply (lib_state_frame Σ1 LB); [exact HEAP5| exact LSC5| exact MUF| exact WMF|]. subst WF.
          constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|].
          constructor; [apply w_cx; [reflexivity| intros x' Hx; left; cbn in Hx; lia]|].
          constructor; [|constructor].
          eapply (w_foreign OW1 LB ls AD EA true [] _ pn An 400); [exact INN1| exact FRESHA| cbn; lia| cbn; lia].
        - change (repeat (bn_nil 0 : bignum bptr) 16) with (bn_nil 0 :: repeat (bn_nil 0 : bignum bptr) 15). cbn [bns_gen]. split.
          + unfold repR, bn_rep. exists 0. split; [exact BNt|]. unfold bn_arr. cbn [bn_nil bn_d bn_buf]. auto.
          + apply (bns_gen_zeros 15). change (24 * 15)%nat with 360%nat.
            eapply rw_cells_transport; [exact ZR| exact MUt| exact WMt|]. cbn [disjoint_from cells_size csize Nat.add]. clear - SEPc BAC CEIL LO SPR. unfold BnHeapA.ACEIL in *. lia.
        - unfold ctx_cells, c2. cbn [cx_pused cx_psize cx_frames cx_ssize cx_used cx_err_stack cx_too_many Z.b2z]. unfold MallocRep.wz.
          rewrite EP0, EPZ in CXt. rewrite (Nat2Z.inj_succ (cx_used c)). unfold Z.succ. exact CXt.
        - change (stack_rep mF OW1 IX (ls_ctx ls)). fold c.
          eapply (stack_rep_munch Σ1 OW1 LB m5 mF ls AD EA IX); [exact HEAP5| exact IDS| | exact STK5| exact MUF| exact WMF|].
          + destruct ADB as (A1 & A2 & A3 & A4 & A5 & A6). unfold ad_blocks. repeat split; right; assumption.
          + subst WF. constructor; [left; cbn; unfold BnHeapA.ACEIL in *; lia|]. constructor; [right; left; cbn; lia|]. constructor; [|constructor].
            right; right. exists pn, An, 400. split; [exact INN1|]. cbn [fst snd]. split; [lia|]. split; [lia|].
            fold c. intros E. apply FRESHA. unfold all_ids. apply in_or_app; right; apply in_or_app; right. apply idx_in_m. symmetry. exact E.
        - unfold pool_mem, c2. cbn [cx_head cx_current]. split; [|right; split; reflexivity].
          eapply rw_cells_transport; [exact B2| exact MUt| exact WMt|]. cbn [disjoint_from cells_size csize Nat.add]. clear - SEPc BAC CEIL LO SPR. unfold BnHeapA.ACEIL in *. lia.
        - unfold ctx_okm, c2. cbn [cx_pused cx_used cx_psize cx_vals cx_frames cx_ssize cx_current cx_head cx_err_stack].
          split; [lia|]. split; [lia|]. split; [rewrite repeat_length; reflexivity|].
          split; [eapply nondecr_last_incr; [exact CK4| lia]|]. split; [exact CK5|]. split; [reflexivity| reflexivity].
        - eapply (ids_ok_set_ctx_new_head ls AD EA c2 pn); [exact IDS| reflexivity| exact Eh| exact EV0| reflexivity| reflexivity| exact FRESHA]. }
      unfold bn_postA. do 17 eexists. exists mF, OW1. split; [reflexivity|]. cbn [fst snd].
      split; [exact (seg_heap Σ1 OW1 LB m5 mF _ lo _ HEAP5 MUF WMF HWL5 CEIL ltac:(unfold USTACK_TOP; lia))|]. split; [exact LSF|].
      split; [exact STt|]. split; [exact MIt|].
      split. { eapply ax_pres_trans; [exact AXP5|]. exact (seg_ax_pres' Σ1 OW1 LB m5 mF _ lo _ _ HEAP5 MUF HWL5 CEIL ltac:(lia)). }
      split; [exact CR3|].
      split. { unfold cnt_eq, cnt_bal, blocks_of. cbn [set_ctx ls_b1 ls_b2 ls_b3 ls_b4 ls_b5 ls_ctx]. fold c. unfold c2. cbn [cx_vals cx_head cx_indexes].
               rewrite Eh, EV0.
               assert (EC2 : concat (map bn_blocks (repeat (bn_nil 0 : bignum bptr) 16)) = []) by reflexivity. rewrite EC2.
               cbn [map concat opt_block app]. unfold OW1. rewrite !length_app. cbn [length]. lia. }
      split. { intros r' a' HA'. destruct r' as [| | | | |j]; cbn [ref_at] in HA' |- *; try exact HA'.
               destruct HA' as (p0 & H0 & E0 & _). fold c in E0. congruence. }
      split; [|intros q0 A0 n0 Hq0; right; exact Hq0].
      exists An. split; [|reflexivity].
      cbn [ref_at]. exists pn, An. split; [reflexivity|]. split; [exact HinN|]. split; [lia| lia].
Qed.

End WithRT.
