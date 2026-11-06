(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.openssl.bndiv.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnModel BnTree BnInv BnSpecs BnMInv BnBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.U Require Import Layout Lib_iface Lib_kit F_memset F_memcpy.
From OSSVerify.Proofs.openssl.bndiv.lib.U Require Drv_facts.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnMem BnTac.
From OSSVerify.Proofs.openssl.bndiv.lib.BnWU Require Import BnUTac.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bndiv.lib.BnU Require Import BnHeap BnRep BnIface BnUAlign BnUKit W_small W_small2 W_crypto W_ctx.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition BN_CTX_GET : Z := 0x115460.
Definition BN_CTX_GET_STACK : Z := 64 + 8400.

(* [comment removed for export] *)
Definition get_tail_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo CTX A D : Z) (b : bignum bptr) (c0 c1 c2 c3 c4 c5 c6 c7 c9 c10 c11 c12 : word) (used : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (A, A + 24); (CTX, CTX + 72)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' A (bn_cells D (bn_zero_pure b))
    /\ rw_cells usegs m' CTX [C8 c0; C8 c1; C8 c2; C4 c3; C4 c4; C8 c5; C4 c6; C4 c7; C4 (Z_to_bv 64 (used + 1)); C4 c9; C4 c10; C4 c11; C8 c12].

Lemma get_tail : forall (x1 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra s0 s1 s2 s3 s4 s5 s6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo CTX A D : Z) (b : bignum bptr)
    (c0 c1 c2 c3 c4 c5 c6 c7 c9 c10 c11 c12 : word) (used : Z),
  rw_cells usegs m A (bn_cells D b) -> 0 < A /\ A mod 8 = 0 -> 0 <= bn_flags b <= 1 ->
  rw_cells usegs m CTX [C8 c0; C8 c1; C8 c2; C4 c3; C4 c4; C8 c5; C4 c6; C4 c7; C4 (Z_to_bv 64 used); C4 c9; C4 c10; C4 c11; C8 c12] ->
  0 <= used < 2^31 - 1 ->
  rw_cells usegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk usegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - 80 -> mem_inv usegs m ->
  (A + 24 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= A) -> (CTX + 72 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= CTX) ->
  (A + 24 <= CTX \/ CTX + 72 <= A) -> 0 <= lo ->
  evt usegs (get_tail_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo CTX A D b c0 c1 c2 c3 c4 c5 c6 c7 c9 c10 c11 c12 used)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 CTX) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 A) x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x115630) fc None m (seg_rom usegs)).
Proof.
  intros until used. intros BN PAL FLR CX USED FR ST LO MI SEPA SEPC SEPAC LO0.
  pose proof PAL as [PA PM].
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (A, A + 24); (CTX, CTX + 72)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  step. step.
  eapply evt_cut.
  { eapply (BN_zero_ex_spec) with (lo := lo) (A := A) (D := D) (b := b); rewrite ?ESP; [exact BN| exact PAL| exact ST| lia| exact MI| lia| reflexivity]. }
  rewrite ?ESP. post_call usegs m.
  rewrite ESP in PC. unfold bn_cells in POST.
  replace (bn_flags (bn_zero_pure b)) with (bn_flags b) in POST by reflexivity.
  step. rewrite (land7_wrap _ PM).
  chk ltac:(fun C => clear - C; lia).
  step. unfold wz at 1. rewrite (zx32_small (bn_flags b)) by lia.
  step. rewrite (sx32_small used) by lia.
  step.
  replace (Z.land (bv_unsigned (Z_to_bv 64 (bn_flags b))) 18446744073709551611) with (bn_flags b)
    by (assert (bn_flags b = 0 \/ bn_flags b = 1) as [E|E] by lia; rewrite E; reflexivity).
  step. step. step. step. step.
  do 8 step. step. release_frame FR PC (bv_unsigned sp). step.
  finish.
Qed.

(* [comment removed for export] *)
Definition init_loop_post (sp gp tp s0 s1 s2 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo P : Z) (n : nat) : machine_state -> Prop :=
  fun ms' => exists ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (P + 24 * Z.of_nat n)) (Z_to_bv 64 0)
                  (Z_to_bv 64 0) (Z_to_bv 64 (-24)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x115548) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (P, P + 24 * Z.of_nat n)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' P [CB (24 * n) (repeat (Z_to_bv 8 0) (24 * n))].

Lemma get_init_loop : forall (n : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo P : Z) (junk : list byte),
  rw_cells usegs m P [CB (24 * S n) junk] ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> mem_inv usegs m ->
  (P + 24 * Z.of_nat (S n) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= P) -> 0 < P -> P + 24 * Z.of_nat (S n) < 2^63 -> (n < 2^20)%nat ->
  evt usegs (init_loop_post sp gp tp s0 s1 s2 s7 s8 s9 s10 s11 F fc m lo P (S n))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 P) (Z_to_bv 64 0)
             (Z_to_bv 64 (Z.of_nat (S n))) (Z_to_bv 64 (-24)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x115520) fc None m (seg_rom usegs)).
Proof.
  induction n as [|n IH]; intros until junk; intros BLK ST LO MI SEP P0 PHI NB.
  - (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (P, P + 24 * Z.of_nat 1)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    change (24 * 1)%nat with 24%nat in *. change (24 * Z.of_nat 1) with 24 in *. change (Z.of_nat 1) with 1.
    step. step.
    eapply evt_cut.
    { eapply (bn_init_spec) with (lo := lo) (A := P) (junk := junk); [exact BLK| exact ST| lia| exact MI| lia| reflexivity]. }
    post_call usegs m.
    step. if_true.
    chk ltac:(fun C => clear - C P0 PHI; lia).
    step. step.
    step. if_false.
    finish. eapply bk_rw_cells_recast; [exact POST| cbn; split; [reflexivity| exact I]| reflexivity| reflexivity].
  - (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (P, P + 24 * Z.of_nat (S (S n)))]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (SPLIT : rw_cells usegs m P ([CB 24 (firstn 24 junk)] ++ [CB (24 * S n) (skipn 24 junk)])).
    { pose proof BLK as [[[LJ _] _] _]. cbn in LJ.
      eapply bk_rw_cells_recast; [exact BLK| | |].
      - cbn. rewrite length_firstn, length_skipn. lia.
      - cbn. rewrite !app_nil_r. apply firstn_skipn.
      - cbn. lia. }
    apply bk_rw_cells_app in SPLIT. destruct SPLIT as [B1 B2]. cbn [cells_size csize Nat.add] in B2. change (Z.of_nat 24) with 24 in B2. clear BLK.
    step. step.
    eapply evt_cut.
    { eapply (bn_init_spec) with (lo := lo) (A := P) (junk := firstn 24 junk); [exact B1| exact ST| lia| exact MI| lia| reflexivity]. }
    post_call usegs m.
    step. if_true.
    chk ltac:(fun C => clear - C P0 PHI; lia).
    step. rewrite (swrap32_wrap64 (Z.of_nat (S (S n))) (-1)) by lia.
    replace (Z.of_nat (S (S n)) + -1) with (Z.of_nat (S n)) by lia.
    step.
    step. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia; [|exfalso; lia]. clear KB.
    replace (P + 24 * Z.of_nat (S (S n))) with (P + 24 + 24 * Z.of_nat (S n)) by lia.
    unfold bn_cells in POST.
    eapply evt_cut.
    { eapply (IH) with (lo := lo) (P := P + 24) (junk := skipn 24 junk); [exact B2| exact PC| lia| exact MI0| lia| lia| lia| lia]. }
    lazymatch goal with |- forall _, _ -> evt _ _ _ => idtac end.
    lazymatch goal with MUx : munch _ m ?mx |- _ => post_call usegs mx end.
    apply evt_done. unfold init_loop_post. do 16 eexists. eexists.
    split. { replace (P + 24 + 24 * Z.of_nat (S n)) with (P + 24 * Z.of_nat (S (S n))) by lia. reflexivity. }
    split; [exact MU|].
    split; [exact WM|]. split; [exact MI|]. split; [exact PC|].
    assert (JOIN : rw_cells usegs x31 P ([C8 (wz 0); C4 (wz (Z.of_nat (bn_top (bn_nil 0 : bignum bptr)))); C4 (wz (Z.of_nat (bn_dmax (bn_nil 0 : bignum bptr))));
                                         C4 (wz (Z.b2z (bn_neg (bn_nil 0 : bignum bptr)))); C4 (wz (bn_flags (bn_nil 0 : bignum bptr)))]
                                        ++ [CB (24 * S n) (repeat (Z_to_bv 8 0) (24 * S n))])).
    { apply bk_rw_cells_app. split; [exact POST| exact POST0]. }
    eapply bk_rw_cells_recast; [exact JOIN| | |].
    + cbn [cells_wf cell_wf]. rewrite repeat_length. tauto.
    + cbn [cells_bytes cbytes app]. rewrite !app_nil_r.
      replace (24 * S (S n))%nat with (24 + 24 * S n)%nat by lia. rewrite repeat_app. reflexivity.
    + cbn [cells_size csize app]. lia.
Qed.

(* [comment removed for export] *)
Lemma bns_gen_zeros : forall (n : nat) (m : mem) (OW : list block) A i,
  rw_cells usegs m A [CB (24 * n) (repeat (Z_to_bv 8 0) (24 * n))] -> bns_gen (repR m OW) A (repeat (bn_nil 0) n) i.
Proof.
  induction n as [|n IH]; intros m OW A i HZ; cbn [repeat bns_gen]; [exact I|].
  assert (SPLIT : rw_cells usegs m A (bn_cells 0 (bn_nil 0) ++ [CB (24 * n) (repeat (Z_to_bv 8 0) (24 * n))])).
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
Lemma cx_vals_head : forall cxo hs ls m OW AD EA, lib_state_hc cxo hs ls m OW AD EA ->
  cx_vals (ls_ctx ls) = [] -> cx_head (ls_ctx ls) = None.
Proof.
  intros cxo hs ls m OW AD EA (_ & _ & _ & (_ & _ & (_ & _ & _ & _ & _ & _ & _ & (H' & Cu' & I' & _ & HPool & _)))) E.
  destruct (cx_head (ls_ctx ls)) as [p|]; [|reflexivity]. destruct HPool as (_ & HL & _). rewrite E in HL. discriminate.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma stack_rep_munch : forall s OW LB m m' ls AD EA IX W,
  RHEAP s (OW ++ LB) m -> ids_ok ls AD EA -> ad_blocks OW AD ->
  stack_rep m OW IX (ls_ctx ls) -> munch W m m' -> wmono usegs m m' ->
  Forall (fun iv : Z * Z => alloc_ceiling <= fst iv \/ (ad_ctx AD <= fst iv /\ snd iv <= ad_ctx AD + 72)
                            \/ (exists q A n, In (q, A, n) (OW ++ LB) /\ A <= fst iv /\ snd iv <= A + n /\ Some q <> cx_indexes (ls_ctx ls))) W ->
  stack_rep m' OW IX (ls_ctx ls).
Proof.
  intros s OW LB m m' ls AD EA IX W HEAP IDS ADB STK MU WM HW. unfold stack_rep in *.
  destruct (cx_indexes (ls_ctx ls)) as [q|] eqn:EI; [|exact STK].
  destruct STK as (HinI & SZ32 & stale & LEN & ARRI). split; [exact HinI|]. split; [exact SZ32|]. exists stale. split; [exact LEN|].
  pose proof (RH_range _ _ _ _ _ _ _ HEAP HinI) as (IA0 & IA16 & _ & IAC & IAI).
  destruct ADB as (_ & _ & _ & _ & _ & BC).
  assert (NEI : ad_pc AD <> q) by (eapply ids_ad_m; [exact IDS| apply ad_pc_in| apply idx_in_m; exact EI]).
  pose proof (RH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP BC HinI NEI) as CXI.
  assert (LWS : Z.of_nat (length (map (fun k : nat => wz (Z.of_nat k)) (cx_frames (ls_ctx ls)) ++ stale)) = 32) by (rewrite length_app, length_map; lia).
  eapply u32arr_transport; [exact ARRI| exact MU| exact WM|]. rewrite LWS. clear MU ARRI.
  induction HW as [|[x y] W Hiv HW IH]; [exact I|]. cbn [disjoint_from]. split; [|exact IH].
  cbn [fst snd] in Hiv. destruct Hiv as [Hs|[Hc|(q' & A & n & Hq & H1 & H2 & NE)]]; [lia| lia|].
  assert (NEq : q' <> q) by congruence.
  pose proof (LH_disjoint _ _ _ (q', A, n) (q, IX, 128) HEAP Hq ltac:(apply in_or_app; left; exact HinI) NEq) as DJ.
  cbn [blk_addr blk_size fst snd] in DJ. lia.
Qed.

Lemma stack_rep_heap_pres : forall (OW : list block) L SP m m' IX (c : bn_ctx bptr),
  (forall b, In b OW -> In b L) -> stack_rep m OW IX c -> rheap_pres L SP m m' -> stack_rep m' OW IX c.
Proof.
  intros OW L SP m m' IX c HI STK HP. unfold stack_rep in *. destruct (cx_indexes c) as [q|]; [|exact STK].
  destruct STK as (HinI & SZ32 & stale & LEN & ARRI). split; [exact HinI|]. split; [exact SZ32|]. exists stale. split; [exact LEN|].
  eapply u32arr_agree; [apply agree_of_heap_pres; exact HP| exact ARRI|]. intros x Hx.
  right; right. exists (q, IX, 128). split; [apply HI; exact HinI|]. cbn [blk_addr blk_size fst snd].
  rewrite length_app, length_map in Hx. lia.
Qed.

Lemma stack_rep_ow : forall (OW OW' : list block) m IX (c : bn_ctx bptr),
  (forall b, In b OW -> In b OW') -> stack_rep m OW IX c -> stack_rep m OW' IX c.
Proof.
  intros OW OW' m IX c HI STK. unfold stack_rep in *. destruct (cx_indexes c) as [q|]; [|exact STK].
  destruct STK as (HinI & REST). split; [apply HI; exact HinI| exact REST].
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.

  Lemma BN_CTX_get_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
      (lo B : Z) (errv : word),
    bn_pre s ls m OW LB AD EA sp lo B errv BN_CTX_GET_STACK -> tp = wz RATP -> a0 = wz (ad_ctx AD) ->
    implM usegs (interp (embed (BN_CTX_get (tree_ops bptr) ls))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA
               (fun r ls' OW' a0' => (exists a, ref_at ls' OW' AD r a /\ a0' = wz a) /\ (forall q A n, In (q, A, n) OW -> In (q, A, n) OW')))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_CTX_GET) fc None m (seg_rom usegs)).
  Proof.
    intros until errv. intros (HEAP & LS & AUX & SPB & ST & CEIL & GLO & LO & ERR & MI) -> ->.
    unfold BN_CTX_GET_STACK, BN_CTX_GET, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
    pose proof SOK as (_ & _ & _ & _ & _ & POK & (CK1 & CK2 & CK3 & CK4 & CK5 & CK6 & CK7)).
    destruct (lib_state_cx_open [] ls m OW AD EA LS) as (H & Cu & IX & CX & STK & PM & HH & LSC).
    pose proof ADB as (_ & _ & _ & _ & _ & BC). pose proof (RH_range _ _ _ _ _ _ _ HEAP BC) as (CA0 & CA16 & _ & CAC & CAI).
    set (c := ls_ctx ls) in *.
    unfold ctx_cells in CX. rewrite CK7 in CX. change (Z.of_nat 0) with 0 in CX.
    unfold LX_ERRNO, RATP in ERR. change (3353240 - 164) with 3353076 in ERR.
    unfold BN_CTX_get, bbind, bgetctx, bret, bunr, bmalloc, bsetctx, bget, bset.
    cbn [bind ret unreachable lib_malloc lib_free tree_ops tbind fst snd]. fold c.
    rewrite CK7. cbn [Nat.eqb negb orb].
    assert (PSZ : cx_psize c = 0%nat \/ cx_psize c = 16%nat).
    { rewrite CK3. destruct POK as [EV|[EV _]]; [left; rewrite EV; reflexivity| right; exact EV]. }
    unfold implM. iprefix.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (CA8 : ad_ctx AD mod 8 = 0) by (clear - CA16; Z.div_mod_to_equations; lia).
    carve_frame 64%nat ST. do 10 step.
    chk ltac:(fun C => clear - C CA0 CAC; lia).
    step. step. rewrite (land7_wrap _ CA8).
    chk ltac:(fun C => clear - C; lia).
    step. unfold MallocRep.wz at 1. rewrite (sx32_small 0) by lia.
    step. if_false.
    step.
    destruct (cx_too_many c) eqn:ETM.
    { ihere. to_implM. cbn [embed interp]. apply implM_interp_unr. }
    cbn [Z.b2z] in *. unfold MallocRep.wz at 1. rewrite (sx32_small 0) by lia.
    step. if_true.
    step. unfold MallocRep.wz at 1. rewrite (zx32_small (Z.of_nat (cx_pused c))) by lia.
    step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (cx_psize c))) by lia.
    step. rewrite (swrap32_wrap64 (Z.of_nat (cx_pused c)) 0) by lia. rewrite Z.add_0_r.
    step. if_cases KP; zify_cond KP; rewrite ?unsigned_lit in KP by lia.
    - (* [comment removed for export] *)
      replace (cx_pused c =? cx_psize c)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
      cbn [tbind fst snd].
      assert (PS16 : cx_psize c = 16%nat) by lia.
      destruct (cx_head c) as [ph|] eqn:Eh.
      2:{ exfalso. pose proof (cx_head_vals _ _ _ _ _ _ _ LSC Eh) as EV. fold c in EV. rewrite EV in CK3. cbn in CK3. lia. }
      pose proof (RH_range _ _ _ _ _ _ _ HEAP HH) as (HA0 & HA16 & _ & HAC & HAI).
      assert (NEH : ad_pc AD <> ph) by (eapply ids_ad_m; [exact IDS| apply ad_pc_in| apply head_in_m; exact Eh]).
      pose proof (RH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP BC HH NEH) as CXH.
      set (i := cx_pused c) in *.
      assert (IR : (i < 16)%nat) by lia.
      assert (IU : i = cx_used c) by exact CK1.
      assert (HA : ref_at ls OW AD (RPool i) (H + 24 * Z.of_nat i)).
      { cbn [ref_at]. exists ph, H. fold c. split; [exact Eh|]. split; [exact HH|]. split; [lia| reflexivity]. }
      destruct (lib_state_open [] ls m OW AD EA (RPool i) _ LSC ND HA ltac:(intros [])) as ((D & BN & ARR) & (OK1 & OK2 & OK3 & OK4) & LSH).
      set (b := getbn (RPool i) ls) in *.
      assert (FLR : 0 <= bn_flags b <= 1) by (destruct OK4 as [E|E]; rewrite E; lia).
      lazymatch goal with |- evt _ ?Q _ => remember Q as QQ eqn:EQQ end.
      assert (HA8 : H mod 8 = 0) by (clear - HA16; Z.div_mod_to_equations; lia).
      lazymatch goal with |- evt _ ?Q (MS _ _ _ _ _ ?mx _) =>
        assert (CONT : forall (x11 x12 : word) (mX : mem),
          rw_cells usegs mX (ad_ctx AD)
            [C8 (wz H); C8 (wz H); C8 (wz H); C4 (wz (Z.of_nat i)); C4 (wz (Z.of_nat (cx_psize c))); C8 (wz IX);
             C4 (wz (Z.of_nat (length (cx_frames c)))); C4 (wz (Z.of_nat (cx_ssize c))); C4 (wz (Z.of_nat (cx_used c)));
             C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0)] ->
          rw_cells usegs mX (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
          stk usegs mX lo (bv_unsigned sp + -64) ->
          munch [(bv_unsigned sp + -64, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72)]%Z m mX -> wmono usegs m mX -> mem_inv usegs mX ->
          rw_cells usegs mX 3353076 [C4 errv] ->
          evt usegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 RATP) t0 t1 t2 sp (Z_to_bv 64 (ad_ctx AD))
                               (Z_to_bv 64 (Z.of_nat i)) x11 x12 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x1155d4) fc None mX (seg_rom usegs))) end.
      { intros x11 x12 mX CXX FRX STX MUX WMX MIX ERRX.
        clear MU WM MI ERR ST FR CX.
        unfold MallocRep.wz in CXX.
        step.
        chk ltac:(fun C => clear - C HA0 HAC; lia).
        step. rewrite (land7_wrap _ HA8).
        chk ltac:(fun C => clear - C; lia).
        step. step.
        rewrite !(unsigned_lit (Z.of_nat i)) by lia.
        replace (Z.land (Z.of_nat i) 15) with (Z.of_nat i)
          by (change 15 with (Z.ones 4); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
        step. step. step.
        rewrite !(unsigned_lit (Z.of_nat i)) by lia. rewrite !Z.shiftl_mul_pow2 by lia.
        rewrite (unsigned_lit (Z.of_nat i * 2 ^ 3)) by lia.
        replace (Z.of_nat i * 2 ^ 5 + - (Z.of_nat i * 2 ^ 3)) with (24 * Z.of_nat i) by lia.
        step. rewrite (not64 H) by (clear - HA0 HAC; lia).
        step.
        chk ltac:(fun C => clear - C HA0 HAC IR; lia).
        step. step.
        unfold bn_cells in BN.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?my _) => rename my into m2 end.
        lazymatch type of MUX with munch ?W0 _ _ =>
          apply (rw_cells_transport usegs W0 m m2 (H + 24 * Z.of_nat i)) in BN; [| exact MUX| exact WMX| cbn [disjoint_from cells_size csize Nat.add]; lia] end.
        eapply evt_cut.
        { eapply (get_tail) with (lo := lo) (CTX := ad_ctx AD) (A := H + 24 * Z.of_nat i) (D := D) (b := b) (used := Z.of_nat (cx_used c));
            [exact BN | split; [clear - HA0; lia| clear - HA8; Z.div_mod_to_equations; lia] | exact FLR | exact CXX | lia | exact FRX | exact STX | lia | exact MIX | lia | lia | lia | lia ]. }
        intros ms' PO. unfold get_tail_post in PO.
        destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & mF & -> & MUt & WMt & MIt & STt & BNt & CXt).
        subst QQ. apply evt_done. to_implM. cbn [embed interp]. apply implM_ret. apply evt_done.
        set (bz := bn_zero_pure b).
        set (cur := if (i =? 0)%nat then Some ph else cx_current c).
        set (c2 := mkCtx (Some ph) cur (list_set (cx_vals c) i bz) (S i) (cx_psize c) (cx_indexes c) (cx_frames c) (cx_ssize c)
                         (S (cx_used c)) 0 false).
        lazymatch goal with |- context [(RPool i, ?lsM)] =>
          change lsM with (set_ctx c2 (setbn (RPool i) bz ls)) end.
        set (WF := [(bv_unsigned sp - 80, bv_unsigned sp); (H + 24 * Z.of_nat i, H + 24 * Z.of_nat i + 24); (ad_ctx AD, ad_ctx AD + 72)]%Z).
        assert (MUF : munch WF m mF).
        { eapply munch_trans; [eapply munch_weaken; [|exact MUX]| exact MUt].
          intros x Hx. subst WF. cbn [outside] in *. clear - Hx. intuition lia. }
        assert (WMF : wmono usegs m mF) by (eapply wmono_trans; eassumption).
        assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) WF).
        { subst WF. constructor; [left; cbn; lia|]. constructor; [right; exists (ph, H, 400); cbn; split; [exact HH| lia]|].
          constructor; [right; exists (ad_pc AD, ad_ctx AD, 72); cbn; auto with zarith| constructor]. }
        pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSC HA) as HV.
        assert (VLEN : length (cx_vals c) = 16%nat) by lia.
        assert (ECUR : cur = Some ph /\ (Cu = H \/ i = 0%nat)).
        { subst cur. destruct (Nat.eqb_spec i 0) as [E0|E0]; [split; [reflexivity| right; exact E0]|].
          pose proof (CK6 E0) as EC. split; [rewrite EC; reflexivity|]. left.
          unfold pool_mem in PM. rewrite Eh in PM. destruct PM as [_ [[E1 _]|[_ E2]]]; [congruence| exact E2]. }
        destruct (bn_arr_facts s OW LB m HEAP ls AD EA IDS ADB (RPool i) D HV ARR) as (U & LENW & D0 & DC & DI & DSEP).
        specialize (DSEP (RPool i) _ HA). fold b in U, LENW, DC, DI, DSEP.
        assert (DCX : ad_ctx AD + 72 <= D \/ D + 8 * Z.of_nat (bn_dmax b) <= ad_ctx AD).
        { unfold bn_arr in ARR. destruct (bn_d b) as [pd|] eqn:Ed.
          - destruct ARR as [Hin _]. assert (NE : ad_pc AD <> pd) by (eapply ids_ad_m; [exact IDS| apply ad_pc_in| eapply bn_in_m; [exact HV| exact Ed]]).
            exact (RH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP BC Hin NE).
          - destruct ARR as [-> Eb]. unfold bn_dmax. rewrite Eb. cbn. lia. }
        assert (LSF : lib_state (set_ctx c2 (setbn (RPool i) bz ls)) mF OW AD EA).
        { unfold lib_state.
          assert (IDS1 : ids_ok (setbn (RPool i) bz ls) AD EA) by (apply ids_ok_setbn_same; [exact IDS| exact HV| reflexivity]).
          assert (LS1 : lib_state_hc true [] (setbn (RPool i) bz ls) mF OW AD EA).
          { eapply (lib_state_close [] ls mF OW AD EA (RPool i) (H + 24 * Z.of_nat i) bz); [| exact ND| exact HA| | | exact IDS1].
            - eapply (lib_state_frame s LB); [exact HEAP| exact LSH| exact MUF| exact WMF|]. subst WF.
              constructor; [apply w_stack; cbn; lia|].
              constructor; [eapply (w_struct OW LB ls AD EA true [RPool i] _ (RPool i) (H + 24 * Z.of_nat i)); [left; reflexivity| exact HA| cbn; lia| cbn; lia]|].
              constructor; [apply w_cx; [reflexivity| intros x Hx; left; cbn in Hx; lia]| constructor].
            - exists D. split; [exact BNt|]. change (bn_arr mF OW D b).
              eapply bn_arr_of_u64arr; [exact ARR|]. eapply u64arr_transport; [exact U| exact MUF| exact WMF|].
              subst WF. cbn [disjoint_from]. rewrite LENW. clear - DSEP DCX DC CEIL LO SPR. lia.
            - subst bz. unfold bn_okm, bn_zero_pure, bn_dmax in *. cbn [bn_buf bn_top bn_flags]. split; [exact OK1|]. split; [lia|]. split; [exact OK3| exact OK4]. }
          eapply (lib_state_cx_close [] (setbn (RPool i) bz ls) mF OW AD EA c2 H H IX); [exact LS1| exact ND| | | | | | | |].
          - cbn. symmetry. exact Eh.
          - reflexivity.
          - cbn [c2 cx_head]. exact HH.
          - unfold ctx_cells, c2. cbn [cx_pused cx_psize cx_frames cx_ssize cx_used cx_err_stack cx_too_many Z.b2z]. unfold MallocRep.wz.
            rewrite !Nat2Z.inj_succ. unfold Z.succ. exact CXt.
          - change (stack_rep mF OW IX c). unfold stack_rep in *. destruct (cx_indexes c) as [q|] eqn:EI; [|exact STK].
            destruct STK as (HinI & SZ32 & stale & LEN & ARRI). split; [exact HinI|]. split; [exact SZ32|]. exists stale. split; [exact LEN|].
            pose proof (RH_range _ _ _ _ _ _ _ HEAP HinI) as (IA0 & IA16 & _ & IAC & IAI).
            assert (NEI : ad_pc AD <> q) by (eapply ids_ad_m; [exact IDS| apply ad_pc_in| apply idx_in_m; exact EI]).
            pose proof (RH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP BC HinI NEI) as CXI.
            assert (NEHI : ph <> q) by (eapply (ids_head_idx_neq ls ph q); eauto using ids_m_nodup).
            pose proof (RH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP HH HinI NEHI) as HXI.
            eapply u32arr_transport; [exact ARRI| exact MUF| exact WMF|]. subst WF. cbn [disjoint_from].
            rewrite length_app, length_map. clear - LEN CXI HXI IAC CEIL LO SPR IR. lia.
          - unfold pool_mem in *. cbn [c2 cx_head cx_current]. rewrite Eh in PM. destruct PM as [PN _]. split.
            + eapply rw_cells_transport; [exact PN| exact MUF| exact WMF|]. subst WF. cbn [disjoint_from cells_size csize Nat.add].
              clear - CXH HAC CEIL LO SPR IR. lia.
            + right. split; [exact (proj1 ECUR)| reflexivity].
          - unfold ctx_okm, c2. cbn [cx_pused cx_used cx_psize cx_vals cx_frames cx_ssize cx_current cx_head cx_err_stack].
            split; [lia|]. split; [lia|]. split; [rewrite list_set_length; exact CK3|].
            split; [eapply nondecr_last_incr; [exact CK4| lia]|]. split; [exact CK5|]. split; [intros _; exact (proj1 ECUR)| reflexivity].
          - apply ids_ok_set_ctx_same; [exact IDS1| cbn; symmetry; exact Eh| reflexivity| reflexivity]. }
        unfold bn_post. do 15 eexists. exists mF, OW, errv. split; [reflexivity|]. cbn [fst snd].
        split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MUF WMF HWL CEIL)|]. split; [exact LSF|].
        split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ HEAP AUX MUF WMF HWL SPB); unfold GLOBALS_TOP; lia|]. split; [exact STt|].
        split. { unfold LX_ERRNO, RATP. change (3353240 - 164) with 3353076.
                 eapply rw_cells_transport; [exact ERRX| exact MUt| exact WMt|]. cbn [disjoint_from cells_size csize Nat.add].
                 clear - HAI CAI GLO LO SPR IR. lia. }
        split; [exact MIt|].
        split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ HEAP MUF WMF HWL CEIL); unfold GLOBALS_TOP; lia|].
        split; [reflexivity|]. split; [reflexivity|].
        split. { intros r' a' HA'. destruct r' as [| | | | |j]; cbn [ref_at] in HA' |- *; try exact HA'.
                 destruct HA' as (p0 & H0 & E0 & I0 & R0). exists p0, H0. split; [|split; [exact I0| exact R0]].
                 cbn. fold c in E0. rewrite Eh in E0. exact E0. }
        split; [|intros q0 A0 n0 Hq0; exact Hq0].
        exists (H + 24 * Z.of_nat i). split; [|reflexivity].
        cbn [ref_at]. exists ph, H. split; [reflexivity|]. split; [exact HH|]. split; [exact IR| reflexivity]. }
      step. if_cases KU; zify_cond KU; rewrite ?unsigned_lit in KU by lia.
      + (* [comment removed for export] *)
        step. unfold MallocRep.wz at 1. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          eapply evt_eq; [| eapply (CONT _ _ mx); [exact CX| exact FR| exact ST| exact MU| exact WM| exact MI| exact ERR] ] end.
        reflexivity.
      + (* [comment removed for export] *)
        assert (ECu : Cu = H).
        { assert (E0 : i <> 0%nat) by lia. pose proof (CK6 E0) as EC.
          unfold pool_mem in PM. rewrite Eh in PM. destruct PM as [_ [[E1 _]|[_ E2]]]; [congruence| exact E2]. }
        subst Cu.
        step.
        rewrite (unsigned_lit (Z.of_nat i)) by lia.
        replace (Z.land (Z.of_nat i) 15) with (Z.of_nat i)
          by (change 15 with (Z.ones 4); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
        step. if_cases KA; zify_cond KA; rewrite ?unsigned_lit in KA by lia; [|exfalso; lia]. clear KA.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          eapply evt_eq; [| eapply (CONT _ _ mx); [exact CX| exact FR| exact ST| exact MU| exact WM| exact MI| exact ERR] ] end.
        reflexivity.
    - (* [comment removed for export] *)
      replace (cx_pused c =? cx_psize c)%nat with true by (symmetry; apply Nat.eqb_eq; lia).
      destruct (cx_psize c =? 0)%nat eqn:EPZ; cbn [negb tbind fst snd].
      2:{ ihere. to_implM. cbn [embed interp]. apply implM_interp_unr. }
      apply Nat.eqb_eq in EPZ.
      assert (EV0 : cx_vals c = []) by (apply length_zero_iff_nil; lia).
      pose proof (cx_vals_head _ _ _ _ _ _ _ LSC EV0) as Eh. fold c in Eh.
      rewrite Eh in HH. subst H.
      unfold pool_mem in PM. rewrite Eh in PM. destruct PM as [-> ECUR0].
      assert (EU0 : cx_used c = 0%nat) by lia.
      assert (EP0 : cx_pused c = 0%nat) by lia.
      step. unfold MallocRep.wz at 1. rewrite (sx32_small 0) by lia.
      do 5 step.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72)]).
      { constructor; [left; cbn; lia|]. constructor; [right; exists (ad_pc AD, ad_ctx AD, 72); cbn; auto with zarith| constructor]. }
      assert (HEAP1 : RHEAP s (OW ++ LB) m1) by (exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL)).
      assert (AUX1 : rauxv_ok m1 B) by (apply (seg_auxv _ _ _ _ _ _ _ _ _ HEAP AUX MU WM HWL SPB); unfold GLOBALS_TOP; lia).
      assert (LXP1 : lx_pres LB (bv_unsigned sp) LIBW_bn m m1) by (apply (seg_lx_pres _ _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL); unfold GLOBALS_TOP; lia).
      assert (LSC1 : lib_state_hc true [] ls m1 OW AD EA).
      { eapply (lib_state_frame s LB); [exact HEAP| exact LSC| exact MU| exact WM|].
        constructor; [apply w_stack; cbn; lia|].
        constructor; [apply w_cx; [reflexivity| intros x Hx; left; cbn in Hx; lia]| constructor]. }
      assert (STK1 : stack_rep m1 OW IX c).
      { eapply (stack_rep_munch s OW LB m m1 ls AD EA IX); [exact HEAP| exact IDS| exact ADB| exact STK| exact MU| exact WM|].
        constructor; [left; cbn; lia|]. constructor; [right; left; cbn; lia| constructor]. }
      assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
      ihere. to_implM. cbn [embed]. unfold POOL_ITEM_BYTES.
      eapply (CRYPTO_malloc_walk HM) with (B := B) (lo := lo) (errv := errv) (n := 400);
        [exact HEAP1 | exact AUX1 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
        | rewrite ESP; unfold CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia
        | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity
        | exact (proj1 LSC1) | reflexivity | lia | reflexivity | ].
      intros pn st1 ms1 PO. unfold calloc_post in PO. rewrite ?ESP in PO.
      destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & An & errv2
                      & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & BR & HEAP3 & (junkA & BLK)).
      replace (ret_pc (Z_to_bv 64 1135872)) with (Z_to_bv 64 1135872) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (agree_of_heap_pres _ _ _ _ HP) as AGP.
      apply (rw_cells_agree _ _ _ _ _ AGP) in FR; [| intros x Hx; left; cbn in Hx; lia].
      apply (rw_cells_agree _ _ _ _ _ AGP) in CX; [| intros x Hx; right; right; exists (ad_pc AD, ad_ctx AD, 72); split; [apply in_or_app; left; exact BC| cbn in Hx |- *; lia]].
      assert (LSC3 : lib_state_hc true [] ls m3 OW AD EA).
      { eapply lib_state_h_heap_pres; [exact LSC1| exact HP|]. intros b0 Hb0. apply in_or_app. left. exact Hb0. }
      assert (STK3 : stack_rep m3 OW IX c).
      { eapply (stack_rep_heap_pres OW); [| exact STK1| exact HP]. intros b0 Hb0. apply in_or_app. left. exact Hb0. }
      pose proof BR as (BA0 & BA16 & _ & BAC & BAI).
      assert (ND3 : List.NoDup (map blk_id ((pn, An, 400) :: OW ++ LB))) by (eapply LH_nodup; exact HEAP3).
      assert (FRESH : ~ In pn (map blk_id (OW ++ LB))) by (cbn [map] in ND3; apply NoDup_cons_iff in ND3; exact (proj1 ND3)).
      assert (FRESHA : ~ In pn (all_ids ls AD EA)).
      { intros Hin. apply FRESH. rewrite map_app. apply in_or_app. left. eapply all_ids_owned; eauto. }
      assert (NEWSEP : forall q A n, In (q, A, n) OW -> An + 400 <= A \/ A + n <= An).
      { intros q A n Hq. assert (NE : pn <> q) by (intros ->; apply FRESH; rewrite map_app; apply in_or_app; left; apply (in_map blk_id) in Hq; exact Hq).
        exact (LH_disjoint _ _ _ (pn, An, 400) (q, A, n) HEAP3 ltac:(left; reflexivity) ltac:(right; apply in_or_app; left; exact Hq) NE). }
      pose proof (NEWSEP _ _ _ BC) as SEPc.
      set (OW1 := (pn, An, 400) :: OW).
      assert (LSC3' : lib_state_hc true [] ls m3 OW1 AD EA) by (eapply lib_state_h_ow; [exact LSC3|]; intros q A n _ Hq; right; exact Hq).
      assert (LXP3 : lx_pres LB (bv_unsigned sp) LIBW_bn m m3).
      { eapply lx_pres_trans; [exact LXP1|]. apply lx_pres_of_heap_pres.
        eapply rheap_pres_weaken; [exact HP| lia|]. intros b0 Hb0. apply in_or_app. right. exact Hb0. }
      unfold LX_ERRNO, RATP in ERR3. change (3353240 - 164) with 3353076 in ERR3.
      (* [comment removed for export] *)
      assert (SPLIT : rw_cells usegs m3 An ([CB 384 (firstn 384 junkA)] ++ [CB 16 (skipn 384 junkA)])).
      { pose proof BLK as [[[LJ _] _] _]. cbn in LJ.
        eapply bk_rw_cells_recast; [exact BLK| | |].
        - cbn. rewrite length_firstn, length_skipn. lia.
        - cbn. rewrite !app_nil_r. apply firstn_skipn.
        - cbn. lia. }
      apply bk_rw_cells_app in SPLIT. destruct SPLIT as [B1 B2]. cbn [cells_size csize Nat.add] in B2. change (Z.of_nat 384) with 384 in B2. clear BLK.
      cbn [tbind fst snd embed interp]. apply implM_ret.
      pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72); (An, An + 400)]%Z m3) as MU3.
      pose proof (wmono_refl usegs m3) as WM3.
      clear MU WM LSC LSC1 LSC3 HEAP1 AUX1.
      unfold MallocRep.wz in *.
      assert (BA8 : An mod 8 = 0) by (clear - BA16; Z.div_mod_to_equations; lia).
      step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
      step. step. rewrite (land7_wrap _ BA8).
      chk ltac:(fun C => clear - C; lia).
      step. step. step. step.
      eapply evt_cut.
      { eapply (get_init_loop 15) with (lo := lo) (P := An) (junk := firstn 384 junkA); rewrite ?ESP;
          [exact B1 | exact ST3 | lia | exact MI3 | lia | lia | lia | lia]. }
      rewrite ?ESP. post_call usegs m3.
      rewrite ESP in PC. change (24 * Z.of_nat 16) with 384. change (24 * 16)%nat with 384%nat in POST.
      assert (SPLZ : rw_cells usegs x15 An (bn_cells 0 (bn_nil 0) ++ [CB 360 (repeat (Z_to_bv 8 0) 360)])).
      { eapply bk_rw_cells_recast; [exact POST| | |].
        - cbn [bn_cells app cells_wf cell_wf]. rewrite repeat_length. tauto.
        - vm_compute. reflexivity.
        - reflexivity. }
      apply bk_rw_cells_app in SPLZ. destruct SPLZ as [BN0 ZR]. cbn [bn_cells cells_size csize Nat.add] in ZR. change (Z.of_nat 24) with 24 in ZR.
      unfold bn_cells in BN0. clear POST.
      step. step. step. step.
      step. if_true.
      step. step. step.
      step. rewrite (sx32_small (Z.of_nat (cx_psize c))) by lia.
      step. rewrite (sx32_small (Z.of_nat (cx_pused c))) by lia.
      step. step. step. step.

      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      eapply evt_cut.
      { eapply (get_tail) with (lo := lo) (CTX := ad_ctx AD) (A := An) (D := 0) (b := bn_nil 0) (used := Z.of_nat (cx_used c));
          [exact BN0 | split; [clear - BA0; lia| exact BA8] | cbn; lia | exact CX | lia | exact FR | exact PC | lia | eassumption | lia | lia | lia | lia ]. }
      intros ms' PO. unfold get_tail_post in PO.
      destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & mF & -> & MUt & WMt & MIt & STt & BNt & CXt).
      apply evt_done.
      set (c2 := mkCtx (Some pn) (Some pn) (repeat (bn_nil 0) 16) 1 16 (cx_indexes c) (cx_frames c) (cx_ssize c) (S (cx_used c)) 0 false).
      lazymatch goal with |- context [(RPool 0, ?lsM)] => change lsM with (set_ctx c2 ls) end.
      set (WF := [(bv_unsigned sp + -80, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72); (An, An + 400)]%Z).
      assert (MUF : munch WF m3 mF).
      { eapply munch_trans; [exact MU3|]. eapply munch_weaken; [|exact MUt].
        intros xx Hx. subst WF. cbn [outside] in *. clear - Hx. intuition lia. }
      assert (WMF : wmono usegs m3 mF) by (eapply wmono_trans; eassumption).
      assert (HinN : In (pn, An, 400) OW1) by (left; reflexivity).
      assert (BC1 : In (ad_pc AD, ad_ctx AD, 72) OW1) by (right; exact BC).
      assert (ND1 : List.NoDup (map blk_id OW1)) by (eapply (RH_nodup_l st1 OW1 LB m3); exact HEAP3).
      assert (HWL3 : Forall (w_lib OW1 lo (bv_unsigned sp)) WF).
      { subst WF. constructor; [left; cbn; lia|]. constructor; [right; exists (ad_pc AD, ad_ctx AD, 72); cbn; auto with zarith|].
        constructor; [right; exists (pn, An, 400); cbn; auto with zarith| constructor]. }
      assert (LSF : lib_state (set_ctx c2 ls) mF OW1 AD EA).
      { unfold lib_state. eapply (lib_state_cx_close_newpool [] ls mF OW1 AD EA c2 pn An An IX); [| exact Eh| reflexivity| reflexivity| exact HinN| | | | | |].
        - eapply (lib_state_frame st1 LB); [exact HEAP3| exact LSC3'| exact MUF| exact WMF|]. subst WF.
          constructor; [apply w_stack; cbn; lia|].
          constructor; [apply w_cx; [reflexivity| intros x' Hx; left; cbn in Hx; lia]|].
          constructor; [|constructor].
          eapply (w_foreign OW1 LB ls AD EA true [] _ pn An 400); [left; reflexivity| exact FRESHA| cbn; lia| cbn; lia].
        - change (repeat (bn_nil 0 : bignum bptr) 16) with (bn_nil 0 :: repeat (bn_nil 0 : bignum bptr) 15). cbn [bns_gen]. split.
          + unfold repR, bn_rep. exists 0. split; [exact BNt|]. unfold bn_arr. cbn [bn_nil bn_d bn_buf]. auto.
          + apply (bns_gen_zeros 15). change (24 * 15)%nat with 360%nat.
            eapply rw_cells_transport; [exact ZR| exact MUt| exact WMt|]. cbn [disjoint_from cells_size csize Nat.add]. clear - SEPc BAC CEIL LO SPR. lia.
        - unfold ctx_cells, c2. cbn [cx_pused cx_psize cx_frames cx_ssize cx_used cx_err_stack cx_too_many Z.b2z]. unfold MallocRep.wz.
          rewrite EP0, EPZ in CXt. rewrite (Nat2Z.inj_succ (cx_used c)). unfold Z.succ. exact CXt.
        - change (stack_rep mF OW1 IX (ls_ctx ls)). fold c.
          eapply (stack_rep_munch st1 OW1 LB m3 mF ls AD EA IX); [exact HEAP3| exact IDS| | | exact MUF| exact WMF|].
          + destruct ADB as (A1 & A2 & A3 & A4 & A5 & A6). unfold ad_blocks. repeat split; right; assumption.
          + eapply stack_rep_ow; [|exact STK3]. intros b0 Hb0. right. exact Hb0.
          + subst WF. constructor; [left; cbn; lia|]. constructor; [right; left; cbn; lia|]. constructor; [|constructor].
            right; right. exists pn, An, 400. split; [left; reflexivity|]. cbn [fst snd]. split; [lia|]. split; [lia|].
            fold c. intros E. apply FRESHA. unfold all_ids. apply in_or_app; right; apply in_or_app; right. apply idx_in_m. symmetry. exact E.
        - unfold pool_mem, c2. cbn [cx_head cx_current]. split; [|right; split; reflexivity].
          eapply rw_cells_transport; [exact B2| exact MUt| exact WMt|]. cbn [disjoint_from cells_size csize Nat.add]. clear - SEPc BAC CEIL LO SPR. lia.
        - unfold ctx_okm, c2. cbn [cx_pused cx_used cx_psize cx_vals cx_frames cx_ssize cx_current cx_head cx_err_stack].
          split; [lia|]. split; [lia|]. split; [rewrite repeat_length; reflexivity|].
          split; [eapply nondecr_last_incr; [exact CK4| lia]|]. split; [exact CK5|]. split; [reflexivity| reflexivity].
        - eapply (ids_ok_set_ctx_new_head ls AD EA c2 pn); [exact IDS| reflexivity| exact Eh| exact EV0| reflexivity| reflexivity| exact FRESHA]. }
      unfold bn_post. do 15 eexists. exists mF, OW1, errv2. split; [reflexivity|]. cbn [fst snd].
      split; [exact (seg_heap st1 OW1 LB m3 mF _ lo _ HEAP3 MUF WMF HWL3 CEIL)|]. split; [exact LSF|].
      split; [apply (seg_auxv st1 OW1 LB m3 mF _ lo _ B HEAP3 AUX3 MUF WMF HWL3 SPB); unfold GLOBALS_TOP; lia|]. split; [exact STt|].
      split. { unfold LX_ERRNO, RATP. change (3353240 - 164) with 3353076.
               eapply rw_cells_transport; [exact ERR3| exact MUt| exact WMt|]. cbn [disjoint_from cells_size csize Nat.add].
               clear - BAI CAI GLO LO SPR. lia. }
      split; [exact MIt|].
      split. { eapply lx_pres_trans; [exact LXP3|]. apply (seg_lx_pres st1 OW1 LB m3 mF _ lo _ _ HEAP3 MUF WMF HWL3 CEIL); unfold GLOBALS_TOP; lia. }
      split; [exact FA|]. split; [exact SO|].
      split. { intros r' a' HA'. destruct r' as [| | | | |j]; cbn [ref_at] in HA' |- *; try exact HA'.
               destruct HA' as (p0 & H0 & E0 & _). fold c in E0. congruence. }
      split; [|intros q0 A0 n0 Hq0; right; exact Hq0].
      exists An. split; [|reflexivity].
      cbn [ref_at]. exists pn, An. split; [reflexivity|]. split; [exact HinN|]. split; [lia| lia].
  Qed.
End Proofs.
End WithCeiling0.
