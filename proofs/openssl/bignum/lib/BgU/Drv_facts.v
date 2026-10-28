(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr.
From OssFuzzTheorems.openssl.bignum.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc MallocCtrl KInv Monad Prog
  MI_Tree MI_Inv MI_Kit MI_Geom MI_WSlot MI_Sim MI_Contracts.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks MallocTree MallocHINV Malloc_iface MallocFacts_inv.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation bgusegs := ImageBg.bgusegs.
Notation mem := (word -> option byte).

From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_nia__].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Fixpoint tleaf {R} (t : itree node R) (r : R) : Prop :=
  match t with
  | ITree.Ret r' => r' = r
  | ITree.Vis n k => exists rsp, tleaf (k rsp) r
  end.

Definition mleaf {A} (c : M PState A) (s : PState) (a : A) (s' : PState) : Prop := tleaf (c s) (Ok (a, s')).

Lemma impl_leaves : forall {R} (t : itree node R) (Q : R -> machine_state -> Prop) ms,
  impl bgusegs (at_node bgusegs) t Q ms -> impl bgusegs (at_node bgusegs) t (fun r ms' => Q r ms' /\ tleaf t r) ms.
Proof.
  induction t as [r|n k IH]; intros Q ms H; cbn in *.
  - eapply evt_mono; [exact H|]. intros ms' HQ. split; [exact HQ| reflexivity].
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp.
    eapply impl_mono; [apply IH; apply Hk|]. intros r ms' [HQ HL]. split; [exact HQ|]. exists rsp. exact HL.
Qed.

Lemma implM_leaves : forall {A} (c : M PState A) s (Q : A -> PState -> machine_state -> Prop) ms,
  implM bgusegs c s Q ms -> implM bgusegs c s (fun a s' ms' => Q a s' ms' /\ mleaf c s a s') ms.
Proof.
  intros A c s Q ms H. unfold implM, mleaf in *. eapply impl_mono; [apply impl_leaves; exact H|].
  intros [|[a s']] ms' [HQ HL]; cbn in *; [exact HQ|]. split; assumption.
Qed.

Definition rfree_keeps_ptr_stmt : Prop :=
  forall (s s' : PState) (LB : list block) (m : mem) (p : bptr) (A n : Z) (b : block),
    RHEAP s LB m -> In (p, A, n) LB -> mleaf (raw_free p) s tt s' ->
    In b (lb_remove p LB) -> ptr_addr s' (blk_id b) = ptr_addr s (blk_id b).

Lemma tleaf_bind {A B} (t : itree node A) (f : A -> itree node B) r :
  tleaf (ITree.bind _ t f) r -> exists x, tleaf t x /\ tleaf (f x) r.
Proof.
  induction t as [a|n k IH]; cbn; intros H.
  - exists a. split; [reflexivity| exact H].
  - destruct H as [rsp H]. destruct (IH rsp H) as (x & Hx & Hf). exists x. split; [exists rsp; exact Hx| exact Hf].
Qed.

Lemma tleaf_ebind {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) r :
  tleaf (ebind t f) (Ok r) -> exists a, tleaf t (Ok a) /\ tleaf (f a) (Ok r).
Proof.
  unfold ebind. intros H. destruct (tleaf_bind _ _ _ H) as (x & Hx & Hf).
  destruct x as [|a]; [cbn in Hf; discriminate Hf|]. exists a. split; assumption.
Qed.

Lemma mleaf_bind {A B} (c : Monad.M PState A) (f : A -> Monad.M PState B) s b s' :
  mleaf (mbind c f) s b s' -> exists a s1, mleaf c s a s1 /\ mleaf (f a) s1 b s'.
Proof.
  unfold mleaf, mbind. intros H. destruct (tleaf_ebind _ _ _ H) as ([a s1] & H1 & H2). exists a, s1. split; assumption.
Qed.

Lemma mleaf_ret {A} (a : A) s b s' : mleaf (mret a) s b s' -> b = a /\ s' = s.
Proof. unfold mleaf, mret. cbn. intros H. inversion H. auto. Qed.

Lemma mleaf_msys {A} n (dec : resp -> option A) s a s' : mleaf (msys n dec) s a s' -> s' = s.
Proof.
  unfold mleaf, msys, enode. cbn. intros [rsp H]. destruct (dec rsp); cbn in H; [| discriminate H]. inversion H. reflexivity.
Qed.

Lemma ev_step_leaf e s z s1 : mleaf (ev_step e) s z s1 ->
  ps_m s1 = ps_m s /\ match e with EPeek _ _ _ | EUndef _ => False | _ => True end.
Proof.
  destruct e as [rq|a len prot flags|a len|a len prot|p c h|w]; cbn [ev_step]; intros H.
  - destruct (rq =? 0).
    + apply mleaf_bind in H as (r & s2 & H1 & H2). apply mleaf_msys in H1. subst s2.
      apply mleaf_bind in H2 as (u & s3 & H2 & H3). unfold mleaf, mupd in H2. cbn in H2. inversion H2. subst.
      apply mleaf_ret in H3 as [_ ->]. split; [reflexivity| exact I].
    + apply mleaf_bind in H as (s0 & s2 & H1 & H2). unfold mleaf, mget in H1. cbn in H1. inversion H1. subst.
      apply mleaf_bind in H2 as (aa & s3 & H2 & H3). apply mleaf_msys in H2. subst s3.
      destruct aa.
      * apply mleaf_bind in H3 as (u & s4 & H3 & H4). unfold mleaf, mupd in H3. cbn in H3. inversion H3. subst.
        apply mleaf_ret in H4 as [_ ->]. split; [reflexivity| exact I].
      * apply mleaf_ret in H3 as [_ ->]. split; [reflexivity| exact I].
  - destruct (negb (Z.land flags MAP_FIXED_Z =? 0)); [| destruct (prot =? 0)].
    all: apply mleaf_bind in H as (aa & s2 & H1 & H2); apply mleaf_msys in H1; subst s2; apply mleaf_ret in H2 as [_ ->]; split; [reflexivity| exact I].
  - apply mleaf_bind in H as (aa & s2 & H1 & H2); apply mleaf_msys in H1; subst s2; apply mleaf_ret in H2 as [_ ->]; split; [reflexivity| exact I].
  - apply mleaf_bind in H as (aa & s2 & H1 & H2); apply mleaf_msys in H1; subst s2; apply mleaf_ret in H2 as [_ ->]; split; [reflexivity| exact I].
  - unfold mleaf, munr in H. cbn in H. discriminate H.
  - unfold mleaf, munr in H. cbn in H. discriminate H.
Qed.

Lemma membed_leaf {R} (t : stree ev Z R) : forall s r s',
  mleaf (membed t) s r s' -> ps_m s' = ps_m s /\ exists ans, follow t ans = Some r.
Proof.
  induction t as [r0|e k IH]; intros s r s' H; cbn [membed] in H.
  - apply mleaf_ret in H as [-> ->]. split; [reflexivity|]. exists []. reflexivity.
  - apply mleaf_bind in H as (z & s1 & H1 & H2). destruct (ev_step_leaf e s z s1 H1) as [E1 NE].
    destruct (IH z s1 r s' H2) as [E2 [ans Hf]]. split; [rewrite E2; exact E1|].
    exists (z :: ans). destruct e; try exact Hf; destruct NE.
Qed.

Lemma raw_free_leaf p s s' : mleaf (raw_free p) s tt s' ->
  exists ans, follow (cfree (ps_m s) (Some (fst p))) ans = Some (ps_m s').
Proof.
  unfold raw_free. intros H.
  apply mleaf_bind in H as (s0 & s1 & H1 & H2). unfold mleaf, mget in H1. cbn in H1. inversion H1. subst s0 s1.
  apply mleaf_bind in H2 as (cs' & s2 & H2 & H3). destruct (membed_leaf _ _ _ _ H2) as [E [ans Hf]].
  unfold mleaf, mupd in H3. cbn in H3. inversion H3. subst s'. exists ans. cbn. exact Hf.
Qed.

Lemma conc_strip_eq st q : conc (strip st) q = conc st q.
Proof. reflexivity. Qed.

Theorem rfree_keeps_ptr_proof : rfree_keeps_ptr_stmt.
Proof.
  intros s s' LB m p A n b (st & LB0 & PERM & STRIP & MREP & [_ AR]) Hp FL Hb.
  destruct (areach_inv _ st LB0 AR) as (L & LS & BL & INV & LIVE & _ & _ & CR).

  assert (Hp0 : In (p, A, n) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hp]).
  unfold lb_remove in Hb. apply list_elem_of_In in Hb. apply list_elem_of_filter in Hb as [NEQ Hb]. apply list_elem_of_In in Hb.
  assert (Hb0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb]).
  destruct (Forall2_In_l _ _ _ _ CR Hp0) as (k & Hk & (C1 & C2 & C3)). cbn [blk_slot blk_size blk_addr fst snd] in C1, C2, C3.
  destruct k as [[c off] nn]. cbn [bslot boff bsize fst snd] in C1, C2, C3, Hk. subst nn.
  destruct (Forall2_In_l _ _ _ _ CR Hb0) as (kk & Hkk & (D1 & D2 & D3)).

  assert (NE : bslot kk <> c).
  { intros E.
    assert (EM : map blk_slot LB0 = map bslot BL) by (apply (Forall2_map_eq _ _ _ _ _ CR); intros ? ? (X1 & _); exact X1).
    pose proof (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))) as ND. rewrite <- EM in ND. apply NoDup_ListNoDup in ND.
    assert (SS : blk_slot b = blk_slot (p, A, n)) by (rewrite D1, E, C1; reflexivity).
    assert (EQ : forall l (x y : block), List.NoDup (map blk_slot l) -> In x l -> In y l -> blk_slot x = blk_slot y -> x = y).
    { clear. induction l as [|z l IH]; intros x y ND Hx Hy Es; [destruct Hx|]. cbn in ND. inversion ND; subst.
      destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
      - reflexivity.
      - exfalso. apply H1. rewrite Es. apply in_map. exact Hy.
      - exfalso. apply H1. rewrite <- Es. apply in_map. exact Hx.
      - exact (IH x y ltac:(assumption) Hx Hy Es). }
    pose proof (EQ LB0 b (p, A, n) ND Hb0 Hp0 SS) as Eb. subst b.
    unfold bptr_eqb in NEQ. cbn [blk_id fst snd] in NEQ. rewrite aptr_eqb_refl, Z.eqb_refl in NEQ. exact NEQ. }

  destruct (raw_free_leaf p s s' FL) as [ans Hf]. rewrite <- STRIP in Hf. change (fst p) with (blk_slot (p, A, n)) in Hf. rewrite C1 in Hf.
  pose proof (strel_follow (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk)) ans) as SF.
  rewrite Hf in SF.
  destruct (follow (prun pans0 pupd0 tt (free st (Some (aadd c (UNIT * off))))) ans) as [[o1 st1]|] eqn:FF; [| destruct SF].
  unfold FREL in SF. cbn [snd] in SF.
  destruct (free_leaf_facts pans0 pupd0 st L BL LS c off n tt ans o1 st1 INV Hk FF) as [SUB _].
  destruct (free_sim pans0 pupd0 pans0_range st L BL LS c off n tt ans o1 st1 INV Hk FF) as (_ & _ & _ & LS1 & INV1).

  assert (Hk2 : In kk (bl_remove c BL)).
  { rewrite (bl_remove_filter c BL (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))))).
    apply list_elem_of_In. apply list_elem_of_filter. split; [| apply list_elem_of_In; exact Hkk].
    rewrite (MI_Kit.aptr_eqb_neq _ _ NE). exact I. }
  destruct (blk_region _ _ _ _ _ kk INV1 Hk2) as (r1 & Hr1 & _).
  unfold ptr_addr. change (fst (blk_id b)) with (blk_slot b). rewrite D1, <- SF, <- STRIP, !conc_strip_eq.
  rewrite (conc_same st st1 (bslot kk)); [reflexivity|]. exists r1. split; [exact (SUB _ _ Hr1)| exact Hr1].
Qed.

Lemma le4_of_bytes : forall b0 b1 b2 b3 : byte, exists w : word, le4 w = [b0; b1; b2; b3].
Proof.
  intros b0 b1 b2 b3.
  pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
  pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
  unfold bv_modulus in R0, R1, R2, R3. cbn in R0, R1, R2, R3.
  set (v := bv_unsigned b0 + 2^8 * bv_unsigned b1 + 2^16 * bv_unsigned b2 + 2^24 * bv_unsigned b3).
  exists (Z_to_bv 64 v). unfold le4. rewrite Z_to_bv_unsigned.
  assert (HV : 0 <= v < 2^32) by (subst v; lia).
  replace (bv_wrap 64 v) with v by (unfold bv_wrap, bv_modulus; rewrite Z.mod_small; [reflexivity|]; cbn; lia).
  cbn [Z_to_le_bytes]. rewrite !Z.shiftr_shiftr by lia. cbn [Z.add].
  rewrite !Z.shiftr_div_pow2 by lia.
  assert (E0 : Z_to_bv 8 v = b0).
  { apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow_pos Pos.mul Z.of_N]. subst v. Z.div_mod_to_equations. nia. }
  assert (E1 : Z_to_bv 8 (v / 2^8) = b1).
  { apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow_pos Pos.mul Z.of_N]. subst v. Z.div_mod_to_equations. nia. }
  assert (E2 : Z_to_bv 8 (v / 2^16) = b2).
  { apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow_pos Pos.mul Z.of_N]. subst v. Z.div_mod_to_equations. nia. }
  assert (E3 : Z_to_bv 8 (v / 2^24) = b3).
  { apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow_pos Pos.mul Z.of_N]. subst v. Z.div_mod_to_equations. nia. }
  rewrite E0, E1, E2, E3. reflexivity.
Qed.

Lemma libc_head_byte : forall (m : mem) (a : Z), 0x351228 <= a < 0x351230 ->
  exists b : byte, mrd bgusegs m (wa a) = Some b /\ wview bgusegs m (wa a) <> None.
Proof.
  intros m a Ha.
  assert (IMG : exists b0, seg_rom bgusegs (wa a) = Some b0 /\ wview bgusegs (fun _ => None) (wa a) <> None).
  { assert (E : a = 0x351228 \/ a = 0x351229 \/ a = 0x35122a \/ a = 0x35122b \/ a = 0x35122c \/ a = 0x35122d \/ a = 0x35122e \/ a = 0x35122f) by lia.
    destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; (eexists; split; [vm_compute; reflexivity| vm_compute; discriminate]). }
  destruct IMG as (b0 & SR & WV).
  destruct (m (wa a)) as [b|] eqn:E.
  - exists b. split; [unfold mrd; rewrite E; reflexivity|]. unfold wview. rewrite E. discriminate.
  - exists b0. split; [unfold mrd; rewrite E; exact SR|]. unfold wview in *. rewrite E. exact WV.
Qed.

Lemma RHEAP_libc_head : forall s LB m, RHEAP s LB m ->
  exists (cdt thr sec : byte) (tm1 : word),
    rw_cells bgusegs m 0x351228 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1].
Proof.
  intros s LB m (st & LB0 & _ & _ & MREP & _).
  destruct MREP as (_ & _ & (_ & NL & _) & _).
  destruct (libc_head_byte m 0x351228 ltac:(lia)) as (b0 & R0 & W0).
  destruct (libc_head_byte m 0x351229 ltac:(lia)) as (b1 & R1 & W1).
  destruct (libc_head_byte m 0x35122a ltac:(lia)) as (b2 & R2 & W2).
  destruct (libc_head_byte m 0x35122c ltac:(lia)) as (b4 & R4 & W4).
  destruct (libc_head_byte m 0x35122d ltac:(lia)) as (b5 & R5 & W5).
  destruct (libc_head_byte m 0x35122e ltac:(lia)) as (b6 & R6 & W6).
  destruct (libc_head_byte m 0x35122f ltac:(lia)) as (b7 & R7 & W7).
  destruct (le4_of_bytes b4 b5 b6 b7) as [tm1 Htm].
  destruct NL as [[_ NLB] NLW]. unfold RNEED_LOCKS in NLB, NLW.
  pose proof (proj2 (proj2 NLB) 0%nat ltac:(cbn; lia)) as R3. cbn [cells_bytes cbytes app nth_error b8 MallocRep.b8] in R3.
  pose proof (proj2 (proj2 NLW) 0 ltac:(cbn; lia)) as W3.
  exists b0, b1, b2, tm1. split; [split|].
  - cbn. repeat split; exact I.
  - cbn [cells_bytes cbytes app]. rewrite Htm. cbn [app]. split; [lia|]. split; [cbn; lia|].
    intros i Hi. cbn [length] in Hi.
    destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ]; try lia.
    + exact R0. + exact R1. + exact R2.
    + replace (0x351228 + 3) with (0x35122b + Z.of_nat 0) by lia. exact R3.
    + exact R4. + exact R5. + exact R6. + exact R7.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|].
    intros i Hi.
    assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
    destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; cbn [Z.add].
    + exact W0. + exact W1. + exact W2.
    + replace (0x351228 + 3) with (0x35122b + 0) by lia. exact W3.
    + exact W4. + exact W5. + exact W6. + exact W7.
Qed.
End WithCeiling0.
