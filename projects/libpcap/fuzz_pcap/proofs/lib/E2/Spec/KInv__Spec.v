(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaTuning.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc.
From stdpp Require gmap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module KInv.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaTuning.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree Malloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
Inductive brk_phase : Type :=
| BPUntried                 (* [comment removed for export] *)
| BPQueried (cur : Z)       (* [comment removed for export] *)
| BPGuard (cur : Z)         (* [comment removed for export] *)
| BPLive                    (* [comment removed for export] *)
| BPDead.                   (* [comment removed for export] *)

Record mled : Type := mkLed {
  ld_resv : list (Z * Z);          (* [comment removed for export] *)
  ld_groups : list (Z * Z);        (* [comment removed for export] *)
  ld_metas : list (Z * Z * Z);     (* [comment removed for export] *)
  ld_brkreg : option (Z * Z);      (* [comment removed for export] *)
  ld_brk : brk_phase;
  ld_live : list cptr              (* [comment removed for export] *)
}.

Definition led_init (resv : list (Z * Z)) : mled := mkLed resv [] [] None BPUntried [].
Definition set_groups (v : list (Z * Z)) (L : mled) := mkLed (ld_resv L) v (ld_metas L) (ld_brkreg L) (ld_brk L) (ld_live L).
Definition set_metas (v : list (Z * Z * Z)) (L : mled) := mkLed (ld_resv L) (ld_groups L) v (ld_brkreg L) (ld_brk L) (ld_live L).
Definition set_brkreg (v : option (Z * Z)) (L : mled) := mkLed (ld_resv L) (ld_groups L) (ld_metas L) v (ld_brk L) (ld_live L).
Definition set_brkph (v : brk_phase) (L : mled) := mkLed (ld_resv L) (ld_groups L) (ld_metas L) (ld_brkreg L) v (ld_live L).
Definition set_live (v : list cptr) (L : mled) := mkLed (ld_resv L) (ld_groups L) (ld_metas L) (ld_brkreg L) (ld_brk L) v.

(* [comment removed for export] *)
Definition lranges (L : mled) : list (Z * Z) :=
  ld_resv L
  ++ map (fun g => (fst g, round_up_pg (snd g))) (ld_groups L)
  ++ map (fun m => (fst (fst m), round_up_pg (snd (fst m)))) (ld_metas L)
  ++ match ld_brkreg L with Some (b, l) => [(b + PGSZ, round_up_pg l - PGSZ)] | None => [] end.

(* [comment removed for export] *)
Definition lbrk_pages_ok (L : mled) (lo len : Z) : bool :=
  (0 <? lo) && (lo + len <=? alloc_ceiling) && ranges_free (lranges L) lo len.

Definition MAPF : Z := MAP_PRIVATE + MAP_ANON.
Definition MAPFX : Z := MAP_PRIVATE + MAP_ANON + MAP_FIXED.
Definition LEN_MAX : Z := 2^63.   (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint g_remove (a : Z) (l : list (Z * Z)) : list (Z * Z) :=
  match l with
  | [] => []
  | y :: l' => if fst y =? a then l' else y :: g_remove a l'
  end.
Definition bump_meta (a : Z) (m : Z * Z * Z) : Z * Z * Z :=
  let '(b, l, k) := m in if b + (1 + k) * PGSZ =? a then (b, l, k + 1) else m.
Fixpoint ap_remove (c : aptr) (l : list aptr) : list aptr :=
  match l with
  | [] => []
  | y :: l' => if aptr_eqb y c then l' else y :: ap_remove c l'
  end.

(* [comment removed for export] *)
Definition brk_quiet (L : mled) : Prop :=
  match ld_brk L with BPQueried _ | BPGuard _ => False | _ => True end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lranges_wo (L : mled) (a : Z) : list (Z * Z) := lranges (set_groups (g_remove a (ld_groups L)) L).
(* [comment removed for export] *)
Definition mremap_answer_okL (L : mled) (a oldlen newlen r : Z) : bool :=
  is_errno_form r
  || ((r =? a) && ((newlen <=? oldlen)
                   || ((a + newlen <=? alloc_ceiling) && ranges_free (lranges_wo L a) (a + oldlen) (newlen - oldlen))))
  || (negb (r =? a) && (0 <? r) && (r mod PGSZ =? 0) && (r + newlen <=? alloc_ceiling)
      && ranges_free (lranges L) r newlen).
Definition event_pre (L : mled) (e : ev) : Prop :=
  match e with
  | EBrk req =>
      (req = 0 /\ ld_brk L = BPUntried)
      \/ (exists cur, ld_brk L = BPQueried cur /\ req = round_up_pg cur + 2 * PGSZ)
      \/ (exists b l, ld_brk L = BPLive /\ ld_brkreg L = Some (b, l) /\ req = b + l + PGSZ)
  | EMmap a len prot flags =>
      (brk_quiet L /\ a = 0 /\ flags = MAPF /\ (prot = PROT_NONE \/ prot = PROT_RW) /\ 0 < len < LEN_MAX)
      \/ (exists cur, ld_brk L = BPGuard cur /\ a = round_up_pg cur /\ len = PGSZ /\ prot = PROT_NONE /\ flags = MAPFX)
  | EMunmap a len => brk_quiet L /\ exists l, In (a, l) (ld_groups L) /\ (len = l \/ len = round_up_pg l)
        (* [comment removed for export] *)
  | EMprotect a len prot =>
      brk_quiet L /\ len = PGSZ /\ prot = PROT_RW /\
      exists b l k, In (b, l, k) (ld_metas L) /\ a = b + (1 + k) * PGSZ /\ (2 + k) * PGSZ <= round_up_pg l
  | EPeek _ _ _ => False
  | EUndef _ => False
  | EMremap a oldlen newlen =>      (* [comment removed for export] *)
      brk_quiet L /\ (exists l, In (a, l) (ld_groups L) /\ round_up_pg l = oldlen)
      /\ 0 < newlen < LEN_MAX /\ newlen mod PGSZ = 0 /\ oldlen <> newlen
  end.

Definition answer_ok (L : mled) (e : ev) (z : Z) : bool :=
  match e with
  | EBrk req =>
      if req =? 0 then brk0_answer_ok z
      else match ld_brk L with
           | BPQueried cur => brk_answer_ok cur req z && (negb (z =? req) || lbrk_pages_ok L (round_up_pg cur) (2 * PGSZ))
           | _ => match ld_brkreg L with
                  | Some (b, l) => brk_answer_ok (b + l) req z && (negb (z =? req) || lbrk_pages_ok L (b + l) PGSZ)
                  | None => false
                  end
           end
  | EMmap a len prot flags =>
      if Z.land flags MAP_FIXED =? 0 then mmap_answer_ok (lranges L) len z
      else mmap_fixed_answer_ok a z
  | EMunmap _ _ => munmap_answer_ok z
  | EMprotect _ _ _ => mprotect_answer_ok z
  | EMremap a oldlen newlen => mremap_answer_okL L a oldlen newlen z
  | _ => false
  end.

Definition event_post (L : mled) (e : ev) (z : Z) : mled :=
  match e with
  | EBrk req =>
      if req =? 0 then set_brkph (BPQueried z) L
      else if z =? req then
             match ld_brk L with
             | BPQueried cur => set_brkph (BPGuard cur) L
             | _ => match ld_brkreg L with
                    | Some (b, l) => set_brkreg (Some (b, l + PGSZ)) L
                    | None => L
                    end
             end
           else set_brkph BPDead L
  | EMmap a len prot flags =>
      if Z.land flags MAP_FIXED =? 0 then
        if is_err z then L
        else if prot =? PROT_NONE then set_metas ((z, len, 0) :: ld_metas L) L
        else set_groups ((z, len) :: ld_groups L) L
      else set_brkph BPLive (set_brkreg (Some (a, 2 * PGSZ)) L)
  | EMunmap a len => set_groups (g_remove a (ld_groups L)) L
  | EMprotect a len prot =>
      if (z =? 0) || (z =? TWO64 - ENOSYS) then set_metas (map (bump_meta a) (ld_metas L)) L else L
  | EMremap a oldlen newlen =>
      if is_err z then L else set_groups ((z, newlen) :: g_remove a (ld_groups L)) L
  | _ => L
  end.

(* [comment removed for export] *)
Fixpoint ctree_ok {R} (L : mled) (t : stree ev Z R) (Post : mled -> R -> Prop) : Prop :=
  match t with
  | SRet r => Post L r
  | SVis e k => event_pre L e /\ forall z, answer_ok L e z = true -> ctree_ok (event_post L e z) (k z) Post
  end.

(* [comment removed for export] *)
Inductive cpath {R} : mled -> stree ev Z R -> mled -> R -> Prop :=
| cpath_ret L r : cpath L (SRet r) L r
| cpath_vis L e k z L' r :
    answer_ok L e z = true -> cpath (event_post L e z) (k z) L' r -> cpath L (SVis e k) L' r.

(* [comment removed for export] *)
Inductive creach : mstate -> mled -> Prop :=
| creach_init resv : creach (strip (minit 0 resv)) (led_init resv)
| creach_malloc cs L n L' cs' r :
    creach cs L -> 0 <= n -> cpath L (cmalloc cs n) L' (cs', r) ->
    creach cs' (match r with Some c => set_live (c :: ld_live L') L' | None => L' end)
| creach_free cs L c L' cs' :
    creach cs L -> In c (ld_live L) -> cpath L (cfree cs (Some c)) L' cs' ->
    creach cs' (set_live (ap_remove c (ld_live L')) L').

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma in_ap_remove : forall x c l, In x l -> x <> c -> In x (ap_remove c l).
Proof.
  intros x c l. induction l as [|y l IH]; intros Hin Hne; [destruct Hin|].
  cbn. destruct (aptr_eqb y c) eqn:E.
  - assert (y = c).
    { destruct y as [y1 y2], c as [c1 c2]. unfold aptr_eqb in E. cbn in E.
      apply andb_prop in E as [E1 E2]. apply N.eqb_eq in E1. apply Z.eqb_eq in E2. subst. reflexivity. }
    subst y. destruct Hin as [->|Hin]; [congruence| exact Hin].
  - destruct Hin as [->|Hin]; [left; reflexivity| right; apply IH; assumption].
Qed.

#[using="Type"] Lemma cmalloc_overflow : forall cs n, size_overflows n = true -> cmalloc cs n = SRet (strip cs, None).
Proof. intros cs n H. unfold cmalloc, malloc_core. rewrite H. reflexivity. Qed.

End WithCeil.
End KInv.

(* [comment removed for export] *)
Module LB_Tables.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Malloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeil.
Context {CE : CEIL}.
Definition S_ (c : Z) : Z := UNIT * size_class c.
Definition cmax (c : Z) : Z :=
  if c <? 9 then small_cnt c 0 else halve_big 8 (med_cnt (Z.land c 3)) (S_ c).
Definition std_span (c : Z) : Z := cmax c * S_ c + UNIT.
Definition std_nested (c : Z) : bool := std_span c <=? PGSZ / 2.
Definition bighost (c : Z) : Z := if std_nested c then size_to_class (std_span c - IB) else -1.
Definition std_len (c : Z) : Z := round_up_pg (std_span c).

Definition classes : list Z := map Z.of_nat (seq 0 48).

#[using="Type"] Lemma In_classes c : 0 <= c < 48 <-> In c classes.
Proof.
  unfold classes. rewrite in_map_iff. split.
  - intros H. exists (Z.to_nat c). rewrite in_seq. split; lia.
  - intros (n & <- & Hn). rewrite in_seq in Hn. lia.
Qed.

#[using="Type"] Lemma forallb_classes (f : Z -> bool) : forallb f classes = true -> forall c, 0 <= c < 48 -> f c = true.
Proof. intros H c Hc. rewrite forallb_forall in H. apply H. apply In_classes. exact Hc. Qed.
End WithCeil.


Ltac by_table f :=
  let H := fresh in
  assert (H : forallb f classes = true) by (vm_compute; reflexivity);
  intros c Hc; pose proof (forallb_classes f H c Hc) as T; unfold f in T; cbn beta in T;
  repeat (apply andb_prop in T as [T ?]);
  repeat match goal with K : (_ =? _) = true |- _ => apply Z.eqb_eq in K | K : (_ <=? _) = true |- _ => apply Z.leb_le in K | K : (_ <? _) = true |- _ => apply Z.ltb_lt in K end.

(* [comment removed for export] *)
Section WithCeil.
Context {CE : CEIL}.
Definition tab_basic (c : Z) : bool :=
  (16 <=? S_ c) && (S_ c <=? 131056) && (8 <=? cmax c) && (cmax c <=? 32) && (std_span c <=? std_len c) && (std_len c <=? std_span c + 4095)
  && (std_len c <=? 1048576) && (Z.modulo (std_len c) PGSZ =? 0).
#[using="Type"] Lemma tab_basic_ok : forall c, 0 <= c < 48 ->
  16 <= S_ c <= 131056 /\ 8 <= cmax c <= 32 /\ std_span c <= std_len c <= std_span c + 4095 /\ std_len c <= 1048576 /\ std_len c mod PGSZ = 0.
Proof. by_table tab_basic. repeat split; assumption. Qed.

(* [comment removed for export] *)
Definition tab_host (c : Z) : bool :=
  if c <=? 6 then (std_nested c) && ((bighost c =? 15) || (bighost c =? 19) || (bighost c =? 23)) && (std_span c <=? S_ (bighost c)) && (c <? bighost c)
  else negb (std_nested c) && (bighost c =? -1).
#[using="Type"] Lemma tab_host_small : forall c, 0 <= c <= 6 ->
  std_nested c = true /\ (bighost c = 15 \/ bighost c = 19 \/ bighost c = 23) /\ std_span c <= S_ (bighost c) /\ c < bighost c.
Proof.
  intros c Hc. assert (H : forallb tab_host classes = true) by (vm_compute; reflexivity).
  pose proof (forallb_classes tab_host H c ltac:(lia)) as T. unfold tab_host in T.
  replace (c <=? 6) with true in T by (symmetry; apply Z.leb_le; lia).
  apply andb_prop in T as [T T4]. apply andb_prop in T as [T T3]. apply andb_prop in T as [T1 T2].
  apply Z.leb_le in T3. apply Z.ltb_lt in T4.
  split; [exact T1|]. split; [| auto].
  destruct (Z.eqb_spec (bighost c) 15); [auto|]. destruct (Z.eqb_spec (bighost c) 19); [auto|]. destruct (Z.eqb_spec (bighost c) 23); [auto|]. cbn in T2. discriminate.
Qed.
#[using="Type"] Lemma tab_host_big : forall c, 7 <= c < 48 -> std_nested c = false /\ bighost c = -1.
Proof.
  intros c Hc. assert (H : forallb tab_host classes = true) by (vm_compute; reflexivity).
  pose proof (forallb_classes tab_host H c ltac:(lia)) as T. unfold tab_host in T.
  replace (c <=? 6) with false in T by (symmetry; apply Z.leb_gt; lia).
  apply andb_prop in T as [T1 T2]. apply Z.eqb_eq in T2. destruct (std_nested c); [discriminate| auto].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma bighost_inv : forall c, 0 <= c < 48 ->
  (bighost c = 15 <-> c = 0) /\ (bighost c = 19 <-> c = 1 \/ c = 2) /\ (bighost c = 23 <-> 3 <= c <= 6).
Proof.
  intros c Hc.
  assert (H : forallb (fun c => Bool.eqb (bighost c =? 15) (c =? 0) && Bool.eqb (bighost c =? 19) ((c =? 1) || (c =? 2)) && Bool.eqb (bighost c =? 23) ((3 <=? c) && (c <=? 6))) classes = true) by (vm_compute; reflexivity).
  pose proof (forallb_classes _ H c Hc) as T. cbn beta in T.
  apply andb_prop in T as [T T3]. apply andb_prop in T as [T1 T2].
  apply Bool.eqb_prop in T1. apply Bool.eqb_prop in T2. apply Bool.eqb_prop in T3.
  split; [| split].
  - rewrite <- Z.eqb_eq, T1, Z.eqb_eq. tauto.
  - rewrite <- Z.eqb_eq, T2, Bool.orb_true_iff, !Z.eqb_eq. tauto.
  - rewrite <- Z.eqb_eq, T3, Bool.andb_true_iff, Z.leb_le, Z.leb_le. tauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma size_class_pos : forall c, 0 <= c < 48 -> 0 < size_class c.
Proof. intros c Hc. pose proof (tab_basic_ok c Hc). unfold S_, UNIT in *. lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sum_S : fold_right Z.add 0 (map S_ classes) = 795632.
Proof. vm_compute. reflexivity. Qed.

End WithCeil.
End LB_Tables.

(* [comment removed for export] *)
Module MI_Arith.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Malloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma size_classes_length : length size_classes = 48%nat.
Proof. reflexivity. Qed.

#[using="Type"] Lemma size_classes_bounds : Forall (fun x => 1 <= x <= 8191) size_classes.
Proof.
  apply Forall_forall. intros x Hx. unfold size_classes in Hx.
  repeat (destruct Hx as [<-|Hx]; [lia|]). destruct Hx.
Qed.

#[using="Type"] Lemma size_class_bound sc : 0 <= sc < 48 -> 1 <= size_class sc <= 8191.
Proof.
  intros H. unfold size_class.
  apply (Forall_forall (fun x => 1 <= x <= 8191) size_classes); [apply size_classes_bounds|].
  apply nth_In. rewrite size_classes_length. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mask_upto_nonneg k : 0 <= k -> 0 <= mask_upto k.
Proof. intros. unfold mask_upto. assert (0 < 2 ^ (k + 1)) by (apply Z.pow_pos_nonneg; lia). lia. Qed.

#[using="Type"] Lemma testbit_mask_upto k i : 0 <= k -> 0 <= i -> Z.testbit (mask_upto k) i = (i <=? k).
Proof.
  intros Hk Hi. unfold mask_upto. replace (2 ^ (k + 1) - 1) with (Z.pred (2 ^ (k + 1))) by lia.
  rewrite <- Z.ones_equiv. destruct (Z.leb_spec i k).
  - apply Z.ones_spec_low. lia.
  - apply Z.ones_spec_high. lia.
Qed.

#[using="Type"] Lemma testbit_bit i j : 0 <= i -> 0 <= j -> Z.testbit (bit i) j = (i =? j).
Proof.
  intros Hi Hj. unfold bit. destruct (Z.eqb_spec i j) as [<-|NE].
  - apply Z.pow2_bits_true. exact Hi.
  - apply Z.pow2_bits_false. lia.
Qed.

#[using="Type"] Lemma bits_below_bound n a : 0 <= a -> 0 <= n -> (forall i, 0 <= i -> Z.testbit a i = true -> i < n) -> a < 2 ^ n.
Proof.
  intros Ha Hn Hb. destruct (Z.lt_ge_cases a (2 ^ n)) as [|Hge]; [assumption|]. exfalso.
  assert (Hl : n <= Z.log2 a) by (apply Z.log2_le_pow2; lia).
  assert (Ht : Z.testbit a (Z.log2 a) = true) by (apply Z.bit_log2; lia).
  specialize (Hb (Z.log2 a) ltac:(apply Z.log2_nonneg) Ht). lia.
Qed.

#[using="Type"] Lemma testbit_false_above n a i : 0 <= a < 2 ^ n -> n <= i -> Z.testbit a i = false.
Proof.
  intros Ha Hi. destruct (Z.eq_dec a 0) as [->|NZ]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|].
  apply (Z.lt_le_trans _ (2 ^ n)); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

End WithCeil.
End MI_Arith.

(* [comment removed for export] *)
Module MI_Bits.
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Malloc. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma land_opp_odd a : Z.land (2 * a + 1) (- (2 * a + 1)) = 1.
Proof.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
  rewrite Z.bits_opp by lia. replace (Z.pred (2 * a + 1)) with (2 * a) by lia.
  destruct (Z.eq_dec n 0) as [->|].
  - rewrite Z.testbit_odd_0, Z.testbit_even_0. reflexivity.
  - replace n with (Z.succ (n - 1)) by lia. rewrite Z.testbit_odd_succ, Z.testbit_even_succ by lia.
    rewrite andb_negb_r. change 1 with (2^0). rewrite Z.pow2_bits_eqb by lia. symmetry. apply Z.eqb_neq. lia.
Qed.

#[using="Type"] Lemma land_opp_even a : Z.land (2 * a) (- (2 * a)) = 2 * Z.land a (- a).
Proof.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec. replace (- (2 * a)) with (2 * (- a)) by lia.
  destruct (Z.eq_dec n 0) as [->|].
  - rewrite !Z.testbit_even_0. reflexivity.
  - replace n with (Z.succ (n - 1)) by lia. rewrite !Z.testbit_even_succ by lia. symmetry. apply Z.land_spec.
Qed.

#[using="Type"] Lemma lowbit_pow2 : forall m, 0 < m -> exists k, 0 <= k /\ Z.land m (- m) = 2 ^ k /\ 2 ^ k <= m.
Proof.
  intros m Hm.
  pose proof (Wf_Z.Zlt_0_ind (fun x => 0 < x -> exists k, 0 <= k /\ Z.land x (- x) = 2 ^ k /\ 2 ^ k <= x)) as G.
  cbv beta in G. apply G; [|lia|lia]. clear G m Hm.
  intros x IH Hx0 Hx.
  destruct (Z.Even_or_Odd x) as [[a ->]|[a ->]].
  - destruct (IH a ltac:(lia) ltac:(lia)) as (k & Hk & E & L).
    exists (k + 1). rewrite land_opp_even, E, Z.pow_add_r by lia. change (2^1) with 2. lia.
  - exists 0. rewrite land_opp_odd. change (2^0) with 1. lia.
Qed.

#[using="Type"] Lemma land_opp_pow2 k : 0 <= k -> Z.land (2 ^ k) (- 2 ^ k) = 2 ^ k.
Proof.
  intros Hk. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_opp, Z.pow2_bits_eqb by lia.
  rewrite <- Z.ones_equiv, Z.testbit_ones by lia.
  destruct (Z.eqb_spec k n); cbn [andb]; [|reflexivity].
  subst. replace (n <? n) with false by (symmetry; apply Z.ltb_irrefl). destruct (0 <=? n); reflexivity.
Qed.

#[using="Type"] Lemma lowbit_nonzero m : 0 < m -> exists k, 0 <= k /\ lowbit m = 2 ^ k /\ 2 ^ k <= m.
Proof. intros. unfold lowbit. apply lowbit_pow2. assumption. Qed.

#[using="Type"] Lemma ctz32_pow2 k : 0 <= k -> ctz32 (2 ^ k) = k.
Proof. intros. unfold ctz32, lowbit. rewrite land_opp_pow2 by lia. apply Z.log2_pow2. lia. Qed.

#[using="Type"] Lemma lowbit_testbit : forall v k, 0 <= k -> lowbit v = 2 ^ k -> Z.testbit v k = true.
Proof.
  intros v k Hk E. unfold lowbit in E.
  assert (T : Z.testbit (Z.land v (- v)) k = true) by (rewrite E; apply Z.pow2_bits_true; lia).
  rewrite Z.land_spec in T. apply andb_prop in T. tauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sub_bit_ldiff f i : 0 <= f -> 0 <= i -> Z.testbit f i = true -> f - 2 ^ i = Z.ldiff f (2 ^ i).
Proof.
  intros Hf Hi Hb.
  assert (E : f = Z.lor (Z.ldiff f (2 ^ i)) (2 ^ i)).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec, Z.ldiff_spec, Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec i n) as [<-|NE]; [rewrite Hb; reflexivity|]. cbn. rewrite Bool.andb_true_r, Bool.orb_false_r. reflexivity. }
  assert (D : Z.land (Z.ldiff f (2 ^ i)) (2 ^ i) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.ldiff_spec, Z.pow2_bits_eqb, Z.bits_0 by lia.
    destruct (Z.eqb_spec i n); cbn; [rewrite Bool.andb_false_r| rewrite Bool.andb_false_r]; reflexivity. }
  pose proof (Z.add_nocarry_lxor _ _ D) as A. rewrite (Z.lxor_lor _ _ D) in A. rewrite <- E in A. lia.
Qed.

#[using="Type"] Lemma testbit_sub_bit f i j : 0 <= f -> 0 <= i -> 0 <= j -> Z.testbit f i = true ->
  Z.testbit (f - 2 ^ i) j = Z.testbit f j && negb (i =? j).
Proof.
  intros Hf Hi Hj Hb. rewrite (sub_bit_ldiff f i Hf Hi Hb), Z.ldiff_spec, Z.pow2_bits_eqb by lia. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma lowbit_idiom m : 0 < m ->
  exists k, 0 <= k /\ lowbit m = 2 ^ k /\ ctz32 (lowbit m) = k /\ Z.testbit m k = true
    /\ 0 <= m - lowbit m /\ (forall j, 0 <= j -> Z.testbit (m - lowbit m) j = Z.testbit m j && negb (k =? j)).
Proof.
  intros Hm. destruct (lowbit_nonzero m Hm) as (k & Hk & E & L). exists k.
  pose proof (lowbit_testbit m k Hk E) as Tb.
  split; [exact Hk|]. split; [exact E|]. split; [rewrite E; apply ctz32_pow2; exact Hk|]. split; [exact Tb|].
  rewrite E. split; [lia|]. intros j Hj. apply testbit_sub_bit; auto; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mask_below m n : 0 <= m -> 0 <= n -> (forall i, 0 <= i -> Z.testbit m i = true -> i <= n) -> m < 2 ^ (n + 1).
Proof. intros Hm Hn H. apply bits_below_bound; [lia| lia|]. intros i Hi Hb. pose proof (H i Hi Hb). lia. Qed.

End WithCeil.
End MI_Bits.

(* [comment removed for export] *)
Module MallocRe.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree Malloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Open Scope Z_scope.
Local Open Scope stree_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
Definition MREMAP_MAYMOVE : Z := 1.

(* [comment removed for export] *)
Definition live_ranges_wo (st : mstate) (rid : N) : list (Z * Z) :=
  s_reserved st ++ map (fun kr : N * region => region_live_range (snd kr))
                         (filter (fun kr : N * region => negb (N.eqb (fst kr) rid)) (map_to_list (s_regions st))).

(* [comment removed for export] *)
Definition mremap_answer_ok (st : mstate) (rid : N) (base oldlen newlen r : Z) : bool :=
  is_errno_form r
  || ((r =? base) && ((newlen <=? oldlen)
                      || ((base + newlen <=? alloc_ceiling) && ranges_free (live_ranges_wo st rid) (base + oldlen) (newlen - oldlen))))
  || (negb (r =? base) && (0 <? r) && (r mod PGSZ =? 0) && (r + newlen <=? alloc_ceiling)
      && ranges_free (live_ranges st) r newlen).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition resize63 (st : mstate) (rid : N) (needed : Z) (p : aptr) (n idx : Z) : mstate :=
  let e := (rid, needed - IB) in                      (* [comment removed for export] *)
  set_size p e n idx (wr8 e 0 (havoc p (needed - snd p) st)).

(* [comment removed for export] *)
#[using="Type"] Lemma upd_shadow_upd_shadow rid f g st :
  upd_shadow rid f (upd_shadow rid g st) = upd_shadow rid (fun r => f (g r)) st.
Proof.
  unfold upd_shadow, get_shadow, set_shadow; destruct st;
    cbn [Malloc.s_ctx Malloc.s_regions Malloc.s_shadow Malloc.s_next_rid Malloc.s_metas Malloc.s_areas Malloc.s_groups Malloc.s_slots Malloc.s_tick Malloc.s_secret Malloc.s_reserved].
  rewrite lookup_insert_eq, insert_insert_eq. reflexivity.
Qed.

#[using="Type"] Lemma upd_shadow_comm rid1 rid2 f g st : rid1 <> rid2 ->
  upd_shadow rid1 f (upd_shadow rid2 g st) = upd_shadow rid2 g (upd_shadow rid1 f st).
Proof.
  intros NE. unfold upd_shadow, get_shadow, set_shadow; destruct st;
    cbn [Malloc.s_ctx Malloc.s_regions Malloc.s_shadow Malloc.s_next_rid Malloc.s_metas Malloc.s_areas Malloc.s_groups Malloc.s_slots Malloc.s_tick Malloc.s_secret Malloc.s_reserved].
  rewrite !lookup_insert_ne by congruence. rewrite insert_insert_ne by congruence. reflexivity.
Qed.

#[using="Type"] Lemma s_tick_upd_shadow rid f st : s_tick (upd_shadow rid f st) = s_tick st.
Proof. destruct st; reflexivity. Qed.

#[using="Type"] Lemma wr8_havoc_comm q v p n st : wr8 q v (havoc p n st) = havoc p n (wr8 q v st).
Proof.
  unfold havoc. destruct (n <=? 0); [reflexivity|]. unfold wr8. rewrite !s_tick_upd_shadow.
  destruct (N.eq_dec (fst q) (fst p)) as [E|NE].
  - rewrite E, !upd_shadow_upd_shadow. unfold upd_shadow. f_equal. f_equal.
    generalize (get_shadow st (fst p)) as r. intros r. destruct r as [cl hv hp]. cbn [r_cells r_hav r_havp].
    destruct (_ <? _); reflexivity.
  - rewrite upd_shadow_comm by exact NE. reflexivity.
Qed.

#[using="Type"] Lemma set_size_havoc_comm p e n b3 q m st : set_size p e n b3 (havoc q m st) = havoc q m (set_size p e n b3 st).
Proof.
  unfold set_size, wr32. destruct (negb _); destruct (5 <=? _); rewrite ?wr8_havoc_comm; reflexivity.
Qed.

#[using="Type"] Lemma resize63_havoc_last st rid needed p n idx :
  resize63 st rid needed p n idx
  = havoc p (needed - snd p) (set_size p (rid, needed - IB) n idx (wr8 (rid, needed - IB) 0 st)).
Proof. unfold resize63. cbv zeta. rewrite wr8_havoc_comm, set_size_havoc_comm. reflexivity. Qed.

(* [comment removed for export] *)
Definition big_resize (st : mstate) (g : aptr) (rid : N) (newbase needed : Z) (p : aptr) (n idx : Z) : mstate :=
  let st1 := upd_region rid (fun rg => mkRegion (r_kind rg) newbase needed) st in
  let st2 := upd_meta g (m_set_maplen (needed / 4096)) st1 in
  resize63 st2 rid needed p n idx.

Definition realloc (st0 : mstate) (p : optr) (n : Z) : M (mstate * optr) :=
  match p with
  | None => malloc st0 n
  | Some p =>
    if size_overflows n then ret (st0, None) else
    let st := set_tick (N.succ (s_tick st0)) st0 in
    let bail := ret (st0, @None aptr) in
    get_meta st p (fun g _ idx =>
      let mr := get_meta_rec st g in
      match slot_start mr idx with
      | None => SVis (EUndef UBadPtr) (fun _ => bail)
      | Some start =>
        let stride := get_stride mr in
        let e := aadd start (stride - IB) in
        get_nominal_size st p e (fun old_size =>
          let avail := snd e - snd p in
          if (n <=? avail) && (n <? MMAP_THRESHOLD) && (m_sizeclass mr <=? size_to_class n + 1) then
            (* [comment removed for export] *)
            ret (havoc p n (set_size p e n idx st), Some p)
          else
            let fallback (st1 : mstate) : M (mstate * optr) :=
              (* [comment removed for export] *)
              '(st2, q) <-- malloc st1 n ;;
              match q with
              | None => ret (st2, None)
              | Some q => st3 <-- free st2 (Some p) ;; ret (st3, Some q)
              end in
            if (48 <=? m_sizeclass mr) && (MMAP_THRESHOLD <=? n) then
              guard 70 (m_sizeclass mr =? 63) (
                let base := snd p - snd start in
                let needed := round_up_pg (n + base + UNIT + IB) in
                let oldlen := m_maplen mr * 4096 in
                let rid := fst start in
                if oldlen =? needed then
                  ret (resize63 st rid needed p n idx, Some p)      (* [comment removed for export] *)
                else
                  SVis (EMremap (conc st (rid, 0)) oldlen needed) (fun r =>
                    if negb (mremap_answer_ok st rid (conc st (rid, 0)) oldlen needed r) then bad_answer bail
                    else if is_err r then fallback st
                    else ret (big_resize st g rid r needed p n idx, Some p)))
                bail
            else fallback st) bail
      end) bail
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition is_allzero {R} (st : mstate) (p : aptr) (k : bool -> M R) (bail : M R) : M R :=
  get_meta st p (fun g _ _ =>
    let mr := get_meta_rec st g in
    k ((48 <=? m_sizeclass mr) || (get_stride mr <? UNIT * size_class (m_sizeclass mr)))) bail.

Definition SIZE_MAX : Z := 2^64 - 1.

(* [comment removed for export] *)
Definition calloc (st0 : mstate) (m n : Z) : M (mstate * optr) :=
  if negb (n =? 0) && (SIZE_MAX / n <? m) then ret (st0, None)      (* [comment removed for export] *)
  else
    '(st1, p) <-- malloc st0 (m * n) ;;
    match p with
    | None => ret (st1, None)
    | Some q => is_allzero st1 q (fun _ => ret (st1, Some q)) (ret (st1, Some q))
    end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition slot_of_ptr (cs : mstate) (p : aptr) : option (aptr * (aptr * Z)) :=
  let cands := filter (fun sx : aptr * (aptr * Z) =>
                 let s := fst sx in let g := fst (snd sx) in
                 N.eqb (fst s) (fst p) && (snd s <=? snd p) && (snd p <? snd s + get_stride (get_meta_rec cs g)))
               (map_to_list (s_slots cs)) in
  match cands with sx :: _ => Some sx | [] => None end.

Definition crealloc (cs : mstate) (p : optr) (n : Z) : M (mstate * optr) :=
  match p with
  | None => cmalloc cs n
  | Some p =>
    if size_overflows n then ret (cs, None) else
    let bail := ret (cs, @None aptr) in
    match slot_of_ptr cs p with
    | None => SVis (EUndef UBadPtr) (fun _ => bail)
    | Some (start, (g, idx)) =>
      let mr := get_meta_rec cs g in
      let stride := get_stride mr in
      let avail := snd start + stride - IB - snd p in
      if (n <=? avail) && (n <? MMAP_THRESHOLD) && (m_sizeclass mr <=? size_to_class n + 1) then ret (cs, Some p)
      else
        let fallback (cs1 : mstate) : M (mstate * optr) :=
          '(cs2, q) <-- cmalloc cs1 n ;;
          match q with
          | None => ret (cs2, None)
          | Some q => cs3 <-- cfree cs2 (Some start) ;; ret (cs3, Some q)   (* [comment removed for export] *)
          end in
        if (48 <=? m_sizeclass mr) && (MMAP_THRESHOLD <=? n) then
          guard 70 (m_sizeclass mr =? 63) (
            let base := snd p - snd start in
            let needed := round_up_pg (n + base + UNIT + IB) in
            let oldlen := m_maplen mr * 4096 in
            let rid := fst start in
            let resize (nb : Z) := strip (upd_meta g (m_set_maplen (needed / 4096))
                                            (upd_region rid (fun rg => mkRegion (r_kind rg) nb needed) cs)) in
            if oldlen =? needed then ret (resize (conc cs (rid, 0)), Some p)
            else
              SVis (EMremap (conc cs (rid, 0)) oldlen needed) (fun r =>
                if negb (mremap_answer_ok cs rid (conc cs (rid, 0)) oldlen needed r) then bad_answer bail
                else if is_err r then fallback cs
                else ret (resize r, Some p)))
            bail
        else fallback cs
    end
  end.

Definition ccalloc (cs : mstate) (m n : Z) : M (mstate * option cptr) :=
  if negb (n =? 0) && (SIZE_MAX / n <? m) then ret (cs, None)
  else cmalloc cs (m * n).

End WithCeil.
End MallocRe.
