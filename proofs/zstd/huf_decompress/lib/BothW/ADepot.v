(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase ADepot_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition SSTF : Z := 0x18c1c8.    (* [comment removed for export] *)
Definition SSPTR : Z := 0x18c1d8.   (* [comment removed for export] *)
Definition SSST : Z := 0x18c1e0.    (* [comment removed for export] *)
Definition TAB : Z := 0x19c1d8.     (* [comment removed for export] *)
Definition NUNIQ : Z := 0x59c1d8.   (* [comment removed for export] *)
Definition MAP1 : Z := 0x59c1e8.    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition MMUL : Z := 14313749767032793493.
Definition MMUL8 : Z := 3829533694005038248.
Definition MSEED : Z := 10900877739976798860.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mz_mix (k : Z) : Z :=
  (Z.lxor (Z.shiftr ((k * 14313749767032793493) mod 18446744073709551616) 47)
          ((k * 14313749767032793493) mod 18446744073709551616) * 14313749767032793493) mod 18446744073709551616.
(* [comment removed for export] *)
Definition mz_add (h k : Z) : Z := (Z.lxor (mz_mix k) h * 14313749767032793493) mod 18446744073709551616.
Definition mz_adds (h : Z) (ks : list Z) : Z := fold_left mz_add ks h.
(* [comment removed for export] *)
Definition mz_init (sz : Z) : Z := Z.lxor ((sz * 3829533694005038248) mod 18446744073709551616) 10900877739976798860.
(* [comment removed for export] *)
Definition mz_fin (h : Z) : Z := let x2 := mz_mix (Z.lxor 0 h) in Z.lxor (Z.shiftr x2 47) x2.
(* [comment removed for export] *)
Definition hashU (u : list Z) : Z := mz_fin (mz_adds (mz_init (Z.of_nat (length u))) u).
Definition bkt (h : Z) : Z := h mod 1048576.
End CANSEC1.
Arguments hashU : simpl never.

Section CANSEC2. Context {rc : runConstT}.
Lemma lxor_range64 : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= Z.lxor a b < 2^64.
Proof. intros. apply Z_lxor_range; assumption. Qed.
Lemma mz_mix_range : forall k, 0 <= mz_mix k < 2^64.
Proof. intros. unfold mz_mix. change 18446744073709551616 with (2^64). apply Z.mod_pos_bound. lia. Qed.
Lemma mz_add_range : forall h k, 0 <= mz_add h k < 2^64.
Proof. intros. unfold mz_add. change 18446744073709551616 with (2^64). apply Z.mod_pos_bound. lia. Qed.
Lemma mz_adds_range : forall ks h, 0 <= h < 2^64 -> 0 <= mz_adds h ks < 2^64.
Proof.
  intros ks. unfold mz_adds. induction ks as [|k ks IH] using rev_ind; intros h Hh; cbn; [exact Hh|].
  rewrite fold_left_app. cbn. apply mz_add_range.
Qed.
Lemma mz_init_range : forall sz, 0 <= mz_init sz < 2^64.
Proof.
  intros. unfold mz_init. apply lxor_range64; [| lia].
  change 18446744073709551616 with (2^64). apply Z.mod_pos_bound. lia.
Qed.
Lemma mz_fin_range : forall h, 0 <= mz_fin h < 2^64.
Proof.
  intros. unfold mz_fin. cbv zeta. pose proof (mz_mix_range (Z.lxor 0 h)).
  apply lxor_range64; [| lia]. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; lia.
Qed.
Lemma hashU_range : forall u, 0 <= hashU u < 2^64.
Proof. intros. unfold hashU. apply mz_fin_range. Qed.

(* [comment removed for export] *)
Example hashU_w1 : hashU [0x3e6f0; 0x3fa40] = 0x69c69bedfb16eea2.
Proof. vm_compute. reflexivity. Qed.
Example hashU_w2 : hashU [0x3e6f0] = 0x67cb172786e4d619.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint walk (lk : Z -> Z) (fuel : nat) (s : Z) : list Z :=
  match fuel with
  | O => []
  | S f => if s =? 0 then [] else s :: walk lk f (lk s)
  end.

(* [comment removed for export] *)
Definition lk_ok (lk : Z -> Z) (N : Z) : Prop := forall i, 1 <= i <= N -> 0 <= lk i < i.

Lemma walk_fuel : forall lk N, lk_ok lk N -> forall f f' s, 0 <= s <= N -> (Z.to_nat s <= f)%nat -> (Z.to_nat s <= f')%nat ->
  walk lk f s = walk lk f' s.
Proof.
  intros lk N LK f. induction f as [|f IH]; intros f' s Hs Hf Hf'.
  - assert (s = 0) by lia. subst s. destruct f'; [reflexivity|]. cbn. reflexivity.
  - destruct f' as [|f']. { assert (s = 0) by lia. subst s. cbn. reflexivity. }
    cbn. destruct (Z.eqb_spec s 0); [reflexivity|]. f_equal.
    pose proof (LK s ltac:(lia)). apply IH; lia.
Qed.

Lemma walk_unfold : forall lk N s, lk_ok lk N -> 1 <= s <= N ->
  walk lk (Z.to_nat s) s = s :: walk lk (Z.to_nat (lk s)) (lk s).
Proof.
  intros lk N s LK Hs. pose proof (LK s Hs).
  replace (Z.to_nat s) with (S (Z.to_nat s - 1)) by lia. cbn.
  destruct (Z.eqb_spec s 0); [lia|]. f_equal. eapply walk_fuel; eauto; lia.
Qed.

Lemma walk_0 : forall lk f, walk lk f 0 = [].
Proof. intros lk [|f]; reflexivity. Qed.

(* [comment removed for export] *)
Lemma walk_elems : forall lk N, lk_ok lk N -> forall f s, 0 <= s <= N ->
  Forall (fun j => 1 <= j <= N) (walk lk f s).
Proof.
  intros lk N LK f. induction f as [|f IH]; intros s Hs; cbn; [constructor|].
  destruct (Z.eqb_spec s 0); [constructor|]. constructor; [lia|]. pose proof (LK s ltac:(lia)). apply IH. lia.
Qed.

Definition chain (lk : Z -> Z) (s : Z) : list Z := walk lk (Z.to_nat s) s.

Lemma chain_0 : forall lk, chain lk 0 = [].
Proof. intros; reflexivity. Qed.
Lemma chain_cons : forall lk N s, lk_ok lk N -> 1 <= s <= N -> chain lk s = s :: chain lk (lk s).
Proof. intros. unfold chain. eapply walk_unfold; eauto. Qed.
Lemma chain_elems : forall lk N s, lk_ok lk N -> 0 <= s <= N -> Forall (fun j => 1 <= j <= N) (chain lk s).
Proof. intros. unfold chain. eapply walk_elems; eauto. Qed.

(* [comment removed for export] *)
Lemma walk_ext : forall lk lk' N, lk_ok lk N -> (forall i, 1 <= i <= N -> lk' i = lk i) ->
  forall f s, 0 <= s <= N -> walk lk' f s = walk lk f s.
Proof.
  intros lk lk' N LK E f. induction f as [|f IH]; intros s Hs; cbn; [reflexivity|].
  destruct (Z.eqb_spec s 0); [reflexivity|]. pose proof (LK s ltac:(lia)). rewrite E by lia. f_equal. apply IH. lia.
Qed.
Lemma chain_ext : forall lk lk' N s, lk_ok lk N -> (forall i, 1 <= i <= N -> lk' i = lk i) -> 0 <= s <= N ->
  chain lk' s = chain lk s.
Proof. intros. unfold chain. eapply walk_ext; eauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record dstate := mkD {
  dN : Z;          (* [comment removed for export] *)
  dhd : Z -> Z;    (* [comment removed for export] *)
  dhs : Z -> Z;    (* [comment removed for export] *)
  dlk : Z -> Z;    (* [comment removed for export] *)
  dsid : Z -> Z;   (* [comment removed for export] *)
  dtf : Z          (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Fixpoint has_hash (hs : Z -> Z) (n : nat) (h : Z) : bool :=
  match n with O => false | S n' => (hs (Z.of_nat n) =? h) || has_hash hs n' h end.

Lemma has_hash_spec : forall hs n h, has_hash hs n h = true <-> exists i, 1 <= i <= Z.of_nat n /\ hs i = h.
Proof.
  intros hs n h. induction n as [|n IH]; cbn.
  - split; [discriminate|]. intros (i & Hi & _). lia.
  - rewrite Bool.orb_true_iff, Z.eqb_eq, IH. split.
    + intros [E | (i & Hi & E)]; [exists (Z.of_nat (S n)); split; [lia| exact E] | exists i; split; [lia| exact E]].
    + intros (i & Hi & E). destruct (Z.eq_dec i (Z.of_nat (S n))) as [->|]; [left; exact E | right; exists i; split; [lia|exact E]].
Qed.

(* [comment removed for export] *)
Definition ucost (u : list Z) : Z := Z.of_nat (length u) + 1.
Fixpoint BUD (U : list (list Z)) (hs : Z -> Z) (n : nat) : Z :=
  match U with [] => 0 | u :: U' => (if has_hash hs n (hashU u) then 0 else ucost u) + BUD U' hs n end.
Fixpoint CNT (U : list (list Z)) (hs : Z -> Z) (n : nat) : Z :=
  match U with [] => 0 | u :: U' => (if has_hash hs n (hashU u) then 0 else 1) + CNT U' hs n end.

Lemma BUD_nonneg : forall U hs n, 0 <= BUD U hs n.
Proof. induction U as [|u0 U IHU]; intros; cbn [BUD]; [lia|]. unfold ucost. destruct (has_hash hs n (hashU u0)); specialize (IHU hs n); lia. Qed.
Lemma CNT_nonneg : forall U hs n, 0 <= CNT U hs n.
Proof. induction U as [|u0 U IHU]; intros; cbn [CNT]; [lia|]. destruct (has_hash hs n (hashU u0)); specialize (IHU hs n); lia. Qed.

(* [comment removed for export] *)
Lemma BUD_In : forall U hs n u, In u U -> has_hash hs n (hashU u) = false -> ucost u <= BUD U hs n.
Proof.
  induction U as [|u0 U IH]; intros hs n u Hin Hh; [destruct Hin|]. cbn [BUD CNT]. destruct Hin as [-> | Hin].
  - rewrite Hh. pose proof (BUD_nonneg U hs n). lia.
  - pose proof (IH hs n u Hin Hh). destruct (has_hash hs n (hashU u0)); unfold ucost in *; lia.
Qed.
Lemma CNT_In : forall U hs n u, In u U -> has_hash hs n (hashU u) = false -> 1 <= CNT U hs n.
Proof.
  induction U as [|u0 U IH]; intros hs n u Hin Hh; [destruct Hin|]. cbn [BUD CNT]. destruct Hin as [-> | Hin].
  - rewrite Hh. pose proof (CNT_nonneg U hs n). lia.
  - pose proof (IH hs n u Hin Hh). destruct (has_hash hs n (hashU u0)); lia.
Qed.

(* [comment removed for export] *)
Lemma has_hash_ext : forall hs hs' n x, (forall i, 1 <= i <= Z.of_nat n -> hs' i = hs i) ->
  has_hash hs' n x = has_hash hs n x.
Proof.
  intros hs hs' n x. induction n as [|n IH]; intros E; cbn [has_hash]; [reflexivity|].
  rewrite E by lia. f_equal. apply IH. intros; apply E; lia.
Qed.
Lemma has_hash_S : forall hs hs' n h x, (forall i, 1 <= i <= Z.of_nat n -> hs' i = hs i) -> hs' (Z.of_nat (S n)) = h ->
  has_hash hs' (S n) x = (h =? x) || has_hash hs n x.
Proof.
  intros hs hs' n h x E Eh. cbn [has_hash]. rewrite Eh. f_equal. apply has_hash_ext. exact E.
Qed.

Lemma BUD_insert : forall U hs hs' n h, (forall i, 1 <= i <= Z.of_nat n -> hs' i = hs i) -> hs' (Z.of_nat (S n)) = h ->
  forall u, In u U -> hashU u = h -> has_hash hs n h = false ->
  BUD U hs' (S n) + ucost u <= BUD U hs n.
Proof.
  intros U hs hs' n h E Eh. induction U as [|u0 U IH]; intros u Hin Hu Hh; [destruct Hin|]. cbn [BUD CNT].
  rewrite (has_hash_S hs hs' n h) by assumption.
  destruct Hin as [-> | Hin].
  - rewrite Hu, Z.eqb_refl, Hh. cbn [orb].
    assert (M : BUD U hs' (S n) <= BUD U hs n).
    { clear IH. induction U as [|u1 U IH1]; cbn [BUD]; [lia|]. rewrite (has_hash_S hs hs' n h) by assumption.
      destruct (h =? hashU u1); destruct (has_hash hs n (hashU u1)); cbn [orb]; unfold ucost in *; lia. }
    lia.
  - pose proof (IH u Hin Hu Hh). destruct (h =? hashU u0); destruct (has_hash hs n (hashU u0)); cbn [orb]; unfold ucost in *; lia.
Qed.

Lemma CNT_insert : forall U hs hs' n h, (forall i, 1 <= i <= Z.of_nat n -> hs' i = hs i) -> hs' (Z.of_nat (S n)) = h ->
  forall u, In u U -> hashU u = h -> has_hash hs n h = false ->
  CNT U hs' (S n) + 1 <= CNT U hs n.
Proof.
  intros U hs hs' n h E Eh. induction U as [|u0 U IH]; intros u Hin Hu Hh; [destruct Hin|]. cbn [BUD CNT].
  rewrite (has_hash_S hs hs' n h) by assumption.
  destruct Hin as [-> | Hin].
  - rewrite Hu, Z.eqb_refl, Hh. cbn [orb].
    assert (M : CNT U hs' (S n) <= CNT U hs n).
    { clear IH. induction U as [|u1 U IH1]; cbn [CNT]; [lia|]. rewrite (has_hash_S hs hs' n h) by assumption.
      destruct (h =? hashU u1); destruct (has_hash hs n (hashU u1)); cbn [orb]; lia. }
    lia.
  - pose proof (IH u Hin Hu Hh). destruct (h =? hashU u0); destruct (has_hash hs n (hashU u0)); cbn [orb]; lia.
Qed.

(* [comment removed for export] *)
Definition dwf (U : list (list Z)) (D : dstate) : Prop :=
  1 <= dN D
  /\ lk_ok (dlk D) (dN D)
  /\ (forall b, 0 <= b < 1048576 -> 0 <= dhd D b <= dN D /\ (dhd D b <> 0 -> bkt (dhs D (dhd D b)) = b))
  /\ (forall i, 1 <= i <= dN D -> 0 <= dhs D i < 2^64 /\ 0 <= dsid D i < 2^32 /\ (dlk D i <> 0 -> bkt (dhs D (dlk D i)) = bkt (dhs D i)))
  /\ (forall i, 1 <= i <= dN D -> In i (chain (dlk D) (dhd D (bkt (dhs D i)))))
  /\ 0 <= dtf D /\ dtf D + BUD U (dhs D) (Z.to_nat (dN D)) < 1048576
  /\ dN D + CNT U (dhs D) (Z.to_nat (dN D)) < 65536.

(* [comment removed for export] *)
Lemma chain_bkt : forall U D b, dwf U D -> 0 <= b < 1048576 ->
  Forall (fun j => 1 <= j <= dN D /\ bkt (dhs D j) = b) (chain (dlk D) (dhd D b)).
Proof.
  intros U D b (N1 & LK & HD & ND & CMP & _) Hb.
  destruct (HD b Hb) as [R HB].
  assert (G : forall s, 0 <= s <= dN D -> (s <> 0 -> bkt (dhs D s) = b) -> Forall (fun j => 1 <= j <= dN D /\ bkt (dhs D j) = b) (chain (dlk D) s)).
  { intros s. remember (Z.to_nat s) as k eqn:Ek. revert s Ek. induction k as [k IH] using lt_wf_ind; intros s Ek Hs Hsb.
    destruct (Z.eq_dec s 0) as [->|]. { rewrite chain_0. constructor. }
    rewrite (chain_cons _ _ _ LK) by lia. pose proof (LK s ltac:(lia)). destruct (ND s ltac:(lia)) as (_ & _ & LB).
    constructor. { split; [lia| apply Hsb; lia]. }
    eapply (IH (Z.to_nat (dlk D s))); [lia | reflexivity | lia |]. intros Hl. rewrite (LB Hl). apply Hsb. lia. }
  apply G; [lia| exact HB].
Qed.

(* [comment removed for export] *)
Lemma absent_has_hash : forall U D h, dwf U D -> 0 <= h ->
  Forall (fun j => dhs D j <> h) (chain (dlk D) (dhd D (bkt h))) -> has_hash (dhs D) (Z.to_nat (dN D)) h = false.
Proof.
  intros U D h WF Hh FA. destruct (has_hash (dhs D) (Z.to_nat (dN D)) h) eqn:E; [|reflexivity]. exfalso.
  apply has_hash_spec in E. destruct E as (i & Hi & Ei).
  pose proof WF as (N1 & LK & HD & ND & CMP & _).
  pose proof (CMP i ltac:(lia)) as IN. rewrite Ei in IN.
  apply (proj1 (Forall_forall _ _) FA) in IN. exact (IN Ei).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dins (D : dstate) (b0 h v sid sz : Z) : dstate :=
  mkD (dN D + 1)
      (fun b => if b =? b0 then dN D + 1 else dhd D b)
      (fun i => if i =? dN D + 1 then h else dhs D i)
      (fun i => if i =? dN D + 1 then v else dlk D i)
      (fun i => if i =? dN D + 1 then sid else dsid D i)
      (dtf D + sz + 1).

(* [comment removed for export] *)
Lemma dwf_absent_budget : forall U D u h,
  dwf U D -> In u U -> hashU u = h ->
  Forall (fun j => dhs D j <> h) (chain (dlk D) (dhd D (bkt h))) ->
  dtf D + Z.of_nat (length u) + 1 < 1048576 /\ dN D + 1 < 65536.
Proof.
  intros U D u h WF IN HU FA. pose proof (hashU_range u) as HR. rewrite HU in HR.
  pose proof (absent_has_hash U D h WF ltac:(lia) FA) as AB. rewrite <- HU in AB.
  pose proof (BUD_In U (dhs D) (Z.to_nat (dN D)) u IN AB) as B1.
  pose proof (CNT_In U (dhs D) (Z.to_nat (dN D)) u IN AB) as C1.
  pose proof WF as (N1 & LK & HD & ND & CMP & TF0 & TFB & NB). unfold ucost in B1. lia.
Qed.

Lemma dwf_insert : forall U D u h v sid,
  dwf U D -> In u U -> hashU u = h ->
  v = dhd D (bkt h) ->
  Forall (fun j => dhs D j <> h) (chain (dlk D) v) ->
  0 <= sid < 2^32 ->
  dwf U (dins D (bkt h) h v sid (Z.of_nat (length u))).
Proof.
  intros U D u h v sid WF IN HU Hv FA SID.
  pose proof (hashU_range u) as HR. rewrite HU in HR.
  assert (HB : 0 <= bkt h < 1048576) by (unfold bkt; apply Z.mod_pos_bound; lia).
  pose proof WF as (N1 & LK & HD & ND & CMP & TF0 & TFB & NB).
  destruct (HD (bkt h) HB) as [VR VB]. rewrite <- Hv in VR, VB.
  subst v. pose proof (absent_has_hash U D h WF ltac:(lia) FA) as AB.
  pose proof (dwf_absent_budget U D u h WF IN HU FA) as [BB CB0].
  set (N := dN D) in *. set (D' := dins D (bkt h) h (dhd D (bkt h)) sid (Z.of_nat (length u))).
  assert (EN : dN D' = N + 1) by reflexivity.
  assert (EHS : forall i, 1 <= i <= N -> dhs D' i = dhs D i).
  { intros i Hi. cbn. fold N. destruct (Z.eqb_spec i (N + 1)); [lia| reflexivity]. }
  assert (ELK : forall i, 1 <= i <= N -> dlk D' i = dlk D i).
  { intros i Hi. cbn. fold N. destruct (Z.eqb_spec i (N + 1)); [lia| reflexivity]. }
  assert (ESID : forall i, 1 <= i <= N -> dsid D' i = dsid D i).
  { intros i Hi. cbn. fold N. destruct (Z.eqb_spec i (N + 1)); [lia| reflexivity]. }
  assert (EHS1 : dhs D' (N + 1) = h) by (cbn; fold N; rewrite Z.eqb_refl; reflexivity).
  assert (ELK1 : dlk D' (N + 1) = dhd D (bkt h)) by (cbn; fold N; rewrite Z.eqb_refl; reflexivity).
  assert (ESID1 : dsid D' (N + 1) = sid) by (cbn; fold N; rewrite Z.eqb_refl; reflexivity).
  assert (EHD : forall b, dhd D' b = if b =? bkt h then N + 1 else dhd D b) by (intros; reflexivity).
  assert (LK' : lk_ok (dlk D') (N + 1)).
  { intros i Hi. destruct (Z.eq_dec i (N + 1)) as [->|].
    - rewrite ELK1. lia.
    - rewrite ELK by lia. pose proof (LK i ltac:(lia)). lia. }
  assert (CHX : forall s, 0 <= s <= N -> chain (dlk D') s = chain (dlk D) s).
  { intros s Hs. apply (chain_ext (dlk D) (dlk D') N s LK); [| exact Hs]. intros i Hi. apply ELK. exact Hi. }
  unfold dwf. rewrite EN. split; [lia|]. split; [exact LK'|].
  split.
  { intros b Hb. rewrite EHD. destruct (Z.eqb_spec b (bkt h)) as [->|NE].
    - split; [lia|]. intros _. rewrite EHS1. reflexivity.
    - destruct (HD b Hb) as [R1 R2]. split; [lia|]. intros NZ. rewrite EHS by lia. apply R2. exact NZ. }
  split.
  { intros i Hi. destruct (Z.eq_dec i (N + 1)) as [->|NE].
    - rewrite EHS1, ESID1, ELK1. split; [lia|]. split; [lia|]. intros NZ. rewrite EHS by lia. rewrite (VB NZ). reflexivity.
    - rewrite EHS, ESID, ELK by lia. destruct (ND i ltac:(lia)) as (A1 & A2 & A3). split; [exact A1|]. split; [exact A2|].
      intros NZ. pose proof (LK i ltac:(lia)). rewrite EHS by lia. apply A3. exact NZ. }
  split.
  { intros i Hi. rewrite EHD. destruct (Z.eq_dec i (N + 1)) as [->|NE].
    - rewrite EHS1, Z.eqb_refl. rewrite (chain_cons (dlk D') (N + 1) (N + 1) LK') by lia. left. reflexivity.
    - rewrite EHS by lia. destruct (Z.eqb_spec (bkt (dhs D i)) (bkt h)) as [E|NE2].
      + rewrite (chain_cons (dlk D') (N + 1) (N + 1) LK') by lia. right. rewrite ELK1. rewrite CHX by lia.
        rewrite <- E. apply CMP. lia.
      + rewrite CHX by (destruct (HD (bkt (dhs D i)) ltac:(unfold bkt; apply Z.mod_pos_bound; lia)); lia). apply CMP. lia. }
  assert (EXT : forall i, 1 <= i <= Z.of_nat (Z.to_nat N) -> dhs D' i = dhs D i) by (intros; apply EHS; lia).
  assert (EH1 : dhs D' (Z.of_nat (S (Z.to_nat N))) = h) by (replace (Z.of_nat (S (Z.to_nat N))) with (N + 1) by lia; exact EHS1).
  pose proof (BUD_insert U (dhs D) (dhs D') (Z.to_nat N) h EXT EH1 u IN HU AB) as BI.
  pose proof (CNT_insert U (dhs D) (dhs D') (Z.to_nat N) h EXT EH1 u IN HU AB) as CI.
  replace (Z.to_nat (N + 1)) with (S (Z.to_nat N)) by lia.
  change (dtf D') with (dtf D + Z.of_nat (length u) + 1). unfold ucost in BI. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bytes_at_agree : forall m m' a bs,
  bytes_at bsegs m a bs -> (forall x, a <= x < a + Z.of_nat (length bs) -> m' (wa x) = m (wa x)) -> bytes_at bsegs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) E. split; [lia|]. split; [lia|]. intros i Hi.
  unfold mrd in *. rewrite E by lia. apply H. exact Hi.
Qed.

Lemma rw_cells_agree : forall m m' A cs,
  rw_cells bsegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> m' (wa x) = m (wa x)) -> wmono bsegs m m' ->
  rw_cells bsegs m' A cs.
Proof.
  intros m m' A cs [[WF B] (W0 & W1 & W)] E WM. pose proof (cells_bytes_length cs WF) as L.
  split; [split; [exact WF|]|].
  - eapply bytes_at_agree; [exact B|]. rewrite L. exact E.
  - split; [lia|]. split; [lia|]. intros i Hi. apply WM. apply W. exact Hi.
Qed.

Lemma stk_agree : forall m m' lo hi,
  stk bsegs m lo hi -> (forall x, lo <= x < hi -> m' (wa x) = m (wa x)) -> wmono bsegs m m' -> stk bsegs m' lo hi.
Proof.
  intros m m' lo hi (H0 & H1 & H) E WM. split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as [Hw (b & Hb)]. split; [apply WM; exact Hw|].
  exists b. unfold mrd in *. rewrite E by lia. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma munch_point : forall W m m' x, munch W m m' -> 0 <= x < 2^64 -> outside W x -> m' (wa x) = m (wa x).
Proof. intros W m m' x MU Hx Ho. apply MU. rewrite wa_unsigned by lia. exact Ho. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dcells (L : alayout) (D : dstate) (m : amem) : Prop :=
  rw_cells bsegs m SSTF [C8 (Z_to_bv 64 (dtf D))]
  /\ rw_cells bsegs m SSPTR [C8 (Z_to_bv 64 (al_store L))]
  /\ rw_cells bsegs m SSST [C4 (Z_to_bv 64 (dtf D))]
  /\ rw_cells bsegs m NUNIQ [C4 (Z_to_bv 64 (dN D))]
  /\ rw_cells bsegs m MAP1 [C8 (Z_to_bv 64 (al_nodes L))]
  /\ (forall b, 0 <= b < 1048576 -> rw_cells bsegs m (TAB + 4 * b) [C4 (Z_to_bv 64 (dhd D b))])
  /\ (forall i, 1 <= i <= dN D ->
        rw_cells bsegs m (al_nodes L + 16 * i) [C8 (Z_to_bv 64 (dhs D i)); C4 (Z_to_bv 64 (dlk D i)); C4 (Z_to_bv 64 (dsid D i))])
  /\ stk bsegs m (al_nodes L + 16 * (dN D + 1)) (al_nodes L + 1048576)
  /\ stk bsegs m (al_store L) (al_store L + 8388608).

(* [comment removed for export] *)
Definition dlayout (L : alayout) : Prop :=
  al_nodes L mod 4096 = 0 /\ al_store L mod 4096 = 0
  /\ AIMG_HI <= al_nodes L /\ al_nodes L + 1048576 <= ATOP /\ AIMG_HI <= al_store L /\ al_store L + 8388608 <= ATOP
  /\ (al_nodes L + 1048576 <= al_store L \/ al_store L + 8388608 <= al_nodes L).

(* [comment removed for export] *)
Definition ADEPOTi (L : alayout) (m : amem) : Prop :=
  exists D, dwf (al_U L) D /\ dcells L D m /\ dlayout L.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma adepot_frame : depot_frame_stmt ADEPOTi.
Proof.
  unfold depot_frame_stmt. intros L m m' W (D & WF & DC & LY) MU WM FA.
  exists D. split; [exact WF|]. split; [| exact LY].
  pose proof LY as (_ & _ & LN0 & LN1 & LS0 & LS1 & _). unfold AIMG_HI in *.
  pose proof WF as (N1 & LK & HD & ND & CMP & TF0 & TFB & NB).
  pose proof (CNT_nonneg (al_U L) (dhs D) (Z.to_nat (dN D))) as CN.
  assert (OUT : forall x, (0x18c1c8 <= x < 0x5dc210 \/ al_nodes L <= x < al_nodes L + 1048576 \/ al_store L <= x < al_store L + 8388608) ->
                         m' (wa x) = m (wa x)).
  { intros x Hx. apply (munch_point W m m' x MU); [lia|].
    clear - FA Hx. induction FA as [| [lo hi] W Hiv FA IH]; cbn; [exact I|]. split; [| exact IH].
    intros Hin. destruct (Hiv x Hin) as (A & B & C). cbn in *. lia. }
  destruct DC as (C1 & C2 & C3 & C4 & C5 & CT & CN' & SK1 & SK2).
  unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in *.
  split; [eapply rw_cells_agree; [exact C1| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia| exact WM]|].
  split; [eapply rw_cells_agree; [exact C2| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia| exact WM]|].
  split; [eapply rw_cells_agree; [exact C3| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia| exact WM]|].
  split; [eapply rw_cells_agree; [exact C4| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia| exact WM]|].
  split; [eapply rw_cells_agree; [exact C5| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia| exact WM]|].
  split. { intros b Hb. eapply rw_cells_agree; [exact (CT b Hb)| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia| exact WM]. }
  split. { intros i Hi. eapply rw_cells_agree; [exact (CN' i Hi)| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia| exact WM]. }
  split. { eapply stk_agree; [exact SK1| intros x Hx; apply OUT; lia| exact WM]. }
  eapply stk_agree; [exact SK2| intros x Hx; apply OUT; lia| exact WM].
Qed.
End CANSEC2.
