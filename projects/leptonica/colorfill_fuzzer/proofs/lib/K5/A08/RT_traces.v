(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition PC_MALLOC : Z := 0x5ef08.     (* [comment removed for export] *)
Definition PC_FREE : Z := 0x5eda8.       (* [comment removed for export] *)
Definition PC_CALLOC : Z := 0x5f13c.     (* [comment removed for export] *)
Definition ALLOC_PCS : list Z := [PC_MALLOC; PC_FREE; PC_CALLOC].

Definition RA_TOP : Z := 0x8d32c.        (* [comment removed for export] *)
Definition RA_FUZZ_DESER : Z := 0x8d55c. (* [comment removed for export] *)
Definition RA_FUZZ_DESTROY : Z := 0x8d58c. (* [comment removed for export] *)
(* [comment removed for export] *)
Definition DESER_DESTROY_RAS : list Z := [0x92d24; 0x92d88; 0x92ef8; 0x92f38].
(* [comment removed for export] *)
Definition DESTROY_FREE_RAS : list Z := [0x90518; 0x90580].

Definition CLIENT_TRACES : list (list Z) :=
  (* [comment removed for export] *)
  [ [0x8cfe4]; [0x8d038]; [0x8d05c]; [0x8d18c]; [0x8d2c4]; [0x8d358];
  (* [comment removed for export] *)
    [0x90068]; [0x91d14]; [0x91d58]; [0x91a80]; [0x91a88];
  (* [comment removed for export] *)
    [0x8fad0; 0x8f87c] ]
  (* [comment removed for export] *)
  ++ map (fun f => [f; RA_FUZZ_DESTROY; RA_TOP]) DESTROY_FREE_RAS
  (* [comment removed for export] *)
  ++ flat_map (fun r => map (fun f => [f; r; RA_FUZZ_DESER; RA_TOP]) DESTROY_FREE_RAS) DESER_DESTROY_RAS
  (* [comment removed for export] *)
  ++ [ [0x8ea3c]; [0x8ed04]; [0x8ed68]; [0x8e0a4]; [0x8e0b8]; [0x8dc2c]; [0x8dc40]; [0x8e594];
       [0x8ed04; 0x8d578; RA_TOP]; [0x8e534; 0x8d578; RA_TOP]; [0x934cc; 0x8d578; RA_TOP];
       [0x8ef90]; [0x8f094]; [0x8f09c]; [0x8e924]; [0x8e934]; [0x8e3a0]; [0x8e3a8]; [0x8df28]; [0x8df30]; [0x937b8] ].

(* [comment removed for export] *)
Definition ALLOC_RAS : list Z := flat_map (fun t => match t with [ra] => [ra] | _ => [] end) CLIENT_TRACES.

(* [comment removed for export] *)
Definition prefixes (l : list Z) : list (list Z) := map (fun k => firstn (S k) l) (seq 0 (length l)).

(* [comment removed for export] *)
Definition T_MAIN : list (list Z) :=
  flat_map (fun t => flat_map (fun pc => prefixes (pc :: t)) ALLOC_PCS) CLIENT_TRACES.

(* [comment removed for export] *)
Lemma client_traces_count : length CLIENT_TRACES = 43%nat /\ length T_MAIN = 363%nat.
Proof. vm_compute. split; reflexivity. Qed.

Lemma client_traces_wf :
  forallb (fun t => (Nat.leb 1 (length t) && Nat.leb (length t) 4
                     && forallb (fun x => (4096 <=? x) && (x <? 2^64) && negb (existsb (Z.eqb x) ALLOC_PCS)) t)%bool) CLIENT_TRACES = true.
Proof. vm_compute. reflexivity. Qed.

Lemma t_main_wf : forallb (fun t => (Nat.leb 1 (length t) && Nat.leb (length t) 5 && forallb (fun x => (0 <=? x) && (x <? 2^64)) t)%bool) T_MAIN = true.
Proof. vm_compute. reflexivity. Qed.

Lemma prefixes_in : forall l j, (1 <= j <= length l)%nat -> In (firstn j l) (prefixes l).
Proof.
  intros l j Hj. unfold prefixes. apply in_map_iff. exists (j - 1)%nat. split; [f_equal; Lia.lia|]. apply in_seq. Lia.lia.
Qed.

(* [comment removed for export] *)
Lemma t_main_prefix : forall pc t j, In pc ALLOC_PCS -> In t CLIENT_TRACES -> (1 <= j <= S (length t))%nat ->
  In (firstn j (pc :: t)) T_MAIN.
Proof.
  intros pc t j Hpc Ht Hj. unfold T_MAIN. apply in_flat_map. exists t. split; [exact Ht|]. apply in_flat_map. exists pc.
  split; [exact Hpc|]. apply prefixes_in. cbn [length]. exact Hj.
Qed.

Lemma t_main_length : forall tr, In tr T_MAIN -> (1 <= length tr <= 5)%nat.
Proof.
  intros tr H. pose proof t_main_wf as W. rewrite forallb_forall in W. specialize (W tr H).
  apply andb_prop in W as [W _]. apply andb_prop in W as [W1 W2]. apply Nat.leb_le in W1, W2. Lia.lia.
Qed.

Lemma t_main_range : forall tr, In tr T_MAIN -> Forall (fun x => 0 <= x < 2 ^ 64) tr.
Proof.
  intros tr H. pose proof t_main_wf as W. rewrite forallb_forall in W. specialize (W tr H).
  apply andb_prop in W as [_ W]. rewrite forallb_forall in W. apply Forall_forall. intros x Hx. specialize (W x Hx).
  apply andb_prop in W as [W1 W2]. apply Z.leb_le in W1. apply Z.ltb_lt in W2. Lia.lia.
Qed.

Lemma client_trace_facts : forall t, In t CLIENT_TRACES ->
  (1 <= length t <= 4)%nat /\ Forall (fun x => 4096 <= x < 2 ^ 64 /\ ~ In x ALLOC_PCS) t.
Proof.
  intros t H. pose proof client_traces_wf as W. rewrite forallb_forall in W. specialize (W t H).
  apply andb_prop in W as [W W3]. apply andb_prop in W as [W1 W2]. apply Nat.leb_le in W1, W2. split; [Lia.lia|].
  rewrite forallb_forall in W3. apply Forall_forall. intros x Hx. specialize (W3 x Hx).
  apply andb_prop in W3 as [W3 W4]. apply andb_prop in W3 as [Wa Wb]. apply Z.leb_le in Wa. apply Z.ltb_lt in Wb.
  split; [Lia.lia|]. intros Hin. apply negb_true_iff in W4. assert (E : existsb (Z.eqb x) ALLOC_PCS = true).
  { apply existsb_exists. exists x. split; [exact Hin | apply Z.eqb_refl]. } rewrite E in W4. discriminate.
Qed.
