(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition PC_MALLOC : Z := 0x62a20.     (* [comment removed for export] *)
Definition PC_FREE : Z := 0x628c0.       (* [comment removed for export] *)
Definition PC_CALLOC : Z := 0x62c54.     (* [comment removed for export] *)
Definition ALLOC_PCS : list Z := [PC_MALLOC; PC_FREE; PC_CALLOC].

Definition RA_TOP : Z := 0x90e44.        (* [comment removed for export] *)
Definition RA_FUZZ_DESER : Z := 0x910a0.
Definition RA_FUZZ_DESTROY : Z := 0x91130.
Definition DESER_DESTROY_RAS : list Z := [0xae1bc; 0xae228; 0xae3bc; 0xae3fc].
Definition DESTROY_FREE_RAS : list Z := [0x927f0; 0x92858].

(* [comment removed for export] *)
Definition CLIENT_TRACES : list (list Z) :=
  [ [0x90afc];   (* [comment removed for export] *)
    [0x90b50];   (* [comment removed for export] *)
    [0x90b74];   (* [comment removed for export] *)
    [0x90ca4];   (* [comment removed for export] *)
    [0x90ddc];   (* [comment removed for export] *)
    [0x90e70];   (* [comment removed for export] *)
    [0x9163c];   (* [comment removed for export] *)
    [0x9184c];   (* [comment removed for export] *)
    [0x92370];   (* [comment removed for export] *)
    [0x94bdc];   (* [comment removed for export] *)
    [0x94de4];   (* [comment removed for export] *)
    [0x993a4];   (* [comment removed for export] *)
    [0x99da0];   (* [comment removed for export] *)
    [0x99da8];   (* [comment removed for export] *)
    [0x9b558];   (* [comment removed for export] *)
    [0x9b5a8];   (* [comment removed for export] *)
    [0xae718];   (* [comment removed for export] *)
    [0xae778];   (* [comment removed for export] *)
    [0xae8dc];   (* [comment removed for export] *)
    [0xae8e4];   (* [comment removed for export] *)
    [0xaea48];   (* [comment removed for export] *)
    [0xaea84];   (* [comment removed for export] *)
    [0xaeaa4];   (* [comment removed for export] *)
    [0xaeaac];   (* [comment removed for export] *)
    [0xaebf4];   (* [comment removed for export] *)
    [0xaecb4];   (* [comment removed for export] *)
    [0xaecbc];   (* [comment removed for export] *)
    [0xaee8c];   (* [comment removed for export] *)
    [0xaeeb4];   (* [comment removed for export] *)
    [0x91dc8; 0x91b4c];   (* [comment removed for export] *)
    [0x91dc8; 0x92ba0];   (* [comment removed for export] *)
    [0x91e78; 0x91b4c];   (* [comment removed for export] *)
    [0x91e78; 0x92ba0];   (* [comment removed for export] *)
    [0x91e98; 0x91b4c];   (* [comment removed for export] *)
    [0x91e98; 0x92ba0];   (* [comment removed for export] *)
    [0x91ee0; 0x91b4c];   (* [comment removed for export] *)
    [0x91ee0; 0x92ba0];   (* [comment removed for export] *)
    [0x99374; 0x92c8c];   (* [comment removed for export] *)
    [0x99374; 0x92d3c];   (* [comment removed for export] *)
    [0x99374; 0x945b4];   (* [comment removed for export] *)
    [0x993a4; 0x92c8c];   (* [comment removed for export] *)
    [0x993a4; 0x92d3c];   (* [comment removed for export] *)
    [0x993a4; 0x945b4];   (* [comment removed for export] *)
    [0x927f0; 0x91118; 0x90e44];   (* [comment removed for export] *)
    [0x927f0; 0x91128; 0x90e44];   (* [comment removed for export] *)
    [0x927f0; 0x91130; 0x90e44];   (* [comment removed for export] *)
    [0x92810; 0x91118; 0x90e44];   (* [comment removed for export] *)
    [0x92810; 0x91128; 0x90e44];   (* [comment removed for export] *)
    [0x92810; 0x91130; 0x90e44];   (* [comment removed for export] *)
    [0x92858; 0x91118; 0x90e44];   (* [comment removed for export] *)
    [0x92858; 0x91128; 0x90e44];   (* [comment removed for export] *)
    [0x92858; 0x91130; 0x90e44];   (* [comment removed for export] *)
    [0x9b5a8; 0x910a0; 0x90e44];   (* [comment removed for export] *)
    [0x927f0; 0xae1bc; 0x910a0; 0x90e44];   (* [comment removed for export] *)
    [0x927f0; 0xae228; 0x910a0; 0x90e44];   (* [comment removed for export] *)
    [0x927f0; 0xae3bc; 0x910a0; 0x90e44];   (* [comment removed for export] *)
    [0x927f0; 0xae3fc; 0x910a0; 0x90e44];   (* [comment removed for export] *)
    [0x927f0; 0xb0a50; 0x9110c; 0x90e44];   (* [comment removed for export] *)
    [0x927f0; 0xb0a58; 0x9110c; 0x90e44];   (* [comment removed for export] *)
    [0x927f0; 0xb0a70; 0x9110c; 0x90e44];   (* [comment removed for export] *)
    [0x92810; 0xae1bc; 0x910a0; 0x90e44];   (* [comment removed for export] *)
    [0x92810; 0xae228; 0x910a0; 0x90e44];   (* [comment removed for export] *)
    [0x92810; 0xae3bc; 0x910a0; 0x90e44];   (* [comment removed for export] *)
    [0x92810; 0xae3fc; 0x910a0; 0x90e44];   (* [comment removed for export] *)
    [0x92810; 0xb0a50; 0x9110c; 0x90e44];   (* [comment removed for export] *)
    [0x92810; 0xb0a58; 0x9110c; 0x90e44];   (* [comment removed for export] *)
    [0x92810; 0xb0a70; 0x9110c; 0x90e44];   (* [comment removed for export] *)
    [0x92858; 0xae1bc; 0x910a0; 0x90e44];   (* [comment removed for export] *)
    [0x92858; 0xae228; 0x910a0; 0x90e44];   (* [comment removed for export] *)
    [0x92858; 0xae3bc; 0x910a0; 0x90e44];   (* [comment removed for export] *)
    [0x92858; 0xae3fc; 0x910a0; 0x90e44];   (* [comment removed for export] *)
    [0x92858; 0xb0a50; 0x9110c; 0x90e44];   (* [comment removed for export] *)
    [0x92858; 0xb0a58; 0x9110c; 0x90e44];   (* [comment removed for export] *)
    [0x92858; 0xb0a70; 0x9110c; 0x90e44];   (* [comment removed for export] *)
    [0x94bdc; 0xb0a38; 0x9110c; 0x90e44];   (* [comment removed for export] *)
    [0x99374; 0x96f08; 0xb0a24; 0x9110c; 0x90e44];   (* [comment removed for export] *)
    [0x99374; 0x974f0; 0xb0a44; 0x9110c; 0x90e44];   (* [comment removed for export] *)
    [0x993a4; 0x96f08; 0xb0a24; 0x9110c; 0x90e44];   (* [comment removed for export] *)
    [0x993a4; 0x974f0; 0xb0a44; 0x9110c; 0x90e44]]   (* [comment removed for export] *)
.

(* [comment removed for export] *)
Definition ALLOC_RAS : list Z := flat_map (fun t => match t with [ra] => [ra] | _ => [] end) CLIENT_TRACES.

(* [comment removed for export] *)
Definition prefixes (l : list Z) : list (list Z) := map (fun k => firstn (S k) l) (seq 0 (length l)).

(* [comment removed for export] *)
Definition T_MAIN : list (list Z) :=
  flat_map (fun t => flat_map (fun pc => prefixes (pc :: t)) ALLOC_PCS) CLIENT_TRACES.

(* [comment removed for export] *)
Fixpoint zlist_eqb (u v : list Z) : bool :=
  match u, v with
  | [], [] => true
  | x :: u', y :: v' => (x =? y) && zlist_eqb u' v'
  | _, _ => false
  end.
Lemma zlist_eqb_eq : forall u v, zlist_eqb u v = true -> u = v.
Proof.
  induction u as [|x u IH]; intros [|y v] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. subst y. f_equal. exact (IH v H2).
Qed.
Definition ct_mem (t : list Z) : bool := existsb (zlist_eqb t) CLIENT_TRACES.
Definition tm_mem (t : list Z) : bool := existsb (zlist_eqb t) T_MAIN.
Lemma ct_mem_In : forall t, ct_mem t = true -> In t CLIENT_TRACES.
Proof. intros t H. apply existsb_exists in H as (u & Hu & E). apply zlist_eqb_eq in E. subst u. exact Hu. Qed.
Lemma tm_mem_In : forall t, tm_mem t = true -> In t T_MAIN.
Proof. intros t H. apply existsb_exists in H as (u & Hu & E). apply zlist_eqb_eq in E. subst u. exact Hu. Qed.
(* [comment removed for export] *)
Lemma alloc_ras_ct : forall ra, In ra ALLOC_RAS -> In [ra] CLIENT_TRACES.
Proof.
  intros ra H. unfold ALLOC_RAS in H. apply in_flat_map in H as (t & Ht & Hr).
  destruct t as [|x [|y t']]; cbn in Hr; try contradiction. destruct Hr as [<-|[]]. exact Ht.
Qed.

(* [comment removed for export] *)
Lemma client_traces_count : length CLIENT_TRACES = 79%nat /\ length T_MAIN = 822%nat.
Proof. vm_compute. split; reflexivity. Qed.

Lemma client_traces_wf :
  forallb (fun t => (Nat.leb 1 (length t) && Nat.leb (length t) 5
                     && forallb (fun x => (4096 <=? x) && (x <? 2^64) && negb (existsb (Z.eqb x) ALLOC_PCS)) t)%bool) CLIENT_TRACES = true.
Proof. vm_compute. reflexivity. Qed.

Lemma t_main_wf : forallb (fun t => (Nat.leb 1 (length t) && Nat.leb (length t) 6 && forallb (fun x => (0 <=? x) && (x <? 2^64)) t)%bool) T_MAIN = true.
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

Lemma t_main_length : forall tr, In tr T_MAIN -> (1 <= length tr <= 6)%nat.
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
  (1 <= length t <= 5)%nat /\ Forall (fun x => 4096 <= x < 2 ^ 64 /\ ~ In x ALLOC_PCS) t.
Proof.
  intros t H. pose proof client_traces_wf as W. rewrite forallb_forall in W. specialize (W t H).
  apply andb_prop in W as [W W3]. apply andb_prop in W as [W1 W2]. apply Nat.leb_le in W1, W2. split; [Lia.lia|].
  rewrite forallb_forall in W3. apply Forall_forall. intros x Hx. specialize (W3 x Hx).
  apply andb_prop in W3 as [W3 W4]. apply andb_prop in W3 as [Wa Wb]. apply Z.leb_le in Wa. apply Z.ltb_lt in Wb.
  split; [Lia.lia|]. intros Hin. apply negb_true_iff in W4. assert (E : existsb (Z.eqb x) ALLOC_PCS = true).
  { apply existsb_exists. exists x. split; [exact Hin | apply Z.eqb_refl]. } rewrite E in W4. discriminate.
Qed.
