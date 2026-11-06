(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition PC_MALLOC : Z := 0x62300.     (* [comment removed for export] *)
Definition PC_FREE : Z := 0x621a0.       (* [comment removed for export] *)
Definition PC_CALLOC : Z := 0x62534.     (* [comment removed for export] *)
Definition ALLOC_PCS : list Z := [PC_MALLOC; PC_FREE; PC_CALLOC].

Definition RA_TOP : Z := 0x90724.        (* [comment removed for export] *)
Definition RA_FUZZ_DESER : Z := 0x90968.
Definition RA_FUZZ_DESTROY : Z := 0x90ac8.
Definition DESER_DESTROY_RAS : list Z := [0xa7f7c; 0xa7fe0; 0xa8150; 0xa8190].
Definition DESTROY_FREE_RAS : list Z := [0x93f9c; 0x94004].
Definition FUZZ_DESTROY_RAS : list Z := [0x909a4; 0x909ac; 0x909d0; 0x909d8; 0x90a08; 0x90a10; 0x90a44; 0x90a4c; 0x90a78; 0x90a80; 0x90ab8; 0x90ac0; 0x90ac8].
Definition FUZZ_COPY_RAS : list Z := [0x9098c; 0x909bc; 0x909e4; 0x90a1c; 0x90a58; 0x90a8c].
Definition FUZZ_OP_RAS : list Z := [0x90998; 0x909c4; 0x909fc; 0x90a38; 0x90a6c; 0x90aac].

(* [comment removed for export] *)
Definition CLIENT_TRACES : list (list Z) :=
  [ [0x903dc];   (* [comment removed for export] *)
    [0x90430];   (* [comment removed for export] *)
    [0x90454];   (* [comment removed for export] *)
    [0x90584];   (* [comment removed for export] *)
    [0x906bc];   (* [comment removed for export] *)
    [0x90750];   (* [comment removed for export] *)
    [0x90f80];   (* [comment removed for export] *)
    [0x91160];   (* [comment removed for export] *)
    [0x9143c];   (* [comment removed for export] *)
    [0x918ec];   (* [comment removed for export] *)
    [0x919c8];   (* [comment removed for export] *)
    [0x919d0];   (* [comment removed for export] *)
    [0x91b50];   (* [comment removed for export] *)
    [0x91b58];   (* [comment removed for export] *)
    [0x93aec];   (* [comment removed for export] *)
    [0x96bc8];   (* [comment removed for export] *)
    [0x96f7c];   (* [comment removed for export] *)
    [0x96fbc];   (* [comment removed for export] *)
    [0x97458];   (* [comment removed for export] *)
    [0x97e18];   (* [comment removed for export] *)
    [0x97e20];   (* [comment removed for export] *)
    [0x99184];   (* [comment removed for export] *)
    [0x99194];   (* [comment removed for export] *)
    [0x991a4];   (* [comment removed for export] *)
    [0x991e4];   (* [comment removed for export] *)
    [0x99af0];   (* [comment removed for export] *)
    [0x99b34];   (* [comment removed for export] *)
    [0x93554; 0x93300];   (* [comment removed for export] *)
    [0x93554; 0x941a4];   (* [comment removed for export] *)
    [0x93604; 0x93300];   (* [comment removed for export] *)
    [0x93604; 0x941a4];   (* [comment removed for export] *)
    [0x93624; 0x93300];   (* [comment removed for export] *)
    [0x93624; 0x941a4];   (* [comment removed for export] *)
    [0x9366c; 0x93300];   (* [comment removed for export] *)
    [0x9366c; 0x941a4];   (* [comment removed for export] *)
    [0x97430; 0x94284];   (* [comment removed for export] *)
    [0x97430; 0x94330];   (* [comment removed for export] *)
    [0x97430; 0x95598];   (* [comment removed for export] *)
    [0x93f9c; 0x909a4; 0x90724];   (* [comment removed for export] *)
    [0x93f9c; 0x909ac; 0x90724];   (* [comment removed for export] *)
    [0x93f9c; 0x909d0; 0x90724];   (* [comment removed for export] *)
    [0x93f9c; 0x909d8; 0x90724];   (* [comment removed for export] *)
    [0x93f9c; 0x90a08; 0x90724];   (* [comment removed for export] *)
    [0x93f9c; 0x90a10; 0x90724];   (* [comment removed for export] *)
    [0x93f9c; 0x90a44; 0x90724];   (* [comment removed for export] *)
    [0x93f9c; 0x90a4c; 0x90724];   (* [comment removed for export] *)
    [0x93f9c; 0x90a78; 0x90724];   (* [comment removed for export] *)
    [0x93f9c; 0x90a80; 0x90724];   (* [comment removed for export] *)
    [0x93f9c; 0x90ab8; 0x90724];   (* [comment removed for export] *)
    [0x93f9c; 0x90ac0; 0x90724];   (* [comment removed for export] *)
    [0x93f9c; 0x90ac8; 0x90724];   (* [comment removed for export] *)
    [0x93fbc; 0x909a4; 0x90724];   (* [comment removed for export] *)
    [0x93fbc; 0x909ac; 0x90724];   (* [comment removed for export] *)
    [0x93fbc; 0x909d0; 0x90724];   (* [comment removed for export] *)
    [0x93fbc; 0x909d8; 0x90724];   (* [comment removed for export] *)
    [0x93fbc; 0x90a08; 0x90724];   (* [comment removed for export] *)
    [0x93fbc; 0x90a10; 0x90724];   (* [comment removed for export] *)
    [0x93fbc; 0x90a44; 0x90724];   (* [comment removed for export] *)
    [0x93fbc; 0x90a4c; 0x90724];   (* [comment removed for export] *)
    [0x93fbc; 0x90a78; 0x90724];   (* [comment removed for export] *)
    [0x93fbc; 0x90a80; 0x90724];   (* [comment removed for export] *)
    [0x93fbc; 0x90ab8; 0x90724];   (* [comment removed for export] *)
    [0x93fbc; 0x90ac0; 0x90724];   (* [comment removed for export] *)
    [0x93fbc; 0x90ac8; 0x90724];   (* [comment removed for export] *)
    [0x94004; 0x909a4; 0x90724];   (* [comment removed for export] *)
    [0x94004; 0x909ac; 0x90724];   (* [comment removed for export] *)
    [0x94004; 0x909d0; 0x90724];   (* [comment removed for export] *)
    [0x94004; 0x909d8; 0x90724];   (* [comment removed for export] *)
    [0x94004; 0x90a08; 0x90724];   (* [comment removed for export] *)
    [0x94004; 0x90a10; 0x90724];   (* [comment removed for export] *)
    [0x94004; 0x90a44; 0x90724];   (* [comment removed for export] *)
    [0x94004; 0x90a4c; 0x90724];   (* [comment removed for export] *)
    [0x94004; 0x90a78; 0x90724];   (* [comment removed for export] *)
    [0x94004; 0x90a80; 0x90724];   (* [comment removed for export] *)
    [0x94004; 0x90ab8; 0x90724];   (* [comment removed for export] *)
    [0x94004; 0x90ac0; 0x90724];   (* [comment removed for export] *)
    [0x94004; 0x90ac8; 0x90724];   (* [comment removed for export] *)
    [0x96b88; 0x90aac; 0x90724];   (* [comment removed for export] *)
    [0x9c840; 0x909c4; 0x90724];   (* [comment removed for export] *)
    [0x9c850; 0x909c4; 0x90724];   (* [comment removed for export] *)
    [0x9c890; 0x909c4; 0x90724];   (* [comment removed for export] *)
    [0x9c898; 0x909c4; 0x90724];   (* [comment removed for export] *)
    [0x9c92c; 0x909c4; 0x90724];   (* [comment removed for export] *)
    [0x9c934; 0x909c4; 0x90724];   (* [comment removed for export] *)
    [0x9e0c4; 0x90998; 0x90724];   (* [comment removed for export] *)
    [0x9e0d8; 0x90998; 0x90724];   (* [comment removed for export] *)
    [0x9e100; 0x90998; 0x90724];   (* [comment removed for export] *)
    [0x9e110; 0x90998; 0x90724];   (* [comment removed for export] *)
    [0x9e120; 0x90998; 0x90724];   (* [comment removed for export] *)
    [0x9e49c; 0x90998; 0x90724];   (* [comment removed for export] *)
    [0x9e4a4; 0x90998; 0x90724];   (* [comment removed for export] *)
    [0x9ed5c; 0x90998; 0x90724];   (* [comment removed for export] *)
    [0x9ed64; 0x90998; 0x90724];   (* [comment removed for export] *)
    [0x9ed6c; 0x90998; 0x90724];   (* [comment removed for export] *)
    [0x9ed74; 0x90998; 0x90724];   (* [comment removed for export] *)
    [0x9ed7c; 0x90998; 0x90724];   (* [comment removed for export] *)
    [0x9f850; 0x90aac; 0x90724];   (* [comment removed for export] *)
    [0x9f868; 0x90aac; 0x90724];   (* [comment removed for export] *)
    [0x9faac; 0x90aac; 0x90724];   (* [comment removed for export] *)
    [0x9fc94; 0x90aac; 0x90724];   (* [comment removed for export] *)
    [0x9fc9c; 0x90aac; 0x90724];   (* [comment removed for export] *)
    [0x9fca4; 0x90aac; 0x90724];   (* [comment removed for export] *)
    [0x9fd04; 0x90aac; 0x90724];   (* [comment removed for export] *)
    [0x9fe48; 0x90aac; 0x90724];   (* [comment removed for export] *)
    [0xa00ec; 0x90aac; 0x90724];   (* [comment removed for export] *)
    [0x9143c; 0x9f5e0; 0x90aac; 0x90724];   (* [comment removed for export] *)
    [0x918dc; 0x9f5e0; 0x90aac; 0x90724];   (* [comment removed for export] *)
    [0x93f9c; 0x9c8a0; 0x909c4; 0x90724];   (* [comment removed for export] *)
    [0x93f9c; 0x9c8e8; 0x909c4; 0x90724];   (* [comment removed for export] *)
    [0x93f9c; 0x9c93c; 0x909c4; 0x90724];   (* [comment removed for export] *)
    [0x93f9c; 0x9c944; 0x909c4; 0x90724];   (* [comment removed for export] *)
    [0x93f9c; 0x9d800; 0x909fc; 0x90724];   (* [comment removed for export] *)
    [0x93f9c; 0x9d850; 0x909fc; 0x90724];   (* [comment removed for export] *)
    [0x93f9c; 0x9d8a0; 0x909fc; 0x90724];   (* [comment removed for export] *)
    [0x93f9c; 0x9dbe8; 0x909fc; 0x90724];   (* [comment removed for export] *)
    [0x93f9c; 0x9e4ac; 0x90998; 0x90724];   (* [comment removed for export] *)
    [0x93f9c; 0x9e4b4; 0x90998; 0x90724];   (* [comment removed for export] *)
    [0x93f9c; 0x9ed84; 0x90998; 0x90724];   (* [comment removed for export] *)
    [0x93f9c; 0xa00f4; 0x90aac; 0x90724];   (* [comment removed for export] *)
    [0x93f9c; 0xa7f7c; 0x90968; 0x90724];   (* [comment removed for export] *)
    [0x93f9c; 0xa7fe0; 0x90968; 0x90724];   (* [comment removed for export] *)
    [0x93f9c; 0xa8150; 0x90968; 0x90724];   (* [comment removed for export] *)
    [0x93f9c; 0xa8190; 0x90968; 0x90724];   (* [comment removed for export] *)
    [0x93fbc; 0x9c8a0; 0x909c4; 0x90724];   (* [comment removed for export] *)
    [0x93fbc; 0x9c8e8; 0x909c4; 0x90724];   (* [comment removed for export] *)
    [0x93fbc; 0x9c93c; 0x909c4; 0x90724];   (* [comment removed for export] *)
    [0x93fbc; 0x9c944; 0x909c4; 0x90724];   (* [comment removed for export] *)
    [0x93fbc; 0x9d800; 0x909fc; 0x90724];   (* [comment removed for export] *)
    [0x93fbc; 0x9d850; 0x909fc; 0x90724];   (* [comment removed for export] *)
    [0x93fbc; 0x9d8a0; 0x909fc; 0x90724];   (* [comment removed for export] *)
    [0x93fbc; 0x9dbe8; 0x909fc; 0x90724];   (* [comment removed for export] *)
    [0x93fbc; 0x9e4ac; 0x90998; 0x90724];   (* [comment removed for export] *)
    [0x93fbc; 0x9e4b4; 0x90998; 0x90724];   (* [comment removed for export] *)
    [0x93fbc; 0x9ed84; 0x90998; 0x90724];   (* [comment removed for export] *)
    [0x93fbc; 0xa00f4; 0x90aac; 0x90724];   (* [comment removed for export] *)
    [0x93fbc; 0xa7f7c; 0x90968; 0x90724];   (* [comment removed for export] *)
    [0x93fbc; 0xa7fe0; 0x90968; 0x90724];   (* [comment removed for export] *)
    [0x93fbc; 0xa8150; 0x90968; 0x90724];   (* [comment removed for export] *)
    [0x93fbc; 0xa8190; 0x90968; 0x90724];   (* [comment removed for export] *)
    [0x94004; 0x9c8a0; 0x909c4; 0x90724];   (* [comment removed for export] *)
    [0x94004; 0x9c8e8; 0x909c4; 0x90724];   (* [comment removed for export] *)
    [0x94004; 0x9c93c; 0x909c4; 0x90724];   (* [comment removed for export] *)
    [0x94004; 0x9c944; 0x909c4; 0x90724];   (* [comment removed for export] *)
    [0x94004; 0x9d800; 0x909fc; 0x90724];   (* [comment removed for export] *)
    [0x94004; 0x9d850; 0x909fc; 0x90724];   (* [comment removed for export] *)
    [0x94004; 0x9d8a0; 0x909fc; 0x90724];   (* [comment removed for export] *)
    [0x94004; 0x9dbe8; 0x909fc; 0x90724];   (* [comment removed for export] *)
    [0x94004; 0x9e4ac; 0x90998; 0x90724];   (* [comment removed for export] *)
    [0x94004; 0x9e4b4; 0x90998; 0x90724];   (* [comment removed for export] *)
    [0x94004; 0x9ed84; 0x90998; 0x90724];   (* [comment removed for export] *)
    [0x94004; 0xa00f4; 0x90aac; 0x90724];   (* [comment removed for export] *)
    [0x94004; 0xa7f7c; 0x90968; 0x90724];   (* [comment removed for export] *)
    [0x94004; 0xa7fe0; 0x90968; 0x90724];   (* [comment removed for export] *)
    [0x94004; 0xa8150; 0x90968; 0x90724];   (* [comment removed for export] *)
    [0x94004; 0xa8190; 0x90968; 0x90724];   (* [comment removed for export] *)
    [0x96b88; 0x9f7b0; 0x90aac; 0x90724];   (* [comment removed for export] *)
    [0x9aa84; 0x9c814; 0x909c4; 0x90724];   (* [comment removed for export] *)
    [0x9aa84; 0x9d7cc; 0x909fc; 0x90724];   (* [comment removed for export] *)
    [0x9aa84; 0x9e09c; 0x90998; 0x90724];   (* [comment removed for export] *)
    [0x9aa84; 0x9fdec; 0x90aac; 0x90724];   (* [comment removed for export] *)
    [0x9ae84; 0x9c814; 0x909c4; 0x90724];   (* [comment removed for export] *)
    [0x9ae84; 0x9d7cc; 0x909fc; 0x90724];   (* [comment removed for export] *)
    [0x9ae84; 0x9e09c; 0x90998; 0x90724];   (* [comment removed for export] *)
    [0x9ae84; 0x9fdec; 0x90aac; 0x90724];   (* [comment removed for export] *)
    [0x9b04c; 0x9c814; 0x909c4; 0x90724];   (* [comment removed for export] *)
    [0x9b04c; 0x9d7cc; 0x909fc; 0x90724];   (* [comment removed for export] *)
    [0x9b04c; 0x9e09c; 0x90998; 0x90724];   (* [comment removed for export] *)
    [0x9b04c; 0x9fdec; 0x90aac; 0x90724];   (* [comment removed for export] *)
    [0x9c05c; 0x9c814; 0x909c4; 0x90724];   (* [comment removed for export] *)
    [0x9c05c; 0x9d7cc; 0x909fc; 0x90724];   (* [comment removed for export] *)
    [0x9c05c; 0x9e09c; 0x90998; 0x90724];   (* [comment removed for export] *)
    [0x9c05c; 0x9fdec; 0x90aac; 0x90724];   (* [comment removed for export] *)
    [0x9c0dc; 0x9c814; 0x909c4; 0x90724];   (* [comment removed for export] *)
    [0x9c0dc; 0x9d7cc; 0x909fc; 0x90724];   (* [comment removed for export] *)
    [0x9c0dc; 0x9e09c; 0x90998; 0x90724];   (* [comment removed for export] *)
    [0x9c0dc; 0x9fdec; 0x90aac; 0x90724];   (* [comment removed for export] *)
    [0x9c0e4; 0x9c814; 0x909c4; 0x90724];   (* [comment removed for export] *)
    [0x9c0e4; 0x9d7cc; 0x909fc; 0x90724];   (* [comment removed for export] *)
    [0x9c0e4; 0x9e09c; 0x90998; 0x90724];   (* [comment removed for export] *)
    [0x9c0e4; 0x9fdec; 0x90aac; 0x90724];   (* [comment removed for export] *)
    [0x9c0f0; 0x9c814; 0x909c4; 0x90724];   (* [comment removed for export] *)
    [0x9c0f0; 0x9d7cc; 0x909fc; 0x90724];   (* [comment removed for export] *)
    [0x9c0f0; 0x9e09c; 0x90998; 0x90724];   (* [comment removed for export] *)
    [0x9c0f0; 0x9fdec; 0x90aac; 0x90724];   (* [comment removed for export] *)
    [0x9c0fc; 0x9c814; 0x909c4; 0x90724];   (* [comment removed for export] *)
    [0x9c0fc; 0x9d7cc; 0x909fc; 0x90724];   (* [comment removed for export] *)
    [0x9c0fc; 0x9e09c; 0x90998; 0x90724];   (* [comment removed for export] *)
    [0x9c0fc; 0x9fdec; 0x90aac; 0x90724];   (* [comment removed for export] *)
    [0xa03e0; 0x9f7b0; 0x90aac; 0x90724];   (* [comment removed for export] *)
    [0xa85c8; 0x9f5e0; 0x90aac; 0x90724];   (* [comment removed for export] *)
    [0xa85e4; 0x9f5e0; 0x90aac; 0x90724]]   (* [comment removed for export] *)
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
Lemma client_traces_count : length CLIENT_TRACES = 191%nat /\ length T_MAIN = 2355%nat.
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
