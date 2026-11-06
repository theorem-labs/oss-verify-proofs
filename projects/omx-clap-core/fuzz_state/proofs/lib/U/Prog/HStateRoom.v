From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import AllocSlots AllocRoom.
Import ListNotations.
Local Open Scope Z_scope.

(* The allocator requests of a harness function, in code order: a block of n bytes made (HMal n) or released
   (HFre n). The frame's resource bound (sbound: live blocks, live bytes, cap) after them, and the room each
   request needs on the way. *)
Inductive hop := HMal (n : Z) | HFre (n : Z).

Fixpoint hs_rb (b : sbound) (ops : list hop) : sbound :=
  match ops with
  | [] => b
  | HMal n :: r => hs_rb (sb_malloc b n) r
  | HFre n :: r => hs_rb (sb_free b n) r
  end.

Fixpoint hs_room (b : sbound) (ops : list hop) : Prop :=
  match ops with
  | [] => True
  | HMal n :: r => room_slots b n /\ hs_room (sb_malloc b n) r
  | HFre n :: r => hs_room (sb_free b n) r
  end.

Definition dec_ops (ok : bool) (n : Z) : list hop :=
  let m := n / 4 * 3 + 3 + 16 in if ok then [HMal m] else [HMal m; HFre m].

Definition dec_free_ops (ok : bool) (n : Z) : list hop :=
  if ok then [HFre (n / 4 * 3 + 3 + 16)] else [].

Definition hs_small (S : Z) (ops : list hop) : Prop :=
  Forall (fun o => match o with HMal n | HFre n => 0 <= n <= S end) ops.

Definition hs_room_all (b : sbound) (N : nat) (S : Z) : Prop :=
  forall ops, (length ops <= N)%nat -> hs_small S ops -> hs_room b ops.

Lemma hs_rb_cap : forall ops b, sb_cap (hs_rb b ops) = sb_cap b.
Proof. induction ops as [|[n|n] r IH]; intros b; cbn [hs_rb]; [reflexivity | rewrite IH | rewrite IH]; reflexivity. Qed.

(* Room for every short sequence of small requests, from the bound's three numbers. *)
Lemma hs_room_of_bound : forall (N : nat) S ops b,
  0 <= S <= 2 ^ 28 - 2 ^ 13 -> (length ops <= N)%nat -> hs_small S ops ->
  sb_live b + Z.of_nat N <= sb_cap b <= CAPMAX ->
  sb_bytes b + Z.of_nat N * S <= 2 ^ 40 ->
  hs_room b ops.
Proof.
  intros N S ops. revert N. induction ops as [|o r IH]; intros N b HS HL HSm HC HB; [exact I|].
  destruct N as [|N]; [cbn in HL; lia|]. cbn [length] in HL.
  inversion HSm as [|o' r' Ho Hr]; subst.
  rewrite Nat2Z.inj_succ in HC, HB.
  destruct o as [n|n]; cbn [hs_room]; cbv beta iota in Ho.
  - split.
    + unfold room_slots. split; [lia|]. split; [lia|].
      apply (CAPOK_mono CAPMAX (sb_cap b) (2 ^ 40) (sb_bytes b + n) (2 ^ 28 - 2 ^ 13) n);
        [lia | nia | lia | exact CAPOK_big].
    + apply (IH N); [exact HS | lia | exact Hr | cbn [sb_live sb_cap sb_malloc]; lia |].
      cbn [sb_bytes sb_malloc]. nia.
  - apply (IH N); [exact HS | lia | exact Hr | cbn [sb_live sb_cap sb_free]; lia |].
    cbn [sb_bytes sb_free]. nia.
Qed.

Lemma hs_room_all_of_bound : forall b (N : nat) S,
  0 <= S <= 2 ^ 28 - 2 ^ 13 ->
  sb_live b + Z.of_nat N <= sb_cap b <= CAPMAX ->
  sb_bytes b + Z.of_nat N * S <= 2 ^ 40 ->
  hs_room_all b N S.
Proof. intros b N S HS HC HB ops HL HSm. exact (hs_room_of_bound N S ops b HS HL HSm HC HB). Qed.

(* Headroom of a bound for N more requests of at most M bytes each, with 2^30 bytes to spare for a callee that
   asks its own room (the writer's wr_room). *)
Definition hs_cap (b : sbound) (N : nat) (M : Z) : Prop :=
  sb_live b + Z.of_nat N <= sb_cap b <= CAPMAX /\ sb_bytes b + Z.of_nat N * M + 2 ^ 30 <= 2 ^ 40.

Lemma hs_cap_room_all : forall b N M, 0 <= M <= 2 ^ 28 - 2 ^ 13 -> hs_cap b N M -> hs_room_all b N M.
Proof.
  intros b N M HS (HC & HB). apply hs_room_all_of_bound; [exact HS | exact HC | lia].
Qed.

Lemma hs_cap_room : forall b N M n, 0 <= M <= 2 ^ 28 - 2 ^ 13 -> 0 <= n <= M -> hs_cap b (Datatypes.S N) M -> room_slots b n.
Proof.
  intros b N M n HS Hn (HC & HB). rewrite Nat2Z.inj_succ in HC, HB.
  unfold room_slots. split; [lia|]. split; [lia|].
  apply (CAPOK_mono CAPMAX (sb_cap b) (2 ^ 40) (sb_bytes b + n) (2 ^ 28 - 2 ^ 13) n);
    [lia | nia | lia | exact CAPOK_big].
Qed.

Lemma hs_cap_malloc : forall b N M n, 0 <= n <= M -> hs_cap b (Datatypes.S N) M -> hs_cap (sb_malloc b n) N M.
Proof.
  intros b N M n Hn (HC & HB). rewrite Nat2Z.inj_succ in HC, HB. unfold hs_cap, sb_malloc. cbn [sb_live sb_bytes sb_cap].
  split; [lia | nia].
Qed.

Lemma hs_cap_free : forall b N M n, 0 <= n -> hs_cap b N M -> hs_cap (sb_free b n) N M.
Proof. intros b N M n Hn (HC & HB). unfold hs_cap, sb_free. cbn [sb_live sb_bytes sb_cap]. split; lia. Qed.

Lemma hs_cap_le : forall b N N' M, (N' <= N)%nat -> 0 <= M -> hs_cap b N M -> hs_cap b N' M.
Proof. intros b N N' M HN HS (HC & HB). apply inj_le in HN. split; [lia | nia]. Qed.

Lemma hs_cap_realloc : forall b N M k n, 0 <= k -> 0 <= n <= M -> hs_cap b (Datatypes.S N) M -> hs_cap (sb_realloc b k n) N M.
Proof.
  intros b N M k n Hk Hn (HC & HB). rewrite Nat2Z.inj_succ in HC, HB. unfold hs_cap, sb_realloc.
  cbn [sb_live sb_bytes sb_cap]. split; [lia | nia].
Qed.
