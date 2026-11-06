(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: written for libreac/fuzz_scene's ASan+UBSan build (fuzz_scene.asan-ubsan); the twin of lib/A/ArmReadsCover.v. *)
(* arm_rows_cover_reads (the standing obligation of lib/AU/YD1g.v, header lines 12-17) for the 135 symbolic loads of the start-up
   walk. The load log of a Theorem Labs lane (scene-17bytes.md (sha256 a6186fbb7b08; internal record), 2026-10-29T06:08Z, on the start-up data
   at 8b7b8969d1a, which is lib/AU/YB01.v here) shows that no concrete start-up load reads one of the 17
   image bytes with no row in the const list (0x20d88..0x20d8b, 0x20dd0..0x20dd1, 0x20e28..0x20e2b, 0x20e40..0x20e46). It lists
   135 symbolic loads whose checker range still includes them; each reads through the page base 4096 * EVar k of an mmap'd
   region, k in {441, 274, 442, 615, 358, 357, 292}, the same variables as in fuzz_scene.asan. SCENE_MMAP_LOADS is that
   table (its image-B columns).
   Source of the fact: the hand-off certificate. For each region that the walked path of hand-off state h reads, the knowledge of
   HS_tfib h (lib/AU/YB01.v, HS_tfib_<h>_kn) has the entry KDisj (SA (ELit IMG_LO) 0) (ELit (IMG_TOP - IMG_LO)) (SA (4096 * EVar k) 0) (ELit L)
   (in the certificate's numerals: ELit 0x10000, ELit 0x5e9000), L = 4096, or 8192 for EVar 441 in states 8-13, 24-29 and 36-38:
   the region against the image [IMG_LO, IMG_TOP) = [0x10000, 0x5f9000) (lib/Reusable/YImgTop.v). arc_chk checks
   this by vm_compute. co_know of cs_ok (lib/Reusable/YA0e.v:195, read through ho_know, lib/Reusable/YA0j.v:214) makes every such
   entry true under the hand-off environment E (the meaning of KDisj: kentry_ok, lib/Reusable/YK0e.v:567). For 274, 357, 292, 615,
   441 and 442 the map bound vm_bound of YD1g.v:492 (co_bounds) gives the same result, but EVar 358 is not a map at the hand-off
   (it is the ghost TFIB_GHOST, YD1g.v:115), so only its KDisj entry covers it. The range floors of TFIB_RANGES alone do not.
   arm_mmap_off_image and arm_mmap_loads_off_image are about the hand-off state. arm_mmap_off_image_walk and
   arm_mmap_loads_off_image_walk carry them to the environment the load's own step runs in. That bridge is proved, not
   argued: each node of the walk continues with an environment E' that has env_agree (nxt cs) E E' (lib/Reusable/YA0e.v:1618),
   nxt does not decrease along the walk, so the steps from the load to the hand-off compose into one env_agree b (induction
   arc_walk_agree, over arc_walk_ok, the list of the walk's (counter, environment) steps); b is the load state's nxt, and
   EVar k is below it because the load's address base 4096 * EVar k is an expression of the load's state (arc_page_var_lt
   turns that state's vars_lt invariant into the hypothesis). arc_nxt_chk checks the hand-off end of the same bound. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.libreac.fuzz_scene.images Require Import AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YB12 YB1h YB01.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YP09 YK00 YK04 YA0i YA0n YK0g YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Open Scope Z_scope.
(* The page base of an mmap'd region, as the start-up walk's load addresses spell it (a_base of each load). *)
Definition arc_page (k : nat) : expr := EMd M_MUL (ELit 4096) (EVar k).
(* One symbolic start-up load of the load log: pc, page-base variable k (base arc_page k), offset from the base, width in
   bytes, and the hand-off states (indices into HS_tfib_list) whose walked path holds the load. *)
Record arc_load : Type := RL { rl_pc : Z; rl_var : nat; rl_off : Z; rl_width : Z; rl_holes : list nat }.
Definition ARC_H_ALL : list nat :=
[0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24;
25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 36; 37; 38; 39; 40; 41; 42; 43; 44; 45; 46; 47; 48; 49]%nat.
(* The path-hole sets of the load log. ARC_H_441: the paths of the one-page loads through arc_page 441; the musl window of
   these hand-off states holds (arc_page 441, 4096). *)
Definition ARC_H_441 : list nat := [0; 1; 4; 5; 16; 17; 20; 21; 32; 34; 40; 41; 44; 45; 48]%nat.
(* The paths of the loads through arc_page 442 and of part of the second-page loads through arc_page 441; the musl window
   of these states holds (arc_page 442, 4096) and (arc_page 441, 8192). *)
Definition ARC_H_442 : list nat := [8; 9; 24; 25; 36]%nat.
(* The paths of the other second-page loads through arc_page 441; the musl window of these states holds (arc_page 441,
   8192) RW and no other map. *)
Definition ARC_H_441W : list nat := [10; 11; 26; 27; 37]%nat.
Definition SCENE_MMAP_LOADS : list arc_load :=
[ RL 0x5b948 274 0 8 ARC_H_ALL; RL 0x5e9c8 274 0 8 ARC_H_ALL; RL 0x5e9e4 274 0 8 ARC_H_ALL; RL 0x5eab0 274 0 8 ARC_H_ALL;
  RL 0x5ec48 274 0 8 ARC_H_ALL; RL 0x5ecf8 274 0 8 ARC_H_ALL; RL 0x5ed20 274 0 8 ARC_H_ALL; RL 0x5ed28 274 0 8 ARC_H_ALL;
  RL 0x5e244 274 16 8 ARC_H_ALL; RL 0x5e408 274 16 8 ARC_H_ALL; RL 0x5e460 274 16 8 ARC_H_ALL; RL 0x5e4c4 274 16 8 ARC_H_ALL;
  RL 0x5e704 274 16 8 ARC_H_ALL; RL 0x5e728 274 16 8 ARC_H_ALL; RL 0x5e774 274 16 8 ARC_H_ALL; RL 0x5eadc 274 16 8 ARC_H_ALL;
  RL 0x5eaf8 274 16 8 ARC_H_ALL; RL 0x5eb48 274 16 8 ARC_H_ALL; RL 0x5c7f4 274 3168 1 ARC_H_ALL; RL 0x5e3c4 274 40 1 ARC_H_ALL;
  RL 0x5e41c 274 40 1 ARC_H_ALL; RL 0x5e480 274 40 1 ARC_H_ALL; RL 0x5e6c8 274 40 1 ARC_H_ALL; RL 0x5e730 274 40 1 ARC_H_ALL;
  RL 0x5eb10 274 40 1 ARC_H_ALL; RL 0x48ce0 274 48 8 ARC_H_ALL; RL 0x5e258 274 48 8 ARC_H_ALL; RL 0x48ce4 274 56 8 ARC_H_ALL;
  RL 0x5e25c 274 56 8 ARC_H_ALL; RL 0x5e4e8 274 72 8 ARC_H_ALL; RL 0x5e640 274 72 8 ARC_H_ALL; RL 0x5e240 274 8 8 ARC_H_ALL;
  RL 0x5e404 274 8 8 ARC_H_ALL; RL 0x5e45c 274 8 8 ARC_H_ALL; RL 0x5e4c0 274 8 8 ARC_H_ALL; RL 0x5e700 274 8 8 ARC_H_ALL;
  RL 0x5e724 274 8 8 ARC_H_ALL; RL 0x5e770 274 8 8 ARC_H_ALL; RL 0x5ead8 274 8 8 ARC_H_ALL; RL 0x5eaf4 274 8 8 ARC_H_ALL;
  RL 0x5eb4c 274 8 8 ARC_H_ALL; RL 0x6cde0 292 0 8 ARC_H_ALL; RL 0x6bae8 357 24 8 ARC_H_ALL; RL 0x6ec70 358 0 8 ARC_H_ALL;
  RL 0x6e9f0 358 24 8 ARC_H_ALL; RL 0x6ec84 358 8 8 ARC_H_ALL; RL 0x8d798 441 12 1 ARC_H_441; RL 0x8d2ac 441 13 1 ARC_H_441;
  RL 0x8d77c 441 13 1 ARC_H_441; RL 0x8d864 441 13 1 ARC_H_441; RL 0x8d5d0 441 24 1 ARC_H_441; RL 0x8d798 441 28 1 ARC_H_441;
  RL 0x8d2ac 441 29 1 ARC_H_441; RL 0x8d77c 441 29 1 ARC_H_441; RL 0x8d864 441 29 1 ARC_H_441; RL 0x8d5d0 441 40 1 ARC_H_441;
  RL 0x8d32c 441 4120 8 ARC_H_441W; RL 0x8d624 441 4120 8 ARC_H_442; RL 0x8d320 441 4128 8 ARC_H_441W; RL 0x8d354 441 4128 8 ARC_H_441W;
  RL 0x8d618 441 4128 8 ARC_H_442; RL 0x8d5cc 441 4136 8 ARC_H_442; RL 0x8d770 441 4136 8 ARC_H_442; RL 0x8d5b0 441 4144 4 ARC_H_442;
  RL 0x8d60c 441 4144 4 ARC_H_442; RL 0x8d29c 441 4152 8 ARC_H_442; RL 0x8d5e8 441 4152 8 ARC_H_442; RL 0x8d730 441 4152 8 ARC_H_442;
  RL 0x8d32c 441 4160 8 ARC_H_441W; RL 0x8d624 441 4160 8 ARC_H_442; RL 0x8d320 441 4168 8 ARC_H_441W; RL 0x8d354 441 4168 8 ARC_H_441W;
  RL 0x8d618 441 4168 8 ARC_H_442; RL 0x8d5cc 441 4176 8 ARC_H_442; RL 0x8d770 441 4176 8 ARC_H_442; RL 0x8d5b0 441 4184 4 ARC_H_442;
  RL 0x8d60c 441 4184 4 ARC_H_442; RL 0x8d29c 441 4192 8 ARC_H_442; RL 0x8d5e8 441 4192 8 ARC_H_442; RL 0x8d730 441 4192 8 ARC_H_442;
  RL 0x8d32c 441 4200 8 ARC_H_441W; RL 0x8d624 441 4200 8 ARC_H_442; RL 0x8d320 441 4208 8 ARC_H_441W; RL 0x8d354 441 4208 8 ARC_H_441W;
  RL 0x8d618 441 4208 8 ARC_H_442; RL 0x8d5cc 441 4216 8 ARC_H_442; RL 0x8d770 441 4216 8 ARC_H_442; RL 0x8d5b0 441 4224 4 ARC_H_442;
  RL 0x8d60c 441 4224 4 ARC_H_442; RL 0x8d29c 441 4232 8 ARC_H_442; RL 0x8d5e8 441 4232 8 ARC_H_442; RL 0x8d730 441 4232 8 ARC_H_442;
  RL 0x8d348 441 4240 8 ARC_H_441W; RL 0x8d624 441 4240 8 ARC_H_442; RL 0x8d6ac 441 4240 8 ARC_H_441W; RL 0x8d618 441 4248 8 ARC_H_442;
  RL 0x8d6a0 441 4248 8 ARC_H_441W; RL 0x8d5cc 441 4256 8 ARC_H_442; RL 0x8d770 441 4256 8 ARC_H_442; RL 0x8d5b0 441 4264 4 ARC_H_442;
  RL 0x8d60c 441 4264 4 ARC_H_442; RL 0x8d544 441 4272 8 ARC_H_442; RL 0x8d5e8 441 4272 8 ARC_H_442; RL 0x8d730 441 4272 8 ARC_H_442;
  RL 0x8d798 441 44 1 ARC_H_441; RL 0x8d2ac 441 45 1 ARC_H_441; RL 0x8d77c 441 45 1 ARC_H_441; RL 0x8d864 441 45 1 ARC_H_441;
  RL 0x8d5d0 441 56 1 ARC_H_441; RL 0x8d798 441 60 1 ARC_H_441; RL 0x8d77c 441 61 1 ARC_H_441; RL 0x8d864 441 61 1 ARC_H_441;
  RL 0x8d5d0 441 8 1 ARC_H_441; RL 0x8d798 442 12 1 ARC_H_442; RL 0x8d2ac 442 13 1 ARC_H_442; RL 0x8d77c 442 13 1 ARC_H_442;
  RL 0x8d864 442 13 1 ARC_H_442; RL 0x8d5d0 442 24 1 ARC_H_442; RL 0x8d798 442 28 1 ARC_H_442; RL 0x8d2ac 442 29 1 ARC_H_442;
  RL 0x8d77c 442 29 1 ARC_H_442; RL 0x8d864 442 29 1 ARC_H_442; RL 0x8d5d0 442 40 1 ARC_H_442; RL 0x8d798 442 44 1 ARC_H_442;
  RL 0x8d2ac 442 45 1 ARC_H_442; RL 0x8d77c 442 45 1 ARC_H_442; RL 0x8d864 442 45 1 ARC_H_442; RL 0x8d5d0 442 56 1 ARC_H_442;
  RL 0x8d798 442 60 1 ARC_H_442; RL 0x8d77c 442 61 1 ARC_H_442; RL 0x8d864 442 61 1 ARC_H_442; RL 0x8d5d0 442 8 1 ARC_H_442;
  RL 0x4307c 615 0 8 ARC_H_ALL; RL 0x431a4 615 0 8 ARC_H_ALL; RL 0x41944 615 8 8 ARC_H_ALL ].
Lemma scene_mmap_loads_len : length SCENE_MMAP_LOADS = 135%nat.
Proof. reflexivity. Qed.
Lemma scene_mmap_vars : forall r, In r SCENE_MMAP_LOADS -> In (rl_var r) [441; 274; 442; 615; 358; 357; 292]%nat.
Proof.
intros r Hr.
assert (X : forallb (fun r => existsb (Nat.eqb (rl_var r)) [441; 274; 442; 615; 358; 357; 292]%nat) SCENE_MMAP_LOADS = true)
by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) X r Hr) as Y. apply existsb_exists in Y as (k & Hk & Hkk).
apply Nat.eqb_eq in Hkk. rewrite Hkk. exact Hk.
Qed.
(* arc_cover k off w K: K is KDisj (image) (region at arc_page k of length L) with the load's bytes [off, off + w) inside
   the region. The image is (SA (ELit IMG_LO) 0, ELit (IMG_TOP - IMG_LO)), that is [IMG_LO, IMG_TOP). L <= IMG_LO keeps a
   wrapped address of the region below IMG_LO. *)
Definition arc_disj4 (k : nat) (off w : Z) (a1 : saddr) (n1 : expr) (a2 : saddr) (n2 : expr) : bool :=
match n1, n2 with
| ELit z1, ELit L =>
expr_eqb (a_base a1) (ELit IMG_LO) && (a_off a1 =? 0) && (z1 =? IMG_TOP - IMG_LO)
&& expr_eqb (a_base a2) (arc_page k) && (a_off a2 =? 0)
&& (0 <=? off) && (0 <? w) && (off + w <=? L) && (L <=? IMG_LO)
| _, _ => false
end%bool.
Definition arc_cover (k : nat) (off w : Z) (K : kentry) : bool :=
match K with KDisj a1 n1 a2 n2 => arc_disj4 k off w a1 n1 a2 n2 | _ => false end.
Definition arc_row_ok (kn0 : list kentry) (r : arc_load) : bool := existsb (arc_cover (rl_var r) (rl_off r) (rl_width r)) kn0.
Definition arc_on_path (h : nat) (r : arc_load) : bool := existsb (Nat.eqb h) (rl_holes r).
Definition arc_state_ok (h : nat) (cs : acs) : bool :=
forallb (fun r => negb (arc_on_path h r) || arc_row_ok (kn cs) r)%bool SCENE_MMAP_LOADS.
(* arc_states P h0 l: P holds of every state of l with its index, h0 for the head. *)
Fixpoint arc_states (P : nat -> acs -> bool) (h0 : nat) (l : list acs) : bool :=
match l with [] => true | cs :: l' => (P h0 cs && arc_states P (Datatypes.S h0) l')%bool end.
Lemma arc_states_nth : forall P l h0 i cs, arc_states P h0 l = true -> nth_error l i = Some cs -> P (h0 + i)%nat cs = true.
Proof.
intros P l. induction l as [|c l IH]; intros h0 i cs H Hi; [destruct i; discriminate Hi|].
cbn [arc_states] in H. apply andb_prop in H as [H1 H2]. destruct i as [|i]; cbn [nth_error] in Hi.
- injection Hi as <-. rewrite Nat.add_0_r. exact H1.
- replace (h0 + Datatypes.S i)%nat with (Datatypes.S h0 + i)%nat by lia. exact (IH (Datatypes.S h0) i cs H2 Hi).
Qed.
Lemma arc_states_hs : forall P h0 cs, arc_states P 0 HS_tfib_list = true -> HS_tfib h0 = Some cs -> P h0 cs = true.
Proof.
intros P h0 cs HP Hh. assert (Hn : nth_error HS_tfib_list h0 = Some cs) by exact Hh.
pose proof (arc_states_nth P HS_tfib_list 0 h0 cs HP Hn) as X. rewrite Nat.add_0_l in X. exact X.
Qed.
(* Every load of the table, in every hand-off state on its path, has its image-disjointness entry in that state's knowledge. *)
Lemma arc_chk : arc_states arc_state_ok 0 HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.
Lemma arc_hs_row : forall h cs r, HS_tfib h = Some cs -> In r SCENE_MMAP_LOADS -> In h (rl_holes r) -> arc_row_ok (kn cs) r = true.
Proof.
intros h cs r Hh Hr Hin. pose proof (arc_states_hs arc_state_ok h cs arc_chk Hh) as X.
unfold arc_state_ok in X. pose proof (proj1 (forallb_forall _ _) X r Hr) as Y.
assert (P : arc_on_path h r = true) by (unfold arc_on_path; apply existsb_exists; exists h; split; [exact Hin | apply Nat.eqb_refl]).
cbv beta in Y. rewrite P in Y. exact Y.
Qed.
(* The fresh-variable counter nxt of each hand-off state is above every page-base variable the table reads on that state's
   path. nxt does not decrease along the walk, so this is the hand-off end of the bound k < nxt; at the load the bound comes
   from the load state's own vars_lt invariant (arc_page_var_lt below), and the walk theorems take it as a hypothesis. *)
Definition arc_var_lt_nxt (h : nat) (cs : acs) : bool :=
forallb (fun r => negb (arc_on_path h r) || Nat.ltb (rl_var r) (nxt cs))%bool SCENE_MMAP_LOADS.
Lemma arc_nxt_chk : arc_states arc_var_lt_nxt 0 HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.
Lemma arc_hs_var_lt : forall h cs r, HS_tfib h = Some cs -> In r SCENE_MMAP_LOADS -> In h (rl_holes r) -> (rl_var r < nxt cs)%nat.
Proof.
intros h cs r Hh Hr Hin. pose proof (arc_states_hs arc_var_lt_nxt h cs arc_nxt_chk Hh) as X.
unfold arc_var_lt_nxt in X. pose proof (proj1 (forallb_forall _ _) X r Hr) as Y.
assert (P : arc_on_path h r = true) by (unfold arc_on_path; apply existsb_exists; exists h; split; [exact Hin | apply Nat.eqb_refl]).
cbv beta in Y. rewrite P in Y. exact (proj1 (Nat.ltb_lt (rl_var r) (nxt cs)) Y).
Qed.
Lemma arc_cover_sound : forall k off w K, arc_cover k off w K = true ->
exists L, K = KDisj (SA (ELit IMG_LO) 0) (ELit (IMG_TOP - IMG_LO)) (SA (arc_page k) 0) (ELit L) /\ 0 <= off /\ 0 < w /\ off + w <= L <= IMG_LO.
Proof.
intros k off w K H. destruct K; cbn [arc_cover] in H; try discriminate H.
lazymatch type of H with
| arc_disj4 _ _ _ ?a1 ?n1 ?a2 ?n2 = true =>
destruct a1 as [b1 o1]; destruct a2 as [b2 o2];
destruct n1 as [z1| | | | | | |]; [| cbn in H; discriminate H ..];
destruct n2 as [L| | | | | | |]; [| cbn in H; discriminate H ..]
end.
cbn [arc_disj4 a_base a_off] in H.
apply andb_prop in H as [H X9]. apply andb_prop in H as [H X8]. apply andb_prop in H as [H X7]. apply andb_prop in H as [H X6].
apply andb_prop in H as [H X5]. apply andb_prop in H as [H X4]. apply andb_prop in H as [H X3]. apply andb_prop in H as [X1 X2].
apply expr_eqb_eq in X1. apply expr_eqb_eq in X4. apply Z.eqb_eq in X2. apply Z.eqb_eq in X3. apply Z.eqb_eq in X5.
apply Z.leb_le in X6. apply Z.ltb_lt in X7. apply Z.leb_le in X8. apply Z.leb_le in X9.
subst b1 o1 z1 b2 o2. exists L. split; [reflexivity | lia].
Qed.
(* The walk from the load's step to the hand-off state, in the shape the walk relations give it: each node continues with an
   environment E' that has env_agree (nxt cs) E E' (lib/Reusable/YA0e.v:1618), and nxt does not decrease along the walk, so
   every step's counter is at least the counter b of the load's own state. steps lists the (counter, environment) of the
   steps from the load's step to the hand-off state, in walk order; arc_walk_end is the hand-off environment. *)
Fixpoint arc_walk_end (E0 : env) (steps : list (nat * env)) : env :=
match steps with [] => E0 | (_, E1) :: l => arc_walk_end E1 l end.
Fixpoint arc_walk_ok (b : nat) (E0 : env) (steps : list (nat * env)) : Prop :=
match steps with
| [] => True
| (b1, E1) :: l => (b <= b1)%nat /\ env_agree b1 E0 E1 /\ arc_walk_ok b E1 l
end.
(* The induction over the walked path: the steps compose into one env_agree b from the load's environment to the hand-off's. *)
Lemma arc_walk_agree : forall steps b E0, arc_walk_ok b E0 steps -> env_agree b E0 (arc_walk_end E0 steps).
Proof.
induction steps as [|[b1 E1] l IH]; intros b E0 H; cbn [arc_walk_end arc_walk_ok] in H |- *.
- apply env_agree_refl.
- destruct H as (Hle & Hag & Hrest).
exact (env_agree_trans b E0 E1 (arc_walk_end E1 l) (env_agree_le b b1 E0 E1 Hag Hle) (IH b E1 Hrest)).
Qed.
(* A page base has the same value in two environments that agree below a bound above its variable. *)
Lemma arc_page_agree : forall b (E1 E2 : env) k, env_agree b E1 E2 -> (k < b)%nat ->
uE E1 (arc_page k) = uE E2 (arc_page k).
Proof.
intros b E1 E2 k Hag Hk. unfold uE.
rewrite (YK0f.edenot_agree b E1 E2 (arc_page k) Hag (proj2 (Nat.ltb_lt k b) Hk)). reflexivity.
Qed.
(* The bound k < b in the form a state's vars_lt invariant gives it: the load's address base 4096 * EVar k is an expression
   of the load's state, so APG.expr_vars_lt (nxt cs) of it is true, which is k < nxt cs. *)
Lemma arc_page_var_lt : forall b k, APG.expr_vars_lt b (arc_page k) = true -> (k < b)%nat.
Proof. intros b k H. exact (proj1 (Nat.ltb_lt k b) H). Qed.

Section t. Context {fx : YK11.FPState}.
Section a0.
(* The hand-off state ch at main and its environment E, as lib/AU/YD1g.v's construction of tfib_ARm quantifies over them. *)
Variables (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput).
Variable h : nat.
Variables (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis Hch : HS_tfib h = Some ch.
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
#[local] Notation uid := (in_uid inp).
#[local] Notation hw := (in_hwcap inp).
#[local] Notation SINV := (YA02.SINV0 TPH sp rdraw brk argv envp uid hw).
#[local] Notation argH := (YA02.argH0 TPH sp rdraw argv envp uid hw).
#[local] Notation TOP := (YA02.TOP sp).
#[local] Notation LIM := YA02.LIMIT.
Hypothesis HC : cs_ok TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model.
#[local] Notation u := (uE E).
Lemma arc_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (edenot E (ELit z)) = z.
Proof. intros z Hz. cbn [edenot]. rewrite u64_lit by lia. reflexivity. Qed.
Lemma arc_bound : forall e, 0 <= u e < 2 ^ 64.
Proof. intros e. unfold uE. pose proof (bv_unsigned_in_range 64 (edenot E e)) as H. change (bv_modulus 64) with (2 ^ 64) in H. lia. Qed.
(* The source: co_know (cs_ok) makes every KDisj of ch's knowledge true under E. *)
Lemma arc_row_disj : forall r, In r SCENE_MMAP_LOADS -> In h (rl_holes r) ->
exists L, 0 <= rl_off r /\ 0 < rl_width r /\ rl_off r + rl_width r <= L <= IMG_LO
/\ (u (arc_page (rl_var r)) + L <= IMG_LO \/ IMG_TOP <= u (arc_page (rl_var r))).
Proof.
intros r Hr Hin. pose proof (arc_hs_row h ch r Hch Hr Hin) as X. unfold arc_row_ok in X.
apply existsb_exists in X as (K & HK & HD). destruct (arc_cover_sound _ _ _ K HD) as (L & -> & H1 & H2 & H3).
pose proof (proj1 (Forall_forall _ _) (ho_know _ _ _ _ _ _ _ _ _ _ _ _ HC) _ HK) as D.
assert (D' : estart E (SA (ELit IMG_LO) 0) + elenZ E (ELit (IMG_TOP - IMG_LO)) <= estart E (SA (arc_page (rl_var r)) 0)
\/ estart E (SA (arc_page (rl_var r)) 0) + elenZ E (ELit L) <= estart E (SA (ELit IMG_LO) 0)) by exact D.
clear D. unfold estart, elenZ in D'. cbn [a_base a_off] in D'.
rewrite (arc_lit IMG_LO), (arc_lit (IMG_TOP - IMG_LO)), (arc_lit L) in D' by lia.
change (bv_unsigned (edenot E (arc_page (rl_var r)))) with (u (arc_page (rl_var r))) in D'.
exists L. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. lia.
Qed.
(* Each page base 4096 * EVar k of the table (k among the 7 of scene_mmap_vars), with the length its load uses from that base
   (offset + width), lies outside the image [IMG_LO, IMG_TOP), in every hand-off state on the load's walked path. *)
Theorem arm_mmap_off_image : forall r, In r SCENE_MMAP_LOADS -> In h (rl_holes r) ->
u (arc_page (rl_var r)) + (rl_off r + rl_width r) <= IMG_LO \/ IMG_TOP <= u (arc_page (rl_var r)).
Proof.
intros r Hr Hin. destruct (arc_row_disj r Hr Hin) as (L & H1 & H2 & H3 & H4). lia.
Qed.
(* Every byte each of the 135 symbolic loads reads, at address (base + off + i) mod 2^64, lies outside [IMG_LO, IMG_TOP). *)
Theorem arm_mmap_loads_off_image : forall r, In r SCENE_MMAP_LOADS -> In h (rl_holes r) ->
forall i, 0 <= i < rl_width r ->
(u (arc_page (rl_var r)) + rl_off r + i) mod 2 ^ 64 < IMG_LO
\/ IMG_TOP <= (u (arc_page (rl_var r)) + rl_off r + i) mod 2 ^ 64.
Proof.
intros r Hr Hin i Hi. destruct (arc_row_disj r Hr Hin) as (L & H1 & H2 & H3 & H4).
pose proof (arc_bound (arc_page (rl_var r))) as U. set (b := u (arc_page (rl_var r))) in *.
change (2 ^ 64) with 18446744073709551616 in U |- *.
assert (Hx : 0 <= b + rl_off r + i < b + L) by lia.
destruct (Z_lt_le_dec (b + rl_off r + i) 18446744073709551616) as [Hs|Hs].
- rewrite (Z.mod_small (b + rl_off r + i) 18446744073709551616) by lia. lia.
- assert (Hm : (b + rl_off r + i) mod 18446744073709551616 = b + rl_off r + i - 18446744073709551616).
{ symmetry. apply (Z.mod_unique _ _ 1); [left; lia | ring]. }
rewrite Hm. clear Hm. lia.
Qed.
(* The bridge, over the environment the load's step runs in. Eld is that environment, b the load state's fresh-variable
   counter nxt (the hypothesis rl_var r < b is what the load state's vars_lt invariant gives through arc_page_var_lt:
   the load's address base is 4096 * EVar (rl_var r), an expression of that state), and steps is the walk from the load's
   step to this hand-off state. Then EVar (rl_var r), hence the load's page base, has the same value at the load as at the
   hand-off. *)
Theorem arm_mmap_var_walk : forall r, In r SCENE_MMAP_LOADS ->
forall (Eld : env) (steps : list (nat * env)) (b : nat),
(rl_var r < b)%nat -> arc_walk_ok b Eld steps -> arc_walk_end Eld steps = E ->
ev Eld (rl_var r) = ev E (rl_var r) /\ uE Eld (arc_page (rl_var r)) = u (arc_page (rl_var r)).
Proof.
intros r Hr Eld steps b Hk Hw He.
pose proof (arc_walk_agree steps b Eld Hw) as Hag. rewrite He in Hag.
split; [destruct Hag as [Hv _]; exact (Hv (rl_var r) Hk) | exact (arc_page_agree b Eld E (rl_var r) Hag Hk)].
Qed.
(* arm_mmap_off_image at the load's environment. *)
Theorem arm_mmap_off_image_walk : forall r, In r SCENE_MMAP_LOADS -> In h (rl_holes r) ->
forall (Eld : env) (steps : list (nat * env)) (b : nat),
(rl_var r < b)%nat -> arc_walk_ok b Eld steps -> arc_walk_end Eld steps = E ->
uE Eld (arc_page (rl_var r)) + (rl_off r + rl_width r) <= IMG_LO \/ IMG_TOP <= uE Eld (arc_page (rl_var r)).
Proof.
intros r Hr Hin Eld steps b Hk Hw He.
destruct (arm_mmap_var_walk r Hr Eld steps b Hk Hw He) as [_ Hu]. rewrite Hu.
exact (arm_mmap_off_image r Hr Hin).
Qed.
(* arm_mmap_loads_off_image at the load's environment: every byte the load reads, at the address its own step computes,
   lies outside [IMG_LO, IMG_TOP). *)
Theorem arm_mmap_loads_off_image_walk : forall r, In r SCENE_MMAP_LOADS -> In h (rl_holes r) ->
forall (Eld : env) (steps : list (nat * env)) (b : nat),
(rl_var r < b)%nat -> arc_walk_ok b Eld steps -> arc_walk_end Eld steps = E ->
forall i, 0 <= i < rl_width r ->
(uE Eld (arc_page (rl_var r)) + rl_off r + i) mod 2 ^ 64 < IMG_LO
\/ IMG_TOP <= (uE Eld (arc_page (rl_var r)) + rl_off r + i) mod 2 ^ 64.
Proof.
intros r Hr Hin Eld steps b Hk Hw He i Hi.
destruct (arm_mmap_var_walk r Hr Eld steps b Hk Hw He) as [_ Hu]. rewrite Hu.
exact (arm_mmap_loads_off_image r Hr Hin i Hi).
Qed.
End a0.
End t.
