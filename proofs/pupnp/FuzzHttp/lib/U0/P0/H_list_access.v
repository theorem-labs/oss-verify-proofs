(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs HU_list_kit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Ltac sstep := step; fix_lit_store.

Definition ListHead_entry := 0x1627c%Z.
Definition ListNext_entry := 0x162a4%Z.
Definition ListInit_entry := 0x16078%Z.
Definition FreeListInit_entry := 0x1639c%Z.

Definition ListHead_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (first size : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if (size =? 0)%Z then 0 else first)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m (seg_rom rsegs)
    /\ munch [] m m /\ wmono rsegs m m /\ mem_inv rsegs m.

Definition ListHead_stmt : Prop :=
  forall (L first last size flh fk ffree fcmp : Z),
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells rsegs m L (llist_cells first last size flh fk ffree fcmp) ->
  L <> 0%Z -> (0 <= size < 2^63)%Z -> (0 <= first < 2^64)%Z ->
  (L mod 8 = 0)%Z -> mem_inv rsegs m -> a0 = wz L ->
  evt rsegs (ListHead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc first size m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ListHead_entry) fc None m (seg_rom rsegs)).

Lemma ListHead_spec : ListHead_stmt.
Proof.
  intros until m. intros LC NZ SZ FR AL MI ->. unfold ListHead_entry.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (rw_cells_bound rsegs _ _ _ LC) as BL. cbn [cells_size csize Nat.add llist_cells] in BL.
  unfold llist_cells in LC.
  step. if_cases K; zify_cond K; condn K. { exfalso. lia. }
  ub_align.
  step. step. if_cases K2; zify_cond K2; condn K2.
  - step. step. subst size. unfold ListHead_post. cbn [Z.eqb]. finish.
  - step. step. unfold ListHead_post. destruct (Z.eqb_spec size 0); [lia|]. finish.
Qed.

Definition listnext_expr (nx T : Z) : Z :=
  Z.land ((Z.b2z (Z.lxor nx T <? 1) + -1) mod 18446744073709551616) nx.

Lemma listnext_eval : forall nx T, (0 <= nx < 2^64)%Z -> (0 <= T < 2^64)%Z ->
  listnext_expr nx T = (if (nx =? T)%Z then 0 else nx)%Z.
Proof.
  intros nx T Hn HT. unfold listnext_expr.
  pose proof (zr_lxor nx T Hn HT) as RX. unfold inr64 in RX.
  destruct (Z.eqb_spec nx T) as [->|NE].
  - rewrite Z.lxor_nilpotent. cbn. reflexivity.
  - destruct (Z.ltb_spec0 (Z.lxor nx T) 1) as [LT|GE].
    + exfalso. apply NE. apply (proj1 (zb_lxor_eq0 _ _)). lia.
    + cbn [Z.b2z]. change ((0 + -1) mod 18446744073709551616)%Z with (Z.ones 64).
      rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. exact Hn.
Qed.

Definition ListNext_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L nx : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if (nx =? L + 24)%Z then 0 else nx)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m (seg_rom rsegs)
    /\ munch [] m m /\ wmono rsegs m m /\ mem_inv rsegs m.

Definition ListNext_stmt : Prop :=
  forall (L N pv nx it : Z),
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells rsegs m N (node_cells pv nx it) ->
  L <> 0%Z -> N <> 0%Z -> (0 <= nx < 2^64)%Z -> (0 < L /\ L + 96 < 2^64)%Z ->
  (N mod 8 = 0)%Z -> (L mod 8 = 0)%Z -> mem_inv rsegs m -> a0 = wz L -> a1 = wz N ->
  evt rsegs (ListNext_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L nx m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ListNext_entry) fc None m (seg_rom rsegs)).

Lemma ListNext_spec : ListNext_stmt.
Proof.
  intros until m. intros NC LNZ NNZ NX LR AL ALL MI -> ->. unfold ListNext_entry.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (rw_cells_bound rsegs _ _ _ NC) as BN. cbn [cells_size csize Nat.add node_cells] in BN.
  unfold node_cells in NC.
  zstep. zstep. if_cases K; zify_cond K; condn K. { exfalso; lia. }
  zstep. if_cases K2; zify_cond K2; condn K2. { exfalso; lia. }
  zstep. ub_align.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  change (Z.land _ nx) with (listnext_expr nx (L + 24)). rewrite listnext_eval by lia.
  finish.
Qed.

Definition FreeListInit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (FL esz mx : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(FL, FL + 24)%Z] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' FL [C8 (wz 0); C8 (wz esz); C4 (wz mx); C4 (wz 0)].

Definition FreeListInit_stmt : Prop :=
  forall (FL esz mx : Z) (junk : list byte),
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells rsegs m FL [CB 24%nat junk] -> FL <> 0%Z -> (0 <= esz < 2^64)%Z -> (0 <= mx < 2^31)%Z ->
  (FL mod 8 = 0)%Z -> mem_inv rsegs m -> a0 = wz FL -> a1 = wz esz -> a2 = wz mx ->
  evt rsegs (FreeListInit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FL esz mx m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz FreeListInit_entry) fc None m (seg_rom rsegs)).

Lemma FreeListInit_spec : FreeListInit_stmt.
Proof.
  intros until m. intros FC NZ E1 E2 AL MI -> -> ->. unfold FreeListInit_entry.
  pose proof (munch_refl [(FL, FL + 24)%Z] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (rw_cells_bound rsegs _ _ _ FC) as BN. cbn [cells_size csize Nat.add] in BN.
  step. if_cases K; zify_cond K; condn K. { exfalso; lia. }
  sstep. ub_align. sstep. sstep. sstep. sstep. sstep.
  rewrite land7_mod8, AL. finish.
Qed.

Definition ListInit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L fcmp ffree : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (L, L + 96)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' (bv_unsigned sp - 16) (bv_unsigned sp)
    /\ rw_cells rsegs m' L (llist_cells (L + 24) L 0 0 0 ffree fcmp).

Definition ListInit_stmt : Prop :=
  forall (L fcmp ffree : Z) (junk : list byte),
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells rsegs m L [CB 96%nat junk] -> L <> 0%Z -> (0 <= fcmp < 2^64)%Z -> (0 <= ffree < 2^64)%Z ->
  stk rsegs m (bv_unsigned sp - 16) (bv_unsigned sp) -> (64 <= bv_unsigned sp)%Z ->
  (L + 96 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= L)%Z ->
  (L mod 8 = 0)%Z -> mem_inv rsegs m -> a0 = wz L -> a1 = wz fcmp -> a2 = wz ffree ->
  evt rsegs (ListInit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L fcmp ffree m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ListInit_entry) fc None m (seg_rom rsegs)).

Lemma ListInit_spec : ListInit_stmt.
Proof.
  intros until m. intros LC NZ R1 R2 ST SPLO SEP AL MI -> -> ->. unfold ListInit_entry.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (L, L + 96)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (rw_cells_bound rsegs _ _ _ LC) as BN. cbn [cells_size csize Nat.add] in BN.
  step. if_cases K; zify_cond K; condn K. { exfalso; lia. }
  ub_align.
  carve_frame 16%nat ST.
  sstep. sstep. sstep. sstep. sstep. sstep. sstep. sstep. sstep. sstep. sstep. sstep.

  destruct (rw_cells_take3 rsegs _ L [CB 48 (firstn 48 junk); C8 (Z_to_bv 64 0)] [CB 24 (firstn 24 (skipn 56 junk))]
              [C8 (Z_to_bv 64 ffree); C8 (Z_to_bv 64 fcmp)] LC) as (LC1 & LC2 & LC3). clear LC.
  cbn [cells_size csize Nat.add] in LC2, LC3.
  replace (L + Z.of_nat 56)%Z with (L + 56)%Z in LC2 by lia.
  replace (L + Z.of_nat 56 + Z.of_nat 24)%Z with (L + 80)%Z in LC3 by lia.
  call (FreeListInit_spec (L + 56)%Z 24%Z 100%Z).
  1:{ exact LC2. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact MI. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  sstep. sstep. sstep. sstep. sstep. sstep. sstep.
  sstep. sstep. sstep. sstep.
  pose proof (rw_cells_put3 rsegs _ L _ _ _ LC1 ltac:(cbn [cells_size csize Nat.add]; replace (L + Z.of_nat 56)%Z with (L + 56)%Z by lia; exact POST)
                ltac:(cbn [cells_size csize Nat.add]; replace (L + Z.of_nat 56 + Z.of_nat 24)%Z with (L + 80)%Z by lia; exact LC3)) as LC.
  cbn [app] in LC. clear LC1 POST LC3.
  release_frame FR ST (bv_unsigned sp).
  unfold ListInit_post, llist_cells, LISTNODE_SIZEOF, FREELISTSIZE. finish.
Qed.
