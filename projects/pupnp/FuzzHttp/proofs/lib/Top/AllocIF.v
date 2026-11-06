(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec Cells Step Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach.
Import ListNotations.
Local Open Scope Z_scope.

Definition round_up8 (x : Z) : Z := ((x + 7) / 8) * 8.

Section Blocks.
  Context {K : Type}.
  Definition block : Type := (K * Z * Z)%type.
  Definition blk_id (b : block) : K := fst (fst b).
  Definition blk_addr (b : block) : Z := snd (fst b).
  Definition blk_size (b : block) : Z := snd b.

  Definition in_block (LB : list block) (a : Z) : Prop :=
    exists b, In b LB /\ blk_addr b <= a < blk_addr b + blk_size b.

  Context (K_eqb : K -> K -> bool).
  Definition lb_remove (p : K) (LB : list block) : list block :=
    filter (fun b => negb (K_eqb (blk_id b) p)) LB.
End Blocks.
Arguments block K : clear implicits.

Section IF.
Context {HC : HasCeiling}.
Variable segs : list Segment.
Notation mem := (word -> option byte).

Record alloc_layout := mkAL {
  al_tp : Z;
  al_errno : Z;
  al_malloc_pc : Z;
  al_free_pc : Z;
  al_realloc_pc : Z;
  al_stack : Z;
  al_img : list (Z * Z);

  al_client_static : Z -> Z -> Prop
}.

Record alloc_if := mkAI {
  ai_L : alloc_layout;
  ai_K : Type;
  ai_K_eqb : ai_K -> ai_K -> bool;
  ai_K_eqb_eq : forall a b, ai_K_eqb a b = true <-> a = b;
  ai_PS : Type;

  RHEAP : ai_PS -> list (block ai_K) -> mem -> Prop;

  RENV : mem -> Z -> Prop;

  LINK : ai_PS -> list (block ai_K) -> Model -> Prop;
  ai_link_frame : forall s LB mo, LINK s LB mo -> m_halted mo = None /\ m_vm_lazy mo = [];

  ai_keep : ai_PS -> ai_PS -> Prop;
  ai_keep_refl : forall s, ai_keep s s;
  ai_keep_trans : forall s1 s2 s3, ai_keep s1 s2 -> ai_keep s2 s3 -> ai_keep s1 s3;

  ai_mrel : Model -> Model -> Prop;
  ai_mrel_refl : forall mo, ai_mrel mo mo;
  ai_mrel_trans : forall a b c, ai_mrel a b -> ai_mrel b c -> ai_mrel a c;
  ai_mrel_fs : forall mo mo', ai_mrel mo mo' -> m_fs mo' = m_fs mo /\ m_fds mo' = m_fds mo;

  ai_block_range : forall s LB m b, RHEAP s LB m -> In b LB ->
      0 < blk_addr b /\ blk_addr b mod 16 = 0 /\ 0 <= blk_size b
      /\ blk_addr b + blk_size b <= alloc_ceiling
      /\ Forall (fun w => blk_addr b + blk_size b <= fst w \/ snd w <= blk_addr b) (al_img ai_L);
  ai_blocks_disjoint : forall s LB m b1 b2, RHEAP s LB m -> In b1 LB -> In b2 LB -> b1 <> b2 ->
      blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1;
  ai_blocks_nodup : forall s LB m, RHEAP s LB m -> NoDup (map blk_id LB);

  ai_block_slack : forall s LB m b a, RHEAP s LB m -> In b LB ->
      blk_addr b <= a < round_up8 (blk_addr b + blk_size b) ->
      exists v, mrd segs m (wa a) = Some v;

  ai_heap_frame : forall s LB m m' W,
      RHEAP s LB m -> munch W m m' -> wmono segs m m' ->
      Forall (fun iv => alloc_ceiling <= fst iv
                        \/ (exists lo hi, al_client_static ai_L lo hi /\ lo <= fst iv /\ snd iv <= hi)
                        \/ (al_errno ai_L <= fst iv /\ snd iv <= al_errno ai_L + 4)
                        \/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)) W ->
      RHEAP s LB m';
  ai_env_frame : forall s LB m m' W B,
      RHEAP s LB m -> RENV m B -> munch W m m' -> wmono segs m m' ->
      Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= B)
                        \/ (exists lo hi, al_client_static ai_L lo hi /\ lo <= fst iv /\ snd iv <= hi)
                        \/ (al_errno ai_L <= fst iv /\ snd iv <= al_errno ai_L + 4)
                        \/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)) W ->
      RENV m' B;
  ai_heap_perm : forall s LB LB' m, RHEAP s LB m -> Permutation.Permutation LB LB' -> RHEAP s LB' m;
  ai_link_perm : forall s LB LB' mo, LINK s LB mo -> Permutation.Permutation LB LB' -> LINK s LB' mo
}.

End IF.
