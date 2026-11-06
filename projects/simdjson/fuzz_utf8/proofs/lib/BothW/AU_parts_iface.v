(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessU ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface F_apoison AAnnot_iface APoisonR_iface.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import AU_kit AU_iface AHarnessU_iface.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition AOPNEW : Z := 0x16adc4.       (* [comment removed for export] *)
Definition AOPDEL : Z := 0x10c514.       (* [comment removed for export] *)
Definition AOPDEL_SZ : Z := 0x10c518.    (* [comment removed for export] *)
Definition AMEMSET_I : Z := 0x7fe90.     (* [comment removed for export] *)
Definition OPNEW_STACK_A : Z := 16 + AMALLOC_STACK.            (* [comment removed for export] *)

(* [comment removed for export] *)
Definition hrt_cells (m : amem) : Prop :=
     rw_cells bsegs m 0x1788d8 [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m 0x20ab18 [C4 (Z_to_bv 64 0)].

Section Stmts.
Variable AI : AMallocIface.
Notation CI := (aci AI).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition achunk_kind_ok (ch : achunk) (n : Z) : Prop :=
  match ch with CPrim _ _ => is_primary n = true | CSec _ _ _ => is_primary n = false end.

Definition annot_grow_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (A cap lo : Z) (m : amem) (st : astate) (RNG : footprint) (r : astate) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => r = st /\ fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - ANNOT_STACK, bv_unsigned sp); (shad A, shad A + shlen (rup8 cap))] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (shad A) [CB (Z.to_nat (cap / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (cap / 8)))]
    /\ (cap mod 8 <> 0 -> rw_cells bsegs m' (shad A + cap / 8) [C1 (Z_to_bv 8 (cap mod 8))]).

Definition annot_grow_stmtA : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z)
         (st : astate) (p : AsanCtrl.aptr) (ch : achunk) (A cap : Z) (junk : list byte) (sb : byte),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - ANNOT_STACK ->
  poison_cells m -> annot_cells m -> artcells m ->
  premap_cells m -> (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 (A + cap) -> a2 = Z_to_bv 64 A -> a3 = Z_to_bv 64 (A + cap) ->
  ablock_range A cap -> 0 < cap <= AREQMAX ->
  (* [comment removed for export] *)
  (a_live st) !! p = Some ch -> chunk_size ch = cap -> (is_primary cap = false -> A = chunk_user_beg ch) ->
  achunk_kind_ok ch cap ->
  (* [comment removed for export] *)
  rw_cells bsegs m (shad A) [CB (Z.to_nat (cap / 8)) junk] ->
  (cap mod 8 <> 0 -> rw_cells bsegs m (shad A + cap / 8) [C1 sb] /\ end_byte_ok cap sb) ->
  (* [comment removed for export] *)
  (exists RLO RHI, RLO mod 4096 = 0 /\ RHI mod 4096 = 0 /\ RLO + 64 <= A /\ A + cap + 64 <= RHI
       /\ rng RNG (shad RLO) (shlen (RHI - RLO)) /\ wr_at bsegs m (shad RLO) (shlen (RHI - RLO))) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad A) (shlen (rup8 cap)) ->
  implS bsegs RNG (aembed ATOP (aannotate st p cap 0 cap))
        (epostF (annot_grow_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc A cap lo m st RNG))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            FR (Z_to_bv 64 AANNOT) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Lemma aannotate_shrink_ret : forall st p ch cap,
  (a_live st) !! p = Some ch -> 0 < cap <= 2^40 -> aannotate st p cap cap 0 = aret st.
Proof.
  intros st p ch cap L HC. unfold aannotate. rewrite L.
  replace ((0 <=? cap) && (cap <=? cap) && (0 <=? 0) && (0 <=? cap))%bool with true
    by (symmetry; rewrite !Bool.andb_true_iff, !Z.leb_le; lia).
  cbn [negb]. replace (2 ^ 40 <? cap) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (AsanCtrl.rdn cap 8 <? Z.min cap 0) with false
    by (symmetry; apply Z.ltb_ge; unfold AsanCtrl.rdn; rewrite Z.min_r by lia; Z.div_mod_to_equations; lia).
  rewrite Bool.andb_false_r. cbn [negb]. replace (cap <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition opnew_postA (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (s : APS) (LB : list ablock) (n lo : Z) (m : amem)
    (p : AsanCtrl.aptr) (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (A : Z) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ aps_rest s' = aps_rest s
    /\ ablock_range A n
    /\ AHEAP AI L RNG' (aps_m s') (HB p A n :: LB) m'
    /\ rw_cells bsegs m' A [CB (Z.to_nat n) junk]
    /\ rng RNG' A n /\ rng RNG' (shad A) (shlen (n + 7)).

Definition opnew_stmtA : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem)
         (s : APS) (LB : list ablock) (n lo : Z),
  AHEAP AI L RNG (aps_m s) LB m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - OPNEW_STACK_A ->
  bv_unsigned sp < al_top L -> bv_unsigned sp mod 16 = 0 ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 n -> 0 < n <= AREQMAX ->
  In [AMALLOC_PC; AOPNEW_RET] (al_U L) ->
  rng RNG lo (al_top L - lo) ->
  aps_ok L s ->                                        (* [comment removed for export] *)
  implMA RNG (HarnessU.opnew amalloc_M (new_handlerA AAllocAsan) n) s
         (opnew_postA L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB n lo m)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (Z_to_bv 64 AOPNEW) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Definition opdelete_stmtA_at (entry : Z) : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem)
         (s : APS) (LB : list ablock) (p : AsanCtrl.aptr) (A n lo : Z) (tr : list Z),
  AHEAP AI L RNG (aps_m s) LB m -> In (HB p A n) LB ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  bv_unsigned sp + 16 < al_top L ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  uchain m (al_top L) AFREE_PC (bv_unsigned sp) (bv_unsigned s0) UDEPTH tr ->
  In (AFREE_PC :: bv_unsigned ra :: tr) (al_U L) ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC -> (length tr <= 28)%nat ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (al_top L - lo) ->
  aps_ok L s ->                                               (* [comment removed for export] *)
  implMA RNG (HarnessU.opdelete afree_M p) s
    (fun _ s' RNG' ms' => aps_rest s' = aps_rest s
       /\ afree_post CI (AHEAP AI) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc (aps_m s) LB p lo m (aps_m s') RNG' ms')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 entry) fc None m (seg_rom bsegs)).
Definition opdelete_stmtA : Prop := opdelete_stmtA_at AOPDEL_SZ /\ opdelete_stmtA_at AOPDEL.

End Stmts.
End CANSEC1.
