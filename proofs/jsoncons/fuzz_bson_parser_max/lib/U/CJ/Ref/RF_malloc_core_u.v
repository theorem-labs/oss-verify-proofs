(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Agent Require Import F_malloc_free_u F_malloc_fast_u F_malloc_enframe_u MallocTree_u MallocFacts_A_u MallocKit_A_u MallocBlocks_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Agent Require Import Malloc_fp_u F_malloc_enf_u F_malloc_join_u F_malloc_small_u F_malloc_entry_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Ref Require Import RMallocRep_u RMallocTree_u RF_get_meta_u RMallocKit_B_u RMallocKit_B2_u RMallocKit_A_u RMalloc_fp_u RF_malloc_enf_u RAllocSlot_iface_u RF_malloc_entry_u RF_malloc_join_u RF_malloc_small_u.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Notation RAREACH := (AREACH_from ref_reserved).
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
Definition rcoreQ (o m0 : mem) (st : mstate) (s : PState)
    (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z)
    (res : mstate * option (aptr * Z)) (s' : PState) (ms' : machine_state) : Prop :=
  match res with
  | (st2, Some (g, idx)) =>
    exists (b : aptr) (r : region) (m1 : mem) (errv : word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
                   a0 a1 a2 a3 a4 a5 a6 a7 (pw st2 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x9dd68) fc None m1 (seg_rom rsegs)
      /\ rmrep st2 m1 /\ ticks_ok st2 /\ unk_agree st2 o m1 /\ mem_inv rsegs m1
      /\ stk rsegs m1 lo (bv_unsigned sp + -48)
      /\ rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra]
      /\ rw_cells rsegs m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
      /\ rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1
      /\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx - 4 <= a
                   < r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) - 4 ->
            rmalloc_fp st st2 lo (bv_unsigned sp) a)
      /\ 0 <= c_mmap_counter (ctx st2) < 2^32
      /\ slot_ok st2 g b r idx n
      /\ (expo_cond st n -> rdv pans_mem o st2 (fst b, snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -3) = 0)
      /\ mrel st st2 /\ brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
  | (st2, None) =>
    exists (m1 : mem) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m1 (seg_rom rsegs)
      /\ rmrep st2 m1 /\ ticks_ok st2 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (bv_unsigned sp)
      /\ rw_cells rsegs m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
      /\ rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1
      /\ mrel st st2 /\ brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
  end.

Lemma renf_hyp_ret o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo :
  renf_hyp (fun st1 r => ret (st1, r)) o m0 st s (rcoreQ o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo)
           ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo.
Proof.
  intros st2 g b r idx m1 s' errv t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra'; intros.
  apply rimplT_ret. apply evt_done. cbn [rcoreQ].
  exists b, r, m1, errv. do 17 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.

Lemma rfail_hyp_ret o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo :
  rfail_hyp (fun st1 r => ret (st1, r)) o m0 st s (rcoreQ o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo)
            ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc lo.
Proof.
  intros st2 m1 s' errv t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6; intros.
  apply rimplT_ret. apply evt_done. cbn [rcoreQ].
  exists m1, errv. do 14 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.

(* [comment removed for export] *)
Definition rbig_stmt : Prop :=
  forall (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
         (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N)
         (m1 : mem) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4r t3 t4 t5 t6 ra' : word),
  let st1 := set_tick t st in
  RAREACH st LB -> RMFACTS st LB -> rmrep st m0 -> tp = Z_to_bv 64 RATP ->
  alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - RAM_STACK -> MMAP_THRESHOLD <= n < 2^32 -> brk_link_ps st s ->
  rmrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 -> mem_inv rsegs m1 ->
  stk rsegs m1 lo (bv_unsigned sp + -48) ->
  rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
  rw_cells rsegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
  rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m1 ->
  rimplT o (malloc_core full_lay st1 n) s (rcoreQ o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 131052) a1 a2 a3 a4 a5 a6 a7
                 s2r s3r s4r s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9dab8) fc None m1 (seg_rom rsegs)).

Section CORE.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : rbig_stmt.

Lemma rmalloc_core_implT :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (st : mstate) (LB : list block) (s : PState) (n lo : Z) (errv : word) (t : N),
  RAREACH st LB -> RMFACTS st LB -> rmrep st m -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 8192 ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^32 -> (s_tick st < t)%N ->
  rimplT m (malloc_core full_lay (set_tick t st) n) s
        (rcoreQ m m st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until t. intros AR MF MR BL AUX ST CLO LO ERR MI TP HA N TT.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RAS_STACK_ge 0) as ASG.
  assert (RB0 : forall rid r1, (s_regions st) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= alloc_ceiling).
  { intros rid r1 H1. pose proof (rregion_facts st m rid r1 MR H1) as (X1 & _ & X2 & _). pose_ceil. lia. }
  pose proof MR as (WF0 & CX0 & GL0 & _). destruct GL0 as (_ & NL & _).
  assert (PREP : forall m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 -> wmono rsegs m m1 ->
            rmrep (set_tick t st) m1 /\ ticks_ok (set_tick t st) /\ unk_agree (set_tick t st) m m1
            /\ rw_cells rsegs m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
            /\ rpres_except (rmalloc_fp st (set_tick t st) lo (bv_unsigned sp)) m m1).
  { intros m1 MU WM. pose_ceil.
    split. { apply rmrep_set_tick. eapply rmrep_transport_high; [exact MR| exact MU| exact WM| intros lo' hi' [E|[]]; inversion E; pose_ceil; lia]. }
    split. { apply ticks_ok_set_tick; [lia|]. exact (mf_ticks _ _ MF). }
    split. { eapply unk_agree_munch; [| exact MU| |].
             - eapply unk_agree_ext; [apply unk_agree_refl| reflexivity| intros; reflexivity| reflexivity].
             - intros rid r1 H1 K1. pose proof (RB0 rid r1 H1). cbn. lia.
             - intros rid r1 H1. pose proof (RB0 rid r1 H1). lia. }
    split. { eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. subst tp. unfold RATP. rewrite unsigned_lit by lia. cbn. lia. }
    split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
    eapply rpres_except_of_munch; [exact MU| exact WM|]. intros a Ha NC. cbn. split; [|exact I]. intros HX. apply NC. left. left. lia. }
  destruct (Z.le_gt_cases MMAP_THRESHOLD n) as [TH|TH].
  - (* [comment removed for export] *)
    riprefixT. eapply evt_cut.
    { eapply (rentry_big_walk ra sp gp tp); [exact HA| unfold MMAP_THRESHOLD in *; lia| exact ST| pose_ceil; lia| lia| exact MI]. }
    intros ms' (a1' & m1 & -> & FR & ST1 & MU & WM & MI1).
    destruct (PREP m1 MU WM) as (MR1 & TK1 & UA1 & ERR1 & AUX1 & PE1).
    apply evt_done.
    eapply (RBIG m m st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo t); try eassumption.
    + unfold RAM_STACK. lia.
    + lia.
  - (* [comment removed for export] *)
    unfold malloc_core.
    replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; lia).
    replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia).
    riprefixT. eapply evt_cut.
    { eapply (rmalloc_entry_walk ra sp gp tp); [exact HA| unfold MMAP_THRESHOLD in *; lia| exact ST| pose_ceil; lia| lia| exact MI| exact NL]. }
    intros ms' (a0' & a1' & a2' & a3' & m1 & -> & FR & ST1 & MU & WM & MI1).
    destruct (PREP m1 MU WM) as (MR1 & TK1 & UA1 & ERR1 & AUX1 & PE1).
    pose proof (size_to_class_props n ltac:(lia)) as (SCR & SFIT & _).
    apply evt_done.
    eapply (rmalloc_small_implT (fun st1 r => ret (st1, r)) (ret (set_tick t st, None)) m m st LB s _ ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo t as_pre as_inv RAS).
    all: try eassumption.
    + apply renf_hyp_ret.
    + apply rfail_hyp_ret.
    + unfold RAS_STACK. lia.
    + reflexivity.
    + intros sc' Hsc' Hfit'. eapply AS_PRE; [exact AR| exact MF| exact TT| exact Hsc'| lia| exact Hfit'].
Qed.
End CORE.
End CEIL_WRAP_1.

