(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode Arr SFMisc.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_malloc_join.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_malloc_join.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_join.F_malloc_enf OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_join.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMallocRep RMallocTree.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMalloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMalloc_fp.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_malloc_join.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RF_enframe. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMalloc_fp. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMalloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilLia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilLiaP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module RF_malloc_enf.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
Import OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_free OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_fast OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_enframe OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Monad OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prog.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_join.F_malloc_enf.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_get_meta OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_enframe OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_fp.RMallocKit_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_fp.
 Unset Lia Cache.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations.
Local Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RunW.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilLia.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilLiaP.
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac MA.F_malloc_free.mlia ::= RangeFast.rc_decide ltac:(MA.F_malloc_free.pow_lits; Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= lia_acp.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
Lemma renf_glue_walk : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw gw iw rav s0v s1v s2v s3v s4v : word)
    F fc (m : mem) (st : mstate),
  rw_cells rsegs m RCTX (ctx_head_cells st) ->
  rw_cells rsegs m RMLOCK [C4 (wz 0)] ->
  rw_cells rsegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  48 <= bv_unsigned sp ->
  0 <= c_mmap_counter (ctx st) < 2^32 ->
  evt rsegs (fun ms' => ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v gw iw nw (wz (sxv (c_mmap_counter (ctx st)))) a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 renframe_entry) fc None m (seg_rom rsegs))
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7 gw iw s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2a1b8) fc None m (seg_rom rsegs)).
Proof.
  intros until st. intros CH LK FR SP48 CTR.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold RCTX, RMLOCK in *. unfold ctx_head_cells in CH.
  (* [comment removed for export] *)
  step. rewrite sx32_wz_sxv by lia.
  (* [comment removed for export] *)
  step. step.
  eapply evt_cut.
  { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x2a1c4)) with (Z_to_bv 64 0x2a1c4) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  do 12 step.
  apply evt_done. unfold renframe_entry. reflexivity.
Qed.

(* [comment removed for export] *)
Definition renf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (o m0 : mem) (C : Z -> Prop) (st1 : mstate) (g b : aptr) (idx n : Z)
    (r : mstate * optr) (ms' : machine_state) : Prop :=
  exists st' p t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    r = (st', Some p)
    /\ ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (conc st' p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rmrep st' m' /\ ticks_ok st' /\ rpres_except C m0 m'
    /\ enf_leaf o st1 g b idx n st' p
    (* [comment removed for export] *)
    /\ rmrep (fst (enframe_at st1 g idx n
                 (fold_off (enf_off0 o st1 b (get_stride (get_meta_rec st1 g)) idx)
                           ((get_stride (get_meta_rec st1 g) - 4 - n) / 16)))) m'.

(* [comment removed for export] *)
Lemma renf_implT :
  forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' ra s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32)
         (o m0 m1 : mem) (s : PState) (st1 : mstate) (g b : aptr) (r : region) (idx n lo : Z) (C : Z -> Prop),
  let mr := get_meta_rec st1 g in
  let stride := get_stride mr in
  let ctr := c_mmap_counter (ctx st1) in
  rmrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 ->
  mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
  rpres_except C m0 m1 -> (forall a, lo <= a < bv_unsigned sp -> C a) ->
  (forall a, r_base r + snd b + 16 + stride * idx - 4 <= a < r_base r + snd b + 16 + stride * idx + stride - 4 -> C a) ->
  0 <= ctr < 2^32 ->
  slot_ok st1 g b r idx n ->
  rimplT o (enframe_full st1 g idx n ctr (fun st2 p => ret (havoc p n st2, Some p))) s
        (fun res s' ms' => s' = s /\ renf_post ra sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 F fc lo o m0 C st1 g b idx n res ms')
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
                 a0 a1 a2 a3 a4 a5 a6 a7 (pw st1 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x2a1b8) fc None m1 (seg_rom rsegs)).
Proof.
  intros until C. intros mr stride ctr MR TK UA MI ST CLO LO FR PE CST CSL CTR SO.
  destruct SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0 NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
  fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, S31, NS, NOGRP, HDR0, Q16, AVr, FRr, FBr, MPL, SCr.
  fold stride in SPAN, S16, SMOD, S31, NS, NOGRP, HDR0, Q16.
  assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
  { eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
  clear SPAN. rename SPAN1 into SPAN.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  bz_ceil.
  (* [comment removed for export] *)
  cps_destruct (rslot_facts st1 m1 o g b r idx MR UA Hr Hk B0 ltac:(lia) SPAN S16 B16 SMOD HDR0)
    as (x3 & x2 & x1 & WRs & Y & E3 & E2 & E1 & CB & R4 & PEND & RC & RI1).
  fold mr in WRs, Y, E3, E2, E1, PEND. fold stride in WRs, Y, E3, E2, E1, PEND.
  cps_pose (rmeta_chunk_facts st1 m1 g MR MSL) as (MM & G0 & GC & GI1 & GI2 & GDJ & GRG).
  bz_ceil.
  set (G := conc st1 g) in *.
  pose proof (GDJ (fst b) r Hr Hk) as GR.
  change (get_meta_rec st1 g) with mr in MM. unfold meta_cells in MM. rewrite Hmem in MM.
  unfold pw at 3 in MM. cbn [oconc] in MM. unfold meta_word in MM.
  set (B := conc st1 b) in *.
  pose proof (byte_range x3) as X3. pose proof (byte_range x2) as X2. pose proof (byte_range x1) as X1.
  assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN.
  (* [comment removed for export] *)
  pose proof (bytes_at_read rsegs m1 _ _ 0 1 Y ltac:(lia) ltac:(cbn; lia)) as RD4. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD4.
  pose proof (bytes_at_read rsegs m1 _ _ 1 1 Y ltac:(lia) ltac:(cbn; lia)) as RD3. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD3.
  pose proof (bytes_at_read rsegs m1 _ _ 2 2 Y ltac:(lia) ltac:(cbn; lia)) as RD2. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD2.
  rewrite Z.add_0_r in RD4.
  replace (B + 16 + stride * idx - 4 + 1) with (B + 16 + stride * idx - 3) in RD3 by lia.
  replace (B + 16 + stride * idx - 4 + 2) with (B + 16 + stride * idx - 2) in RD2 by lia.
  rewrite <- (le2_lohi (bv_unsigned x2) (bv_unsigned x1)) in RD2 by lia.
  (* [comment removed for export] *)
  unfold enframe_full, enframe_read_off. change (get_meta_rec st1 g) with mr. fold stride. cbv zeta.
  assert (Hp0 : slot_start' mr idx = (fst b, snd b + (16 + stride * idx))).
  { unfold slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd, UNIT. cbn [fst snd]. fold stride. reflexivity. }
  rewrite Hp0. unfold aadd. cbn [fst snd].
  apply rimplT_rd8. rewrite E3.
  change ((stride - IB - n) / UNIT) with ((stride - 4 - n) / 16). set (slack := (stride - 4 - n) / 16).
  set (K := fun off : Z => let '(st2, p) := enframe_at st1 g idx n off in @ret (mstate * optr) (havoc p n st2, Some p)).
  set (off0 := if bv_unsigned x3 =? 0 then Z.land ctr 255 else Z.land (bv_unsigned x2 + 256 * bv_unsigned x1 + 1) 255).
  set (off := fold_off off0 slack).
  assert (OFF0 : 0 <= off0 < 256).
  { subst off0. destruct (bv_unsigned x3 =? 0).
    - split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
    - split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (SL0 : 0 <= slack) by (subst slack; apply Z.div_pos; lia).
  pose proof (fold_off_le_slack off0 slack OFF0 SL0) as OFF. fold off in OFF.
  assert (FIT : 16 * off + n + 4 <= stride) by (subst slack; Z.div_mod_to_equations; lia).
  match goal with |- rimplT _ _ _ ?Q ?ms => 
  assert (GOAL : rimplT o (K off) s Q ms) end.
  2:{ assert (OFFa : bv_unsigned x3 = 0 -> fold_off (Z.land ctr 255) slack = off).
      { intros E0. unfold off, off0. rewrite (proj2 (Z.eqb_eq _ _) E0). reflexivity. }
      assert (OFFb : bv_unsigned x3 <> 0 -> fold_off (Z.land (bv_unsigned x2 + 256 * bv_unsigned x1 + 1) 255) slack = off).
      { intros E0. unfold off, off0. rewrite (proj2 (Z.eqb_neq _ _) E0). reflexivity. }
      clearbody off.
      destruct (Z.eqb_spec (bv_unsigned x3) 0) as [E0|NE0]; cbn [negb].
      - rewrite (OFFa E0). exact GOAL.
      - apply rimplT_rd16. unfold aadd; cbn [fst snd]. rewrite E2, E1. rewrite (OFFb NE0). exact GOAL. }
  subst K. cbv beta. rewrite surj_pair_let. apply rimplT_ret.
  (* [comment removed for export] *)
  cps_pose MR as (WF' & CX & GL & _). destruct GL as (LK & _). destruct CX as (CH & _).
  eapply evt_cut.
  { eapply (renf_glue_walk sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' (Z_to_bv 64 n) (pw st1 (Some g)) (wz idx) ra s0v s1v s2v s3v s4v F fc m1 st1);
      [exact CH| exact LK| exact FR| lia| exact CTR]. }
  intros ms' ->.
  unfold renframe_entry.
  eapply evt_mono.
  { eapply (renframe_walk ra sp gp tp t0 t1 t2 s0v s1v a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (pw st1 (Some g)) (Z_to_bv 64 n)
              (pw st1 (m_prev mr)) (pw st1 (m_next mr)) F fc m1 B stride n idx ctr (m_avail mr) (m_freed mr)
              (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (bv_unsigned x3) (bv_unsigned x2 + 256 * bv_unsigned x1)).
    all: lazymatch goal with
         | |- rw_cells _ _ (bv_unsigned (pw _ _)) _ => unfold pw; cbn [oconc]; fold G; rewrite (wz_unsigned G) by lia; exact MM
         | |- mem_inv _ _ => exact MI
         | |- wr_at _ _ _ _ => exact WRs
         | |- ov_read_bytes _ _ _ 2 = _ => exact RD2
         | |- ov_read_bytes _ _ _ _ = Some [b8 0] => exact RD4
         | |- ov_read_bytes _ _ _ _ = _ => exact RD3
         | |- bv_unsigned (Z_to_bv 64 _) = _ => apply unsigned_lit; lia
         | |- _ => idtac end.
    all: try (unfold pw; cbn [oconc]; fold G; rewrite (wz_unsigned G) by lia).
    all: try lia.
    - subst stride. unfold get_stride, UNIT. reflexivity.
    - intros off' O1 O2. pose proof (Q16 off' O1 O2). lia. }
  (* [comment removed for export] *)
  intros ms' PO. cbv beta in PO. unfold ren3_post in PO.
  cps_destruct PO as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & -> & EM & MI').
  split; [reflexivity|].
  fold slack in EM. fold off0 in EM. fold off in EM. fold slack off0 off.
  set (res := enframe_at st1 g idx n off) in *.
  (* [comment removed for export] *)
  assert (S31n : stride - 4 - n < 2^31) by lia.
  cps_destruct (renframe_mrep st1 m1 g b r idx n off MR TK Hmem Hr Hk B0 ltac:(clear -IDX LI32; lia) ltac:(unfold stride, mr in SPAN; clear -SPAN S16; lia) S16 S31n NOGRP (proj1 OFF) N0 FIT (Q16 off (proj1 OFF) FIT))
    as (MRr & TKr & CONCr & FSTr & SNDr).
  fold stride B res in MRr, TKr, CONCr, FSTr, SNDr.
  change (conc st1 b) with B in MRr, CONCr. change (get_stride (get_meta_rec st1 g)) with stride in MRr, CONCr, SNDr.
  fold res in MRr, TKr, CONCr, FSTr, SNDr.
  set (P0 := B + 16 + stride * idx) in *.
  rewrite <- EM in MRr.
  destruct (rmrep_havoc (fst res) m' (snd res) n MRr TKr) as [MR' TK'].
  (* [comment removed for export] *)
  assert (PE0 : rpres_except (fun a => P0 - 4 <= a < P0 + stride - 4) m1 m').
  { rewrite EM. apply (rpres_enframe _ m1 m1 P0 stride off n idx B (rpres_except_refl _ _) (proj1 OFF) N0 FIT); [unfold P0; lia| unfold P0; lia|].
    intros x Hx. exact Hx. }
  assert (ST' : stk rsegs m' lo (bv_unsigned sp + -48)).
  { eapply rpres_except_stk; [exact PE0| exact ST|]. intros a Ha. cbv beta. unfold P0. lia. }
  assert (FR' : rw_cells rsegs m' (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra]).
  { eapply rpres_except_rw_cells; [exact PE0| exact FR|]. cbn [cells_size csize Nat.add Z.of_nat]. intros a Ha. cbv beta. unfold P0. lia. }
  release_frame FR' ST' (bv_unsigned sp).
  unfold renf_post. exists (havoc (snd res) n (fst res)), (snd res). do 14 eexists. exists m'.
  split; [reflexivity|].
  split. { unfold wz. rewrite conc_havoc. rewrite <- CONCr. unfold res. rewrite conc_enframe_at. reflexivity. }
  split; [exact MI'|]. split; [exact ST'|]. split; [exact MR'|]. split; [exact TK'|].
  split.
  { rewrite EM. apply (rpres_enframe C m0 m1 _ stride off n idx B PE (proj1 OFF) N0 FIT); [unfold B; lia| unfold B; lia|].
    intros x Hx. apply CSL. unfold B in Hx. lia. }
  assert (EOFF : off = fold_off (enf_off0 o st1 b (get_stride (get_meta_rec st1 g)) idx) ((get_stride (get_meta_rec st1 g) - 4 - n) / 16)).
  { unfold off, off0, slack, enf_off0. fold mr. fold stride. rewrite E3, E2, E1. reflexivity. }
  split.
  { exists off. split; [exact (proj1 OFF)|]. split; [exact FIT|].
    split. { clear - FSTr SNDr. destruct (snd res) as [p1 p2]. cbn [fst snd] in FSTr, SNDr. subst. reflexivity. }
    split; [reflexivity|]. split; [reflexivity|]. exact EOFF. }
  rewrite <- EOFF. exact MRr.
Qed.

End ACeilS1.
End RF_malloc_enf.


From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
Module RAllocSlot_iface.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
Import OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_free OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_fast OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_enframe OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Monad OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prog.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_fp.
 Unset Lia Cache.
Import ListNotations.
Local Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RunW.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilLia.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilLiaP.
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac MA.F_malloc_free.mlia ::= RangeFast.rc_decide ltac:(MA.F_malloc_free.pow_lits; Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= lia_acp.   (* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
Definition RAS_STACK (sc : Z) : Z := 288 + 144 * Z.max 0 (27 - sc).

Lemma RAS_STACK_ge sc : 288 <= RAS_STACK sc.
Proof. unfold RAS_STACK. lia. Qed.
(* [comment removed for export] *)
Lemma RAS_STACK_mono a b : a <= b -> RAS_STACK b <= RAS_STACK a.
Proof. unfold RAS_STACK. lia. Qed.
Lemma RAS_STACK_nest sc j : sc < j -> j <= 26 -> RAS_STACK j + 144 <= RAS_STACK sc.
Proof. unfold RAS_STACK. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ras_post (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (o m : mem) (st0 st : mstate) (s : PState) (lo sc req : Z)
    (st1 : mstate) (idx : Z) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' (bv_unsigned sp)
    /\ rmrep st1 m' /\ ticks_ok st1 /\ unk_agree st1 o m'
    /\ rpres_except (rmalloc_fp st0 st1 lo (bv_unsigned sp)) m m'
    /\ mrel st st1 /\ brk_link_ps st1 s'
    /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ as_inv st0 st st1 sc idx
    /\ 0 <= c_mmap_counter (ctx st1) < 2^32
    /\ (idx = -1
        \/ (0 <= idx /\ exists g b r, active st1 sc = Some g /\ slot_ok st1 g b r idx req
              /\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4 <= a
                           < r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx + get_stride (get_meta_rec st1 g) - 4 ->
                    rmalloc_fp st0 st1 lo (bv_unsigned sp) a)
              (* [comment removed for export] *)
              /\ (s_regions st0 = ∅ -> rdv pans_mem o st1 (fst b, snd b + (16 + get_stride (get_meta_rec st1 g) * idx) + -3) = 0))).

Definition ralloc_slot_stmt (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop)
                           (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop) : Prop :=
  forall (fuel : nat) (R : Type) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
  as_pre st0 st sc req fuel ->
  rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
  (forall st1 idx s' ms',
     ras_post as_inv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
     rimplT o (k st1 idx) s' Q ms') ->
  rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom rsegs)).


End ACeilS1.
End RAllocSlot_iface.

Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_fp.RMallocKit_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_malloc_join.RF_malloc_enf OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_malloc_join.RAllocSlot_iface.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLiaP.
Local Ltac lia ::= lia_acp.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition renf_hyp {R} (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (s : PState)
    (Q : R -> PState -> machine_state -> Prop)
    (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) : Prop :=
  forall (st2 : mstate) (g b : aptr) (r : region) (idx : Z) (m1 : mem) (s' : PState) (errv : word)
         (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra' : word),
    rmrep st2 m1 -> ticks_ok st2 -> unk_agree st2 o m1 -> mem_inv rsegs m1 ->
    stk rsegs m1 lo (bv_unsigned sp + -48) ->
    rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
    rw_cells rsegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
    rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
    (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx - 4 <= a
                 < r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) - 4 ->
       rmalloc_fp st st2 lo (bv_unsigned sp) a) ->
    0 <= c_mmap_counter (ctx st2) < 2^32 ->
    slot_ok st2 g b r idx n ->
    (expo_cond st n -> rdv pans_mem o st2 (fst b, snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -3) = 0) ->
    (* [comment removed for export] *)
    (MMAP_THRESHOLD <= n -> forall off, 16 <= off -> cell_read (get_shadow st2 (fst b)) off = Known 0) ->
    mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
    rimplT o (K st2 (Some (g, idx))) s' Q
          (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
                   a0 a1 a2 a3 a4 a5 a6 a7 (pw st2 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x2a1b8) fc None m1 (seg_rom rsegs)).

(* [comment removed for export] *)
Definition rfail_hyp {R} (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (s : PState)
    (Q : R -> PState -> machine_state -> Prop)
    (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) : Prop :=
  forall (st2 : mstate) (m1 : mem) (s' : PState) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    rmrep st2 m1 -> ticks_ok st2 -> mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp) ->
    rw_cells rsegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
    rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
    mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
    rimplT o (K st2 None) s' Q
          (MS (mkR ra sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m1 (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rmalloc_fp_cases st st2 lo sp m0 m2 a :
  rmrep st m0 -> rmrep st2 m2 -> rmalloc_fp st st2 lo sp a ->
  lo <= a < sp \/ a < alloc_ceiling.
Proof.
  intros (WF & _) (WF2 & _) H. cps_pose WF as (_ & WR & _). cps_pose WF2 as (_ & WR2 & _).
  bz_ceil.
  destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC _]]]]].
  - left; exact H.
  - right. rewrite unsigned_lit in H by lia. lia.
  - right. unfold RCTX in H. lia.
  - right. cps_destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). bz_ceil. lia.
  - right. cps_destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). bz_ceil. lia.
  - right. cps_destruct (WR (fst b) r Hr) as (_ & _ & _ & RC & _). bz_ceil. lia.
  - right. cps_destruct (WR (fst b) r Hr) as (_ & _ & _ & RC & _). bz_ceil. lia.
  - right. bz_ceil. lia.
Qed.

Lemma rframe_after_call st st2 lo sp' m0 m m' m2 A cs :
  rmrep st m0 -> rmrep st2 m2 ->
  rpres_except (rmalloc_fp st st2 lo sp') m m' -> rw_cells rsegs m A cs ->
  sp' <= A -> alloc_ceiling <= A -> rw_cells rsegs m' A cs.
Proof.
  intros MR0 MR2 PE H HA HC. eapply rpres_except_rw_cells; [exact PE| exact H|].
  intros a Ha Hfp. destruct (rmalloc_fp_cases st st2 lo sp' m0 m2 a MR0 MR2 Hfp); lia.
Qed.

Lemma rmalloc_fp_sp_mono st st2 lo sp1 sp2 a : sp1 <= sp2 -> rmalloc_fp st st2 lo sp1 a -> rmalloc_fp st st2 lo sp2 a.
Proof.
  intros H [[X|X]|X]; [left; left; lia| left; right; exact X| right; exact X].
Qed.

Lemma rmalloc_fp_st_mono st sta stb lo sp a : mrel sta stb -> rmalloc_fp st sta lo sp a -> rmalloc_fp st stb lo sp a.
Proof. intros [HR _ _] H. eapply rmalloc_fp_mono; [exact HR| exact H]. Qed.

Lemma rmalloc_fp_image st st2 lo sp m0 m2 a :
  rmrep st m0 -> rmrep st2 m2 -> rmalloc_fp st st2 lo sp a -> alloc_ceiling <= lo ->
  0x32000 <= a < 0x66000 -> RCTX <= a < RCTX + 928 \/ 0x4413c <= a < 0x44140.
Proof.
  intros (WF & _) (WF2 & _) H CLO HA. cps_pose WF as (_ & WR & _). cps_pose WF2 as (_ & WR2 & _).
  bz_ceil.
  assert (IMG : forall P : Prop, (forall rid r, (s_regions st) !! rid = Some r -> r_base r <= a < r_base r + round_up_pg (r_len r) -> P)
                 /\ (forall rid r, (s_regions st2) !! rid = Some r -> r_base r <= a < r_base r + round_up_pg (r_len r) -> P)).
  { intros P. split; intros rid r Hr Ha.
    - cps_destruct (WR rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint2 _ _ RF ltac:(lia)) as [D1 D2]. exfalso. lia.
    - cps_destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint2 _ _ RF ltac:(lia)) as [D1 D2]. exfalso. lia. }
  destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC FR]]]]].
  - exfalso. lia.
  - right. rewrite unsigned_lit in H by lia. lia.
  - left. exact H.
  - pose proof (lr_lo_ge r). apply (proj2 (IMG _) rid r Hr ltac:(lia)).
  - pose proof (lr_lo_ge r). apply (proj2 (IMG _) rid r Hr ltac:(lia)).
  - apply (proj1 (IMG _) (fst b) r Hr Ha).
  - apply (proj1 (IMG _) (fst b) r Hr Ha).
  - (* [comment removed for export] *)
    exfalso. pose proof WF as (RS & _). pose proof (rfresh_image st a (conj FC FR) RS). lia.
Qed.

Lemma rauxv_ok_malloc_fp st st2 lo sp m0 m2 m m' B :
  rmrep st m0 -> rmrep st2 m2 -> rauxv_ok m B -> rpres_except (rmalloc_fp st st2 lo sp) m m' ->
  alloc_ceiling <= lo -> sp <= B -> rauxv_ok m' B.
Proof.
  intros MR0 MR2 AUX PE CLO SB. eapply rauxv_ok_pres; [exact AUX| exact PE| |].
  - intros a Ha Hfp. destruct (rmalloc_fp_cases st st2 lo sp m0 m2 a MR0 MR2 Hfp); [lia|].
    cps_destruct AUX as (av & x3 & x4 & x5 & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & HH). bz_ceil. lia.
  - intros a Ha Hfp. unfold RAUXV_CELL, RLIBC in Ha.
    destruct (rmalloc_fp_image st st2 lo sp m0 m2 a MR0 MR2 Hfp CLO ltac:(lia)) as [X|X]; unfold RCTX in X; lia.
Qed.

End ACeilS1.
