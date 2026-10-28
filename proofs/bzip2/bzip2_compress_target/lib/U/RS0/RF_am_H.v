(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep Arr.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode SFMisc.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_malloc_free MallocTree MallocModel_B.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocModel_B.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_B MallocKit_B3 F_am_A F_am_K.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_am_G.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_am_G.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_am_G F_am_H.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_free OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocModel_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocModel_B.F_ntf_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_am_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_am_K OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_am_G.F_am_C OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_am_G.F_am_F OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_am_G OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_am_H. (* [comment removed for export] *) From Stdlib Require ZArith NArith List Lia Bool. From stdpp Require gmap. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep Arr SFMisc. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_syscalls MallocRep F_malloc_free. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require STree Malloc MallocCtrl. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocTree. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_B MallocModel_B. From Stdlib Require Lia. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Prog.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require KStep.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_mm_syscalls RF_ntf_A RF_am_A RF_am_K.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocModel_B. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_am_G.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_ntf_A RF_am_A RF_am_K.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilLia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilLiaP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module RF_am_C.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
Import OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_free OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocModel_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocModel_B.F_ntf_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_am_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_am_K OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_am_G.F_am_C. (* [comment removed for export] *)            
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_ntf_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_am_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_am_K.
 Unset Lia Cache.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations.
Local Open Scope bv_scope.
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
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
Lemma ram_carve2 : forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m0 m : word -> option byte) (junk : list byte) (lo : Z) (st0 st : mstate) (p : aptr) (r : region),
  rmrep st m -> mem_inv rsegs m -> s_regions st = s_regions st0 ->
  (s_regions st) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
  pgal (snd p) -> lr_lo r <= r_base r + snd p ->
  (s_areas st) !! p = None -> (forall k, 0 <= k < NSLOTS -> (s_metas st) !! (aadd p (AREA_HDR + META_SIZE * k)) = None) ->
  0 <= c_secret (ctx st) < 2^64 ->
  rw_cells rsegs m (conc st p) [C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0)] ->
  rw_cells rsegs m (conc st p + 24) [CB 4072 (zeros 4072)] ->
  rpres_except (ram_fp st0 lo (bv_unsigned sp)) m0 m -> wmono rsegs m0 m ->
  rw_cells rsegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk rsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  let stC := upd_ctx (set_meta_area_tail (Some p)) st in
  let stD := set_areas (<[p := mkArea (c_secret (ctx st)) None NSLOTS]> (s_areas stC)) stC in
  evt rsegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st0 m0
               (am_took stD (aadd p AREA_HDR) 100) (Z_to_bv 64 (conc st p + 24)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (conc st p)) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x29e00) fc None m (seg_rom rsegs)).
Proof.
  intros until r. intros MR MI ER0 Hr NK S0 S1 SAL SLR ANone FRESH SEC HDR0 REST PE0 WM0 FR ST LO LOLE stC stD.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  cps_pose MR as (WF & (C1 & _) & _). cps_pose WF as (Hres & WR & DJ & WA & WG).
  pose proof (conc_region' st p r Hr) as Cp.
  cps_destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). cps_destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). bz_ceil.
  pose proof (lr_lo_ge r) as LRG. pose proof (round_up_pg_ge (r_len r)) as RU.
  unfold ctx_head_cells in C1.
  bz_ceil; unfold RCTX, RMLOCK, RSSP_GUARD in *.
  (* [comment removed for export] *)
  assert (PD : conc st p + 4096 <= 0x32000 \/ 0x66000 <= conc st p) by lia.
  assert (PB : 0 <= conc st p /\ conc st p + 4096 <= lo) by lia.
  clear RBAL RL0 RB0 RF DR1 DR23 DR2 LRG RU Hres DJ WA WG.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928); (conc st p, conc st p + 4096)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM. unfold RCTX in MU.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(RCTX + 64, RCTX + 72)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
  unfold RCTX in MUc.
  st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRC : rmrep stC mX) end.
  { eapply (rmrep_ctx_frameW st stC _ _ _ MR MUc WMc); try reflexivity.
    - intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - left. unfold ctx_head_cells, RCTX. cbn [ctx stC upd_ctx s_ctx set_meta_area_tail c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
            c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
      unfold pw at 4. cbn [oconc]. change (conc stC p) with (conc st p). exact C1.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia. }
  clear MUc WMc.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(conc st p, conc st p + 4096)]%Z mX) as MUp; pose proof (wmono_refl rsegs mX) as WMp end.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRC3 : rmrep stC mX) end.
  { eapply rmrep_transport_unowned; [exact MRC | exact MUp | exact WMp |].
    intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. eapply (rfresh_page_avoids stC _ p r a MRC); try assumption. }
  clear MUp WMp MRC.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRD : rmrep stD mX) end.
  { unfold stD. eapply (rmrep_new_area stC _ p r (c_secret (ctx st))); try first [exact MRC3 | exact Hr | exact NK | exact S0 | exact S1 | exact SLR | exact ANone | exact FRESH | idtac].
    - exact SAL.
    - change (conc stC p) with (conc st p). exact HDR0.
    - intros k Hk. change (conc stC p) with (conc st p). rewrite meta_cells_meta0.
      destruct REST as [[_ B] W]. cbn [cells_bytes cbytes cells_size csize Nat.add] in B, W. rewrite app_nil_r in B.
      replace (conc st p + AREA_HDR + META_SIZE * k) with ((conc st p + 24) + 40 * k) by (unfold AREA_HDR, META_SIZE; lia).
      eapply (rrw_cells_of_zeros _ (conc st p + 24) 4072 (40 * k)); [exact B| exact W| cbn; tauto_fast| reflexivity| lia| cbn [cells_size csize Nat.add]; unfold NSLOTS in Hk; lia].
    - change (conc stC p) with (conc st p).
      destruct REST as [[_ B] W]. cbn [cells_bytes cbytes cells_size csize Nat.add] in B, W. rewrite app_nil_r in B.
      replace (conc st p + 4064) with ((conc st p + 24) + 4040) by lia.
      eapply (rrw_cells_of_zeros _ (conc st p + 24) 4072 4040); [exact B| exact W| cbn; split; [reflexivity| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity| lia| cbn [cells_size csize Nat.add]; lia]. }
  clear MRC3 HDR0 REST.
  assert (MSq : meta_slot stD (aadd p AREA_HDR)).
  { exists p, (mkArea (c_secret (ctx st)) None NSLOTS), 0. split; [| split; [unfold NSLOTS; lia| unfold AREA_HDR, META_SIZE; rewrite Z.mul_0_r, Z.add_0_r; reflexivity]].
    unfold stD. cbn [s_areas set_areas]. rewrite lookup_insert_eq. reflexivity. }
  assert (CQ : conc st p + 24 = conc stD (aadd p AREA_HDR)).
  { change (conc stD (aadd p AREA_HDR)) with (conc st (aadd p AREA_HDR)). rewrite (conc_aadd st p AREA_HDR) by (rewrite Hr; eauto). reflexivity. }
  rewrite CQ. change (Z_to_bv 64 410704) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 410848) with (Z_to_bv 64 RMLOCK).
  eapply evt_mono.
  { eapply (ram_b0 sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo 100 stD (aadd p AREA_HDR));
      [exact MRD | assumption | exact MSq | lia | | | bz_ceil; lia | lia].
    - lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
    - lazymatch goal with H : stk rsegs ?mX lo _ |- _ => exact H end. }
  intros ms' RP. unfold ram_ret_post in RP |- *.
  cps_destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
  do 15 eexists. split; [reflexivity|].
  split.
  { eapply rpres_except_trans; [exact PE0|].
    apply (rpres_except_of_munch_cov (ram_fp st0 lo (bv_unsigned sp))) in MU; [|exact WM|].
    - eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha.
      apply (proj1 (ram_fp_same st0 stD lo _ a ltac:(rewrite <- ER0; reflexivity))). exact Ha.
    - cbn [ivs_covered]. split; [|split; [|split; [|exact I]]].
      + intros x Hx. apply ram_fp_stack. lia.
      + intros x Hx. apply ram_fp_ctx. unfold RCTX. lia.
      + intros x Hx. eapply (ram_fp_region st0 lo _ x (fst p) r); [rewrite <- ER0; exact Hr| exact NK|].
        pose proof (lr_lo_ge r). lia. }
  (* [comment removed for export] *)
  split; [eapply wmono_trans; [exact WM0| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.

(* [comment removed for export] *)
Lemma ram_carve_walk : forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (p : aptr) (r : region),
  rmrep st m -> mem_inv rsegs m ->
  (s_regions st) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
  pgal (snd p) -> lr_lo r <= r_base r + snd p ->
  (s_areas st) !! p = None -> (forall k, 0 <= k < NSLOTS -> (s_metas st) !! (aadd p (AREA_HDR + META_SIZE * k)) = None) ->
  (forall tl, c_meta_area_tail (ctx st) = Some tl -> is_Some ((s_areas st) !! tl)) ->
  1 <= c_avail_meta_area_count (ctx st) < 2^64 -> 0 <= c_secret (ctx st) < 2^64 ->
  bytes_at rsegs m (conc st p) (zeros 4096) -> wr_at rsegs m (conc st p) 4096 ->
  rw_cells rsegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk rsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  evt rsegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo (carve_st st p) m
               (am_took (carve_st st p) (aadd p AREA_HDR) 100) (Z_to_bv 64 (conc st p + 24)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (conc st p)) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x29dd4) fc None m (seg_rom rsegs)).
Proof.
  intros until r. intros MR MI Hr NK S0 S1 SAL SLR ANone FRESH TL CNT SEC ZB ZW FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  cps_pose MR as (WF & (C1 & _) & _ & AR & _). cps_pose WF as (Hres & WR & DJ & WA & WG).
  pose proof (conc_region' st p r Hr) as Cp.
  cps_destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). cps_destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). bz_ceil.
  pose proof (lr_lo_ge r) as LRG. pose proof (round_up_pg_ge (r_len r)) as RU.
  unfold ctx_head_cells in C1.
  (* [comment removed for export] *)
  assert (HDR0 : rw_cells rsegs m (conc st p) [C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0)]).
  { rewrite <- (Z.add_0_r (conc st p)). eapply (rrw_cells_of_zeros m (conc st p) 4096 0); [exact ZB| exact ZW| cbn; tauto_fast| reflexivity| lia| cbn; lia]. }
  assert (REST : rw_cells rsegs m (conc st p + 24) [CB 4072 (zeros 4072)]).
  { eapply (rrw_cells_of_zeros m (conc st p) 4096 24); [exact ZB| exact ZW| cbn [cells_wf]; split; [first [reflexivity | apply zeros_length]| exact I] | cbn [cells_bytes cbytes cells_size csize Nat.add]; rewrite app_nil_r; reflexivity| lia| cbn; lia]. }
  clear ZB ZW.
  bz_ceil; unfold RCTX, RMLOCK, RSSP_GUARD in *.
  assert (PD : conc st p + 4096 <= 0x32000 \/ 0x66000 <= conc st p) by lia.
  assert (PB : 0 <= conc st p /\ conc st p + 4096 <= lo) by lia.
  clear RBAL RL0 RF DR1 DR23 DR2 RU.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928); (conc st p, conc st p + 4096)]%Z m) as MU0.
  pose proof (wmono_refl rsegs m) as WM0. unfold RCTX in MU0.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(RCTX + 40, RCTX + 48); (RCTX + 72, RCTX + 80)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
  unfold RCTX in MUc.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1.
  set (st1 := upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR1 : rmrep st1 mX) end.
  { eapply (rmrep_ctx_frameW st st1 _ _ _ MR MUc WMc); try reflexivity.
    - intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - left. unfold ctx_head_cells, RCTX. cbn [ctx st1 upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
            c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
      unfold pw at 5. cbn [oconc]. change (conc st1 (aadd p 4096)) with (conc st (aadd p 4096)).
      rewrite (conc_aadd st p 4096) by (rewrite Hr; eauto). unfold wz at 6 7.
      lazymatch goal with H : rw_cells rsegs ?mX 410856 _ |- _ => exact H end.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia. }
  clear MUc WMc.
  (* [comment removed for export] *)
  st1.
  destruct (c_meta_area_tail (ctx st)) as [tl|] eqn:HT.
  - (* [comment removed for export] *)
    destruct (TL tl eq_refl) as [ar Har].
    cps_destruct (rarea_conc st tl ar WF Har) as (rt & Hrt & Ct & St0 & St1 & StL & NKt & RBt & RBAt & RBCt). bz_ceil.
    pose proof (rarea_lr_lo st tl ar rt WF Har Hrt) as LRt.
    cps_destruct (WR _ _ Hrt) as (_ & _ & _ & _ & RFt). cps_destruct (rreserved_disjoint _ _ RFt) as (DT1 & _ & DT23 & DT2).
    assert (TD : conc st tl + 4096 <= 0x32000 \/ 0x66000 <= conc st tl) by lia.
    assert (TB : 0 < conc st tl /\ conc st tl + 4096 <= lo) by lia.
    assert (TP : conc st tl + 4096 <= conc st p \/ conc st p + 4096 <= conc st tl).
    { destruct (N.eq_dec (fst tl) (fst p)) as [E|NE].
      - rewrite E, Hr in Hrt. assert (rt = r) by congruence. subst rt.
        assert (NEo : snd tl <> snd p) by (intros E2; assert (tl = p) by (destruct tl, p; cbn in *; congruence); subst tl; rewrite ANone in Har; discriminate).
        unfold pgal in SAL. clear - Ct Cp NEo SAL StL E. Z.div_mod_to_equations. lia.
      - destruct (DJ _ _ _ _ Hrt Hr NE); lia. }
    clear RBAt StL RFt DT1 DT23 DT2 St0 St1 LRt RBt RBCt DJ WA WG.
    unfold pw. cbn [oconc]. unfold wz.
    assert (CF : bv_eqb (Z_to_bv 64 (conc st tl)) (Z_to_bv 64 0) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
    rewrite CF. clear CF.
    cps_pose MR1 as (_ & _ & _ & AR1 & _). cps_destruct (AR1 tl ar Har) as (ARh & _ & _). clear AR1.
    change (conc st1 tl) with (conc st tl) in ARh.
    apply (munch_grow2 _ (conc st tl, conc st tl + 4096)) in MU0.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (munch_refl [(conc st tl + 8, conc st tl + 16)]%Z mX) as MUa; pose proof (wmono_refl rsegs mX) as WMa end.
    (* [comment removed for export] *)
    st1. st1.
    set (st2 := set_areas (<[tl := mkArea (a_check ar) (Some p) (a_nslots ar)]> (s_areas st1)) st1).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR2 : rmrep st2 mX) end.
    { eapply (rmrep_set_area_next st1 _ _ tl ar p MR1 Har); [cbn; rewrite Hr; eauto| exact MUa| exact WMa|].
      change (conc st1 tl) with (conc st tl). change (conc st1 p) with (conc st p). unfold wz at 2. exact ARh. }
    clear MUa WMa ARh MR1.
    rewrite (carve_st_some st p tl ar HT Har ANone). cbv zeta. fold st1. fold st2.
    change (Z_to_bv 64 410704) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 410848) with (Z_to_bv 64 RMLOCK).
    eapply evt_mono.
    { eapply (ram_carve2 sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc m _ junk lo st st2 p r);
        first [exact MR2 | reflexivity | exact Hr | exact NK | exact S0 | exact S1 | exact SAL | exact SLR | exact FRESH | exact SEC | exact WM0 | idtac].
      - lazymatch goal with H : mem_inv rsegs ?mX |- _ => exact H end.
      - cbn [s_areas set_areas upd_ctx st2 st1]. rewrite lookup_insert_ne; [exact ANone|]. intros ->. rewrite ANone in Har; discriminate.
      - lazymatch goal with H : rw_cells rsegs ?mX (conc st p) _ |- _ => exact H end.
      - lazymatch goal with H : rw_cells rsegs ?mX (conc st p + 24) _ |- _ => exact H end.
      - apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU0; [exact MU0|exact WM0|].
        cbn [ivs_covered]. split; [|split; [|split; [|split; [|exact I]]]].
        + intros x Hx. apply ram_fp_stack. lia.
        + intros x Hx. eapply ram_fp_area; [exact MR| exact Har| lia].
        + intros x Hx. apply ram_fp_ctx. unfold RCTX. lia.
        + intros x Hx. eapply (ram_fp_region st lo _ x (fst p) r); [exact Hr| exact NK| lia].
      - lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
      - lazymatch goal with H : stk rsegs ?mX lo _ |- _ => exact H end.
      - bz_ceil; lia.
      - lia. }
    intros ms' RP. exact RP.
  - (* [comment removed for export] *)
    unfold pw. cbn [oconc]. unfold wz.
    change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (munch_refl [(RCTX + 56, RCTX + 64)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
    unfold RCTX in MUc.
    (* [comment removed for export] *)
    st1.
    set (st2 := upd_ctx (set_meta_area_head (Some p)) st1).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR2 : rmrep st2 mX) end.
    { eapply (rmrep_ctx_frameW st1 st2 _ _ _ MR1 MUc WMc); try reflexivity.
      - intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - left. unfold ctx_head_cells, RCTX. cbn [ctx st2 st1 upd_ctx s_ctx set_meta_area_head set_avail_meta_areas set_avail_meta_area_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
              c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
        rewrite HT. unfold pw. cbn [oconc]. change (conc st2 ?q) with (conc st q). change (conc st2 p) with (conc st p).
        rewrite (conc_aadd st p 4096) by (rewrite Hr; eauto). unfold wz.
        lazymatch goal with H : rw_cells rsegs ?mX 410856 _ |- _ => exact H end.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia. }
    clear MUc WMc MR1.
    rewrite (carve_st_none st p HT ANone). cbv zeta. fold st1. fold st2.
    change (Z_to_bv 64 410704) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 410848) with (Z_to_bv 64 RMLOCK).
    eapply evt_mono.
    { eapply (ram_carve2 sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc m _ junk lo st st2 p r);
        first [exact MR2 | reflexivity | exact Hr | exact NK | exact S0 | exact S1 | exact SAL | exact SLR | exact ANone | exact FRESH | exact SEC | exact WM0 | idtac].
      - lazymatch goal with H : mem_inv rsegs ?mX |- _ => exact H end.
      - lazymatch goal with H : rw_cells rsegs ?mX (conc st p) _ |- _ => exact H end.
      - lazymatch goal with H : rw_cells rsegs ?mX (conc st p + 24) _ |- _ => exact H end.
      - apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU0; [exact MU0|exact WM0|].
        cbn [ivs_covered]. split; [|split; [|split; [|exact I]]].
        + intros x Hx. apply ram_fp_stack. lia.
        + intros x Hx. apply ram_fp_ctx. unfold RCTX. lia.
        + intros x Hx. eapply (ram_fp_region st lo _ x (fst p) r); [exact Hr| exact NK| lia].
      - lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
      - lazymatch goal with H : stk rsegs ?mX lo _ |- _ => exact H end.
      - bz_ceil; lia.
      - lia. }
    intros ms' RP. exact RP.
Qed.

End ACeilS1.
End RF_am_C.


From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocModel_B. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_am_G. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_am_G.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RF_mm_syscalls.
Module RF_am_F.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
Import OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_free OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocModel_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocModel_B.F_ntf_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_am_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_am_K OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_am_G.F_am_C OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_am_G.F_am_F. (* [comment removed for export] *)            
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prog.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_mm_syscalls OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_ntf_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_am_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_am_K OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_am_H.RF_am_C.
 Unset Lia Cache.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations.
Local Open Scope bv_scope.
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
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_disp_fin : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate) (p : aptr) (r : region),
  rmrep st m -> c_avail_meta_area_count (ctx st) <> 0 -> 0 <= c_avail_meta_area_count (ctx st) < 2^64 ->
  c_avail_meta_areas (ctx st) = Some p -> (s_regions st) !! (fst p) = Some r -> pgal (snd p) -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
  evt rsegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                                   (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x29e64) fc None m (seg_rom rsegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x29cc4) fc None m (seg_rom rsegs)).
Proof.
  intros until r. intros MR CNT CR AMA Hr SAL S0 S1.
  cps_pose MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite AMA in C1.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  cps_pose WF as (_ & WR & _). cps_destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & _). bz_ceil.
  pose proof (conc_region' st p r Hr) as Cp. pose proof (round_up_pg_ge (r_len r)) as RU.
  assert (AL : Z.land (conc st p) 4095 = 0).
  { rewrite Cp. unfold pgal in SAL. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
    clear - RBAL SAL S0 RB0. Z.div_mod_to_equations. lia. }
  assert (AL' : Z.land 4095 (conc st p) = 0) by (rewrite Z.land_comm; exact AL).
  assert (PB : 0 <= conc st p < 2^64) by lia.
  clear RBAL RU RBC RL0 WR.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  (* [comment removed for export] *)
  st1. st1.
  assert (CF : negb (bv_eqb (Z_to_bv 64 (c_avail_meta_area_count (ctx st))) (Z_to_bv 64 0)) = true)
    by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Bool.negb_true_iff; apply Z.eqb_neq; exact CNT).
  rewrite CF.
  (* [comment removed for export] *)
  st1. apply Bool.negb_true_iff in CF. rewrite CF. clear CF.
  st1. st1.
  (* [comment removed for export] *)
  st1. st1. rewrite ?AL, ?AL'. st1.
  change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_to_mprotect : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (P : Z),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x29e74) sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 P)
                                   (Z_to_bv 64 P) (Z_to_bv 64 4096) (Z_to_bv 64 3) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 rmprotect_entry) fc None m (seg_rom rsegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x29e64) fc None m (seg_rom rsegs)).
Proof.
  intros.
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  apply evt_done. unfold rmprotect_entry. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_mp_ok0 : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x29dd4) fc None m (seg_rom rsegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x29e74) fc None m (seg_rom rsegs)).
Proof.
  intros.
  st1. rewrite bv_eqb_refl. cbv iota.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_mp_fail : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m0 m : word -> option byte) (junk : list byte) (lo e : Z) (st : mstate),
  rmrep st m -> mem_inv rsegs m -> tp = Z_to_bv 64 0x441e0 ->
  rw_cells rsegs m (errno_addr tp) [C4 (Z_to_bv 64 e)] -> 1 <= e <= 4095 -> e <> 38 ->
  rpres_except (ram_fp st lo (bv_unsigned sp)) m0 m -> wmono rsegs m0 m ->
  rw_cells rsegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk rsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  evt rsegs (fun ms' => ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m0 st (Z_to_bv 64 0) ms'
                        /\ rw_cells rsegs (ms_mem ms') (errno_addr tp) [C4 (Z_to_bv 64 e)])
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x29e74) fc None m (seg_rom rsegs)).
Proof.
  intros until st. intros MR MI TP ERR ER E38 PE0 WM0 FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  cps_pose MR as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
  subst tp. rewrite (unsigned_lit 0x441e0) in * by lia. change (279008 + -164) with 278844 in *.
  change (Z_to_bv 64 e) with (wz e) in ERR.
  bz_ceil; unfold RCTX, RMLOCK, RSSP_GUARD, ram_frame in *.
  (* [comment removed for export] *)
  st1. change (bv_eqb (Z_to_bv 64 (-1)) (Z_to_bv 64 0)) with false. cbv iota.
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  (* [comment removed for export] *)
  st1. rewrite sx32_wz by lia. st1. st1.
  assert (CF : bv_eqb (wz e) (Z_to_bv 64 38) = false)
    by (unfold bv_eqb, wz; rewrite !unsigned_lit by lia; apply Z.eqb_neq; exact E38).
  rewrite CF; clear CF.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRX : rmrep st mX) end.
  { eapply rmrep_transport_high; [exact MR| exact MU| exact WM|]. intros l h [E|[]]; inversion E; subst; bz_ceil; lia. }
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. split.
  - unfold ram_ret_post. do 15 eexists. split; [reflexivity|].
    split.
    { eapply rpres_except_trans; [exact PE0|].
      apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
      cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply ram_fp_stack. lia. }
    split; [eapply wmono_trans; [exact WM0| exact WM]|]. split; [assumption|]. split; [exact ST|]. exact MRX.
  - cbn [ms_mem]. change (wz e) with (Z_to_bv 64 e) in ERR. exact ERR.
Qed.

End ACeilS1.
End RF_am_F.


From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocModel_B. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_am_G.
Module RF_am_G.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
Import OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_free OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocModel_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocModel_B.F_ntf_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_am_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_am_K OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_am_G.F_am_C OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_am_G. (* [comment removed for export] *)            
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prog.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_mm_syscalls OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_ntf_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_am_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_am_K OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_am_H.RF_am_C.
 Unset Lia Cache.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations.
Local Open Scope bv_scope.
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
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_disp_dead : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate),
  rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> c_brk (ctx st) = BrkDead ->
  evt rsegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (2^64 - 1)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 a7
                                   (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x29d74) fc None m (seg_rom rsegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x29cc4) fc None m (seg_rom rsegs)).
Proof.
  intros until st. intros MR CNT BRK.
  cps_pose MR as (WF & (C1 & _ & _ & _ & _ & C6) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
  unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (410856 + 912) with 411768 in C6.
  (* [comment removed for export] *)
  st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* [comment removed for export] *)
  st1. st1. st1.
  change (bv_eqb (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (-1))) with true. cbv iota.
  (* [comment removed for export] *)
  st1. rewrite bv_eqb_refl. cbv iota.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_to_mmap : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate),
  rmrep st m -> 0 <= c_meta_alloc_shift (ctx st) <= 40 ->
  let n := Z.shiftl 2 (c_meta_alloc_shift (ctx st)) in
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x29da0) sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 n)
                                   (Z_to_bv 64 0) (Z_to_bv 64 (n * 4096)) (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a6 a7
                                   (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom rsegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x29d74) fc None m (seg_rom rsegs)).
Proof.
  intros until st. intros MR SH n.
  cps_pose MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  (* [comment removed for export] *)
  st1. st1. st1.
  rewrite (Z.mod_small (c_meta_alloc_shift (ctx st)) 64) by lia.
  assert (NR : 0 < Z.shiftl 2 (c_meta_alloc_shift (ctx st)) <= 2^41).
  { rewrite Z.shiftl_mul_pow2 by lia. split; [apply Z.mul_pos_pos; [lia| apply Z.pow_pos_nonneg; lia]|].
    change (2^41) with (2 * 2^40). apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1.
  apply evt_done. unfold rmmap_entry. subst n. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_mm_fail : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m0 m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate),
  rmrep st m -> mem_inv rsegs m ->
  rpres_except (ram_fp st lo (bv_unsigned sp)) m0 m -> wmono rsegs m0 m ->
  rw_cells rsegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk rsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  evt rsegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m0 st (Z_to_bv 64 0))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x29da0) fc None m (seg_rom rsegs)).
Proof.
  intros until st. intros MR MI PE0 WM0 FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  cps_pose MR as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
  bz_ceil; unfold RCTX, RMLOCK, RSSP_GUARD, ram_frame in *.
  (* [comment removed for export] *)
  st1. rewrite bv_eqb_refl. cbv iota. st1. st1. st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRX : rmrep st mX) end.
  { eapply rmrep_transport_high; [exact MR| exact MU| exact WM|]. intros l h [E|[]]; inversion E; subst; bz_ceil; lia. }
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold ram_ret_post. do 15 eexists. split; [reflexivity|].
  split.
  { eapply rpres_except_trans; [exact PE0|].
    apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
    cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply ram_fp_stack. lia. }
  split; [eapply wmono_trans; [exact WM0| exact WM]|]. split; [assumption|]. split; [exact ST|]. exact MRX.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_mm_ok : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m0 m : word -> option byte) (junk : list byte) (lo x n : Z) (st0 st : mstate) (rid : N) (r : region),
  rmrep st m -> mem_inv rsegs m -> (forall a, ram_fp st0 lo (bv_unsigned sp) a -> ram_fp st lo (bv_unsigned sp) a) ->
  (s_regions st) !! rid = Some r -> r_base r = x -> x mod 4096 = 0 -> 0 < x -> x + 8192 <= alloc_ceiling -> 1 <= n < 2^62 ->
  0 <= c_meta_alloc_shift (ctx st) < 2^62 ->
  rpres_except (ram_fp st0 lo (bv_unsigned sp)) m0 m -> wmono rsegs m0 m ->
  rw_cells rsegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk rsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  evt rsegs (fun ms' => exists m',
        ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (x + 4096)) (Z_to_bv 64 0)
                      (Z_to_bv 64 (c_meta_alloc_shift (ctx st) + 1)) (Z_to_bv 64 (n - 1)) a3 a4 a5 a6 a7
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x29e64) fc None m' (seg_rom rsegs)
        /\ rpres_except (ram_fp st lo (bv_unsigned sp)) m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw)
        /\ stk rsegs m' lo (bv_unsigned sp + -64)
        /\ rmrep (mm_ok_st st rid n) m')
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 n) (Z_to_bv 64 x) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x29da0) fc None m (seg_rom rsegs)).
Proof.
  intros until r. intros MR MI FP0 Hr RB XAL X0 XC NR SH PE0 WM0 FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  cps_pose MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  assert (AL : Z.land (x + 4096) 4095 = 0).
  { change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096. clear - XAL X0. Z.div_mod_to_equations. lia. }
  assert (AL' : Z.land 4095 (x + 4096) = 0) by (rewrite Z.land_comm; exact AL).
  change (x mod 4096 = 0) with (pgal x) in XAL.
  bz_ceil; unfold RCTX, RMLOCK, RSSP_GUARD, ram_frame in *.
  (* [comment removed for export] *)
  st1.
  assert (CF : bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = false)
    by (unfold bv_eqb; rewrite (unsigned_lit x) by lia; change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1)%Z; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1.
  replace ((n + -1) * 1) with (n - 1) by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(RCTX + 40, RCTX + 56); (RCTX + 72, RCTX + 80)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
  unfold RCTX in MUc.
  (* [comment removed for export] *)
  st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR2 : rmrep (mm_ok_st st rid n) mX) end.
  { eapply (rmrep_ctx_frameW st _ _ _ _ MR MUc WMc); try reflexivity.
    - intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - left. unfold ctx_head_cells, RCTX. cbn [ctx mm_ok_st upd_ctx s_ctx set_meta_alloc_shift set_avail_meta_area_count set_avail_meta_areas c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
            c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
      change (pw (mm_ok_st st rid n) ?q) with (pw st q). unfold pw. cbn [oconc]. change (conc (mm_ok_st st rid n) ?q) with (conc st q).
      rewrite (conc_region' st (rid, 4096) r Hr). cbn [snd]. rewrite RB. unfold wz.
      lazymatch goal with H : rw_cells rsegs ?mX 410856 _ |- _ => exact H end.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia. }
  clear MUc WMc.
  (* [comment removed for export] *)
  st1. st1. rewrite ?AL, ?AL'. st1. rewrite bv_eqb_refl. cbv iota.
  apply evt_done. eexists. split; [reflexivity|].
  split.
  { eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE0| exact FP0]|].
    apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
    cbn [ivs_covered]. split; [|split; [|exact I]].
    - intros y Hy. apply ram_fp_stack. lia.
    - intros y Hy. apply ram_fp_ctx. unfold RCTX. lia. }
  split; [first [exact WM0 | eapply wmono_trans; [exact WM0| exact WM]]|]. split; [assumption|]. split; [exact FR|]. split; [exact ST|]. exact MR2.
Qed.

End ACeilS1.
End RF_am_G.

Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_mm_syscalls OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_ntf_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_am_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_am_K OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_am_H.RF_am_C OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_am_H.RF_am_F OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_am_H.RF_am_G.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLiaP.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac MA.F_malloc_free.mlia ::= RangeFast.rc_decide ltac:(MA.F_malloc_free.pow_lits; Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= lia_acp.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_disp_untried : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate),
  rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> c_brk (ctx st) = BrkUntried ->
  evt rsegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 4095) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
                                   (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x29d00) fc None m (seg_rom rsegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x29cc4) fc None m (seg_rom rsegs)).
Proof.
  intros until st. intros MR CNT BRK.
  cps_pose MR as (WF & (C1 & _ & _ & _ & _ & C6) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
  unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (410856 + 912) with 411768 in C6.
  (* [comment removed for export] *)
  st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* [comment removed for export] *)
  st1. st1. st1.
  change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 (-1))) with false. cbv iota.
  st1. rewrite bv_eqb_refl. cbv iota.
  st1. st1. st1.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ram_disp_live : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate) (rid : N) (off : Z),
  rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> c_brk (ctx st) = BrkLive rid off ->
  0 < conc st (rid, off) -> conc st (rid, off) + 4096 < 2^64 ->
  evt rsegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc st (rid, off) + 4096))
                                   (Z_to_bv 64 (conc st (rid, off) + 4096)) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
                                   (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                             F (Z_to_bv 64 0x29ce8) fc None m (seg_rom rsegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x29cc4) fc None m (seg_rom rsegs)).
Proof.
  intros until off. intros MR CNT BRK C0 C1b.
  cps_pose MR as (WF & (C1 & _ & _ & _ & _ & C6) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
  unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (410856 + 912) with 411768 in C6.
  (* [comment removed for export] *)
  st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* [comment removed for export] *)
  st1. st1. st1.
  assert (CF : bv_eqb (Z_to_bv 64 (conc st (rid, off))) (Z_to_bv 64 (-1)) = false)
    by (unfold bv_eqb; rewrite (unsigned_lit (conc st (rid, off))) by lia; change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1)%Z; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.
  st1.
  assert (CF : bv_eqb (Z_to_bv 64 (conc st (rid, off))) (Z_to_bv 64 0) = false)
    by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.
  st1. st1. st1.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section BRKNODES.
Variables (x1 sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
          (m : word -> option byte).

Definition rbrk_regs (a0 : word) : _ :=
  mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

(* [comment removed for export] *)
Lemma ram_brk0_node :
  impl rsegs (at_node rsegs) (enode (NBrk 0) dec_brk0)
       (epost (fun r ms' => ms' = MS (rbrk_regs (Z_to_bv 64 r)) F (Z_to_bv 64 0x29d04) fc None m (seg_rom rsegs) /\ 0 <= r < 2^64))
       (MS (rbrk_regs (Z_to_bv 64 0)) F (Z_to_bv 64 0x29d00) fc None m (seg_rom rsegs)).
Proof.
  unfold rbrk_regs. apply impl_enode. step_ecall. split. { at_node_solve. }
  intros rsp r Hdec. apply dec_brk0_Some in Hdec. destruct Hdec as [-> Hr]. unfold eff0.
  rewrite nret_MSsvc, mkR_set_a0, apply_mem_none, lit_add_lit. replace (0x29d00 + 4)%Z with 0x29d04%Z by reflexivity.
  apply evt_done. split; [reflexivity| exact Hr].
Qed.

(* [comment removed for export] *)
Lemma ram_brk_node_at (pc : Z) :
  (pc = 0x29ce8 \/ pc = 0x29d24) -> forall cur req, req <> 0 ->
  impl rsegs (at_node rsegs) (enode (NBrk req) (dec_brk cur req))
       (epost (fun a ms' => ms' = MS (rbrk_regs (Z_to_bv 64 (brk_res cur req a))) F (Z_to_bv 64 (pc + 4)) fc None (brk_mem m cur req a) (seg_rom rsegs)))
       (MS (rbrk_regs (Z_to_bv 64 req)) F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
  intros Hpc cur req NZ. unfold rbrk_regs.
  destruct Hpc as [-> | ->]; (apply impl_enode; step_ecall; split; [at_node_solve|]);
    intros rsp a Hdec; apply dec_brk_Some in Hdec; (destruct a; rewrite Hdec; unfold eff0, brk_res, brk_mem, zeros_of;
      rewrite nret_MSsvc, mkR_set_a0, lit_add_lit;
      [ destruct (brk_new_pages cur req) as [[lo n]|]; [rewrite apply_mem_zeros | rewrite apply_mem_none]
      | rewrite apply_mem_none ];
      apply evt_done; reflexivity).
Qed.
End BRKNODES.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_bu_mid : forall (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc
    (m : word -> option byte) (cur : Z),
  0 < cur < 2^64 -> cur mod 4096 = 0 ->
  rw_cells rsegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists a2' m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 0) a2' a3 a4 a5 a6 (Z_to_bv 64 214)
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x29d24) fc None m' (seg_rom rsegs)
        /\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)])
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 cur) (Z_to_bv 64 4095) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x29d04) fc None m (seg_rom rsegs)).
Proof.
  intros until cur. intros CR CAL TC MI.
  pose proof (munch_refl [(RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (land_neg_aligned cur CR CAL) as AL.
  assert (AL' : Z.land 4095 (bv_unsigned (Z_to_bv 64 (0 + - cur))) = 0) by (rewrite Z.land_comm; exact AL).
  change (cur mod 4096 = 0) with (pgal cur) in CAL.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (410856 + 912) with 411768 in TC. change (410856 + 920) with 411776 in MU. change (410856 + 928) with 411784 in MU.
  (* [comment removed for export] *)
  st1. st1. rewrite ?AL, ?AL'. st1. st1.
  replace (0 + cur) with cur by lia.
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  replace (8192 + cur) with (cur + 8192) by lia.
  apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact TC.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_bu_ok : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) (q0 : byte) (q1 : list byte) F fc
    (m : word -> option byte) (cur : Z),
  0 < cur -> cur + 8192 < 2^64 ->
  rw_cells rsegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)] ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x29d48) sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192))
                                   (Z_to_bv 64 cur) (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a6 (Z_to_bv 64 214)
                                   (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom rsegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 (cur + 8192)) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214)
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x29d28) fc None m (seg_rom rsegs)).
Proof.
  intros until cur. intros C0 C1b TC.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (410856 + 912) with 411768 in TC.
  (* [comment removed for export] *)
  st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  st1. st1. st1. st1. st1. st1. st1.
  apply evt_done. unfold rmmap_entry. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_b_store : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc (m : word -> option byte) (nw : Z),
  0 <= nw < 2^64 ->
  rw_cells rsegs m RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10] ->
  rw_cells rsegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 (nw - 4096)) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x29dd4) fc None m' (seg_rom rsegs)
        /\ munch [(RCTX + 40, RCTX + 48); (RCTX + 920, RCTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 (Z_to_bv 64 1); C8 w7; C8 w8; C8 w9; C8 w10]
        /\ rw_cells rsegs m' (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 nw)])
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 nw) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x29d48) fc None m (seg_rom rsegs)).
Proof.
  intros until nw. intros NW HC TC MI.
  pose proof (munch_refl [(RCTX + 40, RCTX + 48); (RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (410856 + 912) with 411768 in TC.
  change (410856 + 40) with 410896 in MU. change (410856 + 48) with 410904 in MU. change (410856 + 920) with 411776 in MU. change (410856 + 928) with 411784 in MU.
  (* [comment removed for export] *)
  st1. st1. rewrite ?(unsigned_lit nw) by lia. replace (nw + - (4096)) with (nw - 4096) by lia. st1. change (Z.shiftr 4096 12) with 1. st1. st1.
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact HC| exact TC].
Qed.

(* [comment removed for export] *)
Lemma ram_bl_ok : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc (m : word -> option byte) (nw : Z),
  0 <= nw < 2^64 ->
  rw_cells rsegs m RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10] ->
  rw_cells rsegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 (nw - 4096)) (Z_to_bv 64 nw) a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x29dd4) fc None m' (seg_rom rsegs)
        /\ munch [(RCTX + 40, RCTX + 48); (RCTX + 920, RCTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 (Z_to_bv 64 1); C8 w7; C8 w8; C8 w9; C8 w10]
        /\ rw_cells rsegs m' (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 nw)])
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 nw) (Z_to_bv 64 nw) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x29cec) fc None m (seg_rom rsegs)).
Proof.
  intros until nw. intros NW HC TC MI.
  (* [comment removed for export] *)
  st1. rewrite bv_eqb_refl. cbv iota.
  eapply (ram_b_store sp gp tp t0 t1 t2 _ a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 q0 q1 q2 F fc m nw NW HC TC MI).
Qed.

(* [comment removed for export] *)
Lemma ram_brk_dead : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (q0 : byte) (q1 : list byte) (q2 : word) F fc (m0 m : word -> option byte) (st : mstate),
  rmrep st m0 -> munch [(RCTX + 920, RCTX + 928)]%Z m0 m -> wmono rsegs m0 m ->
  c_avail_meta_area_count (ctx st) = 0 ->
  rw_cells rsegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> q0 = b8 (c_seq (ctx st)) -> q1 = zeros 7 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x29d74) fc None m' (seg_rom rsegs)
        /\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rmrep (upd_ctx (set_brk BrkDead) st) m')
      (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x29d5c) fc None m (seg_rom rsegs)).
Proof.
  intros until st. intros MR MU0 WM0 CNT TC -> -> MI.
  cps_pose MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite CNT in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  lazymatch type of C1 with rw_cells _ _ _ ?cs =>
    assert (C1' : rw_cells rsegs m RCTX cs)
      by (eapply RMallocKit_B.rrw_cells_agree; [exact C1| | exact WM0]; cbn [cells_size csize Nat.add]; intros y Hy; apply MU0;
          rewrite wa_unsigned by (unfold RCTX in *; lia); unfold RCTX in *; cbn; lia) end.
  clear C1.
  pose proof (munch_refl [(RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (410856 + 912) with 411768 in TC.
  change (410856 + 920) with 411776 in MU, MU0. change (410856 + 928) with 411784 in MU, MU0.
  (* [comment removed for export] *)
  st1. st1. st1. st1. rewrite bv_eqb_refl. cbv iota.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR' : rmrep (upd_ctx (set_brk BrkDead) st) mX) end.
  { eapply (rmrep_ctx_frameW st _ m0 _ [(RCTX + 920, RCTX + 928)]%Z MR); try reflexivity.
    - unfold RCTX. first [exact MU0 | eapply munch_trans; [exact MU0| exact MU]].
    - first [exact WM0 | eapply wmono_trans; [exact WM0| exact WM]].
    - intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - left. unfold ctx_tail_cells, brk_word, RCTX. cbn [ctx upd_ctx s_ctx set_brk c_brk c_seq]. change (410856 + 912) with 411768.
      replace (wz (2 ^ 64 - 1)) with (Z_to_bv 64 (-1)) by (apply Z_to_bv_eqm; reflexivity).
      lazymatch goal with H : rw_cells rsegs ?mX 411768 _ |- _ => exact H end. }
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact MR'.
Qed.

(* [comment removed for export] *)
Lemma ram_bl_fail : forall (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    F fc (m : word -> option byte) (st : mstate) (old : Z),
  rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> 0 < old -> old + 4096 < 2^64 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (old + 4096)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x29d74) fc None m' (seg_rom rsegs)
        /\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rmrep (upd_ctx (set_brk BrkDead) st) m')
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (old + 4096)) (Z_to_bv 64 old) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x29cec) fc None m (seg_rom rsegs)).
Proof.
  intros until old. intros MR CNT O0 O1 MI.
  cps_pose MR as (WF & (_ & _ & _ & _ & _ & C6) & _). unfold ctx_tail_cells in C6.
  (* [comment removed for export] *)
  st1.
  assert (CF : bv_eqb (Z_to_bv 64 old) (Z_to_bv 64 (old + 4096)) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.
  st1.
  eapply (ram_brk_dead sp gp tp t0 t1 t2 _ _ _ _ a2 a3 a4 a5 a6 _ s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m m st MR (munch_refl _ m) (wmono_refl rsegs m) CNT C6 eq_refl eq_refl MI).
Qed.

(* [comment removed for export] *)
Lemma ram_bu_fail : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (q0 : byte) (q1 : list byte) F fc (m0 m : word -> option byte) (st : mstate) (cur : Z),
  rmrep st m0 -> munch [(RCTX + 920, RCTX + 928)]%Z m0 m -> wmono rsegs m0 m ->
  c_avail_meta_area_count (ctx st) = 0 -> 0 < cur -> cur < 2^64 ->
  rw_cells rsegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)] -> q0 = b8 (c_seq (ctx st)) -> q1 = zeros 7 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x29d74) fc None m' (seg_rom rsegs)
        /\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rmrep (upd_ctx (set_brk BrkDead) st) m')
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 cur) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214)
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x29d28) fc None m (seg_rom rsegs)).
Proof.
  intros until cur. intros MR MU0 WM0 CNT C0 C1b TC -> -> MI.
  (* [comment removed for export] *)
  st1.
  assert (CF : negb (bv_eqb (Z_to_bv 64 cur) (Z_to_bv 64 (cur + 8192))) = true).
  { apply Bool.negb_true_iff. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
    apply Z.eqb_neq. rewrite (Z.mod_small cur) by lia. Z.div_mod_to_equations. lia. }
  rewrite CF; clear CF.
  eapply (ram_brk_dead sp gp tp t0 t1 t2 _ _ _ _ a2 a3 a4 a5 a6 _ s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m0 m st MR MU0 WM0 CNT TC eq_refl eq_refl MI).
Qed.

End ACeilS1.
