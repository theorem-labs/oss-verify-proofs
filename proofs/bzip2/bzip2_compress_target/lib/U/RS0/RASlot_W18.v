(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_AS.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_AS ASlot_W0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require ASlot_I ASlot_W18.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS.MallocNat OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp.ASlot_W1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_I OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W18.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMalloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMallocKit_A2 RMalloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RF_malloc_join.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W4.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W4.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RF_ntf_A.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W4.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W4.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_get_meta OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_fp.RMallocKit_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_A2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_malloc_join.RAllocSlot_iface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W4.RASlot_I OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W4.RMallocKit_A3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_ntf_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W4.RASlot_W2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W4.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations.
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
Lemma rmrep_set_free_head : forall st m v,
  rmrep st m ->
  rmrep (upd_ctx (set_free_meta_head v) st) (write_to_mem m (wa (RCTX + 16)) (le8 (pw st v))).
Proof.
  intros st m v MR. cps_pose MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (length_le8 (pw st v)) as L8.
  pose proof (munch_write [(RCTX + 16, RCTX + 24)] m m (RCTX + 16) (le8 (pw st v)) (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(rewrite L8; unfold RCTX; lia) ltac:(rewrite L8; cbn [inside]; lia)) as MU.
  pose proof (wmono_write rsegs m m (wa (RCTX + 16)) (le8 (pw st v)) (wmono_refl rsegs m)) as WM.
  eapply (rmrep_ctx_frameW st (upd_ctx (set_free_meta_head v) st) m _ _ MR MU WM); try reflexivity.
  - intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia.
  - left.
    pose proof (rw_cells_write rsegs m RCTX (ctx_head_cells st) 16 (C8 (pw st (c_free_meta_head (ctx st)))) (C8 (pw st v)) X1 eq_refl eq_refl I) as W.
    cbn [cbytes cell_upd ctx_head_cells Nat.eqb Z.of_nat Pos.of_succ_nat Pos.succ] in W.
    unfold ctx_head_cells, ctx in *. cbn [s_ctx upd_ctx set_free_meta_head c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
      c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
    exact W.
  - right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
  - right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
  - right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
  - right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
    unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx set_free_meta_head c_seq c_brk]. reflexivity.
Qed.

Lemma rmrep_extW : forall stX stY m,
  rmrep stX m ->
  s_regions stY = s_regions stX -> ctx stY = ctx stX -> (forall q, get_meta_rec stY q = get_meta_rec stX q) ->
  s_areas stY = s_areas stX -> s_groups stY = s_groups stX -> (forall rid, get_shadow stY rid = get_shadow stX rid) ->
  s_reserved stY = s_reserved stX ->
  rmrep stY m.
Proof.
  (intros stX stY m; cps_intros (WF & CX & GL & AR & GR & SH); intros ER EC EM EA EG ES ERs).
  assert (Hconc : forall q, conc stY q = conc stX q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
  split; [|split; [|split; [exact GL|split; [|split]]]].
  - unfold rregions_wf. rewrite ER, EA, EG, ERs. exact WF.
  - eapply rmrep_ctx_ext; [exact EC| exact Hconc| exact CX].
  - intros a ar Ha. rewrite EA in Ha. eapply rarea_rep_ext; [exact Hconc| intros; apply EM| exact (AR a ar Ha)].
  - intros b gh Hb. rewrite EG in Hb. eapply rgroup_rep_ext; [exact Hconc| exact (GR b gh Hb)].
  - intros rid r Hr Hk. rewrite ER in Hr. eapply rshadow_rep_ext; [apply ES| exact (SH rid r Hr Hk)].
Qed.
End ACeilS1.


(* [comment removed for export] *)
Ltac rraw_store_finishF A bs' FR MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (rw_cells_frame rsegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write rsegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv rsegs mX |- _ =>
      apply (mem_inv_store rsegs mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.
Section ACeilS2. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


Section FAILM.
Variables (st : mstate) (mt : aptr).
Let G := conc st mt.
Hypothesis MST : meta_slot st mt.
(* [comment removed for export] *)
Hypothesis FL : forall h, c_free_meta_head (ctx st) = Some h ->
  meta_slot st h /\ h <> mt /\ exists p, m_prev (get_meta_rec st h) = Some p /\ meta_slot st p /\ p <> mt.

Definition rfailW (spv : Z) : list (Z * Z) :=
  (spv - 144, spv) :: (G, G + 40) :: (RCTX + 16, RCTX + 24)
  :: match c_free_meta_head (ctx st) with
     | Some h => (conc st h, conc st h + 40)
                 :: match m_prev (get_meta_rec st h) with Some p => [(conc st p, conc st p + 40)] | None => [] end
     | None => []
     end.

(* [comment removed for export] *)
Lemma rfailm1_walk :
  forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
         (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc m junk,
  rmrep st m -> mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  alloc_ceiling <= bv_unsigned sp - 144 ->
  evt rsegs (fun ms' => exists (a1' s6' : word) m' junk',
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (Z_to_bv 64 (-1)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x2aa64) fc None m' (seg_rom rsegs)
      /\ rw_cells rsegs m' (bv_unsigned sp + -144) (rta_frame junk' s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav)
      /\ munch (rfailW (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ rmrep (as_fm_st st mt) m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2a65c) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros MR MI FR SPC.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  cps_pose (rmeta_slot_bounds st m mt MR MST) as (Gpos & GC & GI & G4 & _). fold G in Gpos, GC, GI, G4.
  unfold rfailW. bz_ceil; unfold RCTX, RMLOCK, rta_frame in *.
  (* [comment removed for export] *)
  assert (PRE : forall W, In (bv_unsigned sp - 144, bv_unsigned sp) W -> In (G, G + 40) W ->
    evt rsegs (fun ms' => exists m' junk',
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (Z_to_bv 64 (-1)) (pw st (c_free_meta_head (ctx st))) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 410848) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x2a6b8) fc None m' (seg_rom rsegs)
      /\ rw_cells rsegs m' (bv_unsigned sp + -144) ([CB 48 junk'; C8 (wz run_guard); C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav])
      /\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ rmrep (put_meta mt meta0 st) m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 410848) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2a65c) fc None m (seg_rom rsegs))).
  { intros W HW1 HW2.
    cps_pose MR as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. cbv zeta in CX1. unfold RCTX in CX1.
    rmchunk MR MST CH. fold G in CH.
    (* [comment removed for export] *)
    lazymatch type of CH with rw_cells rsegs m G [?c0; ?c1; ?c2; C4 ?av; C4 ?fr; ?c5] =>
      assert (CH' : rw_cells rsegs m G [c0; c1; c2; CB 8 (le4 av ++ le4 fr); c5]);
      [ eapply rw_cells_congr; [| | | exact CH]; [cbn [cells_bytes cbytes]; rewrite <- !app_assoc; reflexivity| reflexivity| cbn [cells_wf cell_wf]; rewrite length_app, !length_le4; tauto_fast]
      | clear CH ] end.
    pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MUa.
    pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs.
    (* [comment removed for export] *)
    st1. st1. st1. st1. st1.
    lazymatch goal with WMs : wmono rsegs m ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MRs : rmrep st mX) by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; bz_ceil; lia]) end.
    clear MUs.
    rmeta_open G MUb WMb.
    (* [comment removed for export] *)
    step. st1. step. st1. step. st1. step. st1. step. st1.
    (* [comment removed for export] *)
    step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    step. step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    (* [comment removed for export] *)
    step.
    lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR0 : rmrep (put_meta mt meta0 st) mX);
      [ eapply rmrep_put_meta_frame; [exact MRs| exact MST| exact MUb| exact WMb|];
        eapply rw_cells_congr; [| | | exact H]; [cbn [cells_bytes cbytes]; reflexivity| reflexivity| cbn; tauto_fast]
      | clear H MUb WMb ] end.
    lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -144) (CB 8 ?j8 :: _) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (FR' : rw_cells rsegs mX (bv_unsigned sp + -144)
        ([CB 48 (j8 ++ cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]); C8 (wz run_guard); C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]));
      [ destruct H as [[WF BA] WR]; cbn [cells_wf cell_wf] in WF; destruct WF as [L8 WF'];
        split; [split; [cbn [cells_wf cell_wf]; rewrite length_app, L8; cbn; tauto_fast| cbn [cells_bytes cbytes] in BA |- *; rewrite <- !app_assoc; exact BA]
              | cbn [cells_size csize] in WR |- *; exact WR]
      | clear H ] end.
    apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact FR'|].
    split. { eapply munch_weaken; [| exact MUa]. intros y Hy. cbn. split; [| split; [|exact I]]; eapply (outside_In _ y); eauto. }
    split; [assumption|]. split; [assumption| exact MR0]. }
  destruct (c_free_meta_head (ctx st)) as [h|] eqn:FH.
  - (* [comment removed for export] *)
    cps_destruct (FL h eq_refl) as (MSh & NEh & p & HP & MSp & NEp). rewrite HP.
    cps_pose (rmeta_slot_bounds st m h MR MSh) as (Hpos & HC' & HI & _ & _).
    cps_pose (rmeta_slot_bounds st m p MR MSp) as (Ppos & PC & PI & _ & _).
    eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (410856 + 16, 410856 + 24); (conc st h, conc st h + 40); (conc st p, conc st p + 40)]%Z); cbn; tauto_fast|]. cbv beta.
    (intros ms'; cps_intros (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0)). clear PRE WM.
    set (st0 := put_meta mt meta0 st) in *.
    assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
    assert (MSh0 : meta_slot st0 h) by (apply meta_slot_put_meta; exact MSh).
    assert (MSp0 : meta_slot st0 p) by (apply meta_slot_put_meta; exact MSp).
    unfold pw. cbn [oconc]. unfold wz.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
    (* [comment removed for export] *)
    rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
    change (conc st mt) with G in CH.
    rmeta_open G MUa WMa.
    st1.
    lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR1 : rmrep (put_meta mt (mkMeta None (Some h) None 0 0 0 0 0 0) st0) mX);
      [ eapply rmrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto_fast];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 h) with (conc st h); reflexivity
      | clear MUa WMa H ] end.
    set (st1 := put_meta mt _ st0) in MR1.
    assert (MSm1 : meta_slot st1 mt) by (apply meta_slot_put_meta; exact MSm0).
    assert (MSh1 : meta_slot st1 h) by (apply meta_slot_put_meta; exact MSh0).
    assert (MSp1 : meta_slot st1 p) by (apply meta_slot_put_meta; exact MSp0).
    (* [comment removed for export] *)
    rmchunk MR1 MSh1 CH. unfold st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
    rewrite HP in CH. cbn [oconc] in CH.
    step. clear CH.
    (* [comment removed for export] *)
    rmchunk MR1 MSm1 CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH. change (meta_word _) with 0 in CH.
    change (conc st0 mt) with G in CH. change (conc st mt) with G in CH.
    rmeta_open G MUb WMb.
    st1.
    lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR2 : rmrep (put_meta mt (mkMeta (Some p) (Some h) None 0 0 0 0 0 0) st1) mX);
      [ eapply rmrep_put_meta_frame; [exact MR1| exact MSm1| exact MUb| exact WMb|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto_fast];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; reflexivity
      | clear MUb WMb H ] end.
    set (st2 := put_meta mt _ st1) in MR2.
    assert (MSm2 : meta_slot st2 mt) by (apply meta_slot_put_meta; exact MSm1).
    assert (MSh2 : meta_slot st2 h) by (apply meta_slot_put_meta; exact MSh1).
    assert (MSp2 : meta_slot st2 p) by (apply meta_slot_put_meta; exact MSp1).
    (* [comment removed for export] *)
    rmchunk MR2 MSp2 CH. unfold st2, st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
    rmeta_open (conc st p) MUc WMc.
    st1.
    lazymatch goal with H : rw_cells rsegs ?mX (conc st p) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR3 : rmrep (put_meta p (m_set_next (Some mt) (get_meta_rec st p)) st2) mX);
      [ eapply rmrep_put_meta_frame; [exact MR2| exact MSp2| exact MUc| exact WMc|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto_fast];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_next oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
        change (conc st2 mt) with G; reflexivity
      | clear MUc WMc H ] end.
    set (st3 := put_meta p _ st2) in MR3.
    assert (MSm3 : meta_slot st3 mt) by (apply meta_slot_put_meta; exact MSm2).
    assert (MSh3 : meta_slot st3 h) by (apply meta_slot_put_meta; exact MSh2).
    (* [comment removed for export] *)
    rmchunk MR3 MSm3 CH. unfold st3 in CH. rewrite get_meta_rec_put_other in CH by (intros E; exact (NEp (eq_sym E))).
    unfold st2 in CH. rewrite get_meta_rec_put_same in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH.
    change (conc st mt) with G in CH.
    step. clear CH.
    (* [comment removed for export] *)
    rmchunk MR3 MSh3 CH.
    rmeta_open (conc st h) MUd WMd.
    st1.
    lazymatch goal with H : rw_cells rsegs ?mX (conc st h) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR4 : rmrep (put_meta h (m_set_prev (Some mt) (get_meta_rec st3 h)) st3) mX);
      [ eapply rmrep_put_meta_frame; [exact MR3| exact MSh3| exact MUd| exact WMd|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto_fast];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_prev oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
        change (conc st3 mt) with G; reflexivity
      | clear MUd WMd H ] end.
    (* [comment removed for export] *)
    step.
    apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact FR1|].
    split; [exact MU|]. split; [exact WM1|]. split; [assumption|].
    unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
    unfold as_fm_link. rewrite get_meta_rec_put_other by congruence. rewrite HP. cbv zeta.
    eapply (rmrep_extW _ _ _ MR4); try reflexivity.
    intros q. unfold st3, st2, st1, st0, upd_meta.
    destruct (decide (q = h)) as [->|NQh].
    { rewrite !get_meta_rec_put_same. f_equal.
      destruct (decide (h = p)) as [<-|NHp].
      - rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity.
      - rewrite !get_meta_rec_put_other by congruence. reflexivity. }
    rewrite !(get_meta_rec_put_other _ h _ q) by congruence.
    destruct (decide (q = p)) as [->|NQp].
    { rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity. }
    rewrite !(get_meta_rec_put_other _ p _ q) by congruence.
    destruct (decide (q = mt)) as [->|NQm].
    { rewrite !get_meta_rec_put_same. reflexivity. }
    rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
  - (* [comment removed for export] *)
    eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (410856 + 16, 410856 + 24)]%Z); cbn; tauto_fast|]. cbv beta.
    (intros ms'; cps_intros (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0)). clear PRE WM.
    set (st0 := put_meta mt meta0 st) in *.
    assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
    unfold pw. cbn [oconc]. unfold wz.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    (* [comment removed for export] *)
    rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
    change (conc st mt) with G in CH.
    rmeta_open G MUa WMa.
    st1. st1.
    lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR1 : rmrep (put_meta mt (mkMeta (Some mt) (Some mt) None 0 0 0 0 0 0) st0) mX);
      [ eapply rmrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto_fast];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 mt) with G; reflexivity
      | clear MUa WMa H ] end.
    set (st1 := put_meta mt _ st0) in MR1.
    (* [comment removed for export] *)
    step.
    cps_pose MR1 as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. cbv zeta in CX1. unfold RCTX in CX1.
    pose proof (rw_cells_store_ok_at rsegs _ _ _ 16 (C8 (pw st1 (c_free_meta_head (ctx st1)))) 8 (Z_to_bv 64 (410848 + 24)) CX1 eq_refl eq_refl
                  ltac:(unfold wa; f_equal; lia)) as SOK. clear CX1.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_free_head st1 mX (Some mt) MR1) as MR2; unfold RCTX in MR2 end.
    unfold pw in MR2. cbn [oconc] in MR2. change (conc st1 mt) with G in MR2.
    rraw_store_finishF (410856 + 16) (le8 (wz G)) FR1 MU WM1 SOK.
    (* [comment removed for export] *)
    step.
    apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact FR1|].
    split; [exact MU|]. split; [exact WM1|]. split; [assumption|].
    unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
    unfold as_fm_single. cbn [set_head].
    eapply (rmrep_extW _ _ _ MR2); try reflexivity.
    intros q. unfold st1, st0, upd_meta. rewrite !rec_upd_ctx.
    destruct (decide (q = mt)) as [->|NQm].
    { rewrite !get_meta_rec_put_same. reflexivity. }
    rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma rfailm2_walk :
  forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
         (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc m junk,
  rmrep st m -> mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  alloc_ceiling <= bv_unsigned sp - 144 ->
  evt rsegs (fun ms' => exists (s6' : word) m' junk',
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x2aa64) fc None m' (seg_rom rsegs)
      /\ rw_cells rsegs m' (bv_unsigned sp + -144) (rta_frame junk' s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav)
      /\ munch (rfailW (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ rmrep (as_fm_st st mt) m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2a9dc) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros MR MI FR SPC.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  cps_pose (rmeta_slot_bounds st m mt MR MST) as (Gpos & GC & GI & G4 & _). fold G in Gpos, GC, GI, G4.
  unfold rfailW. bz_ceil; unfold RCTX, RMLOCK, rta_frame in *.
  (* [comment removed for export] *)
  assert (PRE : forall W, In (bv_unsigned sp - 144, bv_unsigned sp) W -> In (G, G + 40) W ->
    evt rsegs (fun ms' => exists m' junk',
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (pw st (c_free_meta_head (ctx st))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 410848) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x2aa34) fc None m' (seg_rom rsegs)
      /\ rw_cells rsegs m' (bv_unsigned sp + -144) ([CB 48 junk'; C8 (wz run_guard); C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav])
      /\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ rmrep (put_meta mt meta0 st) m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 410848) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2a9dc) fc None m (seg_rom rsegs))).
  { intros W HW1 HW2.
    cps_pose MR as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. cbv zeta in CX1. unfold RCTX in CX1.
    rmchunk MR MST CH. fold G in CH.
    (* [comment removed for export] *)
    lazymatch type of CH with rw_cells rsegs m G [?c0; ?c1; ?c2; C4 ?av; C4 ?fr; ?c5] =>
      assert (CH' : rw_cells rsegs m G [c0; c1; c2; CB 8 (le4 av ++ le4 fr); c5]);
      [ eapply rw_cells_congr; [| | | exact CH]; [cbn [cells_bytes cbytes]; rewrite <- !app_assoc; reflexivity| reflexivity| cbn [cells_wf cell_wf]; rewrite length_app, !length_le4; tauto_fast]
      | clear CH ] end.
    pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MUa.
    pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs.
    (* [comment removed for export] *)
    st1. st1. st1. st1. st1.
    lazymatch goal with WMs : wmono rsegs m ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MRs : rmrep st mX) by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; bz_ceil; lia]) end.
    clear MUs.
    rmeta_open G MUb WMb.
    (* [comment removed for export] *)
    step. st1. step. st1. step. st1. step. st1. step. st1.
    (* [comment removed for export] *)
    step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    (* [comment removed for export] *)
    step.
    lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR0 : rmrep (put_meta mt meta0 st) mX);
      [ eapply rmrep_put_meta_frame; [exact MRs| exact MST| exact MUb| exact WMb|];
        eapply rw_cells_congr; [| | | exact H]; [cbn [cells_bytes cbytes]; reflexivity| reflexivity| cbn; tauto_fast]
      | clear H MUb WMb ] end.
    lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -144) (CB 8 ?j8 :: _) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (FR' : rw_cells rsegs mX (bv_unsigned sp + -144)
        ([CB 48 (j8 ++ cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]); C8 (wz run_guard); C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]));
      [ destruct H as [[WF BA] WR]; cbn [cells_wf cell_wf] in WF; destruct WF as [L8 WF'];
        split; [split; [cbn [cells_wf cell_wf]; rewrite length_app, L8; cbn; tauto_fast| cbn [cells_bytes cbytes] in BA |- *; rewrite <- !app_assoc; exact BA]
              | cbn [cells_size csize] in WR |- *; exact WR]
      | clear H ] end.
    apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact FR'|].
    split. { eapply munch_weaken; [| exact MUa]. intros y Hy. cbn. split; [| split; [|exact I]]; eapply (outside_In _ y); eauto. }
    split; [assumption|]. split; [assumption| exact MR0]. }
  destruct (c_free_meta_head (ctx st)) as [h|] eqn:FH.
  - (* [comment removed for export] *)
    cps_destruct (FL h eq_refl) as (MSh & NEh & p & HP & MSp & NEp). rewrite HP.
    cps_pose (rmeta_slot_bounds st m h MR MSh) as (Hpos & HC' & HI & _ & _).
    cps_pose (rmeta_slot_bounds st m p MR MSp) as (Ppos & PC & PI & _ & _).
    eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (410856 + 16, 410856 + 24); (conc st h, conc st h + 40); (conc st p, conc st p + 40)]%Z); cbn; tauto_fast|]. cbv beta.
    (intros ms'; cps_intros (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0)). clear PRE WM.
    set (st0 := put_meta mt meta0 st) in *.
    assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
    assert (MSh0 : meta_slot st0 h) by (apply meta_slot_put_meta; exact MSh).
    assert (MSp0 : meta_slot st0 p) by (apply meta_slot_put_meta; exact MSp).
    unfold pw. cbn [oconc]. unfold wz.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
    (* [comment removed for export] *)
    rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
    change (conc st mt) with G in CH.
    rmeta_open G MUa WMa.
    st1.
    lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR1 : rmrep (put_meta mt (mkMeta None (Some h) None 0 0 0 0 0 0) st0) mX);
      [ eapply rmrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto_fast];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 h) with (conc st h); reflexivity
      | clear MUa WMa H ] end.
    set (st1 := put_meta mt _ st0) in MR1.
    assert (MSm1 : meta_slot st1 mt) by (apply meta_slot_put_meta; exact MSm0).
    assert (MSh1 : meta_slot st1 h) by (apply meta_slot_put_meta; exact MSh0).
    assert (MSp1 : meta_slot st1 p) by (apply meta_slot_put_meta; exact MSp0).
    (* [comment removed for export] *)
    rmchunk MR1 MSh1 CH. unfold st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
    rewrite HP in CH. cbn [oconc] in CH.
    step. clear CH.
    (* [comment removed for export] *)
    rmchunk MR1 MSm1 CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH. change (meta_word _) with 0 in CH.
    change (conc st0 mt) with G in CH. change (conc st mt) with G in CH.
    rmeta_open G MUb WMb.
    st1.
    lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR2 : rmrep (put_meta mt (mkMeta (Some p) (Some h) None 0 0 0 0 0 0) st1) mX);
      [ eapply rmrep_put_meta_frame; [exact MR1| exact MSm1| exact MUb| exact WMb|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto_fast];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; reflexivity
      | clear MUb WMb H ] end.
    set (st2 := put_meta mt _ st1) in MR2.
    assert (MSm2 : meta_slot st2 mt) by (apply meta_slot_put_meta; exact MSm1).
    assert (MSh2 : meta_slot st2 h) by (apply meta_slot_put_meta; exact MSh1).
    assert (MSp2 : meta_slot st2 p) by (apply meta_slot_put_meta; exact MSp1).
    (* [comment removed for export] *)
    rmchunk MR2 MSp2 CH. unfold st2, st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
    rmeta_open (conc st p) MUc WMc.
    st1.
    lazymatch goal with H : rw_cells rsegs ?mX (conc st p) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR3 : rmrep (put_meta p (m_set_next (Some mt) (get_meta_rec st p)) st2) mX);
      [ eapply rmrep_put_meta_frame; [exact MR2| exact MSp2| exact MUc| exact WMc|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto_fast];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_next oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
        change (conc st2 mt) with G; reflexivity
      | clear MUc WMc H ] end.
    set (st3 := put_meta p _ st2) in MR3.
    assert (MSm3 : meta_slot st3 mt) by (apply meta_slot_put_meta; exact MSm2).
    assert (MSh3 : meta_slot st3 h) by (apply meta_slot_put_meta; exact MSh2).
    (* [comment removed for export] *)
    rmchunk MR3 MSm3 CH. unfold st3 in CH. rewrite get_meta_rec_put_other in CH by (intros E; exact (NEp (eq_sym E))).
    unfold st2 in CH. rewrite get_meta_rec_put_same in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH.
    change (conc st mt) with G in CH.
    step. clear CH.
    (* [comment removed for export] *)
    step.
    rmchunk MR3 MSh3 CH.
    rmeta_open (conc st h) MUd WMd.
    st1.
    lazymatch goal with H : rw_cells rsegs ?mX (conc st h) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR4 : rmrep (put_meta h (m_set_prev (Some mt) (get_meta_rec st3 h)) st3) mX);
      [ eapply rmrep_put_meta_frame; [exact MR3| exact MSh3| exact MUd| exact WMd|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto_fast];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_prev oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
        change (conc st3 mt) with G; reflexivity
      | clear MUd WMd H ] end.
    (* [comment removed for export] *)
    step.
    apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact FR1|].
    split; [exact MU|]. split; [exact WM1|]. split; [assumption|].
    unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
    unfold as_fm_link. rewrite get_meta_rec_put_other by congruence. rewrite HP. cbv zeta.
    eapply (rmrep_extW _ _ _ MR4); try reflexivity.
    intros q. unfold st3, st2, st1, st0, upd_meta.
    destruct (decide (q = h)) as [->|NQh].
    { rewrite !get_meta_rec_put_same. f_equal.
      destruct (decide (h = p)) as [<-|NHp].
      - rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity.
      - rewrite !get_meta_rec_put_other by congruence. reflexivity. }
    rewrite !(get_meta_rec_put_other _ h _ q) by congruence.
    destruct (decide (q = p)) as [->|NQp].
    { rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity. }
    rewrite !(get_meta_rec_put_other _ p _ q) by congruence.
    destruct (decide (q = mt)) as [->|NQm].
    { rewrite !get_meta_rec_put_same. reflexivity. }
    rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
  - (* [comment removed for export] *)
    eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (410856 + 16, 410856 + 24)]%Z); cbn; tauto_fast|]. cbv beta.
    (intros ms'; cps_intros (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0)). clear PRE WM.
    set (st0 := put_meta mt meta0 st) in *.
    assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
    unfold pw. cbn [oconc]. unfold wz.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    (* [comment removed for export] *)
    rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
    change (conc st mt) with G in CH.
    rmeta_open G MUa WMa.
    st1. st1.
    lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR1 : rmrep (put_meta mt (mkMeta (Some mt) (Some mt) None 0 0 0 0 0 0) st0) mX);
      [ eapply rmrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto_fast];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 mt) with G; reflexivity
      | clear MUa WMa H ] end.
    set (st1 := put_meta mt _ st0) in MR1.
    (* [comment removed for export] *)
    step.
    cps_pose MR1 as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. cbv zeta in CX1. unfold RCTX in CX1.
    pose proof (rw_cells_store_ok_at rsegs _ _ _ 16 (C8 (pw st1 (c_free_meta_head (ctx st1)))) 8 (Z_to_bv 64 (410848 + 24)) CX1 eq_refl eq_refl
                  ltac:(unfold wa; f_equal; lia)) as SOK. clear CX1.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_free_head st1 mX (Some mt) MR1) as MR2; unfold RCTX in MR2 end.
    unfold pw in MR2. cbn [oconc] in MR2. change (conc st1 mt) with G in MR2.
    rraw_store_finishF (410856 + 16) (le8 (wz G)) FR1 MU WM1 SOK.
    (* [comment removed for export] *)
    step.
    apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact FR1|].
    split; [exact MU|]. split; [exact WM1|]. split; [assumption|].
    unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
    unfold as_fm_single. cbn [set_head].
    eapply (rmrep_extW _ _ _ MR2); try reflexivity.
    intros q. unfold st1, st0, upd_meta. rewrite !rec_upd_ctx.
    destruct (decide (q = mt)) as [->|NQm].
    { rewrite !get_meta_rec_put_same. reflexivity. }
    rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
Qed.
End FAILM.

End ACeilS2.
