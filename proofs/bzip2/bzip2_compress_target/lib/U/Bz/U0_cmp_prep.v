(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzArrD BzCLemmas1 CmpMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpArith.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCDriver CmpSess.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Import ListNotations. Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Definition U0_PREP : Z := 0x13e4c.
Definition prep_W (E : Z) : list (Z * Z) := [(E + 108, E + 124); (E + 128, E + 384); (E + 648, E + 652); (E + 660, E + 664)]%Z.

Section Loop.
  Variable Q : machine_state -> Prop.
  Variables (E : Z) (Jb : list byte) (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Hypothesis IE1 : (0 < E)%Z. Hypothesis IE2 : (E + 384 < 2 ^ 64)%Z.
  Variables (m0 : word -> option byte) (ra sp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word).

  Lemma prep_loop : forall (n : nat) (i : Z) (a : zarr) (m : word -> option byte),
    (1 <= Z.of_nat n)%Z -> (i + Z.of_nat n = 256)%Z -> (0 <= i)%Z ->
    u8arr s0segs m (E + 128) (ovb a Jb 256) -> mem_inv s0segs m -> munch [(E + 128, E + 384)]%Z m0 m -> wmono s0segs m0 m ->
    (forall m' (x11 x12 : word),
        u8arr s0segs m' (E + 128) (ovb (inUse_clear a i n) Jb 256) -> mem_inv s0segs m' -> munch [(E + 128, E + 384)]%Z m0 m' -> wmono s0segs m0 m' ->
        evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x11 x12 (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 256) a5 a6 a7
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x13e88) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) (Z_to_bv 64 i) (Z_to_bv 64 (E + 128 + i)) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 256) a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x13e74) fc None m (seg_rom s0segs)).
  Proof using IE1 IE2.
    induction n as [|n IH]; intros i a m Hn Hi Hi0 INU MI MU WM K; [lia|].
    pose proof (ovb_length a Jb 256 ltac:(lia)) as LIU.
    wstep; notrap.
    pose proof (u8arr_store_ok s0segs m (E + 128) _ i _ INU ltac:(rewrite ovb_length_nat; lia) eq_refl) as SO.
    wstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ (le1 ?w)) _) =>
      pose proof (ovb_write1 s0segs mm (E + 128) a Jb 256 i w INU ltac:(lia)) as INU' end.
    clear INU. store_done. rename INU' into INU.
    replace (wr8 a i (bv_unsigned (Z_to_bv 64 0))) with (zset a i 0) in INU by reflexivity.
    wstep. wstep. wstep; if_cases Kb; zify_cond_z Kb.
    - enter_with (IH (i + 1)%Z (zset a i 0)); [st_eq | lia | lia | lia | exact INU | exact MI | exact MU | exact WM |].
      intros m' x11 x12 INU' MI' MU' WM'. eapply K; [| exact MI' | exact MU' | exact WM'].
      rewrite inUse_clear_S. exact INU'.
    - assert (n = 0)%nat by lia. subst n.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _) end; [st_eq | | exact MI | exact MU | exact WM].
      rewrite inUse_clear_S. cbn [inUse_clear]. exact INU.
  Qed.
End Loop.

Section PREP.
  Variable Q : machine_state -> Prop.
  Variables (cx : cctx) (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Notation E := (c_E cx). Notation J := (c_J cx).
  Hypothesis CX : cctx_ok cx. Hypothesis IME : img_apart (ci_hi S0C) E ESTATE_SIZE.

  Ltac pprep :=
    pose proof CX as CX'; unfold cctx_ok in CX'; cbv zeta in CX';
    bz_ceil; bz_params; unfold ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, IMG_HI3, CEIL in CX';
    cps_destruct CX' as (RE1 & RE2 & RA1 & RA1' & RA2 & RA2' & RFT & RFT' & RBZ & RBZ' & RFB & RFB' & ALE & AL1 & AL2 & ALF & ALB & ALFb & LJ & LJB);
    pose proof IME as IME'; unfold img_apart, ESTATE_SIZE, IMG_LO3 in IME'; cbn [ci_hi S0C] in IME';
    bz_ceil; bz_params; unfold ESTATE_SIZE, CEIL in *.

  Lemma U0_prep : forall (g : eg) (e : est) (m : word -> option byte)
      (ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    (0 <= e_blockNo e < 2147483647)%Z ->
    rw_cells s0segs m E (EHEAD1 cx g e) -> rw_cells s0segs m (E + 640) (EHEAD2 cx g e) ->
    u8arr s0segs m (E + 128) (ovb (e_inUse e) (jseg J 128 256) 256) -> mem_inv s0segs m ->
    (forall m' (a1' a2' a3' a4' : word),
        rw_cells s0segs m' E (EHEAD1 cx g (prepare_new_block e)) -> rw_cells s0segs m' (E + 640) (EHEAD2 cx g (prepare_new_block e)) ->
        u8arr s0segs m' (E + 128) (ovb (e_inUse (prepare_new_block e)) (jseg J 128 256) 256) ->
        mem_inv s0segs m' -> munch (prep_W E) m m' -> wmono s0segs m m' ->
        evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1' a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (ret_pc ra) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 U0_PREP) fc None m (seg_rom s0segs)).
  Proof.
    intros g e m ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 BNO EH1 EH2 INU MI K.
    pprep. unfold U0_PREP.
    pose proof (munch_refl (prep_W E) m) as MU. pose proof (wmono_refl s0segs m) as WM. unfold prep_W in MU |- *.
    assert (LE7 : Z.land E 7 = 0%Z).
    { change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. apply (proj2 (Z.mod_divide E 8 ltac:(lia))).
      exists (2 * (E / 16))%Z. pose proof (Z.div_mod E 16 ltac:(lia)) as DM. lia. }
    unfold EHEAD1, EHEAD2 in EH1, EH2.
    pose proof (ovb_length (e_inUse e) (jseg J 128 256) 256 ltac:(lia)) as LIU.
    wstep. rewrite LE7. wstep; notrap.
    wstep. wstep. wstep. wstep. wstep. wstep.
    reword_C4 EH2 2%nat 4294967295%Z. { reflexivity. }
    wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      shelve_mem EH1; shelve_mem EH2;
      enter_with (prep_loop Q E (jseg J 128 256) gp tp F fc ltac:(lia) ltac:(lia) mm ra sp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 256%nat 0%Z (e_inUse e) mm);
      [st_eq | cbn; lia | reflexivity | lia | exact INU | assumption | apply munch_refl | apply wmono_refl |] end.
    clear INU. intros m' x11 x12 INU MI' MUl WMl. unshelve_mems.
    lazymatch type of MUl with munch _ ?ma ?mb => transport_after_call s0segs ma mb MUl WMl end. clear MUl WMl.
    pose proof (ovb_length (inUse_clear (e_inUse e) 0 256) (jseg J 128 256) 256 ltac:(lia)) as LIU'.
    wstep. wstep. wstep; notrap. wstep. wstep.
    eapply K; [exact EH1 | exact EH2 | exact INU | assumption | exact MU | exact WM].
  Qed.
End PREP.

End ACeilS1.
