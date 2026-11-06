(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCBlock BzCDriver BzArrD CmpMem CmpCut CmpArith CmpArith2 CmpSess CmpSessB CmpSdTac GlueTac BzInv BzCLemmas1 CmpFsKit0 AsanKit AsanCut.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_msV A0_cmp_cbV A0_b2c_hcV A0_b2c_wrV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpHmKit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit.
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Ltac dead := let KD := fresh "KD" in if_cases KD; zify_cond_z KD; [exfalso; lia|]; clear KD.
Ltac lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
  | _ => idtac
  end.
(* [comment removed for export] *)

Section A0WRE.
  Variables (cx : cctx) (Q : machine_state -> Prop).
  Variables (SHE SHS : Z) (ob on dbza : Z) (p1 p2 : word) (P STRM lo : Z).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation FT := (c_FT cx).
  Notation cSB := (Z_to_bv 64 2147450880).
  Hypothesis ESTRM : STRM = (c_bz cx + BZF_STRM)%Z.
  Hypothesis CX : cctx_ok cx.
  Hypothesis AE : sanchor E SHE. Hypothesis AS : sanchor STRM SHS.
  Hypothesis SLO : (0x61e000 <= STRM)%Z. Hypothesis SHI : (STRM + 80 <= CEILv)%Z.
  Hypothesis LLO : (CEILv <= lo)%Z. Hypothesis PLO : (lo <= P)%Z. Hypothesis PHI : (P + 64 <= 18446744073709551616)%Z.
  Hypothesis SES : apartv E ESTATE_SIZE STRM 80.

  (* [comment removed for export] *)
  Notation ENDR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (Z_to_bv 64 (STRM + 48)) (Z_to_bv 64 STRM) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (STRM + 72)) (Z_to_bv 64 (STRM + 64)) (Z_to_bv 64 E) (Z_to_bv 64 (SHS + 6)) cSB s7 s8 s9 s10 s11 t3 t4 t5 t6).

  Definition end_W : list (Z * Z) := [(P, P + 64)]%Z.

  (* [comment removed for export] *)
  Lemma A0_end_X1 : forall g e z (ni : Z) (m : amem) (ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    P = (bv_unsigned sp - 64)%Z ->
    stk a0segs m lo (bv_unsigned sp) -> rw_cells a0segs m E (EHEAD1 cx g e) -> rw_cells a0segs m STRM (STRMB cx ob on dbza DBZF z ni p1 p2) ->
    mem_inv a0segs m -> aconsts A0C m ->
    shzW a0segs end_W m E (E + ESTATE_SIZE) -> shzW a0segs end_W m STRM (STRM + 80) ->
    (forall m' (a3' : word),
        rw_cells a0segs m' P (ESAVED s6 s5 s4 s3 s2 s1 s0 ra) -> stk a0segs m' lo P ->
        rw_cells a0segs m' E (EHEAD1 cx g e) -> rw_cells a0segs m' STRM (STRMB cx ob on dbza DBZF z ni p1 p2) ->
        mem_inv a0segs m' -> munch end_W m m' -> wmono a0segs m m' ->
        evt a0segs Q (MS (ENDR (Z_to_bv 64 0x83d4c) t0 t1 t2 (Z_to_bv 64 A1) (Z_to_bv 64 A1) (Z_to_bv 64 DBZF) a3' a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 A0_FREE) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 STRM) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x83c8c) fc None m (seg_rom a0segs)).
  Proof.
    intros g e z ni m ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 EP ST EH1 SM MI AC SHe SHs K.
    cb_ranges CX. unfold CEILv, apartv, ESTATE_SIZE in *. box_ors.
    destruct AC as [GOT SBV]. cbn [aci_segs aci_c aci_got_sh aci_shvar A0C ci_segs] in GOT, SBV.
    pose proof (munch_refl end_W m) as MU. pose proof (wmono_refl a0segs m) as WM. unfold end_W in MU, SHe, SHs.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    pose proof (proj2 AE : saddr E SHE) as AEs.
    unfold EHEAD1 in EH1. rewrite <- ESTRM in EH1. unfold STRMB, DBZF in SM.
    carve_frame 64%nat ST.
    apply (rw_cells_split_CB a0segs _ _ [] 64 _ [] [8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity].
    cbn [mk_CB_cells app] in FR.
    (* [comment removed for export] *)
    wstep. do 8 wstep.
    replace (bv_unsigned sp + -64)%Z with P in * by lia.
    (* [comment removed for export] *)
    arun. dead. arun_to 0x83cd4%Z. sh_norm.
    (* [comment removed for export] *)
    arun. dead. arun. dead. arun. dead. arun. dead.
    arun_to 0x53d54%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _) end;
      [ unfold A0_FREE, DBZF; st_eq | unfold ESAVED; exact FR | exact ST | unfold EHEAD1; rewrite <- ESTRM; exact EH1 | unfold STRMB, DBZF; exact SM | assumption | unfold end_W; exact MU | exact WM ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_end_X2 : forall g e z (ni : Z) (m : amem) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells a0segs m E (EHEAD1 cx g e) -> rw_cells a0segs m STRM (STRMB cx ob on dbza DBZF z ni p1 p2) ->
    shzW a0segs [] m E (E + ESTATE_SIZE) -> shzW a0segs [] m STRM (STRM + 80) ->
    evt a0segs Q (MS (ENDR (Z_to_bv 64 0x83d94) t0 t1 t2 (Z_to_bv 64 A2) (Z_to_bv 64 A2) (Z_to_bv 64 DBZF) a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 A0_FREE) fc None m (seg_rom a0segs)) ->
    evt a0segs Q (MS (ENDR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x83d4c) fc None m (seg_rom a0segs)).
  Proof.
    intros g e z ni m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 EH1 SM SHe SHs K.
    cb_ranges CX. unfold CEILv, apartv, ESTATE_SIZE in *. box_ors.
    pose proof (munch_refl [] m) as MU.
    unfold EHEAD1 in EH1. rewrite <- ESTRM in EH1. unfold STRMB, DBZF in SM.
    (* [comment removed for export] *)
    arun. dead. arun. dead. arun_to 0x53d54%Z.
    enter_with K. unfold A0_FREE, DBZF. st_eq.
  Qed.

  Lemma A0_end_X3 : forall g e z (ni : Z) (m : amem) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells a0segs m E (EHEAD1 cx g e) -> rw_cells a0segs m STRM (STRMB cx ob on dbza DBZF z ni p1 p2) ->
    shzW a0segs [] m E (E + ESTATE_SIZE) -> shzW a0segs [] m STRM (STRM + 80) ->
    evt a0segs Q (MS (ENDR (Z_to_bv 64 0x83ddc) t0 t1 t2 (Z_to_bv 64 FT) (Z_to_bv 64 FT) (Z_to_bv 64 DBZF) a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 A0_FREE) fc None m (seg_rom a0segs)) ->
    evt a0segs Q (MS (ENDR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x83d94) fc None m (seg_rom a0segs)).
  Proof.
    intros g e z ni m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 EH1 SM SHe SHs K.
    cb_ranges CX. unfold CEILv, apartv, ESTATE_SIZE, FTAB_WORDS in *. box_ors.
    pose proof (munch_refl [] m) as MU.
    unfold EHEAD1 in EH1. rewrite <- ESTRM in EH1. unfold STRMB, DBZF in SM.
    arun. dead. arun. dead. arun_to 0x53d54%Z.
    enter_with K. unfold A0_FREE, DBZF. st_eq.
  Qed.

  Lemma A0_end_X4 : forall z (ni : Z) (m : amem) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells a0segs m STRM (STRMB cx ob on dbza DBZF z ni p1 p2) -> shzW a0segs [] m STRM (STRM + 80) ->
    evt a0segs Q (MS (ENDR (Z_to_bv 64 0x83e14) t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 E) (Z_to_bv 64 DBZF) a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 A0_FREE) fc None m (seg_rom a0segs)) ->
    evt a0segs Q (MS (ENDR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x83ddc) fc None m (seg_rom a0segs)).
  Proof.
    intros z ni m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 SM SHs K.
    cb_ranges CX. unfold CEILv, apartv, ESTATE_SIZE in *. box_ors.
    pose proof (munch_refl [] m) as MU.
    unfold STRMB, DBZF in SM.
    (* [comment removed for export] *)
    arun. dead. arun_to 0x53d54%Z.
    enter_with K. unfold A0_FREE, DBZF. st_eq.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition end5_W : list (Z * Z) := [(STRM + 48, STRM + 56)]%Z.
  Lemma A0_end_X5 : forall z (ni : Z) (m : amem) (sp : word) (c6 c5 c4 c3 c2 c1 c0 cra : word)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    P = (bv_unsigned sp - 64)%Z ->
    rw_cells a0segs m STRM (STRMB cx ob on dbza DBZF z ni p1 p2) -> rw_cells a0segs m P (ESAVED c6 c5 c4 c3 c2 c1 c0 cra) -> stk a0segs m lo P ->
    mem_inv a0segs m -> shzW a0segs end5_W m STRM (STRM + 80) ->
    (forall m',
        rw_cells a0segs m' STRM (STRMS ob on dbza DBZF z ni p1 p2 0) -> stk a0segs m' lo (bv_unsigned sp) ->
        mem_inv a0segs m' -> munch end5_W m m' -> wmono a0segs m m' ->
        evt a0segs Q (MS (mkR cra sp gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 c2 c3 c4 c5 c6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (ret_pc cra) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (ENDR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x83e14) fc None m (seg_rom a0segs)).
  Proof.
    intros z ni m sp c6 c5 c4 c3 c2 c1 c0 cra ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 EP SM SAV ST MI SHs K.
    cb_ranges CX. unfold CEILv, apartv, ESTATE_SIZE in *. box_ors.
    pose proof (munch_refl end5_W m) as MU. pose proof (wmono_refl a0segs m) as WM. unfold end5_W in MU, SHs.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    unfold STRMB, DBZF in SM. unfold ESAVED in SAV.
    (* [comment removed for export] *)
    arun_to 0x83e1c%Z. wstep. lit_store. do 8 wstep. wstep.
    lazymatch goal with SAV' : rw_cells a0segs ?mm P _, ST' : stk a0segs ?mm lo P |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (stk_of_rw_cells a0segs _ _ _ SAV') as K5; cbn [cells_size csize Nat.add] in K5; change (Z.of_nat 64) with 64%Z in K5;
      pose proof (stk_join a0segs mm lo P P (P + 64) ST' K5 eq_refl ltac:(lia)) as ST2 end.
    replace (P + 64)%Z with (bv_unsigned sp) in ST2 by lia.
    replace (Z_to_bv 64 (P + 64)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia).
    (* [comment removed for export] *)
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => eapply (K mm) end;
      [ unfold STRMS, DBZF; exact SM | exact ST2 | assumption | unfold end5_W; exact MU | exact WM ].
  Qed.

End A0WRE.

End ACeilS1.
