(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCBlock BzCDriver BzArrD CmpMem CmpCut CmpArith CmpArith2 CmpSess CmpSessB CmpCarve CmpSdTac GlueTac BzInv BzCLemmas1 CmpFsKit0 AsanKit AsanCut AsanCutB0 AsanKitB0.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_msV B0_b2c_cbV B0_b2c_hcV B0_b2c_wrV B0_cmp_prep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpHmKit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit.
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Ltac dead := let KD := fresh "KD" in if_cases KD; zify_cond_z KD; [exfalso; lia|]; clear KD.
Ltac live := let KD := fresh "KD" in if_cases KD; zify_cond_z KD; [|exfalso; lia]; clear KD.
Ltac lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
  | _ => idtac
  end.
(* [comment removed for export] *)
Ltac split_at_cb8 cs :=
  lazymatch cs with
  | CB 8 ?bs :: ?post => constr:((@nil cell, bs, post))
  | ?c :: ?rest => let r := split_at_cb8 rest in lazymatch r with (?pre, ?bs, ?post) => constr:((c :: pre, bs, post)) end
  end.
Ltac cb8_all H :=
  repeat (lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
            let r := split_at_cb8 cs in
            lazymatch r with (?pre, ?bs, ?post) => apply (rw_cells_CB8_C8 segs m A pre bs post) in H; cbn [app] in H end end).
(* [comment removed for export] *)

Section B0WRI.
  Variable Q : machine_state -> Prop.
  Variables (SHS : Z) (P STRM lo : Z).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Notation cSB := (Z_to_bv 64 2147450880).
  Hypothesis AS : sanchor STRM SHS.
  Hypothesis SLO : (0x62b000 <= STRM)%Z. Hypothesis SHI : (STRM + 80 <= CEILv)%Z.
  Hypothesis LLO : (CEILv <= lo)%Z. Hypothesis PLO : (lo <= P)%Z. Hypothesis PHI : (P + 176 <= 18446744073709551616)%Z.

  (* [comment removed for export] *)
  Definition ISLOTS (v0 v8 v16 v24 v32 v40 v48 v56 v64 : word) : list cell := [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 v56; C8 v64].

  Definition init1_W : list (Z * Z) := [(P, P + 176); (STRM + 56, STRM + 72)]%Z.

  (* [comment removed for export] *)
  Lemma B0_init_I1 : forall (m : amem) (w0 w8 w12 w16 w20 w24 w32 w36 w40 w44 w48 : word)
      (ra sp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    P = (bv_unsigned sp - 176)%Z ->
    stk b0segs m lo (bv_unsigned sp) ->
    rw_cells b0segs m STRM (STRMC w0 w8 w12 w16 w20 w24 w32 w36 w40 w44 w48 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
    mem_inv b0segs m -> aconsts B0C m -> shzW b0segs init1_W m STRM (STRM + 80) ->
    (forall m' (v0 v8 v16 v24 v32 v40 v48 v64 : word),
        rw_cells b0segs m' P (ISLOTS v0 v8 v16 v24 v32 v40 v48 (Z_to_bv 64 (SHS + 8)) v64) -> rw_cells b0segs m' (P + 72) (HSAVED s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) -> stk b0segs m' lo P ->
        rw_cells b0segs m' STRM (STRMC w0 w8 w12 w16 w20 w24 w32 w36 w40 w44 w48 (Z_to_bv 64 DBZA) (Z_to_bv 64 DBZF) (Z_to_bv 64 0)) ->
        mem_inv b0segs m' -> munch init1_W m m' -> wmono b0segs m m' ->
        evt b0segs Q (MS (mkR (Z_to_bv 64 0x81818) (Z_to_bv 64 P) gp tp t0 t1 t2 s0 (Z_to_bv 64 STRM) (Z_to_bv 64 55768) (Z_to_bv 64 55768) (Z_to_bv 64 1) (Z_to_bv 64 DBZA) a4 a5 a6 a7
                              (Z_to_bv 64 (SHS + 7)) (Z_to_bv 64 WORKFACTOR) cSB (Z_to_bv 64 (SHS + 9)) (Z_to_bv 64 (STRM + 72)) (Z_to_bv 64 (-2)) (Z_to_bv 64 (STRM + 56)) (Z_to_bv 64 0)
                              (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 (STRM + 64)) t3 t4 t5 t6)
                         F (Z_to_bv 64 B0_MALLOC) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 STRM) (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 0) (Z_to_bv 64 WORKFACTOR) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x816fc) fc None m (seg_rom b0segs)).
  Proof.
    intros m w0 w8 w12 w16 w20 w24 w32 w36 w40 w44 w48 ra sp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 EP ST SM MI AC SHs K.
    unfold CEILv in *. bz_ceil. bz_params.
    destruct AC as [GOT SBV]. cbn [aci_segs aci_c aci_got_sh aci_shvar B0C ci_segs] in GOT, SBV.
    pose proof (munch_refl init1_W m) as MU. pose proof (wmono_refl b0segs m) as WM. unfold init1_W in MU, SHs.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    pose proof (proj1 AS) as SM8.   (* [comment removed for export] *)
    unfold STRMC in SM.
    carve_frame 176%nat ST.
    apply (rw_cells_split_CB b0segs _ _ [] 176 _ [] [8;8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity].
    cbn [mk_CB_cells app] in FR.
    (* [comment removed for export] *)
    wstep. do 13 wstep.
    replace (bv_unsigned sp + -176)%Z with P in * by lia.
    (* [comment removed for export] *)
    brun. dead.
    (* [comment removed for export] *)
    brun. if_cases KD; zify_cond_z KD; [exfalso; clear - KD BZbsL__ BZbsH__; change 18446744073709551615%Z with (Z.ones 64) in KD; rewrite Z.land_ones in KD by lia; mlia|]. clear KD.
    (* [comment removed for export] *)
    brun. dead. brun. live.
    (* [comment removed for export] *)
    brun_to 0x81788%Z. sh_norm.
    (* [comment removed for export] *)
    brun_to 0x817a8%Z. wstep. lit_store.
    (* [comment removed for export] *)
    brun_to 0x817b8%Z. sh_norm.
    (* [comment removed for export] *)
    brun_to 0x817e0%Z. wstep. lit_store.
    (* [comment removed for export] *)
    brun_to 0x817f8%Z. sh_norm.
    (* [comment removed for export] *)
    brun_to 0x537a4%Z.
    cb8_all FR.
    destruct (rw_cells_cutZ b0segs _ P _ 9%nat FR) as [SLa SVc]. cbn [firstn skipn cells_size csize Nat.add] in SLa, SVc. change (Z.of_nat 72) with 72%Z in SVc.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _) end;
      [ unfold B0_MALLOC, DBZA; st_eq | unfold ISLOTS; exact SLa | unfold HSAVED; exact SVc | exact ST | unfold STRMC, DBZA, DBZF; exact SM | assumption | unfold init1_W; exact MU | exact WM ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section WithE.
  Variables (E SHE : Z) (J : list byte).
  Hypothesis AE : sanchor E SHE.
  Hypothesis ELO : (0x62b000 <= E)%Z. Hypothesis EHI : (E + 55768 <= CEILv)%Z.
  Hypothesis SES : apartv E 55768 STRM 80.

  (* [comment removed for export] *)
  Notation INR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s7 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 STRM) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (SHS + 7)) s3 cSB (Z_to_bv 64 (SHS + 9)) (Z_to_bv 64 (STRM + 72)) s7 (Z_to_bv 64 (STRM + 56)) (Z_to_bv 64 (SHE + 3)) (Z_to_bv 64 (SHE + 4)) (Z_to_bv 64 (E + 24)) t3 t4 t5 t6).

  Definition init2_W : list (Z * Z) := [(E, E + 8); (E + 24, E + 48); (P + 8, P + 72)]%Z.
  Lemma B0_init_I2 : forall (m : amem) (c0 c24 c32 c40 v0 v8 v16 v24 v32 v40 v48 v56 v64 : word) (w0 w8 w12 w16 w20 w24 w32 w36 w40 w44 w48 : word)
      (ra t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word),
    rw_cells b0segs m E (EJ1wA J c0 c24 c32 c40) -> rw_cells b0segs m P (ISLOTS v0 v8 v16 v24 v32 v40 v48 v56 v64) ->
    rw_cells b0segs m STRM (STRMC w0 w8 w12 w16 w20 w24 w32 w36 w40 w44 w48 (Z_to_bv 64 DBZA) (Z_to_bv 64 DBZF) (Z_to_bv 64 0)) -> mem_inv b0segs m ->
    shzW b0segs init2_W m E (E + 55768) -> shzW b0segs init2_W m STRM (STRM + 80) ->
    (forall m' (a4' : word),
        rw_cells b0segs m' E (EJ1wA J (Z_to_bv 64 STRM) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
        rw_cells b0segs m' P (ISLOTS v0 (Z_to_bv 64 0) (Z_to_bv 64 WORKFACTOR) (Z_to_bv 64 (SHE + 5)) (Z_to_bv 64 (STRM + 64)) (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 (E + 40)) v56 (Z_to_bv 64 (E + 32))) ->
        rw_cells b0segs m' STRM (STRMC w0 w8 w12 w16 w20 w24 w32 w36 w40 w44 w48 (Z_to_bv 64 DBZA) (Z_to_bv 64 DBZF) (Z_to_bv 64 0)) -> mem_inv b0segs m' ->
        munch init2_W m m' -> wmono b0segs m m' ->
        evt b0segs Q (MS (INR (Z_to_bv 64 0x818d8) t0 t1 t2 (Z_to_bv 64 ARR1_SIZE) (Z_to_bv 64 ARR1_SIZE) (Z_to_bv 64 1) (Z_to_bv 64 DBZA) a4' a5 a6 a7 (Z_to_bv 64 ARR1_SIZE) (Z_to_bv 64 (-3)) t3 t4 t5 t6)
                         F (Z_to_bv 64 B0_MALLOC) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 (Z_to_bv 64 STRM) (Z_to_bv 64 E) a1 a2 a3 a4 a5 a6 a7
                          (Z_to_bv 64 (SHS + 7)) (Z_to_bv 64 WORKFACTOR) cSB (Z_to_bv 64 (SHS + 9)) (Z_to_bv 64 (STRM + 72)) s7 (Z_to_bv 64 (STRM + 56)) (Z_to_bv 64 0)
                          (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 (STRM + 64)) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x81818) fc None m (seg_rom b0segs)).
  Proof.
    intros m c0 c24 c32 c40 v0 v8 v16 v24 v32 v40 v48 v56 v64 w0 w8 w12 w16 w20 w24 w32 w36 w40 w44 w48 ra t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 EH SL SM MI SHe SHs K.
    unfold CEILv, apartv in *. bz_ceil. bz_params. box_ors.
    pose proof (munch_refl init2_W m) as MU. pose proof (wmono_refl b0segs m) as WM. unfold init2_W in MU, SHe, SHs.
    pose proof (proj1 AE) as EM8.   (* [comment removed for export] *)
    unfold EJ1wA in EH. unfold ISLOTS in SL. unfold STRMC, DBZA, DBZF in SM.
    (* [comment removed for export] *)
    brun. dead.
    (* [comment removed for export] *)
    brun_to 0x81844%Z. wstep. lit_store.   (* [comment removed for export] *)
    brun_to 0x8185c%Z. sh_norm.
    (* [comment removed for export] *)
    brun_to 0x81864%Z. wstep. lit_store.
    (* [comment removed for export] *)
    brun_to 0x81878%Z. sh_norm.
    (* [comment removed for export] *)
    brun_to 0x81880%Z. wstep. lit_store.
    (* [comment removed for export] *)
    brun_to 0x81890%Z. sh_norm.
    (* [comment removed for export] *)
    brun_to 0x8189c%Z. wstep. lit_store.
    (* [comment removed for export] *)
    brun_to 0x537a4%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _) end;
      [ unfold B0_MALLOC, DBZA; st_eq | unfold EJ1wA; exact EH | unfold ISLOTS; exact SL | unfold STRMC, DBZA, DBZF; exact SM | assumption | unfold init2_W; exact MU | exact WM ].
  Qed.

  Definition init4_W : list (Z * Z) := [(E + 24, E + 32)]%Z.
  Lemma B0_init_I4 : forall (m : amem) (r1 : Z) (w0 w8 w12 w16 w20 w24 w32 w36 w40 w44 w48 c24 c32 c40 : word)
      (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word),
    (0 <= r1 < 18446744073709551616)%Z ->
    rw_cells b0segs m E (EJ1wA J (Z_to_bv 64 STRM) c24 c32 c40) ->
    rw_cells b0segs m STRM (STRMC w0 w8 w12 w16 w20 w24 w32 w36 w40 w44 w48 (Z_to_bv 64 DBZA) (Z_to_bv 64 DBZF) (Z_to_bv 64 0)) -> mem_inv b0segs m ->
    shzW b0segs init4_W m E (E + 55768) -> shzW b0segs init4_W m STRM (STRM + 80) ->
    (forall m',
        rw_cells b0segs m' E (EJ1wA J (Z_to_bv 64 STRM) (Z_to_bv 64 r1) c32 c40) ->
        rw_cells b0segs m' STRM (STRMC w0 w8 w12 w16 w20 w24 w32 w36 w40 w44 w48 (Z_to_bv 64 DBZA) (Z_to_bv 64 DBZF) (Z_to_bv 64 0)) -> mem_inv b0segs m' ->
        munch init4_W m m' -> wmono b0segs m m' ->
        evt b0segs Q (MS (INR (Z_to_bv 64 0x81908) t0 t1 t2 (Z_to_bv 64 ARR2_SIZE) (Z_to_bv 64 ARR2_SIZE) (Z_to_bv 64 1) (Z_to_bv 64 DBZA) a4 a5 a6 a7 (Z_to_bv 64 ARR1_SIZE) s7 t3 t4 t5 t6)
                         F (Z_to_bv 64 B0_MALLOC) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (INR ra t0 t1 t2 (Z_to_bv 64 r1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ARR1_SIZE) s7 t3 t4 t5 t6) F (Z_to_bv 64 0x818d8) fc None m (seg_rom b0segs)).
  Proof.
    intros m r1 w0 w8 w12 w16 w20 w24 w32 w36 w40 w44 w48 c24 c32 c40 ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 R1 EH SM MI SHe SHs K.
    unfold CEILv, apartv in *. bz_ceil. bz_params. box_ors.
    pose proof (munch_refl init4_W m) as MU. pose proof (wmono_refl b0segs m) as WM. unfold init4_W in MU, SHe, SHs.
    unfold EJ1wA in EH. unfold STRMC, DBZA, DBZF in SM.
    (* [comment removed for export] *)
    brun_to 0x537a4%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm) end;
      [ unfold B0_MALLOC, DBZA; st_eq | unfold EJ1wA; exact EH | unfold STRMC, DBZA, DBZF; exact SM | assumption | unfold init4_W; exact MU | exact WM ].
  Qed.

  Definition init5_W : list (Z * Z) := [(E + 32, E + 40)]%Z.
  Lemma B0_init_I5 : forall (m : amem) (r1 r2 : Z) (w0 w8 w12 w16 w20 w24 w32 w36 w40 w44 w48 c32 c40 v0 v8 v16 v24 v32 v40 v48 v56 : word)
      (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word),
    (0 <= r2 < 18446744073709551616)%Z ->
    rw_cells b0segs m E (EJ1wA J (Z_to_bv 64 STRM) (Z_to_bv 64 r1) c32 c40) ->
    rw_cells b0segs m STRM (STRMC w0 w8 w12 w16 w20 w24 w32 w36 w40 w44 w48 (Z_to_bv 64 DBZA) (Z_to_bv 64 DBZF) (Z_to_bv 64 0)) ->
    rw_cells b0segs m P (ISLOTS v0 v8 v16 v24 v32 v40 v48 v56 (Z_to_bv 64 (E + 32))) -> mem_inv b0segs m ->
    shzW b0segs init5_W m E (E + 55768) -> shzW b0segs init5_W m STRM (STRM + 80) ->
    (forall m',
        rw_cells b0segs m' E (EJ1wA J (Z_to_bv 64 STRM) (Z_to_bv 64 r1) (Z_to_bv 64 r2) c40) ->
        rw_cells b0segs m' STRM (STRMC w0 w8 w12 w16 w20 w24 w32 w36 w40 w44 w48 (Z_to_bv 64 DBZA) (Z_to_bv 64 DBZF) (Z_to_bv 64 0)) ->
        rw_cells b0segs m' P (ISLOTS v0 v8 v16 v24 v32 v40 v48 v56 (Z_to_bv 64 (E + 32))) -> mem_inv b0segs m' ->
        munch init5_W m m' -> wmono b0segs m m' ->
        evt b0segs Q (MS (INR (Z_to_bv 64 0x81940) t0 t1 t2 (Z_to_bv 64 262148) (Z_to_bv 64 262148) (Z_to_bv 64 1) (Z_to_bv 64 DBZA) a4 a5 a6 a7 (Z_to_bv 64 ARR1_SIZE) s7 t3 t4 t5 t6)
                         F (Z_to_bv 64 B0_MALLOC) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (INR ra t0 t1 t2 (Z_to_bv 64 r2) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ARR1_SIZE) s7 t3 t4 t5 t6) F (Z_to_bv 64 0x81908) fc None m (seg_rom b0segs)).
  Proof.
    intros m r1 r2 w0 w8 w12 w16 w20 w24 w32 w36 w40 w44 w48 c32 c40 v0 v8 v16 v24 v32 v40 v48 v56 ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 R2 EH SM SL MI SHe SHs K.
    unfold CEILv, apartv in *. bz_ceil. bz_params. box_ors.
    pose proof (munch_refl init5_W m) as MU. pose proof (wmono_refl b0segs m) as WM. unfold init5_W in MU, SHe, SHs.
    unfold EJ1wA in EH. unfold STRMC, DBZA, DBZF in SM. unfold ISLOTS in SL.
    (* [comment removed for export] *)
    brun_to 0x537a4%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm) end;
      [ unfold B0_MALLOC, DBZA; st_eq | unfold EJ1wA; exact EH | unfold STRMC, DBZA, DBZF; exact SM | unfold ISLOTS; exact SL | assumption | unfold init5_W; exact MU | exact WM ].
  Qed.

  Definition init6_W : list (Z * Z) := [(E, E + 128); (E + 128, E + 384); (E + 640, E + 672); (STRM + 12, STRM + 56); (P - 16, P + 176)]%Z.
  Lemma B0_init_I6 : forall (m : amem) (sp : word) (r1 r2 r3 : Z) (jin : list byte) (w0 w8 w12 w16 w20 w24 w32 w36 w40 w44 w48 c40 v0 : word)
      (c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word),
    P = (bv_unsigned sp - 176)%Z -> (lo + 16 <= P)%Z ->
    (0 < r1 < 18446744073709551616)%Z -> (0 < r2 < 18446744073709551616)%Z -> (0 < r3 < 18446744073709551616)%Z ->
    rw_cells b0segs m E (EJ1wA J (Z_to_bv 64 STRM) (Z_to_bv 64 r1) (Z_to_bv 64 r2) c40) -> rw_cells b0segs m (E + 128) [CB 256 jin] -> rw_cells b0segs m (E + 640) (EJ2A J) ->
    rw_cells b0segs m STRM (STRMC w0 w8 w12 w16 w20 w24 w32 w36 w40 w44 w48 (Z_to_bv 64 DBZA) (Z_to_bv 64 DBZF) (Z_to_bv 64 0)) ->
    rw_cells b0segs m P (ISLOTS v0 (Z_to_bv 64 0) (Z_to_bv 64 WORKFACTOR) (Z_to_bv 64 (SHE + 5)) (Z_to_bv 64 (STRM + 64)) (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 (E + 40)) (Z_to_bv 64 (SHS + 8)) (Z_to_bv 64 (E + 32))) ->
    rw_cells b0segs m (P + 72) (HSAVED c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) -> stk b0segs m lo P -> mem_inv b0segs m -> aconsts B0C m ->
    shzW b0segs init6_W m E (E + 55768) -> shzW b0segs init6_W m STRM (STRM + 80) ->
    (forall m' (t0' a1' a2' a3' a4' a5' a6' a7' : word),
        rw_cells b0segs m' E (EFINA J STRM r1 r2 r3) -> u8arr b0segs m' (E + 128) (repeat (Z_to_bv 8 0) 256) -> rw_cells b0segs m' (E + 640) (EFIN2A J (Z_to_bv 64 1)) ->
        rw_cells b0segs m' STRM (STRMC w0 w8 (Z_to_bv 64 0) (Z_to_bv 64 0) w20 w24 w32 (Z_to_bv 64 0) (Z_to_bv 64 0) w44 (Z_to_bv 64 E) (Z_to_bv 64 DBZA) (Z_to_bv 64 DBZF) (Z_to_bv 64 0)) ->
        stk b0segs m' lo (bv_unsigned sp) -> mem_inv b0segs m' -> munch init6_W m m' -> wmono b0segs m m' ->
        evt b0segs Q (MS (mkR cra sp gp tp t0' t1 t2 c0 c1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 t3 t4 t5 t6)
                         F (ret_pc cra) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (INR ra t0 t1 t2 (Z_to_bv 64 r3) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ARR1_SIZE) s7 t3 t4 t5 t6) F (Z_to_bv 64 0x81940) fc None m (seg_rom b0segs)).
  Proof.
    intros m sp r1 r2 r3 jin w0 w8 w12 w16 w20 w24 w32 w36 w40 w44 w48 c40 v0 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6
           EP LP16 R1 R2 R3 EH INJ EH2 SM SL SAV ST MI AC SHe SHs K.
    unfold CEILv, apartv in *. bz_ceil. bz_params. box_ors.
    pose proof (munch_refl init6_W m) as MU. pose proof (wmono_refl b0segs m) as WM. unfold init6_W in MU, SHe, SHs.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    destruct AC as [GOT SBV]. cbn [aci_segs aci_c aci_got_sh aci_shvar B0C ci_segs] in GOT, SBV.
    pose proof (proj1 AE) as EM8.
    unfold EJ1wA in EH. unfold EJ2A in EH2. unfold STRMC, DBZA, DBZF in SM. unfold ISLOTS in SL. unfold HSAVED in SAV.
    (* [comment removed for export] *)
    brun. dead.
    (* [comment removed for export] *)
    brun. dead. brun. dead.
    (* [comment removed for export] *)
    brun_to 0x81aa8%Z. wstep. lit_store.
    (* [comment removed for export] *)
    brun_to 0x81e74%Z.
    (* [comment removed for export] *)
    destruct (rw_cells_cutZ b0segs _ E _ 19%nat EH) as [EHa EHr]. cbn [firstn skipn cells_size csize Nat.add] in EHa, EHr. change (Z.of_nat 108) with 108%Z in EHr.
    destruct (rw_cells_cutZ b0segs _ (E + 108) _ 4%nat EHr) as [EHm EHb]. cbn [firstn skipn cells_size csize Nat.add] in EHm, EHb.
    replace (E + 108 + Z.of_nat 16)%Z with (E + 124)%Z in EHb by lia. clear EH EHr.
    destruct (rw_cells_cutZ b0segs _ (E + 640) _ 2%nat EH2) as [E2a E2r]. cbn [firstn skipn cells_size csize Nat.add] in E2a, E2r.
    replace (E + 640 + Z.of_nat 8)%Z with (E + 648)%Z in E2r by lia.
    destruct (rw_cells_cutZ b0segs _ (E + 648) _ 1%nat E2r) as [E2c E2s]. cbn [firstn skipn cells_size csize Nat.add] in E2c, E2s.
    replace (E + 648 + Z.of_nat 4)%Z with (E + 652)%Z in E2s by lia.
    destruct (rw_cells_cutZ b0segs _ (E + 652) _ 2%nat E2s) as [E2d E2t]. cbn [firstn skipn cells_size csize Nat.add] in E2d, E2t.
    replace (E + 652 + Z.of_nat 8)%Z with (E + 660)%Z in E2t by lia.
    destruct (rw_cells_cutZ b0segs _ (E + 660) _ 1%nat E2t) as [E2n E2u]. cbn [firstn skipn cells_size csize Nat.add] in E2n, E2u.
    replace (E + 660 + Z.of_nat 4)%Z with (E + 664)%Z in E2u by lia. clear EH2 E2r E2s E2t.
    pose proof (ovb_init b0segs _ (E + 128) 256 jin INJ ltac:(lia)) as INU. clear INJ.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (B0_prep_P Q E lo gp tp F fc EM8 ltac:(lia) ltac:(unfold CEILv; lia) ltac:(unfold CEILv; lia) P mm znew jin _ _ _ _ _ 0%Z);
        [ lia | exact EHm | exact INU | exact E2c | exact E2n | lia | assumption | exact ST | exact LP16 | split; [exact GOT| exact SBV]
        | eapply (shzW_sub b0segs _ _ m mm); [exact SHe| exact MU| unfold prep_W; a_sub_fp| lia| lia] |] end.
    clear EHm INU E2c E2n ST.
    intros m' a0' a1' a2' a3' a4' a5' a6' a7' EHm INU E2c E2n MI' ST MU' WM'. unfold prep_W in MU'.
    lazymatch type of MU' with munch _ ?ma ?mb => transport_after_call b0segs ma mb MU' WM' end. clear MU' WM'.
    rewrite (ret_pc_even 0x81b78 ltac:(lia) eq_refl).
    (* [comment removed for export] *)
    pose proof (rw_cells_glue b0segs m' (E + 108) _ _ (E + 124) EHm EHb ltac:(cbn [cells_size csize Nat.add]; lia)) as EHr.
    pose proof (rw_cells_glue b0segs m' E _ _ (E + 108) EHa EHr ltac:(cbn [cells_size csize Nat.add]; lia)) as EH. cbn [app] in EH. clear EHa EHm EHb EHr.
    pose proof (rw_cells_glue b0segs m' (E + 660) _ _ (E + 664) E2n E2u ltac:(cbn [cells_size csize Nat.add]; lia)) as E2t.
    pose proof (rw_cells_glue b0segs m' (E + 652) _ _ (E + 660) E2d E2t ltac:(cbn [cells_size csize Nat.add]; lia)) as E2s.
    pose proof (rw_cells_glue b0segs m' (E + 648) _ _ (E + 652) E2c E2s ltac:(cbn [cells_size csize Nat.add]; lia)) as E2r.
    pose proof (rw_cells_glue b0segs m' (E + 640) _ _ (E + 648) E2a E2r ltac:(cbn [cells_size csize Nat.add]; lia)) as EH2. cbn [app] in EH2. clear E2a E2c E2d E2n E2u E2t E2s E2r.
    rewrite CmpSess.ovb_inUse_clear in INU.
    (* [comment removed for export] *)
    brun_to 0x81c24%Z. do 13 wstep. wstep.
    pose proof (stk_of_rw_cells b0segs _ _ _ SL) as K0. cbn [cells_size csize Nat.add] in K0. change (Z.of_nat 72) with 72%Z in K0.
    pose proof (stk_of_rw_cells b0segs _ _ _ SAV) as K5. cbn [cells_size csize Nat.add] in K5. change (Z.of_nat 104) with 104%Z in K5.
    pose proof (stk_join b0segs m' lo P P (P + 72) ST K0 eq_refl ltac:(lia)) as ST1.
    pose proof (stk_join b0segs m' lo (P + 72) (P + 72) (P + 72 + 104) ST1 K5 eq_refl ltac:(lia)) as ST2.
    replace (P + 72 + 104)%Z with (bv_unsigned sp) in ST2 by lia.
    replace (Z_to_bv 64 (P + 176)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia).
    (* [comment removed for export] *)
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => eapply (K mm) end;
      [ unfold EFINA; first [exact EH | cells_eq_by EH] | exact INU | unfold EFIN2A; first [exact EH2 | cells_eq_by EH2] | unfold STRMC, DBZA, DBZF; exact SM | exact ST2 | assumption
      | unfold init6_W; exact MU | exact WM ].
  Qed.
  End WithE.
End B0WRI.

End ACeilS1.
