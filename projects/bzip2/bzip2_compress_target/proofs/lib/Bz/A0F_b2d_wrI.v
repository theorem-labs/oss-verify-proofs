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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCBlock BzCDriver BzArrD CmpMem CmpCut CmpArith CmpArith2 CmpSess CmpSessB CmpCarve CmpSdTac GlueTac BzInv BzCLemmas1 CmpFsKit0 AsanKit AsanCut.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_msV A0_cmp_cbV A0_cmp_smV A0_b2c_hcV A0_b2c_wrV AsanKit2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpHmKit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit.
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0F_b2d_wrV.
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Ltac dead := let KD := fresh "KD" in if_cases KD; zify_cond_z KD; [exfalso; lia|]; clear KD.
(* [comment removed for export] *)
Ltac lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
  | _ => idtac
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
(* [comment removed for export] *)

Section A0FWRI.
  Variable Q : machine_state -> Prop.
  Variables (P STRM lo verb small : Z).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Notation cSB := (Z_to_bv 64 2147450880).
  Hypothesis SLO : (0x61e000 <= STRM)%Z. Hypothesis SHI : (STRM + 80 <= CEILv)%Z.
  Hypothesis LLO : (CEILv <= lo)%Z. Hypothesis PLO : (lo <= P)%Z. Hypothesis PHI : (P + 48 <= 18446744073709551616)%Z.
  Hypothesis VERB : (0 <= verb <= 4)%Z. Hypothesis SMALL : (0 <= small <= 1)%Z.

  Definition dinit1_W : list (Z * Z) := [(P, P + 48); (STRM + 56, STRM + 72)]%Z.

  (* [comment removed for export] *)
  Lemma A0_dinit_I1 : forall (m : amem) (w0 w8 w12 w16 : word) (q1 : list byte) (w24 w32 w36 w40 : word) (q2 : list byte) (w48 : word)
      (ra sp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    P = (bv_unsigned sp - 48)%Z ->
    stk a0segs m lo (bv_unsigned sp) ->
    rw_cells a0segs m STRM (STRMD w0 w8 w12 w16 q1 w24 w32 w36 w40 q2 w48 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
    mem_inv a0segs m -> aconsts A0C m -> shzW a0segs dinit1_W m STRM (STRM + 80) ->
    (forall m' (v0 : word),
        rw_cells a0segs m' P (DISAVED v0 s3 s2 s1 s0 ra) -> stk a0segs m' lo P ->
        rw_cells a0segs m' STRM (STRMD w0 w8 w12 w16 q1 w24 w32 w36 w40 q2 w48 (Z_to_bv 64 DBZA) (Z_to_bv 64 DBZF) (Z_to_bv 64 0)) ->
        mem_inv a0segs m' -> munch dinit1_W m m' -> wmono a0segs m m' ->
        evt a0segs Q (MS (mkR (Z_to_bv 64 0x83f90) (Z_to_bv 64 P) gp tp t0 t1 t2 (Z_to_bv 64 verb) (Z_to_bv 64 small) (Z_to_bv 64 64144) (Z_to_bv 64 64144) (Z_to_bv 64 1) (Z_to_bv 64 DBZA)
                              (Z_to_bv 64 0) a5 a6 a7 (Z_to_bv 64 STRM) cSB s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 A0_MALLOC) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 STRM) (Z_to_bv 64 verb) (Z_to_bv 64 small) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x83eb4) fc None m (seg_rom a0segs)).
  Proof.
    intros m w0 w8 w12 w16 q1 w24 w32 w36 w40 q2 w48 ra sp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 EP ST SM MI AC SHs K.
    unfold CEILv in *. bz_ceil.
    destruct AC as [GOT SBV]. cbn [aci_segs aci_c aci_got_sh aci_shvar A0C ci_segs] in GOT, SBV.
    pose proof (munch_refl dinit1_W m) as MU. pose proof (wmono_refl a0segs m) as WM. unfold dinit1_W in MU, SHs.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    unfold STRMD in SM.
    carve_frame 48%nat ST.
    apply (rw_cells_split_CB a0segs _ _ [] 48 _ [] [8;8;8;8;8;8]%nat) in FR; [| reflexivity].
    cbn [mk_CB_cells app] in FR.
    (* [comment removed for export] *)
    wstep. do 5 wstep.
    replace (bv_unsigned sp + -48)%Z with P in * by lia.
    (* [comment removed for export] *)
    arun. dead.
    (* [comment removed for export] *)
    arun. dead.
    (* [comment removed for export] *)
    arun. dead.
    (* [comment removed for export] *)
    arun_to 0x83f28%Z. wstep. lit_store.
    (* [comment removed for export] *)
    arun_to 0x83f58%Z. wstep. lit_store.
    (* [comment removed for export] *)
    arun_to 0x53d58%Z.
    cb8_all FR.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _) end;
      [ unfold A0_MALLOC, DBZA; st_eq | unfold DISAVED; exact FR | exact ST | unfold STRMD, DBZA, DBZF; exact SM | assumption | unfold dinit1_W; exact MU | exact WM ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section WithS.
  Variable S : Z.
  Hypothesis SSLO : (0x61e000 <= S)%Z. Hypothesis SSHI : (S + 64144 <= CEILv)%Z.
  Hypothesis SES : apartv S 64144 STRM 80.

  Definition dinit2_W : list (Z * Z) := [(S, S + 68); (S + 3188, S + 3192); (STRM + 12, STRM + 20); (STRM + 36, STRM + 44); (STRM + 48, STRM + 56)]%Z.

  Lemma A0_dinit_I2 : forall (m : amem) (jh jm : list byte) (w0 w8 w12 w16 : word) (q1 : list byte) (w24 w32 w36 w40 : word) (q2 : list byte) (w48 : word)
      (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells a0segs m S [CB 68 jh] -> rw_cells a0segs m (S + 3152) [CB 44 jm] ->
    rw_cells a0segs m STRM (STRMD w0 w8 w12 w16 q1 w24 w32 w36 w40 q2 w48 (Z_to_bv 64 DBZA) (Z_to_bv 64 DBZF) (Z_to_bv 64 0)) ->
    mem_inv a0segs m -> shzW a0segs dinit2_W m S (S + 64144) -> shzW a0segs dinit2_W m STRM (STRM + 80) ->
    (forall m' (p20 p4 p3 pv p12 q24 q12 q4 : list byte) (a3' : word),
        rw_cells a0segs m' S (DHEAD2 STRM small p20 p4 p3 pv p12) -> rw_cells a0segs m' (S + 3152) (DMID2 q24 q12 q4) ->
        rw_cells a0segs m' STRM (STRMD w0 w8 (Z_to_bv 64 0) (Z_to_bv 64 0) q1 w24 w32 (Z_to_bv 64 0) (Z_to_bv 64 0) q2 (Z_to_bv 64 S) (Z_to_bv 64 DBZA) (Z_to_bv 64 DBZF) (Z_to_bv 64 0)) ->
        mem_inv a0segs m' -> munch dinit2_W m m' -> wmono a0segs m m' ->
        evt a0segs Q (MS (mkR (Z_to_bv 64 0x840d0) (Z_to_bv 64 P) gp tp t0 t1 t2 (Z_to_bv 64 verb) (Z_to_bv 64 (S + 52)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 0) (Z_to_bv 64 24) a3' a4 a5 a6 a7
                              (Z_to_bv 64 STRM) cSB s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x52ea0) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (Z_to_bv 64 verb) (Z_to_bv 64 small) (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7
                          (Z_to_bv 64 STRM) cSB s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x83f90) fc None m (seg_rom a0segs)).
  Proof.
    intros m jh jm w0 w8 w12 w16 q1 w24 w32 w36 w40 q2 w48 ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 HDJ MDJ SM MI SHd SHs K.
    unfold CEILv, apartv in *. bz_ceil. box_ors.
    pose proof (munch_refl dinit2_W m) as MU. pose proof (wmono_refl a0segs m) as WM. unfold dinit2_W in MU, SHd, SHs.
    unfold STRMD, DBZA, DBZF in SM.
    apply (rw_cells_split_CB a0segs _ _ [] 68 _ [] [8;4;20;4;4;4;1;3;4;4;12]%nat) in HDJ; [| reflexivity]. cbn [mk_CB_cells app] in HDJ.
    apply (rw_cells_split_CB a0segs _ _ [] 44 _ [] [24;12;4;4]%nat) in MDJ; [| reflexivity]. cbn [mk_CB_cells app] in MDJ.
    repeat (match type of HDJ with context [CB ?k (firstn ?a ?b)] => let v := fresh "hb" in set (v := firstn a b) in HDJ; clearbody v end).
    repeat (match type of MDJ with context [CB ?k (firstn ?a ?b)] => let v := fresh "mb" in set (v := firstn a b) in MDJ; clearbody v end).
    (* [comment removed for export] *)
    arun. dead.
    (* [comment removed for export] *)
    arun_to 0x8409c%Z. wstep. rewrite BzInv.le1_lit. mem_after_store.
    (* [comment removed for export] *)
    arun_to 0x52ea0%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _) end;
      [ st_eq | unfold DHEAD2; first [exact HDJ | cells_eq_by HDJ] | unfold DMID2; first [exact MDJ | cells_eq_by MDJ]
      | unfold STRMD, DBZA, DBZF; first [exact SM | cells_eq_by SM] | assumption | unfold dinit2_W; exact MU | exact WM ].
  Qed.

  Definition dinit3_W : list (Z * Z) := [(S + 52, S + 56)]%Z.
  Lemma A0_dinit_I3 : forall (m : amem) (sp : word) (p20 p4 p3 pv p12 : list byte) (v0 c3 c2 c1 c0 cra : word)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    P = (bv_unsigned sp - 48)%Z ->
    rw_cells a0segs m S (DHEAD2 STRM small p20 p4 p3 pv p12) ->
    rw_cells a0segs m P (DISAVED v0 c3 c2 c1 c0 cra) -> stk a0segs m lo P -> mem_inv a0segs m ->
    shzW a0segs dinit3_W m S (S + 64144) ->
    (forall m',
        rw_cells a0segs m' S (DHEAD3 STRM small verb p20 p4 p3 p12) -> stk a0segs m' lo (bv_unsigned sp) -> mem_inv a0segs m' ->
        munch dinit3_W m m' -> wmono a0segs m m' ->
        evt a0segs Q (MS (mkR cra sp gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 c2 c3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (ret_pc cra) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (Z_to_bv 64 verb) (Z_to_bv 64 (S + 52)) a0 a1 a2 a3 a4 a5 a6 a7
                          s2 cSB s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x840d0) fc None m (seg_rom a0segs)).
  Proof.
    intros m sp p20 p4 p3 pv p12 v0 c3 c2 c1 c0 cra ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 EP HD SAV ST MI SHd K.
    unfold CEILv, apartv in *. bz_ceil. box_ors.
    pose proof (munch_refl dinit3_W m) as MU. pose proof (wmono_refl a0segs m) as WM. unfold dinit3_W in MU, SHd.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    unfold DHEAD2 in HD. unfold DISAVED in SAV.
    (* [comment removed for export] *)
    arun_to 0x840f4%Z. do 4 wstep. wstep.
    lazymatch goal with SAV' : rw_cells a0segs ?mm P _, ST' : stk a0segs ?mm lo P |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (stk_of_rw_cells a0segs _ _ _ SAV') as K0; cbn [cells_size csize Nat.add] in K0; change (Z.of_nat 48) with 48%Z in K0;
      pose proof (stk_join a0segs mm lo P P (P + 48) ST' K0 eq_refl ltac:(lia)) as ST1 end.
    replace (P + 48)%Z with (bv_unsigned sp) in ST1 by lia.
    replace (Z_to_bv 64 (P + 48)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia).
    (* [comment removed for export] *)
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => eapply (K mm) end;
      [ unfold DHEAD3; first [exact HD | cells_eq_by HD] | exact ST1 | assumption | unfold dinit3_W; exact MU | exact WM ].
  Qed.
  End WithS.

End A0FWRI.
End ACeilS1.
