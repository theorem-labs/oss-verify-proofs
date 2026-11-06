(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCBlock BzCDriver BzArrD CmpMem CmpCut CmpArith CmpArith2 CmpSess CmpSessB CmpSdTac GlueTac BzInv BzCLemmas1 CmpFsKit0 AsanKit AsanCut AsanCutB0 AsanKitB0.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV B0_cmp_msV B0_b2c_cbV B0_b2c_hcV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpHmKit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit.
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

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
Ltac lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?v)) _) => change (Z_to_le_bytes 4 v) with (le4 (Z_to_bv 64 v)); mem_after_store
  | _ => idtac
  end.
(* [comment removed for export] *)
Lemma land7_off : forall E o r, (E mod 8 = 0)%Z -> (r = o mod 8)%Z -> Z.land (E + o) 7 = r.
Proof.
  intros E o r HE ->. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3)%Z with 8%Z.
  rewrite Z.add_mod, HE, Z.add_0_l, Z.mod_mod by lia. reflexivity.
Qed.

Section B0HCG.
  Variables (cx : cctx) (Q : machine_state -> Prop).
  Variables (SHE SHS : Z) (ob on dbza dbzfr : Z) (p1 p2 : word) (P STRM lo : Z).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Notation E := (c_E cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation cSB := (Z_to_bv 64 2147450880).
  Hypothesis ESTRM : STRM = (c_bz cx + BZF_STRM)%Z.
  Hypothesis CX : cctx_ok cx.
  Hypothesis AE : sanchor E SHE. Hypothesis AS : sanchor STRM SHS.
  Hypothesis SLO : (0x62b000 <= STRM)%Z. Hypothesis SHI : (STRM + 80 <= CEILv)%Z.
  Hypothesis LLO : (CEILv <= lo)%Z. Hypothesis PLO : (lo + 16 <= P)%Z. Hypothesis PHI : (P + 288 <= 18446744073709551616)%Z.
  Hypothesis SES : apartv E ESTATE_SIZE STRM 80.

  (* [comment removed for export] *)
  Notation TOPR s1 a0 a1 a4 a5 a6 a7 s2 s3 s7 t6 :=
    (mkR (Z_to_bv 64 (SHE + 14)) (Z_to_bv 64 P) gp tp (Z_to_bv 64 (E + 92)) (Z_to_bv 64 (E + 96)) (Z_to_bv 64 (E + 108)) (Z_to_bv 64 E) s1
         a0 a1 (Z_to_bv 64 (E + 12)) (Z_to_bv 64 (SHE + 1)) a4 a5 a6 a7
         s2 s3 (Z_to_bv 64 2) (Z_to_bv 64 (E + 120)) (Z_to_bv 64 1) s7 (Z_to_bv 64 (E + 116)) (Z_to_bv 64 SHE) (Z_to_bv 64 (E + 80)) cSB
         (Z_to_bv 64 (SHE + 13)) (Z_to_bv 64 (E + 16)) (Z_to_bv 64 (E + 112)) t6).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_hc_P : forall z (ni : Z) (m : amem) (ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    P = (bv_unsigned sp - 288)%Z ->
    stk b0segs m lo (bv_unsigned sp) -> rw_cells b0segs m STRM (STRMB cx ob on dbza dbzfr z ni p1 p2) -> mem_inv b0segs m -> aconsts B0C m ->
    shzW b0segs [(P, P + 288)]%Z m STRM (STRM + 80) ->
    (forall m' (v64 v80 v88 a0' a1' a4' a5' a6' a7' t6' : word),
        rw_cells b0segs m' P (hc_slots E SHE v64 (Z_to_bv 64 0) v80 v88) ->
        rw_cells b0segs m' (P + 184) (HSAVED s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) -> stk b0segs m' lo P ->
        rw_cells b0segs m' STRM (STRMB cx ob on dbza dbzfr z ni p1 p2) -> mem_inv b0segs m' -> munch [(P, P + 288)]%Z m m' -> wmono b0segs m m' ->
        evt b0segs Q (MS (TOPR s1 a0' a1' a4' a5' a6' a7' s2 (Z_to_bv 64 0) s7 t6') F (Z_to_bv 64 0x825d4) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 STRM) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x82470) fc None m (seg_rom b0segs)).
  Proof.
    intros z ni m ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 EP ST SM MI AC SHs K.
    cb_ranges CX. unfold CEILv, apartv, ESTATE_SIZE in *. box_ors.
    destruct AC as [GOT SBV]. cbn [aci_segs aci_c aci_got_sh aci_shvar B0C ci_segs] in GOT, SBV.
    pose proof (proj1 AS) as SM8. pose proof (proj1 AE) as EM8.   (* [comment removed for export] *)
    pose proof (munch_refl [(P, P + 288)]%Z m) as MU. pose proof (wmono_refl b0segs m) as WM.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    unfold STRMB in SM.
    carve_frame 288%nat ST.
    apply (rw_cells_split_CB b0segs _ _ [] 288 _ [] [8;8;8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8;8;8; 8;8;8;8;8;8]%nat) in FR; [| reflexivity].
    cbn [mk_CB_cells app] in FR.
    (* [comment removed for export] *)
    wstep. do 13 wstep.
    replace (bv_unsigned sp + -288)%Z with P in * by lia.
    (* [comment removed for export] *)
    brun_to 0x824f4%Z. wstep. lit_store.
    (* [comment removed for export] *)
    brun_to 0x82570%Z.
    rewrite (land7_off E 12 4 EM8 eq_refl), (land7_off E 8 0 EM8 eq_refl), (land7_off E 108 4 EM8 eq_refl), (land7_off E 112 0 EM8 eq_refl).
    change (4 + 3)%Z with 7%Z. sh_norm.
    (* [comment removed for export] *)
    brun. lit_store. brun. lit_store. brun. lit_store. brun. lit_store.
    (* [comment removed for export] *)
    brun.
    cb8_all FR.
    destruct (rw_cells_cutZ b0segs _ P _ 23%nat FR) as [SLa SVc]. cbn [firstn skipn cells_size csize Nat.add] in SLa, SVc. change (Z.of_nat 184) with 184%Z in SVc.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | unfold hc_slots; exact SLa | unfold HSAVED; exact SVc | exact ST | unfold STRMB; exact SM | assumption | exact MU | exact WM ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_hc_top_in : forall g e (m : amem) (v64 v72 v80 v88 : word) (s1 a0 a1 a4 a5 a6 a7 s2 s3 s7 t6 : word),
    e_state e = BZ_S_INPUT -> e_mode e = BZ_M_FINISHING ->
    rw_cells b0segs m E (EHEAD1 cx g e) -> rw_cells b0segs m P (hc_slots E SHE v64 v72 v80 v88) -> shzW b0segs [] m E (E + ESTATE_SIZE) ->
    evt b0segs Q (MS (TOPR s1 (Z_to_bv 64 4) a1 a4 a5 a6 a7 s2 s3 s7 t6) F (Z_to_bv 64 0x829a8) fc None m (seg_rom b0segs)) ->
    evt b0segs Q (MS (TOPR s1 a0 a1 a4 a5 a6 a7 s2 s3 s7 t6) F (Z_to_bv 64 0x825d4) fc None m (seg_rom b0segs)).
  Proof.
    intros g e m v64 v72 v80 v88 s1 a0 a1 a4 a5 a6 a7 s2 s3 s7 t6 STI MF EH1 SL SHe K.
    cb_ranges CX. unfold CEILv, apartv, ESTATE_SIZE in *. box_ors.
    pose proof (proj1 AE) as EM8. pose proof (proj2 AE : saddr E SHE) as AEs.
    pose proof (munch_refl [] m) as MU.
    unfold EHEAD1 in EH1. rewrite STI, MF in EH1. unfold BZ_S_INPUT, BZ_M_FINISHING in EH1. unfold hc_slots in SL.
    (* [comment removed for export] *)
    brun_to 0x829a8%Z.
    exact K.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition hcr_W : list (Z * Z) := [(E + 12, E + 16)]%Z.
  Lemma B0_hc_cbret : forall g e (m : amem) (v64 v72 v80 v88 : word)
      (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s7 t3 t4 t5 t6 : word),
    rw_cells b0segs m E (EHEAD1 cx g e) ->
    rw_cells b0segs m P (hc_slots E SHE v64 v72 v80 v88) -> mem_inv b0segs m ->
    shzW b0segs hcr_W m E (E + ESTATE_SIZE) ->
    (forall m' (a0' : word),
        rw_cells b0segs m' E (EHEAD1 cx g (est_set_modes e (e_mode e) BZ_S_OUTPUT (e_avail_in_expect e))) ->
        rw_cells b0segs m' P (hc_slots E SHE v64 v72 v80 v88) -> mem_inv b0segs m' ->
        munch hcr_W m m' -> wmono b0segs m m' ->
        evt b0segs Q (MS (TOPR s1 a0' a1 a4 a5 a6 a7 s2 s3 s7 t6) F (Z_to_bv 64 0x825d4) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7
                          s2 s3 (Z_to_bv 64 2) (Z_to_bv 64 (E + 120)) (Z_to_bv 64 1) s7 (Z_to_bv 64 (E + 116)) (Z_to_bv 64 SHE) (Z_to_bv 64 (E + 80)) cSB t3 t4 t5 t6)
                     F (Z_to_bv 64 0x83350) fc None m (seg_rom b0segs)).
  Proof.
    intros g e m v64 v72 v80 v88 ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s7 t3 t4 t5 t6 EH1 SL MI SHe K.
    cb_ranges CX. unfold CEILv, apartv, ESTATE_SIZE in *. box_ors.
    pose proof (proj1 AE) as EM8. pose proof (proj2 AE : saddr E SHE) as AEs.
    pose proof (munch_refl hcr_W m) as MU. pose proof (wmono_refl b0segs m) as WM. unfold hcr_W in MU, SHe.
    unfold EHEAD1 in EH1. unfold hc_slots in SL.
    (* [comment removed for export] *)
    brun_to 0x825d4%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _) end;
      [ st_eq
      | unfold EHEAD1; cbn [est_set_modes e_mode e_state e_avail_in_expect e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse e_bw];
        unfold BZ_S_OUTPUT; exact EH1
      | unfold hc_slots; exact SL | assumption | unfold hcr_W; exact MU | exact WM ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_hc_ret : forall (pin pout : bool) (m : amem) (sp : word) (v64 v80 v88 : word)
      (c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word)
      (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    P = (bv_unsigned sp - 288)%Z ->
    rw_cells b0segs m P (hc_slots E SHE v64 (Z_to_bv 64 (Z.b2z pout)) v80 v88) ->
    rw_cells b0segs m (P + 184) (HSAVED c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) -> stk b0segs m lo P ->
    (stk b0segs m lo (bv_unsigned sp) ->
       evt b0segs Q (MS (mkR cra sp gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 (Z.b2z (pin || pout))) a1 a2 a3 a4 a5 a6 a7 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 t3 t4 t5 t6)
                        F (ret_pc cra) fc None m (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (Z.b2z pin)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x834f4) fc None m (seg_rom b0segs)).
  Proof.
    intros pin pout m sp v64 v80 v88 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra
           ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 EP SL SAV ST K.
    unfold CEILv in *. pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    pose proof (b2z_range pout) as BP. pose proof (b2z_range pin) as BI.
    unfold hc_slots in SL. unfold HSAVED in SAV.
    (* [comment removed for export] *)
    wstep. wstep. rewrite (lor_b2z pin pout).
    destruct (pin || pout) eqn:PR; cbn [Z.b2z]; (wstep; flags);
      (* [comment removed for export] *)
      do 13 wstep; wstep;
      pose proof (stk_of_rw_cells b0segs _ _ _ SL) as K0; cbn [cells_size csize Nat.add] in K0; change (Z.of_nat 184) with 184%Z in K0;
      pose proof (stk_of_rw_cells b0segs _ _ _ SAV) as K5; cbn [cells_size csize Nat.add] in K5; change (Z.of_nat 104) with 104%Z in K5;
      pose proof (stk_join b0segs m lo P P (P + 184) ST K0 eq_refl ltac:(lia)) as ST1;
      pose proof (stk_join b0segs m lo (P + 184) (P + 184) (P + 184 + 104) ST1 K5 eq_refl ltac:(lia)) as ST2;
      replace (P + 184 + 104)%Z with (bv_unsigned sp) in ST2 by lia;
      replace (Z_to_bv 64 (P + 288)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia);
      (* [comment removed for export] *)
      wstep; exact (K ST2).
  Qed.

End B0HCG.

End ACeilS1.
