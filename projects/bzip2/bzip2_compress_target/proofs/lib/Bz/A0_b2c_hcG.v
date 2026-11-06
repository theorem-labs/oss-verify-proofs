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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_msV A0_cmp_cbV A0_b2c_hcV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpHmKit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit.
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold.
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
  | _ => idtac
  end.

Section A0HCG.
  Variables (cx : cctx) (Q : machine_state -> Prop).
  Variables (SHE SHS : Z) (ob on dbza dbzfr : Z) (p1 p2 : word) (P STRM lo : Z).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Notation E := (c_E cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation cSB := (Z_to_bv 64 2147450880).
  Hypothesis ESTRM : STRM = (c_bz cx + BZF_STRM)%Z.
  Hypothesis CX : cctx_ok cx.
  Hypothesis AE : sanchor E SHE. Hypothesis AS : sanchor STRM SHS.
  Hypothesis SLO : (0x61e000 <= STRM)%Z. Hypothesis SHI : (STRM + 80 <= CEILv)%Z.
  Hypothesis LLO : (CEILv <= lo)%Z. Hypothesis PLO : (lo + 16 <= P)%Z. Hypothesis PHI : (P + 304 <= 18446744073709551616)%Z.
  Hypothesis SES : apartv E ESTATE_SIZE STRM 80.

  (* [comment removed for export] *)
  Notation TOPR ra a0 a1 a4 a5 s2 s6 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp (Z_to_bv 64 (E + 16)) (Z_to_bv 64 (E + 8)) (Z_to_bv 64 2) (Z_to_bv 64 E) cSB
         a0 a1 (Z_to_bv 64 (E + 12)) (Z_to_bv 64 (SHE + 1)) a4 a5 (Z_to_bv 64 1) (Z_to_bv 64 (E + 108))
         s2 (Z_to_bv 64 (E + 120)) (Z_to_bv 64 (SHE + 15)) (Z_to_bv 64 (E + 92)) s6 (Z_to_bv 64 (E + 116)) (Z_to_bv 64 (E + 96)) (Z_to_bv 64 SHE) (Z_to_bv 64 (E + 80))
         (Z_to_bv 64 (SHE + 14)) (Z_to_bv 64 (E + 648)) t4 t5 t6).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_hc_P : forall z (ni : Z) (m : amem) (ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    P = (bv_unsigned sp - 304)%Z ->
    stk a0segs m lo (bv_unsigned sp) -> rw_cells a0segs m STRM (STRMB cx ob on dbza dbzfr z ni p1 p2) -> mem_inv a0segs m -> aconsts A0C m ->
    shzW a0segs [(P, P + 304)]%Z m STRM (STRM + 80) ->
    (forall m' (v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 v112 a0' a1' : word),
        rw_cells a0segs m' P (hc_slots E SHE v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 (Z_to_bv 64 0) v112) ->
        rw_cells a0segs m' (P + 200) (HSAVED s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) -> stk a0segs m' lo P ->
        rw_cells a0segs m' STRM (STRMB cx ob on dbza dbzfr z ni p1 p2) -> mem_inv a0segs m' -> munch [(P, P + 304)]%Z m m' -> wmono a0segs m m' ->
        evt a0segs Q (MS (TOPR ra a0' a1' (Z_to_bv 64 (E + 12)) a5 (Z_to_bv 64 0) s6 t4 t5 t6) F (Z_to_bv 64 0x829ec) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 STRM) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x828cc) fc None m (seg_rom a0segs)).
  Proof.
    intros z ni m ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 EP ST SM MI AC SHs K.
    cb_ranges CX. unfold CEILv, apartv, ESTATE_SIZE in *. box_ors.
    destruct AC as [GOT SBV]. cbn [aci_segs aci_c aci_got_sh aci_shvar A0C ci_segs] in GOT, SBV.
    pose proof (munch_refl [(P, P + 304)]%Z m) as MU. pose proof (wmono_refl a0segs m) as WM.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    unfold STRMB in SM.
    carve_frame 304%nat ST.
    apply (rw_cells_split_CB a0segs _ _ [] 304 _ [] [8;8;8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity].
    cbn [mk_CB_cells app] in FR.
    (* [comment removed for export] *)
    wstep. do 13 wstep.
    replace (bv_unsigned sp + -304)%Z with P in * by lia.
    (* [comment removed for export] *)
    arun_to 0x8292c%Z. wstep. lit_store.
    arun_to 0x829bc%Z. sh_norm.
    arun_to 0x829ec%Z.
    cb8_all FR.
    destruct (rw_cells_cutZ a0segs _ P _ 25%nat FR) as [SLa SVc]. cbn [firstn skipn cells_size csize Nat.add] in SLa, SVc. change (Z.of_nat 200) with 200%Z in SVc.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [ st_eq | unfold hc_slots; exact SLa | unfold HSAVED; exact SVc | exact ST | unfold STRMB; exact SM | assumption | exact MU | exact WM ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_hc_top_in : forall g e (m : amem) (ra a0 a1 a4 a5 s2 s6 t4 t5 t6 : word),
    e_state e = BZ_S_INPUT ->
    rw_cells a0segs m E (EHEAD1 cx g e) -> shzW a0segs [] m E (E + ESTATE_SIZE) ->
    evt a0segs Q (MS (TOPR ra (Z_to_bv 64 2) a1 a4 a5 s2 s6 t4 t5 t6) F (Z_to_bv 64 0x82d64) fc None m (seg_rom a0segs)) ->
    evt a0segs Q (MS (TOPR ra a0 a1 a4 a5 s2 s6 t4 t5 t6) F (Z_to_bv 64 0x829ec) fc None m (seg_rom a0segs)).
  Proof.
    intros g e m ra a0 a1 a4 a5 s2 s6 t4 t5 t6 STI EH1 SHe K.
    cb_ranges CX. unfold CEILv, apartv, ESTATE_SIZE in *. box_ors.
    pose proof (munch_refl [] m) as MU.
    unfold EHEAD1 in EH1. rewrite STI in EH1. unfold BZ_S_INPUT in EH1.
    (* [comment removed for export] *)
    arun_to 0x82d64%Z.
    exact K.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition hms_W : list (Z * Z) := [(E + 12, E + 16); (E + 660, E + 664)]%Z.
  Lemma A0_hc_msret : forall g e (m : amem) (v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 v104 v112 : word)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word),
    e_mode e = BZ_M_FINISHING -> (1 <= e_blockNo e < 2147483647)%Z ->
    rw_cells a0segs m E (EHEAD1 cx g (hc_prep_a e)) -> rw_cells a0segs m (E + 640) (EHEAD2 cx g (hc_prep_a e)) ->
    rw_cells a0segs m P (hc_slots E SHE v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 v104 v112) -> mem_inv a0segs m ->
    shzW a0segs hms_W m E (E + ESTATE_SIZE) ->
    (forall m' (a1' : word),
        rw_cells a0segs m' E (EHEAD1 cx g (hc_prep e)) -> rw_cells a0segs m' (E + 640) (EHEAD2 cx g (hc_prep e)) ->
        rw_cells a0segs m' P (hc_slots E SHE v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 v104 v112) -> mem_inv a0segs m' ->
        munch hms_W m m' -> wmono a0segs m m' ->
        evt a0segs Q (MS (TOPR ra (Z_to_bv 64 3) a1' a4 a5 s2 (Z_to_bv 64 (e_mode e)) t4 t5 t6) F (Z_to_bv 64 0x82d64) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (Z_to_bv 64 E) cSB a0 a1 a2 a3 a4 a5 a6 a7
                          s2 (Z_to_bv 64 (E + 120)) (Z_to_bv 64 (SHE + 15)) (Z_to_bv 64 (E + 92)) (Z_to_bv 64 (e_mode e)) (Z_to_bv 64 (E + 116)) (Z_to_bv 64 (E + 96))
                          (Z_to_bv 64 SHE) (Z_to_bv 64 (E + 80)) (Z_to_bv 64 (SHE + 14)) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x82cb4) fc None m (seg_rom a0segs)).
  Proof.
    intros g e m v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 v104 v112 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 MF BNO EH1 EH2 SL MI SHe K.
    cb_ranges CX. unfold CEILv, apartv, ESTATE_SIZE in *. box_ors.
    pose proof (munch_refl hms_W m) as MU. pose proof (wmono_refl a0segs m) as WM. unfold hms_W in MU, SHe.
    unfold EHEAD1 in EH1. unfold EHEAD2 in EH2. unfold hc_slots in SL.
    cbn [hc_prep_a e_mode e_state e_avail_in_expect e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF
         bw_buff bw_live bw_numZ] in EH1, EH2.
    (* [comment removed for export] *)
    arun_to 0x82cd4%Z.
    reword_C4 EH2 5%nat (e_blockNo e + 1)%Z. { now low32. }
    (* [comment removed for export] *)
    arun. rewrite MF. unfold BZ_M_FINISHING. if_cases K3; zify_cond_z K3; [| exfalso; clear - K3; lia].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _) end;
      [ rewrite MF; unfold BZ_M_FINISHING; st_eq
      | rewrite hc_prep_of_a; unfold EHEAD1;
        cbn [e_mode e_state e_avail_in_expect e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF bw_buff bw_live bw_numZ];
        unfold BZ_S_INPUT; exact EH1
      | rewrite hc_prep_of_a; unfold EHEAD2;
        cbn [e_mode e_state e_avail_in_expect e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF bw_buff bw_live bw_numZ];
        exact EH2
      | unfold hc_slots; exact SL | assumption | unfold hms_W; exact MU | exact WM ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition hcr_W : list (Z * Z) := [(E + 12, E + 16)]%Z.
  Lemma A0_hc_cbret : forall g e (m : amem) (v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 v104 v112 : word)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 t3 t4 t5 t6 : word),
    rw_cells a0segs m E (EHEAD1 cx g e) ->
    rw_cells a0segs m P (hc_slots E SHE v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 v104 v112) -> mem_inv a0segs m ->
    shzW a0segs hcr_W m E (E + ESTATE_SIZE) ->
    (forall m',
        rw_cells a0segs m' E (EHEAD1 cx g (est_set_modes e (e_mode e) BZ_S_OUTPUT (e_avail_in_expect e))) ->
        rw_cells a0segs m' P (hc_slots E SHE v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 v104 v112) -> mem_inv a0segs m' ->
        munch hcr_W m m' -> wmono a0segs m m' ->
        evt a0segs Q (MS (TOPR ra (Z_to_bv 64 0) a1 a4 a5 s2 s6 t4 t5 t6) F (Z_to_bv 64 0x829ec) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (Z_to_bv 64 E) cSB a0 a1 a2 a3 a4 a5 a6 a7
                          s2 (Z_to_bv 64 (E + 120)) (Z_to_bv 64 (SHE + 15)) (Z_to_bv 64 (E + 92)) s6 (Z_to_bv 64 (E + 116)) (Z_to_bv 64 (E + 96))
                          (Z_to_bv 64 SHE) (Z_to_bv 64 (E + 80)) (Z_to_bv 64 (SHE + 14)) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8373c) fc None m (seg_rom a0segs)).
  Proof.
    intros g e m v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 v104 v112 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 t3 t4 t5 t6 EH1 SL MI SHe K.
    cb_ranges CX. unfold CEILv, apartv, ESTATE_SIZE in *. box_ors.
    pose proof (munch_refl hcr_W m) as MU. pose proof (wmono_refl a0segs m) as WM. unfold hcr_W in MU, SHe.
    unfold EHEAD1 in EH1. unfold hc_slots in SL.
    (* [comment removed for export] *)
    arun_to 0x829ec%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm) end;
      [ st_eq
      | unfold EHEAD1; cbn [est_set_modes e_mode e_state e_avail_in_expect e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse e_bw];
        unfold BZ_S_OUTPUT; exact EH1
      | unfold hc_slots; exact SL | assumption | unfold hcr_W; exact MU | exact WM ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_hc_ret : forall (pin pout : bool) (m : amem) (sp : word) (v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 v112 : word)
      (c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word)
      (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    P = (bv_unsigned sp - 304)%Z ->
    rw_cells a0segs m P (hc_slots E SHE v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 (Z_to_bv 64 (Z.b2z pin)) v112) ->
    rw_cells a0segs m (P + 200) (HSAVED c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) -> stk a0segs m lo P ->
    (stk a0segs m lo (bv_unsigned sp) ->
       evt a0segs Q (MS (mkR cra sp gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 (Z.b2z (pin || pout))) a1 a2 a3 a4 a5 a6 a7 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 t3 t4 t5 t6)
                        F (ret_pc cra) fc None m (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.b2z pout)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8398c) fc None m (seg_rom a0segs)).
  Proof.
    intros pin pout m sp v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 v112 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra
           ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 EP SL SAV ST K.
    unfold CEILv in *. pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    pose proof (b2z_range pout) as BP. pose proof (b2z_range pin) as BI.
    unfold hc_slots in SL. unfold HSAVED in SAV.
    (* [comment removed for export] *)
    wstep. wstep. rewrite (lor_b2z pin pout).
    destruct (pin || pout) eqn:PR; cbn [Z.b2z]; (wstep; flags);
      (* [comment removed for export] *)
      do 13 wstep; wstep;
      pose proof (stk_of_rw_cells a0segs _ _ _ SL) as K0; cbn [cells_size csize Nat.add] in K0; change (Z.of_nat 200) with 200%Z in K0;
      pose proof (stk_of_rw_cells a0segs _ _ _ SAV) as K5; cbn [cells_size csize Nat.add] in K5; change (Z.of_nat 104) with 104%Z in K5;
      pose proof (stk_join a0segs m lo P P (P + 200) ST K0 eq_refl ltac:(lia)) as ST1;
      pose proof (stk_join a0segs m lo (P + 200) (P + 200) (P + 200 + 104) ST1 K5 eq_refl ltac:(lia)) as ST2;
      replace (P + 200 + 104)%Z with (bv_unsigned sp) in ST2 by lia;
      replace (Z_to_bv 64 (P + 304)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia);
      (* [comment removed for export] *)
      wstep; exact (K ST2).
  Qed.

End A0HCG.

End ACeilS1.
