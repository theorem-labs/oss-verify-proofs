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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require A0_b2c_hcA.
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)

Section A0HCD.
  Variables (cx : cctx) (Q : machine_state -> Prop).
  Variables (HCXB : cctx -> Z -> eg -> est -> zstrm -> Prop) (CBFACTS : est -> Prop).
  Variables (SHE SHS : Z) (ob on dbza dbzfr : Z) (p1 p2 : word) (OB : list byte) (P STRM lo : Z).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Notation E := (c_E cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation cSB := (Z_to_bv 64 2147450880).
  Hypothesis ESTRM : STRM = (c_bz cx + BZF_STRM)%Z.
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis LAWS : hc_lawsB HCXB CBFACTS.
  Hypothesis AE : sanchor E SHE. Hypothesis AS : sanchor STRM SHS.
  Hypothesis SLO : (0x61e000 <= STRM)%Z. Hypothesis SHI : (STRM + 80 <= CEILv)%Z.
  Hypothesis LLO : (CEILv <= lo)%Z. Hypothesis PLO : (lo + 16 <= P)%Z. Hypothesis PHI : (P + 304 <= 18446744073709551616)%Z.
  Hypothesis OOK : out_okB (aci_c A0C) cx ob on. Hypothesis LOB : Z.of_nat (length OB) = on.
  Hypothesis SES : apartv E ESTATE_SIZE STRM 80. Hypothesis SOS : apartv ob on STRM 80.

  (* [comment removed for export] *)
  Notation AFTR ra a0 a1 a2 a3 a4 a5 s2 s6 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp (Z_to_bv 64 (E + 16)) (Z_to_bv 64 (E + 8)) (Z_to_bv 64 2) (Z_to_bv 64 E) cSB
         a0 a1 a2 a3 a4 a5 (Z_to_bv 64 1) (Z_to_bv 64 (E + 108))
         s2 (Z_to_bv 64 (E + 120)) (Z_to_bv 64 (SHE + 15)) (Z_to_bv 64 (E + 92)) s6 (Z_to_bv 64 (E + 116)) (Z_to_bv 64 (E + 96)) (Z_to_bv 64 SHE) (Z_to_bv 64 (E + 80))
         (Z_to_bv 64 (SHE + 14)) (Z_to_bv 64 (E + 648)) t4 t5 t6).

  Ltac hcbn := cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_outpos est_set_modes est_set_rl est_rl rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len
         z_in z_avail_in z_outr z_avail_out z_tin_lo z_tin_hi z_tout_lo z_tout_hi fst snd bw_buff bw_live bw_numZ hc_prep_a].
  (* [comment removed for export] *)
  Ltac hci_facts HI :=
    let MODES := ident:(MODES) in let STATES := ident:(STATES) in pose proof (HCIB_est_ok _ _ _ _ _ HI) as EOK;
    pose proof (HCIB_avail_out _ _ _ _ _ HI) as (AOR & OLEN); pose proof (HCIB_avail_in _ _ _ _ _ HI) as (AIL & AIR);
    pose proof (HCIB_mode _ _ _ _ _ HI) as MD; pose proof (HCIB_rl _ _ _ _ _ HI) as RLD; pose proof (HCIB_inUse _ _ _ _ _ HI) as DEFI;
    unfold est_ok in EOK; cps_destruct EOK as (BOK1 & BOK2 & FTR & NBR & NZ0 & POSR & MODES & STATES & CHR & LENR & CRCR & CCR & BNO);
    unfold BZ_M_IDLE, BZ_M_RUNNING, BZ_M_FLUSHING, BZ_M_FINISHING, BZ_S_OUTPUT, BZ_S_INPUT in MODES, STATES, MD.

  Definition haft_W : list (Z * Z) := [(E + 108, E + 124); (E + 648, E + 652)]%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_hc_aft : forall g e z (pout itb : bool) (m : amem) (v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 v104 v112 : word)
      (ra a1 a2 a3 a4 a5 s6 t4 t5 t6 : word),
    e_state e = BZ_S_OUTPUT -> (z_avail_out z = 0 \/ bw_numZ (e_bw e) <= e_state_out_pos e)%Z ->
    HCXB cx on g e z ->
    rw_cells a0segs m E (EHEAD1 cx g e) -> rw_cells a0segs m (E + 640) (EHEAD2 cx g e) ->
    rw_cells a0segs m P (hc_slots E SHE v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 v104 v112) -> mem_inv a0segs m ->
    shzW a0segs haft_W m E (E + ESTATE_SIZE) ->
    (forall (a0' a1' a2' s6' : word),
        hc_aft e z (pout || itb) = (e, z, pout || itb, true) ->
        evt a0segs Q (MS (AFTR ra a0' a1' a2' a3 a4 a5 (Z_to_bv 64 (Z.b2z (pout || itb))) s6' t4 t5 t6) F (Z_to_bv 64 0x8398c) fc None m (seg_rom a0segs))) ->
    (forall m',
        hc_aft e z (pout || itb) = (hc_prep e, z, pout || itb, false) -> HCXB cx on g (hc_prep e) z ->
        rw_cells a0segs m' E (EHEAD1 cx g (hc_prep_a e)) -> rw_cells a0segs m' (E + 640) (EHEAD2 cx g (hc_prep_a e)) ->
        rw_cells a0segs m' P (hc_slots E SHE v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 v104 v112) -> mem_inv a0segs m' ->
        munch haft_W m m' -> wmono a0segs m m' ->
        evt a0segs Q (MS (AFTR (Z_to_bv 64 0x82cb4) (Z_to_bv 64 (E + 128)) (Z_to_bv 64 0) (Z_to_bv 64 256) a3 a4 a5 (Z_to_bv 64 (Z.b2z (pout || itb))) (Z_to_bv 64 (e_mode e)) t4 t5 t6)
                         F (Z_to_bv 64 0x52ea0) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (AFTR ra (Z_to_bv 64 (Z.b2z itb)) a1 a2 a3 a4 a5 (Z_to_bv 64 (Z.b2z pout)) s6 t4 t5 t6) F (Z_to_bv 64 0x82bd8) fc None m (seg_rom a0segs)).
  Proof.
    intros g e z pout itb m v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 v104 v112 ra a1 a2 a3 a4 a5 s6 t4 t5 t6 STO EXO HX EH1 EH2 SL MI SHe KR KM.
    pose proof (hlB_hci _ _ LAWS _ _ _ _ _ HX) as HI. hci_facts HI. destruct MD as (MD & GA & AIE).
    cps_pose (HCIB_output _ _ _ _ _ HI STO) as (GZ & NZR & ZREL).
    cb_ranges CX. unfold CEILv, apartv, ESTATE_SIZE in *. box_ors.
    pose proof (b2z_range pout) as BP. pose proof (b2z_range itb) as BI.
    pose proof (munch_refl haft_W m) as MU. pose proof (wmono_refl a0segs m) as WM. unfold haft_W in MU, SHe.
    unfold EHEAD1 in EH1. rewrite GA, <- ESTRM in EH1. unfold EHEAD2 in EH2. unfold hc_slots in SL.
    (* [comment removed for export] *)
    arun_to 0x82bf4%Z. rewrite (lor_b2z itb pout), (Bool.orb_comm itb pout).
    wstep; if_cases KP; zify_cond_z KP.
    { enter_with (KR _ _ _ _); [st_eq| unfold hc_aft; replace (e_state_out_pos e <? bw_numZ (e_bw e))%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity]. }
    assert (T1 : (e_state_out_pos e <? bw_numZ (e_bw e))%Z = false) by (apply Z.ltb_ge; lia).
    (* [comment removed for export] *)
    assert (PREP : forall (x10 x11 x12 : word),
      ((e_mode e =? BZ_M_FINISHING)%Z && (e_avail_in_expect e =? 0)%Z && isempty_RL_e e)%bool = false ->
      evt a0segs Q (MS (AFTR ra x10 x11 x12 a3 a4 a5 (Z_to_bv 64 (Z.b2z (pout || itb))) (Z_to_bv 64 (e_mode e)) t4 t5 t6) F (Z_to_bv 64 0x82c60) fc None m (seg_rom a0segs))).
    { intros x10 x11 x12 NF.
      pose proof (hlB_prep _ _ LAWS cx on g e z HX STO ltac:(lia) NF) as HX'.
      (* [comment removed for export] *)
      arun_to 0x82ca4%Z.
      reword_C4 EH2 2%nat 4294967295%Z. { reflexivity. }
      (* [comment removed for export] *)
      arun_to 0x52ea0%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KM mm) end;
        [ st_eq
        | unfold hc_aft; rewrite T1; rewrite NF; unfold hc_prep, prepare_new_block; hcbn; hcbn;
          rewrite MD; cbn [Z.eqb Pos.eqb BZ_M_FLUSHING andb]; reflexivity
        | exact HX'
        | unfold EHEAD1; hcbn; rewrite GA, <- ESTRM; exact EH1
        | unfold EHEAD2; hcbn; unfold crc_init; exact EH2
        | unfold hc_slots; exact SL | assumption | unfold haft_W; exact MU | exact WM ]. }
    (* [comment removed for export] *)
    arun. if_cases KM4; zify_cond_z KM4; [exfalso; clear - KM4 MD; lia|].
    (* [comment removed for export] *)
    arun. if_cases KE; zify_cond_z KE.
    { assert (NF : ((e_mode e =? BZ_M_FINISHING)%Z && (e_avail_in_expect e =? 0)%Z && isempty_RL_e e)%bool = false).
      { replace (e_avail_in_expect e =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia). rewrite Bool.andb_false_r. reflexivity. }
      enter_with (PREP _ _ _ NF); st_eq. }
    (* [comment removed for export] *)
    arun. if_cases KC; zify_cond_z KC.
    { enter_with (KR _ _ _ _); [st_eq| unfold hc_aft; rewrite T1; unfold isempty_RL_e, isempty_RL, est_rl; hcbn; rewrite MD;
          replace (e_avail_in_expect e =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia);
          cbn [Z.eqb Pos.eqb BZ_M_FINISHING andb]; replace (e_state_in_ch e <? 256)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity]. }
    (* [comment removed for export] *)
    arun. if_cases KL; zify_cond_z KL.
    { enter_with (KR _ _ _ _); [st_eq| unfold hc_aft; rewrite T1; unfold isempty_RL_e, isempty_RL, est_rl; hcbn; rewrite MD;
          replace (e_avail_in_expect e =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia);
          cbn [Z.eqb Pos.eqb BZ_M_FINISHING andb]; replace (e_state_in_ch e <? 256)%Z with true by (symmetry; apply Z.ltb_lt; lia);
          replace (0 <? e_state_in_len e)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity]. }
    assert (NF : ((e_mode e =? BZ_M_FINISHING)%Z && (e_avail_in_expect e =? 0)%Z && isempty_RL_e e)%bool = false).
    { unfold isempty_RL_e, isempty_RL, est_rl. hcbn.
      replace (e_state_in_ch e <? 256)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      replace (0 <? e_state_in_len e)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb andb]. apply Bool.andb_false_r. }
    enter_with (PREP _ _ _ NF); st_eq.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition hco_W : list (Z * Z) := [(E + 108, E + 124); (E + 648, E + 652); (STRM + 24, STRM + 44); (ob, ob + on)]%Z.

  Notation TOPR ra a0 a1 a4 a5 s2 s6 t4 t5 t6 := (AFTR ra a0 a1 (Z_to_bv 64 (E + 12)) (Z_to_bv 64 (SHE + 1)) a4 a5 s2 s6 t4 t5 t6).

  Lemma A0_hc_out : forall g e z (pout : bool) (ni : Z) (m : amem) (v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 v104 v112 : word)
      (ra a0 a1 a4 a5 s6 t4 t5 t6 : word),
    e_state e = BZ_S_OUTPUT -> HCXB cx on g e z ->
    rw_cells a0segs m E (EHEAD1 cx g e) -> rw_cells a0segs m (E + 640) (EHEAD2 cx g e) ->
    rw_cells a0segs m STRM (STRMB cx ob on dbza dbzfr z ni p1 p2) -> u8arr a0segs m ob (outb (z_outr z) OB) ->
    rw_cells a0segs m P (hc_slots E SHE v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 v104 v112) ->
    u8arrW hco_W m A2 (zb8 (e_arr2 e) ARR2_SIZE) -> mem_inv a0segs m ->
    shzW a0segs hco_W m E (E + ESTATE_SIZE) -> shzW a0segs hco_W m STRM (STRM + 80) -> shzW a0segs hco_W m A2 (A2 + ARR2_SIZE) -> shpW a0segs hco_W m ob (ob + on) ->
    (forall e1 z1 pout1 m' (a0' a1' a2' a3' s6' : word),
        hc_out e z pout = (e1, z1, pout1, true) -> HCXB cx on g e1 z1 -> z_in z1 = z_in z -> z_avail_in z1 = z_avail_in z -> e_arr2 e1 = e_arr2 e ->
        rw_cells a0segs m' E (EHEAD1 cx g e1) -> rw_cells a0segs m' (E + 640) (EHEAD2 cx g e1) ->
        rw_cells a0segs m' STRM (STRMB cx ob on dbza dbzfr z1 ni p1 p2) -> u8arr a0segs m' ob (outb (z_outr z1) OB) ->
        rw_cells a0segs m' P (hc_slots E SHE v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 v104 v112) -> mem_inv a0segs m' ->
        munch hco_W m m' -> wmono a0segs m m' ->
        evt a0segs Q (MS (AFTR ra a0' a1' a2' a3' a4 a5 (Z_to_bv 64 (Z.b2z pout1)) s6' t4 t5 t6) F (Z_to_bv 64 0x8398c) fc None m' (seg_rom a0segs))) ->
    (forall e1 z1 pout1 m' (a3' : word),
        hc_out e z pout = (hc_prep e1, z1, pout1, false) -> HCXB cx on g (hc_prep e1) z1 -> z_in z1 = z_in z -> z_avail_in z1 = z_avail_in z -> e_arr2 e1 = e_arr2 e ->
        rw_cells a0segs m' E (EHEAD1 cx g (hc_prep_a e1)) -> rw_cells a0segs m' (E + 640) (EHEAD2 cx g (hc_prep_a e1)) ->
        rw_cells a0segs m' STRM (STRMB cx ob on dbza dbzfr z1 ni p1 p2) -> u8arr a0segs m' ob (outb (z_outr z1) OB) ->
        rw_cells a0segs m' P (hc_slots E SHE v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 v104 v112) -> mem_inv a0segs m' ->
        munch hco_W m m' -> wmono a0segs m m' ->
        evt a0segs Q (MS (AFTR (Z_to_bv 64 0x82cb4) (Z_to_bv 64 (E + 128)) (Z_to_bv 64 0) (Z_to_bv 64 256) a3' a4 a5 (Z_to_bv 64 (Z.b2z pout1)) (Z_to_bv 64 (e_mode e1)) t4 t5 t6)
                         F (Z_to_bv 64 0x52ea0) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (TOPR ra a0 a1 a4 a5 (Z_to_bv 64 (Z.b2z pout)) s6 t4 t5 t6) F (Z_to_bv 64 0x829ec) fc None m (seg_rom a0segs)).
  Proof.
    intros g e z pout ni m v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 v104 v112 ra a0 a1 a4 a5 s6 t4 t5 t6 STO HX EH1 EH2 SM OBM SL VA2 MI SHe SHs SH2 SHo KR KM.
    pose proof EH1 as EH1f. pose proof SM as SMf. pose proof SL as SLf. pose proof SHe as SHe0. pose proof SHs as SHs0.
    pose proof (hlB_hci _ _ LAWS _ _ _ _ _ HX) as HI. hci_facts HI. destruct MD as (MD & GA & AIE).
    cps_pose (HCIB_output _ _ _ _ _ HI STO) as (GZ & NZR & ZREL).
    cb_ranges CX.
    pose proof OOK as OOK'. unfold out_okB, apart, img_apart in OOK'. cbn [ci_hi aci_c A0C] in OOK'. cps_destruct OOK' as (RO1 & RO2 & RO3 & RO4 & SO1 & SO2 & SO3 & SO4 & IO).
    unfold CEILv, CEIL, apartv, ESTATE_SIZE in *. box_ors.
    pose proof (b2z_range pout) as BP. pose proof (proj2 AE : saddr E SHE) as AEs.
    pose proof (munch_refl hco_W m) as MU. pose proof (wmono_refl a0segs m) as WM. unfold hco_W in MU, SHe, SHs.
    assert (DJO : forall outr, (Z.of_nat (length outr) <= on)%Z -> disjoint_from haft_W ob (Z.of_nat (length (outb outr OB)))).
    { intros outr Ho. rewrite (outb_length outr OB on LOB Ho). unfold haft_W. cbn [disjoint_from]. clear - SO1 XE0 XE1 RO1 RO2. unfold id in SO1. lia. }
    rewrite hc_out_aft in KR, KM.
    replace (Z.to_nat (z_avail_out z) + 1)%nat with (S (Z.to_nat (z_avail_out z))) in KR, KM by lia.
    (* [comment removed for export] *)
    assert (AFT : forall e' z' (itb : bool) (mj : amem) (x11 x12 x13 : word),
      e_state e' = BZ_S_OUTPUT -> (z_avail_out z' = 0 \/ bw_numZ (e_bw e') <= e_state_out_pos e')%Z ->
      HCXB cx on g e' z' -> z_in z' = z_in z -> z_avail_in z' = z_avail_in z -> e_arr2 e' = e_arr2 e ->
      copy_output (S (Z.to_nat (z_avail_out z))) e z pout = (e', z', pout || itb) ->
      rw_cells a0segs mj E (EHEAD1 cx g e') -> rw_cells a0segs mj (E + 640) (EHEAD2 cx g e') ->
      rw_cells a0segs mj STRM (STRMB cx ob on dbza dbzfr z' ni p1 p2) -> u8arr a0segs mj ob (outb (z_outr z') OB) ->
      rw_cells a0segs mj P (hc_slots E SHE v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 v104 v112) -> mem_inv a0segs mj ->
      munch hco_W m mj -> wmono a0segs m mj ->
      evt a0segs Q (MS (AFTR ra (Z_to_bv 64 (Z.b2z itb)) x11 x12 x13 a4 a5 (Z_to_bv 64 (Z.b2z pout)) s6 t4 t5 t6) F (Z_to_bv 64 0x82bd8) fc None mj (seg_rom a0segs))).
    { clear EH1 EH1f EH2 SM SMf OBM SL SLf MI MU WM. intros e' z' itb mj x11 x12 x13 ST' EX' HXn ZI' ZA' AR' CO' EH1 EH2 SM OBM SL MI MU WM.
      rewrite CO' in KR, KM.
      pose proof (hlB_hci _ _ LAWS _ _ _ _ _ HXn) as HI'. pose proof (HCIB_avail_out _ _ _ _ _ HI') as (AOR' & OLEN').
      eapply (A0_hc_aft g e' z' pout itb mj); [ exact ST' | exact EX' | exact HXn | exact EH1 | exact EH2 | exact SL | exact MI
        | eapply (shzW_sub a0segs _ _ m mj _ _ _ _ SHe0 MU); [unfold hco_W, haft_W; a_sub_fp| lia| unfold ESTATE_SIZE; lia] | |].
      - intros a0' a1' a2' s6' HA.
        eapply (KR e' z' (pout || itb) mj); [exact HA | exact HXn | exact ZI' | exact ZA' | exact AR' | exact EH1 | exact EH2 | exact SM | exact OBM | exact SL | exact MI | exact MU | exact WM].
      - intros m' HA HX' EH1' EH2' SL' MI' MU' WM'.
        pose proof (u8arr_transport a0segs _ mj m' ob _ OBM MU' WM' (DJO (z_outr z') ltac:(lia))) as OBM'.
        unfold STRMB in SM. unfold hco_W in MU.
        clear EH1 EH2 SL OBM MI. unfold haft_W in MU'. transport_after_call a0segs mj m' MU' WM'.
        eapply (KM e' z' (pout || itb) m'); [exact HA | exact HX' | exact ZI' | exact ZA' | exact AR' | exact EH1' | exact EH2' | unfold STRMB; exact SM | exact OBM' | exact SL' | exact MI'
          | unfold hco_W; exact MU | exact WM]. }
    idtac "AFT done".
    unfold EHEAD1 in EH1. rewrite GA, <- ESTRM, STO in EH1. unfold BZ_S_OUTPUT in EH1. unfold STRMB in SM.
    (* [comment removed for export] *)
    arun. if_cases KA; zify_cond_z KA.
    { enter_with (AFT e z false m _ _ _); [ st_eq; cbn [Z.b2z]; lia | exact STO | lia | exact HX | reflexivity | reflexivity | reflexivity
        | rewrite copy_output_S, Bool.orb_false_r; replace (z_avail_out z =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia); reflexivity
        | exact EH1f | exact EH2 | exact SMf | exact OBM | exact SLf | exact MI | unfold hco_W; exact MU | exact WM ]. }
    (* [comment removed for export] *)
    arun. if_cases KG; zify_cond_z KG.
    { (* [comment removed for export] *)
      wstep.
      enter_with (AFT e z false m _ _ _); [ st_eq | exact STO | lia | exact HX | reflexivity | reflexivity | reflexivity
        | rewrite copy_output_S, Bool.orb_false_r; replace (z_avail_out z =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia);
          replace (bw_numZ (e_bw e) <=? e_state_out_pos e)%Z with true by (symmetry; apply Z.leb_le; lia); reflexivity
        | exact EH1f | exact EH2 | exact SMf | exact OBM | exact SLf | exact MI | unfold hco_W; exact MU | exact WM ]. }
    (* [comment removed for export] *)
    assert (CT : copy_output (S (Z.to_nat (z_avail_out z))) e z pout = copy_output (S (Z.to_nat (z_avail_out z))) e z true).
    { rewrite !copy_output_S. replace (z_avail_out z =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
      replace (bw_numZ (e_bw e) <=? e_state_out_pos e)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
    pose proof SLO as SLO'. pose proof SHI as SHI'. pose proof SES as SES'. pose proof SOS as SOS'. rewrite ESTRM in SLO', SHI', SES', SOS'.
    pose proof SMf as SMc. rewrite ESTRM in SMc.
    enter_with (A0_b2c_hcA.A0_co_loop cx Q HCXB CBFACTS SHE ob on dbza dbzfr p1 p2 OB gp tp F fc CX SEP LAWS AE SLO' SHI' OOK LOB SES' SOS'
                  (S (Z.to_nat (z_avail_out z))) g e z ni m m);
      [ st_eq | lia | exact STO | lia | lia | exact HX | exact EH1f | exact SMc | exact OBM
      | intros mv MUv; apply VA2; eapply munch_weaken; [| exact MUv]; unfold A0_b2c_hcA.co_W, hco_W; rewrite <- ESTRM; a_sub_fp
      | exact MI | apply munch_refl | apply wmono_refl
      | eapply (shzW_sub a0segs _ _ m m _ _ _ _ SHe0 (munch_refl _ _)); [unfold A0_b2c_hcA.co_W, hco_W; rewrite <- ESTRM; a_sub_fp| lia| unfold ESTATE_SIZE; lia]
      | rewrite <- ESTRM; eapply (shzW_sub a0segs _ _ m m _ _ _ _ SHs0 (munch_refl _ _)); [unfold A0_b2c_hcA.co_W, hco_W; rewrite <- ESTRM; a_sub_fp| lia| lia]
      | eapply (shzW_sub a0segs _ _ m m _ _ _ _ SH2 (munch_refl _ _)); [unfold A0_b2c_hcA.co_W, hco_W; rewrite <- ESTRM; a_sub_fp| lia| lia]
      | eapply (shpW_sub a0segs _ _ m m _ _ _ _ SHo (munch_refl _ _)); [unfold A0_b2c_hcA.co_W, hco_W; rewrite <- ESTRM; a_sub_fp| lia| lia]
      | ].
    intros e' z' m' a1' a2' a3' CO' ST' EX' HXn ZI' ZA' AR' EH1' SM' OBM' MI' MU' WM'.
    rewrite <- ESTRM in SM'.
    assert (MUh : munch hco_W m m') by (eapply munch_weaken; [| exact MU']; unfold A0_b2c_hcA.co_W, hco_W; rewrite <- ESTRM; a_sub_fp).
    unfold hc_slots in SL. unfold EHEAD2 in EH2.
    clear EH1 EH1f SM SMf SMc OBM MI. unfold A0_b2c_hcA.co_W in MU'. rewrite <- ESTRM in MU'. transport_after_call a0segs m m' MU' WM'.
    enter_with (AFT e' z' true m' _ _ _); [ st_eq | exact ST' | exact EX' | exact HXn | exact ZI' | exact ZA' | exact AR'
      | rewrite Bool.orb_true_r, CT; exact CO'
      | exact EH1'
      | pose proof (copy_output_frame (S (Z.to_nat (z_avail_out z))) e z true) as FRM; rewrite CO' in FRM; cbn [fst] in FRM; rewrite FRM; unfold EHEAD2; hcbn; exact EH2
      | exact SM' | exact OBM' | unfold hc_slots; exact SL | exact MI' | exact MUh | exact WM' ].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

End A0HCD.

End ACeilS1.
