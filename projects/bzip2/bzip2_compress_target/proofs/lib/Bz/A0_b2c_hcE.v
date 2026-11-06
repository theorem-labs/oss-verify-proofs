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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_msV A0_cmp_cbV A0_b2c_hcV A0_b2c_hcR.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require A0_b2c_hcC.
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)

Section A0HCE.
  Variables (cx : cctx) (Q : machine_state -> Prop).
  Variables (HCXB : cctx -> Z -> eg -> est -> zstrm -> Prop) (CBFACTS : est -> Prop).
  Variables (SHE SHS : Z) (ob on dbza dbzfr : Z) (p1 p2 sv : word) (P STRM lo : Z) (z0 : zstrm) (nb : Z) (pl : list byte).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Notation E := (c_E cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation cSB := (Z_to_bv 64 2147450880).
  Hypothesis ESTRM : STRM = (c_bz cx + BZF_STRM)%Z.
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis IMG : cctx_img (aci_c A0C) cx. Hypothesis LAWS : hc_lawsB HCXB CBFACTS.
  Hypothesis AE : sanchor E SHE. Hypothesis AS : sanchor STRM SHS.
  Hypothesis SLO : (0x61e000 <= STRM)%Z. Hypothesis SHI : (STRM + 80 <= CEILv)%Z.
  Hypothesis LLO : (CEILv <= lo)%Z. Hypothesis PLO : (lo + 16 <= P)%Z. Hypothesis PHI : (P + 304 <= 18446744073709551616)%Z.
  Hypothesis SES : apartv E ESTATE_SIZE STRM 80. Hypothesis S2S : apartv A2 ARR2_SIZE STRM 80.
  Hypothesis PAYR : pl <> [] -> (0 < nb /\ nb + Z.of_nat (length pl) <= CEILv)%Z.

  Local Notation ci_W := (A0_b2c_hcC.ci_W cx P STRM).
  Local Notation ci_loopL := (A0_b2c_hcC.A0_ci_loop cx Q HCXB CBFACTS SHE ob on dbza dbzfr p1 p2 sv P STRM lo z0 nb pl gp tp F fc ESTRM CX SEP IMG LAWS AE SLO SHI LLO PLO PHI SES S2S PAYR).
  Local Notation ap_callL := (A0_b2c_hcC.A0_ap_call cx Q sv P STRM lo gp tp F fc CX SEP IMG SLO SHI LLO PLO PHI).

  Ltac hcbn := cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_outpos est_set_modes est_set_rl est_rl rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len
         z_in z_avail_in z_outr z_avail_out z_tin_lo z_tin_hi z_tout_lo z_tout_hi fst snd].
  Ltac hcbn_in H := cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_outpos est_set_modes est_set_rl est_rl rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len
         z_in z_avail_in z_outr z_avail_out z_tin_lo z_tin_hi z_tout_lo z_tout_hi fst snd] in H.
  Ltac hci_facts HI :=
    let MODES := ident:(MODES) in let STATES := ident:(STATES) in pose proof (HCIB_est_ok _ _ _ _ _ HI) as EOK;
    pose proof (HCIB_avail_out _ _ _ _ _ HI) as (AOR & OLEN); pose proof (HCIB_avail_in _ _ _ _ _ HI) as (AIL & AIR);
    pose proof (HCIB_mode _ _ _ _ _ HI) as MD; pose proof (HCIB_rl _ _ _ _ _ HI) as RLD; pose proof (HCIB_inUse _ _ _ _ _ HI) as DEFI;
    unfold est_ok in EOK; cps_destruct EOK as (BOK1 & BOK2 & FTR & NBR & NZ0 & POSR & MODES & STATES & CHR & LENR & CRCR & CCR & BNO);
    unfold BZ_M_IDLE, BZ_M_RUNNING, BZ_M_FLUSHING, BZ_M_FINISHING, BZ_S_OUTPUT, BZ_S_INPUT in MODES, STATES, MD.

  (* [comment removed for export] *)
  Notation CBR il t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s6 t3 t4 t5 t6 :=
    (mkR (Z_to_bv 64 0x8373c) (Z_to_bv 64 P) gp tp t0 t1 t2 (Z_to_bv 64 E) cSB (Z_to_bv 64 E) (Z_to_bv 64 (if il then 1 else 0)) a2 a3 a4 a5 a6 a7
         s2 (Z_to_bv 64 (E + 120)) (Z_to_bv 64 (SHE + 15)) (Z_to_bv 64 (E + 92)) s6 (Z_to_bv 64 (E + 116)) (Z_to_bv 64 (E + 96)) (Z_to_bv 64 SHE) (Z_to_bv 64 (E + 80))
         (Z_to_bv 64 (SHE + 14)) t3 t4 t5 t6).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition hfin_W : list (Z * Z) := [(E + 92, E + 112); (E + 128, E + 384); (E + 648, E + 652); (A2, A2 + ARR2_SIZE); (P - 16, P); (P + 104, P + 112)]%Z.
  Lemma A0_hc_fin : forall g e z (pin itb : bool) (m : amem) (v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 : word)
      (a0 a1 a2 a4 a5 s2 s6 t4 : word),
    e_state e = BZ_S_INPUT -> (NBLOCKMAX <= e_nblock e \/ z_avail_in z = 0)%Z -> HCXB cx on g e z ->
    rw_cells a0segs m E (EHEAD1 cx g e) -> rw_cells a0segs m (E + 640) (EHEAD2 cx g e) ->
    u8arr a0segs m (E + 128) (ovb (e_inUse e) (jseg J 128 256) 256) -> u8arr a0segs m A2 (zb8 (e_arr2 e) ARR2_SIZE) ->
    rw_cells a0segs m P (hc_slots E SHE v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 (Z_to_bv 64 (SHE + 1)) (Z_to_bv 64 (Z.b2z pin)) (Z_to_bv 64 (SHE + -2147450868))) ->
    stk a0segs m lo P -> mem_inv a0segs m ->
    acimgW hfin_W m sv -> acoW hfin_W m -> cctx_sh a0segs cx hfin_W m -> cimg_sh A0C hfin_W m ->
    (forall e_cb (il : bool) m' (t0' t1' t2' a2' a3' a4' a5' a6' a7' s6' t3' t4' t5' t6' : word),
        ((il = true /\ e_avail_in_expect e = 0%Z /\ e_cb = hc_flush e) \/ (il = false /\ e_avail_in_expect e <> 0%Z /\ (NBLOCKMAX <= e_nblock e)%Z /\ e_cb = e)) ->
        cb_pre g e_cb -> CBFACTS e_cb -> HCXB cx on (eg_after_cb cx g e_cb) (hc_after_cb e_cb il) z ->
        rw_cells a0segs m' E (EHEAD1 cx g e_cb) -> rw_cells a0segs m' (E + 640) (EHEAD2 cx g e_cb) ->
        u8arr a0segs m' (E + 128) (ovb (e_inUse e_cb) (jseg J 128 256) 256) -> u8arr a0segs m' A2 (zb8 (e_arr2 e_cb) ARR2_SIZE) ->
        rw_cells a0segs m' P (hc_slots E SHE v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 (Z_to_bv 64 (SHE + 1)) (Z_to_bv 64 (Z.b2z (pin || itb))) (Z_to_bv 64 (SHE + -2147450868))) ->
        stk a0segs m' lo P -> mem_inv a0segs m' -> munch hfin_W m m' -> wmono a0segs m m' ->
        evt a0segs Q (MS (CBR il t0' t1' t2' a2' a3' a4' a5' a6' a7' s2 s6' t3' t4' t5' t6') F (Z_to_bv 64 0x88a10) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR (Z_to_bv 64 (SHE + -2147450869)) (Z_to_bv 64 P) gp tp (Z_to_bv 64 (E + 16)) (Z_to_bv 64 (E + 8)) (Z_to_bv 64 2) (Z_to_bv 64 E) cSB
                          a0 a1 a2 (Z_to_bv 64 (Z.b2z itb)) a4 a5 (Z_to_bv 64 1) (Z_to_bv 64 (E + 108))
                          s2 (Z_to_bv 64 (E + 120)) (Z_to_bv 64 (SHE + 15)) (Z_to_bv 64 (E + 92)) s6 (Z_to_bv 64 (E + 116)) (Z_to_bv 64 (E + 96)) (Z_to_bv 64 SHE) (Z_to_bv 64 (E + 80))
                          (Z_to_bv 64 (SHE + 14)) (Z_to_bv 64 (E + 648)) t4 (Z_to_bv 64 (SHE + 13)) (Z_to_bv 64 (SHE + 14)))
                     F (Z_to_bv 64 0x83638) fc None m (seg_rom a0segs)).
  Proof.
    intros g e z pin itb m v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 a0 a1 a2 a4 a5 s2 s6 t4 STI EXI HX EH1 EH2 INU AR2 SL ST MI VCM VAC CSH0 ISH0 K.
    pose proof (hlB_hci _ _ LAWS _ _ _ _ _ HX) as HI. hci_facts HI. destruct MD as (MD & GA & AIE).
    pose proof CSH0 as CSH. cps_destruct CSH as (SHe & SH1 & SH2 & SHF & SHFp). clear SH1 SH2 SHF SHFp.
    pose proof SEP as SP'; unfold cctx_sep, apart, ESTATE_SIZE in SP'; cbv zeta in SP'; cps_destruct SP' as (_ & AEA2 & _).
    cb_ranges CX. unfold CEILv, apartv, ESTATE_SIZE in *. box_ors.
    pose proof (proj2 AE : saddr E SHE) as AEs.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    pose proof (b2z_range pin) as BI. pose proof (b2z_range itb) as BT.
    pose proof (munch_refl hfin_W m) as MU. pose proof (wmono_refl a0segs m) as WM. unfold hfin_W in MU, SHe.
    unfold EHEAD1 in EH1. rewrite GA, <- ESTRM, MD in EH1. unfold EHEAD2 in EH2. unfold hc_slots in SL.
    (* [comment removed for export] *)
    arun. rewrite (lor_b2z itb pin), (Bool.orb_comm itb pin) in SL.
    if_cases KE; zify_cond_z KE.
    - (* [comment removed for export] *)
      assert (E0 : e_avail_in_expect e = 0%Z) by lia.
      cps_pose (hlB_cbF _ _ LAWS cx on g e z HX STI E0) as (PRE & FACTS & HX').
      rewrite hc_cbF_after in HX'.
      assert (MFL : (e_mode (hc_flush e) =? BZ_M_FINISHING)%Z = true) by (unfold hc_flush; hcbn; rewrite MD; reflexivity).
      rewrite MFL in HX'.
      (* [comment removed for export] *)
      assert (FLT : forall (r1 : rlst) (mj : amem) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
        r1 = (if (e_state_in_ch e <? 256)%Z then add_pair_to_block (est_rl e) else est_rl e) ->
        rw_cells a0segs mj E (EHEAD1 cx g (est_set_rl e r1)) -> rw_cells a0segs mj (E + 640) (EHEAD2 cx g (est_set_rl e r1)) ->
        u8arr a0segs mj (E + 128) (ovb (rl_inUse r1) (jseg J 128 256) 256) -> u8arr a0segs mj A2 (zb8 (rl_block r1) ARR2_SIZE) ->
        rw_cells a0segs mj P (hc_slots E SHE v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 (Z_to_bv 64 (SHE + 1)) (Z_to_bv 64 (Z.b2z (pin || itb))) (Z_to_bv 64 (SHE + -2147450868))) ->
        stk a0segs mj lo P -> mem_inv a0segs mj -> munch hfin_W m mj -> wmono a0segs m mj ->
        evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 (Z_to_bv 64 (E + 8)) x7 (Z_to_bv 64 E) cSB x10 x11 x12 x13 x14 x15 x16 x17
                              s2 (Z_to_bv 64 (E + 120)) (Z_to_bv 64 (SHE + 15)) (Z_to_bv 64 (SHE + 11)) (Z_to_bv 64 (E + 92)) (Z_to_bv 64 (E + 116)) (Z_to_bv 64 (E + 96)) (Z_to_bv 64 SHE)
                              (Z_to_bv 64 (E + 80)) (Z_to_bv 64 (SHE + 14)) x28 x29 x30 x31)
                         F (Z_to_bv 64 0x836f4) fc None mj (seg_rom a0segs))).
      { clear EH1 EH2 INU AR2 SL ST MI MU WM. intros r1 mj x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 R1 EH1 EH2 INU AR2 SL ST MI MU WM.
        assert (FL : hc_flush e = est_set_rl e (RL (rl_nblock r1) (rl_block r1) (rl_inUse r1) (rl_crc r1) 256 0)).
        { hcbn_in R1. unfold hc_flush, flush_RL, init_RL. hcbn. rewrite <- R1. reflexivity. }
        unfold hfin_W in MU. unfold EHEAD1 in EH1. hcbn_in EH1. rewrite GA, <- ESTRM, MD in EH1. unfold hc_slots in SL.
        (* [comment removed for export] *)
        arun_to 0x83730%Z. wstep; flags.
        (* [comment removed for export] *)
        arun_to 0x88a10%Z.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (hc_flush e) true mm _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [ st_eq | left; split; [reflexivity| split; [exact E0| reflexivity]] | exact PRE | exact FACTS | exact HX'
          | rewrite FL; unfold EHEAD1; hcbn; rewrite GA, <- ESTRM, MD; exact EH1 | rewrite FL; unfold EHEAD2 in EH2 |- *; hcbn_in EH2; hcbn; exact EH2
          | rewrite FL; hcbn; exact INU | rewrite FL; hcbn; exact AR2 | unfold hc_slots; exact SL | exact ST | exact MI | unfold hfin_W; exact MU | exact WM ]. }
      (* [comment removed for export] *)
      arun. if_cases KC; zify_cond_z KC.
      + lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (FLT (est_rl e) mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [ st_eq | replace (e_state_in_ch e <? 256)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity
          | unfold EHEAD1; hcbn; rewrite GA, <- ESTRM, MD; exact EH1 | unfold EHEAD2; hcbn; exact EH2 | hcbn; exact INU | hcbn; exact AR2
          | unfold hc_slots; exact SL | exact ST | exact MI | unfold hfin_W; exact MU | exact WM ].
      + (* [comment removed for export] *)
        assert (LEN1 : (1 <= e_state_in_len e)%Z) by (clear - RLD KC; unfold id in RLD; lia).
        arun_to 0x884f4%Z.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
        pose proof (VCM m1 MU) as CM.
        eapply (ap_callL g e m1);
          [ lia | lia | exact CRCR | lia | destruct EXI; bz_params; lia | exact DEFI | exact BOK2
          | unfold EHEAD1; rewrite GA, <- ESTRM, MD; exact EH1 | unfold EHEAD2; exact EH2 | exact INU | exact AR2 | exact CM | exact MI | exact ST
          | exact (VAC m1 MU)
          | eapply (cctx_sh_sub a0segs cx hfin_W _ m m1 CSH0 MU); unfold hfin_W, A0_b2c_hcC.hap_W; a_sub_fp
          | unfold cimg_sh in *; eapply (shzW_sub a0segs hfin_W _ m m1 _ _ _ _ ISH0 MU); [unfold hfin_W, A0_b2c_hcC.hap_W; a_sub_fp| lia| lia]
          | ].
        intros m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' e' EH1' EH2' INU' AR2' MI' ST' MU' WM'. subst e'.
        lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
          replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
        clear EH1 EH2 INU AR2 MI ST CM. unfold A0_b2c_hcC.hap_W in MU'. transport_after_call a0segs m1 m' MU' WM'.
        (* [comment removed for export] *)
        arun_to 0x836f4%Z.
        enter_with (FLT (add_pair_to_block (est_rl e)) m' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
          [ st_eq | replace (e_state_in_ch e <? 256)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity
          | exact EH1' | exact EH2' | hcbn_in INU'; exact INU' | hcbn_in AR2'; exact AR2'
          | unfold hc_slots; exact SL | exact ST' | exact MI' | unfold hfin_W; exact MU | exact WM ].
    - (* [comment removed for export] *)
      assert (NE0 : e_avail_in_expect e <> 0%Z) by lia.
      arun. if_cases KN; zify_cond_z KN; [| exfalso; destruct EXI as [EXI|EXI]; bz_params; lia].
      cps_pose (hlB_cbM _ _ LAWS cx on g e z HX STI NE0 ltac:(bz_params; lia)) as (PRE & FACTS & HX').
      rewrite hc_cbR_after in HX'.
      (* [comment removed for export] *)
      arun_to 0x88a10%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K e false mm _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [ st_eq | right; split; [reflexivity| split; [exact NE0| split; [bz_params; lia| reflexivity]]] | exact PRE | exact FACTS | exact HX'
        | unfold EHEAD1; rewrite GA, <- ESTRM, MD; exact EH1 | unfold EHEAD2; exact EH2 | exact INU | exact AR2 | unfold hc_slots; exact SL | exact ST | exact MI
        | unfold hfin_W; exact MU | exact WM ].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation INR ra a0 a1 a2 a3 a4 a5 s2 s6 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp (Z_to_bv 64 (E + 16)) (Z_to_bv 64 (E + 8)) (Z_to_bv 64 2) (Z_to_bv 64 E) cSB
         a0 a1 a2 a3 a4 a5 (Z_to_bv 64 1) (Z_to_bv 64 (E + 108))
         s2 (Z_to_bv 64 (E + 120)) (Z_to_bv 64 (SHE + 15)) (Z_to_bv 64 (E + 92)) s6 (Z_to_bv 64 (E + 116)) (Z_to_bv 64 (E + 96)) (Z_to_bv 64 SHE) (Z_to_bv 64 (E + 80))
         (Z_to_bv 64 (SHE + 14)) (Z_to_bv 64 (E + 648)) t4 t5 t6).

  Lemma A0_hc_in : forall g e z (pin pout : bool) (m : amem) (v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 v112 : word)
      (ra a0 a1 a2 a3 a4 a5 s6 t4 t5 t6 : word),
    e_state e = BZ_S_INPUT -> HPURE HCXB cx on z0 pl g e z ->
    rw_cells a0segs m E (EHEAD1 cx g e) -> rw_cells a0segs m (E + 640) (EHEAD2 cx g e) ->
    u8arr a0segs m (E + 128) (ovb (e_inUse e) (jseg J 128 256) 256) -> u8arr a0segs m A2 (zb8 (e_arr2 e) ARR2_SIZE) ->
    rw_cells a0segs m STRM (STRMB cx ob on dbza dbzfr z (nb + hkin z0 z) p1 p2) ->
    rw_cells a0segs m P (hc_slots E SHE v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 (Z_to_bv 64 (Z.b2z pin)) v112) -> stk a0segs m lo P -> mem_inv a0segs m ->
    u8roW ci_W m nb pl -> acimgW ci_W m sv -> acoW ci_W m ->
    cctx_sh a0segs cx ci_W m -> cimg_sh A0C ci_W m -> shzW a0segs ci_W m STRM (STRM + 80) -> shpW a0segs ci_W m nb (nb + Z.of_nat (length pl)) ->
    (forall e_cb (il : bool) z1 pin1 m' (v8' v16' v24' v64' v72' v80' v88' : word) (t0' t1' t2' a2' a3' a4' a5' a6' a7' s6' t3' t4' t5' t6' : word),
        hc_in znew e z pin pout = (hc_after_cb e_cb il, z1, pin1, pout, false) ->
        cb_pre g e_cb -> CBFACTS e_cb -> hc_rest e e_cb -> HPURE HCXB cx on z0 pl (eg_after_cb cx g e_cb) (hc_after_cb e_cb il) z1 ->
        rw_cells a0segs m' E (EHEAD1 cx g e_cb) -> rw_cells a0segs m' (E + 640) (EHEAD2 cx g e_cb) ->
        u8arr a0segs m' (E + 128) (ovb (e_inUse e_cb) (jseg J 128 256) 256) -> u8arr a0segs m' A2 (zb8 (e_arr2 e_cb) ARR2_SIZE) ->
        rw_cells a0segs m' STRM (STRMB cx ob on dbza dbzfr z1 (nb + hkin z0 z1) p1 p2) ->
        rw_cells a0segs m' P (hc_slots E SHE v0 v8' v16' v24' v32 v40 v48 v64' v72' v80' v88' (Z_to_bv 64 (SHE + 1)) (Z_to_bv 64 (Z.b2z pin1)) (Z_to_bv 64 (SHE + -2147450868))) ->
        stk a0segs m' lo P -> mem_inv a0segs m' -> munch ci_W m m' -> wmono a0segs m m' ->
        evt a0segs Q (MS (CBR il t0' t1' t2' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (Z.b2z pout)) s6' t3' t4' t5' t6') F (Z_to_bv 64 0x88a10) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (INR ra a0 a1 a2 a3 a4 a5 (Z_to_bv 64 (Z.b2z pout)) s6 t4 t5 t6) F (Z_to_bv 64 0x82d64) fc None m (seg_rom a0segs)).
  Proof.
    intros g e z pin pout m v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 v112 ra a0 a1 a2 a3 a4 a5 s6 t4 t5 t6 STI PU EH1 EH2 INU AR2 SM SL ST MI VPL VCM VAC CSH0 ISH0 SHs0 SHp0 K.
    pose proof PU as PU0. destruct PU as (HX & ZI & KNN).
    pose proof (hlB_hci _ _ LAWS _ _ _ _ _ HX) as HI. hci_facts HI. destruct MD as (MD & GA & AIE).
    (* [comment removed for export] *)
    assert (HIN : forall e1 z1 pin1, copy_input (S (Z.to_nat (z_avail_in z))) e z pin = (e1, z1, pin1) ->
              hc_in znew e z pin pout =
              if (e_avail_in_expect e1 =? 0)%Z then (hc_after_cb (hc_flush e1) true, z1, pin1, pout, false)
              else if (NBLOCKMAX <=? e_nblock e1)%Z then (hc_after_cb e1 false, z1, pin1, pout, false)
              else if (z_avail_in z1 =? 0)%Z then (e1, z1, pin1, pout, true) else (e1, z1, pin1, pout, false)).
    { intros e1 z1 pin1 CI. unfold hc_in. replace (Z.to_nat (z_avail_in z) + 1)%nat with (S (Z.to_nat (z_avail_in z))) by lia.
      rewrite CI. pose proof (proj1 (copy_input_modes (S (Z.to_nat (z_avail_in z))) e z pin)) as CM. rewrite CI in CM. cbn [fst] in CM.
      rewrite CM, MD. cbn [Z.eqb Pos.eqb negb andb BZ_M_RUNNING BZ_M_FINISHING].
      unfold hc_after_cb, hc_flush. rewrite (surjective_pairing (compressBlock e1 false znew)).
      rewrite (surjective_pairing (compressBlock (est_set_rl e1 (flush_RL (est_rl e1))) _ znew)).
      rewrite (surjective_pairing (compressBlock (est_set_rl e1 (flush_RL (est_rl e1))) true znew)).
      replace (e_mode (est_set_rl e1 (flush_RL (est_rl e1))) =? BZ_M_FINISHING)%Z with true by (symmetry; hcbn; rewrite CM, MD; reflexivity).
      reflexivity. }
    assert (CI0 : (NBLOCKMAX <= e_nblock e \/ z_avail_in z = 0)%Z -> copy_input (S (Z.to_nat (z_avail_in z))) e z pin = (e, z, pin)).
    { intros HX0. rewrite (copy_input_S_finF _ e z pin MD). bz_params.
      destruct (Z.leb_spec NBLOCKMAX (e_nblock e)); [reflexivity|].
      replace (z_avail_in z =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
    pose proof CSH0 as CSH. cps_destruct CSH as (SHe & SH1 & SH2 & SHF & SHFp). clear SH1 SH2 SHF SHFp.
    pose proof SHs0 as SHs.
    pose proof SEP as SP'; unfold cctx_sep, apart, ESTATE_SIZE in SP'; cbv zeta in SP'; cps_destruct SP' as (_ & AEA2 & _).
    cb_ranges CX. unfold CEILv, apartv, ESTATE_SIZE in *. box_ors.
    pose proof (proj2 AE : saddr E SHE) as AEs.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    pose proof (b2z_range pin) as BI. pose proof (b2z_range pout) as BP.
    pose proof (munch_refl ci_W m) as MU. pose proof (wmono_refl a0segs m) as WM. unfold A0_b2c_hcC.ci_W in MU, SHe, SHs.
    (* [comment removed for export] *)
    assert (TAILK : forall e1 z1 (itb : bool) (mj : amem) (w8 w16 w24 w64 w72 w80 w88 x10 x11 x12 x14 x15 x22 x29 : word),
      copy_input (S (Z.to_nat (z_avail_in z))) e z pin = (e1, z1, pin || itb) -> e_state e1 = BZ_S_INPUT ->
      (NBLOCKMAX <= e_nblock e1 \/ z_avail_in z1 = 0)%Z -> HPURE HCXB cx on z0 pl g e1 z1 ->
      rw_cells a0segs mj E (EHEAD1 cx g e1) -> rw_cells a0segs mj (E + 640) (EHEAD2 cx g e1) ->
      u8arr a0segs mj (E + 128) (ovb (e_inUse e1) (jseg J 128 256) 256) -> u8arr a0segs mj A2 (zb8 (e_arr2 e1) ARR2_SIZE) ->
      rw_cells a0segs mj STRM (STRMB cx ob on dbza dbzfr z1 (nb + hkin z0 z1) p1 p2) ->
      rw_cells a0segs mj P (hc_slots E SHE v0 w8 w16 w24 v32 v40 v48 w64 w72 w80 w88 (Z_to_bv 64 (SHE + 1)) (Z_to_bv 64 (Z.b2z pin)) (Z_to_bv 64 (SHE + -2147450868))) ->
      stk a0segs mj lo P -> mem_inv a0segs mj -> munch ci_W m mj -> wmono a0segs m mj ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 (SHE + -2147450869)) (Z_to_bv 64 P) gp tp (Z_to_bv 64 (E + 16)) (Z_to_bv 64 (E + 8)) (Z_to_bv 64 2) (Z_to_bv 64 E) cSB
                            x10 x11 x12 (Z_to_bv 64 (Z.b2z itb)) x14 x15 (Z_to_bv 64 1) (Z_to_bv 64 (E + 108))
                            (Z_to_bv 64 (Z.b2z pout)) (Z_to_bv 64 (E + 120)) (Z_to_bv 64 (SHE + 15)) (Z_to_bv 64 (E + 92)) x22 (Z_to_bv 64 (E + 116)) (Z_to_bv 64 (E + 96)) (Z_to_bv 64 SHE)
                            (Z_to_bv 64 (E + 80)) (Z_to_bv 64 (SHE + 14)) (Z_to_bv 64 (E + 648)) x29 (Z_to_bv 64 (SHE + 13)) (Z_to_bv 64 (SHE + 14)))
                       F (Z_to_bv 64 0x83638) fc None mj (seg_rom a0segs))).
    { clear EH1 EH2 INU AR2 SM SL ST MI MU WM.
      intros e1 z1 itb mj w8 w16 w24 w64 w72 w80 w88 x10 x11 x12 x14 x15 x22 x29 CI ST1 EX1 PU1 EH1 EH2 INU AR2 SM SL ST MI MU WM.
      pose proof (HIN e1 z1 (pin || itb) CI) as HIN1. destruct PU1 as (HX1 & ZI1 & KNN1).
      assert (SF : sub_fp hfin_W ci_W) by (unfold hfin_W, A0_b2c_hcC.ci_W; a_sub_fp).
      eapply (A0_hc_fin g e1 z1 pin itb mj); [ exact ST1 | exact EX1 | exact HX1 | exact EH1 | exact EH2 | exact INU | exact AR2 | exact SL | exact ST | exact MI
        | exact (acimgW_sub _ _ _ _ _ VCM MU SF) | exact (acoW_sub _ _ _ _ VAC MU SF) | exact (cctx_sh_sub a0segs cx _ _ _ _ CSH0 MU SF)
        | unfold cimg_sh in *; exact (shzW_sub a0segs _ _ _ _ _ _ _ _ ISH0 MU SF (Z.le_refl _) (Z.le_refl _)) |].
      intros e_cb il m' t0' t1' t2' a2' a3' a4' a5' a6' a7' s6' t3' t4' t5' t6' DJ PRE FACTS HX' EH1' EH2' INU' AR2' SL' ST' MI' MU' WM'.
      unfold STRMB in SM. clear EH1 EH2 INU AR2 SL ST MI. unfold hfin_W in MU'. unfold A0_b2c_hcC.ci_W in MU.
      assert (MUh : munch ci_W mj m') by (eapply munch_weaken; [exact SF| unfold hfin_W; exact MU']).
      transport_after_call a0segs mj m' MU' WM'.
      eapply (K e_cb il z1 (pin || itb) m'); [ | exact PRE | exact FACTS
        | (* [comment removed for export] *)
          pose proof (copy_input_rest (S (Z.to_nat (z_avail_in z))) e z pin) as RR; rewrite CI in RR; cbn [fst] in RR;
          destruct DJ as [(_ & _ & ->)|(_ & _ & _ & ->)]; [exact (hc_rest_trans _ _ _ RR (hc_flush_rest e1))| exact RR]
        | unfold HPURE; split; [exact HX'| split; [exact ZI1| exact KNN1]]
        | exact EH1' | exact EH2' | exact INU' | exact AR2' | unfold STRMB; exact SM | exact SL' | exact ST' | exact MI' | unfold A0_b2c_hcC.ci_W; exact MU | exact WM ].
      rewrite HIN1. destruct DJ as [(-> & E0 & ->) | (-> & NE0 & NB' & ->)].
      - rewrite E0. reflexivity.
      - replace (e_avail_in_expect e1 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact NE0).
        replace (NBLOCKMAX <=? e_nblock e1)%Z with true by (symmetry; apply Z.leb_le; exact NB'). reflexivity. }
    idtac "TAILK done".
    unfold EHEAD1 in EH1. rewrite GA, <- ESTRM, MD in EH1. unfold EHEAD2 in EH2. unfold STRMB in SM. unfold hc_slots in SL.
    (* [comment removed for export] *)
    arun_to 0x82d6c%Z. sh_norm.
    (* [comment removed for export] *)
    arun_to 0x82db0%Z. sh_norm.
    (* [comment removed for export] *)
    arun. if_cases KN; zify_cond_z KN.
    { (* [comment removed for export] *)
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (TAILK e z false mm _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [ st_eq | rewrite Bool.orb_false_r; apply CI0; bz_params; lia | exact STI | bz_params; lia | exact PU0
        | unfold EHEAD1; rewrite GA, <- ESTRM, MD; exact EH1 | unfold EHEAD2; exact EH2 | exact INU | exact AR2 | unfold STRMB; exact SM | unfold hc_slots; exact SL
        | exact ST | exact MI | unfold A0_b2c_hcC.ci_W; exact MU | exact WM ]. }
    (* [comment removed for export] *)
    arun. if_cases KA; zify_cond_z KA.
    { (* [comment removed for export] *)
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (TAILK e z false mm _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [ st_eq | rewrite Bool.orb_false_r; apply CI0; lia | exact STI | lia | exact PU0
        | unfold EHEAD1; rewrite GA, <- ESTRM, MD; exact EH1 | unfold EHEAD2; exact EH2 | exact INU | exact AR2 | unfold STRMB; exact SM | unfold hc_slots; exact SL
        | exact ST | exact MI | unfold A0_b2c_hcC.ci_W; exact MU | exact WM ]. }
    (* [comment removed for export] *)
    arun_to 0x831f0%Z. sh_norm.
    (* [comment removed for export] *)
    arun. if_cases KE; zify_cond_z KE; [exfalso; clear - KE KA AIE; lia|].
    assert (CT : copy_input (S (Z.to_nat (z_avail_in z))) e z pin = copy_input (S (Z.to_nat (z_avail_in z))) e z true).
    { rewrite !(copy_input_S_finF _ e z _ MD). bz_params.
      replace (NBLOCKMAX <=? e_nblock e)%Z with false by (symmetry; apply Z.leb_gt; lia).
      replace (z_avail_in z =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
      replace (e_avail_in_expect e =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (ci_loopL (S (Z.to_nat (z_avail_in z))) g e z m mm v0 v8 v16 v32 v40 v48 (Z_to_bv 64 (Z.b2z pin))) end;
      [ st_eq | lia | exact STI | bz_params; lia | lia | exact PU0
      | unfold EHEAD1; rewrite GA, <- ESTRM, MD; exact EH1 | unfold EHEAD2; exact EH2 | exact INU | exact AR2 | unfold STRMB; exact SM
      | unfold hc_slotsL, hc_slots; exact SL | exact ST | exact MI | unfold A0_b2c_hcC.ci_W; exact MU | exact WM
      | exact VPL | exact VCM | exact VAC | exact CSH0 | exact ISH0 | exact SHs0 | exact SHp0 | ].
    intros e' z' m' v8' v16' a0' a1' a2' a4' t4' CO' ST' EX' PU' EH1' EH2' INU' AR2' SM' SL' STK' MI' MU' WM'.
    enter_with (TAILK e' z' true m' _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [ st_eq | rewrite CT, Bool.orb_true_r; exact CO' | exact ST' | exact EX' | exact PU'
      | exact EH1' | exact EH2' | exact INU' | exact AR2' | exact SM' | unfold hc_slotsL in SL'; exact SL' | exact STK' | exact MI' | exact MU' | exact WM' ].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

End A0HCE.

End ACeilS1.
