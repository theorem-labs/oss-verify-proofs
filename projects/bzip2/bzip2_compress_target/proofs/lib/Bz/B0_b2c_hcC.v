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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require B0_cmp_ap B0_b2c_hcB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpHmKit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit.
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma low32_crc_stepB : forall crc t, (0 <= crc < 4294967296)%Z -> (0 <= t < 4294967296)%Z ->
  (bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (sx32 (Z_to_bv 64 t))) (crc * 256))) mod 4294967296 = Z.lxor ((Z.shiftl crc 8) mod 4294967296) t)%Z.
Proof.
  intros crc t Hc Ht. rewrite Z.lxor_comm.
  replace (crc * 256)%Z with ((bv_unsigned (Z_to_bv 64 crc) * 256) mod 18446744073709551616)%Z by (rewrite (unsigned_lit crc) by lia; apply Z.mod_small; lia).
  apply (low32_crc_step' (Z_to_bv 64 crc) crc t); [| exact Ht]. rewrite (unsigned_lit crc) by lia. apply Z.mod_small. lia.
Qed.

Section B0HCC.
  Variables (cx : cctx) (Q : machine_state -> Prop).
  Variables (HCXB : cctx -> Z -> eg -> est -> zstrm -> Prop) (CBFACTS : est -> Prop).
  Variables (SHE SHS : Z) (ob on dbza dbzfr : Z) (p1 p2 sv : word) (P STRM lo : Z) (z0 : zstrm) (nb : Z) (pl : list byte).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Notation E := (c_E cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation cSB := (Z_to_bv 64 2147450880).
  (* [comment removed for export] *)
  Hypothesis ESTRM : STRM = (c_bz cx + BZF_STRM)%Z.
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis IMG : cctx_img (aci_c B0C) cx. Hypothesis LAWS : hc_lawsB HCXB CBFACTS.
  Hypothesis AE : sanchor E SHE. Hypothesis AS : sanchor STRM SHS.
  Hypothesis SLO : (0x62b000 <= STRM)%Z. Hypothesis SHI : (STRM + 80 <= CEILv)%Z.
  Hypothesis LLO : (CEILv <= lo)%Z. Hypothesis PLO : (lo + 16 <= P)%Z. Hypothesis PHI : (P + 288 <= 18446744073709551616)%Z.
  Hypothesis SES : apartv E ESTATE_SIZE STRM 80. Hypothesis S2S : apartv A2 ARR2_SIZE STRM 80.

  (* [comment removed for export] *)
  Definition hap_W : list (Z * Z) := [(E + 108, E + 112); (E + 648, E + 652); (E + 128, E + 384); (A2, A2 + ARR2_SIZE); (P - 16, P)]%Z.

  (* [comment removed for export] *)
  Lemma B0_ap_call : forall g e (m : amem)
      (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    (0 <= e_state_in_ch e < 256)%Z -> (1 <= e_state_in_len e <= 255)%Z -> (0 <= e_blockCRC e < 4294967296)%Z ->
    (0 <= e_nblock e)%Z -> (e_nblock e + 5 <= ARR2_SIZE)%Z -> zdefr (e_inUse e) 0 256 -> zbok (e_arr2 e) ->
    rw_cells b0segs m E (EHEAD1 cx g e) -> rw_cells b0segs m (E + 640) (EHEAD2 cx g e) ->
    u8arr b0segs m (E + 128) (ovb (e_inUse e) (jseg J 128 256) 256) -> u8arr b0segs m A2 (zb8 (e_arr2 e) ARR2_SIZE) ->
    acimg_mem B0C m sv -> mem_inv b0segs m -> stk b0segs m lo P ->
    aconsts B0C m -> cctx_sh b0segs cx hap_W m -> cimg_sh B0C hap_W m ->
    (forall m' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        let e' := est_set_rl e (add_pair_to_block (est_rl e)) in
        rw_cells b0segs m' E (EHEAD1 cx g e') -> rw_cells b0segs m' (E + 640) (EHEAD2 cx g e') ->
        u8arr b0segs m' (E + 128) (ovb (e_inUse e') (jseg J 128 256) 256) -> u8arr b0segs m' A2 (zb8 (e_arr2 e') ARR2_SIZE) ->
        mem_inv b0segs m' -> stk b0segs m' lo P -> munch hap_W m m' -> wmono b0segs m m' ->
        evt b0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x88fa4) fc None m (seg_rom b0segs)).
  Proof.
    intros g e m ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 CH LEN CRCR NB0 NB5 DEFI BOK EH1 EH2 INU AR2 CM MI ST AC CSH ISH K.
    cb_ranges CX. unfold CEILv in *.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    assert (HP : (0 <= P < 18446744073709551616)%Z) by lia.
    pose proof (B0_cmp_ap.B0_add_pair ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cx g e lo sv) as AP.
    cbv zeta in AP. cbn [aci_segs aci_c ci_segs B0C ci_add_pair] in AP. unfold add_pair_post in AP.
    rewrite (unsigned_lit P) in AP by lia.
    eapply evt_cut.
    { eapply AP; [reflexivity| exact EH1| exact EH2| exact INU| exact AR2| exact CM| exact MI| exact ST| lia| unfold CEIL; lia| exact CX| exact SEP| exact IMG
        | exact CH| exact LEN| exact CRCR| exact NB0| exact NB5| exact DEFI| exact BOK| exact AC| |].
      - eapply (cctx_sh_sub b0segs cx hap_W _ m m CSH (munch_refl _ _)).
        unfold add_pair_W, hap_W. cbn [app]. a_sub_fp.
      - unfold cimg_sh in *. cbn [aci_segs aci_c ci_segs B0C ci_crc] in *.
        eapply (shzW_sub b0segs hap_W _ m m _ _ _ _ ISH (munch_refl _ _)); [| lia| lia].
        unfold add_pair_W, hap_W. cbn [app]. a_sub_fp. }
    clear EH1 EH2 INU AR2 MI ST AP.
    intros ms' PO; destruct_exs PO. destruct PO as [EQ [MUc [WMc [MI2 [ST2 PO]]]]]; subst ms'. cbv zeta in PO. destruct PO as [EH1 [EH2 [INU AR2]]].
    lazymatch type of MUc with munch _ m ?m' =>
      assert (MU' : munch hap_W m m');
      [ eapply munch_weaken; [| exact MUc]; unfold add_pair_W, hap_W; cbn [app]; a_sub_fp | ] end.
    eapply K; [exact EH1| exact EH2| exact INU| exact AR2| exact MI2| exact ST2| exact MU'| exact WMc].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis PAYR : pl <> [] -> (0 < nb /\ nb + Z.of_nat (length pl) <= CEILv)%Z.

  (* [comment removed for export] *)
  Definition ci_W : list (Z * Z) := [(E, E + 384); (E + 648, E + 652); (A2, A2 + ARR2_SIZE); (STRM, STRM + 20); (P - 16, P); (P + 64, P + 96)]%Z.

  (* [comment removed for export] *)
  Notation CIR s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s7 t6 :=
    (mkR (Z_to_bv 64 (SHE + 14)) (Z_to_bv 64 P) gp tp (Z_to_bv 64 (E + 92)) (Z_to_bv 64 (E + 96)) (Z_to_bv 64 (E + 108)) (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7
         s2 s3 (Z_to_bv 64 2) (Z_to_bv 64 (E + 120)) (Z_to_bv 64 1) s7 (Z_to_bv 64 (E + 116)) (Z_to_bv 64 SHE) (Z_to_bv 64 (E + 80)) cSB
         (Z_to_bv 64 (SHE + 13)) (Z_to_bv 64 (E + 16)) (Z_to_bv 64 (E + 112)) t6).

  Ltac hcbn := cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_outpos est_set_modes est_set_rl est_rl rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len
         z_in z_avail_in z_outr z_avail_out z_tin_lo z_tin_hi z_tout_lo z_tout_hi fst snd].
  Ltac hcbn_in H := cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_outpos est_set_modes est_set_rl est_rl rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len
         z_in z_avail_in z_outr z_avail_out z_tin_lo z_tin_hi z_tout_lo z_tout_hi fst snd] in H.

  Lemma B0_ci_loop : forall (fuel : nat) g e z (p : bool) (me m : amem) (v64 v72 : word)
      (s1 a0 a1 a4 a5 a6 a7 s2 s3 s7 t6 : word),
    (Z.of_nat fuel > z_avail_in z)%Z -> e_state e = BZ_S_INPUT -> (e_nblock e < NBLOCKMAX)%Z ->
    HPURE HCXB cx on z0 pl g e z ->
    rw_cells b0segs m E (EHEAD1 cx g e) -> rw_cells b0segs m (E + 640) (EHEAD2 cx g e) ->
    u8arr b0segs m (E + 128) (ovb (e_inUse e) (jseg J 128 256) 256) -> u8arr b0segs m A2 (zb8 (e_arr2 e) ARR2_SIZE) ->
    rw_cells b0segs m STRM (STRMB cx ob on dbza dbzfr z (nb + hkin z0 z) p1 p2) ->
    rw_cells b0segs m P (hc_slotsL E SHE v64 v72) -> stk b0segs m lo P ->
    mem_inv b0segs m -> munch ci_W me m -> wmono b0segs me m ->
    u8roW ci_W me nb pl -> acimgW ci_W me sv -> acoW ci_W me ->
    cctx_sh b0segs cx ci_W me -> cimg_sh B0C ci_W me -> shzW b0segs ci_W me STRM (STRM + 80) -> shpW b0segs ci_W me nb (nb + Z.of_nat (length pl)) ->
    (forall e' z' (p' : bool) m' (s1' a0' a1' a2' a4' a5' a6' a7' s2' s3' s7' t6' : word),
        copy_input fuel e z p = (e', z', p') -> e_state e' = BZ_S_INPUT ->
        (NBLOCKMAX <= e_nblock e' \/ z_avail_in z' = 0)%Z ->
        HPURE HCXB cx on z0 pl g e' z' ->
        rw_cells b0segs m' E (EHEAD1 cx g e') -> rw_cells b0segs m' (E + 640) (EHEAD2 cx g e') ->
        u8arr b0segs m' (E + 128) (ovb (e_inUse e') (jseg J 128 256) 256) -> u8arr b0segs m' A2 (zb8 (e_arr2 e') ARR2_SIZE) ->
        rw_cells b0segs m' STRM (STRMB cx ob on dbza dbzfr z' (nb + hkin z0 z') p1 p2) ->
        rw_cells b0segs m' P (hc_slotsL E SHE v64 v72) -> stk b0segs m' lo P ->
        mem_inv b0segs m' -> munch ci_W me m' -> wmono b0segs me m' ->
        evt b0segs Q (MS (CIR s1' a0' a1' a2' (Z_to_bv 64 (Z.b2z p')) a4' a5' a6' a7' s2' s3' s7' t6') F (Z_to_bv 64 0x83240) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (CIR s1 a0 a1 (Z_to_bv 64 (e_nblock e)) (Z_to_bv 64 (Z.b2z p)) a4 a5 a6 a7 s2 s3 s7 t6) F (Z_to_bv 64 0x82df0) fc None m (seg_rom b0segs)).
  Proof.
    induction fuel as [|fuel IH]; intros g e z p me m v64 v72 s1 a0 a1 a4 a5 a6 a7 s2 s3 s7 t6 FUEL STI NBM PU EH1 EH2 INU AR2 SM SL ST MI MU WM VPL VCM VAC CSH0 ISH0 SHs0 SHp0 K;
    destruct PU as (HX & ZI & KNN); pose proof (hlB_hci _ _ LAWS _ _ _ _ _ HX) as HI;
    pose proof (HCIB_est_ok _ _ _ _ _ HI) as EOK; pose proof (HCIB_avail_in _ _ _ _ _ HI) as (AIL & AIR); pose proof (HCIB_rl _ _ _ _ _ HI) as RLD;
    pose proof (HCIB_inUse _ _ _ _ _ HI) as DEFI; cps_pose (HCIB_mode _ _ _ _ _ HI) as (MF & GA & AIE);
    unfold est_ok in EOK; cps_destruct EOK as (BOK1 & BOK2 & FTR & NBR & NZ0 & POSR & MODES & STATES & CHR & LENR & CRCR & CCR & BNO);
    [exfalso; lia|].
    pose proof CSH0 as CSH. cps_destruct CSH as (SHe & SH1 & SH2 & SHF & SHFp). clear SH1 SHF SHFp.
    pose proof ISH0 as ISH. pose proof SHs0 as SHs. pose proof SHp0 as SHp.
    pose proof SEP as SP'; unfold cctx_sep, apart, ESTATE_SIZE in SP'; cbv zeta in SP'; cps_destruct SP' as (_ & AEA2 & _).
    cb_ranges CX. unfold CEILv, apartv, ESTATE_SIZE in *. box_ors. bz_params.
    pose proof (proj2 AE : saddr E SHE) as AEs. pose proof (proj1 AE) as EM8. pose proof (proj1 AS) as SM8.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    pose proof (b2z_range p) as BPP.
    unfold cimg_sh in ISH. cbn [aci_segs aci_c ci_segs B0C ci_crc] in ISH.
    unfold ci_W in MU, SHe, SH2, SHs, SHp, ISH.
    pose proof EH1 as EH1f. pose proof SM as SMf. pose proof SL as SLf.
    unfold EHEAD1 in EH1. rewrite GA, <- ESTRM, AIE in EH1. unfold EHEAD2 in EH2. unfold STRMB in SM. unfold hc_slotsL, hc_slots in SL.
    (* [comment removed for export] *)
    brun. try rewrite (sx32_of_Z (z_avail_in z)) by lia.
    if_cases KA; zify_cond_z KA.
    { eapply (K e z p m); [ rewrite (copy_input_S_finF fuel e z p MF); bz_params; replace (NBLOCKMAX <=? e_nblock e)%Z with false by (symmetry; apply Z.leb_gt; lia);
                            replace (z_avail_in z =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia); reflexivity
        | exact STI | right; lia | unfold HPURE; split; [exact HX| split; [exact ZI| exact KNN]]
        | exact EH1f | exact EH2 | exact INU | exact AR2 | exact SMf | exact SLf | exact ST | exact MI | unfold ci_W; exact MU | exact WM ]. }
    (* [comment removed for export] *)
    brun. try rewrite (sx32_of_Z (z_avail_in z)) by lia. sh_norm.
    if_cases KE; zify_cond_z KE; [exfalso; lia|].
    clear EH1f SMf SLf.
    (* [comment removed for export] *)
    destruct (skipn (Z.to_nat (hkin z0 z)) pl) as [|b plrest] eqn:SK.
    { exfalso. rewrite ZI in AIL. cbn [map length] in AIL. lia. }
    assert (NTH : nth_error pl (Z.to_nat (hkin z0 z)) = Some b).
    { rewrite <- (Nat.add_0_r (Z.to_nat (hkin z0 z))), <- nth_error_skipn, SK. reflexivity. }
    pose proof (nth_error_lt _ _ _ NTH) as KLT.
    set (ch := bv_unsigned b). assert (Hch : (0 <= ch < 256)%Z) by (subst ch; apply byte_range).
    assert (ZI' : z_in z = ch :: map bv_unsigned plrest) by (rewrite ZI; reflexivity).
    pose proof (ci_stepF_eq e z ch (map bv_unsigned plrest) ZI') as CIE.
    assert (CIS : copy_input (S fuel) e z p = copy_input fuel (fst (ci_stepF e z)) (snd (ci_stepF e z)) true).
    { rewrite (copy_input_S_finF fuel e z p MF). bz_params. replace (NBLOCKMAX <=? e_nblock e)%Z with false by (symmetry; apply Z.leb_gt; lia).
      replace (z_avail_in z =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
      replace (e_avail_in_expect e =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
    pose proof (hlB_ci _ _ LAWS cx on g e z HX STI ltac:(bz_params; lia) ltac:(lia)) as HX'.
    rewrite CIE in CIS, HX'. cbv zeta in CIS. cbv zeta in HX'. cbn [fst snd] in CIS, HX'. clear CIE.
    assert (ZIn : map bv_unsigned plrest = map bv_unsigned (skipn (Z.to_nat (hkin z0 z + 1)) pl)).
    { f_equal. replace (Z.to_nat (hkin z0 z + 1)) with (1 + Z.to_nat (hkin z0 z))%nat by lia. rewrite <- skipn_skipn, SK. reflexivity. }
    assert (AI1 : (1 <= z_avail_in z < 2147483648)%Z) by lia.
    assert (NE : pl <> []) by (intros ->; rewrite skipn_nil in SK; discriminate SK).
    destruct (PAYR NE) as (NB0 & NB1).
    (* [comment removed for export] *)
    assert (ADV : forall (r' : rlst) (mj : amem) (x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x31 : word),
      add_char_to_block (est_rl e) ch = r' ->
      rw_cells b0segs mj E (EHEAD1 cx g (est_set_rl e r')) -> rw_cells b0segs mj (E + 640) (EHEAD2 cx g (est_set_rl e r')) ->
      u8arr b0segs mj (E + 128) (ovb (rl_inUse r') (jseg J 128 256) 256) -> u8arr b0segs mj A2 (zb8 (rl_block r') ARR2_SIZE) ->
      rw_cells b0segs mj STRM (STRMB cx ob on dbza dbzfr z (nb + hkin z0 z) p1 p2) ->
      rw_cells b0segs mj P (hc_slotsL E SHE v64 v72) -> stk b0segs mj lo P ->
      mem_inv b0segs mj -> munch ci_W me mj -> wmono b0segs me mj ->
      evt b0segs Q (MS (CIR x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (SHE + 2)) x23 x31) F (Z_to_bv 64 0x83014) fc None mj (seg_rom b0segs))).
    { clear EH1 EH2 INU AR2 SM SL ST MI MU WM.
      intros r' mj x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x31 ACB EH1 EH2 INU AR2 SM SL ST MI MU WM.
      rewrite ACB in CIS, HX'. hcbn_in CIS. hcbn_in HX'. unfold ci_W in MU. unfold EHEAD2 in EH2.
      pose proof (hlB_hci _ _ LAWS _ _ _ _ _ HX') as HI'. pose proof (HCIB_est_ok _ _ _ _ _ HI') as EOK'.
      unfold est_ok in EOK'. hcbn_in EOK'. destruct EOK' as (_ & _ & _ & NBR' & _).
      eapply (B0_b2c_hcB.B0_ci_adv cx Q SHE SHS ob on dbza dbzfr p1 p2 P STRM gp tp F fc ESTRM CX AE AS SLO SHI SES g (est_set_rl e r') z (map bv_unsigned plrest) (nb + hkin z0 z)%Z mj mj);
        [ exact AI1 | hcbn; exact AIE | exact GA | hcbn; bz_params; lia | lia | lia | exact EH1 | exact SM | exact MI | apply munch_refl | apply wmono_refl
        | eapply (shzW_sub b0segs _ _ me mj _ _ _ _ SHe); [exact MU| unfold B0_b2c_hcB.ci_adv_W; a_sub_fp| lia| unfold ESTATE_SIZE; lia]
        | eapply (shzW_sub b0segs _ _ me mj _ _ _ _ SHs); [exact MU| unfold B0_b2c_hcB.ci_adv_W; a_sub_fp| lia| lia]
        | |].
      - (* [comment removed for export] *)
        intros m' y10 y11 NB' EH1' SM' MI' MU' WM'. hcbn_in NB'.
        unfold B0_b2c_hcB.ci_adv_W in MU'.
        clear EH1 SM MI. transport_after_call b0segs mj m' MU' WM'.
        eapply (K (est_set_modes (est_set_rl e r') (e_mode e) (e_state e) (e_avail_in_expect e - 1)) (z_adv z (map bv_unsigned plrest)) true m');
          [ rewrite CIS; destruct fuel as [|fuel']; [reflexivity|];
            rewrite copy_input_S_finF by (hcbn; exact MF); hcbn; bz_params;
            match goal with |- context [(NBLOCKMAX <=? ?x)%Z] => replace (NBLOCKMAX <=? x)%Z with true by (symmetry; apply Z.leb_le; lia) end; reflexivity
          | hcbn; exact STI | hcbn; left; exact NB'
          | unfold HPURE; split; [exact HX'|]; unfold hkin in *; unfold z_adv; hcbn; rewrite ZIn; split; [f_equal; f_equal; f_equal; lia| lia]
          | hcbn_in EH1'; exact EH1' | unfold EHEAD2; exact EH2 | hcbn; exact INU | hcbn; exact AR2
          | unfold STRMB, hkin, z_adv in *; hcbn; hcbn_in SM'; cells_eq_by SM'
          | exact SL | exact ST | exact MI' | unfold ci_W; exact MU | exact WM ].
      - (* [comment removed for export] *)
        intros m' y10 y11 NB' EH1' SM' MI' MU' WM'. hcbn_in NB'.
        unfold B0_b2c_hcB.ci_adv_W in MU'.
        clear EH1 SM MI. transport_after_call b0segs mj m' MU' WM'.
        enter_with (IH g (est_set_modes (est_set_rl e r') (e_mode e) (e_state e) (e_avail_in_expect e - 1)) (z_adv z (map bv_unsigned plrest)) true me m' v64 v72);
          [ hcbn; st_eq | unfold z_adv; hcbn; lia | hcbn; exact STI | hcbn; exact NB'
          | unfold HPURE; split; [exact HX'|]; unfold hkin in *; unfold z_adv; hcbn; rewrite ZIn; split; [f_equal; f_equal; f_equal; lia| lia]
          | hcbn_in EH1'; exact EH1' | unfold EHEAD2; exact EH2 | hcbn; exact INU | hcbn; exact AR2
          | unfold STRMB, hkin, z_adv in *; hcbn; hcbn_in SM'; cells_eq_by SM'
          | exact SL | exact ST | exact MI' | unfold ci_W; exact MU | exact WM | exact VPL | exact VCM | exact VAC | exact CSH0 | exact ISH0 | exact SHs0 | exact SHp0
          | intros e'' z'' p'' m'' s1'' a0'' a1'' a2'' a4'' a5'' a6'' a7'' s2'' s3'' s7'' t6'' CO'' ST'' EX'' PU'' EH1'' EH2'' INU'' AR2'' SM'' SL'' STK'' MI'' MU'' WM'';
            eapply K; [rewrite CIS; exact CO''| exact ST'' | exact EX'' | exact PU'' | exact EH1'' | exact EH2'' | exact INU'' | exact AR2'' | exact SM'' | exact SL'' | exact STK'' | exact MI'' | exact MU'' | exact WM''] ]. }
    idtac "ADV done".
    (* [comment removed for export] *)
    assert (SETCH : forall (r1 : rlst) (mj : amem) (x10 x11 x12 x13 x14 x15 x16 x17 x31 : word),
      add_char_to_block (est_rl e) ch = RL (rl_nblock r1) (rl_block r1) (rl_inUse r1) (rl_crc r1) ch 1 ->
      rw_cells b0segs mj E (EHEAD1 cx g (est_set_rl e r1)) -> rw_cells b0segs mj (E + 640) (EHEAD2 cx g (est_set_rl e r1)) ->
      u8arr b0segs mj (E + 128) (ovb (rl_inUse r1) (jseg J 128 256) 256) -> u8arr b0segs mj A2 (zb8 (rl_block r1) ARR2_SIZE) ->
      rw_cells b0segs mj STRM (STRMB cx ob on dbza dbzfr z (nb + hkin z0 z) p1 p2) ->
      rw_cells b0segs mj P (hc_slotsL E SHE v64 v72) -> stk b0segs mj lo P ->
      mem_inv b0segs mj -> munch ci_W me mj -> wmono b0segs me mj ->
      evt b0segs Q (MS (CIR (Z_to_bv 64 (SHE + 12)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (SHE + 11)) (Z_to_bv 64 (SHE + 2)) (Z_to_bv 64 ch) x31)
                       F (Z_to_bv 64 0x82ffc) fc None mj (seg_rom b0segs))).
    { clear EH1 EH2 INU AR2 SM SL ST MI MU WM. intros r1 mj x10 x11 x12 x13 x14 x15 x16 x17 x31 ACB EH1 EH2 INU AR2 SM SL ST MI MU WM.
      unfold ci_W in MU. unfold EHEAD1 in EH1. hcbn_in EH1. rewrite GA, <- ESTRM, AIE in EH1. unfold EHEAD2 in EH2. hcbn_in EH2. unfold STRMB in SM. unfold hc_slotsL, hc_slots in SL.
      (* [comment removed for export] *)
      brun_to 0x83014%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (ADV (RL (rl_nblock r1) (rl_block r1) (rl_inUse r1) (rl_crc r1) ch 1) mm _ _ _ _ _ _ _ _ _ _ _ _) end;
        [ st_eq | exact ACB | unfold EHEAD1; hcbn; rewrite GA, <- ESTRM, AIE; first [exact EH1 | cells_eq_by EH1] | unfold EHEAD2; hcbn; exact EH2 | hcbn; exact INU | hcbn; exact AR2
        | unfold STRMB; exact SM | unfold hc_slotsL, hc_slots; exact SL | exact ST | exact MI | unfold ci_W; exact MU | exact WM ]. }
    idtac "SETCH done".
    (* [comment removed for export] *)
    brun_to 0x82e5c%Z.
    ack_rd (nb + hkin z0 z)%Z 1%Z.
    ack_merge.
    (* [comment removed for export] *)
    brun.
    pose proof (u8ro_read b0segs m nb pl (hkin z0 z) b _ (VPL m MU) NTH ltac:(lia) eq_refl) as RD.
    wstep. clear RD. cbv beta. fold ch.
    (* [comment removed for export] *)
    brun. try rewrite (sx32_of_Z (e_state_in_ch e)) by lia. try rewrite (sx32_of_Z (e_state_in_len e)) by lia. sh_norm.
    (* [comment removed for export] *)
    assert (APC : forall (x10 x11 x12 x13 x14 x15 x16 : word),
      (e_state_in_ch e < 256)%Z ->
      add_char_to_block (est_rl e) ch = (let r1 := add_pair_to_block (est_rl e) in RL (rl_nblock r1) (rl_block r1) (rl_inUse r1) (rl_crc r1) ch 1) ->
      evt b0segs Q (MS (CIR (Z_to_bv 64 (SHE + 12)) x10 x11 x12 x13 x14 x15 x16 a7 (Z_to_bv 64 (SHE + 11)) (Z_to_bv 64 (SHE + 2)) (Z_to_bv 64 ch) t6)
                       F (Z_to_bv 64 0x82fd8) fc None m (seg_rom b0segs))).
    { intros x10 x11 x12 x13 x14 x15 x16 IC ACB. cbv zeta in ACB.
      assert (LEN1 : (1 <= e_state_in_len e)%Z) by (clear - RLD IC; unfold id in RLD; lia).
      (* [comment removed for export] *)
      brun_to 0x88fa4%Z.
      pose proof (VCM m MU) as CM.
      eapply (B0_ap_call g e m);
        [ lia | lia | exact CRCR | lia | bz_params; lia | exact DEFI | exact BOK2
        | unfold EHEAD1; rewrite GA, <- ESTRM, AIE; exact EH1 | unfold EHEAD2; exact EH2 | exact INU | exact AR2 | exact CM | exact MI | exact ST
        | exact (VAC m MU)
        | eapply (cctx_sh_sub b0segs cx ci_W hap_W me m CSH0 MU); unfold ci_W, hap_W; a_sub_fp
        | unfold cimg_sh in *; eapply (shzW_sub b0segs ci_W hap_W me m _ _ _ _ ISH0 MU); [unfold ci_W, hap_W; a_sub_fp| lia| lia]
        | ].
      intros m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' e' EH1' EH2' INU' AR2' MI' ST' MU' WM'. subst e'.
      lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
      clear EH1 EH2 INU AR2 MI ST CM. unfold hap_W in MU'. transport_after_call b0segs m m' MU' WM'.
      (* [comment removed for export] *)
      brun_to 0x82ffc%Z.
      enter_with (SETCH (add_pair_to_block (est_rl e)) m' _ _ _ _ _ _ _ _ _);
        [ st_eq | exact ACB | exact EH1' | exact EH2' | hcbn_in INU'; exact INU' | hcbn_in AR2'; exact AR2'
        | unfold STRMB; exact SM | unfold hc_slotsL, hc_slots; exact SL | exact ST' | exact MI' | unfold ci_W; exact MU | exact WM ].
      all: lazymatch goal with |- ?G => idtac "LEFT:" G end. }
    idtac "APC done".
    if_cases Kne; zify_cond_z Kne.
    - (* [comment removed for export] *)
      brun. if_cases K1; zify_cond_z K1.
      + (* [comment removed for export] *)
        brun. if_cases K256; zify_cond_z K256.
        * (* [comment removed for export] *)
          enter_with (SETCH (est_rl e) m _ _ _ _ _ _ _ _ _);
            [ st_eq | hcbn; apply acb_gen256; hcbn; lia
            | unfold EHEAD1; hcbn; rewrite GA, <- ESTRM, AIE; exact EH1 | unfold EHEAD2; hcbn; exact EH2 | hcbn; exact INU | hcbn; exact AR2
            | unfold STRMB; exact SM | unfold hc_slotsL, hc_slots; exact SL | exact ST | exact MI | unfold ci_W; exact MU | exact WM ].
        * (* [comment removed for export] *)
          enter_with (APC _ _ _ _ _ _ _); [ st_eq | lia | apply acb_gen; hcbn; lia ].
      + (* [comment removed for export] *)
        assert (IC : (e_state_in_ch e < 256)%Z) by (clear - RLD K1; unfold id in RLD; lia).
        lazymatch goal with MUc : munch _ me ?mm, WMc : wmono _ me ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (VCM mm MUc) as CM end.
        pose proof (acimg_crc_u32arr B0C _ sv CM) as CRC. cps_destruct CM as (_ & GOTC & _ & _).
        cbn [aci_segs aci_c ci_segs B0C ci_got ci_crc] in GOTC, CRC. change (0xcda98 + 24)%Z with 0xcdab0%Z in GOTC.
        pose proof crc_words_length as CWL.
        (* [comment removed for export] *)
        brun_to 0x82ee8%Z.
        try rewrite !low32_sx32. try rewrite !low32_lit by lia.
        try replace (bv_unsigned (sx32 (Z_to_bv 64 (e_blockCRC e))) mod 4294967296)%Z with (e_blockCRC e) by (rewrite low32_sx32, low32_lit; symmetry; apply Z.mod_small; lia).
        rewrite ?land255_mod, ?(Z.mod_small (e_state_in_ch e) 256) by lia.
        set (idx := Z.lxor (e_blockCRC e / 16777216) (e_state_in_ch e)).
        assert (Hidx : (0 <= idx < 256)%Z).
        { subst idx. apply lxor_byte; [|lia]. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
        (* [comment removed for export] *)
        brun.
        replace (0xd13e0 + idx * 4)%Z with (0xd13e0 + 4 * idx)%Z by lia.
        u32_read CRC CWL idx tw NTHt RDt.
        wstep. clear RDt GOTC.
        assert (Etw : tw = Z_to_bv 64 (crc32_tbl idx)).
        { pose proof (nth_error_wnth crc_words idx ltac:(lia) ltac:(rewrite CWL; lia)) as N2.
          rewrite NTHt in N2. injection N2 as N3. rewrite N3. apply wnth_crc_words. lia. }
        subst tw. clear NTHt CRC. pose proof (CmpCut.crc32_tbl_range idx Hidx) as TR.
        (* [comment removed for export] *)
        brun.
        reword_C4 EH2 2%nat (crc_update (e_blockCRC e) (Z.land (e_state_in_ch e) 255)).
        { pose proof (crc_update_range (e_blockCRC e) (Z.land (e_state_in_ch e) 255) ltac:(lia)) as CR'.
          replace (crc_update (e_blockCRC e) (Z.land (e_state_in_ch e) 255) mod 4294967296)%Z with (crc_update (e_blockCRC e) (Z.land (e_state_in_ch e) 255))
            by (symmetry; apply Z.mod_small; exact CR').
          unfold crc_update. rewrite !land255_mod, !(Z.mod_small (e_state_in_ch e) 256), shiftr_div24 by lia. subst idx.
          apply low32_crc_stepB; [lia| exact TR]. }
        match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (u8arr_store_ok b0segs mm (E + 128) _ (e_state_in_ch e) _ INU ltac:(rewrite ovb_length_nat; lia) eq_refl) as SO end.
        wstep.
        match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ (le1 ?w)) _) =>
          pose proof (ovb_write1 b0segs mm (E + 128) (e_inUse e) (jseg J 128 256) 256 (e_state_in_ch e) w INU ltac:(lia)) as INU' end.
        clear INU. store_done. rename INU' into INU.
        replace (wr8 (e_inUse e) (e_state_in_ch e) (bv_unsigned (Z_to_bv 64 1))) with (zset (e_inUse e) (e_state_in_ch e) 1) in INU by reflexivity.
        (* [comment removed for export] *)
        brun.
        match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (u8arr_store_ok b0segs mm A2 _ (e_nblock e) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO end.
        wstep.
        match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ (le1 ?w)) _) =>
          pose proof (zb8_write1 b0segs mm A2 (e_arr2 e) ARR2_SIZE (e_nblock e) w AR2 ltac:(lia)) as AR2' end.
        clear AR2. store_done. rename AR2' into AR2.
        rewrite unsigned_lit in AR2 by lia. rewrite (wr8_zset_land (e_arr2 e) (e_nblock e) (e_state_in_ch e)) in AR2 by lia.
        (* [comment removed for export] *)
        brun_to 0x83014%Z.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (ADV (RL (e_nblock e + 1) (zset (e_arr2 e) (e_nblock e) (Z.land (e_state_in_ch e) 255)) (zset (e_inUse e) (e_state_in_ch e) 1)
                              (crc_update (e_blockCRC e) (Z.land (e_state_in_ch e) 255)) ch 1) mm _ _ _ _ _ _ _ _ _ _ _ _) end;
          [ st_eq | apply acb_fast; hcbn; lia
          | unfold EHEAD1; hcbn; rewrite GA, <- ESTRM, AIE; first [exact EH1 | cells_eq_by EH1] | unfold EHEAD2; hcbn; first [exact EH2 | cells_eq_by EH2] | hcbn; exact INU | hcbn; exact AR2
          | unfold STRMB; exact SM | unfold hc_slotsL, hc_slots; exact SL | exact ST | exact MI | unfold ci_W; exact MU | exact WM ].
    - (* [comment removed for export] *)
      brun. if_cases K255; zify_cond_z K255.
      + (* [comment removed for export] *)
        assert (IC : (e_state_in_ch e < 256)%Z) by lia.
        enter_with (APC _ _ _ _ _ _ _); [ st_eq | lia | apply acb_same255; hcbn; lia ].
      + (* [comment removed for export] *)
        brun_to 0x83014%Z.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (ADV (RL (e_nblock e) (e_arr2 e) (e_inUse e) (e_blockCRC e) (e_state_in_ch e) (e_state_in_len e + 1)) mm _ _ _ _ _ _ _ _ _ _ _ _) end;
          [ st_eq | apply acb_same; hcbn; lia
          | unfold EHEAD1; hcbn; rewrite GA, <- ESTRM, AIE; first [exact EH1 | cells_eq_by EH1] | unfold EHEAD2; hcbn; exact EH2 | hcbn; exact INU | hcbn; exact AR2
          | unfold STRMB; exact SM | unfold hc_slotsL, hc_slots; exact SL | exact ST | exact MI | unfold ci_W; exact MU | exact WM ].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

End B0HCC.

End ACeilS1.
