From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmExit LbB_PiStmt.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma pi_blocks_of : forall words n diag c, c_blocks c = state_blocks (pi_stc words n diag c) ++ c_tr c.
Proof.
  intros words n diag c. unfold c_blocks, state_blocks, pi_stc. cbn [st_m1 st_m2 st_m3 st_v1 st_v2 st_v3].
  rewrite (vob_eq (t3a (c_v1 c)) (t3b (c_v1 c)) (t3c (c_v1 c))).
  rewrite (v32b_eq (t3a (c_v2 c)) (Zlen (t3b (c_v2 c))) (t3c (c_v2 c))).
  rewrite (v32b_eq (t3a (c_v3 c)) (Zlen (t3b (c_v3 c))) (t3c (c_v3 c))).
  rewrite <- !app_assoc. reflexivity.
Qed.

Section PiExit.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.

  Definition pi_prcw (w : piw H) (c : pmc) : parserC :=
    pi_prc (pw_cons H w) (pw_user H w) (pw_words H w) (pw_n H w) (pw_diag H w) c.

  Lemma pi_exit : forall (w : piw H) LF s LB LBs m c,
    piw_ok H w LF m -> PIX H LINV w s LB LBs m c -> pw_n H w <= c_widx c ->
    exists c', pi_err H LINV w s LB LBs m c'.
  Proof.
    intros w LF s LB LBs m c K P Hn. exists (pi_prcw w c).
    pose proof (pk_papp _ _ _ _ K) as (PA & PA0 & PA16).
    pose proof (aapp_below_aceil _ _ PA) as PR2.
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (px_scal _ _ _ _ _ _ _ _ P) as (Sc1 & Sc2 & Sc3 & Sc4).
    pose proof (px_own _ _ _ _ _ _ _ _ P) as [OWN1 OWN2].
    pose proof (pk_n _ _ _ _ K) as Hn24. pose proof (pk_diag _ _ _ _ K) as Hd.
    assert (Hw : 0 <= pw_words H w < 2 ^ 64).
    { destruct (pk_words _ _ _ _ K) as (pw & k & _ & Rg & W0 & _ & Whi & _ & _). lia. }
    assert (SB : state_blocks (pi_stc (pw_words H w) (pw_n H w) (pw_diag H w) c) = c_blocks c).
    { rewrite (pi_blocks_of (pw_words H w) (pw_n H w) (pw_diag H w) c), (px_tr _ _ _ _ _ _ _ _ P), app_nil_r. reflexivity. }
    pose proof (px_pdef _ _ _ _ _ _ _ _ P) as PD.
    pose proof (px_meas _ _ _ _ _ _ _ _ P) as (ME1 & ME2 & ME3).
    pose proof (px_al _ _ _ _ _ _ _ _ P) as (AL1 & AL2 & AL3).
    pose proof (pm_phi_le_cap c) as PHC.
    unfold pi_err, pi_prcw.
    split; [exact (px_rheap _ _ _ _ _ _ _ _ P)|].
    split; [split; [exact OWN1 | change (Permutation (lbl LBs) (state_blocks (pi_stc (pw_words H w) (pw_n H w) (pw_diag H w) c))); rewrite SB; exact OWN2]|].
    split; [exact (px_lbown _ _ _ _ _ _ _ _ P)|].
    split.
    { constructor; cbn [pi_prc pc_cons pc_user pc_state].
      - exact (px_cons _ _ _ _ _ _ _ _ P).
      - exact (px_user _ _ _ _ _ _ _ _ P).
      - exact (px_hdrfn _ _ _ _ _ _ _ _ P).
      - exact (px_insfn _ _ _ _ _ _ _ _ P).
      - exact (px_hunk _ _ _ _ _ _ _ _ P).
      - unfold ST_OFF. constructor; cbn [pi_stc st_words st_nwords st_diag st_widx st_icount st_endian st_flags st_m1 st_m2 st_m3 st_v1 st_v2 st_v3].
        + apply cell8_of_fld; [exact Hw | exact (px_words _ _ _ _ _ _ _ _ P)].
        + replace (pw_p H w + 48 + 8) with (pw_p H w + O_N) by (unfold O_N; lia).
          apply cell8_of_fld; [lia | exact (px_n _ _ _ _ _ _ _ _ P)].
        + replace (pw_p H w + 48 + 16) with (pw_p H w + O_DIAG) by (unfold O_DIAG; lia).
          apply cell8_of_fld; [exact Hd | exact (px_diag _ _ _ _ _ _ _ _ P)].
        + replace (pw_p H w + 48 + 24) with (pw_p H w + O_WIDX) by (unfold O_WIDX; lia).
          apply cell8_of_fld; [lia | exact (px_widx _ _ _ _ _ _ _ _ P)].
        + replace (pw_p H w + 48 + 32) with (pw_p H w + O_ICOUNT) by (unfold O_ICOUNT; lia).
          apply cell8_of_fld; [lia | exact (px_icount _ _ _ _ _ _ _ _ P)].
        + replace (pw_p H w + 48 + 40) with (pw_p H w + O_ENDIAN) by (unfold O_ENDIAN; lia).
          apply cell4_of_fld; [lia | exact (px_endian _ _ _ _ _ _ _ _ P)].
        + replace (pw_p H w + 48 + 44) with (pw_p H w + O_FLAGS) by (unfold O_FLAGS; lia).
          apply cellw2_of_flds; [unfold O_FLAGS; lia | unfold O_FLAGS, PARSER_SIZE in *; lia | exact Sc4 | exact (px_flags _ _ _ _ _ _ _ _ P)
                                | exact (px_retry _ _ _ _ _ _ _ _ P)].
        + replace (pw_p H w + 48 + 48) with (pw_p H w + O_M1) by (unfold O_M1; lia). exact (px_m1 _ _ _ _ _ _ _ _ P).
        + replace (pw_p H w + 48 + 88) with (pw_p H w + O_M2) by (unfold O_M2; lia). exact (px_m2 _ _ _ _ _ _ _ _ P).
        + replace (pw_p H w + 48 + 128) with (pw_p H w + O_M3) by (unfold O_M3; lia). exact (px_m3 _ _ _ _ _ _ _ _ P).
        + replace (pw_p H w + 48 + 168) with (pw_p H w + O_V1) by (unfold O_V1; lia). cbn [t3a t3b t3c fst snd].
          exact (vraw_of_vec_opnd _ _ _ _ _ _ (px_v1 _ _ _ _ _ _ _ _ P)).
        + replace (pw_p H w + 48 + 192) with (pw_p H w + O_V2) by (unfold O_V2; lia). cbn [t3a t3b t3c fst snd].
          exact (vraw_of_vec32 _ _ _ _ _ _ (px_v2 _ _ _ _ _ _ _ _ P)).
        + replace (pw_p H w + 48 + 216) with (pw_p H w + O_V3) by (unfold O_V3; lia). cbn [t3a t3b t3c fst snd].
          exact (vraw_of_vec32 _ _ _ _ _ _ (px_v3 _ _ _ _ _ _ _ _ P)).
        + intros i Hi. replace (pw_p H w + 48 + i) with (pw_p H w + (48 + i)) by lia. apply PD. unfold PARSER_SIZE. lia.
        + Z.div_mod_to_equations. lia.
        + rewrite SB. apply NoDup_ListNoDup.
          apply (Permutation_NoDup (Permutation_map fst OWN2)). rewrite map_fst_lbl.
          apply (nodup_addrs H HHbp s LB m LBs (pw_LB0 H w)). { exact (px_rheap _ _ _ _ _ _ _ _ P). }
          eapply Permutation_trans; [exact OWN1 | apply Permutation_app_comm].
      - intros i Hi. apply PD. unfold ST_OFF, PARSER_SIZE in *. lia.
      - exact PA16.
      - unfold PARSER_SIZE in *. lia.
      - exact (px_consf _ _ _ _ _ _ _ _ P).
      - exact (px_consd _ _ _ _ _ _ _ _ P).
      - pose proof (pk_pcons _ _ _ _ K) as PC. unfold apart, PARSER_SIZE in *. lia. }
    split.
    { pose proof (px_sh _ _ _ _ _ _ _ _ P) as ((U1 & U2 & U3 & V1 & V2 & V3) & SHp & SHc).
      split; [exact SHp|]. split; [exact SHc|].
      unfold state_sh. cbn [pi_prc pc_state pi_stc st_m1 st_m2 st_m3 st_v1 st_v2 st_v3].
      split; [exact U1|]. split; [exact U2|]. split; [exact U3|].
      split; [exact (vec_sh_of_opnd m _ _ _ V1) |]. split; [exact (vec_sh_of_32 m _ _ _ V2) | exact (vec_sh_of_32 m _ _ _ V3)]. }
    cbn [pi_prc pc_cons pc_user pc_state pi_stc st_words st_nwords].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [lia|]. split; [lia|]. split; [lia|].
    split.
    { unfold st_vsteps. cbn [pi_prc pc_state pi_stc st_v1 st_v2 st_v3 t3a t3b t3c fst snd].
      pose proof (px_v1 _ _ _ _ _ _ _ _ P) as (_ & _ & _ & V1 & _).
      split; [exists (t3b (c_v1 c)); unfold OPND_SZ; split; [lia | reflexivity]|].
      split; [exists (Zlen (t3b (c_v2 c))); split; [unfold Zlen; lia | reflexivity]|].
      exists (Zlen (t3b (c_v3 c))); split; [unfold Zlen; lia | reflexivity]. }
    split; [intros q k Hq; apply (px_bsz _ _ _ _ _ _ _ _ P q k); rewrite <- SB; exact Hq|].
    split; [exact (px_meminv _ _ _ _ _ _ _ _ P)|].
    split; [exact (px_errno _ _ _ _ _ _ _ _ P)|].
    split; [exact (px_rauxv _ _ _ _ _ _ _ _ P)|].
    split; [exact (px_aconst _ _ _ _ _ _ _ _ P)|].
    split; [exact (px_stack0 _ _ _ _ _ _ _ _ P)|].
    split; [exact (px_linv _ _ _ _ _ _ _ _ P)|].
    split; [unfold PM_RESERVE in *; lia | exact PD].
  Qed.
End PiExit.
