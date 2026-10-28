(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_ContStmt LbB_ContV4R LbB_ContV4 LbB_ContVot.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablStmt LbB_TablOS LbB_TablPT1 LbB_TablPT3 LbB_TablPT4 LbB_TablPT6 LbB_TablPT8 LbB_TablPT9 LbB_TablPT15.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablXP1 LbB_TablXPk1 LbB_TablXPk2 LbB_TablXPx.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition xres (t : Z) : Z := match PrsGrammar.expand t with Some _ => 1 | None => 0 end.

Lemma xp_ret_ok : v4_ret_ok XP_RET.
Proof.
  intros Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m HQ.
  unfold XP_RET. step. apply evt_done. exact HQ.
Qed.

Section XPm1.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HB : asan_rt_hyps H.

  Definition xQ (e : xpent H) : config -> Prop :=
    pat_post H (x_ra e) (x_sp e) (x_gp e) (x_tp e) (x_s0 e) (x_s1 e) (x_s2 e) (x_s3 e) (x_s4 e) (x_s5 e) (x_s6 e) (x_s7 e) (x_s8 e)
             (x_s9 e) (x_s10 e) (x_s11 e) (x_F e) (x_fc e) (x_s e) (x_LB e) (x_LF e) (x_v e) (x_b e) (x_cap e) (xcapm e)
             (x_xs e ++ expandA (x_t e)) (x_pid e) (x_lo e) (x_B e) (x_shi e) (x_m e) (x_mo e)
             (fun r0 => r0 = Z_to_bv 64 (xres (x_t e))).

  Definition x_end (e : xpent H) (ys : list Z) (one : bool) (cf : config) : Prop :=
    exists R mL sL LBi bi capi pidi eL sv,
      as_VIS H sL (cfg_ms cf) = MS R (x_F e) (Z_to_bv 64 (if one then XP_ONE else XP_EXIT)) (x_fc e) None mL (seg_rom asegs) /\ rfull R
      /\ getr R 3 = x_gp e /\ getr R 4 = x_tp e /\ RPl (xcommon (xg e bi capi ys) ++ [(18%bv, g_ff (xg e bi capi ys))]) R /\ (one = false -> getr R 10 = Z_to_bv 64 0)
      /\ as_AKREL H sL cf /\ as_MPRES H (x_mo e) (cfg_model cf)
      /\ xmem H e ys sv mL sL LBi bi capi pidi eL.

  Lemma xp_exit_step : forall (e : xpent H) one msF mo, xpre H e ->
    x_end e (x_xs e ++ expandA (x_t e)) one (mkCfg msF mo) -> (if one then 1 else 0) = xres (x_t e) ->
    as_SR H (xQ e) (mkCfg msF mo).
  Proof.
    intros e one msF mo P EX RES.
    destruct EX as (R & mL & sL & LBi & bi & capi & pidi & eL & sv & VIS & HF & G3 & G4 & RP & RA0 & KR & MP & PM).
    cbn [cfg_ms cfg_model] in VIS, MP.
    destruct PM as (PF & SL & PV & XP & AL).
    destruct PF as (MI & AC & ST & S00 & ER & RA & SV & CL & FPc & WF & WS & WP & WL & KC & RF & RH & OW).
    pose proof PV as (VEC & SH & AD & WV & OB & GR).
    pose proof (xgeoP_of H e P) as G.
    destruct G as (SP16 & S45 & S132 & S1S & S1L & SPH & CE & LO & F64 & FL & FH & P1 & P2 & P3 & P4 & FS1 & FS2 & SHF0 & SHF1 & SHF2 & SHF3
                   & FB & PB & V8 & VB & VL & VF & VFL & VFP & SV1 & SV2 & TR & TP).
    pose proof P as (FF & _). pose proof (x2frame_facts H _ _ _ FF) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G10 & _).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    unfold XP_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO.
    unfold RPl, xcommon in RP. cbn [app g_S1 g_SP g_ff xg] in RP.
    pose proof RP as RP'. apply Forall_cons_iff in RP' as [R2 RP']. apply Forall_cons_iff in RP' as [R8 RP']. apply Forall_cons_iff in RP' as [R9 RP'].
    apply Forall_cons_iff in RP' as [R25 RP']. apply Forall_cons_iff in RP' as [R26 RP']. apply Forall_cons_iff in RP' as [_ RP']. apply Forall_cons_iff in RP' as [R18 _]. cbn [fst snd] in R2, R8, R9, R18, R25, R26.
    assert (WF8 : wr_at asegs mL (x_ff e) 8) by (eapply os_wr_at_sub; [exact WF | lia | lia | lia]).
    destruct (xp_tail one R (x_F e) (x_fc e) mL (seg_rom asegs) (x_ra e) (x_s0 e) (x_s1 e) (x_s2 e) (x_s3 e) (x_s4 e) (x_s5 e) (x_s6 e)
                (x_s7 e) (x_s8 e) (x_s9 e) (x_s10 e) (x_s11 e) (x_ff e) (x_fp e) (xSP e) (xS1 e) R8 R9 R18 R25 R26 F64 ltac:(lia) ltac:(lia) FB
                ltac:(lia) ltac:(lia) PB S45 S1S SPH ltac:(lia) SV FPc WF8 WS WP MI)
      as (R1 & M1 & RUN & L1 & L2 & L8 & L9 & L18 & L19 & L20 & L21 & L22 & L23 & L24 & L25 & L26 & L27 & KK & L10 & MU & WM & MI1 & SK & FLB).
    pose proof (msteps_full asegs _ _ RUN HF) as HF1. cbn [ms_regs] in HF1.
    assert (SPv : Z_to_bv 64 (xSP e) = x_sp e) by (unfold xSP; apply Z_to_bv_bv_unsigned).
    rewrite SPv in L2.
    assert (K3 : getr R1 3 = x_gp e) by (rewrite (KK 3%bv ltac:(inb)); exact G3).
    assert (K4 : getr R1 4 = x_tp e) by (rewrite (KK 4%bv ltac:(inb)); exact G4).
    assert (K10 : getr R1 10 = Z_to_bv 64 (xres (x_t e))).
    { rewrite L10. rewrite <- RES. destruct one; [reflexivity | exact (RA0 eq_refl)]. }
    eapply (sr_evt H HB) with
      (P := fun ms => ms = MS (mkR (x_ra e) (x_sp e) (x_gp e) (x_tp e) (getr R1 5) (getr R1 6) (getr R1 7) (x_s0 e) (x_s1 e)
                                   (Z_to_bv 64 (xres (x_t e))) (getr R1 11) (getr R1 12) (getr R1 13) (getr R1 14) (getr R1 15) (getr R1 16) (getr R1 17)
                                   (x_s2 e) (x_s3 e) (x_s4 e) (x_s5 e) (x_s6 e) (x_s7 e) (x_s8 e) (x_s9 e) (x_s10 e) (x_s11 e)
                                   (getr R1 28) (getr R1 29) (getr R1 30) (getr R1 31))
                              (x_F e) (ret_pc (x_ra e)) (x_fc e) None M1 (seg_rom asegs));
      [exact KR | exact VIS | |].
    { eapply evt_of_msteps; [exact RUN|]. rewrite (rfull_eq R1 HF1). apply xp_ret_ok.
      rewrite L1, L2, K3, K4, L8, L9, K10, L18, L19, L20, L21, L22, L23, L24, L25, L26, L27. reflexivity. }
    intros msF' mo' KR' MP' HP. cbv beta in HP.

    set (W := [(sh (x_ff e), sh (x_ff e) + 32); (x_ff e, x_ff e + 8); (x_fp e, x_fp e + 1)]) in MU.
    assert (SHA : sh (as_FSB H) <= sh (x_ff e) /\ sh (x_ff e + 256) <= sh (as_FSB H + AFS_SIZE))
      by (split; apply sh_mono; unfold AFS_SIZE in *; lia).
    assert (SHT : sh AIMG_TOP <= sh (x_ff e)) by (apply sh_mono; unfold AIMG_TOP in *; lia).
    pose proof SHT as SHT'. replace (sh AIMG_TOP) with 0x800d5000 in SHT' by reflexivity.
    pose proof (sh_lt_2_45 (x_ff e + 256) ltac:(lia)) as SB.
    assert (WA : Forall (aclient_write_ok H LBi) W).
    { apply Forall_cons; [right; right; right; right; right; left; cbn [fst snd]; lia|].
      apply Forall_cons; [right; right; right; right; left; cbn [fst snd]; unfold AFS_SIZE in *; lia|].
      apply Forall_cons; [right; right; right; right; left; cbn [fst snd]; unfold AFS_SIZE in *; lia | apply Forall_nil]. }
    assert (WC : Forall aconst_ok W).
    { apply Forall_cons; [apply aconst_ok_high; [cbn [fst]; clear - SHT; lia | right; left; cbn [fst]; clear - SHT'; lia]|].
      apply Forall_cons; [eapply (LbB_SR.aconst_ok_app (as_FSB H) AFS_SIZE); [exact G10 | cbn; lia | cbn; unfold AFS_SIZE in *; lia]|].
      apply Forall_cons; [eapply (LbB_SR.aconst_ok_app (as_FSB H) AFS_SIZE); [exact G10 | cbn; lia | cbn; unfold AFS_SIZE in *; lia]|].
      apply Forall_nil. }
    assert (W0 : Forall stack0_ok W).
    { apply Forall_cons; [right; cbn [snd]; assert (sh (x_ff e + 256) <= sh aceil) by (apply sh_mono; lia); lia|].
      apply Forall_cons; [eapply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact G10 | lia | unfold AFS_SIZE in *; lia]|].
      apply Forall_cons; [eapply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact G10 | lia | unfold AFS_SIZE in *; lia] | apply Forall_nil]. }
    destruct (xvec_blk H HB e _ mL sL LBi bi capi pidi RH PV) as (LEN & BK & DJV).
    assert (BR : (capi = 0 /\ bi = 0) \/ (0 < capi /\ ablock_range H bi (4 * capi) /\ bi mod 8 = 0)).
    { destruct BK as [X|(C0 & HIn & ABR)]; [left; exact X | right]. split; [exact C0|]. split; [exact ABR|].
      pose proof ABR as (_ & A16 & _). clear - A16; Z.div_mod_to_equations; lia. }
    assert (F8 : x_ff e mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
    unfold xQ, pat_post.
    exists (getr R1 5), (getr R1 6), (getr R1 7), (Z_to_bv 64 (xres (x_t e))), (getr R1 11), (getr R1 12), (getr R1 13), (getr R1 14),
      (getr R1 15), (getr R1 16), (getr R1 17), (getr R1 28), (getr R1 29), (getr R1 30), (getr R1 31), M1, eL, sL, LBi, bi, capi, (xXS H e).
    cbn [cfg_ms cfg_model].
    split; [exact HP|]. split; [reflexivity|]. split; [exact KR'|]. split; [exact (ah_mpres_trans H HB _ _ _ MP MP')|].
    split; [exact MI1|]. split; [exact (SK _ _ ST)|].
    split.
    { eapply rw_cells_transport; [exact ER | exact MU | exact WM |].
      assert (ERA : errno_addr (x_tp e) = ATP - 164) by (rewrite TP, HLib.u64_of_Z by (unfold ATP; lia); lia).
      rewrite ERA. unfold ATP. cbn. clear - SHF1 FL P1 FS1. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
    split; [eapply (ah_rauxv_frame H HB); [exact RA | exact MU | exact WM | exact WA]|].
    split.
    { eapply (vec32A_munch LBi mL M1 (x_v e) bi _ capi W VEC MU).
      - cbn. split; [destruct (pt_app_sh (x_v e) 24 (x_ff e) 256 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct VB; [left|right]; lia)) as [X|X];
                      change (nsh 256) with 32 in X; clear - X; lia|].
        clear - VF VFP. split; [lia|]. split; [lia | exact I].
      - destruct BR as [(C0 & B0)|(C0 & (A0 & A16 & An & AI & ACe & AF & AP) & B8)];
          [subst bi; cbn; clear - LEN C0 SHF1 FL P1 FS1; split; [lia|]; split; [lia|]; split; [lia | exact I]|].
        cbn. split; [destruct (pt_app_sh bi (4 * Zlen (x_xs e ++ expandA (x_t e))) (x_ff e) 256 ltac:(lia) ltac:(lia) ltac:(lia)
                                ltac:(unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in AP; destruct AP; [left|right]; lia)) as [X|X];
                     change (nsh 256) with 32 in X; clear - X; lia|].
        clear - LEN AF P1 P2 P3 P4. unfold AFS_SIZE, AFS_HDR in *. split; [lia|]. split; [lia | exact I]. }
    split; [eapply (ah_RHEAP_frame H HB); [exact RH | exact MU | exact WM | exact WA]|].
    split.
    { intros Hc. eapply SHAD_transport; [exact (SH Hc) | exact MU | exact WM |].
      destruct BR as [(C0 & B0)|(C0 & (A0 & A16 & An & AI & ACe & AF & AP) & B8)]; [lia|].
      rewrite cc_gen_length by lia.
      assert (SHB : sh bi + nsh (4 * capi) <= sh (bi + 4 * capi) + 1) by (clear; unfold sh, nsh; Z.div_mod_to_equations; lia).
      pose proof (sh_lt_2_45 (bi + 4 * capi) ltac:(lia)) as SB2.
      assert (D1 : sh bi + nsh (4 * capi) <= as_FSB H \/ as_FSB H + AFS_SIZE <= sh bi)
        by (apply aapp_disjoint_sh; [exact G10 | lia | unfold AAPP_HI; lia | lia]).
      assert (X : sh bi + nsh (4 * capi) <= sh (x_ff e) \/ sh (x_ff e) + 32 <= sh bi).
      { destruct (pt_sh_apart bi (4 * capi) (x_ff e) 256 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) B8 F8
                   ltac:(clear - AF P3 P4; unfold AFS_SIZE, AFS_HDR in *; lia)) as [X|X]; change (nsh 256) with 32 in X; [left | right]; lia. }
      cbn. clear - X D1 P1 P2 P3 P4 FS1. unfold AFS_SIZE, AFS_HDR in *. repeat (split; [lia|]). exact I. }
    split.
    { eapply addressable_transport; [exact AD | exact MU | exact WM |]. change (nsh 24) with 3.
      assert (X : sh (x_v e) + 3 <= sh (x_ff e) \/ sh (x_ff e) + 32 <= sh (x_v e)).
      { destruct (pt_sh_apart (x_v e) 24 (x_ff e) 256 ltac:(destruct VB; lia) ltac:(lia) ltac:(lia) ltac:(lia) V8 F8
                   ltac:(clear - VF; destruct VF; lia)) as [X|X]; change (nsh 256) with 32 in X; change (nsh 24) with 3 in X; [left | right]; lia. }
      cbn. clear - X SV1 SV2 FB PB. repeat (split; [lia|]). exact I. }
    split; [exact (wr_at_wmono _ _ _ _ WV WM)|]. split; [exact (lb_own_wmono _ _ _ OW WM)|].
    split; [exact (fs_scratch_of_fresh H (x_LF e) 2 (x_ff e) (x_fp e) FF)|].
    assert (XP1 : xpres H (x_LB e) (xSP e) (xXE H e) (x_m e) M1).
    { pose proof P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RH0 & _).
      eapply (xpres_trans H); [exact XP|].
      eapply (xpres_of_munch H (x_s e) (x_LB e) (xSP e) (xXE H e) W (x_m e) mL M1); [exact HB | exact RH0 | exact MU | exact WM |].
      unfold W.
      apply Forall_cons; [right; intros a Ha; cbn [fst snd] in Ha; apply (xXE_frm H); clear - Ha; lia|].
      apply Forall_cons; [right; intros a Ha; cbn [fst snd] in Ha; apply (xXE_frm H); clear - Ha; lia|].
      apply Forall_cons; [right; intros a Ha; cbn [fst snd] in Ha; apply (xXE_frm H); clear - Ha; lia|].
      apply Forall_nil. }
    split.
    { unfold xSP in XP1. destruct GR as [(E1 & E2 & E3 & E4)|(G1 & G2 & G3')].
      - left. split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
        eapply (xpres_weaken H); [exact XP1 | lia | intros bb Hb; exact Hb |].
        intros a Ha. unfold xXE, v4_oldx in Ha. cbn [rin_ivs] in Ha |- *.
        destruct Ha as [Ha|Ha]; [left; exact Ha|]. right.
        destruct (Z.eqb_spec (x_b e) 0) as [_|_]; cbn [app rin_ivs] in Ha; [right; right; exact Ha|].
        destruct Ha as [Ha|[Ha|Ha]]; [left; exact Ha | right; left; exact Ha | right; right; exact Ha].
      - right. split; [exact G1|]. split; [exists pidi; split; [exact G2 | exact G3']|]. exact XP1. }
    split.
    { pose proof (ah_release H HB (xLF e) mL M1 W 2 (x_ff e) (x_fp e) RF (or_introl eq_refl) MU WM) as REL.
      unfold xLF in REL. rewrite lf_remove_head in REL. apply REL; [|exact FLB].
      apply Forall_cons; [left; left; cbn [fst snd]; split; [unfold AFS_SIZE in *; lia | right; unfold ATLS_PRIV_HI, ATP; lia]|].
      apply Forall_cons; [left; right; exists (2, x_ff e, x_fp e); split; [left; reflexivity | cbn; change (fsz 2) with 256; lia]|].
      apply Forall_cons; [right; split; reflexivity | apply Forall_nil]. }
    split; [eapply ACONST_frame; [exact AC | exact MU | exact WM | exact WC]|].
    split; [eapply stack0_transport; [exact S00 | exact MU | exact WM | exact W0]|].
    exact AL.
  Qed.

  Lemma xp_xpre_of : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe) (t v b cap : Z) (xs : list Z)
      (pid : bptr) (lo B shi ff fp : Z),
    let SP := bv_unsigned sp in
    fresh_frame H LF 2 ff fp ->
    (length LF < AFS_MAXLIVE_BP)%nat -> as_RFS H LF m ->
    SP mod 16 = 0 -> SP <= 2 ^ 47 -> SP <= B -> SP <= shi -> aceil <= lo -> lo <= SP - XP_STACK ->
    tp = Z_to_bv 64 ATP -> bv_unsigned ra mod 2 = 0 ->
    0 <= t < 2 ^ 31 -> trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_RREF] ->
    v mod 8 = 0 -> ((0x6e8000 <= v /\ v + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= v /\ v + 24 <= 2 ^ 47)) ->
    obj_win H LB LF SP lo v 24 -> v4_oldblk LB b cap pid -> vec32A LB m v b xs cap -> as_RHEAP H s LB m ->
    (PrsGrammar.expand t <> None -> xbud LB cap (capmax (Zlen xs) cap 3) (as_AL H s)) ->
    trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_CREF] -> 0 <= as_AL H s ->
    xpre H (XPEnt H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF t v b cap xs pid lo B shi ff fp).
  Proof.
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF t v b cap xs pid lo B shi ff fp SP
      FF LFL RF SP16 SPH SPB SPS CE LO TP RA TR TRO2 V8 VB OBJ OLD VEC RH BU TRO AL0.
    pose proof VEC as (_ & _ & _ & LEN & BK & _).
    unfold xpre, XV. cbn [x_LF x_LB x_v x_b x_cap x_pid x_t x_xs x_m x_s x_lo x_B x_shi x_tp x_ra x_sp x_ff x_fp xcapm].
    split; [exact FF|]. split; [exact LFL|].
    split; [intros f Hf; exact (proj2 (ah_RFS_range H HB _ _ RF) f Hf)|].
    split; [exact SP16|]. split; [exact SPH|]. split; [exact SPB|]. split; [exact SPS|]. split; [exact CE|]. split; [exact LO|].
    split; [exact TP|]. split; [exact RA|]. split; [exact TR|]. split; [exact TRO2|]. split; [exact I|]. split; [exact I|].
    split; [exact I|]. split; [exact I|]. split; [exact V8|]. split; [exact VB|]. split; [exact OBJ|]. split; [exact OLD|].
    split; [exact (ah_nodup H HB _ _ _ RH)|]. split; [exact RH|].
    assert (BU' : PrsGrammar.expand t <> None -> xbud LB cap (match PrsGrammar.expand t with Some _ => capmax (Zlen xs) cap 3 | None => cap end) (as_AL H s)).
    { intros X. destruct (PrsGrammar.expand t); [exact (BU X) | exfalso; exact (X eq_refl)]. }
    split; [intros X; exact (proj1 (BU' X))|]. split; [intros X; exact (proj1 (proj2 (BU' X)))|]. split; [intros X; exact (proj1 (proj2 (proj2 (BU' X))))|].
    split; [intros X; exact (proj2 (proj2 (proj2 (BU' X))))|]. split; [exact TRO|]. split; [exact AL0|].
    split; [exact LEN|].
    destruct BK as [(B0 & C0)|(B0 & B16 & C0 & BC & HIn & DJ)].
    - split; [intros _; exact C0|]. split; [left; lia|]. intros X; contradiction.
    - split; [intros X; lia|].
      destruct OLD as [(X & _)|(_ & HIn')]; [lia|].
      pose proof (ah_blocks H HB _ _ _ _ RH HIn') as (_ & _ & _ & AI & ACe & _ & AP). cbn [blk_addr blk_size fst snd] in AI, ACe, AP.
      pose proof aceil_facts as ((ACF1 & ACF2) & _).
      split; [unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in AP; destruct AP; [left | right]; lia|].
      intros _; exact DJ.
  Qed.

  Lemma xp_entry_xmem : forall (e : xpent H) M errv,
    xpre H e ->
    munch [(x_lo e, xSP e); (as_FSB H, as_FSB H + AFS_FLAGS); (x_fp e, x_fp e + 1); (x_ff e, x_ff e + 256);
           (sh (x_ff e), sh (x_ff e) + 32)] (x_m e) M -> wmono asegs (x_m e) M -> mem_inv asegs M ->
    stk asegs M (x_lo e) (xSP e) -> ACONST (x_m e) ->
    rw_cells asegs (x_m e) (errno_addr (x_tp e)) [C4 errv] -> as_rauxv_ok H (x_m e) (x_B e) -> stack0 (x_m e) (x_lo e) (x_shi e) ->
    rw_cells asegs M (xSP e - 104) (xsaved e) -> rw_cells asegs M (x_ff e + 32) [C4 (Z_to_bv 64 (x_t e))] ->
    rw_cells asegs M (x_ff e + 248) [C8 (Z_to_bv 64 (x_fp e))] -> wr_at asegs M (x_ff e) 256 -> wr_at asegs M (sh (x_ff e)) 32 ->
    wr_at asegs M (x_fp e) 1 -> wr_at asegs M (x_ff e + 32) 4 -> rw_cells asegs M (sh (x_ff e) + 4) [C1 (b8 4)] ->
    as_RFS H (xLF e) M ->
    vec32A (x_LB e) (x_m e) (x_v e) (x_b e) (x_xs e) (x_cap e) ->
    (0 < x_cap e -> SHAD (x_m e) (x_b e) (cc_gen (4 * x_cap e) (4 * Zlen (x_xs e)))) ->
    addressable (x_m e) (x_v e) 24 -> wr_at asegs (x_m e) (x_v e) 24 -> lb_own (x_LB e) (x_m e) ->
    xmem H e (x_xs e) None M (x_s e) (x_LB e) (x_b e) (x_cap e) (x_pid e) errv.
  Proof.
    intros e M errv P MU WM MI ST AC ER RA S0 SV SL FPc WF WS WP WL KC RF VEC OSH ADV WV OWN.
    pose proof (xgeoP_of H e P) as G.
    destruct G as (_ & S45 & _ & S1S & _ & SPH & CE & LO & F64 & FL & FH & P1 & P2 & P3 & P4 & FS1 & FS2 & SHF0 & SHF1 & SHF2 & SHF3
                   & FB & PB & V8 & VB & VL & VF & VFL & VFP & SV1 & SV2 & _ & TP).
    pose proof P as (FF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OLD & ND & RH & _ & _ & _ & _ & _ & _
                     & CX & B0C & BB & BD).
    pose proof FF as FF'. apply (x2frame_facts H) in FF' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G10 & _).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    unfold XP_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO.
    set (W := [(x_lo e, xSP e); (as_FSB H, as_FSB H + AFS_FLAGS); (x_fp e, x_fp e + 1); (x_ff e, x_ff e + 256);
               (sh (x_ff e), sh (x_ff e) + 32)]) in MU.
    assert (SHA : sh (as_FSB H) <= sh (x_ff e) /\ sh (x_ff e + 256) <= sh (as_FSB H + AFS_SIZE))
      by (split; apply sh_mono; unfold AFS_SIZE in *; lia).
    assert (SHT0 : sh AIMG_TOP <= sh (x_ff e)) by (apply sh_mono; unfold AIMG_TOP in *; lia).
    pose proof SHT0 as SHT. replace (sh AIMG_TOP) with 0x800d5000 in SHT by reflexivity.
    pose proof (sh_lt_2_45 (x_ff e + 256) ltac:(lia)) as SB.
    assert (WA : Forall (aclient_write_ok H (x_LB e)) W).
    { apply Forall_cons; [left; cbn [fst]; lia|].
      apply Forall_cons; [right; right; right; right; left; cbn [fst snd]; unfold AFS_SIZE, AFS_FLAGS in *; lia|].
      apply Forall_cons; [right; right; right; right; left; cbn [fst snd]; unfold AFS_SIZE in *; lia|].
      apply Forall_cons; [right; right; right; right; left; cbn [fst snd]; unfold AFS_SIZE in *; lia|].
      apply Forall_cons; [right; right; right; right; right; left; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (WC : Forall aconst_ok W).
    { apply Forall_cons; [apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d5000 by reflexivity; cbn [fst]; clear - CE ACF1; lia | right; left; cbn [fst]; clear - CE ACF1; lia]|].
      apply Forall_cons; [eapply (LbB_SR.aconst_ok_app (as_FSB H) AFS_SIZE); [exact G10 | cbn; lia | cbn; unfold AFS_FLAGS, AFS_SIZE in *; lia]|].
      apply Forall_cons; [eapply (LbB_SR.aconst_ok_app (as_FSB H) AFS_SIZE); [exact G10 | cbn; lia | cbn; unfold AFS_SIZE in *; lia]|].
      apply Forall_cons; [eapply (LbB_SR.aconst_ok_app (as_FSB H) AFS_SIZE); [exact G10 | cbn; lia | cbn; unfold AFS_SIZE in *; lia]|].
      apply Forall_cons; [apply aconst_ok_high; [cbn [fst]; clear - SHT0; lia | right; left; cbn [fst]; clear - SHT; lia]|].
      apply Forall_nil. }
    assert (W0 : Forall stack0_ok W).
    { apply Forall_cons; [left; cbn [fst]; unfold AHI_LO; lia|].
      apply Forall_cons; [eapply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact G10 | lia | unfold AFS_FLAGS, AFS_SIZE in *; lia]|].
      apply Forall_cons; [eapply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact G10 | lia | unfold AFS_SIZE in *; lia]|].
      apply Forall_cons; [eapply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact G10 | lia | unfold AFS_SIZE in *; lia]|].
      apply Forall_cons; [right; cbn [snd]; assert (sh (x_ff e + 256) <= sh aceil) by (apply sh_mono; lia); lia | apply Forall_nil]. }
    pose proof VEC as (_ & _ & _ & LEN & BK & _).
    assert (BR : (x_b e = 0 /\ x_cap e = 0) \/ (0 < x_cap e /\ ablock_range H (x_b e) (4 * x_cap e) /\ x_b e mod 8 = 0)).
    { destruct BK as [(B0 & C0)|(B0 & B16 & C0 & BC & HIn & DJ)]; [left; split; assumption|].
      right. destruct OLD as [(X & _)|(_ & HIn')]; [lia|]. split; [lia|].
      split; [exact (ah_blocks H HB _ _ _ _ RH HIn')|]. clear - B16; Z.div_mod_to_equations; lia. }
    assert (F8 : x_ff e mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
    unfold xmem.
    split.
    { unfold xframe.
      split; [exact MI|]. split; [eapply ACONST_frame; [exact AC | exact MU | exact WM | exact WC]|]. split; [exact ST|].
      split; [eapply stack0_transport; [exact S0 | exact MU | exact WM | exact W0]|].
      split.
      { eapply rw_cells_transport; [exact ER | exact MU | exact WM |].
        assert (ERA : errno_addr (x_tp e) = ATP - 164) by (rewrite TP, HLib.u64_of_Z by (unfold ATP; lia); lia).
        rewrite ERA. unfold W, ATP. cbn. clear - CE ACF1 FS1 P1 SHF1 FL. unfold AFS_SIZE in *. repeat (split; [lia|]). exact I. }
      split; [eapply (ah_rauxv_frame H HB); [exact RA | exact MU | exact WM | exact WA]|].
      split; [exact SV|]. split; [exact SL|]. split; [exact FPc|]. split; [exact WF|]. split; [exact WS|]. split; [exact WP|].
      split; [exact WL|]. split; [exact KC|]. split; [exact RF|].
      split; [eapply (ah_RHEAP_frame H HB); [exact RH | exact MU | exact WM | exact WA]|].
      exact (lb_own_wmono _ _ _ OWN WM). }
    split; [exact I|].
    split.
    { unfold xvec. split.
      { eapply (vec32A_munch (x_LB e) (x_m e) M (x_v e) (x_b e) (x_xs e) (x_cap e) W VEC MU).
        - unfold W. cbn.
          destruct (pt_app_sh (x_v e) 24 (x_ff e) 256 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct VB; [left|right]; lia)) as [X|X];
            change (nsh 256) with 32 in X; clear - X VL VF VFL VFP; unfold AFS_FLAGS in *; (repeat (split; [lia|])); exact I.
        - destruct BR as [(B0 & C0)|(C0 & (A0 & A16 & An & AI & ACe & AF & AP) & B8)].
          + rewrite B0, C0 in *. assert (Zlen (x_xs e) = 0) by lia. rewrite H0. unfold W. cbn. clear - CE ACF1 FS1 P1 FL SHF1. repeat (split; [lia|]). exact I.
          + unfold W. cbn.
            destruct (pt_app_sh (x_b e) (4 * Zlen (x_xs e)) (x_ff e) 256 ltac:(lia) ltac:(lia) ltac:(lia)
                       ltac:(unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in AP; destruct AP; [left|right]; lia)) as [X|X];
              change (nsh 256) with 32 in X; clear - X LEN AF ACe CE P1 P2 P3 P4; unfold AFS_SIZE, AFS_FLAGS, AFS_HDR in *;
              (repeat (split; [lia|])); exact I. }
      split.
      { intros Hc. eapply SHAD_transport; [exact (OSH Hc) | exact MU | exact WM |].
        destruct BR as [(B0 & C0)|(C0 & (A0 & A16 & An & AI & ACe & AF & AP) & B8)]; [lia|].
        rewrite cc_gen_length by lia.
        assert (SHB : sh (x_b e) + nsh (4 * x_cap e) <= sh (x_b e + 4 * x_cap e) + 1) by (clear; unfold sh, nsh; Z.div_mod_to_equations; lia).
        pose proof (sh_lt_2_45 (x_b e + 4 * x_cap e) ltac:(lia)) as SB2.
        assert (D1 : sh (x_b e) + nsh (4 * x_cap e) <= as_FSB H \/ as_FSB H + AFS_SIZE <= sh (x_b e))
          by (apply aapp_disjoint_sh; [exact G10 | lia | unfold AAPP_HI; lia | lia]).
        assert (X : sh (x_b e) + nsh (4 * x_cap e) <= sh (x_ff e) \/ sh (x_ff e) + 32 <= sh (x_b e)).
        { destruct (pt_sh_apart (x_b e) (4 * x_cap e) (x_ff e) 256 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) B8 F8
                     ltac:(clear - AF P3 P4; unfold AFS_SIZE, AFS_HDR in *; lia)) as [X|X]; change (nsh 256) with 32 in X; [left | right]; lia. }
        unfold W. cbn. clear - X D1 P1 P2 P3 P4 FS1 SHB SB2 CE S45 LO ACF1. unfold AFS_SIZE, AFS_FLAGS, AFS_HDR in *.
        repeat (split; [lia|]). exact I. }
      split.
      { eapply addressable_transport; [exact ADV | exact MU | exact WM |]. change (nsh 24) with 3.
        assert (X : sh (x_v e) + 3 <= sh (x_ff e) \/ sh (x_ff e) + 32 <= sh (x_v e)).
        { destruct (pt_sh_apart (x_v e) 24 (x_ff e) 256 ltac:(destruct VB; lia) ltac:(lia) ltac:(lia) ltac:(lia) V8 F8
                     ltac:(clear - VF; destruct VF; lia)) as [X|X]; change (nsh 256) with 32 in X; change (nsh 24) with 3 in X; [left | right]; lia. }
        assert (D1 : sh (x_v e) + nsh 24 <= as_FSB H \/ as_FSB H + AFS_SIZE <= sh (x_v e))
          by (apply aapp_disjoint_sh; [exact G10 | destruct VB; lia | unfold AAPP_HI; destruct VB; lia | lia]).
        change (nsh 24) with 3 in D1.
        unfold W. cbn. clear - X D1 SV1 SV2 CE S45 LO ACF1 FS1 P1 P2 P3 P4. unfold AFS_SIZE, AFS_FLAGS in *. repeat (split; [lia|]). exact I. }
      split; [exact (wr_at_wmono _ _ _ _ WV WM)|].
      split; [exact OLD|]. left. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity. }
    split; [|rewrite closs_refl; lia].
    eapply (xpres_of_munch H (x_s e) (x_LB e) (xSP e) (xXE H e) W (x_m e) (x_m e) M); [exact HB | exact RH | exact MU | exact WM |].
    unfold W.
    apply Forall_cons; [left; cbn [fst snd]; split; [exact CE | lia]|].
    do 4 (apply Forall_cons; [right; intros a Ha; cbn [fst snd] in Ha; unfold xXE; cbn [rin_ivs]; right; apply rin_ivs_app; right;
                               unfold xXS; cbn [rin_ivs fst snd]; lia|]).
    apply Forall_nil.
  Qed.
End XPm1.
