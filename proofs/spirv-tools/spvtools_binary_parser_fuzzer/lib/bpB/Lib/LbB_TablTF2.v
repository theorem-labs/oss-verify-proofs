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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_DStat LbB_ContStmt LbB_ContV4R LbB_ContV4 LbB_ContVot.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablStmt LbB_TablOS LbB_TablPT1 LbB_TablPT4 LbB_TablPT6 LbB_TablPT8 LbB_TablPT9 LbB_TablPT11.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablXP1 LbB_TablXPk1 LbB_TablXPs LbB_TablXPm1 LbB_TablXP LbB_TablTF1 LbB_TablTFk.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma vec32A_pop : forall LB' m m' v b ys t cap, vec32A LB' m v b (ys ++ [t]) cap -> AIMG_TOP <= v ->
  munch [(v + 8, v + 16)] m m' -> rw_cells asegs m' (v + 8) [C8 (Z_to_bv 64 (b + 4 * Zlen ys))] -> vec32A LB' m' v b ys cap.
Proof.
  intros LB' m m' v b ys t cap VEC VT MU HC. pose proof VEC as (Hv & Hv' & HD & Hlen & Hb & F0 & F1 & F2 & FE).
  rewrite Zlen_app1 in Hlen, FE.
  pose proof (mdef_of_rw_cells_hi _ _ _ HC ltac:(lia)) as MD. cbn [cells_size csize] in MD.
  assert (AG : forall lo n, v <= lo -> lo + n <= v + 8 \/ v + 16 <= lo -> lo + n <= v + 24 -> 0 <= n -> agree_on (zwin lo (lo + n)) m m').
  { intros lo n H1 H2 H3 H4 a Ha. unfold zwin in Ha. apply MU. rewrite unsigned_lit by lia. cbn. split; [lia | exact I]. }
  unfold vec32A, vec32. split; [exact Hv|]. split; [exact Hv'|].
  split.
  { intros i Hi. destruct (Z_lt_le_dec i 8) as [L|L]; [|destruct (Z_lt_le_dec i 16) as [L'|L']].
    - rewrite (MU (Z_to_bv 64 (v + i))); [apply HD; lia|]. rewrite unsigned_lit by lia. cbn. split; [lia | exact I].
    - replace (v + i) with (v + 8 + (i - 8)) by lia. apply MD. lia.
    - rewrite (MU (Z_to_bv 64 (v + i))); [apply HD; lia|]. rewrite unsigned_lit by lia. cbn. split; [lia | exact I]. }
  split; [pose proof (Zlen_nonneg ys); lia|]. split; [exact Hb|].
  split; [eapply fld_agree; [lia | cbn; lia | exact F0 | apply (AG v 8); cbn; lia]|].
  split; [exact (fld_of_rw_cells8 m' (v + 8) _ HC ltac:(lia))|].
  split; [eapply fld_agree; [lia | cbn; lia | exact F2 | apply (AG (v + 16) 8); cbn; lia]|].
  intros i Hi. destruct (FE i ltac:(lia)) as [Hr HF]. rewrite Znth_app1_lt in Hr, HF by lia. split; [exact Hr|].
  destruct Hb as [[-> ->]|(Hb0 & Hal & Hc0 & Hbc & HIn & Hdj)]; [lia|].
  eapply fld_agree; [lia | cbn; lia | exact HF |].
  intros a Ha. unfold zwin in Ha. cbn in Ha. apply MU. rewrite unsigned_lit by lia. cbn. split; [lia | exact I].
Qed.

Section TF2.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps_bp H.

  Lemma fs_scratch_where : forall LF iv, fs_scratch H LF iv ->
    (as_FSB H <= fst iv /\ snd iv <= as_FSB H + AFS_SIZE) \/ (sh (as_FSB H) <= fst iv /\ snd iv <= sh (as_FSB H + AFS_SIZE)).
  Proof.
    intros LF iv FS.
    destruct FS as [->|(k & ff' & fp' & FF' & E)]; [left; cbn; unfold AFS_FLAGS, AFS_SIZE; lia|].
    pose proof (fresh_frame_facts H _ _ _ _ FF') as (K & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
    pose proof (fsz_pos k ltac:(lia)).
    unfold AFS_HDR, AFS_FLAGS in *. destruct E as [E|[E|E]]; rewrite E; cbn [fst snd]; [left; lia | left; unfold AFS_SIZE in *; lia | right].
    assert (sh (as_FSB H) <= sh ff') by (apply sh_mono; lia).
    assert (sh ff' + fshn k = sh (ff' + fsz k)) by (unfold sh, fshn, fsz; Z.div_mod_to_equations; nia).
    assert (sh (ff' + fsz k) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; lia). lia.
  Qed.

  Lemma relro0_xpres : forall LB SP X m m', relro0 m -> xpres H LB SP X m m' ->
    (forall a, 0x17e000 <= a < 0x186000 -> ~ rin_ivs X a) -> relro0 m'.
  Proof.
    intros LB SP X m m' RR XP NX i Hi.
    destruct (XP i ltac:(lia)) as [E _]; [|unfold wa in E; rewrite E; apply RR; exact Hi].
    split; [|exact (NX i Hi)]. right; left. unfold aimg_client. lia.
  Qed.

  Lemma tf_iter : forall (e : tfent H) ys t XS LBi bi capi pidi msF mo (Q : config -> Prop),
    tpre H e -> th H e (ys ++ [t]) XS LBi bi capi pidi (mkCfg msF mo) ->
    (PrsGrammar.expand t <> None -> capi = t_cap e /\ bi = t_b e /\ LBi = t_LB e /\ pidi = t_pid e /\ Zlen ys = Zlen (t_xs e) - 1) ->
    (forall msF' mo' XS' LB' b' cap' pid',
       tx H e (ys ++ expandA t) t (xres t) (XS ++ XS') LB' b' cap' pid' (mkCfg msF' mo') -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros e ys t XS LBi bi capi pidi msF mo Q P TH NG K.
    pose proof (rt_bp_base H HH) as HB.
    destruct TH as (R & mL & sL & eL & VIS & HF & TR & KR & MP & TM).
    cbn [cfg_ms cfg_model] in VIS, MP.
    destruct TM as (TFm & TV & FS & XP & AL).
    pose proof TFm as (MI & AC & ST & S00 & ER & RA & SV & RF & RH & OW & RR).
    pose proof TV as (VEC & SH & AD & WV & OB & GR & F31).
    pose proof P as (SP16 & SPH & SPB & SPS & CE & LO & FSB & LFL & TP & RAE & V8 & VB & OBJ & OLD & ND & RH0 & BU1 & BU2 & BU3 & BU4
                     & TRO & TRO2 & AL0 & XL & BNZ & BB & BD & XS31 & RR0).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    unfold TF_STACK, XP_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO.
    destruct TR as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27).
    destruct (tvec_blk H HB e _ mL sL LBi bi capi pidi RH TV) as (LEN & BK & DJV).
    rewrite Zlen_app1 in LEN.
    destruct BK as [(C0 & B0)|(C0 & HIn & ABR)]; [pose proof (Zlen_nonneg ys); lia|].
    pose proof ABR as (A0 & A16 & An & AI & ACe & AF & AP).
    assert (B16 : 16 <= bi) by (clear - A0 A16; Z.div_mod_to_equations; lia).
    assert (B8 : bi mod 8 = 0) by (clear - A16; Z.div_mod_to_equations; lia).
    specialize (DJV ltac:(clear - B16; lia)).
    assert (CB : 4 * capi <= 2 ^ 26).
    { destruct BU1 as [BU1a _]. unfold tcapm in BU1a. destruct GR as [(G1 & _)|((_ & G1) & _)]; unfold tcapm, capmax, vgrow in *; clear - BU1a G1 XL; lia. }
    pose proof VEC as (_ & _ & _ & _ & _ & F0 & F8 & F16 & FE).
    pose proof (Zlen_nonneg ys) as YN.
    assert (TR31 : 0 <= t < 2 ^ 31).
    { apply Forall_app in F31 as [_ X]. inversion X. assumption. }
    assert (F31y : Forall (fun x => 0 <= x < 2 ^ 31) ys) by (apply Forall_app in F31 as [X _]; exact X).
    assert (FT : fldA mL (bi + 4 * Zlen ys) 4 t).
    { destruct (FE (Zlen ys) ltac:(rewrite Zlen_app1; lia)) as [_ X]. rewrite Znth_app1_eq in X. exact X. }
    assert (SH' : SHAD mL bi (cc_gen (4 * capi) (4 * Zlen ys + 4))).
    { pose proof (SH C0) as X. rewrite Zlen_app1 in X. replace (4 * (Zlen ys + 1)) with (4 * Zlen ys + 4) in X by lia. exact X. }
    destruct (vt_slot_shk mL bi capi (Zlen ys) SH' A16 ltac:(lia) YN ltac:(lia)) as (j & SJ & JC).
    assert (JC' : j = 0 \/ ((bi + 4 * Zlen ys) mod 8 = 0 /\ 4 <= j < 8)).
    { destruct JC as [J|J]; [left; exact J|]. right.
      assert (M4 : (bi + 4 * Zlen ys) mod 8 = 0 \/ (bi + 4 * Zlen ys) mod 8 = 4) by (clear - B8; Z.div_mod_to_equations; lia).
      clear - J M4. lia. }
    assert (GZ : gz mL (t_v e) 24) by (intros k Hk; eapply sh0_of_addressable; [exact AD | change (8 * (24 / 8)) with 24; lia]).
    assert (WV8 : wr_at asegs mL (t_v e + 8) 8) by (eapply vt_wr_sub; [exact WV | lia | lia | lia]).
    assert (F8' : fldA mL (t_v e + 8) 8 (bi + 4 * Zlen ys + 4)).
    { rewrite Zlen_app1 in F8. replace (bi + 4 * (Zlen ys + 1)) with (bi + 4 * Zlen ys + 4) in F8 by lia. exact F8. }

    destruct (tf_pop R (t_F e) (t_fc e) mL (seg_rom asegs) (t_v e) bi (bi + 4 * Zlen ys) (bi + 4 * capi) t j Q8 Q9 Q18 Q20 Q21 Q22 Q23 Q24 HF
                V8 ltac:(clear - VB; lia) ltac:(clear - VB; lia) ltac:(clear - VB; lia) B16 B8 ltac:(clear - YN; lia) ltac:(clear - LEN; lia) ltac:(clear - ACe ACF2; lia)
                ltac:(clear - B8; Z.div_mod_to_equations; lia) ltac:(unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in AP; clear - AP; destruct AP; [left | right]; lia)
                DJV F0 F8' F16 GZ FT TR31 SJ JC' WV8)
      as (R1 & M1 & RUN1 & HF1 & KK1 & L1 & L10 & L11 & L12 & L13 & L19 & L8' & L9' & L18' & L20' & L21 & L22 & L23 & L24 & MU1 & WM1 & SK1 & MI1 & CV1).
    eapply (sr_blk H HB); [exact KR | exact VIS | exact HF | exact RUN1 |].
    intros msF1 mo1 KR1 MP1 VIS1.

    pose proof (tgrown_blocks H HB e LBi bi capi pidi P GR) as BL.
    assert (AWO : aclient_write_ok H LBi (t_v e + 8, t_v e + 16)).
    { destruct OBJ as (_ & _ & WO & _).
      replace (t_v e + 16) with (t_v e + 8 + 8) by lia.
      eapply (pt_awo_LBi H (t_LB e) LBi (t_v e + 8) 8 (t_b e) (4 * t_cap e)); [| lia | | clear - BD; lia |].
      - replace (t_v e + 8 + 8) with (t_v e + 16) by lia.
        exact (aclient_write_ok_sub H (t_LB e) (t_v e) (t_v e + 24) (t_v e + 8) (t_v e + 16) WO ltac:(lia) ltac:(lia)).
      - intros bb Hb. destruct (BL bb Hb) as [IN|(EQ & _)]; [left; exact IN | right; subst bb; cbn; split; reflexivity].
      - destruct (pt_app_sh (t_v e + 8) 8 (t_b e) (4 * t_cap e) ltac:(clear - BB; lia) ltac:(clear - XL; lia) ltac:(clear - BB; lia)
                   ltac:(clear - VB; destruct VB; [left | right]; lia)) as [X|X]; [left | right]; exact X. }
    assert (W1 : Forall (fun iv => aclient_write_ok H LBi iv /\ afs_write_ok H (t_LF e) iv /\ aconst_ok iv /\ stack0_ok iv
                      /\ (snd iv <= ATP - 164 \/ ATP - 160 <= fst iv) /\ (snd iv <= tSP e - 80 \/ tSP e <= fst iv)
                      /\ (snd iv <= 0x17e000 \/ 0x186000 <= fst iv)) [(t_v e + 8, t_v e + 16)]).
    { destruct OBJ as (_ & _ & WO & FW & CO & VL). apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
      split; [exact AWO|].
      split; [exact (afs_write_ok_sub H (t_LF e) (t_v e) (t_v e + 24) (t_v e + 8) (t_v e + 16) FW ltac:(lia) ltac:(lia))|].
      split; [exact (aconst_ok_sub (t_v e) (t_v e + 24) (t_v e + 8) (t_v e + 16) CO ltac:(lia) ltac:(lia))|].
      split.
      { unfold stack0_ok. cbn [fst snd].
        assert (SHC : 0x7fff7000 < sh aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
        destruct VB as [VB'|VB']; [right | left; unfold AHI_LO]; lia. }
      unfold ATP. clear - VB VL LO. lia. }
    assert (TF1 : tframe H e M1 sL LBi eL)
      by (eapply (tframe_munch H HB e mL M1 sL LBi eL); [exact P | exact TFm | exact MU1 | exact WM1 | exact (MI1 MI) | exact (SK1 _ _ ST) | exact W1]).
    assert (DVS : sh (t_v e) + nsh 24 <= sh bi \/ sh bi + nsh (4 * capi) <= sh (t_v e)).
    { destruct (pt_sh_apart (t_v e) 24 bi (4 * capi) ltac:(clear - VB; destruct VB; lia) ltac:(lia) ltac:(lia) ltac:(lia) V8 B8 ltac:(clear - DJV; lia)) as [X|X];
      [left | right]; exact X. }
    change (nsh 24) with 3 in DVS.
    assert (VEC1 : vec32A LBi M1 (t_v e) bi ys capi)
      by (eapply (vec32A_pop LBi mL M1 (t_v e) bi ys t capi VEC ltac:(clear - VB; destruct VB; unfold AIMG_TOP; lia) MU1); exact CV1).
    assert (SH1 : SHAD M1 bi (cc_gen (4 * capi) (4 * Zlen ys + 4))).
    { eapply SHAD_transport; [exact SH' | exact MU1 | exact WM1 |]. rewrite cc_gen_length by lia. cbn.
      split; [destruct (pt_app_sh (t_v e + 8) 8 bi (4 * capi) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(clear - VB; destruct VB; [left|right]; lia)); lia | exact I]. }
    assert (AD1 : addressable M1 (t_v e) 24).
    { eapply addressable_transport; [exact AD | exact MU1 | exact WM1 |]. change (nsh 24) with 3. cbn.
      split; [destruct (pt_app_sh (t_v e + 8) 8 (t_v e) 24 ltac:(clear - VB; destruct VB; lia) ltac:(lia) ltac:(clear - VB; destruct VB; lia)
                          ltac:(clear - VB; destruct VB; [left|right]; lia)) as [X|X]; change (nsh 24) with 3 in X; lia | exact I]. }
    assert (XP1 : xpres H (t_LB e) (tSP e) (tXE e XS) (t_m e) M1).
    { eapply (xpres_trans H); [exact XP|].
      eapply (tf_xp_step H HB e XS LBi bi capi pidi sL mL mL M1 _ P GR RH C0 MU1 WM1).
      apply Forall_cons; [|apply Forall_nil]. right; right; right. intros a Ha. cbn [fst snd] in Ha. unfold tXE. cbn [rin_ivs fst snd]. left. clear - Ha. lia. }
    clear MU1 SK1 MI1 W1.
    pose proof TF1 as (MI1 & AC1 & ST1 & S01 & ER1 & RA1 & SV1 & RF1 & RH1 & OW1 & RR1).

    assert (US : bv_unsigned (Z_to_bv 64 (tSP e - 80)) = tSP e - 80) by (apply u64_of_Z; clear - LO CE ACF1 SPH; lia).
    destruct (stk_split asegs M1 (t_lo e) (tSP e - 80) (tSP e) ST1 ltac:(clear - LO CE; lia)) as [ST1l ST1u].
    eapply (ahh_evt_then H HB); [exact KR1 | exact VIS1 | |].
    { eapply (rt_bp_annot H HH) with (beg := bi) (len := 4 * capi) (oldmid := 4 * Zlen ys + 4) (newmid := 4 * Zlen ys) (lo := t_lo e);
        [ exact L10 | exact L11 | rewrite L12; f_equal; lia | exact L13 | exact B8 | clear - C0 CB; lia | clear - YN LEN; lia | clear - YN LEN; lia | exact AP
        | unfold AAPP_HI; clear - ACe ACF2; lia | exact SH1
        | rewrite (KK1 2%bv ltac:(inb)), Q2, US; exact ST1l
        | exact CE
        | rewrite (KK1 2%bv ltac:(inb)), Q2, US; unfold AINTRIN_STACK; clear - LO; lia
        | exact MI1 | exact AC1
        | unfold in_app_mem; destruct (vt_band_of_aapp _ _ AP) as [X|X]; [left | right]; unfold ASHADOW_BASE, AHI_LO, AAPP_HI; clear - X ACe ACF2 C0; lia ]. }
    intros msF2 mo2 KR2 MP2 POST.
    destruct POST as (u0 & u1 & u2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & u3 & u4 & u5 & u6 & m2 & VIS2 & MU2 & WM2 & MI2 & ST2 & SH2 & AC2).
    rewrite L1 in VIS2. rewrite (ret_pc_even TF_ANN_RET ltac:(unfold TF_ANN_RET; lia) eq_refl) in VIS2.
    rewrite (KK1 2%bv ltac:(inb)), Q2, US in MU2, ST2. unfold AINTRIN_STACK in MU2.

    assert (SHB : sh bi + nsh (4 * capi) <= sh (bi + 4 * capi) + 1) by (clear; unfold sh, nsh; Z.div_mod_to_equations; lia).
    assert (BR47 : 0 <= bi + 4 * capi <= 2 ^ 47) by (clear - A0 C0 ACe ACF2; lia).
    pose proof (sh_lt_2_45 (bi + 4 * capi) BR47) as SHB2.
    assert (SHB3 : 0x7fff8000 <= sh bi) by (clear - A0; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    pose proof FSB as (G7 & G9 & _ & G10).
    assert (D1 : sh bi + nsh (4 * capi) <= as_FSB H \/ as_FSB H + AFS_SIZE <= sh bi)
      by (apply aapp_disjoint_sh; [exact G10 | clear - A0; lia | unfold AAPP_HI; clear - ACe ACF2; lia | clear - C0; lia]).
    assert (ST2f : stk asegs m2 (t_lo e) (tSP e)).
    { apply (stk_merge asegs m2 (t_lo e) (tSP e - 80) (tSP e)); [exact ST2 | | clear - LO; lia].
      eapply stk_transport_disjoint; [exact ST1u | exact MU2 | exact WM2 |].
      cbn. clear - SHB SHB2 LO CE ACF1. split; [lia|]. split; [lia | exact I]. }
    assert (W2 : Forall (fun iv => aclient_write_ok H LBi iv /\ afs_write_ok H (t_LF e) iv /\ aconst_ok iv /\ stack0_ok iv
                      /\ (snd iv <= ATP - 164 \/ ATP - 160 <= fst iv) /\ (snd iv <= tSP e - 80 \/ tSP e <= fst iv)
                      /\ (snd iv <= 0x17e000 \/ 0x186000 <= fst iv)) [(sh bi, sh bi + nsh (4 * capi)); (tSP e - 80 - 4096, tSP e - 80)]).
    { assert (AK : aceil <= tSP e - 80 - 4096) by (clear - LO CE; lia).
      destruct (stack_window_ok H LBi (t_LF e) (tSP e - 80 - 4096) (tSP e - 80) AK G9) as (Wa & Wb & Wc).
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
      - split; [right; right; right; left; exists (pidi, bi, 4 * capi); split; [exact HIn | cbn [blk_addr blk_size fst snd]; lia]|].
        split; [left; cbn [fst snd]; split; [clear - D1; unfold AFS_SIZE in *; lia | right; unfold ATLS_PRIV_HI, ATP; clear - SHB3; lia]|].
        split; [apply aconst_ok_high; [apply sh_mono; unfold AIMG_TOP in *; clear - AI; lia | right; left; clear - SHB3; lia]|].
        split; [apply stack0_ok_sh; clear - A0 ACe ACF2 C0; lia|].
        unfold ATP. clear - SHB SHB2 SHB3 LO CE ACF1. lia.
      - split; [exact Wa|]. split; [exact Wb|]. split; [exact Wc|].
        split; [left; cbn [fst]; unfold AHI_LO; clear - AK ACF1; lia|].
        unfold ATP. clear - AK ACF1. lia. }
    assert (TF2 : tframe H e m2 sL LBi eL)
      by (eapply (tframe_munch H HB e M1 m2 sL LBi eL); [exact P | exact TF1 | exact MU2 | exact WM2 | exact MI2 | exact ST2f | exact W2]).
    assert (VEC2 : vec32A LBi m2 (t_v e) bi ys capi).
    { eapply (vec32A_munch LBi M1 m2 (t_v e) bi ys capi _ VEC1 MU2).
      - cbn. split; [destruct (pt_app_sh (t_v e) 24 bi (4 * capi) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(clear - VB; destruct VB; [left|right]; lia)); clear - H0 SHB; lia|].
        destruct OBJ as (_ & _ & _ & _ & _ & VL). split; [clear - VL LO; lia | exact I].
      - cbn. split; [destruct (pt_app_sh bi (4 * Zlen ys) bi (4 * capi) ltac:(lia) ltac:(lia) ltac:(lia)
                                 ltac:(unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in AP; clear - AP LEN YN A0; destruct AP; [left|right]; lia)); clear - H0 SHB LEN YN; lia|].
        split; [clear - ACe CE LO LEN YN; lia | exact I]. }
    assert (AD2 : addressable m2 (t_v e) 24).
    { eapply addressable_transport; [exact AD1 | exact MU2 | exact WM2 |]. change (nsh 24) with 3. cbn.
      split; [clear - DVS; lia|]. split; [pose proof (sh_lt_2_45 (t_v e + 24) ltac:(clear - VB; destruct VB; lia)) as X;
                              assert (sh (t_v e) + 3 <= sh (t_v e + 24) + 1) by (clear; unfold sh; Z.div_mod_to_equations; lia); clear - X H0 LO CE ACF1; lia | exact I]. }
    assert (WV2 : wr_at asegs m2 (t_v e) 24) by exact (wr_at_wmono _ _ _ _ (wr_at_wmono _ _ _ _ WV WM1) WM2).
    assert (OW2 : lb_own LBi m2) by exact (lb_own_wmono _ _ _ (lb_own_wmono _ _ _ OW WM1) WM2).
    assert (XP2 : xpres H (t_LB e) (tSP e) (tXE e XS) (t_m e) m2).
    { eapply (xpres_trans H); [exact XP1|].
      eapply (tf_xp_step H HB e XS LBi bi capi pidi sL M1 M1 m2 _ P GR RH1 C0 MU2 WM2).
      apply Forall_cons; [right; left; cbn [fst snd]; lia|]. apply Forall_cons; [|apply Forall_nil].
      right; right; left. cbn [fst snd]. clear - LO CE. lia. }
    clear MU2 W2.
    pose proof TF2 as (_ & _ & _ & S02 & ER2 & RA2 & SV2 & RF2 & RH2 & _ & RR2).

    set (R3 := mkR (Z_to_bv 64 TF_ANN_RET) (getr R1 2) (getr R1 3) (getr R1 4) u0 u1 u2 (getr R1 8) (getr R1 9) d0 d1 d2 d3 d4 d5 d6 d7
                   (getr R1 18) (getr R1 19) (getr R1 20) (getr R1 21) (getr R1 22) (getr R1 23) (getr R1 24) (getr R1 25)
                   (getr R1 26) (getr R1 27) u3 u4 u5 u6) in VIS2.
    assert (HF3 : rfull R3) by apply rfull_mkR.
    destruct (tf_call R3 (t_F e) (t_fc e) m2 (seg_rom asegs) HF3) as (R4 & RUN4 & HF4 & KK4 & M1' & M10 & M11).
    eapply (sr_blk H HB); [exact KR2 | exact VIS2 | exact HF3 | exact RUN4 |].
    intros msF4 mo4 KR4 MP4 VIS4.

    assert (E2 : getr R4 2 = Z_to_bv 64 (tSP e - 80)) by (rewrite (KK4 2%bv ltac:(inb)); change (getr R3 2) with (getr R1 2); rewrite (KK1 2%bv ltac:(inb)); exact Q2).
    assert (E3 : getr R4 3 = t_gp e) by (rewrite (KK4 3%bv ltac:(inb)); change (getr R3 3) with (getr R1 3); rewrite (KK1 3%bv ltac:(inb)); exact Q3).
    assert (E4 : getr R4 4 = t_tp e) by (rewrite (KK4 4%bv ltac:(inb)); change (getr R3 4) with (getr R1 4); rewrite (KK1 4%bv ltac:(inb)); exact Q4).
    assert (E8 : getr R4 8 = Z_to_bv 64 (t_v e)) by (rewrite (KK4 8%bv ltac:(inb)); exact L8').
    assert (E9 : getr R4 9 = Z_to_bv 64 (t_v e + 8)) by (rewrite (KK4 9%bv ltac:(inb)); exact L9').
    assert (E18 : getr R4 18 = Z_to_bv 64 (t_v e + 16)) by (rewrite (KK4 18%bv ltac:(inb)); exact L18').
    assert (E19 : getr R4 19 = Z_to_bv 64 t) by (rewrite (KK4 19%bv ltac:(inb)); exact L19).
    assert (E20 : getr R4 20 = Z_to_bv 64 5) by (rewrite (KK4 20%bv ltac:(inb)); exact L20').
    assert (E21 : getr R4 21 = Z_to_bv 64 0x7fff8000) by (rewrite (KK4 21%bv ltac:(inb)); exact L21).
    assert (E22 : getr R4 22 = Z_to_bv 64 (sh (t_v e + 8))) by (rewrite (KK4 22%bv ltac:(inb)); exact L22).
    assert (E23 : getr R4 23 = Z_to_bv 64 (sh (t_v e))) by (rewrite (KK4 23%bv ltac:(inb)); exact L23).
    assert (E24 : getr R4 24 = Z_to_bv 64 (sh (t_v e + 16))) by (rewrite (KK4 24%bv ltac:(inb)); exact L24).
    assert (E25 : getr R4 25 = t_s9 e) by (rewrite (KK4 25%bv ltac:(inb)); change (getr R3 25) with (getr R1 25); rewrite (KK1 25%bv ltac:(inb)); exact Q25).
    assert (E26 : getr R4 26 = t_s10 e) by (rewrite (KK4 26%bv ltac:(inb)); change (getr R3 26) with (getr R1 26); rewrite (KK1 26%bv ltac:(inb)); exact Q26).
    assert (E27 : getr R4 27 = t_s11 e) by (rewrite (KK4 27%bv ltac:(inb)); change (getr R3 27) with (getr R1 27); rewrite (KK1 27%bv ltac:(inb)); exact Q27).
    assert (E10 : getr R4 10 = Z_to_bv 64 t) by (rewrite M10; exact L19).
    assert (E11 : getr R4 11 = Z_to_bv 64 (t_v e)) by (rewrite M11; exact L8').

    assert (OBJ2 : obj_win H LBi (t_LF e) (tSP e - 80) (t_lo e) (t_v e) 24).
    { destruct OBJ as (O1 & O2 & O3 & O4 & O5 & VL).
      eapply (pt_objwin_LBi H (t_LB e) LBi (t_LF e) (t_LF e) (tSP e) (tSP e - 80) (t_lo e) (t_v e) (t_b e) (4 * t_cap e)
                (conj O1 (conj O2 (conj O3 (conj O4 (conj O5 VL))))));
        [ clear; lia | clear - VL; destruct VL; [left | right]; lia
        | intros bb Hb; destruct (BL bb Hb) as [IN|(EQ & _)]; [left; exact IN | right; subst bb; cbn; split; reflexivity]
        | intros f Hf; exact Hf | clear - VB; destruct VB; lia | exact V8 | clear - BB; destruct BB; lia
        | | clear - XL; lia | clear - BB; destruct BB; lia | clear - VB; destruct VB; [left | right]; lia
        | exact BD | clear - BB; destruct BB; [left | right]; lia | clear - VB; destruct VB; lia ].
      destruct OLD as [(X & _)|(Cc & HIn0)]; [exfalso; exact (BNZ X)|].
      pose proof (ah_blocks H HB _ _ _ _ RH0 HIn0) as (_ & X16 & _). cbn [blk_addr fst snd] in X16.
      clear - X16; Z.div_mod_to_equations; lia. }
    assert (BUD : PrsGrammar.expand t <> None -> xbud LBi capi (capmax (Zlen ys) capi 3) (as_AL H sL)).
    { intros NE. destruct (NG NE) as (-> & -> & -> & -> & EL). rewrite EL. unfold xbud. unfold tcapm in BU1, BU2.
      destruct BU1 as [BU1a BU1b]. rewrite closs_refl in AL.
      split; [split; [exact BU1a | clear - BU1b AL; lia]|]. split; [exact BU2|]. split; [exact BU3 | exact BU4]. }
    eapply (ah_seq H HB).
    { eapply (expand_okA H HH) with (t := t) (v := t_v e) (b := bi) (cap := capi) (xs := ys) (pid := pidi) (LB := LBi) (LF := t_LF e)
        (lo := t_lo e) (B := t_B e) (shi := t_shi e) (errv := eL) (s := sL);
        [ exact VIS4 | exact E10 | exact E11 | exact TR31 | exact RR2 | | exact BUD ].
      unfold pat_pre0. rewrite E2, US, E4.
      split; [exact VEC2|]. split; [exact V8|]. split; [exact AD2|]. split; [exact OBJ2|]. split; [exact VB|]. split; [exact WV2|]. split; [exact OW2|].
      split; [exact OB|]. split; [intros Hc; exact SH2|]. split; [exact RH2|]. split; [exact KR4|].
      split.
      { assert (CC : t_cap e <= capi <= tcapm e) by (destruct GR as [(G1 & _)|((G1 & G1') & _)]; [clear - G1 XL | clear - G1 G1' XL]; unfold tcapm, capmax in *; lia).
        destruct BU1 as [_ BU1b]. pose proof (closs_mono (t_cap e) capi (tcapm e) ltac:(clear - CC XL; lia)).
        clear - AL AL0 BU1b H0. lia. }
      split; [exact TRO|]. split; [exact TRO2|]. split; [exact RA2|]. split; [clear - SPB; lia|].
      split; [clear - SP16; Z.div_mod_to_equations; lia|]. split; [clear - SPH; lia|].
      split; [exact ST2|]. split; [exact CE|]. split; [unfold XP_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK; clear - LO; lia|].
      split; [exact ER2|]. split; [exact MI2|]. split; [exact TP|].
      split; [rewrite (proj1 (conj M1' I)), u64_of_Z by (unfold TF_XP_RET; lia); reflexivity|].
      split; [exact AC2|]. split; [exact RF2|]. split; [exact LFL|]. split; [exact S02 | clear - SPS; lia]. }
    intros c5 POST. destruct c5 as [msF5 mo5].
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m5 & errv5 & s5 & LB5 & b5 & cap5 & XS5 & POST).
    destruct POST as (VIS5 & R05 & KR5 & MP5 & MI5 & ST5 & ER5 & RA5 & VEC5 & RH5 & SH5 & AD5 & WV5 & OW5 & FS5 & GR5 & RF5 & AC5 & S05 & AL5).
    cbn [cfg_ms cfg_model] in VIS5, KR5, MP5.
    rewrite E2, US in ST5, GR5. rewrite E4 in ER5.
    rewrite (proj1 (conj M1' I)) in VIS5. rewrite (ret_pc_even TF_XP_RET ltac:(unfold TF_XP_RET; lia) eq_refl) in VIS5.

    assert (XE5 : v4_oldx bi (4 * capi) = [(bi, bi + 4 * capi); (sh bi, sh bi + nsh (4 * capi))])
      by (unfold v4_oldx; destruct (Z.eqb_spec bi 0); [lia | reflexivity]).
    assert (GX : xpres H LBi (tSP e - 80) ((t_v e, t_v e + 24) :: v4_oldx bi (4 * capi) ++ XS5) m2 m5
                 /\ ((cap5 = capi /\ b5 = bi /\ LB5 = LBi)
                     \/ (capi < cap5 <= match PrsGrammar.expand t with Some _ => capmax (Zlen ys) capi 3 | None => capi end
                         /\ (exists pid', LB5 = v4_newLB H LBi bi pidi pid' b5 (4 * cap5)) /\ ablock_range H b5 (4 * cap5)))).
    { destruct GR5 as [(Y1 & Y2 & Y3 & X5)|(G1 & (pid' & G2 & G3) & X5)].
      - split; [rewrite XE5; exact X5|]. left. split; [exact Y1|]. split; [exact Y2 | exact Y3].
      - split; [exact X5|]. right. split; [exact G1|]. split; [exists pid'; exact G2 | exact G3]. }
    clear GR5. destruct GX as [XP5 GI].

    assert (FW5 : forall l h, In (l, h) ((t_v e, t_v e + 24) :: v4_oldx bi (4 * capi) ++ XS5) ->
                  (l = t_v e /\ h = t_v e + 24) \/ (h <= aceil /\ 0x186000 <= l) \/ (0x7fff8000 <= l /\ h <= 2 ^ 45)).
    { intros l h Hin. destruct Hin as [E|Hin]; [left; injection E as -> ->; split; reflexivity|].
      rewrite XE5 in Hin. cbn [app] in Hin. destruct Hin as [E|[E|Hin]].
      - injection E as <- <-. right; left. unfold AIMG_TOP in AI. clear - AI ACe C0. lia.
      - injection E as <- <-. right; right. clear - SHB SHB2 SHB3. lia.
      - rewrite Forall_forall in FS5. destruct (fs_scratch_where (t_LF e) (l, h) (FS5 _ Hin)) as [W|W]; cbn [fst snd] in W.
        + right; left. unfold AIMG_TOP in G7. clear - W G7 G9. lia.
        + right; right. assert (sh (as_FSB H + AFS_SIZE) <= sh aceil) by (apply sh_mono; exact G9).
          assert (0x7fff8000 <= sh (as_FSB H)) by (unfold sh; rewrite ASHADOW_BASE_val; unfold AIMG_TOP in G7; clear - G7; Z.div_mod_to_equations; lia).
          assert (AC47 : 0 <= aceil <= 2 ^ 47) by (clear - ACF1 ACF2; lia).
          pose proof (sh_lt_2_45 aceil AC47). clear - W H0 H1 H2. lia. }
    assert (CR5 : forall A n, 0 <= n -> tSP e - 80 <= A -> A + n <= tSP e -> (A + n <= 0x186000 \/ True) ->
                 xclient_range H LBi (tSP e - 80) ((t_v e, t_v e + 24) :: v4_oldx bi (4 * capi) ++ XS5) A n).
    { intros A n N0 A1 A2 _. split; [left; exact A1|]. apply Forall_forall. intros [l h] Hin. cbn [fst snd].
      destruct OBJ as (_ & _ & _ & _ & _ & VL).
      destruct (FW5 l h Hin) as [(-> & ->)|[(X1 & X2)|(X1 & X2)]]; [clear - VL LO A1 A2; lia | clear - X1 CE LO A1; lia | ].
      assert (2 ^ 45 <= tSP e - 80) by (clear - CE LO ACF1; lia). clear - X2 H0 A1. lia. }
    assert (ST5f : stk asegs m5 (t_lo e) (tSP e)).
    { apply (stk_merge asegs m5 (t_lo e) (tSP e - 80) (tSP e)); [exact ST5 | | clear - LO; lia].
      destruct (stk_split asegs m2 (t_lo e) (tSP e - 80) (tSP e) ST2f ltac:(clear - LO CE; lia)) as [_ STu2].
      eapply (xpres_stk H); [exact XP5 | exact STu2 | lia |].
      apply Forall_forall. intros [l h] Hin. cbn [fst snd]. destruct OBJ as (_ & _ & _ & _ & _ & VL).
      destruct (FW5 l h Hin) as [(-> & ->)|[(X1 & X2)|(X1 & X2)]]; [clear - VL LO; lia | clear - X1 CE LO; lia | ].
      assert (2 ^ 45 <= tSP e - 80) by (clear - CE LO ACF1; lia). clear - X2 H0. lia. }
    assert (SV5 : rw_cells asegs m5 (tSP e - 80) (tsaved e)).
    { eapply (xpres_rw_cells H); [exact XP5 | exact SV2 |]. change (Z.of_nat (cells_size (tsaved e))) with 80.
      apply CR5; [lia | lia | lia | right; exact I]. }
    assert (RR5 : relro0 m5).
    { eapply relro0_xpres; [exact RR2 | exact XP5 |]. intros a Ha IN.
      assert (EX : exists l h, In (l, h) ((t_v e, t_v e + 24) :: v4_oldx bi (4 * capi) ++ XS5) /\ l <= a < h).
      { clear - IN. induction ((t_v e, t_v e + 24) :: v4_oldx bi (4 * capi) ++ XS5) as [|[l h] W IH]; [destruct IN|].
        cbn [rin_ivs fst snd] in IN. destruct IN as [IN|IN]; [exists l, h; split; [left; reflexivity | exact IN]|].
        destruct (IH IN) as (l' & h' & I1 & I2). exists l', h'. split; [right; exact I1 | exact I2]. }
      destruct EX as (l & h & Hin & Ha2).
      destruct (FW5 l h Hin) as [(-> & ->)|[(X1 & X2)|(X1 & X2)]]; [clear - VB Ha Ha2; lia | clear - X2 Ha Ha2; lia | clear - X1 Ha Ha2; lia]. }
    assert (F31' : Forall (fun x => 0 <= x < 2 ^ 31) (ys ++ expandA t)).
    { apply Forall_app. split; [exact F31y|]. unfold expandA, PrsGrammar.expand. cbv -[Z.le Z.lt Z.pow Z.eqb].
      repeat (destruct (t =? _); [repeat constructor; clear; lia|]). apply Forall_nil. }

    assert (XP15 : xpres H (t_LB e) (tSP e) (tXE e (XS ++ XS5)) (t_m e) m5).
    { eapply (xpres_trans H).
      { eapply (xpres_weaken H); [exact XP2 | lia | intros bb Hb; exact Hb | intros a Ha; exact (tXE_mono H e XS XS5 a Ha)]. }
      destruct GR as [(Y1 & Y2 & Y3 & Y4)|(GG1 & GG2 & GG3)].
      - rewrite Y2, Y1, Y3 in XP5.
        eapply (xpres_weaken H); [exact XP5 | clear; lia | intros bb Hb; exact Hb |].
        intros a Ha. unfold tXE. cbn [rin_ivs] in Ha |- *. destruct Ha as [Ha|Ha]; [left; exact Ha | right].
        rewrite rin_ivs_app in Ha. rewrite !rin_ivs_app. destruct Ha as [Ha|Ha]; [left; exact Ha | right; right; exact Ha].
      - destruct (tgrown_tail H HB e LBi bi capi pidi P GG2) as (LBt & EL & BLt).
        pose proof RH2 as RH2'. rewrite EL in XP5, RH2'.
        assert (NI : ~ In pidi (map blk_id LBt)).
        { pose proof (ah_nodup H HB _ _ _ RH2') as NDi. cbn [map] in NDi. apply NoDup_cons_iff in NDi as [X _]. exact X. }
        rewrite XE5 in XP5.
        assert (XP5' : xpres H ((pidi, bi, 4 * capi) :: LBt) (tSP e - 80) (((t_v e, t_v e + 24) :: XS5) ++ [(bi, bi + 4 * capi); (sh bi, sh bi + nsh (4 * capi))]) m2 m5).
        { eapply (xpres_weaken H); [exact XP5 | clear; lia | intros bb Hb; exact Hb |].
          intros a Ha. cbn [rin_ivs app] in Ha |- *. rewrite rin_ivs_app. cbn [rin_ivs fst snd] in Ha |- *.
          clear - Ha. tauto. }
        pose proof (pt_xp_drop H HB sL LBt pidi bi (4 * capi) (tSP e - 80) ((t_v e, t_v e + 24) :: XS5) m2 m2 m5 RH2' NI ltac:(clear - CE LO; lia) XP5') as XP3.
        eapply (pt_xp_lift H LBt (tSP e - 80) ((t_v e, t_v e + 24) :: XS5) (t_LB e) (tSP e) (tXE e (XS ++ XS5)) m2 m5 XP3 ltac:(clear; lia)).
        + intros bb Hb. destruct (BLt bb Hb) as [IN|(EQ & Cc & Bc)]; [left; exact IN|]. right. intros a Ha. subst bb.
          cbn [blk_addr blk_size fst snd] in Ha. apply (tXE_old H); assumption.
        + intros a Ha. cbn [rin_ivs] in Ha. unfold tXE. cbn [rin_ivs]. destruct Ha as [Ha|Ha]; [left; exact Ha | right].
          rewrite !rin_ivs_app. right; right. exact Ha. }
    set (R5 := mkR (Z_to_bv 64 TF_XP_RET) (getr R4 2) (getr R4 3) (getr R4 4) t0' t1' t2' (getr R4 8) (getr R4 9) a0' a1' a2' a3' a4' a5' a6' a7'
                   (getr R4 18) (getr R4 19) (getr R4 20) (getr R4 21) (getr R4 22) (getr R4 23) (getr R4 24) (getr R4 25) (getr R4 26) (getr R4 27)
                   t3' t4' t5' t6') in VIS5.
    assert (TX : forall pid5, v4_oldblk LB5 b5 cap5 pid5 -> tgrown H e LB5 b5 cap5 pid5 ->
                 tx H e (ys ++ expandA t) t (xres t) (XS ++ XS5) LB5 b5 cap5 pid5 (mkCfg msF5 mo5)).
    { intros pid5 OB5 TG5. exists R5, m5, s5, errv5. cbn [cfg_ms cfg_model].
      split; [exact VIS5|]. split; [apply rfull_mkR|].
      split.
      { unfold tregs. change (getr R5 2) with (getr R4 2). change (getr R5 3) with (getr R4 3). change (getr R5 4) with (getr R4 4).
        change (getr R5 8) with (getr R4 8). change (getr R5 9) with (getr R4 9). change (getr R5 18) with (getr R4 18).
        change (getr R5 20) with (getr R4 20). change (getr R5 21) with (getr R4 21). change (getr R5 22) with (getr R4 22).
        change (getr R5 23) with (getr R4 23). change (getr R5 24) with (getr R4 24). change (getr R5 25) with (getr R4 25).
        change (getr R5 26) with (getr R4 26). change (getr R5 27) with (getr R4 27).
        repeat (split; [assumption|]). exact E27. }
      split; [change (getr R5 19) with (getr R4 19); exact E19|].
      split; [change (getr R5 10) with a0'; rewrite R05; unfold xres; reflexivity|].
      split; [exact KR5|].
      split; [eapply (ah_mpres_trans H HB); [exact MP|]; eapply (ah_mpres_trans H HB); [exact MP1|];
              eapply (ah_mpres_trans H HB); [exact MP2|]; eapply (ah_mpres_trans H HB); [exact MP4 | exact MP5]|].
      split.
      { unfold tframe. split; [exact MI5|]. split; [exact AC5|]. split; [exact ST5f|]. split; [exact S05|]. split; [exact ER5|].
        split; [exact RA5|]. split; [exact SV5|]. split; [exact RF5|]. split; [exact RH5|]. split; [exact OW5 | exact RR5]. }
      split.
      { unfold tvec. split; [exact VEC5|]. split; [exact SH5|]. split; [exact AD5|]. split; [exact WV5|].
        split; [exact OB5|]. split; [exact TG5 | exact F31']. }
      split; [apply Forall_app; split; [exact FS | exact FS5]|].
      split; [exact XP15|].
      pose proof (closs_tele (t_cap e) capi cap5). clear - AL AL5 H0. lia. }
    destruct GI as [(Y1 & Y2 & Y3)|(G1 & (pid' & G2) & G3)].
    - subst cap5 b5 LB5. exact (K msF5 mo5 XS5 LBi bi capi pidi (TX pidi OB GR)).
    - apply (K msF5 mo5 XS5 LB5 b5 cap5 pid'). apply TX.
      + right. split; [clear - G1 C0; lia|]. rewrite G2. unfold v4_newLB. left. reflexivity.
      + right. destruct (PrsGrammar.expand t) as [l|] eqn:ET; [|exfalso; clear - G1; lia].
        destruct (NG ltac:(intros XX; discriminate XX)) as (Ec & Eb & EL & Ep & EY). subst capi bi LBi pidi.
        split; [unfold tcapm, capmax in *; rewrite <- EY; clear - G1 XL; unfold capmax in G1; lia|].
        split; [exact G2 | exact G3].
  Qed.
End TF2.
