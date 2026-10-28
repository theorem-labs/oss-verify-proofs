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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_DStat LbB_ContStmt LbB_ContV4 LbB_ContVot.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablStmt LbB_TablLO LbB_TablOS LbB_TablPT1 LbB_TablPT2 LbB_TablPT4 LbB_TablPT5 LbB_TablPT6.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablPT8 LbB_TablPT9 LbB_TablPT14 LbB_TablPT16.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section PT17.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps_bp H.

  Lemma pt_entry_pmem : forall (e : ptent H) k M errv,
    ppre H e ->
    munch [(p_lo e, pSP e); (as_FSB H, as_FSB H + AFS_FLAGS); (p_fp e, p_fp e + 1); (p_ff e, p_ff e + 64);
           (sh (p_ff e), sh (p_ff e) + 8)] (p_m e) M -> wmono asegs (p_m e) M -> mem_inv asegs M ->
    stk asegs M (p_lo e) (pSP e) -> ACONST (p_m e) ->
    rw_cells asegs (p_m e) (errno_addr (p_tp e)) [C4 errv] -> as_rauxv_ok H (p_m e) (p_B e) -> stack0 (p_m e) (p_lo e) (p_shi e) ->
    rw_cells asegs M (pSP e - 104) (psaved e) -> pslotsP e M ->
    rw_cells asegs M (p_ff e + 56) [C8 (Z_to_bv 64 (p_fp e))] -> wr_at asegs M (p_ff e) 8 -> wr_at asegs M (sh (p_ff e)) 8 ->
    wr_at asegs M (p_fp e) 1 -> wr_at asegs M (p_ff e + 32) 4 -> rw_cells asegs M (sh (p_ff e) + 4) [C1 (b8 k)] ->
    as_RFS H (pLF e) M ->
    vec32A (p_LB e) (p_m e) (p_v e) (p_b e) (p_xs e) (p_cap e) ->
    (0 < p_cap e -> SHAD (p_m e) (p_b e) (cc_gen (4 * p_cap e) (4 * Zlen (p_xs e)))) ->
    addressable (p_m e) (p_v e) 24 -> wr_at asegs (p_m e) (p_v e) 24 -> lb_own (p_LB e) (p_m e) ->
    pmem H e (p_xs e) k M (p_s e) (p_LB e) (p_b e) (p_cap e) (p_pid e) errv.
  Proof.
    intros e k M errv P MU WM MI ST AC ER RA S0 SV SL FPc WF WS WP WL KC RF VEC OSH ADV WV OWN.
    pose proof (rt_bp_base H HH) as HB.
    pose proof (pgeo_of H e P) as G.
    destruct G as (_ & S45 & _ & S1S & _ & SPH & CE & LO & F64 & FL & FH & P1 & P2 & P3 & P4 & FS1 & FS2 & SHF0 & SHF1 & SHF2 & SHF3
                   & FB & PB & V8 & VB & VL & VF & VFL & VFP & SV1 & SV2 & _ & TP).
    pose proof P as (FF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OLD & ND & RH & _ & _ & _ & _ & _ & _
                     & CX & B0C & BB & BD).
    pose proof FF as FF'. apply (osframe_facts H) in FF' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G10 & _).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    unfold PT_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO.
    set (W := [(p_lo e, pSP e); (as_FSB H, as_FSB H + AFS_FLAGS); (p_fp e, p_fp e + 1); (p_ff e, p_ff e + 64);
               (sh (p_ff e), sh (p_ff e) + 8)]) in MU.
    assert (SHA : sh (as_FSB H) <= sh (p_ff e) /\ sh (p_ff e + 64) <= sh (as_FSB H + AFS_SIZE))
      by (split; apply sh_mono; unfold AFS_SIZE in *; lia).
    assert (SHT : 0x800d5000 <= sh (p_ff e)) by (replace 0x800d5000 with (sh AIMG_TOP) by reflexivity; apply sh_mono; unfold AIMG_TOP in *; lia).
    pose proof (sh_lt_2_45 (p_ff e + 64) ltac:(lia)) as SB.
    assert (WA : Forall (aclient_write_ok H (p_LB e)) W).
    { apply Forall_cons; [left; cbn [fst]; lia|].
      apply Forall_cons; [right; right; right; right; left; cbn [fst snd]; unfold AFS_SIZE, AFS_FLAGS in *; lia|].
      apply Forall_cons; [right; right; right; right; left; cbn [fst snd]; unfold AFS_SIZE in *; lia|].
      apply Forall_cons; [right; right; right; right; left; cbn [fst snd]; unfold AFS_SIZE in *; lia|].
      apply Forall_cons; [right; right; right; right; right; left; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (WC : Forall aconst_ok W).
    { apply Forall_cons; [apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d5000 by reflexivity; cbn [fst]; lia | right; left; cbn [fst]; lia]|].
      apply Forall_cons; [eapply (LbB_SR.aconst_ok_app (as_FSB H) AFS_SIZE); [exact G10 | cbn; lia | cbn; unfold AFS_FLAGS, AFS_SIZE in *; lia]|].
      apply Forall_cons; [eapply (LbB_SR.aconst_ok_app (as_FSB H) AFS_SIZE); [exact G10 | cbn; lia | cbn; unfold AFS_SIZE in *; lia]|].
      apply Forall_cons; [eapply (LbB_SR.aconst_ok_app (as_FSB H) AFS_SIZE); [exact G10 | cbn; lia | cbn; unfold AFS_SIZE in *; lia]|].
      apply Forall_cons; [apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d5000 by reflexivity; cbn [fst]; lia | right; left; cbn [fst]; lia]|].
      apply Forall_nil. }
    assert (W0 : Forall stack0_ok W).
    { apply Forall_cons; [left; cbn [fst]; unfold AHI_LO; lia|].
      apply Forall_cons; [eapply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact G10 | lia | unfold AFS_FLAGS, AFS_SIZE in *; lia]|].
      apply Forall_cons; [eapply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact G10 | lia | unfold AFS_SIZE in *; lia]|].
      apply Forall_cons; [eapply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact G10 | lia | unfold AFS_SIZE in *; lia]|].
      apply Forall_cons; [right; cbn [snd]; assert (sh (p_ff e + 64) <= sh aceil) by (apply sh_mono; lia); lia | apply Forall_nil]. }
    pose proof VEC as (_ & _ & _ & LEN & BK & _).
    assert (BR : (p_b e = 0 /\ p_cap e = 0) \/ (0 < p_cap e /\ ablock_range H (p_b e) (4 * p_cap e) /\ p_b e mod 8 = 0)).
    { destruct BK as [(B0 & C0)|(B0 & B16 & C0 & BC & HIn & DJ)]; [left; split; assumption|].
      right. destruct OLD as [(X & _)|(_ & HIn')]; [lia|]. split; [lia|].
      split; [exact (ah_blocks H HB _ _ _ _ RH HIn')|]. clear - B16; Z.div_mod_to_equations; lia. }
    assert (F8 : p_ff e mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
    unfold pmem.
    split.
    { unfold pframe.
      split; [exact MI|]. split; [eapply ACONST_frame; [exact AC | exact MU | exact WM | exact WC]|]. split; [exact ST|].
      split; [eapply stack0_transport; [exact S0 | exact MU | exact WM | exact W0]|].
      split.
      { eapply rw_cells_transport; [exact ER | exact MU | exact WM |].
        assert (ERA : errno_addr (p_tp e) = ATP - 164) by (rewrite TP, HLib.u64_of_Z by (unfold ATP; lia); lia).
        rewrite ERA. unfold W, ATP. cbn. clear - CE ACF1 FS1 P1 SHF1 FL. unfold AFS_SIZE in *. repeat (split; [lia|]). exact I. }
      split; [eapply (ah_rauxv_frame H HB); [exact RA | exact MU | exact WM | exact WA]|].
      split; [exact SV|]. split; [exact SL|]. split; [exact FPc|]. split; [exact WF|]. split; [exact WS|]. split; [exact WP|].
      split; [exact WL|]. split; [exact KC|]. split; [exact RF|].
      split; [eapply (ah_RHEAP_frame H HB); [exact RH | exact MU | exact WM | exact WA]|].
      exact (lb_own_wmono _ _ _ OWN WM). }
    split.
    { unfold pvec. split.
      { eapply (vec32A_munch (p_LB e) (p_m e) M (p_v e) (p_b e) (p_xs e) (p_cap e) W VEC MU).
        - unfold W. cbn.
          destruct (pt_app_sh (p_v e) 24 (p_ff e) 64 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct VB; [left|right]; lia)) as [X|X];
            change (nsh 64) with 8 in X; clear - X VL VF VFL VFP; unfold AFS_FLAGS in *; (repeat (split; [lia|])); exact I.
        - destruct BR as [(B0 & C0)|(C0 & (A0 & A16 & An & AI & ACe & AF & AP) & B8)].
          + rewrite B0, C0 in *. assert (Zlen (p_xs e) = 0) by lia. rewrite H0. unfold W. cbn. clear - CE ACF1 FS1 P1 FL SHF1. repeat (split; [lia|]). exact I.
          + unfold W. cbn.
            destruct (pt_app_sh (p_b e) (4 * Zlen (p_xs e)) (p_ff e) 64 ltac:(lia) ltac:(lia) ltac:(lia)
                       ltac:(unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in AP; destruct AP; [left|right]; lia)) as [X|X];
              change (nsh 64) with 8 in X; clear - X LEN AF ACe CE P1 P2 P3 P4; unfold AFS_SIZE, AFS_FLAGS, AFS_HDR in *;
              (repeat (split; [lia|])); exact I. }
      split.
      { intros Hc. eapply SHAD_transport; [exact (OSH Hc) | exact MU | exact WM |].
        destruct BR as [(B0 & C0)|(C0 & (A0 & A16 & An & AI & ACe & AF & AP) & B8)]; [lia|].
        rewrite cc_gen_length by lia.
        assert (SHB : sh (p_b e) + nsh (4 * p_cap e) <= sh (p_b e + 4 * p_cap e) + 1) by (clear; unfold sh, nsh; Z.div_mod_to_equations; lia).
        pose proof (sh_lt_2_45 (p_b e + 4 * p_cap e) ltac:(lia)) as SB2.
        assert (D1 : sh (p_b e) + nsh (4 * p_cap e) <= as_FSB H \/ as_FSB H + AFS_SIZE <= sh (p_b e))
          by (apply aapp_disjoint_sh; [exact G10 | lia | unfold AAPP_HI; lia | lia]).
        assert (X : sh (p_b e) + nsh (4 * p_cap e) <= sh (p_ff e) \/ sh (p_ff e) + 8 <= sh (p_b e)).
        { destruct (pt_sh_apart (p_b e) (4 * p_cap e) (p_ff e) 64 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) B8 F8
                     ltac:(clear - AF P3 P4; unfold AFS_SIZE, AFS_HDR in *; lia)) as [X|X]; change (nsh 64) with 8 in X; [left | right]; lia. }
        unfold W. cbn. clear - X D1 P1 P2 P3 P4 FS1 SHB SB2 CE S45 LO ACF1. unfold AFS_SIZE, AFS_FLAGS, AFS_HDR in *.
        repeat (split; [lia|]). exact I. }
      split.
      { eapply addressable_transport; [exact ADV | exact MU | exact WM |]. change (nsh 24) with 3.
        assert (X : sh (p_v e) + 3 <= sh (p_ff e) \/ sh (p_ff e) + 8 <= sh (p_v e)).
        { destruct (pt_sh_apart (p_v e) 24 (p_ff e) 64 ltac:(destruct VB; lia) ltac:(lia) ltac:(lia) ltac:(lia) V8 F8
                     ltac:(clear - VF; destruct VF; lia)) as [X|X]; change (nsh 64) with 8 in X; change (nsh 24) with 3 in X; [left | right]; lia. }
        assert (D1 : sh (p_v e) + nsh 24 <= as_FSB H \/ as_FSB H + AFS_SIZE <= sh (p_v e))
          by (apply aapp_disjoint_sh; [exact G10 | destruct VB; lia | unfold AAPP_HI; destruct VB; lia | lia]).
        change (nsh 24) with 3 in D1.
        unfold W. cbn. clear - X D1 SV1 SV2 CE S45 LO ACF1 FS1 P1 P2 P3 P4. unfold AFS_SIZE, AFS_FLAGS in *. repeat (split; [lia|]). exact I. }
      split; [exact (wr_at_wmono _ _ _ _ WV WM)|].
      split; [exact OLD|]. left. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity. }
    split; [|rewrite closs_refl; lia].
    eapply (xpres_of_munch H (p_s e) (p_LB e) (pSP e) (pXE H e) W (p_m e) (p_m e) M); [exact HB | exact RH | exact MU | exact WM |].
    unfold W.
    apply Forall_cons; [left; cbn [fst snd]; split; [exact CE | lia]|].
    do 4 (apply Forall_cons; [right; intros a Ha; cbn [fst snd] in Ha; unfold pXE; cbn [rin_ivs]; right; apply rin_ivs_app; right;
                               unfold pXS; cbn [rin_ivs fst snd]; lia|]).
    apply Forall_nil.
  Qed.

  Lemma pmem_setk : forall (e : ptent H) ys k k' mL M sL LBi bi capi pidi eL,
    ppre H e -> pmem H e ys k mL sL LBi bi capi pidi eL ->
    munch [(sh (p_ff e) + 4, sh (p_ff e) + 5)] mL M -> wmono asegs mL M -> mem_inv asegs M -> stk asegs M (p_lo e) (pSP e) ->
    rw_cells asegs M (sh (p_ff e) + 4) [C1 (b8 k')] ->
    pmem H e ys k' M sL LBi bi capi pidi eL.
  Proof.
    intros e ys k k' mL M sL LBi bi capi pidi eL P PM MU WM MI ST KC.
    pose proof (rt_bp_base H HH) as HB.
    destruct PM as (PF & PV & XP & AL).
    pose proof PF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RH & _).
    pose proof (pgeo_of H e P) as G.
    destruct G as (_ & S45 & _ & S1S & _ & SPH & CE & LO & F64 & FL & FH & P1 & P2 & P3 & P4 & FS1 & FS2 & SHF0 & SHF1 & SHF2 & SHF3
                   & FB & PB & V8 & VB & VL & VF & _ & _ & SV1 & SV2 & (N0 & N48) & TP).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    split; [exact (pframe_setk H HH e k k' mL M sL LBi eL P PF MU WM MI ST KC)|].
    destruct (pvec_blk H HB e ys mL sL LBi bi capi pidi RH PV) as (LEN & BK & DJV).
    split.
    { eapply pvec_munch; [exact PV | exact MU | exact WM | | | |].
      - cbn. split; [|exact I]. destruct (pt_app_sh (p_v e) 24 (p_ff e) 64 ltac:(lia) ltac:(lia) ltac:(lia)
                                            ltac:(destruct VB; [left|right]; lia)) as [X|X]; change (nsh 64) with 8 in X; lia.
      - destruct BK as [(C0 & B0)|(C0 & HIn & (A0 & A16 & An & AI & ACe & AF & AP))]; [subst bi; cbn; split; [lia | exact I]|].
        cbn. split; [|exact I]. destruct (pt_app_sh bi (4 * Zlen ys) (p_ff e) 64 ltac:(lia) ltac:(lia) ltac:(lia)
                                   ltac:(unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in AP; destruct AP; [left|right]; lia)) as [X|X];
          change (nsh 64) with 8 in X; lia.
      - intros Hc. destruct BK as [(C0 & B0)|(C0 & HIn & (A0 & A16 & An & AI & ACe & AF & AP))]; [lia|].
        assert (B8 : bi mod 8 = 0) by (clear - A16; Z.div_mod_to_equations; lia).
        assert (F8 : p_ff e mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
        cbn. split; [|exact I].
        destruct (pt_sh_apart bi (4 * capi) (p_ff e) 64 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) B8 F8
                   ltac:(unfold AFS_SIZE, AFS_HDR in *; lia)) as [X|X]; change (nsh 64) with 8 in X; lia.
      - assert (F8 : p_ff e mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
        cbn. split; [|exact I]. change (nsh 24) with 3.
        destruct (pt_sh_apart (p_v e) 24 (p_ff e) 64 ltac:(destruct VB; lia) ltac:(lia) ltac:(lia) ltac:(lia) V8 F8
                   ltac:(destruct VF; lia)) as [X|X]; change (nsh 64) with 8 in X; change (nsh 24) with 3 in X; lia. }
    split; [|exact AL].
    pose proof P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RH0 & _).
    eapply (xpres_trans H); [exact XP|].
    eapply (xpres_of_munch H (p_s e) (p_LB e) (pSP e) (pXE H e) _ (p_m e) mL M); [exact HB | exact RH0 | exact MU | exact WM |].
    apply Forall_cons; [|apply Forall_nil]. right. intros a Ha. cbn [fst snd] in Ha.
    unfold pXE. cbn [rin_ivs]. right. apply rin_ivs_app. right. unfold pXS. cbn [rin_ivs fst snd]. lia.
  Qed.

  Lemma pt_entry_evt : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe)
      (pspan p v b cap : Z) (l xs : list Z) (pid : bptr) (lo B shi : Z) (errv : word),
    let SP := bv_unsigned sp in
    a0 = Z_to_bv 64 pspan -> a1 = Z_to_bv 64 v ->
    span_keep H LB LF SP ((v, v + 24) :: v4_oldx b (4 * cap)) m pspan p (Zlen l) -> pspan mod 8 = 0 ->
    (pspan + 16 <= v \/ v + 24 <= pspan) -> spanA p l -> Zlen l <= 48 -> Forall (fun t => 0 <= t < 2 ^ 31) l ->
    (pspan + 16 <= lo \/ SP <= pspan) -> relro0 m ->
    vec32A LB m v b xs cap -> v mod 8 = 0 -> addressable m v 24 -> obj_win H LB LF SP lo v 24 ->
    ((0x6e8000 <= v /\ v + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= v /\ v + 24 <= 2 ^ 47)) ->
    wr_at asegs m v 24 -> lb_own LB m -> v4_oldblk LB b cap pid -> (0 < cap -> SHAD m b (cc_gen (4 * cap) (4 * Zlen xs))) ->
    (4 * capmax (Zlen xs) cap (Zlen l) <= 2 ^ 26 /\ closs cap (capmax (Zlen xs) cap (Zlen l)) <= as_AL H s) ->
    lb_small LB + 3 * 64512 <= RT_SMALL_MAX ->
    Z.of_nat (length LB) + 2 <= RT_CNT_MAX -> nlarge LB + 2 <= RT_LARGE_MAX ->
    as_RHEAP H s LB m -> 0 <= as_AL H s -> trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_CREF] ->
    as_rauxv_ok H m B -> SP <= B -> SP mod 16 = 0 -> SP <= 2 ^ 47 ->
    stk asegs m lo SP -> aceil <= lo -> lo <= SP - PT_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> bv_unsigned ra mod 2 = 0 ->
    ACONST m -> as_RFS H LF m -> (length LF < AFS_MAXLIVE_BP)%nat -> stack0 m lo shi -> SP <= shi ->
    evt asegs (pt_epost H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF pspan p v b cap l xs pid lo B shi)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AT_PUSH_TYPES) fc None m (seg_rom asegs)).
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo s LB LF
      pspan p v b cap l xs pid lo B shi errv SP Ha0 Ha1 SPK PS8 PSD SPN N48 LR PSS RR VEC V8 ADV OBJ VB WV OWN OLD OSH BU1 BU2 BU3 BU4
      RH AL0 TRO RA SPB SP16 SP47 ST CE LO ER MI TP RA2 AC RF LFL S0 SHI.
    pose proof (rt_bp_base H HH) as HB. pose proof (rt_bp_ext H HH) as (SM0 & _).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    assert (LO' : lo <= SP - 224 - 1024 - 4096 - 8304) by (unfold PT_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO; lia).
    assert (Hsp : sp = Z_to_bv 64 SP) by (subst SP; symmetry; apply Z_to_bv_bv_unsigned).
    assert (SPE : bv_unsigned sp = SP) by reflexivity. clearbody SP.
    set (S1 := SP - 192 - SP mod 32).
    assert (S1b : SP - 223 <= S1 <= SP - 192 /\ S1 mod 32 = 0) by (subst S1; clear - SP16; Z.div_mod_to_equations; lia).
    assert (S1E : SP - 192 - SP mod 32 = S1) by reflexivity. clearbody S1.
    destruct (SPK [] m (Forall_nil _) AC MI ltac:(rewrite app_nil_r; apply xpres_refl)) as [_ ACS0].
    pose proof ACS0 as (PS0 & PS1 & _). unfold AAPP_HI in PS1.
    assert (V0 : 0 <= v /\ v + 24 <= 2 ^ 47) by (destruct VB; lia).

    eapply evt_cut.
    { eapply (pt_b1 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m pspan v lo);
        [exact Ha0 | lia | exact Ha1 | lia | rewrite SPE; exact SP16 | rewrite SPE; lia | rewrite SPE; exact ST | exact CE
        | rewrite SPE; lia | exact MI | exact AC]. }
    intros ms1 P1. destruct P1 as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1
                                   & EQ1 & MU1 & WM1 & MI1 & ST1 & CS1 & CS3).
    subst ms1. rewrite SPE in MU1, ST1, CS1, CS3 |- *. rewrite S1E in *.
    assert (X2 : as_FSB H + AFS_SIZE <= aceil) by (pose proof (ah_RFS_range H HB _ _ RF) as [(_ & X & _) _]; exact X).
    assert (X1 : aceil <= SP - 192) by (clear - CE LO'; lia).
    pose proof (stack_window_ok H LB LF (SP - 192) SP X1 X2) as (W1a & W1b & W1c).
    assert (RF1 : as_RFS H LF m1) by (eapply (ah_RFS_frame H HB); [exact RF | exact MU1 | exact WM1 | apply Forall_cons; [exact W1b | apply Forall_nil]]).
    assert (RH1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HB); [exact RH | exact MU1 | exact WM1 | apply Forall_cons; [exact W1a | apply Forall_nil]]).
    assert (AC1 : ACONST m1) by (eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 | apply Forall_cons; [exact W1c | apply Forall_nil]]).

    eapply evt_cut.
    { eapply (SM0 _ (Z_to_bv 64 S1)) with (LF := LF) (lo := lo);
        [exact RF1 | exact LFL | rewrite HLib.u64_of_Z by lia; exact (proj1 (stk_split asegs m1 lo S1 SP ST1 ltac:(lia)))
        | exact CE | rewrite HLib.u64_of_Z by lia; unfold AFS_STACK; lia | exact MI1 | exact TP | exact AC1 | exact (ah_thr H HB _ _ _ RH1)]. }
    intros ms2 P2.
    destruct P2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & ff & fp & j1 & j2
                    & EQ2 & MU2 & WM2 & MI2 & ST2 & RF2 & CF2 & SF2 & FP2 & AC2).
    subst ms2. rewrite HLib.u64_of_Z in MU2, ST2 by lia. unfold AFS_STACK in MU2.
    rewrite (ret_pc_even PT_SM_RET ltac:(unfold PT_SM_RET; lia) eq_refl).
    pose proof (fresh_of_RFS H HB LF 0 ff fp m2 RF2) as FFR.
    set (e := PTEnt H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF pspan p v b cap l xs pid lo B shi ff fp).
    assert (P : ppre H e).
    { pose proof SP16 as SP16'. pose proof SP47 as SP47'. pose proof SPB as SPB'. pose proof SHI as SHI'. pose proof LO as LOs.
      pose proof SPK as SPK'. pose proof OBJ as OBJ'.
      rewrite <- SPE in SP16', SP47', SPB', SHI', LOs, SPK', OBJ'.
      exact (pt_ppre_of H HH ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF pspan p v b cap l xs pid lo B shi ff fp
                  FFR LFL RF SP16' SP47' SPB' SHI' CE LOs TP RA2 SPK' PS8 PSD SPN N48 LR V8 VB OBJ' OLD VEC RH BU1 BU2 BU3 BU4 TRO AL0). }
    pose proof (pgeo_of H e P) as G.
    destruct G as (_ & S45 & _ & _ & _ & _ & _ & _ & F64 & FL & FH & P1 & P2 & P3 & P4 & FS1 & FS2 & SHF0 & SHF1 & SHF2 & SHF3
                   & FB & PB & _ & _ & VL & VF & VFL & VFP & SV1 & SV2 & (N0 & _) & _).
    assert (PSPE : pSP e = SP) by exact SPE.
    assert (PS1E : pS1 e = S1) by (unfold pS1; rewrite PSPE; exact S1E).
    assert (PNE : pn e = Zlen l) by reflexivity.
    rewrite ?PSPE, ?PS1E, ?PNE in *. cbn [p_sp p_ff p_fp p_v p_lo p_l e] in *.
    change (fsz 0) with 64 in MU2, CF2. change (fshn 0) with 8 in MU2, SF2. change (Z.to_nat (64 - 40)) with 24%nat in CF2.
    pose proof FFR as FFR'. apply (osframe_facts H) in FFR' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G10 & _).

    assert (ST2f : stk asegs m2 lo SP).
    { destruct (stk_split asegs m1 lo S1 SP ST1 ltac:(lia)) as [_ STu].
      assert (STu2 : stk asegs m2 S1 SP)
        by (eapply stk_transport_disjoint; [exact STu | exact MU2 | exact WM2 | cbn; unfold AFS_FLAGS, AFS_SIZE in *; clear - FS1 FS2 P1 P2 P3 P4 FL FH S1b LO' CE ACF1 ACF2 S45 SHF2; lia]).
      exact (stk_merge asegs m2 lo S1 SP ST2 STu2 ltac:(lia)). }
    assert (WF2 : wr_at asegs m2 ff 64) by (eapply rw_cells_wr_at; [exact CF2 | cbn; lia]).
    assert (WS2 : wr_at asegs m2 (sh ff) 8).
    { destruct SF2 as (_ & _ & (_ & W)).
      assert (L : Z.of_nat (length (poison_bytes (Z.to_nat 8) 0)) = 8) by reflexivity. rewrite L in W. exact W. }
    assert (CFP2 : rw_cells asegs m2 (ff + 56) [C8 (Z_to_bv 64 fp)]).
    { apply (rw_cells_app asegs m2 ff [CB 24 j1; C8 (Z_to_bv 64 S1); CB 24 j2] [C8 (Z_to_bv 64 fp)]) in CF2 as [_ CFb].
      cbn [cells_size csize] in CFb. change (Z.of_nat (24 + (8 + (24 + 0)))) with 56 in CFb. exact CFb. }
    assert (WP2 : wr_at asegs m2 fp 1) by (eapply rw_cells_wr_at; [exact FP2 | cbn; lia]).
    assert (D2 : forall A n, A + n <= S1 - 1024 \/ S1 <= A -> A + n <= as_FSB H \/ as_FSB H + AFS_SIZE <= A ->
                 A + n <= sh ff \/ sh ff + 8 <= A -> disjoint_from [(S1 - 1024, S1); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 64); (sh ff, sh ff + 8)] A n).
    { intros A n K1 K2 K3. cbn. unfold AFS_FLAGS, AFS_SIZE in *. clear - K1 K2 K3 P1 P2 P3 P4. lia. }
    assert (CS3' : rw_cells asegs m2 (S1 + 40) [C8 (Z_to_bv 64 v)]).
    { eapply rw_cells_transport; [exact CS3 | exact MU2 | exact WM2 |]. change (Z.of_nat (cells_size _)) with 8.
      apply D2; [lia | unfold AFS_SIZE in *; lia | lia]. }
    assert (RR2 : relro0 m2).
    { intros i Hi. rewrite (MU2 (Z_to_bv 64 i)); [rewrite (MU1 (Z_to_bv 64 i)); [apply RR; exact Hi|]|].
      - rewrite u64_of_Z by lia. cbn [outside]. lia.
      - rewrite u64_of_Z by lia. cbn [outside]. unfold AFS_FLAGS, AFS_SIZE in *. lia. }

    destruct (pt_b2a u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 gp tp s3 s4 s5 s6 s7 s9 s10 s11 F fc m2 (seg_rom asegs) ff SP S1 pspan v lo
                F64 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S45 ltac:(lia) SP47 WF2 WS2 ST2f ltac:(lia) ltac:(lia) CS3' RR2 MI2)
      as (R3 & m3 & RUN3 & ER3 & MU3 & WM3 & MI3 & ST3 & CS4 & KF3).
    eapply evt_of_msteps; [exact RUN3|].
    pose proof (msteps_full asegs _ _ RUN3 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)) as HF3.
    cbn [ms_regs] in HF3.
    assert (SHT : 0x800d5000 <= sh ff) by (replace 0x800d5000 with (sh AIMG_TOP) by reflexivity; apply sh_mono; unfold AIMG_TOP in *; lia).
    pose proof (sh_lt_2_45 (ff + 64) ltac:(lia)) as SB.
    assert (SHA : sh (as_FSB H) <= sh ff /\ sh (ff + 64) <= sh (as_FSB H + AFS_SIZE))
      by (split; apply sh_mono; unfold AFS_SIZE in *; lia).

    assert (AC3 : ACONST m3).
    { eapply ACONST_frame; [exact AC2 | exact MU3 | exact WM3 |].
      apply Forall_cons; [apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d5000 by reflexivity; cbn [fst]; lia | right; left; cbn [fst]; lia]|].
      apply Forall_cons; [eapply (LbB_SR.aconst_ok_app (as_FSB H) AFS_SIZE); [exact G10 | cbn; lia | cbn; unfold AFS_SIZE in *; lia]|].
      apply Forall_cons; [apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d5000 by reflexivity; cbn [fst]; lia | right; left; cbn [fst]; lia]|].
      apply Forall_nil. }
    assert (XW : forall a, (as_FSB H <= a < as_FSB H + AFS_FLAGS \/ fp <= a < fp + 1 \/ ff <= a < ff + 64 \/ sh ff <= a < sh ff + 8) ->
                 rin_ivs (pXE H e) a).
    { intros a Ha. unfold pXE. cbn [rin_ivs]. right. apply rin_ivs_app. right. unfold pXS. cbn [rin_ivs fst snd p_ff p_fp e]. clear - Ha. tauto. }
    assert (XP3 : xpres H LB SP (pXE H e) m m3).
    { eapply (xpres_trans H); [| eapply (xpres_trans H)].
      - eapply (xpres_of_munch H s LB SP (pXE H e) _ m m m1); [exact HB | exact RH | exact MU1 | exact WM1 |].
        apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil].
      - eapply (xpres_of_munch H s LB SP (pXE H e) _ m m1 m2); [exact HB | exact RH | exact MU2 | exact WM2 |].
        apply Forall_cons; [left; cbn [fst snd]; lia|].
        apply Forall_cons; [right; intros a Ha; apply XW; cbn [fst snd] in Ha; clear - Ha; tauto|].
        apply Forall_cons; [right; intros a Ha; apply XW; cbn [fst snd] in Ha; clear - Ha; tauto|].
        apply Forall_cons; [right; intros a Ha; apply XW; cbn [fst snd] in Ha; clear - Ha; tauto|].
        apply Forall_cons; [right; intros a Ha; apply XW; cbn [fst snd] in Ha; clear - Ha; tauto | apply Forall_nil].
      - eapply (xpres_of_munch H s LB SP (pXE H e) _ m m2 m3); [exact HB | exact RH | exact MU3 | exact WM3 |].
        apply Forall_cons; [left; cbn [fst snd]; lia|].
        apply Forall_cons; [right; intros a Ha; apply XW; cbn [fst snd] in Ha; lia|].
        apply Forall_cons; [right; intros a Ha; apply XW; cbn [fst snd] in Ha; clear - Ha; tauto | apply Forall_nil]. }
    destruct (SPK (pXS H e) m3 (fs_scratch_of_fresh H LF 0 ff fp FFR) AC3 MI3 XP3) as [CSp3 ACC3].
    apply (rw_cells_app asegs m3 pspan [C8 (Z_to_bv 64 p)] [C8 (Z_to_bv 64 (Zlen l))]) in CSp3 as [_ CN3].
    cbn [cells_size csize] in CN3. replace (pspan + Z.of_nat (8 + 0)) with (pspan + 8) in CN3 by lia.
    assert (SH3 : sh0 m3 (pspan + 8)).
    { apply sh0_of_acc8; [eapply accessible_sub; [exact ACC3 | lia | lia | lia] | clear - PS8; Z.div_mod_to_equations; lia]. }
    assert (CS3'' : rw_cells asegs m3 (S1 + 40) [C8 (Z_to_bv 64 v)]).
    { eapply rw_cells_transport; [exact CS3' | exact MU3 | exact WM3 |]. cbn. clear - FH CE S1b LO' SB S45 SHF0. lia. }

    rewrite ER3.
    destruct (pt_b2b u0 u1 u2 (getr R3 11) (getr R3 12) (getr R3 13) (getr R3 14) b7 u3 u4 u5 u6 gp tp s3 s4 s5 s6 s7 s9 s11
                F fc m3 (seg_rom asegs) ff SP S1 pspan v (Zlen l) lo F64 ltac:(lia) ltac:(lia) PS0 PS1 PS8
                ltac:(clear - VB; destruct VB; lia) V8 ltac:(lia) ltac:(lia) ltac:(lia) S45 ltac:(lia) SP47 ST3 ltac:(lia) CN3 SH3
                ltac:(clear - PSS S1b LO' CE; lia) MI3)
      as (R4 & m4 & RUN4 & MU4 & WM4 & MI4 & ST4 & C8a & C80 & K2 & K8 & K9 & K26 & K1 & K3 & K4 & K24 & K25 & NZ).
    eapply evt_of_msteps; [exact RUN4|].
    pose proof (msteps_full asegs _ _ RUN4 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)) as HF4.
    cbn [ms_regs] in HF4.

    pose proof (munch_app _ _ _ _ _ MU3 MU4) as MU34. cbn [app] in MU34.
    pose proof (wmono_trans asegs _ _ _ WM3 WM4) as WM34.
    assert (D4 : forall A n, A + n <= S1 \/ S1 + 88 <= A -> A + n <= ff \/ ff + 24 <= A -> A + n <= sh ff \/ sh ff + 8 <= A ->
                 disjoint_from [(S1, S1 + 8); (ff, ff + 24); (sh ff, sh ff + 8); (S1 + 8, S1 + 40); (S1 + 48, S1 + 64); (S1 + 80, S1 + 88)] A n).
    { intros A n Y1 Y2 Y3. cbn. clear - Y1 Y2 Y3. lia. }
    assert (PM4 : pmem H e xs 0xf8 m4 s LB b cap pid errv).
    { apply (pt_entry_pmem e 0xf8 m4 errv P);
        cbv beta iota zeta delta [psaved pslotsP pslots_lo pslots pS1 pSP pn pLF p_ra p_sp p_gp p_tp p_s0 p_s1 p_s2 p_s3 p_s4 p_s5
             p_s6 p_s7 p_s8 p_s9 p_s10 p_s11 p_F p_fc p_m p_mo p_s p_LB p_LF p_ps p_p p_v p_b p_cap p_l p_xs p_pid p_lo p_B p_shi p_ff p_fp e];
        rewrite ?SPE, ?S1E.
      - apply (munch_trans _ m m1 m4); [eapply munch_weaken; [|exact MU1]; intros z Hz; cbn [outside] in Hz |- *; clear - Hz LO'; lia|].
        apply (munch_trans _ m1 m2 m4); [eapply munch_weaken; [|exact MU2]; intros z Hz; cbn [outside] in Hz |- *; clear - Hz LO' S1b; lia|].
        eapply munch_weaken; [|exact MU34]; intros z Hz; cbn [outside] in Hz |- *; clear - Hz LO' S1b SHF0 SB S45; lia.
      - exact (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _ WM1 WM2) WM34).
      - exact MI4.
      - exact ST4.
      - exact AC.
      - exact ER.
      - exact RA.
      - exact S0.
      - eapply rw_cells_transport; [| exact MU34 | exact WM34 | change (Z.of_nat (cells_size _)) with 104; apply D4;
            [clear - S1b; lia | clear - FH CE LO' S1b; lia | clear - SHF0 SB S45 S1b; lia]].
        eapply rw_cells_transport; [exact CS1 | exact MU2 | exact WM2 | change (Z.of_nat (cells_size _)) with 104; apply D2;
            [clear - S1b; lia | clear - X2 CE LO'; unfold AFS_SIZE in *; lia | clear - SHF0 SB S45 S1b; lia]].
      - split.
        + apply rw_cells_cons8_c; [|exact C8a].
          eapply rw_cells_transport; [exact CS4 | exact MU4 | exact WM4 | cbn; clear - S1b; lia].
        + intros N00. destruct (NZ N00) as (C16 & C48 & _).
          apply (proj2 (rw_cells_app asegs m4 (S1 + 16) [C8 (Z_to_bv 64 (sh v)); C8 (Z_to_bv 64 (sh (v + 16))); C8 (Z_to_bv 64 (v + 16))]
                          [C8 (Z_to_bv 64 v); C8 (Z_to_bv 64 (2 ^ 61)); C8 (Z_to_bv 64 (sh pspan))])).
          split; [exact C16|]. cbn [cells_size csize]. replace (S1 + 16 + Z.of_nat (8 + (8 + (8 + 0)))) with (S1 + 40) by lia.
          apply rw_cells_cons8_c; [eapply rw_cells_transport; [exact CS3'' | exact MU4 | exact WM4 | cbn; clear - S1b; lia]|].
          replace (S1 + 40 + 8) with (S1 + 48) by lia. exact C48.
      - eapply rw_cells_transport; [exact CFP2 | exact MU34 | exact WM34 | change (Z.of_nat (cells_size _)) with 8; apply D4;
            [clear - FH CE LO' S1b; lia | clear - S1b; lia | clear - FB SHF1 SHF2; lia]].
      - exact (LbB_Own.wr_at_wmono m2 m4 ff 8 ltac:(eapply os_wr_at_sub; [exact WF2 | lia | lia | lia]) WM34).
      - exact (LbB_Own.wr_at_wmono m2 m4 _ 8 WS2 WM34).
      - exact (LbB_Own.wr_at_wmono m2 m4 _ 1 WP2 WM34).
      - exact (LbB_Own.wr_at_wmono m2 m4 (ff + 32) 4 ltac:(eapply os_wr_at_sub; [exact WF2 | lia | lia | lia]) WM34).
      - eapply rw_cells_transport; [exact KF3 | exact MU4 | exact WM4 | cbn; clear - SHF0 SB S45; lia].
      - assert (XA0 : aceil <= S1) by (clear - CE LO' S1b; lia).
        assert (XA1 : aceil <= S1 + 8) by (clear - XA0; lia). assert (XA2 : aceil <= S1 + 48) by (clear - XA0; lia).
        assert (XA3 : aceil <= S1 + 80) by (clear - XA0; lia).
        pose proof (stack_window_ok H LB ((0, ff, fp) :: LF) S1 (S1 + 8) XA0 X2) as (_ & Wa & _).
        pose proof (stack_window_ok H LB ((0, ff, fp) :: LF) (S1 + 8) (S1 + 40) XA1 X2) as (_ & Wb & _).
        pose proof (stack_window_ok H LB ((0, ff, fp) :: LF) (S1 + 48) (S1 + 64) XA2 X2) as (_ & Wc & _).
        pose proof (stack_window_ok H LB ((0, ff, fp) :: LF) (S1 + 80) (S1 + 88) XA3 X2) as (_ & Wd & _).
        eapply (ah_RFS_frame H HB); [exact RF2 | exact MU34 | exact WM34 |].
        apply Forall_cons; [exact Wa|].
        apply Forall_cons; [right; exists (0, ff, fp); split; [left; reflexivity | cbn; change (fsz 0) with 64; clear - S1b; lia]|].
        apply Forall_cons; [left; cbn [fst snd]; split; [clear - SHF3; unfold AFS_SIZE in *; lia | right; clear - SHF1; unfold ATLS_PRIV_HI, ATP; lia]|].
        apply Forall_cons; [exact Wb|]. apply Forall_cons; [exact Wc|]. apply Forall_cons; [exact Wd | apply Forall_nil].
      - exact VEC.
      - exact OSH.
      - exact ADV.
      - exact WV.
      - exact OWN. }

    destruct (Z.eqb_spec (Zlen l) 0) as [N00|N00].
    - apply evt_done. exists ff, fp, R4, m4, 0xf8, errv. cbv zeta.
      rewrite (proj2 (Z.eqb_eq (Zlen l) 0) N00).
      split; [reflexivity|]. split; [exact HF4|]. split; [exact K3|]. split; [exact K4|].
      split; [intros X; exfalso; exact (X N00)|].
      split; [intros _; cbv beta iota zeta delta [pSP pS1 p_sp]; rewrite SPE, S1E; split; [exact K8|]; split; [exact K9 | exact K26]|].
      split; [exact FFR|]. exact PM4.
    - destruct (NZ N00) as (C16 & C48 & K10 & K11 & K12 & K13 & K15 & K16 & K18 & K19 & K20 & K21 & K22 & K23 & K27).
      assert (PX4 : PTX R4 SP S1 ff pspan v (Zlen l) 0).
      { unfold PTX. change (0 + 1) with 1. repeat (split; [assumption|]). exact K27. }
      destruct (pt_r0 R4 F fc m4 (seg_rom asegs) SP S1 ff pspan v (Zlen l) 0 PX4 K10 K11 F64 ltac:(clear - FL; lia) ltac:(clear - FH CE LO' SP47; lia)
                  (LbB_Own.wr_at_wmono m2 m4 _ 8 WS2 WM34) S45 ltac:(clear - S1b; lia) SP47 C48)
        as (R5 & M5 & RUN5 & PH5 & KK5 & MU5 & WM5 & SK5 & MI5 & KC5).
      eapply evt_of_msteps_done; [exact RUN5|].
      exists ff, fp, R5, M5, 4, errv. cbv zeta.
      rewrite (proj2 (Z.eqb_neq (Zlen l) 0) N00).
      split; [reflexivity|]. split; [exact (msteps_full asegs _ _ RUN5 HF4)|].
      split; [rewrite (KK5 3%bv ltac:(inb)); exact K3|]. split; [rewrite (KK5 4%bv ltac:(inb)); exact K4|].
      split; [intros _; split; [cbv beta iota zeta delta [pSP pS1 p_sp]; rewrite SPE, S1E; exact PH5 | reflexivity]|].
      split; [intros X; exfalso; exact (N00 X)|].
      split; [exact FFR|].
      apply (pmem_setk e xs 0xf8 4 m4 M5 s LB b cap pid errv P PM4 MU5 WM5 (MI5 MI4)).
      + cbv beta iota zeta delta [p_lo pSP p_sp e]. rewrite SPE. exact (SK5 _ _ ST4).
      + exact KC5.
  Qed.

  Theorem push_types_okA : push_types_stmtA H.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LB LF
      pspan p v b cap l xs pid lo B shi errv VIS Ha0 Ha1 SPK PS8 PSD SPN N48 LR PSS RR PRE.
    pose proof (rt_bp_base H HH) as HB.
    destruct PRE as (VEC & V8 & ADV & OBJ & VB & WV & OWN & OLD & OSH & BU1 & BU2 & BU3 & BU4 & RH & KR & AL0 & TRO & TRO2
                     & RA & SPB & SP16 & SP47 & ST & CE & LO & ER & MI & TP & RA2 & AC & RF & LFL & S0 & SHI).
    eapply (ahh_evt_then H HB _ _ s msF _ mo KR VIS).
    { exact (pt_entry_evt ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo s LB LF
               pspan p v b cap l xs pid lo B shi errv Ha0 Ha1 SPK PS8 PSD SPN N48 LR PSS RR VEC V8 ADV OBJ VB WV OWN OLD OSH BU1 BU2 BU3 BU4
               RH AL0 TRO RA SPB SP16 SP47 ST CE LO ER MI TP RA2 AC RF LFL S0 SHI). }
    intros msF' mo' KR' MP' POST.
    exact (pt_after_entry H HH ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF pspan p v b cap l xs pid lo B shi msF' mo'
             LFL RF SP16 SP47 SPB SHI CE LO TP RA2 SPK PS8 PSD SPN N48 LR V8 VB OBJ OLD VEC RH BU1 BU2 BU3 BU4 TRO AL0 KR' MP' POST).
  Qed.
End PT17.
