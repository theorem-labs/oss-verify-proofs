(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_VecT LbB_VecD1 LbB_VecD2.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Section VecD.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis HANN : annotate_gen_stmt.

  Lemma vd_pre : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Dd V P n lo shi : Z),
    a0 = Z_to_bv 64 Dd ->
    rw_cells asegs m Dd [C8 (wz V)] -> Dd mod 8 = 0 -> bv_unsigned sp <= Dd -> Dd + 8 <= shi -> stack0 m lo shi ->
    rw_cells asegs m V [C8 (wz P); C8 (wz (P + 4 * n)); C8 (wz (P + 4 * n))] -> SHAD m V (repeat (b8 0) 3) -> V mod 8 = 0 ->
    aapp V 24 -> (V + 24 <= bv_unsigned sp - VD_STACK \/ bv_unsigned sp <= V) ->
    1 <= n <= 2 ^ 24 -> aapp P (4 * n) -> P mod 16 = 0 -> SHAD m P (shadow_of (4 * n)) -> (P + 4 * n <= V \/ V + 24 <= P) ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - VD_STACK ->
    bv_unsigned sp mod 16 = 0 -> 2 ^ 45 <= bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m -> ACONST m ->
    evt asegs (fun ms' => exists t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
        ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 (4 * n)) a2' a3' a4' a5' a6' a7'
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 AOPDEL2) fc None m' (seg_rom asegs)
        /\ munch [(bv_unsigned sp - VD_STACK, bv_unsigned sp); (sh P, sh P + nsh (4 * n)); (V + 8, V + 16)] m m'
        /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
        /\ SHAD m' P (shadow_of (4 * n)) /\ ACONST m' /\ stack0 m' lo shi
        /\ rw_cells asegs m' V [C8 (wz P); C8 (wz P); C8 (wz (P + 4 * n))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VDESTROY) fc None m (seg_rom asegs)).
  Proof.
    intros until shi. intros Ha0 CD D8 DSP DHI S0 CV SV V8 VA VAP Hn PA P16 SP PVD ST CE LO SP16 SPR MI AC.
    eapply evt_cut; [eapply vd_a; eassumption|].
    intros ms2 (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m2 & EQ & MU & WM & MI2 & ST2 & CV2 & CD2
                & CF2 & SV2 & S02 & SH2 & AC2).
    subst ms2.
    eapply evt_mono; [eapply vd_b; eassumption|].
    intros ms' (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & EQ' & MU' & WM' & MI' & ST' & SH'
                & AC' & S0' & CV').
    exists t0', t1', t2', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact EQ'|].
    split.
    { eapply munch_weaken; [| exact (munch_app _ _ _ _ _ MU MU')].
      unfold VD_STACK, AINTRIN_STACK. intros x Hx; cbn [app outside] in Hx |- *; lia. }
    split; [exact (wmono_trans asegs _ _ _ WM WM')|].
    repeat (split; [assumption|]). assumption.
  Qed.

  Lemma lb_remove_notin : forall p LB b, List.NoDup (map blk_id LB) -> In b (as_lb_remove H p LB) -> blk_id b <> p.
  Proof.
    pose proof (ah_lb_remove H HH) as (L1 & L2 & L3).
    intros p LB. induction LB as [|b0 LB IH]; intros b ND Hb.
    - exfalso. exact (L3 p [] b Hb).
    - cbn [map] in ND. inversion ND as [|? ? NI ND']; subst.
      destruct (Z.eq_dec (blk_id b0) p) as [E|E].
      + destruct b0 as [[p0 A0] n0]. unfold blk_id in E. cbn [fst] in E. subst p0.
        assert (E2 : as_lb_remove H p ((p, A0, n0) :: LB) = LB) by (apply L1; exact NI).
        assert (Hb2 : In b LB) by (rewrite <- E2; exact Hb).
        intros Eb. apply NI. unfold blk_id at 1. cbn [fst]. rewrite <- Eb. apply in_map. exact Hb2.
      + rewrite (L2 p b0 LB E) in Hb. destruct Hb as [<-|Hb]; [exact E | exact (IH b ND' Hb)].
  Qed.

  Lemma xpres_of_munch_rm : forall s LB pid A n SP X W m0 m m',
    as_RHEAP H s LB m0 -> In (pid, A, n) LB -> aceil <= SP ->
    munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => (aceil <= fst iv /\ snd iv <= SP) \/ (sh A <= fst iv /\ snd iv <= sh A + nsh n)
                              \/ (forall a, fst iv <= a < snd iv -> rin_ivs X a)) W ->
    xpres H (as_lb_remove H pid LB) SP X m m'.
  Proof.
    intros s LB pid A n SP X W m0 m m' RH IN HSP MU WM FW a Ha [Hc Hx].
    pose proof (ah_blocks H HH _ _ _ _ RH IN) as (R0 & R16 & Rn & RI & RC & RF & RAPP).
    unfold blk_addr, blk_size in R0, R16, Rn, RI, RC, RF, RAPP. cbn [fst snd] in R0, R16, Rn, RI, RC, RF, RAPP.
    pose proof (ah_fsb H HH _ _ _ RH) as (F1 & F2 & F3 & F4).
    pose proof (ah_nodup H HH _ _ _ RH) as ND.
    pose proof aceil_facts as ACF.
    assert (SHA : sh A + nsh n <= sh aceil) by (unfold sh, nsh; acb; Z.div_mod_to_equations; nia).
    assert (SHB : sh aceil < 0x10007fff8000) by (unfold sh; rewrite ASHADOW_BASE_val; acb; Z.div_mod_to_equations; lia).
    unfold AIMG_TOP in RI.
    assert (SHL : 0x7fff7000 < sh A) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (CLS : SP <= a \/ (a < aceil /\ ~ (sh A <= a < sh A + nsh n))).
    { unfold aclient_addr in Hc.
      destruct Hc as [Hc|[Hc|[(b & Hb & Hr)|[(b & Hb & Hr)|[Hc|[Hc|Hc]]]]]].
      - left. exact Hc.
      - right. unfold aimg_client in Hc. acb. destruct Hc as [Hc|[Hc|[Hc|Hc]]]; (split; [lia | lia]).
      - right. pose proof (ah_lb_remove H HH) as (_ & _ & L3).
        pose proof (ah_blocks H HH _ _ _ b RH (L3 _ _ _ Hb)) as (Q0 & Q16 & Qn & QI & QC & QF & QAPP).
        assert (HI2 : sh A + nsh n <= AHI_LO) by (apply sh_nsh_high; unfold AAPP_HI; acb; lia).
        destruct b as [[pb Ab] nb]. unfold blk_addr, blk_size in *. cbn [fst snd] in *.
        unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in QAPP, HI2. acb.
        destruct QAPP as [QAPP|QAPP]; split; lia.
      - right. pose proof (ah_lb_remove H HH) as (_ & _ & L3).
        pose proof (L3 _ _ _ Hb) as Hb'.
        pose proof (lb_remove_notin pid LB b ND Hb) as Hid.
        pose proof (ah_disj H HH _ _ _ (pid, A, n) b RH IN Hb' (fun E => Hid (eq_sym E))) as D.
        pose proof (ah_blocks H HH _ _ _ b RH Hb') as (Q0 & Q16 & Qn & QI & QC & QF & QAPP).
        unfold blk_addr, blk_size in D, Hr, Q0, Q16, Qn, QI, QC, QF, QAPP. cbn [fst snd] in D.
        destruct b as [[pb Ab] nb]. cbn [fst snd] in *.
        unfold aapp, aapp_lo, aapp_hi in RAPP, QAPP. acb.
        unfold nsh, sh, AHI_LO, ALOWSH_LO, AIMG_TOP in *. rewrite ASHADOW_BASE_val in *.
        clear MU WM FW. Z.div_mod_to_equations.
        destruct D as [D|D]; split; try lia.
      - right. assert (HI2 : sh A + nsh n <= AHI_LO) by (apply sh_nsh_high; unfold AAPP_HI; acb; lia).
        unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in F4, HI2. unfold AFS_SIZE in *. acb.
        destruct RF as [RF|RF]; destruct F4 as [F4|F4]; split; lia.
      - right. unfold aapp, aapp_lo, aapp_hi in RAPP, F4. acb.
        unfold sh, nsh, AFS_SIZE, AHI_LO, ALOWSH_LO, AIMG_TOP in *. rewrite ASHADOW_BASE_val in *. clear MU WM FW.
        Z.div_mod_to_equations.
        destruct RF as [RF|RF]; split; lia.
      - right. acb. unfold AHI_LO in Hc. split; lia. }
    assert (OUT : outside W a).
    { clear MU WM. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
      pose proof (Forall_inv FW) as H1. cbn in H1.
      split; [| apply IH; apply (Forall_inv_tail FW)].
      destruct H1 as [[H1 H2]|[[H1 H2]|H1]].
      - destruct CLS as [C|(C1 & C2)]; lia.
      - destruct CLS as [C|(C1 & C2)]; [acb; lia | intros K; apply C2; lia].
      - intros K. apply Hx. apply H1. exact K. }
    split.
    - unfold wa. apply MU. rewrite unsigned_lit by lia. exact OUT.
    - intros Hw. apply WM. exact Hw.
  Qed.

  Definition vdestroy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (pv : bptr) (V P n lo shi B : Z) (errv : word) (m : mem) (mo : Model)
      : config -> Prop :=
    fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ as_rauxv_ok H m' B
      /\ xpres H (as_lb_remove H pv LB) (bv_unsigned sp) [(V + 8, V + 16)] m m'
      /\ as_RHEAP H s' (as_lb_remove H pv LB) m' /\ ACONST m' /\ as_RFS H LF m' /\ stack0 m' lo shi
      /\ rw_cells asegs m' V [C8 (wz P); C8 (wz P); C8 (wz (P + 4 * n))]
      /\ as_AL H s' >= as_AL H s - as_Cf H (4 * n).

  Lemma vdestroy_sr : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H) (LB : list block) (LF : list fframe)
      (pv : bptr) (Dd V P n lo shi B : Z) (errv : word) (mo : Model) (CH : list (Z * Z)) (bs : list byte),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 VDESTROY) fc None m (seg_rom asegs) ->
    a0 = Z_to_bv 64 Dd ->
    rw_cells asegs m Dd [C8 (wz V)] -> Dd mod 8 = 0 -> bv_unsigned sp <= Dd -> Dd + 8 <= shi -> stack0 m lo shi ->
    rw_cells asegs m V [C8 (wz P); C8 (wz (P + 4 * n)); C8 (wz (P + 4 * n))] -> SHAD m V (repeat (b8 0) 3) -> V mod 8 = 0 ->
    aapp V 24 -> V + 24 <= bv_unsigned sp - VD_STACK ->
    aclient_write_ok H LB (V + 8, V + 16) -> afs_write_ok H LF (V + 8, V + 16) -> (P + 4 * n <= V \/ V + 24 <= P) ->
    aclient_range H (as_lb_remove H pv LB) (bv_unsigned sp) V 24 ->
    1 <= n <= 2 ^ 24 -> In (pv, P, 4 * n) LB -> rw_cells asegs m P [CB (Z.to_nat (4 * n)) bs] -> addressable m P (4 * n) ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> as_Cf H (4 * n) <= as_AL H s ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned sp mod 16 = 0 -> 2 ^ 45 <= bv_unsigned sp <= 2 ^ 47 -> ACONST m -> as_RFS H LF m ->
    as_chain H m (bv_unsigned s0) CH -> trace_ok (as_TR H) APC0_FREE (bv_unsigned ra :: map snd CH) ->
    (forall fp ra', In (fp, ra') CH -> bv_unsigned sp + 16 <= fp) ->
    as_SR H (vdestroy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF pv V P n lo shi B errv m mo) (mkCfg msF mo).
  Proof.
    intros until bs. intros VIS Ha0 CD D8 DSP DHI S0 CV SV V8 VA VAP VWO VFS PVD VCL Hn INB CBP ADDR RH KR CF RA SPB ST CE LO ERR MI TP SP16 SPR AC RF
      CHN TRC CHUP.
    set (spz := bv_unsigned sp) in *.
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    unfold AFREE_STACK in LO.
    pose proof (ah_blocks H HH _ _ _ _ RH INB) as ABR. unfold blk_addr, blk_size in ABR. cbn [fst snd] in ABR.
    pose proof ABR as (B0 & B16 & Bn & BI & BC & BF & BAPP). unfold AIMG_TOP in BI.

    eapply (ahh_evt_then H HH); [exact KR | exact VIS | |].
    { eapply vd_pre; try eassumption; unfold VD_STACK, AINTRIN_STACK in *; try lia; exact (proj2 ADDR). }
    intros msF1 mo1 KR1 MP1 POST1.
    destruct POST1 as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & VIS1 & MU1 & WM1 & MI1 & ST1 & SH1
                       & AC1 & S01 & CV1).
    unfold VD_STACK, AINTRIN_STACK in MU1.

    assert (SPH : sh P + nsh (4 * n) <= 0x10007fff8000)
      by (pose proof (sh_nsh_high P (4 * n) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as X; unfold AHI_LO in X; exact X).
    assert (SVP : sh P + nsh (4 * n) <= V \/ V + 24 <= sh P)
      by (apply (aapp_disjoint_sh V 24 P (4 * n) VA); unfold AAPP_HI; lia).
    pose proof (aapp_bounds V 24 VA ltac:(lia)) as (VB1 & VB2 & VB3 & VB4 & VB5).
    assert (W1 : Forall (aclient_write_ok H LB) [(spz - (48 + 4096), spz); (sh P, sh P + nsh (4 * n)); (V + 8, V + 16)]).
    { apply Forall_cons; [left; cbn; lia|].
      apply Forall_cons; [right; right; right; left; exists (pv, P, 4 * n); split; [exact INB | cbn; lia]|].
      apply Forall_cons; [exact VWO | apply Forall_nil]. }
    assert (RH1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact RH | exact MU1 | exact WM1 | exact W1]).
    assert (RA1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact RA | exact MU1 | exact WM1 | exact W1]).
    assert (SHL : 0x7fff8000 <= sh P) by (unfold sh, ASHADOW_BASE; pose proof (Z.div_pos P 8 ltac:(lia) ltac:(lia)); lia).
    assert (ERR1 : rw_cells asegs m1 (errno_addr tp) [C4 errv]).
    { subst tp. unfold errno_addr in ERR |- *. rewrite u64_of_Z in ERR |- * by (unfold ATP; lia).
      eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 | cbn; unfold ATP; unfold AIMG_TOP in VB1; lia]. }
    assert (CB1 : rw_cells asegs m1 P [CB (Z.to_nat (4 * n)) bs]).
    { eapply rw_cells_transport; [exact CBP | exact MU1 | exact WM1 |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. cbn.
      unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in BAPP. destruct BAPP; lia. }
    assert (RF1 : as_RFS H LF m1).
    { eapply (ah_RFS_frame H HH); [exact RF | exact MU1 | exact WM1 |].
      pose proof (ah_fsb H HH _ _ _ RH) as FSBOK.
      apply Forall_cons; [left; cbn; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP; destruct FSBOK as (F1 & F2 & F3 & F4); unfold AFS_SIZE in *; lia|].
      apply Forall_cons.
      { left. cbn. pose proof (ah_fsb H HH _ _ _ RH) as (F1 & F2 & F3 & F4).
        pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE P (4 * n) F4 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as S.
        unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP. assert (0x7fff7000 < sh P) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
        split; lia. }
      apply Forall_cons; [exact VFS | apply Forall_nil]. }
    assert (CHN1 : as_chain H m1 (bv_unsigned s0) CH).
    { eapply (chain_via_munch H HH); [exact CHN | exact MU1 |]. intros fp ra' IN. pose proof (CHUP fp ra' IN) as U. cbn. lia. }

    eapply (ah_mono H HH).
    { eapply (ah_opdel2 H HH) with (LB := LB) (p := pv) (A := P) (n := 4 * n) (lo := lo) (B := B) (errv := errv) (CH := CH) (sbs := shadow_of (4 * n));
        [exact VIS1 | exact RH1 | exact KR1 | exact INB | exact CF | exact CB1 | exact SH1 | rewrite shadow_of_length by lia; reflexivity
        | exact RA1 | exact SPB | exact ST1 | exact CE | unfold AFREE_STACK; lia | exact ERR1 | exact MI1 | exact TP | exact SP16 | exact AC1
        | exact CHN1 | exact TRC | reflexivity ]. }
    intros c POST. destruct POST as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m' & s'
                                     & V' & K' & MP' & MI' & ST' & ERR' & RA' & AP' & RH' & AC' & AL').
    exists t0'', t1'', t2'', a0'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', t3'', t4'', t5'', t6'', m', s'.
    split; [exact V'|]. split; [exact K'|]. split; [eapply (ah_mpres_trans H HH); [exact MP1 | exact MP']|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact RA'|].
    split.
    { eapply xpres_trans; [| exact (xpres_of_apres H _ _ _ _ _ AP')].
      eapply (xpres_of_munch_rm s LB pv P (4 * n) spz [(V + 8, V + 16)] _ m); [exact RH | exact INB | lia | exact MU1 | exact WM1 |].
      apply Forall_cons; [left; cbn; lia|].
      apply Forall_cons; [right; left; cbn; lia|].
      apply Forall_cons; [right; right; intros a Ha; cbn; left; exact Ha | apply Forall_nil]. }
    split; [exact RH'|]. split; [exact AC'|].
    assert (FRM : forall a, 0 <= a < 2 ^ 64 -> (as_FSB H <= a < as_FSB H + AFS_SIZE \/ ATLS_PRIV_LO <= a < ATLS_PRIV_HI
                             \/ sh (as_FSB H) <= a < sh (as_FSB H + AFS_SIZE)) ->
                   m' (wa a) = m1 (wa a) /\ (wview asegs m1 (wa a) <> None -> wview asegs m' (wa a) <> None)).
    { intros a Ha Hr. apply (AP' a Ha). unfold aclient_addr. destruct Hr as [Hr|[Hr|Hr]].
      - right; right; right; right; left; exact Hr.
      - right; left. unfold aimg_client, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *. right; right; right; lia.
      - right; right; right; right; right; left; exact Hr. }
    split; [eapply (ah_RFS_ext H HH); [exact RF1 | exact FRM]|].
    split; [eapply (stack0_xpres H); [exact (xpres_of_apres H _ _ [] _ _ AP') | exact S01 | apply Forall_nil]|].
    split; [eapply (apres_rw_cells H); [exact AP' | exact CV1 | exact VCL]|].
    exact AL'.
  Qed.

  Lemma vdestroy0_evt : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Dd V lo shi : Z),
    a0 = Z_to_bv 64 Dd ->
    rw_cells asegs m Dd [C8 (wz V)] -> Dd mod 8 = 0 -> bv_unsigned sp <= Dd -> Dd + 8 <= shi -> stack0 m lo shi ->
    rw_cells asegs m V [C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> SHAD m V (repeat (b8 0) 3) -> V mod 8 = 0 -> aapp V 24 ->
    (V + 24 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= V) ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 32 ->
    bv_unsigned sp mod 16 = 0 -> 2 ^ 45 <= bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m -> ACONST m ->
    evt asegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
        ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (ret_pc ra) fc None m' (seg_rom asegs)
        /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ stk asegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VDESTROY) fc None m (seg_rom asegs)).
  Proof.
    intros until shi. intros Ha0 CD D8 DSP DHI S0 CV SV V8 VA VAP ST CE LO SP16 SPR MI AC.
    set (spz := bv_unsigned sp) in *.
    assert (Hsp : sp = Z_to_bv 64 spz) by (subst spz; symmetry; apply Z_to_bv_bv_unsigned).
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof (stack0_bounds m lo shi S0) as SB0. unfold AAPP_HI in SB0.
    pose proof (aapp_bounds V 24 VA ltac:(lia)) as (VB1 & VB2 & VB3 & VB4 & VB5). unfold AIMG_TOP in VB1.
    remember (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 Dd; Z_to_bv 64 spz; Z_to_bv 64 V]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; try reflexivity; [exact Ha0 | exact Hsp]. }
    pose proof (ACONST_shbase m AC) as [CG CS].
    assert (GZV : gz m V 24) by (intros i Hi; eapply sh0_of_SHAD0; [exact SV | cbn; lia]).
    assert (SDD : sh0 m Dd) by (eapply sh0_of_stack0; [exact S0 | lia]).
    assert (HK : know_ok asegs E m
       (kn_fix 20 [0xe8f84] (SCR [] [] []) VDESTROY (srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33)])
       [ KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL);
         KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit 0x7fff8000);
         KWord (SA (EVar 32) 0) 8 (EVar 34);
         KWord (SA (EVar 34) 0) 8 (ELit 0);
         KWr (SA (EVar 33) (-32)) (ELit 32);
         KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) (2 ^ 45) (2 ^ 47); KRange (EVar 34) 0x6e8000 (2 ^ 47); KAlign (EVar 34) 8;
         KDisj (SA (EVar 32) 0) (ELit 8) (SA (EVar 33) (-32)) (ELit 32) ] 40)).
    { kn_eval. unfold know_ok.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m 0x1850a0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m 0x191038 _ 0%nat (C8 (wz ASHADOW_BASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons. { kword_cell CD 0%nat (C8 (wz V)). }
      apply Forall_cons. { kword_cell CV 0%nat (C8 (wz 0)). }
      apply Forall_cons.
      { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
                           | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      do 4 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
      apply Forall_cons; [cbn [kentry_ok]; unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; lia|].
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R VDESTROY m (seg_rom asegs) HR HK 60%nat [0xe8f84] (SCR [] [] []) 40%N.
    { split_scs.
      all: clear - E VA DSP DHI SPR LO CE ACF1 ACF2 SB0.
      all: unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in VA.
      all: first [ sc_shdj | sc_dj ]. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1. cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 2%bv L2.
    assert (MU1 : munch [(spz - 32, spz)] m M1).
    { subst M1. clear - Hlf VAP DSP SPR LO CE ACF1 ACF2 VB1 VB2 VB3. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite u64_of_Z by lia; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L2, <- Hsp.
    step. apply evt_done.
    do 16 eexists. split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|].
    split; [exact (msteps_mem_inv asegs _ _ Hms MI)|]. subst M1; apply stk_mem_denot; exact ST.
  Qed.
End VecD.
