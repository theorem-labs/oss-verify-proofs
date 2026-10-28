(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface RtB_Annot BakeStackRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_MILB LbB_Own LbB_ContStmt LbB_ContV4R LbB_ContV4.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section SK.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma sk_cls : forall s' LBx p A n SP m0 a,
    as_RHEAP H s' ((p, A, n) :: LBx) m0 -> ~ In p (map blk_id LBx) -> aceil <= SP -> aclient_addr H LBx SP a ->
    SP <= a \/ (a < aceil /\ ~ (A <= a < A + n) /\ ~ (sh A <= a < sh A + nsh n)).
  Proof.
    intros s' LBx p A n SP m0 a RH NI HSP Hc.
    pose proof (ah_blocks H HH _ _ _ (p, A, n) RH (or_introl eq_refl)) as (R0 & R16 & Rn & RI & RC & RF & RAPP).
    unfold blk_addr, blk_size in R0, R16, Rn, RI, RC, RF, RAPP. cbn [fst snd] in R0, R16, Rn, RI, RC, RF, RAPP.
    pose proof (ah_fsb H HH _ _ _ RH) as (F1 & F2 & F3 & F4).
    pose proof aceil_facts as ACF.
    assert (SHA : sh A + nsh n <= sh aceil).
    { unfold sh, nsh. acb. Z.div_mod_to_equations. nia. }
    assert (SHB : sh aceil < 0x10007fff8000) by (unfold sh; rewrite ASHADOW_BASE_val; acb; Z.div_mod_to_equations; lia).
    unfold AIMG_TOP in RI.
    assert (SHL : 0x7fff7000 < sh A) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    acb.
    unfold aclient_addr in Hc.
    destruct Hc as [Hc|[Hc|[(b0 & Hb & Hr)|[(b0 & Hb & Hr)|[Hc|[Hc|Hc]]]]]].
    - left. exact Hc.
    - right. unfold aimg_client in Hc. destruct Hc as [Hc|[Hc|[Hc|Hc]]]; (split; [lia | split; lia]).
    - right. assert (Hb' : In b0 ((p, A, n) :: LBx)) by (right; exact Hb).
      assert (Hid : blk_id b0 <> p) by (intros E; apply NI; rewrite <- E; apply in_map; exact Hb).
      pose proof (ah_disj H HH _ _ _ (p, A, n) b0 RH (or_introl eq_refl) Hb' (fun E => Hid (eq_sym E))) as D.
      pose proof (ah_blocks H HH _ _ _ b0 RH Hb') as (Q0 & Q16 & Qn & QI & QC & QF & QAPP).
      assert (HI2 : sh A + nsh n <= AHI_LO) by (apply sh_nsh_high; unfold AAPP_HI; lia).
      destruct b0 as [[pb Ab] nb]. unfold blk_addr, blk_size in *. cbn [fst snd] in *.
      unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in QAPP, HI2.
      destruct D as [D|D]; destruct QAPP as [QAPP|QAPP]; split; try lia; split; lia.
    - right. assert (Hb' : In b0 ((p, A, n) :: LBx)) by (right; exact Hb).
      assert (Hid : blk_id b0 <> p) by (intros E; apply NI; rewrite <- E; apply in_map; exact Hb).
      pose proof (ah_disj H HH _ _ _ (p, A, n) b0 RH (or_introl eq_refl) Hb' (fun E => Hid (eq_sym E))) as D.
      pose proof (ah_blocks H HH _ _ _ b0 RH Hb') as (Q0 & Q16 & Qn & QI & QC & QF & QAPP).
      unfold blk_addr, blk_size in D, Hr, Q0, Q16, Qn, QI, QC, QF, QAPP. cbn [fst snd] in D.
      destruct b0 as [[pb Ab] nb]. cbn [fst snd] in *.
      unfold aapp, aapp_lo, aapp_hi in RAPP, QAPP. acb.
      unfold nsh, sh, AHI_LO, ALOWSH_LO, AIMG_TOP in *. rewrite ASHADOW_BASE_val in *.
      Z.div_mod_to_equations.
      destruct D as [D|D]; split; try lia; split; lia.
    - right. assert (HI2 : sh A + nsh n <= AHI_LO) by (apply sh_nsh_high; unfold AAPP_HI; lia).
      unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in F4, HI2. unfold AFS_SIZE in *.
      destruct RF as [RF|RF]; destruct F4 as [F4|F4]; split; try lia; split; lia.
    - right. unfold aapp, aapp_lo, aapp_hi in RAPP, F4. acb.
      unfold sh, nsh, AFS_SIZE, AHI_LO, ALOWSH_LO, AIMG_TOP in *. rewrite ASHADOW_BASE_val in *.
      Z.div_mod_to_equations.
      destruct RF as [RF|RF]; split; try lia; split; lia.
    - right. assert (SA0 : 0x7fff8000 <= sh aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
      unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in RAPP, Hc. destruct RAPP as [RP|RP]; split; try lia; split; lia.
  Qed.

  Lemma sk_xpres_mixed : forall LB s' p A n SP X m0 m1 m2 W,
    as_RHEAP H s' ((p, A, n) :: LB) m0 -> ~ In p (map blk_id LB) -> aceil <= SP ->
    munch W m1 m2 -> wmono asegs m1 m2 ->
    Forall (fun iv : Z * Z => (A <= fst iv /\ snd iv <= A + n) \/ (sh A <= fst iv /\ snd iv <= sh A + nsh n)
                              \/ (aceil <= fst iv /\ snd iv <= SP) \/ (forall a, fst iv <= a < snd iv -> rin_ivs X a)) W ->
    xpres H LB SP X m1 m2.
  Proof.
    intros LB s' p A n SP X m0 m1 m2 W RH NI HSP MU WM FW a Ha [Hc Hx].
    pose proof (sk_cls s' LB p A n SP m0 a RH NI HSP Hc) as CLS.
    assert (OUT : outside W a).
    { clear MU WM. induction W as [|[l h] W IH]; [exact I|]. cbn.
      pose proof (Forall_inv FW) as H1. cbn in H1.
      split; [| apply IH; apply (Forall_inv_tail FW)].
      destruct H1 as [[H1 H2]|[[H1 H2]|[[H1 H2]|H1]]].
      - destruct CLS as [C|(C1 & C2 & C3)]; [pose proof (ah_blocks H HH _ _ _ (p, A, n) RH (or_introl eq_refl)) as (_ & _ & _ & _ & RC & _); cbn in RC|]; lia.
      - destruct CLS as [C|(C1 & C2 & C3)].
        + assert (sh A + nsh n <= sh aceil).
          { pose proof (ah_blocks H HH _ _ _ (p, A, n) RH (or_introl eq_refl)) as (R0 & _ & Rn & _ & RC & _). cbn in *.
            unfold sh, nsh. acb. Z.div_mod_to_equations. nia. }
          assert (sh aceil < aceil) by (apply sh_below_aceil; acb; unfold AAPP_HI; lia). lia.
        + lia.
      - destruct CLS as [C|(C1 & C2 & C3)]; lia.
      - intros K. apply Hx. apply H1. exact K. }
    split.
    - unfold wa. apply MU. rewrite unsigned_lit by lia. exact OUT.
    - intros Hw. apply WM. exact Hw.
  Qed.

  Definition smid (LB LBo : list block) (LF : list fframe) (lo spz shi B : Z) (tp : word) (fa : Z) (FR : list cell)
      (s : as_St H) (m : mem) (n : Z) (sk : as_St H) (mk : mem) (pid' : bptr) (A : Z) (Xk : list (Z * Z)) : Prop :=
    mem_inv asegs mk /\ stk asegs mk lo spz /\ (exists e, rw_cells asegs mk (errno_addr tp) [C4 e]) /\ as_rauxv_ok H mk B
    /\ ACONST mk /\ as_RFS H LF mk /\ stack0 mk lo shi /\ as_RHEAP H sk ((pid', A, n) :: LB) mk
    /\ rw_cells asegs mk fa FR /\ xpres H LB spz Xk m mk /\ as_AL H sk >= as_AL H s - as_Cm H n
    /\ lb_own ((pid', A, n) :: LBo) mk.

  Definition swk (LB : list block) (LF : list fframe) (spz fb A n : Z) (Xk : list (Z * Z)) (iv : Z * Z) : Prop :=
    (aceil <= fst iv /\ snd iv <= fb)
    \/ (A <= fst iv /\ snd iv <= A + n)
    \/ (sh A <= fst iv /\ snd iv <= sh A + nsh n)
    \/ ((forall a, fst iv <= a < snd iv -> rin_ivs Xk a) /\ aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv
        /\ stack0_ok iv /\ (snd iv <= fb \/ spz <= fst iv) /\ (snd iv <= ATP - 164 \/ ATP - 160 <= fst iv)).

  Lemma smid_munch : forall LB LBo LF lo spz shi B tp fa FR s m n sk mk mk' pid' A Xk W fb,
    smid LB LBo LF lo spz shi B tp fa FR s m n sk mk pid' A Xk -> ablock_range H A n -> ~ In pid' (map blk_id LB) ->
    aceil <= lo -> lo <= fb -> fb <= fa -> fa + Z.of_nat (cells_size FR) <= spz -> spz <= 2 ^ 47 -> tp = Z_to_bv 64 ATP ->
    munch W mk mk' -> wmono asegs mk mk' -> mem_inv asegs mk' -> Forall (swk LB LF spz fb A n Xk) W ->
    smid LB LBo LF lo spz shi B tp fa FR s m n sk mk' pid' A Xk.
  Proof.
    intros LB LBo LF lo spz shi B tp fa FR s m n sk mk mk' pid' A Xk W fb
      (MI & ST & (e & ERR) & RA & AC & RF & S0 & RH & FR0 & XP & AL & OW) ABR NI LO1 LO2 LO3 LO4 SPH TPV MU WM MI' FW.
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof ABR as (B0 & B16 & Bn & BI & BC & BF & BAPP). unfold AIMG_TOP in BI.
    pose proof (ah_fsb H HH _ _ _ RH) as (FS1 & FS2 & FS3 & FS4).
    assert (SHAb : sh A + nsh n <= sh aceil) by (unfold sh, nsh; Z.div_mod_to_equations; nia).
    assert (SHAl : 0x7fff7000 < sh A) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHAC : sh aceil < 0x10007fff8000) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHIT : sh AIMG_TOP <= sh A) by (unfold sh, AIMG_TOP; Z.div_mod_to_equations; lia).
    assert (VSPZ : AIMG_TOP <= lo) by (unfold AIMG_TOP; lia).

    assert (W1 : Forall (aclient_write_ok H ((pid', A, n) :: LB)) W).
    { eapply Forall_impl; [|exact FW]. intros [l h] Hw. unfold swk in Hw. cbn [fst snd] in Hw.
      destruct Hw as [Hw|[Hw|[Hw|(_ & Hw & _)]]].
      - left. cbn. lia.
      - right; right; left. exists (pid', A, n). split; [left; reflexivity | cbn; lia].
      - right; right; right; left. exists (pid', A, n). split; [left; reflexivity | cbn; lia].
      - unfold aclient_write_ok in *.
        destruct Hw as [K|[K|[(b' & Hb & K)|[(b' & Hb & K)|K]]]]; [left; exact K | right; left; exact K | | | right; right; right; right; exact K].
        + right; right; left. exists b'. split; [right; exact Hb | exact K].
        + right; right; right; left. exists b'. split; [right; exact Hb | exact K]. }
    assert (W2 : Forall (afs_write_ok H LF) W).
    { eapply Forall_impl; [|exact FW]. intros [l h] Hw. unfold swk in Hw. cbn [fst snd] in Hw.
      unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in FS4, BAPP. unfold AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *.
      destruct Hw as [Hw|[Hw|[Hw|(_ & _ & Hw & _)]]]; [left; cbn; unfold AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *; lia | | | exact Hw].
      - left. cbn. unfold AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *. split; [destruct BF; lia | lia].
      - left. cbn. unfold AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *. split; [destruct FS4; lia | lia]. }
    assert (W3 : Forall aconst_ok W).
    { eapply Forall_impl; [|exact FW]. intros [l h] Hw. unfold swk in Hw. cbn [fst snd] in Hw.
      destruct Hw as [Hw|[Hw|[Hw|(_ & _ & _ & Hw & _)]]]; [| | | exact Hw].
      - apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d5000 by reflexivity; lia | right; left; lia].
      - eapply (aconst_ok_app A n); [exact BAPP | lia | lia].
      - apply aconst_ok_high; [lia | right; left; lia]. }
    assert (W4 : Forall stack0_ok W).
    { eapply Forall_impl; [|exact FW]. intros [l h] Hw. unfold swk in Hw. cbn [fst snd] in Hw.
      destruct Hw as [Hw|[Hw|[Hw|(_ & _ & _ & _ & Hw & _)]]]; [| | | exact Hw].
      - left. cbn. unfold AHI_LO. lia.
      - eapply (stack0_ok_aapp A n); [exact BAPP | lia | lia].
      - right. cbn. lia. }
    destruct (client_frame H HH sk _ LF B W mk mk' RH RF AC RA MU WM W1 W2 W3) as (RH' & RF' & AC' & RA').
    split; [exact MI'|]. split; [eapply BakeStackRep.stk_high_transport; [exact ST | exact WM | exact VSPZ]|].
    split.
    { exists e. eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. subst tp. rewrite u64_of_Z by (unfold ATP; lia).
      eapply disjoint_from_of_Forall; [exact FW|]. intros l h Hw. unfold swk in Hw. cbn [fst snd cells_size csize Z.of_nat] in *.
      unfold ATP in *. destruct Hw as [Hw|[Hw|[Hw|(_ & _ & _ & _ & _ & _ & Hw)]]]; lia. }
    split; [exact RA'|]. split; [exact AC'|]. split; [exact RF'|].
    split; [eapply stack0_transport; [exact S0 | exact MU | exact WM | exact W4]|].
    split; [exact RH'|].
    split.
    { eapply rw_cells_transport; [exact FR0 | exact MU | exact WM |].
      eapply disjoint_from_of_Forall; [exact FW|]. intros l h Hw. unfold swk in Hw. cbn [fst snd] in Hw.
      destruct Hw as [Hw|[Hw|[Hw|(_ & _ & _ & _ & _ & Hw & _)]]]; lia. }
    split; [|split; [exact AL | exact (lb_own_wmono _ _ _ OW WM)]].
    eapply (xpres_trans H); [exact XP|].
    eapply (sk_xpres_mixed LB sk pid' A n spz Xk mk mk mk' W RH NI ltac:(lia) MU WM).
    eapply Forall_impl; [|exact FW]. intros [l h] Hw. unfold swk in Hw. cbn [fst snd] in *.
    destruct Hw as [Hw|[Hw|[Hw|(Hw & _)]]].
    - right; right; left. lia.
    - left. exact Hw.
    - right; left. exact Hw.
    - right; right; right. exact Hw.
  Qed.

  Lemma sk_blk_shad : forall sk mk LBx p A n, as_RHEAP H sk LBx mk -> In (p, A, n) LBx ->
    exists sbs, SHAD mk A sbs /\ Z.of_nat (length sbs) = nsh n.
  Proof.
    intros sk mk LBx p A n RH HIn.
    pose proof (ah_blk_shvis H HH _ _ _ _ _ _ RH HIn) as SV. unfold shvis in SV.
    pose proof (ah_blocks H HH _ _ _ _ RH HIn) as (B0 & B16 & Bn & BI & BC & BF & BAPP).
    cbn [blk_addr blk_size fst snd] in B0, B16, Bn, BI, BC, BF, BAPP.
    pose proof (v4_mod16_8 A B16) as B8.
    destruct (v4_sh_hull A n ltac:(lia) B8 Bn) as [HL1 HL2].
    assert (NS : 0 <= nsh n) by (unfold nsh; apply Z.div_pos; lia).
    destruct (stk_split asegs mk _ (sh A) _ SV ltac:(lia)) as [_ SV2].
    destruct (stk_split asegs mk _ (sh A + nsh n) _ SV2 ltac:(lia)) as [SV3 _].
    destruct (stk_carve asegs mk (sh A) (sh A + nsh n) (Z.to_nat (nsh n)) SV3 ltac:(lia)) as [_ (junk & RC)].
    rewrite Z2Nat.id in RC by lia. replace (sh A + nsh n - nsh n) with (sh A) in RC by lia.
    exists junk. split.
    - eapply SHAD_of_rw_cells; [lia | exact B8 | exact RC].
    - destruct RC as [[Hwf _] _]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _]. rewrite Hl, Z2Nat.id by lia. reflexivity.
  Qed.
End SK.
