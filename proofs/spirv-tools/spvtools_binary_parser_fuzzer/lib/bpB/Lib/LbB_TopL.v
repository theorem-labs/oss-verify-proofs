(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require FPSteps CatSim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import DvB_FuzzStmt LbB_PrsStmt LbB_DStat LbB_SR LbB_Conv LbB_Ctx LbB_RG2 LbB_RG.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_RGl.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TopDefs LbB_TopKit LbB_TopH2 LbB_TopL1 LbB_TopT LbB_TopC LbB_TopP.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section TopL.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps_bp H.
  Hypothesis HPO : binary_parse_stmtA H LINV_P5.
  Hypothesis HTR : po_tr_ok H.

  Definition cut_LP (e : hent H) (c : config) : Prop :=
    exists (ff fp : Z) (XSc : list (Z * Z)) (sk : as_St H) (LBk : list block) (F' : bvmap 5 word) (fc' : bv 32)
           (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x26 x28 x29 x30 x31 : word) (m' : mem) (n P : Z) (pv pc : bptr)
           (A : Z) (j1 j2 : list byte),
      as_VIS H sk (cfg_ms c) = MS (mkR x1 (Z_to_bv 64 (eS1 e)) (e_gp e) (e_tp e) x5 x6 x7 (Z_to_bv 64 (eSP e)) (Z_to_bv 64 (eS1 e)) x10 x11 x12 x13
                    x14 x15 x16 x17 (Z_to_bv 64 (ff + 2672)) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff))
                    (Z_to_bv 64 0x7fff8000) x23 x24 x25 x26 (Z_to_bv 64 (e_N e)) x28 x29 x30 x31)
                                  F' (Z_to_bv 64 0xe8a8c) fc' None m' (seg_rom asegs)
      /\ as_AKREL H sk c /\ as_MPRES H (e_mo e) (cfg_model c)
      /\ FPSteps.frm_zero fc'
      /\ hinv H e ff fp XSc sk LBk m'
       /\ rw_cells asegs m' (eS1 e + 24) (top_fr A ff) /\ rw_cells asegs m' (eS1 e + 80) (top_vd ff (e_D e))
      /\ 1 <= e_N e /\ n = e_N e / 4 /\ as_AL H sk >= as_AL H (e_s e) - ICM 64 - ICM (4 * n)
      /\ (exists j, rw_cells asegs m' (sh ff + 4) [CB 313 j])
      /\ rw_cells asegs m' (ff + 2672) [C8 (wz P); C8 (wz (P + 4 * n)); C8 (wz (P + 4 * n))]
      /\ SHAD m' (ff + 2672) (repeat (b8 0) 3)
      /\ rw_cells asegs m' A [C4 (wz RG_ENV); CB 44 j1; C8 (wz 0); CB 8 j2] /\ addressable m' A CTX_SZ
      /\ vec_st H e LBk m' n P pv pc A.

  Lemma hinv_lpw : forall (e : hent H) ff fp XSc sk LBk m1 m2 pv P k,
    hpre H e -> hinv H e ff fp XSc sk LBk m1 -> In (pv, P, k) LBk ->
    (forall b, In b (e_LB e) -> In b LBk /\ blk_id b <> pv) ->
    munch [(P, P + k); (eS1 e - 16, eS1 e); (eS1 e + 64, eS1 e + 80)] m1 m2 -> wmono asegs m1 m2 -> mem_inv asegs m2 ->
    stk asegs m2 (e_lo e) (eSP e) -> hinv H e ff fp XSc sk LBk m2.
  Proof.
    intros e ff fp XSc sk LBk m1 m2 pv P k HP HI INv LBI MU WM MI2 ST2.
    pose proof (rt_bp_base H HH) as HB.
    pose proof (eS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CE).
    pose proof (hpre_geo H e HP) as (_ & LO & SSHI & SHIH & SP16 & TP).
    destruct HI as (RF & FF & RH & AC & MI & S0 & RA & (errv & ER) & ST & SV & SF & WF & XP & FS & LVI).
    pose proof (hframe_facts H _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof (ah_blocks H HB _ _ _ _ RH INv) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in B0, B16, Bn, BI, BC, BF, BAPP.
    pose proof aceil_facts as ACF. pose proof sh_aceil_lt as SAL.
    pose proof (hwin_ok H e ff fp XSc (eS1 e - 16, eS1 e) FF CE ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(left; cbn; lia))
      as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    pose proof (hwin_ok H e ff fp XSc (eS1 e + 64, eS1 e + 80) FF CE ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(left; cbn; lia))
      as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
    assert (WW : Forall (fun iv => aclient_write_ok H LBk iv /\ afs_write_ok H ((6, ff, fp) :: e_LF e) iv /\ aconst_ok iv /\ stack0_ok iv)
                   [(P, P + k); (eS1 e - 16, eS1 e); (eS1 e + 64, eS1 e + 80)]).
    { apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      - split; [right; right; left; exists (pv, P, k); split; [exact INv | cbn; lia]|].
        split; [left; cbn [fst snd]; split; [destruct BF; [left | right]; unfold AFS_SIZE in *; lia | right; unfold ATLS_PRIV_HI, ATP, AIMG_TOP in *; lia]|].
        split; [eapply (aconst_ok_app P k); [exact BAPP | cbn; lia | cbn; lia]|].
        eapply (stack0_ok_aapp P k); [exact BAPP | cbn; lia | cbn; lia].
      - split; [exact (A2 LBk)|]. split; [exact A1|]. split; [exact A3 | exact A4].
      - split; [exact (C2 LBk)|]. split; [exact C1|]. split; [exact C3 | exact C4]. }
    assert (DJ : forall A n, (A + n <= P \/ P + k <= A) -> (A + n <= eS1 e - 16 \/ eS1 e + 80 <= A \/ (eS1 e <= A /\ A + n <= eS1 e + 64)) ->
                 disjoint_from [(P, P + k); (eS1 e - 16, eS1 e); (eS1 e + 64, eS1 e + 80)] A n).
    { intros A n K1 K2. cbn. repeat split; lia. }
    unfold hinv. rewrite (errno_ATP H e TP) in ER |- *.
    split; [eapply (ah_RFS_frame H HB); [exact RF | exact MU | exact WM | eapply Forall_impl; [| exact WW]; intros iv X; apply X]|].
    split; [exact FF|].
    split; [eapply (ah_RHEAP_frame H HB); [exact RH | exact MU | exact WM | eapply Forall_impl; [| exact WW]; intros iv X; apply X]|].
    split; [eapply ACONST_frame; [exact AC | exact MU | exact WM | eapply Forall_impl; [| exact WW]; intros iv X; apply X]|].
    split; [exact MI2|].
    split; [eapply stack0_transport; [exact S0 | exact MU | exact WM | eapply Forall_impl; [| exact WW]; intros iv X; apply X]|].
    split; [eapply (ah_rauxv_frame H HB); [exact RA | exact MU | exact WM | eapply Forall_impl; [| exact WW]; intros iv X; apply X]|].
    split; [exists errv; eapply rw_cells_transport; [exact ER | exact MU | exact WM | cbn [cells_size csize]; apply DJ; unfold ATP, AIMG_TOP in *; lia]|].
    split; [exact ST2|].
    split; [eapply rw_cells_transport; [exact SV | exact MU | exact WM | apply DJ; cbn; lia]|].
    split; [eapply rw_cells_transport; [exact SF | exact MU | exact WM | apply DJ; cbn; destruct BF; unfold AFS_SIZE in *; lia]|].
    split; [exact (wr_at_wmono _ _ _ _ WF WM)|].
    split; [| split; [exact FS|]].
    2: {
      eapply LbB_TdKit.LINV_P5_munch_hi; [exact LVI | exact MU |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd]; unfold AIMG_TOP in *; lia. }
    eapply xpres_trans; [exact XP|]. intros a Ha [Hc _]. split; [| intros X; apply WM; exact X].
    apply MU. unfold wa. rewrite HLib.u64_of_Z by lia.
    assert (K : (a + 1 <= P \/ P + k <= a) /\ (a + 1 <= eS1 e - 16 \/ eS1 e + 80 <= a \/ (eS1 e <= a /\ a + 1 <= eS1 e + 64))).
    { unfold aclient_addr in Hc.
      destruct Hc as [Hc|[Hc|[(b & INb & Hb)|[(b & INb & Hb)|[Hc|[Hc|Hc]]]]]].
      - split; lia.
      - unfold aimg_client in Hc. unfold AIMG_TOP in BI. split; lia.
      - destruct (LBI b INb) as (INb' & NE).
        pose proof (ah_blocks H HB _ _ _ _ RH INb') as (C0 & C16 & Cn & CI & CC & CF & CAPP).
        split; [destruct (ah_disj H HB _ _ _ b (pv, P, k) RH INb' INv NE) as [D|D]; cbn in D; lia | lia].
      - destruct (LBI b INb) as (INb' & _).
        pose proof (ah_blocks H HB _ _ _ _ RH INb') as (C0 & C16 & Cn & CI & CC & CF & CAPP).
        assert (SB : sh (blk_addr b) + nsh (blk_size b) <= sh aceil).
        { rewrite <- (sh_add8 (blk_addr b) (nsh (blk_size b))). apply sh_mono. unfold nsh. clear - C16 Cn CC ACF. Z.div_mod_to_equations. lia. }
        split; [| lia].
        pose proof (aapp_disjoint_sh P k (blk_addr b) (blk_size b) BAPP ltac:(lia) ltac:(unfold AAPP_HI; lia) Cn) as D. lia.
      - split; [destruct BF; unfold AFS_SIZE in *; lia | lia].
      - assert (sh (as_FSB H + AFS_SIZE) <= sh aceil) by (apply sh_mono; lia).
        split; [| lia].
        pose proof (aapp_disjoint_sh P k (as_FSB H) AFS_SIZE BAPP ltac:(lia) ltac:(unfold AAPP_HI, AFS_SIZE in *; lia) ltac:(unfold AFS_SIZE; lia)) as D.
        assert (sh (as_FSB H + AFS_SIZE) <= sh (as_FSB H) + nsh AFS_SIZE) by (unfold sh, nsh; Z.div_mod_to_equations; lia). lia.
      - split; [| unfold AHI_LO in Hc; lia].
        unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in BAPP, Hc.
        assert (sh 0x7fff7000 <= sh aceil) by (apply sh_mono; lia). replace (sh 0x7fff7000) with 0x8fff6e00 in * by reflexivity. lia. }
    apply (disjoint_outside _ a 1 a); [apply DJ; apply K | lia].
  Qed.

  Lemma seg_LP : forall (e : hent H) (c : config), hpre H e -> cut_LP e c -> as_SR H (hpost H e) c.
Proof.
    intros e [msF mo] HP CT.
    destruct CT as (ff & fp & XSc & sk & LBk & F' & fc' & x1 & x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x23 & x24 & x25 & x26
                    & x28 & x29 & x30 & x31 & m' & n & P & pv & pc & A & j1 & j2
                    & VIS & KR & MP & FZ & HI & CFR & CVD & HN1 & HNn & AL & (j & CJ) & CV & SV & CC & CA & VST).
    cbn [cfg_ms cfg_model] in VIS, MP.
    pose proof (rt_bp_base H HH) as HB.
    pose proof (eS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CE).
    pose proof (hpre_geo H e HP) as (_ & LO & SSHI & SHIH & SP16 & TP).
    pose proof (hinv_ff H _ _ _ _ _ _ _ HI) as FFR.
    pose proof (hframe_facts H _ _ _ FFR) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof aceil_facts as ACF. pose proof sh_aceil_lt as SAL.
    pose proof HP as (_ & BDS & BLN & NR & D16 & DIN & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ADN & _).
    pose proof (hinv_rh H _ _ _ _ _ _ _ HI) as RH.
    pose proof (seg_P9 H) as SP9; try specialize (SP9 HH); try specialize (SP9 HPO); try specialize (SP9 HTR).
    subst n.
    set (SP := eSP e) in *. set (S1 := eS1 e) in *. set (lo := e_lo e) in *. set (N := e_N e) in *. set (D := e_D e) in *.
    assert (LOS : lo <= S1 - 16) by lia.
    assert (SHA : sh aceil < aceil) by lia.
    destruct VST as [(N0 & P0 & PERM) | (Hn & PERM & (bs & CP) & AP)].
    - assert (HN4 : 0 <= N < 4) by (clear - N0 HN1; Z.div_mod_to_equations; lia).
      eapply (ahh_evt_then H HB _ _ sk msF _ mo KR VIS).
      { exact (hLP0 x1 (e_gp e) (e_tp e) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (ff + 2672)) (Z_to_bv 64 (sh ff + 4))
                 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 SHBASE) x23 x24 x25 x26 x28 x29 x30 x31 F' fc' m' SP S1 N HN4). }
      intros msF2 mo2 KR2 MP2 EQ2.
      apply SP9; [exact HP|].
      exists ff, fp, XSc, sk, LBk, F', fc', x1, x5, x6, x7, (Z_to_bv 64 4), x11, x12, x13, x14, x15, x16, x17,
        (Z_to_bv 64 (ff + 2672)), (Z_to_bv 64 (sh ff + 4)), (Z_to_bv 64 ff), (Z_to_bv 64 (sh ff)), (Z_to_bv 64 SHBASE), x23, x24, x25, x26,
        (Z_to_bv 64 N), x28, x29, x30, x31, m', (N / 4), P, pv, pc, A, j1, j2.
      cbn [cfg_ms cfg_model]. split; [exact EQ2|]. split; [exact KR2|].
      split; [exact (ah_mpres_trans H HB (e_mo e) mo mo2 MP MP2)|]. split; [exact FZ|]. split; [exact HI|].
      split; [exact CFR|]. split; [exact CVD|]. split; [reflexivity|]. split; [exact AL|].
      split; [exists j; exact CJ|]. split; [exact CV|]. split; [exact SV|]. split; [exact CC|]. split; [exact CA|].
      left. split; [exact N0|]. split; [exact P0 | exact PERM].
    - assert (HN4 : 4 <= N) by (clear - Hn; Z.div_mod_to_equations; lia).
      assert (ND : List.NoDup (pv :: pc :: map blk_id (e_LB e))).
      { exact (Permutation_NoDup (Permutation_map blk_id PERM) (ah_nodup H HB _ _ _ RH)). }
      pose proof (proj1 (NoDup_cons_iff _ _) ND) as (NI & _).
      assert (LBI : forall b, In b (e_LB e) -> In b LBk /\ blk_id b <> pv).
      { intros b Hb. split; [apply (Permutation_in _ (Permutation_sym PERM)); right; right; exact Hb|].
        intros Eb. apply NI. right. rewrite <- Eb. apply in_map. exact Hb. }
      assert (NEC : pc <> pv) by (intros E; apply NI; left; exact E).
      assert (INP : In (pv, P, 4 * (N / 4)) LBk) by (apply (Permutation_in _ (Permutation_sym PERM)); left; reflexivity).
      assert (INC : In (pc, A, 64) LBk) by (apply (Permutation_in _ (Permutation_sym PERM)); right; left; reflexivity).
      destruct (DIN ltac:(lia)) as (pD & IND).
      destruct (LBI _ IND) as (INDk & NED).
      pose proof (ah_blocks H HB _ _ _ _ RH INP) as (P0 & P16 & Pn & PI & PCe & PF & PAPP). cbn in P0, P16, Pn, PI, PCe, PF, PAPP.
      pose proof (ah_blocks H HB _ _ _ _ RH INDk) as (D0 & D16' & Dn & DI & DCe & DF & DAPP). cbn in D0, D16', Dn, DI, DCe, DF, DAPP.
      pose proof (ah_blocks H HB _ _ _ _ RH INC) as (C0 & C16 & Cn & CI & CCe & CF & CAPP). cbn in C0, C16, Cn, CI, CCe, CF, CAPP.
      pose proof (ah_disj H HB _ _ _ _ _ RH INDk INP NED) as DPD. cbn in DPD.
      pose proof (ah_disj H HB _ _ _ _ _ RH INC INP NEC) as CPD. cbn in CPD.
      assert (BAND : P + 4 * (N / 4) <= ALOWSH_LO \/ AHI_LO <= P).
      { pose proof PAPP as PB. unfold aapp, aapp_lo, aapp_hi in PB. destruct PB as [(X1 & X2)|(X1 & X2)]; [left | right]; lia. }
      pose proof (hbytes H) as HBY; try specialize (HBY HB).
      pose proof (haddressable H) as HAD; try specialize (HAD HB).
      pose proof (hLP x1 (e_gp e) (e_tp e) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 (ff + 2672)) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) x23 x24 x25 x26 x28 x29 x30 x31
                    F' fc' m' SP S1 ff D N P lo (e_ds e) bs) as EV.
      eapply (ahh_evt_then H HB _ _ sk msF _ mo KR VIS).
      { apply EV.
        - lia.
        - exact D16.
        - exact DI.
        - lia.
        - exact S32.
        - exact S1L.
        - lia.
        - exact SPH.
        - exact LOS.
        - unfold AIMG_TOP in *; lia.
        - lia.
        - exact F3.
        - exact P16.
        - exact PI.
        - lia.
        - exact BAND.
        - lia.
        - lia.
        - lia.
        - lia.
        - lia.
        - exact (hinv_stk H _ _ _ _ _ _ _ HI).
        - exact (hinv_mi H _ _ _ _ _ _ _ HI).
        - exact (hinv_ac H _ _ _ _ _ _ _ HI).
        - exact CVD.
        - exact CV.
        - exact SV.
        - eapply HBY; [exact HP | exact HI | exact IND | lia | lia | exact BDS].
        - exact BLN.
        - eapply HAD; [exact HP | exact HI | exact IND | exact (ADN ltac:(lia))].
        - exact CP.
        - exact AP. }
      intros msF2 mo2 KR2 MP2 (x1' & x10' & x11' & x12' & x13' & x14' & x15' & x16' & x17' & x18' & x19' & x20' & x21' & x22' & x23' & x24'
                               & x25' & x26' & x27' & m1 & EQ2 & MU & WM & MI1 & ST1).
      assert (HI1 : hinv H e ff fp XSc sk LBk m1) by exact (hinv_lpw e ff fp XSc sk LBk m' m1 pv P (4 * (N / 4)) HP HI INP LBI MU WM MI1 ST1).
      assert (DJ : forall a k, (a + k <= P \/ P + 4 * (N / 4) <= a) -> (a + k <= S1 - 16 \/ S1 + 80 <= a \/ (S1 <= a /\ a + k <= S1 + 64)) ->
                   disjoint_from [(P, P + 4 * (N / 4)); (S1 - 16, S1); (S1 + 64, S1 + 80)] a k)
        by (intros a k K1 K2; cbn; repeat split; lia).
      pose proof (aapp_disjoint_sh P (4 * (N / 4)) ff 4096 PAPP ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as SDF.
      change (nsh 4096) with 512 in SDF.
      assert (SHF : sh (ff + 4096) <= sh aceil) by (apply sh_mono; lia).
      assert (SHV : sh (ff + 2672) = sh ff + 334) by (rewrite <- (sh_add8 ff 334); f_equal).
      apply SP9; [exact HP|].
      exists ff, fp, XSc, sk, LBk, F', fc', x1', x5, x6, x7, x10', x11', x12', x13', x14', x15', x16', x17', x18', x19', x20', x21', x22', x23',
        x24', x25', x26', x27', x28, x29, x30, x31, m1, (N / 4), P, pv, pc, A, j1, j2.
      cbn [cfg_ms cfg_model]. split; [exact EQ2|]. split; [exact KR2|].
      split; [exact (ah_mpres_trans H HB (e_mo e) mo mo2 MP MP2)|]. split; [exact FZ|]. split; [exact HI1|].
      split; [eapply rw_cells_transport; [exact CFR | exact MU | exact WM | apply DJ; cbn; lia]|].
      split; [eapply rw_cells_transport; [exact CVD | exact MU | exact WM | apply DJ; cbn; lia]|].
      split; [reflexivity|]. split; [exact AL|].
      split; [exists j; eapply rw_cells_transport; [exact CJ | exact MU | exact WM | apply DJ; cbn; lia]|].
      split; [eapply rw_cells_transport; [exact CV | exact MU | exact WM | apply DJ; cbn; lia]|].
      split.
      { destruct SV as (S1a & S1b & U). split; [exact S1a|]. split; [exact S1b|].
        eapply u8arr_transport; [exact U | exact MU | exact WM | rewrite repeat_length; apply DJ; cbn; lia]. }
      split; [eapply rw_cells_transport; [exact CC | exact MU | exact WM | apply DJ; cbn; lia]|].
      split.
      { destruct CA as (CA0 & S1a & S1b & U). split; [exact CA0|]. split; [exact S1a|]. split; [exact S1b|].
        assert (SHA8 : sh A + 8 <= sh aceil) by (rewrite <- (sh_add8 A 8); apply sh_mono; lia).
        pose proof (aapp_disjoint_sh P (4 * (N / 4)) A 64 PAPP ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as SDA.
        change (nsh 64) with 8 in SDA.
        eapply u8arr_transport; [exact U | exact MU | exact WM | rewrite shadow_of_length by (unfold CTX_SZ; lia); change (nsh CTX_SZ) with 8; apply DJ; lia]. }
      right. split; [lia|]. split; [exact PERM|]. split.
      { apply wr_at_rw_cells; [| unfold AIMG_TOP in PI; lia | lia].
        destruct CP as [_ WR]. cbn [cells_size csize] in WR. rewrite Nat.add_0_r, Z2Nat.id in WR by lia. exact (wr_at_wmono _ _ _ _ WR WM). }
      destruct AP as (AP0 & S1a & S1b & U). split; [exact AP0|]. split; [exact S1a|]. split; [exact S1b|].
      assert (SHP : sh P + nsh (4 * (N / 4)) <= sh aceil).
      { rewrite <- (sh_add8 P (nsh (4 * (N / 4)))). apply sh_mono. unfold nsh. clear - P16 PCe ACF. Z.div_mod_to_equations. lia. }
      pose proof (aapp_disjoint_sh P (4 * (N / 4)) P (4 * (N / 4)) PAPP ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as SDP.
      eapply u8arr_transport; [exact U | exact MU | exact WM | rewrite shadow_of_length by lia; apply DJ; lia].
Qed.
End TopL.
