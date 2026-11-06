(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps SjStage1 SjS1Bytes.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import SjInvPath SjInv.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AU_kit AU_iface AHarnessU_iface AU_client_kit AU_fuzz_kit AU_parts_iface AU_steptac Stdio_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import ShadowTac APC_kit APC_kit2 APC_kit3 APC_s12iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import ADkModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_tight | solve_load_image ].
Local Ltac solve_store ::= solve_store_tight.

Section CANSEC1. Context {rc : runConstT}.

Lemma nodup3_of7 : forall {T} (a b c d e f g : T), List.NoDup [a; b; c; d; e; f; g] -> List.NoDup [a; c; b].
Proof.
  intros T a b c d e f g H. apply NoDup_cons_iff in H as [Ha H]. apply NoDup_cons_iff in H as [Hb _].
  cbn [In] in Ha, Hb. constructor; [cbn [In]; tauto|]. constructor; [cbn [In]; intros [E|[]]; subst; tauto|].
  constructor; [intros []| constructor].
Qed.

Lemma nodup7P : forall {T} (x1 x2 x3 x4 x5 x6 x7 : T), List.NoDup [x1; x2; x3; x4; x5; x6; x7] ->
  x1 <> x2 /\ x1 <> x3 /\ x1 <> x4 /\ x1 <> x5 /\ x1 <> x6 /\ x1 <> x7 /\ x2 <> x3 /\ x2 <> x4 /\ x2 <> x5 /\ x2 <> x6 /\ x2 <> x7
  /\ x3 <> x4 /\ x3 <> x5 /\ x3 <> x6 /\ x3 <> x7 /\ x4 <> x5 /\ x4 <> x6 /\ x4 <> x7 /\ x5 <> x6 /\ x5 <> x7 /\ x6 <> x7.
Proof.
  intros T x1 x2 x3 x4 x5 x6 x7 N. apply NoDup_cons_iff in N as [N1 N]. apply NoDup_cons_iff in N as [N2 N]. apply NoDup_cons_iff in N as [N3 N].
  apply NoDup_cons_iff in N as [N4 N]. apply NoDup_cons_iff in N as [N5 N]. apply NoDup_cons_iff in N as [N6 _].
  cbn [In] in N1, N2, N3, N4, N5, N6. repeat split; intros E; subst; tauto.
Qed.

(* [comment removed for export] *)
Lemma uchain_below : forall m m' top pc prev frame k tr, uchain m top pc prev frame k tr -> frame <= prev -> uchain m' top pc prev frame k tr.
Proof.
  intros m m' top pc prev frame k tr H Hf. inversion H as [p f k' Hn| |]; subst.
  - apply uc_stop. exact Hn.
  - lia.
  - lia.
Qed.

Section Pres.
  Variable AI : AMallocIface.
  Lemma blk_disjA : forall L RNG st LB m b1 b2, AHEAP AI L RNG st LB m -> In b1 LB -> In b2 LB -> b1 <> b2 ->
    ab_addr b1 + ab_size b1 <= ab_addr b2 \/ ab_addr b2 + ab_size b2 <= ab_addr b1.
  Proof. intros L RNG st LB m b1 b2 AH H1 H2 Hn. exact (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH H1 H2 Hn). Qed.
  Lemma aheap_pres_W_weakenA : forall LB SP W W' m m', (forall a, outside W' a -> outside W a) ->
    aheap_pres_W (aci AI) LB SP W m m' -> aheap_pres_W (aci AI) LB SP W' m m'.
  Proof. intros LB SP W W' m m' HW H a Ha Hc Hx. exact (H a Ha Hc (HW a Hx)). Qed.
  (* [comment removed for export] *)
  Lemma apres_W_munch : forall L RNG st LB m0 SP lo W W2 m m',
    AHEAP AI L RNG st LB m0 -> ATOP <= lo ->
    munch ((lo, SP) :: W2) m m' -> wmono asegs m m' ->
    (forall a, outside W a -> outside W2 a) ->
    aheap_pres_W (aci AI) LB SP W m m'.
  Proof.
    intros L RNG st LB m0 SP lo W W2 m m' AH HLO MU WM HW a Ha Hc Hx. split; [|intros Hv; apply WM; exact Hv].
    apply MU. unfold wa. rewrite unsigned_lit by lia. cbn [outside]. split; [| apply HW; exact Hx].
    destruct (aclient_lo_or_sp AI L RNG st LB LB m0 SP a AH ltac:(intros b Hb; exact Hb) Hc) as [H|H]; lia.
  Qed.
End Pres.

Section Proof.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis S1L : s1l_stmtA AI.
  Hypothesis S2 : stage2_stmtA AI rng_fs.

  Theorem parse_proofA : parse_stmtA AI rng_fs.
  Proof.
    unfold parse_stmtA. intros until jia. intros AH ND INM NIM INS NSI NSI40 INC BUF1 BUF2 INT INB INO NOC INA NIA NF5 NF4 TP8 TPS SB1 SB2
      BUFB DB DL O8 O16 O24 O40 O56 DOCC DM8 FKD DSH RDOC RDSH BLT BLS BLO BLA CIMG CSH ICI UCH TRL S0SP RA4 RANF MALU
      ST LOA LOS RCL RCL1 RCL2 RCL3 RRNG SPT SP16 MI FZ TPE RSTK RIMG RIMGSH RFS AOK AFR DKW A0 A1 A2 A3.
    set (d := strip_bom data) in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof atop_range as ATOPR. unfold APARSE_STACK, STAGE2_STACK_A in LOS.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (_ & _ & HTOP & _).
    assert (ZD0 : 0 <= zlength d) by (unfold zlength; lia).
    (* [comment removed for export] *)
    pose proof (AI_block_bounds AI _ _ _ _ _ _ AH INM) as BM. pose proof (AI_block_bounds AI _ _ _ _ _ _ AH INS) as BS.
    pose proof (AI_block_bounds AI _ _ _ _ _ _ AH INC) as BC. pose proof (AI_block_bounds AI _ _ _ _ _ _ AH INT) as BT.
    pose proof (AI_block_bounds AI _ _ _ _ _ _ AH INB) as BB. pose proof (AI_block_bounds AI _ _ _ _ _ _ AH INO) as BO.
    pose proof (AI_block_bounds AI _ _ _ _ _ _ AH INA) as BA. cbn [ab_addr ab_size] in BM, BS, BC, BT, BB, BO, BA.
    destruct FKD as (fcls & FA & FN & INF & FK1 & FK2 & FKB).
    pose proof (AI_block_bounds AI _ _ _ _ _ _ AH INF) as BF. cbn [ab_addr ab_size] in BF.
    unfold AIMG_HI in BM, BS, BC, BT, BB, BO, BA, BF.
    assert (BUFL : Z.of_nat (length (s1buf d)) = zlength d + 64) by (unfold s1buf, zlength; rewrite length_map, length_app, repeat_length; lia).
    assert (SHD : 0x7fff8000 <= Z.shiftr DOC 3 + 2147450880 /\ Z.shiftr DOC 3 + 2147450880 + 2 <= 0x10007fff8000).
    { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - BF FK1 FK2 ATOPR. Z.div_mod_to_equations. lia. }
    apply implMA_from_evtF.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    park_memA m.
    carve_frame 32%nat ST.
    subst a0 a1 a2 a3. unfold APARSE.
    do 8 zstep.
    unparkA. trmB MU WM.
    (* [comment removed for export] *)
    assert (WF1 : Forall wfar [(lo, bv_unsigned sp)]) by (repeat constructor; unfold AIMG_HI, KLS; cbn; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AH1 : AHEAP AI L RNG (aps_m s) LB mx)
        by (eapply (AI_frame AI); [exact AH| exact MU| exact WM|]; apply Forall_cons; [left; left; cbn; lia| apply Forall_nil]);
      assert (CIMG1 : client_img mx) by exact (client_img_munch32 _ _ _ CIMG MU WM WF1);
      assert (CSH1 : client_sh mx) by exact (client_sh_munch32 _ _ _ CSH MU WF1);
      assert (RCL' : rclean mx rstk) by (eapply rclean_transport; [exact RCL| exact MU| exact WM| repeat constructor; unfold KHIGH; cbn; lia])
    end.
    pose proof (client_img_x _ CIMG1) as (_ & _ & _ & CT1 & _).
    assert (ND3 : List.NoDup [pim; pcp; psi]) by exact (nodup3_of7 _ _ _ _ _ _ _ ND).
    eapply evtF_cut.
    { eapply S1L with (THIS := THIS) (BUF := BUF) (ASI := ASI) (d := d) (lo := lo) (rstk := rstk); rewrite ?unsigned_lit by lia;
        [ exact AH1 | exact MI | exact ND3 | exact INM | exact NIM | exact INC | exact BUF1 | exact BUF2 | exact INS | exact NSI | exact NSI40
        | exact BUFB | exact DB | exact DL | exact O16 | exact CT1 | exact ST | exact LOA | unfold AS1_STACK; lia | lia | lia
        | exact RCL' | exact RCL1 | lia | exact RRNG | exact RSTK | exact RIMG | exact RIMGSH | exact FZ
        | reflexivity | reflexivity | reflexivity | reflexivity ]. }
    intros ms2 PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F' & fc' & m2 & rcv & -> & FZ2 & RCV & MI2 & ST2 & WM2 & MU2
                    & AH2 & RC & C72 & CS).
    rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in MU2 by lia.
    retlit.
    (* [comment removed for export] *)
    lazymatch goal with H : rw_cells asegs _ (bv_unsigned sp + -32) ?cs |- _ =>
      assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -32) cs)
        by (eapply rw_cells_transport; [exact H| exact MU2| exact WM2| unfold s1_winA; cbn; lia]); clear H end.
    (* [comment removed for export] *)
    assert (MUA : munch ((lo, bv_unsigned sp) :: [(THIS + 8, THIS + 12); (THIS + 24, THIS + 28); (THIS + 72, THIS + 88);
                                                  (ASI, ASI + 4 * zlength d + 36)]) m m2).
    { eapply munch_trans.
      - eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside] in Hx |- *. tauto.
      - eapply munch_weaken; [| exact MU2]. intros x Hx. unfold s1_winA. cbn [outside] in Hx |- *. lia. }
    assert (WMA : wmono asegs m m2) by (eapply wmono_trans; [exact WM| exact WM2]).
    clear MU WM.
    zstep.
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      assert (R0 : rcv = 0) by (change 18446744073709551615 with (Z.ones 64) in K; rewrite ?Z.land_ones in K by lia; rewrite ?Z.mod_small in K by lia; lia).
      destruct (CS R0) as (CS8 & CS24 & CSI). clear CS.
      destruct (scan d) as [ok idx] eqn:ES. cbn [fst snd] in RC, CS8, CSI.
      assert (OK : ok = true) by (apply RC; exact R0). subst ok.
      pose proof (scan_S1OUT d idx ES) as S1O. destruct S1O as [NIX _ _ _ _ _].
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      destruct (nodup7P _ _ _ _ _ _ _ ND) as (E12 & E13 & E14 & E15 & E16 & E17 & E23 & E24 & E25 & E26 & E27 & _).
      Local Ltac hbne E := let e := fresh in intros e; injection e; intros; subst; apply E; reflexivity.
      pose proof (blk_disjA AI L RNG _ LB m _ _ AH INM INS ltac:(hbne E12)) as DMI.
      pose proof (blk_disjA AI L RNG _ LB m _ _ AH INM INC ltac:(hbne E13)) as DMC.
      pose proof (blk_disjA AI L RNG _ LB m _ _ AH INM INT ltac:(hbne E14)) as DMT.
      pose proof (blk_disjA AI L RNG _ LB m _ _ AH INM INB ltac:(hbne E15)) as DMB.
      pose proof (blk_disjA AI L RNG _ LB m _ _ AH INM INO ltac:(hbne E16)) as DMO.
      pose proof (blk_disjA AI L RNG _ LB m _ _ AH INM INA ltac:(hbne E17)) as DMA.
      pose proof (blk_disjA AI L RNG _ LB m _ _ AH INS INC ltac:(hbne E23)) as DIC.
      pose proof (blk_disjA AI L RNG _ LB m _ _ AH INS INT ltac:(hbne E24)) as DIT.
      pose proof (blk_disjA AI L RNG _ LB m _ _ AH INS INB ltac:(hbne E25)) as DIB.
      pose proof (blk_disjA AI L RNG _ LB m _ _ AH INS INO ltac:(hbne E26)) as DIO.
      pose proof (blk_disjA AI L RNG _ LB m _ _ AH INS INA ltac:(hbne E27)) as DIA.
      pose proof (blk_disjA AI L RNG _ LB m _ _ AH INM INF ltac:(discriminate)) as DMF.
      pose proof (blk_disjA AI L RNG _ LB m _ _ AH INS INF ltac:(discriminate)) as DIF.
      cbn [ab_addr ab_size] in DMI, DMC, DMT, DMB, DMO, DMA, DIC, DIT, DIB, DIO, DIA, DMF, DIF.
      clear E12 E13 E14 E15 E16 E17 E23 E24 E25 E26 E27.
      destruct (AI_block AI _ _ _ _ _ _ _ _ AH INM) as (_ & (BMk & _ & _ & _) & _). band_ind BMk bM.
      destruct (AI_block AI _ _ _ _ _ _ _ _ AH INS) as (_ & (BSk & _ & _ & _) & _). band_ind BSk bS.
      Local Ltac trc H MUA WMA := eapply rw_cells_transport; [exact H| exact MUA| exact WMA|]; unfold s1_winA; cbn [disjoint_from cells_size csize Nat.add].
      assert (O16' : rw_cells asegs m2 (THIS + 16) [C8 (Z_to_bv 64 ASI)]) by (trc O16 MU2 WM2; clear - BM BS DMI NIM NSI LOA LOS ATOPR ZD0; lia).
      lazymatch type of O40 with rw_cells _ _ _ ?cs =>
        assert (O40' : rw_cells asegs m2 (THIS + 40) cs) by (trc O40 MU2 WM2; clear - BM BS DMI NIM NSI LOA LOS ATOPR ZD0; lia) end.
      destruct (rw_cells_app_split asegs _ (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA)] [C8 x72; C8 x80; C8 x88] O56) as [O56a O56b].
      cbn [cells_size csize] in O56b. change (Z.of_nat (8 + (8 + 0))) with 16 in O56b. replace (THIS + 56 + 16) with (THIS + 72) in O56b by lia.
      destruct (rw_cells_app_split asegs _ (THIS + 72) [C8 x72; C8 x80] [C8 x88] O56b) as [_ O88].
      cbn [cells_size csize] in O88. change (Z.of_nat (8 + (8 + 0))) with 16 in O88. replace (THIS + 72 + 16) with (THIS + 88) in O88 by lia.
      assert (O56' : rw_cells asegs m2 (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA)])
        by (trc O56a MU2 WM2; clear - BM BS DMI NIM NSI LOA LOS ATOPR ZD0; lia).
      assert (O88' : rw_cells asegs m2 (THIS + 88) [C8 x88]) by (trc O88 MU2 WM2; clear - BM BS DMI NIM NSI LOA LOS ATOPR ZD0; lia).
      clear O16 O40 O56 O56a O56b O88 O8 O24.
      assert (OB56 : rw_cells asegs m2 (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA); C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 (zlength d)); C8 x88]).
      { pose proof (rw_cells_app_join asegs _ (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA)] [C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 (zlength d))] O56') as J1.
        cbn [cells_size csize app] in J1. change (Z.of_nat (8 + (8 + 0))) with 16 in J1. replace (THIS + 56 + 16) with (THIS + 72) in J1 by lia.
        specialize (J1 C72).
        pose proof (rw_cells_app_join asegs _ (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA); C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 (zlength d))] [C8 x88] J1) as J2.
        cbn [cells_size csize app] in J2. change (Z.of_nat (8 + (8 + (8 + (8 + 0))))) with 32 in J2. replace (THIS + 56 + 32) with (THIS + 88) in J2 by lia.
        exact (J2 O88'). }
      clear O56' O88' C72.
      (* [comment removed for export] *)
      assert (BLT' : rw_cells asegs m2 TPA [CB (Z.to_nat ntp) jtp]) by (trc BLT MU2 WM2; clear - BT DMT DIT NIM NSI LOA LOS ATOPR ZD0 BM BS; lia).
      assert (BLS' : rw_cells asegs m2 SBA [CB (Z.to_nat nsb) jsb]) by (trc BLS MU2 WM2; clear - BB DMB DIB NIM NSI LOA LOS ATOPR ZD0 BM BS; lia).
      change (rw_cells asegs m AOC [CB 8192 joc]) with (rw_cells asegs m AOC [CB (Z.to_nat 8192) joc]) in BLO.
      assert (BLO' : rw_cells asegs m2 AOC [CB (Z.to_nat 8192) joc]) by (trc BLO MUA WMA; clear - BO DMO DIO NIM NSI NOC LOA LOS ATOPR ZD0 BM BS; lia).
      lazymatch type of BLA with rw_cells asegs ?mb AIA _ => change (rw_cells asegs mb AIA [CB 1024 jia]) with (rw_cells asegs mb AIA [CB (Z.to_nat 1024) jia]) in BLA end.
      assert (BLA' : rw_cells asegs m2 AIA [CB (Z.to_nat 1024) jia]) by (trc BLA MU2 WM2; clear - BA DMA DIA NIM NSI NIA LOA LOS ATOPR ZD0 BM BS; lia).
      assert (DOC' : rw_cells asegs m2 DOC [C8 (Z_to_bv 64 TPA); C8 (Z_to_bv 64 SBA)])
        by (trc DOCC MU2 WM2; clear - BF DMF DIF FK1 FK2 NIM NSI LOA LOS ATOPR ZD0 BM BS; lia).
      assert (DSH' : rw_cells asegs m2 (Z.shiftr DOC 3 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)])
        by (trc DSH MU2 WM2; clear - SHD NIM NSI LOA LOS ATOPR ZD0 BM BS bMr bMhi bMlo bSr bShi bSlo; lia).
      assert (BUF' : bytes_at asegs m2 BUF (s1buf d))
        by (eapply bytes_at_transport; [exact BUFB| exact MU2|]; rewrite BUFL; unfold s1_winA; cbn [disjoint_from]; clear - BC DMC DIC BUF1 BUF2 NIM NSI LOA LOS ATOPR ZD0 BM BS; lia).
      clear BLT BLS BLO BLA DOCC DSH BUFB.
      (* [comment removed for export] *)
      assert (WFA : Forall wfar [(lo, bv_unsigned sp); (THIS + 8, THIS + 12); (THIS + 24, THIS + 28); (THIS + 72, THIS + 88); (ASI, ASI + 4 * zlength d + 36)])
        by (repeat apply Forall_cons; try apply Forall_nil; unfold wfar, AIMG_HI, KLS; cbn [fst snd]; clear - BM BS NIM NSI LOA LOS ATOPR ZD0 bMr bMhi bMlo bSr bShi bSlo; lia).
      assert (CIMG2 : client_img m2) by exact (client_img_munch32 _ _ _ CIMG MUA WMA WFA).
      assert (CSH2 : client_sh m2) by exact (client_sh_munch32 _ _ _ CSH MUA WFA).
      assert (RCL2' : rclean m2 rstk)
        by (eapply rclean_transport; [exact RCL| exact MUA| exact WMA|];
            unfold appW; repeat apply Forall_cons; try apply Forall_nil; unfold KLOW, KHIGH; cbn [fst snd]; clear - BM BS NIM NSI LOA LOS ATOPR ZD0 bMr bMhi bMlo bSr bShi bSlo; lia).
      assert (UCH2 : uchain m2 (al_top L) AFREE_PC (bv_unsigned sp) (bv_unsigned s0) (Nat.pred UDEPTH) tr0).
      { destruct S0SP as [S0L|S0H]; [eapply uchain_below; [exact UCH| lia]|].
        eapply uchain_pres_above; [exact UCH| exact S0H|]. intros a Ha. apply MUA. unfold wa. rewrite unsigned_lit by lia.
        cbn [outside]. clear - Ha BM BS NIM NSI LOA LOS ATOPR ZD0 HTOP. lia. }
      clear CIMG CSH RCL UCH WFA.
      clear DMI DMC DMT DMB DMO DMA DIC DIT DIB DIO DIA DMF DIF bM bMr bMhi bMlo bS bSr bShi bSlo BMk BSk.
      boxm S0SP. boxm TPS. boxm SB2. boxm BUF2.
      (* [comment removed for export] *)
      do 7 zstep.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evtF_done.
      rewrite (parse_impl_rnA data idx ES).
      unbox S0SP. unbox TPS. unbox SB2. unbox BUF2.
      eapply implMA_mono.
      { eapply S2 with (LB := LB) (lo := lo) (rstk := rstk) (d := d) (idx := idx) (tr0 := tr0) (pim := pim) (psi := psi) (pcp := pcp)
          (ptp := ptp) (psb := psb) (poc := poc) (pia := pia) (THIS := THIS) (ASI := ASI) (ACP := ACP) (TPA := TPA) (SBA := SBA) (AOC := AOC)
          (AIA := AIA) (DOC := DOC) (BUF := BUF) (nim := nim) (nsi := nsi) (ncp := ncp) (ntp := ntp) (nsb := nsb) (noc := noc) (nia := nia)
          (x24 := Z_to_bv 64 0) (x88 := x88) (jtp := jtp) (jsb := jsb) (joc := joc) (jia := jia);
          rewrite ?unsigned_lit by lia;
          [ exact AH2 | exact ND | exact INM | exact NIM | exact INS | unfold zlength in *; lia | exact INC | exact BUF1 | exact BUF2
          | exact INT | exact INB | exact INO | exact NOC | exact INA | exact NIA | exact NF5 | exact NF4 | exact TP8 | unfold zlength in *; lia | exact SB1 | exact SB2
          | exact BUF' | exact DB | exact DL | exact ES | exact CSI | exact CS8 | exact O16' | exact CS24 | exact O40' | exact OB56
          | exact DOC' | exact DM8 | exists fcls, FA, FN; split; [exact INF| split; [exact FK1| split; [exact FK2| exact FKB]]]
          | exact DSH' | exact RDOC | exact RDSH | exact BLT' | exact BLS' | exact BLO' | exact BLA'
          | exact CIMG2 | exact CSH2 | exact ICI | exact UCH2 | exact TRL | exact S0SP | exact RA4 | exact RANF | exact MALU
          | exact ST2 | exact LOA | unfold STAGE2_STACK_A; lia | exact RCL2' | exact RCL1 | exact RCL2 | exact RCL3 | exact RRNG
          | exact SPT | exact SP16 | exact MI2 | exact FZ2 | exact TPE | exact RSTK | exact RIMG | exact RIMGSH | exact RFS | exact AOK | exact AFR | exact DKW
          | reflexivity | reflexivity ]. }
      cbv beta. intros [] s' RNG' ms' PO.
      destruct PO as (FPL & v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & F3 & fc3 & m3 & -> & FZ3 & MI3 & ST3 & PW3 & ARS & AH3).
      split; [exact FPL|].
      exists v0, v1, v2, c0, c1, c2, c3, c4, c5, c6, c7, v3, v4, v5, v6, F3, fc3, m3. split; [reflexivity|].
      split; [exact FZ3|]. split; [exact MI3|]. split; [exact ST3|].
      split; [| split; [exact ARS| exact AH3]].
      eapply aheap_pres_W_trans.
      + eapply (apres_W_munch AI L RNG (aps_m s) LB m (bv_unsigned sp) lo _ _ m m2 AH ltac:(lia) MUA WMA).
        intros a Ha. unfold parse_winA in Ha. cbn [outside] in Ha |- *. lia.
      + eapply aheap_pres_W_weakenA; [| exact PW3]. intros a Ha. unfold parse_winA in Ha. unfold s2_winA. cbn [outside] in Ha |- *. lia.
    - (* [comment removed for export] *)
      assert (R0 : rcv <> 0) by (change 18446744073709551615 with (Z.ones 64) in K; rewrite ?Z.land_ones in K by lia; rewrite ?Z.mod_small in K by lia; lia).
      clear K.
      do 5 zstep.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evtF_done.
      assert (SF : fst (scan d) = false) by (destruct (fst (scan d)) eqn:E; [exfalso; apply R0; apply RC; reflexivity| reflexivity]).
      rewrite (parse_impl_failA data SF).
      apply implMA_ret. apply evtF_done.
      unfold s2_postA. split; [apply fp_le_refl|].
      do 15 eexists. exists F', fc', m2. split; [reflexivity|].
      split; [exact FZ2|]. split; [exact MI2|]. split; [exact ST2|].
      split; [| split; [reflexivity| exact AH2]].
      eapply (apres_W_munch AI L RNG (aps_m s) LB m (bv_unsigned sp) lo _ _ m m2 AH ltac:(lia) MUA WMA).
      intros a Ha. unfold parse_winA in Ha. cbn [outside] in Ha |- *. lia.
  Qed.
End Proof.
End CANSEC1.
