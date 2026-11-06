(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pwlopts_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pwlopts_A.CJ_band3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs CJ_iface AShadow CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pv_ctx.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pv_ctx.CJ_fp_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_fuzz_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_fuzz_iface.CJ_print_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.CJ_print_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_pv_ctx CJ_pv_common ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaOn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section PVK.
  Variable Q : pvi.
  Local Notation AI := (q_ai Q).    Local Notation TI := (q_ti Q).
  Local Notation ra := (q_ra Q).    Local Notation sp := (q_sp Q).    Local Notation gp := (q_gp Q).    Local Notation tp := (q_tp Q).
  Local Notation s0 := (q_s0 Q).    Local Notation s1 := (q_s1 Q).    Local Notation s2 := (q_s2 Q).    Local Notation s3 := (q_s3 Q).
  Local Notation s4 := (q_s4 Q).    Local Notation s5 := (q_s5 Q).    Local Notation s6 := (q_s6 Q).    Local Notation s7 := (q_s7 Q).
  Local Notation s8 := (q_s8 Q).    Local Notation s9 := (q_s9 Q).    Local Notation s10 := (q_s10 Q).  Local Notation s11 := (q_s11 Q).
  Local Notation F := (q_F Q).      Local Notation m := (q_m Q).      Local Notation g := (q_g Q).
  Local Notation sp0 := (q_sp0 Q).  Local Notation SPB := (q_SPB Q).  Local Notation LR := (q_LR Q).    Local Notation B := (q_B Q).
  Local Notation LF := (q_LF Q).    Local Notation np0 := (q_np0 Q).  Local Notation BB := (q_BB Q).    Local Notation CH := (q_CH Q).
  Local Notation n := (q_n Q).      Local Notation p := (q_p Q).      Local Notation PB := (q_PB Q).    Local Notation len0 := (q_len0 Q).
  Local Notation dep := (q_dep Q).  Local Notation fw := (q_fw Q).    Local Notation lo := (q_lo Q).
  Local Notation SA := (q_SA Q).    Local Notation Fr := (q_Fr Q).
  Hypothesis PVL : pvl Q.
  Local Notation SP := (bv_unsigned sp).
  Local Notation POST := (pvalue_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR B LF np0 BB CH n p PB len0 dep fw lo m g).
  Ltac lits := pose proof (pvl_lits Q PVL)
                 as ((PL1 & PL2 & PL3) & PB8 & AL & S47 & TOP & BOT & PB80 & CEIL & LO & TP & N1 & BLR & DEPN & DEP0 & PNZ
                     & CHOK & CHL & CHB & RA1 & RA2 & NPM & BBA & LEN0 & LFR & (GSA1 & GSA2) & (FAL & FLO & FHI & FNEW)
                     & SPR & RAR & S0R & (TOPR & BOTE) & CHN0);
               pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR; change (2^3) with 8 in SHFR;
               pose proof alloc_ceiling_eq as ACE; pose proof KHIGH_eqs as KHE.
  Ltac alia := first [ rewrite ?alloc_ceiling_eq; unfold sclr, AMALLOC_STACK, AINTRIN_STACK, ASTRFN_STACK, AENSURE_STACK, ASTKMALLOC_STACK, APSTR_STACK, AFORMAT_STACK, APV_STACK, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_END in *; lia | sclr_tac ].
  Ltac dj := cbn [disjoint_from cells_size Cells.csize Nat.add length map]; rewrite ?cells_size_mapC8, ?cells_size_mapC1, ?length_map; unfold AERRNO, ATP; lia.

  (* [comment removed for export] *)
  Hypothesis ENS : ensure_stmt AI TI.
  Hypothesis PSTR : pstr_stmt AI TI.
  Hypothesis STRLEN : strlen_icpt_spec.
  Hypothesis REC : forall d, (d < n)%nat -> print_value_at AI TI d.
  Hypothesis FLAGLOW : art_flag_low_stmt AI.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pvx_chain_own : forall mm loc jb shp Fx fcx,
    PVFR Q mm loc jb shp Fx fcx -> chain_cells mm CH ->
    chain_cells mm ((SP, bv_unsigned ra, bv_unsigned s0) :: CH)
    /\ chain_ok SP ((SP, bv_unsigned ra, bv_unsigned s0) :: CH) (ASTACK_TOP sp0).
  Proof.
    intros mm loc jb shp Fx fcx (SAVW & _) CC. lits. bandM. sepM. unfold SAVEDV in SAVW. split.
    - split; [| exact CC].
      destruct (rw_cells_app_split mm (SP + -120) [C8 (reg_get F (Z_to_bv 5 9)); C8 (reg_get F (Z_to_bv 5 8)); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7;
                 C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] SAVW) as [_ T2].
      cbn [cells_size Cells.csize Nat.add] in T2. replace (SP + -120 + Z.of_nat 104) with (SP + -16) in T2 by lia.
      exact (proj1 (chain_cells_frame1 mm SP s0 ra T2)).
    - apply chain_ok_cons; [lia| Z.div_mod_to_equations; lia| lia| lia| exact RA2| lia| eapply chain_ok_mono; [exact CHOK| lia]|].
      unfold chain_link in CHL. destruct CH as [|[[f1 r1] sv1] CH']; [exact CHL| exact CHL].
  Qed.

  (* [comment removed for export] *)
  Lemma pvx_pb_below : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb shp Fx fcx,
    PVM Q depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs -> PVFR Q mm loc jb shp Fx fcx -> pb_below mm PB.
  Proof.
    intros until fcx. intros CTX (SAVW & _). lits. bandM. sepM. unfold SAVEDV in SAVW.
    (nelimp CTX 15%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ HB16 HB8 _).
    destruct (rw_cells_app_split mm (SP + -120) [C8 (reg_get F (Z_to_bv 5 9)); C8 (reg_get F (Z_to_bv 5 8)); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7;
               C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] SAVW) as [_ T2].
    cbn [cells_size Cells.csize Nat.add] in T2. replace (SP + -120 + Z.of_nat 104) with (SP + -16) in T2 by lia.
    destruct T2 as [[_ BY2] _]. cbn [cells_bytes cbytes app] in BY2. rewrite app_nil_r in BY2.
    assert (C3 : SP + 16 <= PB \/ PB = SP + 8 \/ PB = SP) by (Z.div_mod_to_equations; lia).
    destruct C3 as [C|[C|C]].
    - exact (HB16 C).
    - destruct (HB8 C) as [w BW]. exists ra, w. split; [| lia].
      apply bytes_at_app in BY2. destruct BY2 as [_ BYra]. rewrite length_le8 in BYra. replace (SP + -16 + Z.of_nat 8) with (PB - 16) in BYra by lia.
      apply bytes_at_app. split; [exact BYra|]. rewrite length_le8. replace (PB - 16 + Z.of_nat 8) with SP by lia. exact BW.
    - exists s0, ra. split; [replace (PB - 16) with (SP + -16) by lia; exact BY2|].
      unfold chain_link in CHL. destruct CH as [|[[f1 r1] sv1] CH']; [lia|].
      apply Forall_cons_iff in CHB as [Hf _]. unfold fr_f in Hf. cbn [fst snd] in Hf. lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pvx_after_agree : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb shp Fx fcx mm',
    PVM Q depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs -> PVFR Q mm loc jb shp Fx fcx ->
    pv_agree sp0 LR ((Fr, 1) :: LF) SA PB mm mm' ->
    rw_cells bsegs mm' (SP + -120) (SAVEDV Q) /\ rw_cells bsegs mm' SA (map C8 loc) /\ stk bsegs mm' (SA + 72) (SP + -120)
    /\ FHDR Q mm' /\ FBODY Q mm' jb /\ SHCV Q mm' shp
    /\ pv_agree sp0 LR LF SP PB m mm' /\ cj_chain CJ_PRINTABLE mm' n p B /\ chain_cells mm' CH /\ sh_zero mm' alloc_ceiling (2^47)
    /\ (SP + 16 <= PB -> pb_below mm' PB) /\ (PB = SP + 8 -> exists w : word, bytes_at bsegs mm' SP (le8 w)).
  Proof.
    intros until mm'. intros CTX (SAVW & LOC & LL & PAD & ST & HDR & BODY & SHC & L16 & FRM & FA) PVE. lits. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM.
    (nelimp CTX 15%nat; intros HL HP _ _ _ _ _ _ PVA CHN CC SSZ HB16 HB8 _).
    assert (HLR : forall b, In b LR -> In b LB1) by (intros b Hb; eapply Permutation_in; [exact HP| right; exact Hb]).
    assert (INF : In (Fr, 1) ((Fr, 1) :: LF)) by (left; reflexivity).
    (* [comment removed for export] *)
    assert (MAGS : magree (fun a => SA <= a < Z.max (sp0 + 4096) (2^47) /\ ~ (PB <= a < PB + 64)) mm mm').
    { eapply magree_mono; [exact PVE|]. cbv beta. intros a [Hs Hn]. split; [left; exact Hs| exact Hn]. }
    assert (MAGF : magree (fun a => Fr <= a < Fr + 120 \/ SH Fr <= a < SH Fr + 16) mm mm').
    { eapply magree_mono; [exact PVE|]. cbv beta. intros a Hf. split; [| unfold SH, SHADOW_OFFSET in Hf; Z.div_mod_to_equations; lia].
      do 3 right. left. exists Fr, 1. split; [exact INF|]. change (fsz 1) with 128. lia. }
    assert (AGS : forall a, 0 <= a < 2^64 -> SA <= a < Z.max (sp0 + 4096) (2^47) -> ~ (PB <= a < PB + 64) -> mm' (wa a) = mm (wa a)).
    { intros a Ha Hs Hn. destruct (MAGS a Ha ltac:(split; [exact Hs| exact Hn])) as [E _]. exact E. }
    unfold SAVEDV in SAVW |- *. unfold FHDR in HDR |- *. unfold FBODY in BODY |- *. unfold SHCV, SHCW in SHC |- *.
    split. { eapply rw_cells_magree; [exact MAGS| exact SAVW|]. cbn [cells_size Cells.csize Nat.add]. intros a Ha. lia. }
    split. { eapply rw_cells_magree; [exact MAGS| exact LOC|]. rewrite cells_size_mapC8, LL. cbn. intros a Ha. lia. }
    split. { (nelim PAD 3%nat; intros P0 P1 PW). split; [exact P0|]. split; [exact P1|]. intros a Ha.
             destruct (MAGS a ltac:(lia) ltac:(cbv beta; lia)) as [E X]. (nelim (PW a Ha) 3%nat; intros W0 b Hb).
             split; [apply X, W0| exists b; unfold mrd in *; rewrite E; exact Hb]. }
    split. { eapply rw_cells_magree; [exact MAGF| exact HDR|]. cbn. intros a Ha. left. lia. }
    split. { eapply rw_cells_magree; [exact MAGF| exact BODY|]. cbn. intros a Ha. left. lia. }
    split. { eapply rw_cells_magree; [exact MAGF| exact SHC|]. rewrite cells_size_mapC1, length_map, L16, SH_shiftr. cbn. intros a Ha. right. lia. }
    split. { eapply pv_agree_trans; [exact PVA|]. eapply (pv_agree_weaken_lf sp0 LR ((Fr, 1) :: LF) LF); [| intros f Hf; right; exact Hf].
             eapply pv_agree_weaken; [exact PVE| lia| intros b Hb; exact Hb]. }
    split. { eapply cj_chain_magree; [exact CHN| exact PVE|]. intros a nelH_; (nelim nelH_ 4%nat; intros A' n' Hin Hr).
             (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (HLR _ (BLR _ Hin))) 4%nat; intros _ _ _ R4). try rewrite alloc_ceiling_eq in R4.
             split; [right; right; left; exists A', n'; split; [apply BLR; exact Hin| exact Hr]| lia]. }
    split. { eapply (chain_cells_ext_below Q mm mm' (SP + 16) CH (ASTACK_TOP sp0)); [exact CC| exact CHOK| exact CHB|].
             intros a Ha. apply AGS; lia. }
    split. { eapply sh_zero_stack_pv_agree; [exact PVE| lia| exact SSZ]. }
    split. { intros H16. (nelim (HB16 H16) 4%nat; intros w1 w2 BY Hw). exists w1, w2. split; [| exact Hw].
             (nelim BY 3%nat; intros B0 B1' B2). split; [exact B0|]. split; [exact B1'|]. intros i Hi.
             assert (Hi16 : (i < 16)%nat) by (clear -Hi; first [rewrite length_app, !length_le8 in Hi | idtac]; cbn in Hi; lia).
             rewrite <- (B2 i Hi). unfold mrd. rewrite AGS; [reflexivity| lia| lia| lia]. }
    intros H8. (nelim (HB8 H8) 4%nat; intros w B0 B1' B2). exists w. split; [exact B0|]. split; [exact B1'|]. intros i Hi.
    assert (Hi8 : (i < 8)%nat) by (clear -Hi; first [rewrite length_le8 in Hi | idtac]; cbn in Hi; lia).
    rewrite <- (B2 i Hi). unfold mrd. rewrite AGS; [reflexivity| lia| lia| lia].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ens_kpost (depc off needed : Z) (loc : list word) (jb : list byte) (shp : list Z) (Fx : bvmap 5 word) (fcx : bv 32)
      (x1 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) : machine_state -> Model -> lghost -> Prop :=
    fun ms' mo' g' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte)
                          (LB' : list cblock) (TRS' : list (list Z)) (B' np' : Z) (errv' : word),
      ms' = MS (mkR x1 (Z_to_bv 64 SA) gp tp t0 t1 t2 sp (Z_to_bv 64 SA) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
               Fx (ret_pc x1) fcx None m' (seg_rom bsegs)
      /\ ( (a0 = Z_to_bv 64 0 /\ pv_exit Q m' mo' g' LB' TRS' B' np' errv' loc jb shp Fx fcx 0)
        \/ (exists buf' len' bs', a0 = Z_to_bv 64 (buf' + off) /\ buf' <> 0
              /\ PVX Q depc m' mo' g' LB' TRS' B' np' errv' buf' len' off bs' loc jb shp Fx fcx
              /\ needed + off + 1 <= len' /\ len' < 2^31) ).

  Lemma pvx_ensure : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb shp Fx fcx needed
      (x1 t0 t1 t2 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    PVX Q depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb shp Fx fcx ->
    0 <= needed < 2^64 -> 0x81ed8 <= bv_unsigned x1 ->
    LSCPS bsegs (ens_kpost depc off needed loc jb shp Fx fcx x1 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27)
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp t0 t1 t2 sp (Z_to_bv 64 SA) (Z_to_bv 64 PB) (Z_to_bv 64 needed) a2 a3 a4 a5 a6 a7
              x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) Fx (wz AENSURE_ENTRY) fcx None mm (seg_rom bsegs)) mo1 g1.
  Proof.
    intros until t6. intros [CTX FRX] ND RX. lits. bandM. sepM.
    pose proof (pvx_pb_below _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX FRX) as PBW.
    pose proof (pvm_allow Q PVL _ _ _ _ _ _ _ _ _ _ _ _ _ CTX) as [HBA HNA].
    (nelimp CTX 19%nat; intros HL HP PBS1 ARR LEN PN ERR MI PVA CHN CC SSZ HB16 HB8 GM TV L0 HB HNP).
    (nelimp FRX 11%nat; intros SAVW LOC LL PAD ST HDR BODY SHC L16 FRM FA).
    (nelimp PN 3%nat; intros PN1 PN2 PN3).
    assert (E1 : bv_unsigned (Z_to_bv 64 SA) = SA) by (apply unsigned_lit; lia).
    pose proof (pb_npallow_ge2 len ltac:(unfold INT_MAX; lia)) as NP2.
    eapply lscps_mono.
    { eapply ENS with (lo := lo) (LR := LR) (bs := bs) (dep := depc); rewrite ?E1;
        first [ exact HL | exact HP | exact PBS1 | split; [exact ARR| exact LEN] | exact PN | exact PBW | exact ST | exact ERR | exact MI
              | exact TP | exact SSZ | exact TV | exact HBA | reflexivity
              | split; [lia| split; [lia| lia]]
              | apply not_pc0_high; exact RX
              | unfold AENSURE_STACK, AMALLOC_STACK; (lia_on PL1 PB8 CEIL LO N1 FLO SPR GSA1 PB80 S47 TOP BOT GSA2 HNA NP2 ND)
              | Z.div_mod_to_equations; lia
              | lia ]. }
    cbv beta. intros ms2 mo2 g2 PO.
    (nelim PO 30%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 errv2 LB2 TRS2 B2 np2 -> MI2 ST2 ERR2 PVE HL2 TV2 GM2 OUT)
.
    rewrite ?E1 in ST2, PVE.
    (nelim (pvx_after_agree _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX FRX PVE) 12%nat; intros SAVW2 LOC2 PAD2 HDR2 BODY2 SHC2 PVA2 CHN2 CC2 SSZ2 HB16' HB8').
    assert (FRX2 : PVFR Q m2 loc jb shp Fx fcx).
    { split; [exact SAVW2|]. split; [exact LOC2|]. split; [exact LL|]. split; [exact PAD2|]. split; [exact ST2|].
      split; [exact HDR2|]. split; [exact BODY2|]. split; [exact SHC2|]. split; [exact L16|]. split; [exact FRM| exact FA]. }
    assert (GM2' : gmono g g2) by (eapply gmono_trans; [exact GM| exact GM2]).
    unfold ens_kpost. nexists 15%nat. exists m2, LB2, TRS2, B2, np2, errv2. split; [reflexivity|].
    destruct OUT as [(-> & HPn & PBSn & HBn & HNn) | [(-> & HPn & PBSn & PDn & -> & ->) | (buf' & len' & bs' & -> & HPn & PBSn & PDn & ROOM & L31 & LL' & HBn & HNn)]].
    - (* [comment removed for export] *)
      left. split; [reflexivity|].
      split; [exact FRX2|]. split; [exact HL2|]. split; [exact ERR2|]. split; [exact MI2|]. split; [exact PVA2|]. split; [exact CHN2|].
      split; [exact CC2|]. split; [exact GM2'|]. split; [exact TV2|].
      exists 0, 0, off. left. split; [reflexivity|]. split; [exists depc; exact PBSn|]. split; [left; split; [reflexivity| exact HPn]|].
      pose proof (pb_allow_ge_fail len ltac:(unfold INT_MAX; lia)) as AF.
      eapply (pvm_pot_fail Q PVL len B1 np1); [exact L0| unfold INT_MAX; lia| exact HB| exact HNP| lia| lia].
    - (* [comment removed for export] *)
      left. split; [reflexivity|].
      split; [exact FRX2|]. split; [exact HL2|]. split; [exact ERR2|]. split; [exact MI2|]. split; [exact PVA2|]. split; [exact CHN2|].
      split; [exact CC2|]. split; [exact GM2'|]. split; [exact TV2|].
      exists buf, len, off. left. split; [reflexivity|]. split; [exists depc; exact PBSn|].
      pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL2 (perm_in_head _ _ _ HPn)) as (Y1 & _). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in Y1. bandM. sepM.
      split; [right; split; [lia| exact HPn]|].
      pose proof (pb_pot_mono len INT_MAX ltac:(unfold INT_MAX; lia) ltac:(lia)). pose proof (pb_npot_mono len INT_MAX ltac:(unfold INT_MAX; lia) ltac:(lia)).
      pose proof PB_FAIL_eq as PFE. unfold pb_allow, pb_npallow in *. lia.
    - (* [comment removed for export] *)
      right. exists buf', len', bs'. split; [reflexivity|].
      pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL2 (perm_in_head _ _ _ HPn)) as (Y1 & _). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in Y1. bandM. sepM.
      split; [lia|]. destruct PDn as [ARRn LENn].
      split; [| split; [exact ROOM| exact L31]]. split; [| exact FRX2].
      split; [exact HL2|]. split; [exact HPn|]. split; [exact PBSn|]. split; [exact ARRn|]. split; [exact LENn|]. split; [split; [lia| split; [exact L31| lia]]|].
      split; [exact ERR2|]. split; [exact MI2|]. split; [exact PVA2|]. split; [exact CHN2|]. split; [exact CC2|]. split; [exact SSZ2|].
      split; [exact HB16'|]. split; [exact HB8'|]. split; [exact GM2'|]. split; [exact TV2|].
      eapply (pvm_pot_grow Q len B1 np1); [exact L0| exact HB| exact HNP| exact HBn| exact HNn| exact LL'].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition rec_kpost (depc : Z) (loc : list word) (jb : list byte) (shp : list Z)
      (x1 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) : machine_state -> Model -> lghost -> Prop :=
    fun ms' mo' g' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Fx' : bvmap 5 word) (fcx' : bv 32) (m' : word -> option byte)
                          (LB' : list cblock) (TRS' : list (list Z)) (B' np' : Z) (errv' : word),
      ms' = MS (mkR x1 (Z_to_bv 64 SA) gp tp t0 t1 t2 sp (Z_to_bv 64 SA) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
               Fx' (ret_pc x1) fcx' None m' (seg_rom bsegs)
      /\ ( (a0 = Z_to_bv 64 0 /\ pv_exit Q m' mo' g' LB' TRS' B' np' errv' loc jb shp Fx' fcx' 0)
        \/ (a0 = Z_to_bv 64 1 /\ exists buf' len' off' bs',
              PVX Q depc m' mo' g' LB' TRS' B' np' errv' buf' len' off' bs' loc jb shp Fx' fcx' /\ pb_nul bs' len' off') ).

  Lemma pvx_rec : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb shp Fx fcx (d : nat) (c : Z) (Bc : list cblock)
      (x1 t0 t1 t2 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    PVX Q depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb shp Fx fcx ->
    (d < n)%nat -> cj_chain CJ_PRINTABLE m d c Bc -> c <> 0 -> (forall b, In b Bc -> In b B) ->
    0 <= depc -> depc + Z.of_nat d <= 2^40 -> 0x81ed8 <= bv_unsigned x1 < AIMG_HI ->
    LSCPS bsegs (rec_kpost depc loc jb shp x1 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27)
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp t0 t1 t2 sp (Z_to_bv 64 SA) (Z_to_bv 64 c) (Z_to_bv 64 PB) a2 a3 a4 a5 a6 a7
              x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) Fx (wz PVALUE_ENTRY) fcx None mm (seg_rom bsegs)) mo1 g1.
  Proof.
    intros until t6. intros [CTX FRX] Dn CHc CNZ SUB DEPc DEPd RX. lits. bandM. sepM.
    pose proof (pvx_pb_below _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX FRX) as PBW.
    pose proof (pvm_allow Q PVL _ _ _ _ _ _ _ _ _ _ _ _ _ CTX) as [HBA HNA].
    pose proof (pvm_chain Q PVL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX CHc SUB) as CHcn.
    (nelimp CTX 19%nat; intros HL HP PBS1 ARR LEN PN ERR MI PVA CHN CC SSZ HB16 HB8 GM TV L0 HB HNP).
    (nelimp FRX 11%nat; intros SAVW LOC LL PAD ST HDR BODY SHC L16 FRM FA).
    destruct (pvx_chain_own _ _ _ _ _ _ FRX CC) as [CCX CHOKX].
    (nelimp PN 3%nat; intros PN1 PN2 PN3).
    assert (E1 : bv_unsigned (Z_to_bv 64 SA) = SA) by (apply unsigned_lit; lia).
    assert (LFR1 : lf_room 1 ((Fr, 1) :: LF) (Z.of_nat d)).
    { eapply lf_room_mono; [eapply lf_room_push; [exact LFR| lia]| lia]. }
    eapply lscps_mono.
    { eapply (REC d Dn) with (lo := lo) (LR := LR) (B := Bc) (bs := bs) (dep := depc) (CH := (SP, bv_unsigned ra, bv_unsigned s0) :: CH);
        rewrite ?E1;
        first [ exact HL | exact HP | exact PBS1 | split; [exact ARR| exact LEN] | exact PN | exact CHcn | exact CNZ | exact ST | exact ERR | exact MI
              | exact TP | exact FRM | exact SSZ | exact TV | exact HNA | exact LFR1 | exact CCX | exact HBA | reflexivity
              | intros b Hb; apply BLR, SUB, Hb
              | intros _; exact PBW
              | intros E8; exfalso; (cut_to PL1 GSA1 E8; lia)
              | split; [lia| split; [lia| lia]]
              | eapply chain_ok_mono; [exact CHOKX| lia]
              | cbn; split; [reflexivity| lia]
              | apply Forall_cons; [unfold fr_f; cbn; lia| exact CHB]
              | apply not_pc0_high; lia
              | unfold APV_STACK in *; (lia_on DEPd PB8 CEIL LO GSA1 GSA2 S47 TOP BOT PB80 Dn RX)
              | Z.div_mod_to_equations; lia
              | lia ]. }
    cbv beta. intros ms2 mo2 g2 PO.
    (nelim PO 30%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Fx' fcx' m2 errv2 -> MI2 FRM2 FA2 ST2 ERR2 PVE CHc2 GM2 CCX2 OUT)
.
    rewrite ?E1 in ST2, PVE.
    (nelim (pvx_after_agree _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX FRX PVE) 12%nat; intros SAVW2 LOC2 PAD2 HDR2 BODY2 SHC2 PVA2 CHN2 CC2 SSZ2 HB16' HB8').
    assert (FA2' : FAG18 F Fx') by (eapply FAG18_callee; [exact FA| exact FA2]).
    assert (FRX2 : PVFR Q m2 loc jb shp Fx' fcx').
    { split; [exact SAVW2|]. split; [exact LOC2|]. split; [exact LL|]. split; [exact PAD2|]. split; [exact ST2|].
      split; [exact HDR2|]. split; [exact BODY2|]. split; [exact SHC2|]. split; [exact L16|]. split; [exact FRM2| exact FA2']. }
    assert (GM2' : gmono g g2) by (eapply gmono_trans; [exact GM| exact GM2]).
    unfold rec_kpost. nexists 15%nat. exists Fx', fcx', m2.
    (nelim OUT 10%nat; intros LB2 TRS2 B2 np2 buf' len' off' HL2 TV2 OUT).
    exists LB2, TRS2, B2, np2, errv2. split; [reflexivity|].
    destruct OUT as [(-> & (dep' & PBSn) & HBn & HB2 & HN2) | (-> & (bs' & HPn & PBSn & PDn & PNn & NUL) & LL' & HB2 & HN2)].
    - left. split; [reflexivity|].
      split; [exact FRX2|]. split; [exact HL2|]. split; [exact ERR2|]. split; [exact MI2|]. split; [exact PVA2|]. split; [exact CHN2|].
      split; [exact CC2|]. split; [exact GM2'|]. split; [exact TV2|].
      exists buf', len', off'. left. split; [reflexivity|]. split; [exists dep'; exact PBSn|]. split; [exact HBn|].
      eapply (pvm_pot_fail Q PVL len B1 np1); [exact L0| unfold INT_MAX; lia| exact HB| exact HNP| exact HB2| exact HN2].
    - right. split; [reflexivity|]. exists buf', len', off', bs'. split; [| exact NUL]. split; [| exact FRX2].
      destruct PDn as [ARRn LENn].
      split; [exact HL2|]. split; [exact HPn|]. split; [exact PBSn|]. split; [exact ARRn|]. split; [exact LENn|]. split; [exact PNn|].
      split; [exact ERR2|]. split; [exact MI2|]. split; [exact PVA2|]. split; [exact CHN2|]. split; [exact CC2|]. split; [exact SSZ2|].
      split; [exact HB16'|]. split; [exact HB8'|]. split; [exact GM2'|]. split; [exact TV2|].
      eapply (pvm_pot_grow Q len B1 np1); [exact L0| exact HB| exact HNP| exact HB2| exact HN2| exact LL'].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pvx_pstr : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb shp Fx fcx (sv : Z) (Bv : list cblock)
      (x1 t0 t1 t2 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    PVX Q depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb shp Fx fcx ->
    cj_str m sv Bv -> (forall b, In b Bv -> In b B) -> 0x81ed8 <= bv_unsigned x1 ->
    LSCPS bsegs (rec_kpost depc loc jb shp x1 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27)
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp t0 t1 t2 sp (Z_to_bv 64 SA) (Z_to_bv 64 sv) (Z_to_bv 64 PB) a2 a3 a4 a5 a6 a7
              x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) Fx (wz APSTR_ENTRY) fcx None mm (seg_rom bsegs)) mo1 g1.
  Proof.
    intros until t6. intros [CTX FRX] SV SUB RX. lits. bandM. sepM.
    pose proof (pvx_pb_below _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX FRX) as PBW.
    pose proof (pvm_allow Q PVL _ _ _ _ _ _ _ _ _ _ _ _ _ CTX) as [HBA HNA].
    pose proof (pvm_str Q PVL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX SV SUB) as SVn.
    (nelimp CTX 19%nat; intros HL HP PBS1 ARR LEN PN ERR MI PVA CHN CC SSZ HB16 HB8 GM TV L0 HB HNP).
    (nelimp FRX 11%nat; intros SAVW LOC LL PAD ST HDR BODY SHC L16 FRM FA).
    (nelimp PN 3%nat; intros PN1 PN2 PN3).
    assert (E1 : bv_unsigned (Z_to_bv 64 SA) = SA) by (apply unsigned_lit; lia).
    eapply lscps_mono.
    { eapply PSTR with (lo := lo) (LR := LR) (Bv := Bv) (bs := bs) (dep := depc); rewrite ?E1;
        first [ exact HL | exact HP | exact PBS1 | split; [exact ARR| exact LEN] | exact PN | exact SVn | exact PBW | exact ST | exact ERR | exact MI
              | exact TP | exact FRM | exact SSZ | exact TV | exact HNA | exact HBA | reflexivity
              | intros b Hb; apply BLR, SUB, Hb
              | split; [lia| split; [lia| lia]]
              | apply not_pc0_high; lia
              | unfold APSTR_STACK in *; (lia_on PL1 PB8 CEIL LO N1 FLO SPR GSA1 PB80 S47 TOP BOT GSA2 KHE RX)
              | Z.div_mod_to_equations; lia
              | lia ]. }
    cbv beta. intros ms2 mo2 g2 PO.
    (nelim PO 28%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Fx' fcx' m2 errv2 -> MI2 FRM2 FA2 ST2 ERR2 PVE GM2 OUT)
.
    rewrite ?E1 in ST2, PVE.
    (nelim (pvx_after_agree _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX FRX PVE) 12%nat; intros SAVW2 LOC2 PAD2 HDR2 BODY2 SHC2 PVA2 CHN2 CC2 SSZ2 HB16' HB8').
    assert (FA2' : FAG18 F Fx') by (eapply FAG18_callee; [exact FA| exact FA2]).
    assert (FRX2 : PVFR Q m2 loc jb shp Fx' fcx').
    { split; [exact SAVW2|]. split; [exact LOC2|]. split; [exact LL|]. split; [exact PAD2|]. split; [exact ST2|].
      split; [exact HDR2|]. split; [exact BODY2|]. split; [exact SHC2|]. split; [exact L16|]. split; [exact FRM2| exact FA2']. }
    assert (GM2' : gmono g g2) by (eapply gmono_trans; [exact GM| exact GM2]).
    unfold rec_kpost. nexists 15%nat. exists Fx', fcx', m2.
    (nelim OUT 10%nat; intros LB2 TRS2 B2 np2 buf' len' off' HL2 TV2 OUT).
    exists LB2, TRS2, B2, np2, errv2. split; [reflexivity|].
    destruct OUT as [(-> & (dep' & PBSn) & HBn & HB2 & HN2) | (-> & (bs' & HPn & PBSn & PDn & PNn & NUL) & LL' & HB2 & HN2)].
    - left. split; [reflexivity|].
      split; [exact FRX2|]. split; [exact HL2|]. split; [exact ERR2|]. split; [exact MI2|]. split; [exact PVA2|]. split; [exact CHN2|].
      split; [exact CC2|]. split; [exact GM2'|]. split; [exact TV2|].
      exists buf', len', off'. left. split; [reflexivity|]. split; [exists dep'; exact PBSn|]. split; [exact HBn|].
      eapply (pvm_pot_fail Q PVL len B1 np1); [exact L0| unfold INT_MAX; lia| exact HB| exact HNP| exact HB2| exact HN2].
    - right. split; [reflexivity|]. exists buf', len', off', bs'. split; [| exact NUL]. split; [| exact FRX2].
      destruct PDn as [ARRn LENn].
      split; [exact HL2|]. split; [exact HPn|]. split; [exact PBSn|]. split; [exact ARRn|]. split; [exact LENn|]. split; [exact PNn|].
      split; [exact ERR2|]. split; [exact MI2|]. split; [exact PVA2|]. split; [exact CHN2|]. split; [exact CC2|]. split; [exact SSZ2|].
      split; [exact HB16'|]. split; [exact HB8'|]. split; [exact GM2'|]. split; [exact TV2|].
      eapply (pvm_pot_grow Q len B1 np1); [exact L0| exact HB| exact HNP| exact HB2| exact HN2| exact LL'].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pvx_below_SA : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 sbuf slen buf len off bs loc jb shp Fx fcx mm' u,
    PVMs Q depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 sbuf slen buf len off bs -> PVFR Q mm loc jb shp Fx fcx ->
    munch [(u, SA)] mm mm' -> wmono bsegs mm mm' -> lo <= u -> mem_inv bsegs mm' -> stk bsegs mm' lo SA ->
    PVMs Q depc mm' mo1 g1 LB1 TRS1 B1 np1 errv1 sbuf slen buf len off bs /\ PVFR Q mm' loc jb shp Fx fcx.
  Proof.
    intros until u. intros CTX FRX MU WM HU MI' ST'. lits. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM.
    (nelimp CTX 19%nat; intros HL HP PBS1 ARR LEN PN ERR MI PVA CHN CC SSZ HB16 HB8 GM TV L0 HB HNP).
    (nelimp FRX 11%nat; intros SAVW LOC LL PAD ST HDR BODY SHC L16 FRM FA).
    assert (HLR : forall b, In b LR -> In b LB1) by (intros b Hb; eapply Permutation_in; [exact HP| right; exact Hb]).
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 _ _ R4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    assert (OWN : Forall (pv_own_iv Q) [(u, SA)]) by (constructor; [unfold pv_own_iv; cbn [fst snd]; lia| constructor]).
    unfold PVMs, PVFR. unfold PBS in PBS1 |- *. unfold SAVEDV in SAVW |- *. unfold FHDR in HDR |- *. unfold FBODY in BODY |- *. unfold SHCV, SHCW in SHC |- *. unfold AERRNO, ATP in ERR |- *.
    split.
    - split; [eapply (pvm_art_store Q PVL); [exact HL| exact MU| exact WM| exact OWN]|]. split; [exact HP|].
      split; [eapply (rw_cells_transport bsegs); [exact PBS1| exact MU| exact WM| dj]|].
      split; [eapply u8arr_transport; [exact ARR| exact MU| exact WM| rewrite LEN; dj]|]. split; [exact LEN|]. split; [exact PN|].
      split; [eapply (rw_cells_transport bsegs); [exact ERR| exact MU| exact WM| dj]|]. split; [exact MI'|].
      split; [eapply (pvm_agree_store Q PVL); [exact HL| exact HLR| exact MU| exact WM| exact OWN| exact PVA]|].
      split. { eapply cj_chain_frame; [exact CHN| exact MU| exact WM|]. intros A k Hin. cbn.
               (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (HLR _ (BLR _ Hin))) 4%nat; intros Q1 _ _ Q4). try rewrite alloc_ceiling_eq in Q4. lia. }
      split; [eapply (pvm_chain_cells_store Q PVL); [exact CC| exact MU| exact OWN]|].
      split; [eapply (pvm_sh_zero_store Q PVL); [exact SSZ| exact MU| exact OWN]|].
      destruct (pvm_below_store Q PVL _ _ _ HB16 HB8 MU OWN) as [HB16' HB8'].
      split; [exact HB16'|]. split; [exact HB8'|]. split; [exact GM|]. split; [exact TV|]. split; [exact L0|]. split; [exact HB| exact HNP].
    - split; [eapply (rw_cells_transport bsegs); [exact SAVW| exact MU| exact WM| dj]|].
      split; [eapply (rw_cells_transport bsegs); [exact LOC| exact MU| exact WM| dj]|]. split; [exact LL|].
      split; [eapply stk_transport_disjoint; [exact PAD| exact MU| exact WM| dj]|]. split; [exact ST'|].
      split; [eapply (rw_cells_transport bsegs); [exact HDR| exact MU| exact WM| dj]|].
      split; [eapply (rw_cells_transport bsegs); [exact BODY| exact MU| exact WM| dj]|].
      split; [eapply (rw_cells_transport bsegs); [exact SHC| exact MU| exact WM| dj]|].
      split; [exact L16|]. split; [exact FRM| exact FA].
  Qed.

  (* [comment removed for export] *)
  Definition strlen_kpost (depc : Z) (mo1 : Model) (g1 : lghost) (LB1 : list cblock) (TRS1 : list (list Z)) (B1 np1 : Z) (errv1 : word)
      (buf len off : Z) (bs : list byte) (loc : list word) (jb : list byte) (shp : list Z) (Fx : bvmap 5 word) (fcx : bv 32)
      (x1 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) : machine_state -> Prop :=
    fun ms' => exists (k : Z) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
      ms' = MS (mkR x1 (Z_to_bv 64 SA) gp tp t0 t1 t2 sp (Z_to_bv 64 SA) (Z_to_bv 64 k) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
               Fx (ret_pc x1) fcx None m' (seg_rom bsegs)
      /\ PVX Q depc m' mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb shp Fx fcx
      /\ 0 <= k /\ off + k < len /\ nth_error bs (Z.to_nat (off + k)) = Some (wb 0).

  Lemma pvx_strlen_off : forall depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb shp Fx fcx
      (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    PVX Q depc mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb shp Fx fcx -> pb_nul bs len off ->
    evt bsegs (strlen_kpost depc mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb shp Fx fcx x1 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27)
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp t0 t1 t2 sp (Z_to_bv 64 SA) (Z_to_bv 64 (buf + off)) a1 a2 a3 a4 a5 a6 a7
              x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) Fx (Z_to_bv 64 ASTRLEN_T) fcx None mm (seg_rom bsegs)).
  Proof.
    intros until t6. intros [CTX FRX] NUL. lits. bandM. sepM.
    (nelimp CTX 9%nat; intros HL HP PBS1 ARR LEN PN ERR MI _).
    (nelimp FRX 6%nat; intros SAVW LOC LL PAD ST _).
    (nelimp PN 3%nat; intros PN1 PN2 PN3).
    assert (E1 : bv_unsigned (Z_to_bv 64 SA) = SA) by (apply unsigned_lit; lia).
    eapply evt_cut.
    { eapply (strlen_off_ok AI STRLEN) with (lo := lo) (off := off) (buf := buf) (len := len) (bs := bs); rewrite ?E1;
        first [ exact HL | eapply perm_in_head; exact HP | exact ARR | exact LEN | exact NUL | exact MI | exact ST | reflexivity | lia ]. }
    cbv beta. intros ms' PO.
    (nelim PO 24%nat; intros k t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' -> MU WM MI' ST' K0 K1 KN).
    rewrite ?E1 in MU, ST'.
    destruct (pvx_below_SA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX FRX MU WM ltac:(lia) MI' ST') as [CTX' FRX'].
    apply evt_done. unfold strlen_kpost. exists k. nexists 14%nat. exists m'. split; [reflexivity|].
    split; [split; [exact CTX'| exact FRX']|]. split; [exact K0|]. split; [exact K1| exact KN].
  Qed.
End PVK.


End CeilWrap.
