(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSums_u5 ParseSums2_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSpecs_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5 ParseBridges3_u5 ParseBridges4_u5 ParseSomeAt_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallKn.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module SPA.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.

Abbreviation wincells := PSA.wincells.
Abbreviation estart_uv := PSA.estart_uv.  Abbreviation elen_uv := PSA.elen_uv.  Abbreviation elen_lit := PSA.elen_lit.  Abbreviation krange_uv := PSA.krange_uv.

Section Sem.
Variable C : PSK.consts.
Hypothesis C_vtp : PSK.c_vt_parser C = PML.VT_PARSER.
Hypothesis C_vtf : PSK.c_vt_func C = PML.VT_FUNC.
Hypothesis C_hull : PSK.c_hull_lo C = 0x10000 /\ PSK.c_hull_hi C = 0xfe000.
Hypothesis C_scr : 0 <= PSK.c_scr C <= 2 ^ 20.
Variables (Pe Ve Ee spe wende : expr) (X : PSK.pexprs).
Variables (E : env) (M : mem).
Variables (Pv Ev Vv spv : Z) (ps : PML.pstate) (linev posv ecv : Z).
Hypothesis UP : uv E Pe = Pv.   Hypothesis UE : uv E Ee = Ev.   Hypothesis UV : uv E Ve = Vv.   Hypothesis USP : uv E spe = spv.
Hypothesis RP : 2 ^ 40 <= Pv /\ Pv + 272 <= 2 ^ 47.   Hypothesis RE : 2 ^ 40 <= Ev /\ Ev + 16 <= 2 ^ 47.   Hypothesis RV : 2 ^ 40 <= Vv /\ Vv + 8 <= 2 ^ 47.
Hypothesis RSP : 2 ^ 40 <= spv - PSK.c_scr C /\ spv <= 2 ^ 47.
Hypothesis HPA : PML.parser_at M Pv ps.
(* [comment removed for export] *)
Hypothesis L_level : uv E (PSK.x_level X) = PML.ps_level ps.
Hypothesis L_wptr : edenot E (PSK.x_wptr X) = Z_to_bv 64 (fst (wincells (PML.ps_win ps))).
Hypothesis L_wend : edenot E wende = Z_to_bv 64 (snd (wincells (PML.ps_win ps))).
Hypothesis L_st : uv E (PSK.x_st X) = PML.ps_st ps.   Hypothesis L_sst : uv E (PSK.x_sst X) = PML.ps_sst ps.   Hypothesis L_nst : uv E (PSK.x_nst X) = PML.ps_nst ps.
Hypothesis L_more : uv E (PSK.x_more X) = PML.b2z (PML.ps_more ps).   Hypothesis L_done : uv E (PSK.x_done X) = PML.b2z (PML.ps_done ps).
Hypothesis L_k : 2 * uv E (PSK.x_k X) = PML.ps_bcap ps.   Hypothesis L_size : uv E (PSK.x_size X) = Z.of_nat (length (PML.ps_buf ps)).   Hypothesis L_p : uv E (PSK.x_p X) = PML.ps_bptr ps.
Hypothesis L_sb : uv E (PSK.x_sb X) = PML.ps_sb ps.   Hypothesis L_slen : uv E (PSK.x_slen X) = Z.of_nat (length (PML.ps_stack ps)).   Hypothesis L_scap : uv E (PSK.x_scap X) = PML.ps_scap ps.
Hypothesis L_line : uv E (PSK.x_line X) = linev.   Hypothesis C160 : PML.u64 M (Pv + 160) linev.
Hypothesis L_pos : uv E (PSK.x_pos X) = posv.   Hypothesis C168 : PML.u64 M (Pv + 168) posv.
Hypothesis L_ec : uv E (PSK.x_ec X) = ecv.   Hypothesis CEC : PML.u32 M Ev ecv.
(* [comment removed for export] *)
Hypothesis N_level : 0 <= PML.ps_level ps <= 1025.
Hypothesis N_st : 0 <= PML.ps_st ps <= 255 /\ 0 <= PML.ps_sst ps <= 255 /\ 0 <= PML.ps_nst ps <= 255.
Hypothesis N_buf : Z.of_nat (length (PML.ps_buf ps)) < 2 ^ 26 /\ PML.ps_bcap ps <= 2 ^ 27.
Hypothesis N_stk : 1 <= Z.of_nat (length (PML.ps_stack ps)) <= 1027 /\ 66 <= PML.ps_scap ps <= 1056.
(* [comment removed for export] *)
Variable L : heap_layout.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis B_buf : block_range L (PML.ps_bptr ps) (PML.ps_bcap ps) /\ L5.defined M (PML.ps_bptr ps) (PML.ps_bcap ps).
Hypothesis B_stk : block_range L (PML.ps_sb ps) (PML.ps_scap ps) /\ L5.defined M (PML.ps_sb ps) (PML.ps_scap ps).
Hypothesis B_apart : PML.ps_bptr ps + PML.ps_bcap ps <= PML.ps_sb ps \/ PML.ps_sb ps + PML.ps_scap ps <= PML.ps_bptr ps.
Hypothesis B_ceil : hl_ceil L <= spv - PSK.c_scr C /\ spv <= Pv /\ spv <= Ev /\ spv <= Vv.

Lemma kn_sem_ok : know_ok RSEGS E M (SPK.kn_sem C Pe Ve Ee spe wende X).
Proof.
  pose proof HPA as HPA'. unfold PML.parser_at in HPA'.
  destruct HPA' as (C0 & C8 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & S24 & S48 & S72 & C96 & C128 & C144 & CW & C208 & C209 & C210 & C211 & C212 & C213 & C216 & Hstr & Hb264 & C248 & C256 & C264 & Hstk & Hsl & HdefP).
  assert (CWc : PML.u64 M (Pv + 200) (fst (wincells (PML.ps_win ps))) /\ PML.u64 M (Pv + 192) (snd (wincells (PML.ps_win ps)))).
  { destruct (PML.ps_win ps) as [[p e]|]; cbn [wincells fst snd]; [destruct CW as (A & B & _) | destruct CW as (B & A)]; split; assumption. }
  destruct CWc as [C200 C192].
  destruct RP as [RP1 RP2], RE as [RE1 RE2], RV as [RV1 RV2], RSP as [RS1 RS2].
  destruct N_st as (NS1 & NS2 & NS3), N_buf as [NB1 NB2], N_stk as [NK1 NK2].
  destruct B_buf as [(BB0 & BB1 & BB2 & BB3 & BB4) BBD], B_stk as [(BS0 & BS1 & BS2 & BS3 & BS4) BSD], B_ceil as (BC1 & BC2 & BC3 & BC4), C_hull as [CH1 CH2].
  pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
  destruct Hstr as (Hlong & Hc8 & Hlt).
  set (bcap := PML.ps_bcap ps) in *. set (bptr := PML.ps_bptr ps) in *. set (sb := PML.ps_sb ps) in *. set (scap := PML.ps_scap ps) in *.
  set (size := Z.of_nat (length (PML.ps_buf ps))) in *. set (slen := Z.of_nat (length (PML.ps_stack ps))) in *.
  assert (Uk : uv E (PSK.x_k X) = bcap / 2) by (rewrite <- L_k, Z.mul_comm, Z.div_mul by lia; reflexivity).
  assert (U2k : uv E (APC.escale 2 (PSK.x_k X)) = bcap) by (rewrite PB.uv_escale, L_k; apply Z.mod_small; lia).
  assert (ESP : forall o, estart E (SA Pe o) = Pv + o) by (intros o; rewrite estart_uv, UP; reflexivity).
  assert (SHORT : forall o, L5.lstr_short RSEGS M (Pv + o) [] -> PML.u8 M (Pv + o) 0 /\ PML.u8 M (Pv + (o + 1)) 0).
  { intros o (_ & H0 & _ & H1). cbn [length] in H0, H1. split; [exact H0|]. replace (Pv + (o + 1)) with (Pv + o + 1 + Z.of_nat 0) by lia. exact H1. }
  destruct (SHORT 24 S24) as [C24 C25]. destruct (SHORT 48 S48) as [C48 C49]. destruct (SHORT 72 S72) as [C72 C73].
  (* [comment removed for export] *)
  assert (HW : PML.u64 M (Pv + 224) (bcap + 1) /\ PML.u64 M (Pv + 232) size /\ PML.u64 M (Pv + 240) bptr /\ PML.u8 M (bptr + size) 0).
  { destruct Hlong as (_ & H0 & H8 & H16 & _ & HN). replace (Pv + 224 + 8) with (Pv + 232) in H8 by lia. replace (Pv + 224 + 16) with (Pv + 240) in H16 by lia. repeat split; assumption. }
  destruct HW as (W0 & W8 & W16 & WNUL).
  unfold SPK.kn_sem. unfold know_ok. rewrite !Forall_app. split; [|split; [|split; [|split]]].
  - (* [comment removed for export] *) unfold PSK.pconst, PSK.kw.
    apply Forall_cons; [eapply CL5.kword64_intro with (A := Pv + 0); [apply ESP | lia | lia | rewrite C_vtp; reflexivity | replace (Pv + 0) with Pv by lia; exact C0]|].
  apply Forall_cons; [eapply PB.kword32_intro with (A := Pv + 8); [apply ESP | lia | lia | reflexivity | exact C8]|].
  apply Forall_cons; [eapply PB2.kword8_intro with (A := Pv + 12); [apply ESP | lia | lia | reflexivity | lia | exact C12]|].
  apply Forall_cons; [eapply PB2.kword8_intro with (A := Pv + 13); [apply ESP | lia | lia | reflexivity | lia | exact C13]|].
  apply Forall_cons; [eapply PB2.kword8_intro with (A := Pv + 14); [apply ESP | lia | lia | reflexivity | lia | exact C14]|].
  apply Forall_cons; [eapply PB2.kword8_intro with (A := Pv + 15); [apply ESP | lia | lia | reflexivity | lia | exact C15]|].
  apply Forall_cons; [eapply PB2.kword8_intro with (A := Pv + 16); [apply ESP | lia | lia | reflexivity | lia | exact C16]|].
  apply Forall_cons; [eapply PB2.kword8_intro with (A := Pv + 17); [apply ESP | lia | lia | reflexivity | lia | exact C17]|].
  apply Forall_cons; [eapply PB2.kword8_intro with (A := Pv + 18); [apply ESP | lia | lia | reflexivity | lia | exact C18]|].
  apply Forall_cons; [eapply PB2.kword8_intro with (A := Pv + 24); [apply ESP | lia | lia | reflexivity | lia | exact C24]|].
  apply Forall_cons; [eapply PB2.kword8_intro with (A := Pv + 25); [apply ESP | lia | lia | reflexivity | lia | exact C25]|].
  apply Forall_cons; [eapply PB2.kword8_intro with (A := Pv + 48); [apply ESP | lia | lia | reflexivity | lia | exact C48]|].
  apply Forall_cons; [eapply PB2.kword8_intro with (A := Pv + 49); [apply ESP | lia | lia | reflexivity | lia | exact C49]|].
  apply Forall_cons; [eapply PB2.kword8_intro with (A := Pv + 72); [apply ESP | lia | lia | reflexivity | lia | exact C72]|].
  apply Forall_cons; [eapply PB2.kword8_intro with (A := Pv + 73); [apply ESP | lia | lia | reflexivity | lia | exact C73]|].
  apply Forall_cons; [eapply CL5.kword64_intro with (A := Pv + 96); [apply ESP | lia | lia | rewrite C_vtf; reflexivity | exact C96]|].
  apply Forall_cons; [eapply CL5.kword64_intro with (A := Pv + 128); [apply ESP | lia | lia | apply PB.edenot_of_uv; rewrite PB.uv_eaddz, UP; apply Z.mod_small; lia | exact C128]|].
  apply Forall_cons; [eapply PB2.kword8_intro with (A := Pv + 213); [apply ESP | lia | lia | reflexivity | lia | exact C213]|].
  apply Forall_cons; [eapply PB.kword32_intro with (A := Pv + 216); [apply ESP | lia | lia | reflexivity | exact C216]|].
    apply Forall_nil.
  - (* [comment removed for export] *) unfold PSK.pstate_cells, PSK.kw.
  apply Forall_cons; [eapply PB.kword32_intro with (A := Pv + 144); [apply ESP | lia | lia | apply PB.edenot_of_uv; exact L_level | exact C144]|].
  apply Forall_cons; [eapply CL5.kword64_intro with (A := Pv + 192); [apply ESP | lia | lia | exact L_wend | exact C192]|].
  apply Forall_cons; [eapply CL5.kword64_intro with (A := Pv + 200); [apply ESP | lia | lia | exact L_wptr | exact C200]|].
  apply Forall_cons; [eapply PB2.kword8_intro with (A := Pv + 208); [apply ESP | lia | lia | apply PB.edenot_of_uv; exact L_st | first [lia | destruct (PML.ps_more ps); cbn; lia | destruct (PML.ps_done ps); cbn; lia] | exact C208]|].
  apply Forall_cons; [eapply PB2.kword8_intro with (A := Pv + 209); [apply ESP | lia | lia | apply PB.edenot_of_uv; exact L_sst | first [lia | destruct (PML.ps_more ps); cbn; lia | destruct (PML.ps_done ps); cbn; lia] | exact C209]|].
  apply Forall_cons; [eapply PB2.kword8_intro with (A := Pv + 210); [apply ESP | lia | lia | apply PB.edenot_of_uv; exact L_nst | first [lia | destruct (PML.ps_more ps); cbn; lia | destruct (PML.ps_done ps); cbn; lia] | exact C210]|].
  apply Forall_cons; [eapply PB2.kword8_intro with (A := Pv + 211); [apply ESP | lia | lia | apply PB.edenot_of_uv; exact L_more | first [lia | destruct (PML.ps_more ps); cbn; lia | destruct (PML.ps_done ps); cbn; lia] | exact C211]|].
  apply Forall_cons; [eapply PB2.kword8_intro with (A := Pv + 212); [apply ESP | lia | lia | apply PB.edenot_of_uv; exact L_done | first [lia | destruct (PML.ps_more ps); cbn; lia | destruct (PML.ps_done ps); cbn; lia] | exact C212]|].
  apply Forall_cons; [eapply CL5.kword64_intro with (A := Pv + 224); [apply ESP | lia | lia | apply PB.edenot_of_uv; rewrite PB.uv_eaddz, U2k; apply Z.mod_small; lia | exact W0]|].
  apply Forall_cons; [eapply CL5.kword64_intro with (A := Pv + 232); [apply ESP | lia | lia | apply PB.edenot_of_uv; exact L_size | exact W8]|].
  apply Forall_cons; [eapply CL5.kword64_intro with (A := Pv + 240); [apply ESP | lia | lia | apply PB.edenot_of_uv; exact L_p | exact W16]|].
  apply Forall_cons; [eapply CL5.kword64_intro with (A := Pv + 248); [apply ESP | lia | lia | apply PB.edenot_of_uv; exact L_sb | exact C248]|].
  apply Forall_cons; [eapply CL5.kword64_intro with (A := Pv + 256); [apply ESP | lia | lia | apply PB.edenot_of_uv; rewrite PB.uv_eadd, L_sb, L_slen; apply Z.mod_small; lia | exact C256]|].
  apply Forall_cons; [eapply CL5.kword64_intro with (A := Pv + 264); [apply ESP | lia | lia | apply PB.edenot_of_uv; rewrite PB.uv_eadd, L_sb, L_scap; apply Z.mod_small; lia | exact C264]|].
  apply Forall_cons; [eapply CL5.kword64_intro with (A := Pv + 160); [apply ESP | lia | lia | apply PB.edenot_of_uv; exact L_line | exact C160]|].
  apply Forall_cons; [eapply CL5.kword64_intro with (A := Pv + 168); [apply ESP | lia | lia | apply PB.edenot_of_uv; exact L_pos | exact C168]|].
    apply Forall_nil.
  - (* [comment removed for export] *) unfold PSK.strblk, PSK.kw.
    assert (Usp : uv E (APC.eadd (PSK.x_size X) (PSK.x_p X)) = size + bptr) by (rewrite PB.uv_eadd, L_size, L_p; apply Z.mod_small; unfold hl_ceil in *; lia).
    apply Forall_cons; [apply (PB.kword8_zero_intro E M _ (bptr + size)); [rewrite estart_uv, Usp; lia | lia | unfold hl_ceil in *; lia | exact WNUL]|].
    apply Forall_cons; [apply krange_uv; rewrite Uk; split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]|].
    apply Forall_cons; [apply krange_uv; rewrite PB.uv_esub, PB.uv_eaddz, U2k, L_size; rewrite (Z.mod_small (bcap + -1)) by lia; rewrite Z.mod_small by lia; lia|].
    apply Forall_cons; [cbn [kentry_ok]; fold (uv E (APC.escale 2 (PSK.x_k X))); rewrite U2k; split; [lia | exact Hc8]|].
    apply Forall_cons; [eapply CL5.kunk_intro with (A := bptr) (N := bcap); [rewrite estart_uv, L_p; lia | rewrite elen_uv; exact U2k | lia | unfold hl_ceil in *; lia | unfold hl_ceil in *; lia | exact BBD]|].
    apply Forall_cons; [eapply CL5.kwr_intro with (A := bptr) (N := bcap); [rewrite estart_uv, L_p; lia | rewrite elen_uv; exact U2k | lia | unfold hl_ceil in *; lia | unfold hl_ceil in *; lia | exact BBD]|].
    apply Forall_cons; [apply krange_uv; rewrite L_p; unfold hl_ceil in *; lia|].
    apply Forall_cons; [cbn [kentry_ok]; fold (uv E (PSK.x_p X)); rewrite L_p; split; [lia | exact BB2]|].
    apply Forall_nil.
  - (* [comment removed for export] *) unfold SPK.objs_h, PSK.kw.
    apply Forall_cons; [eapply PB.kword32_intro with (A := Ev + 0); [rewrite estart_uv, UE; reflexivity | lia | lia | apply PB.edenot_of_uv; exact L_ec | replace (Ev + 0) with Ev by lia; exact CEC]|].
    apply Forall_cons; [eapply CL5.kunk_intro with (A := sb) (N := scap); [rewrite estart_uv, L_sb; lia | rewrite elen_uv; exact L_scap | lia | unfold hl_ceil in *; lia | unfold hl_ceil in *; lia | exact BSD]|].
    apply Forall_cons; [eapply CL5.kwr_intro with (A := sb) (N := scap); [rewrite estart_uv, L_sb; lia | rewrite elen_uv; exact L_scap | lia | unfold hl_ceil in *; lia | unfold hl_ceil in *; lia | exact BSD]|].
    apply Forall_cons; [apply krange_uv; rewrite L_sb; unfold hl_ceil in *; lia|].
    apply Forall_cons; [apply krange_uv; rewrite L_slen; lia|].
    apply Forall_cons; [apply krange_uv; rewrite L_scap; lia|].
    apply Forall_cons; [apply krange_uv; rewrite PB.uv_esub, L_scap, L_slen; rewrite Z.mod_small by lia; lia|].
    apply Forall_cons; [apply krange_uv; rewrite L_size; lia|].
    apply Forall_cons; [apply krange_uv; rewrite L_level; lia|].
    apply Forall_cons; [apply krange_uv; rewrite L_st; lia|].
    apply Forall_cons; [apply krange_uv; rewrite L_sst; lia|].
    apply Forall_cons; [apply krange_uv; rewrite L_nst; lia|].
    apply Forall_cons; [apply krange_uv; rewrite L_more; destruct (PML.ps_more ps); cbn; lia|].
    apply Forall_cons; [apply krange_uv; rewrite L_done; destruct (PML.ps_done ps); cbn; lia|].
    apply Forall_nil.
  - (* [comment removed for export] *) unfold SPK.disj_h, PSK.hull, PSK.kdisj. cbn [flat_map app].
    assert (ELS : elenZ E (ELit (PSK.c_scr C)) = PSK.c_scr C) by (apply elen_lit; lia).
    assert (EP : estart E (SA (PSK.x_p X) 0) = bptr) by (rewrite estart_uv, L_p; lia).
    assert (ES : estart E (SA (PSK.x_sb X) 0) = sb) by (rewrite estart_uv, L_sb; lia).
    assert (NP : elenZ E (APC.escale 2 (PSK.x_k X)) = bcap) by (rewrite elen_uv; exact U2k).
    assert (NS : elenZ E (PSK.x_scap X) = scap) by (rewrite elen_uv; exact L_scap).
    apply Forall_cons; [eapply CL5.kdisj_intro; [rewrite estart_uv, USP; reflexivity | exact ELS | exact EP | exact NP | unfold hl_ceil in *; lia]|].
    apply Forall_cons; [eapply CL5.kdisj_intro; [rewrite estart_uv, USP; reflexivity | exact ELS | exact ES | exact NS | unfold hl_ceil in *; lia]|].
    apply Forall_cons; [eapply CL5.kdisj_intro; [apply ESP | apply elen_lit; lia | exact EP | exact NP | unfold hl_ceil in *; lia]|].
    apply Forall_cons; [eapply CL5.kdisj_intro; [apply ESP | apply elen_lit; lia | exact ES | exact NS | unfold hl_ceil in *; lia]|].
    apply Forall_cons; [eapply CL5.kdisj_intro; [rewrite estart_uv, UE; reflexivity | apply elen_lit; lia | exact EP | exact NP | unfold hl_ceil in *; lia]|].
    apply Forall_cons; [eapply CL5.kdisj_intro; [rewrite estart_uv, UE; reflexivity | apply elen_lit; lia | exact ES | exact NS | unfold hl_ceil in *; lia]|].
    apply Forall_cons; [eapply CL5.kdisj_intro; [rewrite estart_uv, UV; reflexivity | apply elen_lit; lia | exact EP | exact NP | unfold hl_ceil in *; lia]|].
    apply Forall_cons; [eapply CL5.kdisj_intro; [rewrite estart_uv, UV; reflexivity | apply elen_lit; lia | exact ES | exact NS | unfold hl_ceil in *; lia]|].
    apply Forall_cons; [eapply CL5.kdisj_intro; [exact EP | exact NP | exact ES | exact NS | exact B_apart]|].
    apply Forall_cons; [eapply CL5.kdisj_intro; [exact EP | exact NP | unfold estart; cbn [a_base a_off edenot]; rewrite (u64_of_Z 0) by lia; reflexivity | apply elen_lit; lia | rewrite CH1, CH2; lia]|].
    apply Forall_cons; [eapply CL5.kdisj_intro; [exact ES | exact NS | unfold estart; cbn [a_base a_off edenot]; rewrite (u64_of_Z 0) by lia; reflexivity | apply elen_lit; lia | rewrite CH1, CH2; lia]|].
    apply Forall_nil.
Qed.
End Sem.

(* [comment removed for export] *)
Lemma sltu_sub_ne : forall Ex x c, uv Ex (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB x (ELit c)) (ELit 1)) = 0 -> 0 <= c < 2 ^ 64 -> uv Ex x <> c.
Proof.
  intros Ex x c H Hc Heq. unfold PB.uv in H. cbn [edenot] in H. rewrite u_sltu64, u_sub64 in H. cbn [edenot] in H. rewrite u_lit64 in H. unfold two64 in H.
  rewrite (Z.mod_small c) in H by lia. unfold PB.uv in Heq. rewrite Heq, Z.sub_diag in H. change (bv_unsigned (Z_to_bv 64 1)) with 1 in H. rewrite Z.mod_0_l in H by lia. cbn in H. discriminate H.
Qed.

(* [comment removed for export] *)
Section Frz.
Variable C : PSK.consts.
Hypothesis C_vtv : PSK.c_vt_visitor C = PML.VT_VISITOR.
Hypothesis C_img : PSK.c_img_lo C = 0x10000 /\ PSK.c_img_hi C = PML.IMG_RO_HI.
Hypothesis C_scr : 0 <= PSK.c_scr C <= 2 ^ 20.
Variables (Pe Ve Ee spe : expr) (E : env) (M : mem) (Pv Ev Vv spv : Z).
Hypothesis UP : uv E Pe = Pv.   Hypothesis UE : uv E Ee = Ev.   Hypothesis UV : uv E Ve = Vv.   Hypothesis USP : uv E spe = spv.
Hypothesis RP : 2 ^ 40 <= Pv /\ Pv + 272 <= 2 ^ 47.   Hypothesis RE : 2 ^ 40 <= Ev /\ Ev + 16 <= 2 ^ 47.   Hypothesis RV : 2 ^ 40 <= Vv /\ Vv + 8 <= 2 ^ 47.
Hypothesis RSP : 2 ^ 40 <= spv - PSK.c_scr C /\ spv <= 2 ^ 47.
Hypothesis DP : L5.defined M Pv 272.   Hypothesis DE : L5.defined M Ev 16.   Hypothesis DS : L5.defined M (spv - PSK.c_scr C) (PSK.c_scr C).
Hypothesis AP8 : Pv mod 8 = 0.   Hypothesis AS16 : spv mod 16 = 0.
Hypothesis HVIS : PML.vis_at M Vv.   Hypothesis HIMG : PML.img_ro M.
Hypothesis ABOVE : spv <= Pv /\ spv <= Ev /\ spv <= Vv.
Hypothesis APART : (Pv + 272 <= Ev \/ Ev + 16 <= Pv) /\ (Pv + 272 <= Vv \/ Vv + 8 <= Pv) /\ (Ev + 16 <= Vv \/ Vv + 8 <= Ev).

Lemma kn_frz_ok : know_ok RSEGS E M (SPK.kn_frz C false Pe Ve Ee spe).
Proof.
  destruct RP as [RP1 RP2], RE as [RE1 RE2], RV as [RV1 RV2], RSP as [RS1 RS2], ABOVE as (AB1 & AB2 & AB3), APART as (A1 & A2 & A3), C_img as [CI1 CI2].
  assert (ELS : elenZ E (ELit (PSK.c_scr C)) = PSK.c_scr C) by (apply elen_lit; lia).
  assert (ESS : estart E (SA spe (- PSK.c_scr C)) = spv - PSK.c_scr C) by (rewrite estart_uv, USP; lia).
  assert (ESP : forall o, estart E (SA Pe o) = Pv + o) by (intros o; rewrite estart_uv, UP; reflexivity).
  assert (ESE : forall o, estart E (SA Ee o) = Ev + o) by (intros o; rewrite estart_uv, UE; reflexivity).
  assert (ESV : forall o, estart E (SA Ve o) = Vv + o) by (intros o; rewrite estart_uv, UV; reflexivity).
  unfold SPK.kn_frz, know_ok. rewrite !Forall_app. split; [|split].
  - unfold SPK.objs_f, PSK.kw.
    apply Forall_cons; [eapply CL5.kwr_intro with (A := Pv + 0) (N := 272); [apply ESP | apply elen_lit; lia | lia | lia | lia | replace (Pv + 0) with Pv by lia; exact DP]|].
    apply Forall_cons; [apply krange_uv; rewrite UP; lia|].
    apply Forall_cons; [cbn [kentry_ok]; fold (uv E Pe); rewrite UP; split; [lia | exact AP8]|].
    apply Forall_cons; [eapply CL5.kwr_intro with (A := Ev + 0) (N := 16); [apply ESE | apply elen_lit; lia | lia | lia | lia | replace (Ev + 0) with Ev by lia; exact DE]|].
    apply Forall_cons; [apply krange_uv; rewrite UE; lia|].
    apply Forall_cons; [eapply CL5.kword64_intro with (A := Vv + 0); [apply ESV | lia | lia | rewrite C_vtv; reflexivity | replace (Vv + 0) with Vv by lia; exact HVIS]|].
    apply Forall_cons; [apply krange_uv; rewrite UV; lia|].
    apply Forall_nil.
  - unfold PSK.frame. cbn [app].
    apply Forall_cons; [eapply CL5.kunk_intro with (A := spv - PSK.c_scr C) (N := PSK.c_scr C); [exact ESS | exact ELS | lia | lia | lia | exact DS]|].
    apply Forall_cons; [eapply CL5.kwr_intro with (A := spv - PSK.c_scr C) (N := PSK.c_scr C); [exact ESS | exact ELS | lia | lia | lia | exact DS]|].
    apply Forall_cons; [apply krange_uv; rewrite USP; lia|].
    apply Forall_cons; [cbn [kentry_ok]; fold (uv E spe); rewrite USP; split; [lia | exact AS16]|].
    apply Forall_cons; [cbn [kentry_ok]; rewrite CI1, CI2; split; [lia | split; [unfold PML.IMG_RO_HI; lia | exact HIMG]]|].
    apply Forall_nil.
  - unfold SPK.disj_f, PSK.kdisj.
    apply Forall_cons; [eapply CL5.kdisj_intro; [exact ESS | exact ELS | apply ESP | apply elen_lit; lia | lia]|].
    apply Forall_cons; [eapply CL5.kdisj_intro; [exact ESS | exact ELS | apply ESE | apply elen_lit; lia | lia]|].
    apply Forall_cons; [eapply CL5.kdisj_intro; [exact ESS | exact ELS | apply ESV | apply elen_lit; lia | lia]|].
    apply Forall_cons; [eapply CL5.kdisj_intro; [apply ESP | apply elen_lit; lia | apply ESE | apply elen_lit; lia | lia]|].
    apply Forall_cons; [eapply CL5.kdisj_intro; [apply ESP | apply elen_lit; lia | apply ESV | apply elen_lit; lia | lia]|].
    apply Forall_cons; [eapply CL5.kdisj_intro; [apply ESE | apply elen_lit; lia | apply ESV | apply elen_lit; lia | lia]|].
    apply Forall_nil.
Qed.
End Frz.

(* [comment removed for export] *)
Definition pview_w (cells : list kentry) (Pb pe ce : expr) : option PB4.pvals2 :=
  match CAX.cell_at cells Pb 144 4, CAX.cell_at cells Pb 192 8, CAX.cell_at cells Pb 200 8, CAX.cell_at cells Pb 208 1, CAX.cell_at cells Pb 209 1,
        CAX.cell_at cells Pb 210 1, CAX.cell_at cells Pb 211 1, CAX.cell_at cells Pb 212 1, CAX.cell_at cells Pb 232 8,
        CAX.cell_at cells Pb 248 8, CAX.cell_at cells Pb 256 8, CAX.cell_at cells Pb 264 8 with
  | Some lvl, Some wend, Some wptr, Some st, Some sst, Some nst, Some more, Some done, Some se, Some csb, Some csend, Some cscend =>
      if (PB2.pconst_chk cells Pb && PB.str_pat cells Pb 224 pe ce se 264 67108864)%bool
      then Some (PB4.PV2 lvl wend wptr st sst nst more done se csb csend cscend) else None
  | _, _, _, _, _, _, _, _, _, _, _, _ => None
  end.

Lemma parser_view_w : forall E (M : mem) cells Pb pe ce pv P (bm bd : bool) (stack : list Z) scap (w : option (Z * Z)),
  know_ok RSEGS E M cells -> pview_w cells Pb pe ce = Some pv ->
  uv E Pb = P -> 2 ^ 32 <= P -> P + 272 <= 2 ^ 63 ->
  uv E (PB4.pv_more pv) = PML.b2z bm -> uv E (PB4.pv_done pv) = PML.b2z bd ->
  L5.bytes_at RSEGS M (uv E (PB4.pv_sb pv)) stack -> uv E (PB4.pv_send pv) = uv E (PB4.pv_sb pv) + Z.of_nat (length stack) -> uv E (PB4.pv_scend pv) = uv E (PB4.pv_sb pv) + scap -> Z.of_nat (length stack) <= scap ->
  edenot E (PB4.pv_wptr pv) = Z_to_bv 64 (fst (PSA.wincells w)) -> edenot E (PB4.pv_wend pv) = Z_to_bv 64 (snd (PSA.wincells w)) -> match w with Some (p, e) => p <= e | None => True end ->
  L5.defined M P 272 ->
  exists buf : list Z,
    PML.parser_at M P (PML.PS (uv E (PB4.pv_st pv)) (uv E (PB4.pv_sst pv)) (uv E (PB4.pv_nst pv)) bm bd (uv E (PB4.pv_level pv)) stack (uv E (PB4.pv_sb pv)) scap (uv E ce) (uv E pe) buf
                              w)
    /\ Z.of_nat (length buf) = uv E (PB4.pv_size pv) /\ 264 <= uv E ce <= 2 ^ 27 /\ uv E ce mod 8 = 0 /\ 4096 <= uv E pe <= 2 ^ 47 /\ L5.defined M (uv E pe) (uv E ce).
Proof.
  intros E M cells Pb pe ce pv P bm bd stack scap w HK HV HP P0 P1 Hm Hd Hst HS1 HS2 HS3 Hwp Hwe Hwin Hdef.
  unfold pview_w in HV.
  destruct (CAX.cell_at cells Pb 144 4) as [lvl|] eqn:C144; [|discriminate]. destruct (CAX.cell_at cells Pb 192 8) as [wend|] eqn:C192; [|discriminate].
  destruct (CAX.cell_at cells Pb 200 8) as [wptr|] eqn:C200; [|discriminate]. destruct (CAX.cell_at cells Pb 208 1) as [st|] eqn:C208; [|discriminate].
  destruct (CAX.cell_at cells Pb 209 1) as [sst|] eqn:C209; [|discriminate]. destruct (CAX.cell_at cells Pb 210 1) as [nst|] eqn:C210; [|discriminate].
  destruct (CAX.cell_at cells Pb 211 1) as [more|] eqn:C211; [|discriminate]. destruct (CAX.cell_at cells Pb 212 1) as [done|] eqn:C212; [|discriminate].
  destruct (CAX.cell_at cells Pb 232 8) as [se|] eqn:C232; [|discriminate].
  destruct (CAX.cell_at cells Pb 248 8) as [csb|] eqn:C248; [|discriminate]. destruct (CAX.cell_at cells Pb 256 8) as [csend|] eqn:C256; [|discriminate].
  destruct (CAX.cell_at cells Pb 264 8) as [cscend|] eqn:C264; [|discriminate].
  lazymatch type of HV with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection HV as <-. cbn [PB4.pv_level PB4.pv_wend PB4.pv_wptr PB4.pv_st PB4.pv_sst PB4.pv_nst PB4.pv_more PB4.pv_done PB4.pv_size PB4.pv_sb PB4.pv_send PB4.pv_scend] in *.
  apply andb_prop in Hb as [B1 B2].
  assert (ES : forall k, estart E (SA Pb k) = P + k) by (intros k; unfold estart; cbn [a_base a_off]; fold (uv E Pb); rewrite HP; reflexivity).
  destruct (PB.str_view E M cells Pb 224 pe ce se 264 67108864 HK B2 ltac:(lia) ltac:(rewrite ES; lia) ltac:(rewrite ES; lia)) as (buf & Hstr & Hlen & Hcap & Hlt & Hsm & Hc8 & Hpr & Hpdef).
  rewrite ES in Hstr.
  exists buf. split; [|repeat split; try lia; try assumption].
  unfold PB2.pconst_chk, PB2.hasw in B1.
  repeat (let X := fresh "K" in apply andb_prop in B1 as [B1 X]; apply (PB.has_ok E M _ _ HK) in X).
  apply (PB.has_ok E M _ _ HK) in B1.
  pose proof (fun k w v (H : kentry_ok RSEGS E M (KWord (SA Pb k) w v)) => H) as _.
  assert (U8 : forall k v z, kentry_ok RSEGS E M (KWord (SA Pb k) 1 v) -> uv E v = z -> PML.u8 M (P + k) z).
  { intros k v z H <-. apply (PB2.kword8_elim E M _ _ _ H). apply ES. }
  assert (U32 : forall k v z, kentry_ok RSEGS E M (KWord (SA Pb k) 4 v) -> uv E v = z -> PML.u32 M (P + k) z).
  { intros k v z H <-. apply (PB2.kword32_elim E M _ _ _ H). apply ES. }
  assert (U64 : forall k v z, kentry_ok RSEGS E M (KWord (SA Pb k) 8 v) -> uv E v = z -> PML.u64 M (P + k) z).
  { intros k v z H <-. apply (PB2.kword64_elim E M _ _ _ H). apply ES. }
  assert (LIT : forall z, 0 <= z < 2 ^ 64 -> uv E (ELit z) = z) by (intros; apply PB2.uv_lit; assumption).
  assert (SHORT : forall k, kentry_ok RSEGS E M (KWord (SA Pb k) 1 (ELit 0)) -> kentry_ok RSEGS E M (KWord (SA Pb (k + 1)) 1 (ELit 0)) -> L5.lstr_short RSEGS M (P + k) []).
  { intros k H1 H2. split; [cbn; lia|]. cbn [length]. split; [exact (U8 k _ 0 H1 (LIT 0 ltac:(lia)))|]. split; [intros i Hi; cbn in Hi; lia|].
    replace (P + k + 1 + Z.of_nat 0) with (P + (k + 1)) by lia. exact (U8 (k + 1) _ 0 H2 (LIT 0 ltac:(lia))). }
  pose proof (PB2.cell_at_ok E M _ _ _ _ _ HK C144) as D144. pose proof (PB2.cell_at_ok E M _ _ _ _ _ HK C192) as D192. pose proof (PB2.cell_at_ok E M _ _ _ _ _ HK C200) as D200.
  pose proof (PB2.cell_at_ok E M _ _ _ _ _ HK C208) as D208. pose proof (PB2.cell_at_ok E M _ _ _ _ _ HK C209) as D209. pose proof (PB2.cell_at_ok E M _ _ _ _ _ HK C210) as D210.
  pose proof (PB2.cell_at_ok E M _ _ _ _ _ HK C211) as D211. pose proof (PB2.cell_at_ok E M _ _ _ _ _ HK C212) as D212.
  pose proof (PB2.cell_at_ok E M _ _ _ _ _ HK C248) as D248. pose proof (PB2.cell_at_ok E M _ _ _ _ _ HK C256) as D256. pose proof (PB2.cell_at_ok E M _ _ _ _ _ HK C264) as D264.
  unfold PML.parser_at. cbn [PML.ps_st PML.ps_sst PML.ps_nst PML.ps_more PML.ps_done PML.ps_level PML.ps_stack PML.ps_sb PML.ps_scap PML.ps_bcap PML.ps_bptr PML.ps_buf PML.ps_win].
  split; [replace P with (P + 0) by lia; apply (U64 0 _ _ B1); apply LIT; unfold PML.VT_PARSER; lia|].
  split; [apply (U32 8 _ _ K16); apply LIT; lia|].
  split; [apply (U8 12 _ _ K15); apply LIT; lia|]. split; [apply (U8 13 _ _ K14); apply LIT; lia|]. split; [apply (U8 14 _ _ K13); apply LIT; lia|].
  split; [apply (U8 15 _ _ K12); apply LIT; lia|]. split; [apply (U8 16 _ _ K11); apply LIT; lia|]. split; [apply (U8 17 _ _ K10); apply LIT; lia|].
  split; [apply (U8 18 _ _ K9); apply LIT; lia|].
  split; [exact (SHORT 24 K8 K7)|]. split; [exact (SHORT 48 K6 K5)|]. split; [exact (SHORT 72 K4 K3)|].
  split; [apply (U64 96 _ _ K2); apply LIT; unfold PML.VT_FUNC; lia|].
  split; [apply (U64 128 _ _ K1); rewrite PB.uv_eaddz, HP; apply Z.mod_small; lia|].
  split; [exact (U32 144 _ _ D144 eq_refl)|].
  split; [assert (W200 : PML.u64 M (P + 200) (fst (PSA.wincells w))) by
            (pose proof (CL5.kword64_elim RSEGS E M _ _ (P + 200) _ D200 (ES 200) eq_refl) as X; rewrite Hwp in X; unfold PML.u64, L5.u64_at in *; rewrite Z_to_bv_bv_unsigned in X; exact X);
          assert (W192 : PML.u64 M (P + 192) (snd (PSA.wincells w))) by
            (pose proof (CL5.kword64_elim RSEGS E M _ _ (P + 192) _ D192 (ES 192) eq_refl) as X; rewrite Hwe in X; unfold PML.u64, L5.u64_at in *; rewrite Z_to_bv_bv_unsigned in X; exact X);
          destruct w as [[wp we]|]; cbn [PSA.wincells fst snd] in W200, W192; [split; [exact W200 | split; [exact W192 | exact Hwin]] | split; [exact W192 | exact W200]]|].
  split; [exact (U8 208 _ _ D208 eq_refl)|]. split; [exact (U8 209 _ _ D209 eq_refl)|]. split; [exact (U8 210 _ _ D210 eq_refl)|].
  split; [exact (U8 211 _ _ D211 Hm)|]. split; [exact (U8 212 _ _ D212 Hd)|].
  split; [apply (U8 213 _ _ K0); apply LIT; lia|]. split; [apply (U32 216 _ _ K); apply LIT; lia|].
  split; [exact Hstr|]. split; [lia|].
  split; [exact (U64 248 _ _ D248 eq_refl)|].
  split; [exact (U64 256 _ _ D256 HS1)|].
  split; [exact (U64 264 _ _ D264 HS2)|].
  split; [exact Hst|]. split; [lia | exact Hdef].
Qed.
End SPA.
