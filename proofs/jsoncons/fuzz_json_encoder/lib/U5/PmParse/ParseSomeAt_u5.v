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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSums_u5 ParseSums2_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSpecs_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PSA.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.

(* [comment removed for export] *)
Definition wincells (w : option (Z * Z)) : Z * Z := match w with None => (0, 0) | Some pe => pe end.

Lemma estart_uv : forall E b o, estart E (SA b o) = uv E b + o.
Proof. reflexivity. Qed.
Lemma elen_uv : forall E n, elenZ E n = uv E n.
Proof. reflexivity. Qed.
Lemma elen_lit : forall E z, 0 <= z < 2 ^ 64 -> elenZ E (ELit z) = z.
Proof. intros. unfold elenZ. cbn [edenot]. apply u64_of_Z. assumption. Qed.
Lemma krange_uv : forall E (M : mem) e lo hi, lo <= uv E e <= hi -> kentry_ok RSEGS E M (KRange e lo hi).
Proof. intros E M e lo hi H. exact H. Qed.

Section Sem.
Variable C : PSK.consts.
Hypothesis C_vtp : PSK.c_vt_parser C = PML.VT_PARSER.
Hypothesis C_vtf : PSK.c_vt_func C = PML.VT_FUNC.
Hypothesis C_hull : PSK.c_hull_lo C = 0x10000 /\ PSK.c_hull_hi C = 0xfe000.
Hypothesis C_scr : 0 <= PSK.c_scr C <= 2 ^ 20.
Variables (Pe Ve Ee spe sege wlene : expr) (X : PSK.pexprs).
Variables (E : env) (M : mem).
Variables (Pv Ev Vv spv segv wlenv : Z) (ps : PML.pstate) (linev posv ecv : Z).
Hypothesis UP : uv E Pe = Pv.   Hypothesis UE : uv E Ee = Ev.   Hypothesis UV : uv E Ve = Vv.   Hypothesis USP : uv E spe = spv.
Hypothesis USEG : uv E sege = segv.   Hypothesis UWL : uv E wlene = wlenv.
Hypothesis RP : 2 ^ 40 <= Pv /\ Pv + 272 <= 2 ^ 47.   Hypothesis RE : 2 ^ 40 <= Ev /\ Ev + 16 <= 2 ^ 47.   Hypothesis RV : 2 ^ 40 <= Vv /\ Vv + 8 <= 2 ^ 47.
Hypothesis RSP : 2 ^ 40 <= spv - PSK.c_scr C /\ spv <= 2 ^ 47.
Hypothesis RW : 0 <= segv /\ 0 <= wlenv <= 16384 /\ segv + wlenv <= 2 ^ 47.
Hypothesis HPA : PML.parser_at M Pv ps.
(* [comment removed for export] *)
Hypothesis L_level : uv E (PSK.x_level X) = PML.ps_level ps.
Hypothesis L_wptr : uv E (PSK.x_wptr X) = fst (wincells (PML.ps_win ps)).
Hypothesis L_wend : segv + wlenv = snd (wincells (PML.ps_win ps)).
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
Hypothesis B_win : (PML.ps_bptr ps + PML.ps_bcap ps <= segv \/ segv + wlenv <= PML.ps_bptr ps) /\ (PML.ps_sb ps + PML.ps_scap ps <= segv \/ segv + wlenv <= PML.ps_sb ps).
Hypothesis B_ceil : hl_ceil L <= spv - PSK.c_scr C /\ spv <= Pv /\ spv <= Ev /\ spv <= Vv.

Lemma pkn_sem_ok : know_ok RSEGS E M (PSK.pkn_sem C Pe Ve Ee spe sege wlene X).
Proof.
  pose proof HPA as HPA'. unfold PML.parser_at in HPA'.
  destruct HPA' as (C0 & C8 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & S24 & S48 & S72 & C96 & C128 & C144 & CW & C208 & C209 & C210 & C211 & C212 & C213 & C216 & Hstr & Hb264 & C248 & C256 & C264 & Hstk & Hsl & HdefP).
  assert (CWc : PML.u64 M (Pv + 200) (fst (wincells (PML.ps_win ps))) /\ PML.u64 M (Pv + 192) (snd (wincells (PML.ps_win ps)))).
  { destruct (PML.ps_win ps) as [[p e]|]; cbn [wincells fst snd]; [destruct CW as (A & B & _) | destruct CW as (B & A)]; split; assumption. }
  destruct CWc as [C200 C192].
  destruct RP as [RP1 RP2], RE as [RE1 RE2], RV as [RV1 RV2], RSP as [RS1 RS2], RW as (RW1 & RW2 & RW3).
  destruct N_st as (NS1 & NS2 & NS3), N_buf as [NB1 NB2], N_stk as [NK1 NK2].
  destruct B_buf as [(BB0 & BB1 & BB2 & BB3 & BB4) BBD], B_stk as [(BS0 & BS1 & BS2 & BS3 & BS4) BSD], B_win as [BW1 BW2], B_ceil as (BC1 & BC2 & BC3 & BC4), C_hull as [CH1 CH2].
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
  unfold PSK.pkn_sem. unfold know_ok. rewrite !Forall_app. split; [|split; [|split; [|split]]].
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
  apply Forall_cons; [eapply CL5.kword64_intro with (A := Pv + 192); [apply ESP | lia | lia | apply PB.edenot_of_uv; rewrite PB.uv_eadd, USEG, UWL, L_wend; apply Z.mod_small; rewrite <- L_wend; lia | exact C192]|].
  apply Forall_cons; [eapply CL5.kword64_intro with (A := Pv + 200); [apply ESP | lia | lia | apply PB.edenot_of_uv; exact L_wptr | exact C200]|].
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
  - (* [comment removed for export] *) unfold PSK.objs_h, PSK.kw.
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
  - (* [comment removed for export] *) unfold PSK.disj_h, PSK.hull, PSK.kdisj. cbn [flat_map app].
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
    apply Forall_cons; [eapply CL5.kdisj_intro; [rewrite estart_uv, USEG; reflexivity | rewrite elen_uv; exact UWL | exact EP | exact NP | lia]|].
    apply Forall_cons; [eapply CL5.kdisj_intro; [rewrite estart_uv, USEG; reflexivity | rewrite elen_uv; exact UWL | exact ES | exact NS | lia]|].
    apply Forall_cons; [eapply CL5.kdisj_intro; [exact EP | exact NP | exact ES | exact NS | exact B_apart]|].
    apply Forall_cons; [eapply CL5.kdisj_intro; [exact EP | exact NP | unfold estart; cbn [a_base a_off edenot]; rewrite (u64_of_Z 0) by lia; reflexivity | apply elen_lit; lia | rewrite CH1, CH2; lia]|].
    apply Forall_cons; [eapply CL5.kdisj_intro; [exact ES | exact NS | unfold estart; cbn [a_base a_off edenot]; rewrite (u64_of_Z 0) by lia; reflexivity | apply elen_lit; lia | rewrite CH1, CH2; lia]|].
    apply Forall_nil.
Qed.
End Sem.
End PSA.
