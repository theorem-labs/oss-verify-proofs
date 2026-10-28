(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmLibSpecsX_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSums_u5 ParseSums2_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSpecs_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5 ParseBridges3_u5 ParseBridges4_u5 ParseSomeAt_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallPure SmallKn SmallKnX. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmSmall Require Import SmallAt_u5 SmallPt_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncKit_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module SPTX.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.
Definition S2V : expr := EVar 52.      (* [comment removed for export] *)

(* [comment removed for export] *)
Section Credit.
Variable L : heap_layout.
Lemma kenc_nonneg : forall g, 0 <= hl_k_per_malloc L -> 0 <= PMX.kenc L g.
Proof.
  intros g Hk. unfold PMX.kenc. pose proof (EK.kv_s2_pos (PMES.g_rep g)). pose proof (EK.kv_st_nonneg (PMES.g_scap g)). nia.
Qed.
(* [comment removed for export] *)
End Credit.

(* [comment removed for export] *)
Lemma enc_inv_keep : forall L (M1 M2 : mem) V S2 g, hl_ceil L <= 2 ^ 64 ->
  0 <= V -> V + PMES.ENC_SIZE <= 2 ^ 64 -> 0 <= S2 -> S2 + 24 <= 2 ^ 64 ->
  (forall b, In b (PMES.g_lbv g) -> block_range L (fst b) (snd b)) ->
  (forall a, (V <= a < V + PMES.ENC_SIZE \/ S2 <= a < S2 + 24 \/ in_block (PMES.g_lbv g) a) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  PMES.enc_inv M1 V S2 g -> PMES.enc_inv M2 V S2 g.
Proof.
  intros L M1 M2 V S2 g HC HV HV2 HS HS2 HB HAG HINV.
  apply (EK.enc_inv_agree M1 M2 V S2 g HV HV2 HS HS2); [| | | | |exact HINV].
  - intros i Hi. apply HAG. left. unfold PMES.O_COLUMN, PMES.ENC_SIZE in *. lia.
  - intros i Hi. apply HAG. left. unfold PMES.O_COLON, PMES.ENC_SIZE in *. lia.
  - destruct HINV as (I1 & _). unfold PMES.enc_obj in I1.
    destruct I1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcol & _).
    intros j Hj. rewrite (HAG (V + PMES.O_COLUMN + j)) by (left; unfold PMES.O_COLUMN, PMES.ENC_SIZE in *; lia). exact (Hcol j Hj).
  - intros i Hi. apply HAG. right. left. lia.
  - intros b Hb. destruct (HB b Hb) as (B0 & B1 & B2 & B3 & B4).
    split; [lia|]. split; [lia|]. intros i Hi. apply HAG. right. right. exists b. split; [exact Hb | lia].
Qed.

Section Ptx.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Variables (mw : option (Z * Z)) (LBo LBV : list (Z * Z)) (cr : credit) (sp r P V E S2 B kx bx : Z) (g : PML.ls_state) (ps : PML.pstate).
Variables (R : bvmap 5 word) (M : mem) (model : Model).
Variables (SCRC : Z) (HDECL : CH.hdecl) (Pb Vb Eb : expr) (line0 pos0 : Z) (xv : list Z) (ebf : nat -> list (bv 8)).
Let SCR := CH.hd_scr HDECL.
Let bcap := PML.ps_bcap ps.
Let bptr := PML.ps_bptr ps.
Let sb := PML.ps_sb ps.
Let scap := PML.ps_scap ps.

(* [comment removed for export] *)
Definition instx : Prop :=
  SPT.inst L HI mw (LBo ++ LBV) cr sp r P V E B kx bx g ps R M model SCRC HDECL Pb Vb Eb line0 pos0 xv ebf /\ PMX.objs_x L sp P V E S2 /\ nth 3 xv 0 = S2.
Hypothesis INSTX : instx.
Let INST : SPT.inst L HI mw (LBo ++ LBV) cr sp r P V E B kx bx g ps R M model SCRC HDECL Pb Vb Eb line0 pos0 xv ebf := proj1 INSTX.
Local Notation kit X := (X L HI mw (LBo ++ LBV) cr sp r P V E B kx bx g ps R M model SCRC HDECL Pb Vb Eb line0 pos0 xv ebf INST) (only parsing).
Abbreviation E0 := (SPT.E0 mw B ps R line0 pos0 xv ebf).

Definition W : list L5.range := PMX.W_parx P V E S2.

Lemma OBJX : PMX.objs_x L sp P V E S2.
Proof. exact (proj1 (proj2 INSTX)). Qed.

Lemma STATWx : forall a, (0xdb5c0 <= a < 0xdb5c2 \/ 0xfd058 <= a < 0xfd058 + 544) \/ PML.LIT_LO <= a < PML.LIT_HI -> CH2.wclient L sp a.
Proof.
  pose proof (kit SPT.SPF) as (S1 & S2' & S3 & S4 & S5 & S6 & S7). destruct INST as (_ & LAY & _).
  intros a Ha. unfold PML.LIT_LO, PML.LIT_HI in Ha. split; [lia|]. right. rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY). split; [lia|].
  split; [intros X; pose proof (PmLayout.ly_static L LAY a X); lia|].
  split; [intros X; destruct (PmLayout.ly_ro_img L LAY a X ltac:(rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY); lia)) as [Q|[Q|Q]]; unfold PML.IMG_RO_HI in *; lia|].
  unfold in_errno. rewrite (PmLayout.ly_errno L LAY). lia.
Qed.
Lemma W_OKx : forall (w : L5.range) (a : Z), In w W -> L5.in_rng w a -> CH2.wclient L sp a.
Proof.
  pose proof (kit SPT.SPF) as (S1 & S2' & S3 & S4 & S5 & S6 & S7). pose proof OBJX as (OP & OV & OS & OE & _).
  destruct OP as (OP1 & OP2 & _), OV as (OV1 & OV2 & _), OS as (OS1 & OS2 & _), OE as (OE1 & OE2 & _). unfold PMES.ENC_SIZE in OV2.
  intros w a Hw Hin. unfold W, PMX.W_parx, PML.W_par, PMES.W_enc in Hw. apply in_app_or in Hw.
  destruct Hw as [[<-|[<-|[<-|[<-|[]]]]]|[<-|[<-|[<-|[<-|[]]]]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin;
    unfold PMES.O_STACK, PMES.O_DEPTH in *.
  - split; [lia | left; lia].
  - split; [lia | left; lia].
  - apply STATWx. lia.
  - apply STATWx. lia.
  - split; [lia | left; lia].
  - split; [lia | left; lia].
  - split; [lia | left; lia].
  - apply STATWx. right. lia.
Qed.
Lemma WRS_OKx : forall rg : SGP.region, In rg [(Pb, 0, ELit 272); (Eb, 0, ELit 16)] -> SGP.region_vars_lt SPT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w W /\ L5.in_rng w a).
Proof.
  intros rg Hrg. destruct (kit SPT.WRS_OK rg Hrg) as [H1 H2]. split; [exact H1|]. intros a Ha. destruct (H2 a Ha) as (w & Hw & Hin).
  exists w. split; [|exact Hin]. unfold W, PMX.W_parx. apply in_or_app. left. exact Hw.
Qed.
(* [comment removed for export] *)
Lemma CRS_OKx : forall seg wlen, (wlen = 0 \/ exists ch, In (ch, 16384) LBo /\ ch <= seg /\ seg + wlen <= ch + 16384) -> 0 <= wlen -> 0 <= seg -> seg + wlen < 2 ^ 64 ->
  nth 1 xv 0 = seg -> nth 2 xv 0 = wlen ->
  forall rg : SGP.region, In rg [(Vb, 0, ELit 8); (EVar 50, 0, EVar 51)] -> SGP.region_vars_lt SPT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> CH2.sclient L LBo sp a).
Proof.
  intros seg wlen Hch Hw0 Hs0 Hs1 X1 X2.
  assert (Hch' : wlen = 0 \/ exists ch, In (ch, 16384) (LBo ++ LBV) /\ ch <= seg /\ seg + wlen <= ch + 16384).
  { destruct Hch as [H|(ch & Hin & C1 & C2)]; [left; exact H | right; exists ch; split; [apply in_or_app; left; exact Hin | split; assumption]]. }
  intros rg Hrg. destruct (kit SPT.CRS_OK seg wlen Hch' Hw0 Hs0 Hs1 X1 X2 rg Hrg) as [H1 H2]. split; [exact H1|].
  intros a Ha. destruct (H2 a Ha) as (Q1 & Q2). split; [exact Q1|].
  destruct Hrg as [<-|[<-|[]]].
  - destruct Q2 as [Q|[Q|Q]]; [left; exact Q | right; left; exact Q |].
    (* [comment removed for export] *)
    pose proof (kit SPT.UU) as (_ & _ & _ & UV). pose proof OBJX as (_ & (OV1 & _) & _).
    unfold CH2.in_reg, estart, elenZ in Ha. cbn [a_base a_off] in Ha. fold (uv E0 Vb) in Ha. rewrite UV in Ha. cbn [edenot] in Ha. rewrite u64_of_Z in Ha by lia. left. lia.
  - unfold CH2.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    assert (E50 : ev E0 50 = Z_to_bv 64 seg) by (unfold SPT.E0; cbn [ev reg_ev]; rewrite <- X1; reflexivity).
    assert (E51 : ev E0 51 = Z_to_bv 64 wlen) by (unfold SPT.E0; cbn [ev reg_ev]; rewrite <- X2; reflexivity).
    rewrite E50, E51 in Ha. rewrite !u64_of_Z in Ha by lia. destruct Hch as [->|(ch & Hin & C1 & C2)]; [lia|].
    right. right. exists (ch, 16384). split; [exact Hin | cbn [fst snd]; lia].
Qed.

(* [comment removed for export] *)
Lemma amb_defx : forall NFx Wx BLS (GB : PMES.eghost -> list (Z * Z)) (Cr : PMES.eghost -> nat -> env -> credit -> Prop) g1 (M0c : mem) i E1 (M1 : mem) model1 a n,
  CH2V.heap_ambV L HI NFx E0 model LBo sp HDECL Wx BLS PMES.eghost GB Cr g1 M0c i E1 M1 model1 -> CH2V.okV L M LBo sp HDECL Wx M0c -> L5.defined M a n ->
  (sp <= a /\ a + n <= 2 ^ 47) \/ (exists ch, In (ch, 16384) LBo /\ ch <= a /\ a + n <= ch + 16384) -> L5.defined M1 a n.
Proof.
  intros NFx Wx BLS GB Cr g1 M0c i E1 M1 model1 a n (_ & _ & _ & (cr1 & HH1 & _) & _ & Hdf) (_ & Hdf0 & _) Hd Hc q Hq. pose proof (kit SPT.SPF) as (S1 & S2' & S3 & S4 & S5 & S6 & S7).
  destruct INST as (HIok & LAY & HH & _).
  assert (STEP : forall x, 0 <= x < 2 ^ 64 -> CH2.client0 L LBo sp x -> M (Z_to_bv 64 x) <> None -> M1 (Z_to_bv 64 x) <> None).
  { intros x Hx HC HM. apply (Hdf x Hx).
    - destruct HC as [HC1 HC2]. split; [|exact HC2]. exact (CH2V.client_LBr L LBo PMES.eghost GB g1 sp 0 x HC1).
    - exact (Hdf0 x Hx HC HM). }
  destruct Hc as [[C1 C2]|(ch & Hch & C1 & C2)].
  - apply STEP; [lia | | apply Hd; exact Hq]. split; [right; left; unfold hl_ceil; split; lia | unfold in_errno; rewrite (PmLayout.ly_errno L LAY); lia].
  - destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & _).
    destruct (Hwf (ch, 16384) ltac:(apply in_or_app; right; apply in_or_app; left; exact Hch)) as ((B0 & B1 & B2 & B3 & B4) & _). cbn [fst snd] in *.
    apply STEP; [unfold hl_ceil in B4; lia | | apply Hd; exact Hq].
    split; [left; exists (ch, 16384); split; [exact Hch | cbn [fst snd]; lia] | unfold in_errno; rewrite (PmLayout.ly_errno L LAY); rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY) in B1; lia].
Qed.

(* [comment removed for export] *)
Lemma FRZS2 : forall E', env_agree SPT.NF E0 E' -> uv E' S2V = S2.
Proof.
  intros E' Hag. pose proof OBJX as (_ & _ & (OS1 & OS2 & _) & _). pose proof (kit SPT.SPF) as (S1 & S2' & S3 & S4 & S5 & S6 & S7).
  pose proof (proj2 (proj2 INSTX)) as X3.
  exact (proj1 (SPT.FRZx mw B ps R HDECL line0 pos0 xv ebf E' 3%nat S2 Hag ltac:(unfold SPT.NF; lia) X3 ltac:(lia))).
Qed.
Lemma ES2 : ev E0 52 = Z_to_bv 64 S2.
Proof.
  pose proof OBJX as (_ & _ & (OS1 & OS2 & _) & _). pose proof (kit SPT.SPF) as (S1 & S2' & S3 & S4 & S5 & S6 & S7).
  pose proof (FRZS2 E0 (CC.env_agree_refl _ _)) as X. unfold uv, PB.uv, S2V in X. cbn [edenot] in X.
  rewrite <- (Z_to_bv_bv_unsigned 64 (ev E0 52)). rewrite X. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma GEOM :
  (sp <= P /\ P + 272 <= hl_sptop L) /\ (sp <= V /\ V + 408 <= hl_sptop L /\ V mod 8 = 0) /\ (sp <= S2 /\ S2 + 24 <= hl_sptop L /\ S2 mod 8 = 0) /\ (sp <= E /\ E + 16 <= hl_sptop L) /\
  0x7fff80000000 <= hl_sptop L <= 2 ^ 47 /\ hl_sptop L - 2 ^ 23 + SCR <= sp <= hl_sptop L /\ 0 <= SCR <= 2 ^ 20 /\ 0x7fff7f800000 <= sp /\
  (4096 <= bptr /\ 0 < bcap /\ bptr + bcap <= hl_sptop L - 2 ^ 23) /\ (4096 <= sb /\ 0 < scap /\ sb + scap <= hl_sptop L - 2 ^ 23) /\
  bcap = 2 * (bcap / 2) /\ bcap <= 2 ^ 27 /\ scap <= 1056 /\
  PML.apart P 272 V 408 /\ PML.apart P 272 S2 24 /\ PML.apart P 272 E 16 /\ PML.apart V 408 S2 24 /\ PML.apart V 408 E 16 /\ PML.apart S2 24 E 16.
Proof.
  pose proof (kit SPT.SPF) as (S1 & S2' & S3 & S4 & S5 & S6 & S7).
  pose proof (kit SPT.NUM) as (P0 & P4 & BD1 & BD2 & A1 & Hk & N1 & N2 & N3 & N4 & N5 & _).
  pose proof OBJX as ((OP1 & OP2 & OP3) & (OV1 & OV2 & OV3) & (OS1 & OS2 & OS3) & (OE1 & OE2 & OE3) & AP1 & AP2 & AP3 & AP4 & AP5 & AP6).
  unfold PMES.ENC_SIZE in *. fold bptr bcap sb scap in P0, P4, Hk, N1, N5 |- *.
  destruct P0 as (B0 & B1 & B2 & B3 & B4). destruct P4 as (C0 & C1 & C2 & C3 & C4). unfold hl_ceil in B4, C4, S6.
  split; [split; [exact OP1 | exact OP2]|]. split; [split; [exact OV1 | split; [exact OV2 | exact OV3]]|]. split; [split; [exact OS1 | split; [exact OS2 | exact OS3]]|].
  split; [split; [exact OE1 | exact OE2]|]. destruct INST as (_ & _ & _ & _ & HS1 & HS2 & _). fold SCR in HS1.
  split; [exact S4|]. split; [clear - S3 S6 S7; lia|]. split; [clear - HS1 HS2; lia|]. split; [clear - S2' S7; lia|].
  split; [clear - B0 B3 B4; lia|]. split; [clear - C0 C3 C4; lia|]. split; [clear - Hk; lia|]. split; [clear - N1; lia|]. split; [clear - N5; lia|].
  split; [exact AP1|]. split; [exact AP2|]. split; [exact AP3|]. split; [exact AP4|]. split; [exact AP5 | exact AP6].
Qed.
(* [comment removed for export] *)
Lemma UBLK : uv E0 (EVar 37) = bptr /\ uv E0 (EVar 38) = sb /\ elenZ E0 (EVar 40) = scap /\ elenZ E0 (APC.escale 2 (EVar 35)) = bcap.
Proof.
  pose proof GEOM as (_ & _ & _ & _ & G4 & _ & _ & _ & (B0 & B3 & B4) & (C0 & C3 & C4) & Hk & N1 & N5 & _).
  assert (E37 : ev E0 37 = Z_to_bv 64 bptr) by reflexivity. assert (E38 : ev E0 38 = Z_to_bv 64 sb) by reflexivity.
  assert (E40 : ev E0 40 = Z_to_bv 64 scap) by reflexivity. assert (E35 : ev E0 35 = Z_to_bv 64 (bcap / 2)) by reflexivity.
  split; [unfold uv, PB.uv; cbn [edenot]; rewrite E37; apply u64_of_Z; lia|].
  split; [unfold uv, PB.uv; cbn [edenot]; rewrite E38; apply u64_of_Z; lia|].
  split; [unfold elenZ; cbn [edenot]; rewrite E40; apply u64_of_Z; lia|].
  unfold elenZ. fold (PB.uv E0 (APC.escale 2 (EVar 35))). rewrite PB.uv_escale. unfold PB.uv. cbn [edenot]. rewrite E35.
  rewrite u64_of_Z by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma xtra_ok : forall (C : PSK.consts) wptrx stx morex, PSK.c_scr C = SCR ->
  know_ok RSEGS E0 M (SPKX.xtra C Pb Vb Eb (EVar 2) (SPT.X0w wptrx stx morex)).
Proof.
  intros C wptrx stx morex C6.
  pose proof (kit SPT.UU) as (U2' & UP & UE & UV). pose proof UBLK as (U37 & U38 & EL40 & ELK).
  pose proof GEOM as ((OP1 & OP2) & (OV1 & OV2 & OV3) & (OS1 & OS2 & OS3) & (OE1 & OE2) & G4 & G5 & G6 & G7 & (B0 & B3 & B4) & (C0 & C3 & C4) & Hk & N1 & N5 & AP1 & AP2 & AP3 & AP4 & AP5 & AP6).
  unfold PML.apart in AP1, AP2, AP3, AP4, AP5, AP6.
  assert (ESB : forall b v q, uv E0 b = v -> estart E0 (SA b q) = v + q) by (intros b v q Hb; unfold estart; cbn [a_base a_off]; fold (uv E0 b); rewrite Hb; reflexivity).
  assert (ELL : forall z, 0 <= z < 2 ^ 64 -> elenZ E0 (ELit z) = z) by (intros z Hz; unfold elenZ; cbn [edenot]; apply u64_of_Z; exact Hz).
  assert (U52 : uv E0 S2V = S2) by (exact (FRZS2 E0 (CC.env_agree_refl _ _))).
  unfold SPKX.xtra, PSK.kdisj. cbn [PSK.x_p PSK.x_k PSK.x_sb PSK.x_scap SPT.X0w]. rewrite C6. change SPKX.S2V with S2V. unfold SPKX.ENC_SIZE.
  repeat (apply Forall_cons); [.. | apply Forall_nil].
  - apply PSA.krange_uv. rewrite U52. clear - OS1 OS2 G4 G7. lia.
  - cbn [kentry_ok]. fold (PB.uv E0 S2V). fold uv. rewrite U52. split; [clear - OS1 G7; lia | exact OS3].
  - eapply CL5.kdisj_intro; [exact (ESB _ _ _ UV) | exact (ELL 408 ltac:(lia)) | exact (ESB _ _ _ U37) | exact ELK | clear - OV1 G5 G6 B4; lia].
  - eapply CL5.kdisj_intro; [exact (ESB _ _ _ UV) | exact (ELL 408 ltac:(lia)) | exact (ESB _ _ _ U38) | exact EL40 | clear - OV1 G5 G6 C4; lia].
  - eapply CL5.kdisj_intro; [exact (ESB _ _ _ U52) | exact (ELL 24 ltac:(lia)) | exact (ESB _ _ _ U37) | exact ELK | clear - OS1 G5 G6 B4; lia].
  - eapply CL5.kdisj_intro; [exact (ESB _ _ _ U52) | exact (ELL 24 ltac:(lia)) | exact (ESB _ _ _ U38) | exact EL40 | clear - OS1 G5 G6 C4; lia].
  - eapply CL5.kdisj_intro; [exact (ESB _ _ _ U2') | exact (ELL SCR ltac:(clear - G5 G6 G7 OV1 OV2 G4; lia)) | exact (ESB _ _ _ UV) | exact (ELL 408 ltac:(lia)) | clear - OV1 G6; lia].
  - eapply CL5.kdisj_intro; [exact (ESB _ _ _ U2') | exact (ELL SCR ltac:(clear - G5 G6 G7 OV1 OV2 G4; lia)) | exact (ESB _ _ _ U52) | exact (ELL 24 ltac:(lia)) | clear - OS1 G6; lia].
  - eapply CL5.kdisj_intro; [exact (ESB _ _ _ UP) | exact (ELL 272 ltac:(lia)) | exact (ESB _ _ _ UV) | exact (ELL 408 ltac:(lia)) | clear - AP1; lia].
  - eapply CL5.kdisj_intro; [exact (ESB _ _ _ UE) | exact (ELL 16 ltac:(lia)) | exact (ESB _ _ _ UV) | exact (ELL 408 ltac:(lia)) | clear - AP5; lia].
  - eapply CL5.kdisj_intro; [exact (ESB _ _ _ UP) | exact (ELL 272 ltac:(lia)) | exact (ESB _ _ _ U52) | exact (ELL 24 ltac:(lia)) | clear - AP2; lia].
  - eapply CL5.kdisj_intro; [exact (ESB _ _ _ UE) | exact (ELL 16 ltac:(lia)) | exact (ESB _ _ _ U52) | exact (ELL 24 ltac:(lia)) | clear - AP6; lia].
  - eapply CL5.kdisj_intro; [exact (ESB _ _ _ UV) | exact (ELL 408 ltac:(lia)) | exact (ESB _ _ _ U52) | exact (ELL 24 ltac:(lia)) | clear - AP4; lia].
Qed.
Lemma knx_okw : forall (C : PSK.consts) wptrx wendx stx morex,
  PSK.c_vt_parser C = PML.VT_PARSER -> PSK.c_vt_func C = PML.VT_FUNC -> PSK.c_vt_visitor C = PML.VT_VISITOR ->
  PSK.c_hull_lo C = 0x10000 /\ PSK.c_hull_hi C = 0xfe000 -> PSK.c_img_lo C = 0x10000 /\ PSK.c_img_hi C = PML.IMG_RO_HI -> PSK.c_scr C = SCR ->
  uv E0 stx = PML.ps_st ps -> uv E0 morex = PML.b2z (PML.ps_more ps) -> edenot E0 wptrx = Z_to_bv 64 (fst (PSA.wincells mw)) -> edenot E0 wendx = Z_to_bv 64 (snd (PSA.wincells mw)) ->
  know_ok RSEGS E0 M (SPKX.knx C false Pb Vb Eb (EVar 2) wendx (SPT.X0w wptrx stx morex)).
Proof.
  intros C wptrx wendx stx morex C1 C2 C3 C4 C5 C6 Lst Lmore Lwp Lwe. unfold SPKX.knx, know_ok. rewrite Forall_app. split.
  - exact (kit SPT.kn_okw C wptrx wendx stx morex C1 C2 C3 C4 C5 C6 Lst Lmore Lwp Lwe).
  - exact (xtra_ok C wptrx stx morex C6).
Qed.
Lemma knx_ok : forall (C : PSK.consts) stx morex,
  PSK.c_vt_parser C = PML.VT_PARSER -> PSK.c_vt_func C = PML.VT_FUNC -> PSK.c_vt_visitor C = PML.VT_VISITOR ->
  PSK.c_hull_lo C = 0x10000 /\ PSK.c_hull_hi C = 0xfe000 -> PSK.c_img_lo C = 0x10000 /\ PSK.c_img_hi C = PML.IMG_RO_HI -> PSK.c_scr C = SCR ->
  uv E0 stx = PML.ps_st ps -> uv E0 morex = PML.b2z (PML.ps_more ps) ->
  know_ok RSEGS E0 M (SPKX.knx C false Pb Vb Eb (EVar 2) (EVar 33) (SPT.X0 stx morex)).
Proof. intros C stx morex C1 C2 C3 C4 C5 C6 Lst Lmore. exact (knx_okw C (EVar 32) (EVar 33) stx morex C1 C2 C3 C4 C5 C6 Lst Lmore eq_refl eq_refl). Qed.
(* [comment removed for export] *)
Lemma wxtra_ok : forall seg wlen ch, In (ch, 16384) LBo -> ch <= seg -> seg + wlen <= ch + 16384 -> 0 <= wlen -> nth 1 xv 0 = seg -> nth 2 xv 0 = wlen ->
  know_ok RSEGS E0 M (SPKX.wxtra Vb (EVar 50) (EVar 51)).
Proof.
  intros seg wlen ch Hch C1 C2 Hw0 X1 X2.
  pose proof (kit SPT.UU) as (U2' & UP & UE & UV).
  pose proof GEOM as (_ & (OV1 & OV2 & OV3) & (OS1 & OS2 & OS3) & _ & G4 & G5 & G6 & G7 & _).
  destruct INST as (HIok & LAY & HH & _).
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & _).
  destruct (Hwf (ch, 16384) ltac:(apply in_or_app; right; apply in_or_app; left; exact Hch)) as ((B0 & B1 & B2 & B3 & B4) & _). cbn [fst snd] in B0, B1, B2, B3, B4. unfold hl_ceil in B4.
  assert (ESB : forall b v q, uv E0 b = v -> estart E0 (SA b q) = v + q) by (intros b v q Hb; unfold estart; cbn [a_base a_off]; fold (uv E0 b); rewrite Hb; reflexivity).
  assert (ELL : forall z, 0 <= z < 2 ^ 64 -> elenZ E0 (ELit z) = z) by (intros z Hz; unfold elenZ; cbn [edenot]; apply u64_of_Z; exact Hz).
  assert (U52 : uv E0 S2V = S2) by (exact (FRZS2 E0 (CC.env_agree_refl _ _))).
  assert (E50 : ev E0 50 = Z_to_bv 64 seg) by (unfold SPT.E0; cbn [ev reg_ev]; rewrite <- X1; reflexivity).
  assert (E51 : ev E0 51 = Z_to_bv 64 wlen) by (unfold SPT.E0; cbn [ev reg_ev]; rewrite <- X2; reflexivity).
  assert (Rg : 0 <= seg /\ seg + wlen <= hl_sptop L - 2 ^ 23) by (clear - B0 B4 C1 C2 Hw0; lia).
  assert (ES : estart E0 (SA (EVar 50) 0) = seg) by (unfold estart; cbn [a_base a_off edenot]; rewrite E50, u64_of_Z by (clear - Rg G4 Hw0; lia); lia).
  assert (EL : elenZ E0 (EVar 51) = wlen) by (unfold elenZ; cbn [edenot]; rewrite E51; apply u64_of_Z; clear - Rg G4 Hw0; lia).
  unfold SPKX.wxtra, PSK.kdisj. change SPKX.S2V with S2V. unfold SPKX.ENC_SIZE.
  repeat (apply Forall_cons); [.. | apply Forall_nil].
  - eapply CL5.kdisj_intro; [exact (ESB _ _ _ UV) | exact (ELL 408 ltac:(lia)) | exact ES | exact EL | clear - OV1 G5 G6 Rg; lia].
  - eapply CL5.kdisj_intro; [exact (ESB _ _ _ U52) | exact (ELL 24 ltac:(lia)) | exact ES | exact EL | clear - OS1 G5 G6 Rg; lia].
Qed.
(* [comment removed for export] *)
Definition xinv (M1 : mem) (g1 : PMES.eghost) : Prop := PMES.enc_inv M1 V S2 g1 /\ PML.lits_ok M1.
Definition gblocks (g1 : PMES.eghost) : Prop := forall b, In b (PMES.g_lbv g1) -> block_range L (fst b) (snd b).
Lemma gblocks_of_hi_heap : forall own LBo' g1 cr1 (M1 : mem) vm, hi_heap HI (own ++ LBo' ++ PMES.g_lbv g1) cr1 M1 vm -> gblocks g1.
Proof.
  intros own LBo' g1 cr1 M1 vm HH1 b Hb. destruct INST as (HIok & _). destruct (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (Hwf & _).
  apply (Hwf b). apply in_or_app. right. apply in_or_app. right. exact Hb.
Qed.
Lemma xinv_keep : forall (M1 M2 : mem) g1, gblocks g1 ->
  (forall a, (V <= a < V + PMES.ENC_SIZE \/ S2 <= a < S2 + 24 \/ in_block (PMES.g_lbv g1) a \/ PML.LIT_LO <= a < PML.LIT_HI) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  xinv M1 g1 -> xinv M2 g1.
Proof.
  intros M1 M2 g1 HB HAG [HINV HLIT]. pose proof GEOM as (_ & (OV1 & OV2 & OV3) & (OS1 & OS2 & OS3) & _ & G4 & G5 & G6 & G7 & _). split.
  - apply (enc_inv_keep L M1 M2 V S2 g1 ltac:(clear -G4; unfold hl_ceil; lia) ltac:(clear -OV1 G7; lia) ltac:(clear -OV2 G4; unfold PMES.ENC_SIZE; lia) ltac:(clear -OS1 G7; lia) ltac:(clear -OS2 G4; lia) HB); [|exact HINV].
    intros a Ha. apply HAG. clear -Ha. unfold PMES.ENC_SIZE in *. destruct Ha as [Ha|[Ha|Ha]]; [left; exact Ha | right; left; exact Ha | right; right; left; exact Ha].
  - apply (PML.lits_ok_agree M1 M2); [|exact HLIT]. intros a Ha. apply HAG. right. right. right. exact Ha.
Qed.
(* [comment removed for export] *)
Lemma inv_stretch : forall (F : list SGP.region) E' (M1 M' : mem) g1, SP.F_sub F [(EVar 2, - SCR, ELit SCR); (Pb, 0, ELit 272)] = true -> env_agree SPT.NF E0 E' ->
  (forall a : word, SGP.outside E' F a -> M' a = M1 a) -> gblocks g1 -> xinv M1 g1 -> xinv M' g1.
Proof.
  intros F E' M1 M' g1 HF Hag HFR HB HX.
  pose proof (kit SPT.UU) as (U2' & UP & _ & _). pose proof GEOM as ((OP1 & OP2) & (OV1 & OV2 & OV3) & (OS1 & OS2 & OS3) & _ & G4 & G5 & G6 & G7 & _ & _ & _ & _ & _ & AP1 & AP2 & _).
  unfold PML.apart in AP1, AP2.
  destruct INST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FP & _).
  pose proof (kit SPT.below_frame F E' M1 M' HF Hag HFR) as HLOW.
  apply (xinv_keep M1 M' g1 HB); [|exact HX]. intros a Ha. unfold PMES.ENC_SIZE in Ha.
  destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]].
  3:{ destruct (HB b Hb) as (B0 & B1 & B2 & B3 & B4). apply HLOW. clear -B0 B4 Hr. lia. }
  3:{ apply HLOW. clear -Ha G4 G5 G6. unfold PML.LIT_LO, PML.LIT_HI, hl_ceil in *. lia. }
  all: apply HFR; unfold SGP.outside; apply Forall_forall; intros [[rb rlo] rlen] Hin; pose proof (SP.F_sub_in _ _ _ HF Hin) as Hin0;
       rewrite L5.unsigned_lit by (clear -Ha OV1 OV2 OS1 OS2 G4 G7; lia); destruct Hin0 as [X|[X|[]]]; injection X as <- <- <-;
       [ rewrite (PB.estart_agree SPT.NF E0 E' (EVar 2) (- SCR) Hag eq_refl); unfold estart; cbn [a_base a_off]; fold (PB.uv E0 (EVar 2)); fold uv; rewrite U2';
         unfold elenZ; cbn [edenot]; rewrite u64_of_Z by (clear -G4 G5 G6 G7; lia)
       | rewrite (PB.estart_agree SPT.NF E0 E' Pb 0 Hag FP); unfold estart; cbn [a_base a_off]; fold (PB.uv E0 Pb); fold uv; rewrite UP; unfold elenZ; cbn [edenot]; rewrite u64_of_Z by (clear; lia) ].
  - clear -Ha OV1 G6. lia.
  - clear -Ha AP1. lia.
  - clear -Ha OS1 G6. lia.
  - clear -Ha AP2. lia.
Qed.
(* [comment removed for export] *)
Definition wc_ok (Wc : list L5.range) : Prop :=
  forall w, In w Wc -> (fst w + snd w <= V \/ V + PMES.ENC_SIZE <= fst w) /\ (fst w + snd w <= S2 \/ S2 + 24 <= fst w) /\
                      (sp <= fst w \/ (hl_img_lo L <= fst w /\ fst w + snd w <= hl_img_hi L /\ (fst w + snd w <= PML.LIT_LO \/ PML.LIT_HI <= fst w))).
(* [comment removed for export] *)
Lemma inv_frame_but : forall (M1 M2 : mem) g1 spc scr (Wc : list L5.range),
  L5.frame_but ((spc - scr, scr) :: Wc) M1 M2 -> spc <= sp -> hl_ceil L + scr <= spc -> wc_ok Wc -> gblocks g1 -> xinv M1 g1 -> xinv M2 g1.
Proof.
  intros M1 M2 g1 spc scr Wc HFB Hspc Hscr HW HB HX.
  pose proof GEOM as ((OP1 & OP2) & (OV1 & OV2 & OV3) & (OS1 & OS2 & OS3) & _ & G4 & G5 & G6 & G7 & _). destruct INST as (_ & LAY & _).
  pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
  apply (xinv_keep M1 M2 g1 HB); [|exact HX]. intros a Ha. unfold PMES.ENC_SIZE in Ha.
  assert (Ra : 0 <= a < 2 ^ 64).
  { destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]]; [clear -Ha OV1 OV2 G4 G7; lia | clear -Ha OS1 OS2 G4 G7; lia | | clear -Ha; unfold PML.LIT_LO, PML.LIT_HI in Ha; lia].
    destruct (HB b Hb) as (B0 & B1 & B2 & B3 & B4). clear -Hr B0 B4 G4. unfold hl_ceil in B4. lia. }
  apply HFB. intros w Hw. rewrite (L5.unsigned_lit a) by exact Ra. destruct Hw as [<-|Hw].
  - unfold L5.in_rng. cbn [fst snd]. destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]]; [clear -Ha OV1 Hspc; lia | clear -Ha OS1 Hspc; lia | | clear -Ha Hscr G4; unfold PML.LIT_LO, PML.LIT_HI, hl_ceil in *; lia].
    destruct (HB b Hb) as (B0 & B1 & B2 & B3 & B4). clear -Hr B4 Hscr. lia.
  - destruct (HW w Hw) as (W1 & W2 & W3). unfold L5.in_rng. unfold PMES.ENC_SIZE in W1.
    destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]]; [clear -Ha W1; lia | clear -Ha W2; lia | | clear -Ha W3 G4 G5 G6 OV1 ILO IHI; unfold PML.LIT_LO, PML.LIT_HI, hl_ceil in *; lia].
    destruct (HB b Hb) as (B0 & B1 & B2 & B3 & B4). clear -Hr B0 B1 B3 B4 W3 G5 G6. unfold hl_ceil in *. lia.
Qed.
(* [comment removed for export] *)
Definition wc_ok2 (Wc : list L5.range) : Prop :=
  forall w, In w Wc -> (fst w + snd w <= V \/ V + PMES.ENC_SIZE <= fst w) /\ (fst w + snd w <= S2 \/ S2 + 24 <= fst w) /\
                      (hl_ceil L <= fst w \/ (hl_img_lo L <= fst w /\ fst w + snd w <= hl_img_hi L /\ (fst w + snd w <= PML.LIT_LO \/ PML.LIT_HI <= fst w))).
Lemma wc_ok_2 : forall Wc, wc_ok Wc -> wc_ok2 Wc.
Proof.
  intros Wc HW w Hw. destruct (HW w Hw) as (W1 & W2 & W3). pose proof GEOM as (_ & _ & _ & _ & G4 & G5 & G6 & _).
  split; [exact W1|]. split; [exact W2|]. destruct W3 as [W3|W3]; [left; clear -W3 G5 G6; unfold hl_ceil; lia | right; exact W3].
Qed.
Lemma inv_frame_but2 : forall (M1 M2 : mem) g1 spc scr (Wc : list L5.range),
  L5.frame_but ((spc - scr, scr) :: Wc) M1 M2 -> spc <= sp -> hl_ceil L + scr <= spc -> wc_ok2 Wc -> gblocks g1 -> xinv M1 g1 -> xinv M2 g1.
Proof.
  intros M1 M2 g1 spc scr Wc HFB Hspc Hscr HW HB HX.
  pose proof GEOM as ((OP1 & OP2) & (OV1 & OV2 & OV3) & (OS1 & OS2 & OS3) & _ & G4 & G5 & G6 & G7 & _). destruct INST as (_ & LAY & _).
  pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
  apply (xinv_keep M1 M2 g1 HB); [|exact HX]. intros a Ha. unfold PMES.ENC_SIZE in Ha.
  assert (Ra : 0 <= a < 2 ^ 64).
  { destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]]; [clear -Ha OV1 OV2 G4 G7; lia | clear -Ha OS1 OS2 G4 G7; lia | | clear -Ha; unfold PML.LIT_LO, PML.LIT_HI in Ha; lia].
    destruct (HB b Hb) as (B0 & B1 & B2 & B3 & B4). clear -Hr B0 B4 G4. unfold hl_ceil in B4. lia. }
  apply HFB. intros w Hw. rewrite (L5.unsigned_lit a) by exact Ra. destruct Hw as [<-|Hw].
  - unfold L5.in_rng. cbn [fst snd]. destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]]; [clear -Ha OV1 Hspc; lia | clear -Ha OS1 Hspc; lia | | clear -Ha Hscr G4; unfold PML.LIT_LO, PML.LIT_HI, hl_ceil in *; lia].
    destruct (HB b Hb) as (B0 & B1 & B2 & B3 & B4). clear -Hr B4 Hscr. lia.
  - destruct (HW w Hw) as (W1 & W2 & W3). unfold L5.in_rng. unfold PMES.ENC_SIZE in W1.
    destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]]; [clear -Ha W1; lia | clear -Ha W2; lia | | clear -Ha W3 G4 ILO IHI; unfold PML.LIT_LO, PML.LIT_HI, hl_ceil in *; lia].
    destruct (HB b Hb) as (B0 & B1 & B2 & B3 & B4). clear -Hr B1 B4 W3 ILO IHI. unfold hl_ceil in *. lia.
Qed.
(* [comment removed for export] *)
Lemma inv_hpres : forall (M1 M2 : mem) g1 LBc spc scr (Wc : list L5.range),
  L5C.hpres L LBc spc scr Wc M1 M2 -> incl (PMES.g_lbv g1) LBc -> spc <= sp -> hl_ceil L + scr <= spc -> wc_ok Wc -> gblocks g1 -> xinv M1 g1 -> xinv M2 g1.
Proof.
  intros M1 M2 g1 LBc spc scr Wc (HK & _ & _) Hincl Hspc Hscr HW HB HX.
  pose proof GEOM as ((OP1 & OP2) & (OV1 & OV2 & OV3) & (OS1 & OS2 & OS3) & _ & G4 & G5 & G6 & G7 & _). destruct INST as (_ & LAY & _).
  pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_errno L LAY) as LER.
  apply (xinv_keep M1 M2 g1 HB); [|exact HX]. intros a Ha. unfold PMES.ENC_SIZE in Ha. apply HK.
  assert (Ra : 0 <= a < 2 ^ 64).
  { destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]]; [clear -Ha OV1 OV2 G4 G7; lia | clear -Ha OS1 OS2 G4 G7; lia | | clear -Ha; unfold PML.LIT_LO, PML.LIT_HI in Ha; lia].
    destruct (HB b Hb) as (B0 & B1 & B2 & B3 & B4). clear -Hr B0 B4 G4. unfold hl_ceil in B4. lia. }
  split; [exact Ra|]. split; [|split].
  - destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]].
    + right. left. clear -Ha OV1 Hspc G5 G6 Ra. unfold hl_ceil in *. lia.
    + right. left. clear -Ha OS1 Hspc G5 G6 Ra. unfold hl_ceil in *. lia.
    + left. exists b. split; [exact (Hincl b Hb) | exact Hr].
    + right. right. rewrite ILO, IHI. split; [clear -Ha; unfold PML.LIT_LO, PML.LIT_HI in Ha; lia|]. intros X. pose proof (PmLayout.ly_static L LAY a X). clear -Ha H. unfold PML.LIT_LO, PML.LIT_HI in Ha. lia.
  - unfold in_errno. rewrite LER. destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]]; [clear -Ha OV1 G7; lia | clear -Ha OS1 G7; lia | | clear -Ha; unfold PML.LIT_LO, PML.LIT_HI in Ha; lia].
    destruct (HB b Hb) as (B0 & B1 & B2 & B3 & B4). rewrite ILO, IHI in B1. clear -Hr B1 B3. lia.
  - intros w Hw. destruct (HW w Hw) as (W1 & W2 & W3). unfold L5.in_rng. unfold PMES.ENC_SIZE in W1.
    destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]]; [clear -Ha W1; lia | clear -Ha W2; lia | | clear -Ha W3 G4 G5 G6 OV1 ILO IHI; unfold PML.LIT_LO, PML.LIT_HI, hl_ceil in *; lia].
    destruct (HB b Hb) as (B0 & B1 & B2 & B3 & B4). clear -Hr B0 B1 B3 B4 W3 G5 G6. unfold hl_ceil in *. lia.
Qed.
(* [comment removed for export] *)
Lemma okV_defc : forall M0c, CH2V.okV L M LBo sp HDECL W M0c -> L5.defined M0c (sp - SCRC) SCRC.
Proof.
  intros M0c (O1 & O2 & O3). pose proof (kit SPT.SPF) as (S1 & S2' & S3 & S4 & S5 & S6 & S7). destruct INST as (_ & LAY & _). fold SCR in S7.
  intros q Hq. apply (O2 (sp - SCRC + q)); [clear -Hq S2' S3 S4; lia | | apply S5; exact Hq].
  split; [right; left; clear -Hq S6 S3 S4; unfold hl_ceil in *; lia | unfold in_errno; rewrite (PmLayout.ly_errno L LAY); clear -Hq S2'; lia].
Qed.
Lemma okV_hpres : forall g1 M0c M1, CH2V.okV L M LBo sp HDECL W M0c ->
  L5C.hpres L (CH2V.LBr LBo PMES.eghost PMES.g_lbv g1) sp SCRC W M0c M1 -> L5C.hpres L LBo sp SCRC W M M1.
Proof.
  intros g1 M0c M1 (O1 & O2 & O3) (H1 & H2 & H3). pose proof (kit SPT.SPF) as (_ & _ & _ & _ & _ & _ & S7). fold SCR in S7.
  apply L5C.hpres_intro.
  - intros a (K1 & K2 & K3 & K4). rewrite (H1 a).
    + apply O1. split; [exact K1|]. split; [|split; [exact K3 | exact K4]].
      destruct K2 as [X|[[X1 X2]|X]]; [left; exact X | right; left; split; [exact X1 | clear -X2 S7; lia] | right; right; exact X].
    + split; [exact K1|]. split; [exact (CH2V.client_LBr L LBo PMES.eghost PMES.g_lbv g1 sp SCRC a K2) | split; [exact K3 | exact K4]].
  - exact H2.
  - intros a Ha Hc He Hd. apply (H3 a Ha (CH2V.client_LBr L LBo PMES.eghost PMES.g_lbv g1 sp SCRC a Hc) He). apply (O2 a Ha); [|exact Hd].
    split; [|exact He]. destruct Hc as [X|[[X1 X2]|X]]; [left; exact X | right; left; split; [exact X1 | clear; lia] | right; right; exact X].
Qed.
End Ptx.
End SPTX.
