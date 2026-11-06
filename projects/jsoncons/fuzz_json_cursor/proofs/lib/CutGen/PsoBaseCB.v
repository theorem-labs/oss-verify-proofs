(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm9PlanKit Pm9L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmCurDefs.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_psome_cboth_T.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import PsKitA PsoInstCB.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation RSEGS := Pm9PlanKit.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation IC := PMLA.C_cboth.
Import PSOC.

Module GT := Cut_psome_cboth_T.
Definition IMGHI : Z := 7028736.
Definition hid (P : Prop) : Prop := P.

Section B.
Context {SCFG_P : ScfgP}.
Variable I : PSOI.inst.
Local Abbreviation L := (PSOI.iL I).     Local Abbreviation ar := (PSOI.iar I).    Local Abbreviation C := (PSOI.iC I).     Local Abbreviation HI := (PSOI.iHI I).
Local Abbreviation LBo := (PSOI.iLBo I). Local Abbreviation FF := (PSOI.iFF I).    Local Abbreviation LK := (PSOI.iLK I).   Local Abbreviation cr := (PSOI.icr I).   Local Abbreviation A := (PSOI.iA I).
Local Abbreviation sp := (PSOI.isp I).   Local Abbreviation P := (PSOI.iP I).      Local Abbreviation V := (PSOI.iV I).     Local Abbreviation E := (PSOI.iE I).     Local Abbreviation B := (PSOI.iB I).
Local Abbreviation kx := (PSOI.ikx I).   Local Abbreviation bx := (PSOI.ibx I).    Local Abbreviation g := (PSOI.ig I).     Local Abbreviation ps := (PSOI.ips I).
Local Abbreviation R := (PSOI.iR I).     Local Abbreviation M := (PSOI.iM I).      Local Abbreviation ch := (PSOI.ich I).   Local Abbreviation winb := (PSOI.iwinb I).
Local Abbreviation model := (PSOI.imodel I).
Local Abbreviation HIok := (PSOI.iHIok I). Local Abbreviation LAY := (PSOI.iLAY I). Local Abbreviation HH := (PSOI.iHH I).   Local Abbreviation Hstk := (PSOI.iHstk I).
Local Abbreviation OP := (PSOI.iOP I).     Local Abbreviation OV := (PSOI.iOV I).   Local Abbreviation OE := (PSOI.iOE I).
Local Abbreviation AP1 := (PSOI.iAP1 I).   Local Abbreviation AP2 := (PSOI.iAP2 I). Local Abbreviation AP3 := (PSOI.iAP3 I).
Local Abbreviation FOOTC := (PSOI.iFOOTC I). Local Abbreviation TPV := (PSOI.iTPV I). Local Abbreviation ERRNO_OK := (PSOI.iERRNO I). Local Abbreviation Hsp32 := (PSOI.iHsp32 I).
Local Abbreviation E0 := (PSOI.E0 I).      Local Abbreviation LB := (PSOI.LB I).     Local Abbreviation win := (PSOI.win I).
Local Abbreviation wp0 := (PSOI.wp0 I).    Local Abbreviation we0 := (PSOI.we0 I).   Local Abbreviation wlen := (PSOI.wlen I). Local Abbreviation chg := (PSOI.chg I).
Local Abbreviation bcap := (PSOI.bcap I).  Local Abbreviation k0 := (PSOI.k0 I).     Local Abbreviation bptr := (PSOI.bptr I). Local Abbreviation buf := (PSOI.buf I).   Local Abbreviation size0 := (PSOI.size0 I).
Local Abbreviation sb := (PSOI.sb I).      Local Abbreviation scap := (PSOI.scap I). Local Abbreviation stack := (PSOI.stack I). Local Abbreviation slen := (PSOI.slen I).
Local Abbreviation level := (PSOI.level I). Local Abbreviation st0 := (PSOI.st0 I).  Local Abbreviation sst0 := (PSOI.sst0 I). Local Abbreviation nst0 := (PSOI.nst0 I). Local Abbreviation done0 := (PSOI.done0 I).

Lemma INB : In (bptr, bcap) LB. Proof. unfold PSOI.LB, PSOI.bptr, PSOI.bcap, PML.ps_blocks. left. reflexivity. Qed.
Lemma INS : In (sb, scap) LB. Proof. unfold PSOI.LB, PSOI.sb, PSOI.scap, PML.ps_blocks. right. left. reflexivity. Qed.
Lemma WINF : 0 <= wp0 /\ wp0 + wlen <= 2 ^ 47 /\ 0 <= wlen <= 16384 /\ 0 <= ch /\ ch + 16384 <= 2 ^ 47 /\ 0 <= chg <= 2048 /\ wp0 + wlen = we0
  /\ (win = None \/ (In (ch, 16384) LB /\ ch <= wp0 /\ we0 <= ch + 16384 /\ chg = 2048 /\ ch mod 16 = 0)).
Proof.
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WFT.
  assert (WL : wlen = we0 - wp0) by reflexivity.
  destruct (PSOI.win I) as [[p e]|] eqn:Hw.
  - destruct (PSOI.WSOME I p e Hw) as (W0 & W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8).
    assert (INC : In (ch, 16384) LB) by (unfold PSOI.LB; apply in_or_app; right; exact W3).
    destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (ch, 16384) INC) as ((D0 & D1 & D16 & D3 & D4 & (D5 & D6 & D7)) & _). cbn [fst snd] in D0, D1, D16, D3, D4, D5, D6, D7.
    rewrite W0, W1 in *. repeat split; try (clear - W4 W5 W8 WL D0 D7; lia); try (clear - W2; lia).
    right. split; [exact INC|]. split; [clear - W4; lia|]. split; [exact W5|]. split; [exact W2 | exact D16].
  - destruct (PSOI.WNONE I Hw) as (W0 & W1 & W2 & W3 & W4). rewrite W0, W1, W2, W3, W4. repeat split; try (clear; lia). left. reflexivity.
Qed.

Ltac pose_facts :=
  pose proof (L5A.aly_segs L C LAY) as LS; pose proof (L5A.aly_img_lo L C LAY) as ILO; pose proof (L5A.aly_img_hi L C LAY) as IHI;
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WFT; pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WFT) as RFx;
  pose proof (CHA.rf_ceil _ _ _ _ RFx) as RC; destruct RC as (CL & C8); pose proof (CHA.rf_sptop _ _ _ _ RFx) as RS; destruct RS as (SP1 & SP16);
  pose proof (CHA.wf_top _ _ _ _ _ _ _ _ WFT) as STOP;
  pose proof Hstk as Hstk'; destruct Hstk' as (S1 & S2 & S3 & S4 & S5 & S6); unfold PSOC.SCR in S2, S5;
  pose proof OP as OP'; destruct OP' as (Pfr & P8 & Psh); pose proof OE as OE'; destruct OE' as (Efr & E8 & Esh); pose proof OV as OV'; destruct OV' as (Vfr & V8 & Vsh);
  pose proof (CL5A.infr_rng L ar LB FF P 272 RFx Pfr ltac:(clear; lia)) as OO; destruct OO as (O1 & O2 & O3 & O4 & O5 & O6 & O7);
  pose proof (CL5A.infr_rng L ar LB FF E 16 RFx Efr ltac:(clear; lia)) as QQ; destruct QQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7);
  pose proof (CL5A.infr_rng L ar LB FF V 48 RFx Vfr ltac:(clear; lia)) as VRR; destruct VRR as (VR1 & VR2 & VR3 & VR4 & VR5 & VR6 & VR7);
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in O1, O2, O3, O4, O5, O6, O7, Q1, Q2, Q3, Q4, Q5, Q6, Q7, VR1, VR2, VR3, VR4, VR5, VR6, VR7;
  change (hid (P + 272 <= 2147446784 \/ 17594333495296 <= P)) in O5; change (hid (P + 272 <= hl_img_lo L \/ hl_img_hi L <= P)) in O7;
  change (hid (E + 16 <= 2147446784 \/ 17594333495296 <= E)) in Q5; change (hid (E + 16 <= hl_img_lo L \/ hl_img_hi L <= E)) in Q7;
  change (hid (V + 48 <= 2147446784 \/ 17594333495296 <= V)) in VR5; change (hid (V + 48 <= hl_img_lo L \/ hl_img_hi L <= V)) in VR7;
  assert (FSLO : 7028736 <= ar_fs ar) by (destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [unfold FS_BYTES in A4; rewrite ILO in A4; clear - A0' A4; lia | rewrite IHI in A4; exact A4]);
  pose proof (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (bptr, bcap) INB) as KBB; destruct KBB as ((KB0 & KB1 & KB16 & KB3 & KB4 & (KB5 & KB6 & KB7)) & KBdef & KBsha & KBbap & KBfap);
  cbn [fst snd] in KB0, KB1, KB16, KB3, KB4, KB5, KB6, KB7, KBdef, KBsha, KBbap, KBfap;
  pose proof (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (sb, scap) INS) as KSS; destruct KSS as ((KS0 & KS1 & KS16 & KS3 & KS4 & (KS5 & KS6 & KS7)) & KSdef & KSsha & KSbap & KSfap);
  cbn [fst snd] in KS0, KS1, KS16, KS3, KS4, KS5, KS6, KS7, KSdef, KSsha, KSbap, KSfap;
  unfold BIGSHADOW_LO, BIGSHADOW_HI in KB6, KS6;
  change (hid (bptr + bcap <= 2147446784 \/ 17594333495296 <= bptr)) in KB6; change (hid (sb + scap <= 2147446784 \/ 17594333495296 <= sb)) in KS6;
  pose proof (CHA.mod8_of_16 _ KB16) as KB8; pose proof (CHA.mod8_of_16 _ KS16) as KS8;
  pose proof (PSOI.WFX I) as WFX'; destruct WFX' as (WF1 & WF2 & WF3 & WF4 & WF5 & WF6 & WF7 & WF8 & WF9);
  pose proof (PSOI.BBX I) as BBX'; destruct BBX' as (BB1 & BB2 & BB3);
  pose proof (PSOI.BCX I) as BCX'; destruct BCX' as (BC8 & BC1 & BLT & BK0 & BK1);
  pose proof WINF as WINF'; destruct WINF' as (WI0 & WI1 & WI2 & WI3 & WI4 & WI5 & WI6 & WIC).

Ltac pose_win Hw :=
  lazymatch type of Hw with _ = Some (?p, ?e) =>
    pose proof (PSOI.WSOME I p e Hw) as WS'; destruct WS' as (WP0E & WE0E & CHGE & INCo & CH1 & CH2 & WDEF & CHSH & PLE);
    assert (INC : In (ch, 16384) LB) by (unfold PSOI.LB; apply in_or_app; right; exact INCo);
    lazymatch goal with [ WFT : CHA.wf_facts _ _ _ _ _ _ _ _ |- _ ] =>
      pose proof (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (ch, 16384) INC) as KCC; destruct KCC as ((KC0 & KC1 & KC16 & KC3 & KC4 & (KC5 & KC6 & KC7)) & KCdef & KCsha & KCbap & KCfap);
      cbn [fst snd] in KC0, KC1, KC16, KC3, KC4, KC5, KC6, KC7, KCdef, KCsha, KCbap, KCfap; unfold BIGSHADOW_LO, BIGSHADOW_HI in KC6;
      change (hid (ch + 16384 <= 2147446784 \/ 17594333495296 <= ch)) in KC6; pose proof (CHA.mod8_of_16 _ KC16) as KC8
    end
  end.

Lemma UU : bv_unsigned (ev E0 2) = sp /\ bv_unsigned (ev E0 10) = P /\ bv_unsigned (ev E0 11) = V /\ bv_unsigned (ev E0 12) = E
  /\ bv_unsigned (ev E0 32) = wlen /\ bv_unsigned (ev E0 33) = B /\ bv_unsigned (ev E0 34) = ch /\ bv_unsigned (ev E0 35) = chg /\ bv_unsigned (ev E0 36) = wp0
  /\ bv_unsigned (ev E0 46) = wlen /\ bv_unsigned (ev E0 47) = 0 /\ bv_unsigned (ev E0 48) = st0 /\ bv_unsigned (ev E0 49) = sst0 /\ bv_unsigned (ev E0 50) = nst0
  /\ bv_unsigned (ev E0 51) = 1 /\ bv_unsigned (ev E0 52) = done0 /\ bv_unsigned (ev E0 53) = level /\ bv_unsigned (ev E0 54) = k0 /\ bv_unsigned (ev E0 55) = size0
  /\ bv_unsigned (ev E0 56) = bptr /\ bv_unsigned (ev E0 57) = sb /\ bv_unsigned (ev E0 58) = slen /\ bv_unsigned (ev E0 59) = scap.
Proof.
  pose_facts.
  pose proof (PSOI.VV I) as (V2 & V4 & V10 & V11 & V12 & V32 & V33 & V34 & V35 & V36 & V46 & V47 & V48 & V49 & V50 & V51 & V52 & V53 & V54 & V55 & V56 & V57 & V58 & V59).
  rewrite V2, V10, V11, V12, V32, V33, V34, V35, V36, V46, V47, V48, V49, V50, V51, V52, V53, V54, V55, V56, V57, V58, V59.
  split; [apply u64_of_Z; clear - S2 S3 SP1 CL; lia|]. split; [apply u64_of_Z; clear - O3 O6; lia|]. split; [apply u64_of_Z; clear - VR3 VR6; lia|]. split; [apply u64_of_Z; clear - Q3 Q6; lia|].
  split; [apply u64_of_Z; clear - WI2; lia|]. split; [apply u64_of_Z; clear - BB2 BB1 BB3; unfold PSOI.size0 in *; lia|]. split; [apply u64_of_Z; clear - WI3 WI4; lia|].
  split; [apply u64_of_Z; clear - WI5; lia|]. split; [apply u64_of_Z; clear - WI0 WI1 WI2; lia|]. split; [apply u64_of_Z; clear - WI2; lia|]. split; [apply u64_of_Z; clear; lia|].
  split; [apply u64_of_Z; clear - WF9; lia|]. split; [apply u64_of_Z; clear - WF1; lia|]. split; [apply u64_of_Z; clear - WF2; lia|]. split; [apply u64_of_Z; clear; lia|].
  split; [apply u64_of_Z; clear - WF8; lia|]. split; [apply u64_of_Z; clear - WF7; lia|]. split; [apply u64_of_Z; clear - BK1; lia|]. split; [apply u64_of_Z; clear - BLT BC1; unfold PSOI.size0 in *; lia|].
  split; [apply u64_of_Z; clear - KB0 KB7 KB3; lia|]. split; [apply u64_of_Z; clear - KS0 KS7 KS3; lia|]. split; [apply u64_of_Z; clear - WF3; lia|]. apply u64_of_Z; clear - WF5; lia.
Qed.
Ltac pose_U :=
  pose proof UU as UU'; destruct UU' as (U2 & U10 & U11 & U12 & U32 & U33 & U34 & U35 & U36 & U46 & U47 & U48 & U49 & U50 & U51 & U52 & U53 & U54 & U55 & U56 & U57 & U58 & U59).
Lemma uv_add_lit : forall (E1 : env) (F k : Z) (v : nat), bv_unsigned (ev E1 v) = F -> 0 <= F -> 0 <= k -> F + k < 2 ^ 64 -> CL5A.uv E1 (EAlu Instr.ALU_ADD (EVar v) (ELit k)) = F + k.
Proof.
  intros E1 F k v Hv F0 Kk FK. unfold CL5A.uv. cbn. rewrite bv_add_unsigned, Hv. rewrite L5.unsigned_lit; [|lia].
  unfold bv_wrap. apply Z.mod_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
Lemma UVPK : forall k, 0 <= k <= 272 -> CL5A.uv E0 (EAlu Instr.ALU_ADD (EVar 10) (ELit k)) = P + k.
Proof. intros k Hk. pose_facts. pose_U. apply (uv_add_lit E0 P k 10 U10); clear - Hk O3 O6; lia. Qed.
Lemma UVP : CL5A.uv E0 (EVar 10) = P. Proof. pose_U. exact U10. Qed.
Lemma UVV : CL5A.uv E0 (EVar 11) = V. Proof. pose_U. exact U11. Qed.
Lemma UVE : CL5A.uv E0 (EVar 12) = E. Proof. pose_U. exact U12. Qed.
Lemma UVCH : CL5A.uv E0 (EVar 34) = ch. Proof. pose_U. exact U34. Qed.
Lemma UVWP : CL5A.uv E0 (EVar 36) = wp0. Proof. pose_U. exact U36. Qed.
Lemma UVBP : CL5A.uv E0 (EVar 56) = bptr. Proof. pose_U. exact U56. Qed.
Lemma UVSB : CL5A.uv E0 (EVar 57) = sb. Proof. pose_U. exact U57. Qed.
Lemma UBC : bv_unsigned (edenot E0 (EMd Instr.M_MUL (ELit 2) (EVar 54))) = bcap.
Proof. pose_facts. pose_U. apply CL5.u_lin; [lin_eval; rw_atoms; clear - BK0; lia | clear - KB0 KB3 KB7; lia]. Qed.
Lemma UWL : bv_unsigned (edenot E0 (EVar 32)) = wlen. Proof. pose_U. exact U32. Qed.
Lemma UWE : bv_unsigned (edenot E0 (EAlu Instr.ALU_ADD (EVar 36) (EVar 32))) = we0.
Proof. pose_facts. pose_U. apply CL5.u_lin; [lin_eval; rw_atoms; clear - WI6; lia | clear - WI0 WI1 WI2 WI6; lia]. Qed.

Lemma SCRV : CH.hd_scr GT.HDECL = 10496. Proof. reflexivity. Qed.
Lemma STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr GT.HDECL <= sp /\ sp <= ar_sptop ar.
Proof. pose_facts. rewrite SCRV. split; [exact S1 | clear - S2 S3; lia]. Qed.
Lemma SCRP : 0 <= CH.hd_scr GT.HDECL. Proof. rewrite SCRV. lia. Qed.
Lemma NF32 : (32 <= GT.NF)%nat. Proof. unfold GT.NF, Cut_psome_cboth_T.NF. lia. Qed.
Definition WW : list L5.range := PMSA.W_parEc L IC P V E.
Definition Wo : list L5.range := [(P, 272); (E, 16)].
Lemma WINC : incl Wo WW. Proof. intros w [<-|[<-|[]]]; [left; reflexivity | right; left; reflexivity]. Qed.
Lemma WOK : forall (w : L5.range) (a : Z), In w Wo -> L5.in_rng w a ->
  0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr GT.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Proof.
  pose_facts. intros w a [<-|[<-|[]]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
  - exact (CL5A.infr_wok L ar LB FF sp _ P 272 a RFx Pfr Hin).
  - exact (CL5A.infr_wok L ar LB FF sp _ E 16 a RFx Efr Hin).
Qed.
Lemma WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs GT.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w Wo /\ L5.in_rng w a).
Proof.
  pose_U. intros rg [<-|[<-|[]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha;
    rewrite ?U10, ?U12 in Ha; rewrite u64_of_Z in Ha by (clear; lia).
  - exists (P, 272). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia].
  - exists (E, 16). split; [right; left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia].
Qed.
Lemma SHR : forall q n0 a, 0 <= q -> 0 < n0 -> q + n0 <= 2 ^ 47 -> in_shadow_of q n0 a -> 2147450880 <= a < 17594333495296.
Proof. exact CHA.shadow_range. Qed.

Lemma BLKC : forall u n a, In (u, n) LB -> u <= a < u + n -> CHA.sclientA L ar LB FF sp GT.HDECL a.
Proof.
  pose_facts. intros u n a Hun Ha.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (u, n) Hun) as ((D0 & D1 & D16 & D3 & D4 & (D5 & D6 & D7)) & _). cbn [fst snd] in D0, D1, D16, D3, D4, D5, D6, D7.
  split; [clear - Ha D0 D7; lia|]. split; [left; exists (u, n); split; [exact Hun | cbn [fst snd]; exact Ha]|].
  apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). clear - Ha D6. lia.
Qed.
Lemma BLKS : forall u n a, In (u, n) LB -> in_shadow_of u n a -> CHA.sclientA L ar LB FF sp GT.HDECL a.
Proof.
  pose_facts. intros u n a Hun Ha.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (u, n) Hun) as ((D0 & D1 & D16 & D3 & D4 & (D5 & D6 & D7)) & _). cbn [fst snd] in D0, D1, D16, D3, D4, D5, D6, D7.
  pose proof (SHR u n a ltac:(clear - D0; lia) D3 D7 Ha) as RG. split; [clear - RG; lia|].
  split; [do 6 right; exists (u, n); split; [exact Hun | exact Ha]|].
  apply (CL5A.not_stk_shadow_sh L ar LB FF u n a RFx); [clear - D0; lia | exact D3 | exact D4 | exact Ha].
Qed.

Lemma shreg_sub : forall o n q gr a, o mod 8 = 0 -> q mod 8 = 0 -> o <= q -> q + 8 * gr <= o + n -> 0 < gr -> q / 8 + SB <= a < q / 8 + SB + gr -> in_shadow_of o n a.
Proof.
  intros o n q gr a Ho Hq H1 H2 Hg Ha. pose proof (CL5A.shreg_in_shadow q gr a Hq Hg Ha) as X. destruct X as [X1 X2]. unfold in_shadow_of, S in *.
  pose proof (CL5A.div8_le o q H1). pose proof (CL5A.div8_le (q + 8 * gr - 1) (o + n - 1) ltac:(lia)). lia.
Qed.

Lemma PSH1 : forall k a, P mod 8 = 0 -> 0 <= k < 272 -> (P + k) / 8 + SB <= a < (P + k) / 8 + SB + 1 -> in_shadow_of P 272 a.
Proof.
  intros k a P8 Hk Ha. pose proof (Z_div_mod_eq_full P 8) as D. rewrite P8, Z.add_0_r in D.
  assert (Hq : (P + k) / 8 = P / 8 + k / 8) by (rewrite D at 1; replace (8 * (P / 8) + k) with (k + P / 8 * 8) by lia; rewrite Z.div_add by lia; lia).
  apply (shreg_sub P 272 (P + 8 * (k / 8)) 1 a P8); [rewrite D; replace (8 * (P / 8) + 8 * (k / 8)) with ((P / 8 + k / 8) * 8) by lia; apply Z_mod_mult
    | pose proof (Z.div_pos k 8); lia | pose proof (Z.div_le_upper_bound k 8 33); lia | lia |].
  replace ((P + 8 * (k / 8)) / 8) with (P / 8 + k / 8); [rewrite Hq in Ha; exact Ha|].
  rewrite D at 2. replace (8 * (P / 8) + 8 * (k / 8)) with ((P / 8 + k / 8) * 8) by lia. rewrite Z_div_mult by lia. reflexivity.
Qed.
Lemma CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs GT.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF sp GT.HDECL a).
Proof.
  pose_facts. pose_U. pose proof UWL as UWL'. pose proof UWE as UWE'.
  assert (UP : forall k, 0 <= k <= 272 -> bv_unsigned (edenot E0 (EAlu Instr.ALU_ADD (EVar 10) (ELit k))) = P + k) by (intros k Hk; exact (UVPK k Hk)).
  intros rg Hrg. let l := eval vm_compute in (CH.hd_crs GT.HDECL) in change (CH.hd_crs GT.HDECL) with l in Hrg. cbn [In] in Hrg.
  destruct Hrg as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg in Ha; cbv beta iota in Ha;
    rewrite ?CL5A.estart_srl3' in Ha; unfold estart, elenZ, CL5A.uv in Ha; cbn [a_base a_off] in Ha; rewrite ?UP in Ha by (clear; lia); rewrite ?UWL', ?UWE' in Ha; cbn [edenot] in Ha;
    rewrite ?U2, ?U10, ?U11, ?U12, ?U32, ?U34, ?U35, ?U36 in Ha; rewrite ?u64_of_Z in Ha by (clear; lia).
  -
    destruct WIC as [Hw|(INC & C1 & C2 & _)]; [pose proof (PSOI.WNONE I Hw) as (_ & _ & W2 & _); exfalso; clear - Ha W2; lia|].
    apply (BLKC ch 16384 a INC). clear - Ha C1 C2 WI6. lia.
  - destruct (CL5A.infr_wok L ar LB FF sp (CH.hd_scr GT.HDECL) V 48 a RFx Vfr ltac:(clear - Ha; lia)) as (G1 & G2 & G3). split; [exact G1 | split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]].
  - destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr GT.HDECL) P 272 a RFx Pfr ltac:(clear; lia) (CL5A.shreg_in_shadow P 34 a P8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia))) as (G1 & G2 & G3).
    split; [exact G1 | split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]].
  - destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr GT.HDECL) E 16 a RFx Efr ltac:(clear; lia) (CL5A.shreg_in_shadow E 2 a E8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia))) as (G1 & G2 & G3).
    split; [exact G1 | split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]].
  - destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr GT.HDECL) V 48 a RFx Vfr ltac:(clear; lia) (CL5A.shreg_in_shadow V 6 a V8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia))) as (G1 & G2 & G3).
    split; [exact G1 | split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]].
  -
    destruct WIC as [Hw|(INC & C1 & C2 & C3 & C16)]; [pose proof (PSOI.WNONE I Hw) as (_ & _ & _ & W3 & _); exfalso; clear - Ha W3; lia|].
    rewrite C3 in Ha. apply (BLKS ch 16384 a INC). replace 16384 with (8 * 2048) by (clear; lia). apply (CL5A.shreg_in_shadow ch 2048 a (CHA.mod8_of_16 _ C16) ltac:(clear; lia)). unfold SB. clear - Ha. lia.
  - destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr GT.HDECL) P 272 a RFx Pfr ltac:(clear; lia) (PSH1 209 a P8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia))) as (G1 & G2 & G3).
    split; [exact G1 | split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]].
  - destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr GT.HDECL) P 272 a RFx Pfr ltac:(clear; lia) (PSH1 210 a P8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia))) as (G1 & G2 & G3).
    split; [exact G1 | split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]].
  - destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr GT.HDECL) P 272 a RFx Pfr ltac:(clear; lia) (PSH1 211 a P8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia))) as (G1 & G2 & G3).
    split; [exact G1 | split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]].
  - destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr GT.HDECL) P 272 a RFx Pfr ltac:(clear; lia) (PSH1 212 a P8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia))) as (G1 & G2 & G3).
    split; [exact G1 | split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]].
  - destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr GT.HDECL) P 272 a RFx Pfr ltac:(clear; lia) (PSH1 213 a P8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia))) as (G1 & G2 & G3).
    split; [exact G1 | split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]].
  - destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr GT.HDECL) P 272 a RFx Pfr ltac:(clear; lia) (PSH1 220 a P8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia))) as (G1 & G2 & G3).
    split; [exact G1 | split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]].
Qed.

Lemma RFO : CHA.rng_facts L ar LBo FF.
Proof. pose_facts. apply (CHA.rng_incl L ar LB FF); [exact RFx | intros y Hy; unfold PSOI.LB; apply in_or_app; right; exact Hy | apply incl_refl]. Qed.
Lemma WOKo : forall (w : L5.range) (a : Z), In w Wo -> L5.in_rng w a ->
  0 <= a < 2 ^ 64 /\ aclientw L ar LBo FF sp (CH.hd_scr GT.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Proof.
  pose_facts. pose proof RFO as RFo. intros w a [<-|[<-|[]]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
  - exact (CL5A.infr_wok L ar LBo FF sp _ P 272 a RFo Pfr Hin).
  - exact (CL5A.infr_wok L ar LBo FF sp _ E 16 a RFo Efr Hin).
Qed.
Lemma BLKCo : forall u n a, In (u, n) LBo -> u <= a < u + n -> CHA.sclientA L ar LBo FF sp GT.HDECL a.
Proof.
  pose_facts. intros u n a Hun Ha.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (u, n) ltac:(unfold PSOI.LB; apply in_or_app; right; exact Hun)) as ((D0 & D1 & D16 & D3 & D4 & (D5 & D6 & D7)) & _). cbn [fst snd] in D0, D1, D16, D3, D4, D5, D6, D7.
  split; [clear - Ha D0 D7; lia|]. split; [left; exists (u, n); split; [exact Hun | cbn [fst snd]; exact Ha]|].
  apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). clear - Ha D6. lia.
Qed.
Lemma BLKSo : forall u n a, In (u, n) LBo -> in_shadow_of u n a -> CHA.sclientA L ar LBo FF sp GT.HDECL a.
Proof.
  pose_facts. intros u n a Hun Ha.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (u, n) ltac:(unfold PSOI.LB; apply in_or_app; right; exact Hun)) as ((D0 & D1 & D16 & D3 & D4 & (D5 & D6 & D7)) & _). cbn [fst snd] in D0, D1, D16, D3, D4, D5, D6, D7.
  pose proof (SHR u n a ltac:(clear - D0; lia) D3 D7 Ha) as RG. split; [clear - RG; lia|].
  split; [do 6 right; exists (u, n); split; [exact Hun | exact Ha]|].
  apply (CL5A.not_stk_shadow_sh L ar LB FF u n a RFx); [clear - D0; lia | exact D3 | exact D4 | exact Ha].
Qed.
Lemma CRS_OKo : forall rg : SGP.region, In rg (CH.hd_crs GT.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LBo FF sp GT.HDECL a).
Proof.
  pose_facts. pose_U. pose proof RFO as RFo. pose proof UWL as UWL'. pose proof UWE as UWE'.
  assert (UP : forall k, 0 <= k <= 272 -> bv_unsigned (edenot E0 (EAlu Instr.ALU_ADD (EVar 10) (ELit k))) = P + k) by (intros k Hk; exact (UVPK k Hk)).
  intros rg Hrg. let l := eval vm_compute in (CH.hd_crs GT.HDECL) in change (CH.hd_crs GT.HDECL) with l in Hrg. cbn [In] in Hrg.
  destruct Hrg as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg in Ha; cbv beta iota in Ha;
    rewrite ?CL5A.estart_srl3' in Ha; unfold estart, elenZ, CL5A.uv in Ha; cbn [a_base a_off] in Ha; rewrite ?UP in Ha by (clear; lia); rewrite ?UWL', ?UWE' in Ha; cbn [edenot] in Ha;
    rewrite ?U2, ?U10, ?U11, ?U12, ?U32, ?U34, ?U35, ?U36 in Ha; rewrite ?u64_of_Z in Ha by (clear; lia).
  - destruct WIC as [Hw|(INC & C1 & C2 & _)]; [pose proof (PSOI.WNONE I Hw) as (_ & _ & W2 & _); exfalso; clear - Ha W2; lia|].
    destruct (PSOI.win I) as [[p e]|] eqn:Hw; [|exfalso; pose proof (PSOI.WNONE I Hw) as (_ & _ & _ & _ & C0); pose proof (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (ch, 16384) INC) as ((D0 & _) & _); cbn [fst snd] in D0; clear - D0 C0; lia].
    pose proof (PSOI.WSOME I p e Hw) as (_ & _ & _ & INCo & _). apply (BLKCo ch 16384 a INCo). clear - Ha C1 C2 WI6. lia.
  - destruct (CL5A.infr_wok L ar LBo FF sp (CH.hd_scr GT.HDECL) V 48 a RFo Vfr ltac:(clear - Ha; lia)) as (G1 & G2 & G3). split; [exact G1 | split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]].
  - destruct (CL5A.infr_sh_wok L ar LBo FF sp (CH.hd_scr GT.HDECL) P 272 a RFo Pfr ltac:(clear; lia) (CL5A.shreg_in_shadow P 34 a P8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia))) as (G1 & G2 & G3).
    split; [exact G1 | split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]].
  - destruct (CL5A.infr_sh_wok L ar LBo FF sp (CH.hd_scr GT.HDECL) E 16 a RFo Efr ltac:(clear; lia) (CL5A.shreg_in_shadow E 2 a E8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia))) as (G1 & G2 & G3).
    split; [exact G1 | split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]].
  - destruct (CL5A.infr_sh_wok L ar LBo FF sp (CH.hd_scr GT.HDECL) V 48 a RFo Vfr ltac:(clear; lia) (CL5A.shreg_in_shadow V 6 a V8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia))) as (G1 & G2 & G3).
    split; [exact G1 | split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]].
  - destruct WIC as [Hw|(INC & C1 & C2 & C3 & C16)]; [pose proof (PSOI.WNONE I Hw) as (_ & _ & _ & W3 & _); exfalso; clear - Ha W3; lia|].
    destruct (PSOI.win I) as [[p e]|] eqn:Hw; [|exfalso; pose proof (PSOI.WNONE I Hw) as (_ & _ & _ & C0 & _); clear - C0 C3; lia].
    pose proof (PSOI.WSOME I p e Hw) as (_ & _ & _ & INCo & _).
    rewrite C3 in Ha. apply (BLKSo ch 16384 a INCo). replace 16384 with (8 * 2048) by (clear; lia). apply (CL5A.shreg_in_shadow ch 2048 a (CHA.mod8_of_16 _ C16) ltac:(clear; lia)). unfold SB. clear - Ha. lia.
  - destruct (CL5A.infr_sh_wok L ar LBo FF sp (CH.hd_scr GT.HDECL) P 272 a RFo Pfr ltac:(clear; lia) (PSH1 209 a P8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia))) as (G1 & G2 & G3).
    split; [exact G1 | split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]].
  - destruct (CL5A.infr_sh_wok L ar LBo FF sp (CH.hd_scr GT.HDECL) P 272 a RFo Pfr ltac:(clear; lia) (PSH1 210 a P8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia))) as (G1 & G2 & G3).
    split; [exact G1 | split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]].
  - destruct (CL5A.infr_sh_wok L ar LBo FF sp (CH.hd_scr GT.HDECL) P 272 a RFo Pfr ltac:(clear; lia) (PSH1 211 a P8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia))) as (G1 & G2 & G3).
    split; [exact G1 | split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]].
  - destruct (CL5A.infr_sh_wok L ar LBo FF sp (CH.hd_scr GT.HDECL) P 272 a RFo Pfr ltac:(clear; lia) (PSH1 212 a P8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia))) as (G1 & G2 & G3).
    split; [exact G1 | split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]].
  - destruct (CL5A.infr_sh_wok L ar LBo FF sp (CH.hd_scr GT.HDECL) P 272 a RFo Pfr ltac:(clear; lia) (PSH1 213 a P8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia))) as (G1 & G2 & G3).
    split; [exact G1 | split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]].
  - destruct (CL5A.infr_sh_wok L ar LBo FF sp (CH.hd_scr GT.HDECL) P 272 a RFo Pfr ltac:(clear; lia) (PSH1 220 a P8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia))) as (G1 & G2 & G3).
    split; [exact G1 | split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]].
Qed.

Lemma IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img GT.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a.
Proof.
  pose_facts. intros rg a [<-|[<-|[<-|[]]]] Ha; cbn [fst snd] in Ha; rewrite ILO, IHI; (split; [clear - Ha; lia|]); intros Hs; pose proof (L5A.aly_static_lo L C LAY a Hs); clear - Ha H; lia.
Qed.
Lemma DEF0 : L5.defined M (sp - CH.hd_scr GT.HDECL) (CH.hd_scr GT.HDECL). Proof. pose_facts. rewrite SCRV. exact S5. Qed.

Lemma LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO. Proof. rewrite (L5A.aly_img_lo L C LAY), (L5A.aly_img_hi L C LAY). unfold BIGSHADOW_LO. clear. lia. Qed.
Lemma LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L. Proof. intros a Ha. rewrite (L5A.aly_img_lo L C LAY), (L5A.aly_img_hi L C LAY). exact (L5A.aly_ro_img L C LAY a Ha). Qed.
Lemma LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true. Proof. rewrite (L5A.aly_segs L C LAY), (L5A.aly_img_hi L C LAY). exact L5A.segs_below. Qed.
Lemma LYN : wx_segs_nowrap (hl_segs L). Proof. rewrite (L5A.aly_segs L C LAY). exact L5A.wx_nowrap. Qed.
Lemma LYH : hl_img_hi L = IMGHI. Proof. exact (L5A.aly_img_hi L C LAY). Qed.
Lemma SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS.
Proof. pose_facts. split; [intros y [<-|[<-|[]]]; apply (L5A.aly_cells L C LAY); [left; reflexivity | right; left; reflexivity] | rewrite IHI; repeat constructor; cbn; clear; lia]. Qed.
Lemma GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L.
Proof. pose_facts. rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI, Cut_psome_cboth_T.GLO, Cut_psome_cboth_T.GHI. clear. lia. Qed.
Lemma AL8 : sp mod 8 = 0 /\ (sp - 10496) mod 8 = 0 /\ (sp - 672) mod 32 = 0.
Proof.
  pose proof (Z_div_mod_eq_full sp 32) as D. rewrite Hsp32, Z.add_0_r in D. split; [|split].
  - rewrite D. replace (32 * (sp / 32)) with ((4 * (sp / 32)) * 8) by lia. apply Z_mod_mult.
  - rewrite D. replace (32 * (sp / 32) - 10496) with ((4 * (sp / 32) - 1312) * 8) by lia. apply Z_mod_mult.
  - rewrite D. replace (32 * (sp / 32) - 672) with ((sp / 32 - 21) * 32) by lia. apply Z_mod_mult.
Qed.

Definition inW (a : Z) : Prop := exists w, In w WW /\ L5.in_rng w a.
Lemma FOOTCL : forall a, PMLA.in_foot IC a -> 65536 <= a < 7028736 /\ forall sp' scr', aclient L ar LB FF sp' scr' a.
Proof.
  pose_facts. intros a Hf. assert (RG : 65536 <= a < 7028736) by (destruct Hf as (iv & Hiv & Hr); cbn in Hiv; repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Hr; clear - Hr; lia|]); destruct Hiv).
  split; [exact RG|]. intros sp' scr'. right; right; left. rewrite ILO, IHI. split; [clear - RG; lia | exact (FOOTC a Hf)].
Qed.
Lemma WCL : forall a, inW a -> 0 <= a /\ a < ahl_ceil ar /\ (a < 2147446784 \/ 17594333495296 <= a) /\ (forall sp' scr', aclient L ar LB FF sp' scr' a)
                           /\ (((P <= a < P + 272 \/ E <= a < E + 16) \/ a < 7028736) \/ V + 8 <= a < V + 48).
Proof.
  pose_facts. intros a (w & Hw & Hin). unfold L5.in_rng in Hin. unfold WW, PMSA.W_parEc, PMSA.W_parE in Hw. cbn [In app] in Hw. destruct Hw as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd] in Hin.
  - split; [clear - Hin O3; lia|]. split; [clear - Hin O4; lia|]. split; [unfold hid in O5; clear - Hin O5; lia|].
    split; [intros sp' scr'; exact (aclientw_client _ _ _ _ _ _ _ (CL5A.infr_clientw L ar LB FF sp' scr' P 272 a Pfr Hin)) | left; left; left; exact Hin].
  - split; [clear - Hin Q3; lia|]. split; [clear - Hin Q4; lia|]. split; [unfold hid in Q5; clear - Hin Q5; lia|].
    split; [intros sp' scr'; exact (aclientw_client _ _ _ _ _ _ _ (CL5A.infr_clientw L ar LB FF sp' scr' E 16 a Efr Hin)) | left; left; right; exact Hin].
  - destruct (FOOTCL a) as (RG & CLa); [exists (0x690388, 0x69038a); split; [left; reflexivity | cbn [fst snd]; cbn in Hin; clear - Hin; lia]|].
    split; [clear - RG; lia|]. split; [clear - RG CL; lia|]. split; [clear - RG; lia|]. split; [exact CLa | left; right; clear - RG; lia].
  - destruct (FOOTCL a) as (RG & CLa); [exists (0x6b1de0, 0x6b2000); split; [do 5 right; left; reflexivity | cbn [fst snd]; cbn in Hin; unfold PmIcptIfaceA.ATEXIT_TAB_BYTES in Hin; clear - Hin; lia]|].
    split; [clear - RG; lia|]. split; [clear - RG CL; lia|]. split; [clear - RG; lia|]. split; [exact CLa | left; right; clear - RG; lia].
  - rewrite TPV in Hin. unfold PSOC.TP in Hin. cbn in Hin. split; [clear - Hin; lia|]. split; [clear - Hin CL; lia|]. split; [clear - Hin; lia|].
    split; [|left; right; clear - Hin; lia]. intros sp' scr'. right; right; left. rewrite ILO, IHI. split; [clear - Hin; lia | apply ERRNO_OK; unfold ERRNO; clear - Hin; lia].
  -   split; [clear - Hin VR3; lia|]. split; [clear - Hin VR4; lia|]. split; [unfold hid in VR5; clear - Hin VR5; lia|].
    split; [intros sp' scr'; exact (aclientw_client _ _ _ _ _ _ _ (CL5A.infr_clientw L ar LB FF sp' scr' V 48 a Vfr ltac:(clear - Hin; lia))) | right; clear - Hin; lia].
Qed.
Lemma INWP : forall y, P <= y < P + 272 -> inW y. Proof. intros y Hy; exists (P, 272); split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. Qed.
Lemma INWE : forall y, E <= y < E + 16 -> inW y. Proof. intros y Hy; exists (E, 16); split; [right; left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. Qed.

Lemma uv_eaddz : forall Ex e0 z, CL5A.uv Ex (APC.eaddz e0 z) = (CL5A.uv Ex e0 + z) mod 2 ^ 64.
Proof. intros. unfold CL5A.uv, APC.eaddz. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite u_lit64. unfold two64. rewrite Zplus_mod_idemp_r. reflexivity. Qed.
Lemma uv_eadd : forall Ex a b, CL5A.uv Ex (APC.eadd a b) = (CL5A.uv Ex a + CL5A.uv Ex b) mod 2 ^ 64.
Proof. intros. unfold CL5A.uv, APC.eadd. rewrite mkAlu_denot, u_add64. reflexivity. Qed.
Lemma uv_esub : forall Ex a b, CL5A.uv Ex (APC.esub a b) = (CL5A.uv Ex a - CL5A.uv Ex b) mod 2 ^ 64.
Proof. intros. unfold CL5A.uv, APC.esub. rewrite mkAlu_denot, u_sub64. reflexivity. Qed.
Lemma uv_escale : forall Ex c e0, CL5A.uv Ex (APC.escale c e0) = (c * CL5A.uv Ex e0) mod 2 ^ 64.
Proof. intros. unfold CL5A.uv, APC.escale. rewrite mkMd_denot, u_mul64. cbn [edenot]. rewrite u_lit64. unfold two64. rewrite Zmult_mod_idemp_l. reflexivity. Qed.
Lemma uv_lit : forall Ex z, 0 <= z < 2 ^ 64 -> CL5A.uv Ex (ELit z) = z.
Proof. intros Ex z Hz. unfold CL5A.uv. cbn [edenot]. apply u64_of_Z. exact Hz. Qed.
Lemma UV_escale2 : forall Ex ex, CL5A.uv Ex (APC.escale 2 ex) = (2 * CL5A.uv Ex ex) mod 2 ^ 64.
Proof. intros Ex ex. exact (uv_escale Ex 2 ex). Qed.
Lemma UV_mul2 : forall Ex ex, CL5A.uv Ex (EMd Instr.M_MUL (ELit 2) ex) = (2 * CL5A.uv Ex ex) mod 2 ^ 64.
Proof. intros Ex ex. unfold CL5A.uv. cbn [edenot]. rewrite AX2S.u_mul64. rewrite L5.unsigned_lit by (clear; lia). reflexivity. Qed.

Lemma ind_val : forall Ex x c v, bv_unsigned (edenot Ex x) = v -> 0 <= c < 2 ^ 64 ->
  bv_unsigned (edenot Ex (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB x (ELit c)) (ELit 1))) = if Z.eqb v c then 1 else 0.
Proof.
  intros Ex x c v Hv Hc. cbn [edenot]. rewrite u_sltu64. change (bv_unsigned (Z_to_bv 64 1)) with 1. rewrite u_sub64, u_lit64.
  unfold two64. rewrite (Z.mod_small c) by lia. rewrite Hv. pose proof (u64_range (edenot Ex x)) as Hr. unfold two64 in Hr. rewrite Hv in Hr.
  destruct (Z.eqb_spec v c) as [->|Hne].
  - rewrite Z.sub_diag. reflexivity.
  - destruct (Z.ltb_spec ((v - c) mod 2 ^ 64) 1) as [Hlt|Hge]; [|reflexivity]. exfalso.
    pose proof (Z.mod_pos_bound (v - c) (2 ^ 64) ltac:(lia)) as Hb. assert (Hz : (v - c) mod 2 ^ 64 = 0) by lia.
    apply Z.mod_divide in Hz; [|lia]. destruct Hz as [q Hq]. nia.
Qed.
Lemma ind_valn : forall (w : word) d v, bv_unsigned w = v -> - 2 ^ 64 < d < 0 ->
  bv_unsigned (Sem.alu64 Instr.ALU_SLTU (Sem.alu64 Instr.ALU_ADD w (Z_to_bv 64 d)) (Z_to_bv 64 1)) = if Z.eqb v (- d) then 1 else 0.
Proof.
  intros w d v Hv Hd. rewrite u_sltu64. change (bv_unsigned (Z_to_bv 64 1)) with 1. rewrite u_add64, Hv, Z_to_bv_unsigned.
  pose proof (u64_range w) as Hr. unfold two64 in Hr. rewrite Hv in Hr. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  replace (d mod 2 ^ 64) with (d + 2 ^ 64) by (symmetry; rewrite <- (Z.mod_add d 1 (2 ^ 64)) by lia; apply Z.mod_small; lia).
  destruct (Z.eqb_spec v (- d)) as [->|Hne].
  - replace (- d + (d + 2 ^ 64)) with (0 + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. reflexivity.
  - destruct (Z.ltb_spec ((v + (d + 2 ^ 64)) mod 2 ^ 64) 1) as [Hlt|Hge]; [|reflexivity]. exfalso.
    pose proof (Z.mod_pos_bound (v + (d + 2 ^ 64)) (2 ^ 64) ltac:(lia)) as Hb. assert (Hz : (v + (d + 2 ^ 64)) mod 2 ^ 64 = 0) by lia.
    apply Z.mod_divide in Hz; [|lia]. destruct Hz as [q Hq]. nia.
Qed.

Lemma KIMG : forall Ex lo hi, L5.img_clear M 65536 1400832 -> 65536 <= lo -> hi <= 1400832 -> kentry_ok (hl_segs L) Ex (CCA.vis A model M) (KImg lo hi).
Proof.
  intros Ex lo hi IR Hlo Hhi. apply AxSymRun3.kimg_intro; [clear - Hlo; lia | clear - Hlo Hhi; lia |]. intros i1 Hi1. unfold CCA.vis.
  destruct (mrestrict (ahid A model) M (Z_to_bv 64 i1)) eqn:Hv; [|reflexivity]. exfalso.
  exact (CL5A.vis_def (ahid A model) M (Z_to_bv 64 i1) ltac:(rewrite Hv; discriminate) (IR i1 ltac:(clear - Hi1 Hlo Hhi; lia))).
Qed.
Lemma IRM : L5.img_clear M 65536 1400832.
Proof. pose proof (PSOI.iHLS I) as (IR0 & _). exact IR0. Qed.

Lemma KSHO : forall o n a, CL5A.ainfr FF o n -> 0 < n -> o + n <= 2 ^ 47 -> in_shadow_of o n a -> CHA.akept L ar LBo FF sp (CH.hd_scr GT.HDECL) WW a.
Proof.
  pose_facts. intros o n a Hfr Hn Hon Ha. pose proof RFO as RFo.
  destruct (CL5A.infr_sh_wok L ar LBo FF sp (CH.hd_scr GT.HDECL) o n a RFo Hfr Hn Ha) as (G1 & G2 & _).
  destruct (CL5A.infr_rng L ar LBo FF o n RFo Hfr Hn) as (_ & _ & X3 & _). pose proof (SHR o n a X3 Hn Hon Ha) as SRa.
  split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2)|]. intros w Hw Hin. destruct (WCL a (ex_intro _ w (conj Hw Hin))) as (_ & _ & C2 & _). clear - C2 SRa. lia.
Qed.
Lemma KV : forall a, V <= a < V + 8 -> CHA.akept L ar LBo FF sp (CH.hd_scr GT.HDECL) WW a.
Proof.
  pose_facts. intros a Ha. pose proof RFO as RFo.
  destruct (CL5A.infr_wok L ar LBo FF sp (CH.hd_scr GT.HDECL) V 48 a RFo Vfr ltac:(clear - Ha; lia)) as (G1 & G2 & _). split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2)|].
  intros w Hw Hin. destruct (WCL a (ex_intro _ w (conj Hw Hin))) as (_ & _ & _ & _ & [[[Hp|He]|Himg]|Hv]);
    [pose proof AP1 as AP1'; unfold PMLA.apart in AP1'; clear - Hp Ha AP1'; lia | pose proof AP3 as AP3'; unfold PMLA.apart in AP3'; clear - He Ha AP3'; lia | clear - Himg Ha VR1 FSLO; lia | clear - Hv Ha; lia].
Qed.
Lemma KLB : forall u n a, In (u, n) LBo -> u <= a < u + n \/ in_shadow_of u n a -> CHA.akept L ar LBo FF sp (CH.hd_scr GT.HDECL) WW a.
Proof.
  pose_facts. intros u n a Hun Ha.
  assert (HunL : In (u, n) LB) by (unfold PSOI.LB; apply in_or_app; right; exact Hun).
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (u, n) HunL) as ((D0 & D1 & D16 & D3 & D4 & (D5 & D6 & D7)) & Ddef & _ & _ & Dfap). cbn [fst snd] in D0, D1, D16, D3, D4, D5, D6, D7, Ddef, Dfap.
  assert (AR : 0 <= a < 2 ^ 64) by (destruct Ha as [Ha|Ha]; [clear - Ha D0 D7; lia | pose proof (SHR u n a ltac:(clear - D0; lia) D3 D7 Ha); clear - H; lia]).
  split; [exact AR|]. split; [destruct Ha as [Ha|Ha]; [left; exists (u, n); split; [exact Hun | exact Ha] | do 6 right; exists (u, n); split; [exact Hun | exact Ha]]|].
  intros w Hw Hin. destruct (WCL a (ex_intro _ w (conj Hw Hin))) as (_ & _ & C2 & _ & C4). destruct Ha as [Ha|Ha]; [|pose proof (SHR u n a ltac:(clear - D0; lia) D3 D7 Ha); clear - C2 H; lia].
  rewrite ILO, IHI in D1. unfold WW, PMSA.W_parEc, PMSA.W_parE in Hw. cbn [In app] in Hw. unfold L5.in_rng in Hin.
  destruct Hw as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd] in Hin; [destruct Pfr as (f & Hf & F1 & F2); pose proof (Dfap f (in_or_app _ _ _ (or_introl Hf))); clear - H Hin Ha F1 F2; lia
    | destruct Efr as (f & Hf & F1 & F2); pose proof (Dfap f (in_or_app _ _ _ (or_introl Hf))); clear - H Hin Ha F1 F2; lia | cbn in Hin; clear - Hin Ha D0 D1; lia | cbn in Hin; unfold PmIcptIfaceA.ATEXIT_TAB_BYTES in Hin; clear - Hin Ha D0 D1; lia
    | rewrite TPV in Hin; unfold PSOC.TP in Hin; cbn in Hin; clear - Hin Ha D0 D1; lia
    | destruct Vfr as (f & Hf & F1 & F2); pose proof (Dfap f (in_or_app _ _ _ (or_introl Hf))); clear - H Hin Ha F1 F2; lia].
Qed.
Lemma KSTK : forall a, S (sp - 10496) <= a < S (sp - 10496) + (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - 10496)) / 8 -> CHA.akept L ar LBo FF sp (CH.hd_scr GT.HDECL) WW a.
Proof.
  pose_facts. intros a Ha. destruct (PTA.stksh_rng ar sp 10496 a ltac:(clear - S2; lia) (proj1 (proj2 AL8)) C8 (proj2 SP1) STOP ltac:(clear - CL; lia) Ha) as (G1 & G2).
  split; [exact G1|]. split; [do 4 right; left; exact G2|]. intros w Hw Hin. destruct (WCL a (ex_intro _ w (conj Hw Hin))) as (_ & _ & C2 & _).
  unfold in_shadow_of, S, SB in G2. clear - Hin G2 C2 CL. lia.
Qed.

Lemma DECW : forall a, PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC \/ PMLA.in_foot IC a -> inW a \/ L5.outside WW a.
Proof.
  pose_facts. intros a HaF.
  assert (NE : a < 7028736 /\ (a + 1 <= ERRNO \/ ERRNO + 4 <= a)).
  { unfold ERRNO. destruct HaF as [Ha|(iv & Hiv & Hr)]; [cbn [PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.C_cboth] in Ha; clear - Ha; lia|].
    cbn in Hiv. repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Hr; clear - Hr; lia|]). destruct Hiv. }
  destruct NE as (Ha & NE).
  destruct (Z_le_dec 0x690388 a) as [G1|G1]; [destruct (Z_lt_dec a 0x69038a) as [G2|G2]|].
  - left. exists (PMLA.ERRCAT_GUARD IC, 2). split; [right; right; left; reflexivity | unfold L5.in_rng; cbn; clear - G1 G2; lia].
  - destruct (Z_le_dec 0x6b1de0 a) as [G3|G3]; [destruct (Z_lt_dec a 0x6b2000) as [G4|G4]|].
    + left. exists (PMLA.ATEXIT_TAB IC, PmIcptIfaceA.ATEXIT_TAB_BYTES). split; [do 3 right; left; reflexivity | unfold L5.in_rng, PmIcptIfaceA.ATEXIT_TAB_BYTES; cbn; clear - G3 G4; lia].
    + right. intros w Hw Hin. unfold WW, PMSA.W_parEc, PMSA.W_parE in Hw. cbn [In app] in Hw. unfold L5.in_rng in Hin.
      destruct Hw as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn in Hin; [clear - Hin Ha O1 FSLO; lia | clear - Hin Ha Q1 FSLO; lia | clear - Hin G2; lia | unfold PmIcptIfaceA.ATEXIT_TAB_BYTES in Hin; clear - Hin G4; lia | rewrite TPV in Hin; unfold ERRNO, PSOC.TP in NE, Hin; cbn in Hin; clear - Hin NE; lia | clear - Hin Ha VR1 FSLO; lia].
    + right. intros w Hw Hin. unfold WW, PMSA.W_parEc, PMSA.W_parE in Hw. cbn [In app] in Hw. unfold L5.in_rng in Hin.
      destruct Hw as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn in Hin; [clear - Hin Ha O1 FSLO; lia | clear - Hin Ha Q1 FSLO; lia | clear - Hin G2; lia | unfold PmIcptIfaceA.ATEXIT_TAB_BYTES in Hin; clear - Hin G3; lia | rewrite TPV in Hin; unfold ERRNO, PSOC.TP in NE, Hin; cbn in Hin; clear - Hin NE; lia | clear - Hin Ha VR1 FSLO; lia].
  - right. intros w Hw Hin. unfold WW, PMSA.W_parEc, PMSA.W_parE in Hw. cbn [In app] in Hw. unfold L5.in_rng in Hin.
    destruct Hw as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn in Hin; [clear - Hin Ha O1 FSLO; lia | clear - Hin Ha Q1 FSLO; lia | clear - Hin G1; lia | unfold PmIcptIfaceA.ATEXIT_TAB_BYTES in Hin; clear - Hin G1; lia | rewrite TPV in Hin; unfold ERRNO, PSOC.TP in NE, Hin; cbn in Hin; clear - Hin NE; lia | clear - Hin Ha VR1 FSLO; lia].
Qed.
Lemma PTKF : forall a, PMLA.GLOC_GUARD IC <= a < PMLA.GLOC_GUARD IC + 1 \/ PMLA.GLOC_PTR IC <= a < PMLA.GLOC_PTR IC + 8 \/ PMLA.SYSCAT_GUARD IC <= a < PMLA.SYSCAT_GUARD IC + 1
                 \/ PMLA.ERRCAT_GUARD IC <= a < PMLA.ERRCAT_GUARD IC + 2 \/ PMLA.ATEXIT_TAB IC <= a < PMLA.ATEXIT_TAB IC + 544 \/ a = PMLA.NEED_LOCKS IC
                 \/ PMLA.LOCALE_LOCK IC <= a < PMLA.LOCALE_LOCK IC + 4 \/ PMLA.CONVCAT_GUARD IC <= a < PMLA.CONVCAT_GUARD IC + 2 -> PMLA.in_foot IC a.
Proof.
  intros a Ha. pose proof PMTA.C_cboth_wf as [T1 T2 T3 _ T5 T6 T7 T8 _ _ T11]. unfold PMTA.cell_in_foot, PmIcptIfaceA.ATEXIT_TAB_BYTES in *.
  destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]];
    [apply (proj2 (proj2 T5)); exact Ha | apply (proj2 (proj2 T6)); exact Ha | apply (proj2 (proj2 T7)); exact Ha | apply (proj2 (proj2 T8)); exact Ha
    | apply (proj2 (proj2 T1)); exact Ha | subst a; apply (proj2 (proj2 T2)); lia | apply (proj2 (proj2 T3)); exact Ha | apply (proj2 (proj2 T11)); exact Ha].
Qed.
Lemma IMGCL : forall a, PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC \/ PMLA.in_foot IC a -> 65536 <= a < 7028736 /\ forall sp' scr', aclient L ar LB FF sp' scr' a.
Proof.
  pose_facts. intros a [Ha|Ha]; [|exact (FOOTCL a Ha)]. cbn [PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.C_cboth] in Ha. split; [clear - Ha; lia|].
  intros sp' scr'. right; right; left. rewrite ILO, IHI. split; [clear - Ha; lia | intros Hs; pose proof (L5A.aly_static_lo L C LAY a Hs); clear - Ha H; lia].
Qed.

Lemma STCL : forall a LB' FF' sp' scr', PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC \/ PMLA.in_foot IC a -> aclient L ar LB' FF' sp' scr' a.
Proof.
  pose_facts. intros a LB' FF' sp' scr' Ha. pose proof (proj1 (IMGCL a Ha)) as RG. right; right; left. rewrite ILO, IHI. split; [clear - RG; lia|].
  destruct Ha as [Ha|Ha]; [|exact (FOOTC a Ha)]. cbn [PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.C_cboth] in Ha. intros Hs; pose proof (L5A.aly_static_lo L C LAY a Hs); clear - Ha H; lia.
Qed.

Lemma WFR : forall a F n, inW a -> ar_fs ar <= F -> fframes_apart F n FF -> 0 < n -> ~ (F <= a < F + n).
Proof.
  pose_facts. intros a F n Ha HF0 FAP Hn Hin. destruct (WCL a Ha) as (_ & _ & _ & _ & [[[Hp|He]|Himg]|Hv]).
  - destruct Pfr as (f & Hf & F1 & F2). specialize (FAP f Hf). clear - FAP Hp Hin F1 F2 Hn. lia.
  - destruct Efr as (f & Hf & F1 & F2). specialize (FAP f Hf). clear - FAP He Hin F1 F2 Hn. lia.
  - clear - Himg Hin HF0 FSLO. lia.
  - destruct Vfr as (f & Hf & F1 & F2). specialize (FAP f Hf). clear - FAP Hv Hin F1 F2 Hn. lia.
Qed.

Definition STATIC (a : Z) : Prop := PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC \/ PMLA.in_foot IC a.
Lemma STATIC_lo : forall a, STATIC a -> 0 <= a < 7028736.
Proof. intros a Ha. pose proof (proj1 (IMGCL a Ha)) as RG. clear - RG. lia. Qed.
Lemma LS_mv : forall g1 (M1 M2 : mem), (forall a, STATIC a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> g1 <> PML.LS0 ->
  PMLA.ls_ok (hl_segs L) IC g1 M1 -> PMLA.ls_ok (hl_segs L) IC g1 M2.
Proof.
  intros g1 M1 M2 AG Hg H. apply (PTA.ls_ok_ag (hl_segs L) IC M1 M2 STATIC AG g1 Hg); [| exact PTKF | exact H].
  intros a Ha. pose proof (STATIC_lo a Ha) as X. split; [clear - X; lia | exact Ha].
Qed.
Lemma EC_mv : forall code (M1 M2 : mem), (forall a, E <= a < E + 16 -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  PMLA.ec_at (hl_segs L) IC M1 E code -> PMLA.ec_at (hl_segs L) IC M2 E code.
Proof.
  intros code M1 M2 AG H. pose_facts. apply (PTA.ec_at_ag (hl_segs L) IC M1 M2 _ AG E code); [|exact H].
  split; [clear - Q3; lia|]. split; [clear - Q6; lia|]. intros y Hy. exact Hy.
Qed.

Lemma PROVE : forall (prove : list kentry -> kentry -> bool) c ps0 E' R' A1 M1 m1 M' m' ex lo hi,
  (forall cells f, prove cells f = true -> APC.fact_ok cells f = true \/ PPVA.prove3 cells f = true) ->
  CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' -> prove (SR.ps_cells ps0) (KRange ex lo hi) = true -> lo <= CL5A.uv E' ex <= hi.
Proof.
  intros prove c ps0 E' R' A1 M1 m1 M' m' ex lo hi PRV HLF HP.
  assert (HK : know_ok (hl_segs L) E' (CCA.vis A1 m' M') (SR.ps_cells ps0)) by (unfold know_ok; apply Forall_forall; intros X HX; exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX)).
  destruct (PRV _ _ HP) as [HF|HP3].
  - pose proof (APS.fact_ok_sound (hl_segs L) E' _ _ _ HK HF) as G. cbn [kentry_ok] in G. unfold CL5A.uv. exact G.
  - pose proof (PPVA.prove3_sound (hl_segs L) E' _ _ _ HK HP3) as G. cbn [kentry_ok] in G. unfold CL5A.uv. exact G.
Qed.

Definition prove_std (cells : list kentry) (f : kentry) : bool := (APC.fact_ok cells f || PPVA.prove3 cells f)%bool.
Lemma prove_std_ok : forall cells f, prove_std cells f = true -> APC.fact_ok cells f = true \/ PPVA.prove3 cells f = true.
Proof. intros cells f H. unfold prove_std in H. apply orb_prop in H. exact H. Qed.

Lemma UVR : forall Ex e0, 0 <= CL5A.uv Ex e0 < 2 ^ 64.
Proof. intros Ex e0. unfold CL5A.uv. pose proof (u64_range (edenot Ex e0)) as H. unfold two64 in H. exact H. Qed.
Lemma U64INJ : forall (Mx : mem) a v1 v2, L5.u64_at (hl_segs L) Mx a v1 -> L5.u64_at (hl_segs L) Mx a v2 -> 0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> v1 = v2.
Proof.
  intros Mx a v1 v2 H1 H2 R1 R2. unfold L5.u64_at in H1, H2. rewrite H1 in H2.
  pose proof (f_equal (fun o : option (list byte) => match o with Some l => l | None => nil end) H2) as H. cbn beta iota in H. unfold word_to_le_bytes in H.
  rewrite !u64_of_Z in H by assumption.
  pose proof (f_equal bytes_le_to_Z H) as G. rewrite !bytes_le_Z_to_le in G by lia. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in G.
  rewrite !Z.mod_small in G by lia. exact G.
Qed.

Lemma SUBR : forall x y lo hi, 0 <= x < 2 ^ 62 -> 0 <= y < 2 ^ 62 -> lo <= (x - y) mod 2 ^ 64 <= hi -> 0 <= lo -> hi < 2 ^ 62 -> lo <= x - y <= hi.
Proof.
  intros x y lo hi Hx Hy H Hlo Hhi. destruct (Z_le_dec y x) as [G|G].
  - rewrite Z.mod_small in H by lia. exact H.
  - exfalso. replace ((x - y) mod 2 ^ 64) with (x - y + 2 ^ 64) in H; [lia|]. symmetry. rewrite <- (Z.mod_add _ 1) by lia. apply Z.mod_small. lia.
Qed.
Lemma MODB : forall X, 0 <= X <= 2 ^ 28 -> 0 <= (B - X) mod 2 ^ 64 <= 67108864 -> X <= B.
Proof.
  intros X HX HM. pose proof (PSOI.BBX I) as (BB1 & BB2 & BB3).
  assert (B0 : 0 <= B) by (unfold PSOI.size0 in BB1; clear - BB1 BB3; lia).
  destruct (Z_le_dec X B) as [OK|OK]; [exact OK|]. exfalso.
  replace ((B - X) mod 2 ^ 64) with (B - X + 2 ^ 64) in HM; [clear - HM OK HX BB2 B0; lia|].
  symmetry. rewrite <- (Z.mod_add _ 1) by (clear; lia). apply Z.mod_small. clear - OK HX B0 BB2. lia.
Qed.

Lemma RD8 : forall E' A1 m' (M' : mem) k v, H_off_segments (hl_segs L) (ahid A1 m') -> bv_unsigned (ev E' 10) = P ->
  kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') (KWord (SA PE k) 1 v) -> L5.u8_at (hl_segs L) M' (P + k) (CL5A.uv E' v).
Proof.
  intros E' A1 m' M' k v Hoff W10 HK. apply (CL5A.u8_full (hl_segs L) _ Hoff).
  exact (CL5A.kword8_elim (hl_segs L) E' _ _ _ (P + k) HK ltac:(unfold estart, PE; cbn [a_base a_off edenot]; rewrite W10; reflexivity)).
Qed.
Lemma zlb_mod : forall n z, Z_to_le_bytes n z = Z_to_le_bytes n (z mod 2 ^ (8 * Z.of_nat n)).
Proof.
  induction n as [|n IH]; intros z; [reflexivity|]. cbn [Z_to_le_bytes].
  assert (P8' : 2 ^ (8 * Z.of_nat (Datatypes.S n)) = 2 ^ 8 * 2 ^ (8 * Z.of_nat n)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (Pn : 0 < 2 ^ (8 * Z.of_nat n)) by (apply Z.pow_pos_nonneg; lia).
  f_equal.
  - apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8%N) with (2 ^ 8).
    rewrite P8'. rewrite <- (Z.mod_mod_divide z (2 ^ 8 * 2 ^ (8 * Z.of_nat n)) (2 ^ 8)); [reflexivity | exists (2 ^ (8 * Z.of_nat n)); lia].
  - rewrite (IH (Z.shiftr z 8)), (IH (Z.shiftr (z mod 2 ^ (8 * Z.of_nat (Datatypes.S n))) 8)). f_equal. rewrite !Z.shiftr_div_pow2 by lia. rewrite P8'.
    set (m := 2 ^ (8 * Z.of_nat n)) in *. clearbody m.
    pose proof (Z.div_mod z (2 ^ 8 * m) ltac:(lia)) as D. pose proof (Z.mod_pos_bound z (2 ^ 8 * m) ltac:(lia)) as MB.
    set (rr := z mod (2 ^ 8 * m)) in *. set (qq := z / (2 ^ 8 * m)) in *. rewrite D.
    replace (2 ^ 8 * m * qq + rr) with (rr + (qq * m) * 2 ^ 8) by lia. rewrite Z.div_add by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma u32_mod : forall (Mx : mem) a x, L5.u32_at (hl_segs L) Mx a x -> L5.u32_at (hl_segs L) Mx a (x mod 2 ^ 32).
Proof.
  intros Mx a x H. unfold L5.u32_at in *. rewrite H. f_equal. unfold word_to_le_bytes. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64%N) with (2 ^ 32 * 2 ^ 32).
  rewrite (zlb_mod 4 (x mod _)), (zlb_mod 4 ((x mod 2 ^ 32) mod _)). change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). f_equal.
  rewrite !Z.mod_mod_divide by (exists (2 ^ 32); lia). rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma RD32 : forall E' A1 m' (M' : mem) k v, H_off_segments (hl_segs L) (ahid A1 m') -> bv_unsigned (ev E' 10) = P ->
  kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') (KWord (SA PE k) 4 v) -> L5.u32_at (hl_segs L) M' (P + k) (CL5A.uv E' v mod 2 ^ 32).
Proof.
  intros E' A1 m' M' k v Hoff W10 HK. apply u32_mod. apply (CL5A.u32_full (hl_segs L) _ Hoff).
  exact (CL5A.kword32_elim (hl_segs L) E' _ _ _ (P + k) HK ltac:(unfold estart, PE; cbn [a_base a_off edenot]; rewrite W10; reflexivity)).
Qed.
Lemma RD64 : forall E' A1 m' (M' : mem) k v, H_off_segments (hl_segs L) (ahid A1 m') -> bv_unsigned (ev E' 10) = P ->
  kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') (KWord (SA PE k) 8 v) -> L5.u64_at (hl_segs L) M' (P + k) (CL5A.uv E' v).
Proof.
  intros E' A1 m' M' k v Hoff W10 HK. apply (CL5A.u64_full (hl_segs L) _ Hoff).
  exact (CL5A.kword64_elim (hl_segs L) E' _ _ _ (P + k) HK ltac:(unfold estart, PE; cbn [a_base a_off edenot]; rewrite W10; reflexivity)).
Qed.

Lemma cell_at_has : forall cells b k w v, CAX.cell_at cells b k w = Some v -> In (KWord (SA b k) w v) cells.
Proof.
  intros cells b k w v H. unfold CAX.cell_at in H. destruct (find _ cells) as [X|] eqn:Hf; [|discriminate].
  apply find_some in Hf as [Hin Hb]. destruct X as [[b' k'] w' v'| | | | | | | | |]; try discriminate.
  apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2]. apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. apply Nat.eqb_eq in H3. injection H as <-. subst. exact Hin.
Qed.
Lemma U8DEF : forall (Mx : mem) a v, L5.u8_at (hl_segs L) Mx a v -> hl_img_hi L <= a -> 0 <= a < 2 ^ 64 -> Mx (Z_to_bv 64 a) <> None.
Proof.
  intros Mx a v Hu Ha Hr Hn. unfold L5.u8_at in Hu. cbn [rdn] in Hu. rewrite Hn in Hu. unfold seg_rom, memory_read in Hu.
  rewrite L5.unsigned_lit in Hu by exact Hr. change (Z.of_N 1) with 1 in Hu. rewrite (find_segment1_none_above (hl_segs L) (hl_img_hi L) a LYB Ha) in Hu. discriminate Hu.
Qed.
End B.

Ltac pose_facts I :=
  pose proof (L5A.aly_segs (PSOI.iL I) (PSOI.iC I) (PSOI.iLAY I)) as LS; pose proof (L5A.aly_img_lo (PSOI.iL I) (PSOI.iC I) (PSOI.iLAY I)) as ILO; pose proof (L5A.aly_img_hi (PSOI.iL I) (PSOI.iC I) (PSOI.iLAY I)) as IHI;
  pose proof (CHA.wf_of (PSOI.iL I) (PSOI.iar I) (PSOI.iC I) (PSOI.iHI I) (PSOI.iHIok I) _ _ _ _ _ _ _ (PSOI.iHH I)) as WFT; pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WFT) as RFx;
  pose proof (CHA.rf_ceil _ _ _ _ RFx) as RC; destruct RC as (CL & C8); pose proof (CHA.rf_sptop _ _ _ _ RFx) as RS; destruct RS as (SP1 & SP16);
  pose proof (CHA.wf_top _ _ _ _ _ _ _ _ WFT) as STOP;
  pose proof (PSOI.iHstk I) as Hstk'; destruct Hstk' as (S1 & S2 & S3 & S4 & S5 & S6); unfold PSOC.SCR in S2, S5;
  pose proof (PSOI.iOP I) as OP'; destruct OP' as (Pfr & P8 & Psh); pose proof (PSOI.iOE I) as OE'; destruct OE' as (Efr & E8 & Esh); pose proof (PSOI.iOV I) as OV'; destruct OV' as (Vfr & V8 & Vsh);
  pose proof (CL5A.infr_rng (PSOI.iL I) (PSOI.iar I) (PSOI.LB I) (PSOI.iFF I) (PSOI.iP I) 272 RFx Pfr ltac:(clear; lia)) as OO; destruct OO as (O1 & O2 & O3 & O4 & O5 & O6 & O7);
  pose proof (CL5A.infr_rng (PSOI.iL I) (PSOI.iar I) (PSOI.LB I) (PSOI.iFF I) (PSOI.iE I) 16 RFx Efr ltac:(clear; lia)) as QQ; destruct QQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7);
  pose proof (CL5A.infr_rng (PSOI.iL I) (PSOI.iar I) (PSOI.LB I) (PSOI.iFF I) (PSOI.iV I) 48 RFx Vfr ltac:(clear; lia)) as VRR; destruct VRR as (VR1 & VR2 & VR3 & VR4 & VR5 & VR6 & VR7);
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in O1, O2, O3, O4, O5, O6, O7, Q1, Q2, Q3, Q4, Q5, Q6, Q7, VR1, VR2, VR3, VR4, VR5, VR6, VR7;
  change (hid (PSOI.iP I + 272 <= 2147446784 \/ 17594333495296 <= PSOI.iP I)) in O5; change (hid (PSOI.iP I + 272 <= hl_img_lo (PSOI.iL I) \/ hl_img_hi (PSOI.iL I) <= PSOI.iP I)) in O7;
  change (hid (PSOI.iE I + 16 <= 2147446784 \/ 17594333495296 <= PSOI.iE I)) in Q5; change (hid (PSOI.iE I + 16 <= hl_img_lo (PSOI.iL I) \/ hl_img_hi (PSOI.iL I) <= PSOI.iE I)) in Q7;
  change (hid (PSOI.iV I + 48 <= 2147446784 \/ 17594333495296 <= PSOI.iV I)) in VR5; change (hid (PSOI.iV I + 48 <= hl_img_lo (PSOI.iL I) \/ hl_img_hi (PSOI.iL I) <= PSOI.iV I)) in VR7;
  assert (FSLO : 7028736 <= ar_fs (PSOI.iar I)) by (destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [unfold FS_BYTES in A4; rewrite ILO in A4; clear - A0' A4; lia | rewrite IHI in A4; exact A4]);
  pose proof (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (PSOI.bptr I, PSOI.bcap I) (INB I)) as KBB; destruct KBB as ((KB0 & KB1 & KB16 & KB3 & KB4 & (KB5 & KB6 & KB7)) & KBdef & KBsha & KBbap & KBfap);
  cbn [fst snd] in KB0, KB1, KB16, KB3, KB4, KB5, KB6, KB7, KBdef, KBsha, KBbap, KBfap;
  pose proof (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (PSOI.sb I, PSOI.scap I) (INS I)) as KSS; destruct KSS as ((KS0 & KS1 & KS16 & KS3 & KS4 & (KS5 & KS6 & KS7)) & KSdef & KSsha & KSbap & KSfap);
  cbn [fst snd] in KS0, KS1, KS16, KS3, KS4, KS5, KS6, KS7, KSdef, KSsha, KSbap, KSfap;
  unfold BIGSHADOW_LO, BIGSHADOW_HI in KB6, KS6;
  change (hid (PSOI.bptr I + PSOI.bcap I <= 2147446784 \/ 17594333495296 <= PSOI.bptr I)) in KB6; change (hid (PSOI.sb I + PSOI.scap I <= 2147446784 \/ 17594333495296 <= PSOI.sb I)) in KS6;
  pose proof (CHA.mod8_of_16 _ KB16) as KB8; pose proof (CHA.mod8_of_16 _ KS16) as KS8;
  pose proof (PSOI.WFX I) as WFX'; destruct WFX' as (WF1 & WF2 & WF3 & WF4 & WF5 & WF6 & WF7 & WF8 & WF9);
  pose proof (PSOI.BBX I) as BBX'; destruct BBX' as (BB1 & BB2 & BB3);
  pose proof (PSOI.BCX I) as BCX'; destruct BCX' as (BC8 & BC1 & BLT & BK0 & BK1);
  pose proof (WINF I) as WINF'; destruct WINF' as (WI0 & WI1 & WI2 & WI3 & WI4 & WI5 & WI6 & WIC).
Ltac pose_win I Hw :=
  lazymatch type of Hw with _ = Some (?p, ?e) =>
    pose proof (PSOI.WSOME I p e Hw) as WS'; destruct WS' as (WP0E & WE0E & CHGE & INCo & CH1 & CH2 & WDEF & CHSH & PLE);
    assert (INC : In (PSOI.ich I, 16384) (PSOI.LB I)) by (unfold PSOI.LB; apply in_or_app; right; exact INCo);
    lazymatch goal with [ WFT : CHA.wf_facts _ _ _ _ _ _ _ _ |- _ ] =>
      pose proof (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (PSOI.ich I, 16384) INC) as KCC; destruct KCC as ((KC0 & KC1 & KC16 & KC3 & KC4 & (KC5 & KC6 & KC7)) & KCdef & KCsha & KCbap & KCfap);
      cbn [fst snd] in KC0, KC1, KC16, KC3, KC4, KC5, KC6, KC7, KCdef, KCsha, KCbap, KCfap; unfold BIGSHADOW_LO, BIGSHADOW_HI in KC6;
      change (hid (PSOI.ich I + 16384 <= 2147446784 \/ 17594333495296 <= PSOI.ich I)) in KC6; pose proof (CHA.mod8_of_16 _ KC16) as KC8
    end
  end.

Ltac pose_U I :=
  pose proof (UU I) as UU'; destruct UU' as (U2 & U10 & U11 & U12 & U32 & U33 & U34 & U35 & U36 & U46 & U47 & U48 & U49 & U50 & U51 & U52 & U53 & U54 & U55 & U56 & U57 & U58 & U59).

Section Ex.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Lemma ex_un : forall (M : mem) a (n : nat), (n <= 8)%nat -> L5.defined M a (Z.of_nat n) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  exists v, 0 <= v < 2 ^ (8 * Z.of_nat n) /\ rdn segs M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).
Proof.
  intros M a n Hn HD H0 H1. destruct (PTA.defined_bytes segs M a n HD) as (bs & Hlen & HB).
  pose proof (L5C.bytes_at_rdn segs M bs a H0 ltac:(rewrite Hlen; exact H1) HB) as RD. rewrite Hlen in RD.
  exists (bytes_le_to_Z (map (fun z => Z_to_bv 8 z) bs)). pose proof (AX2S.bytes_le_to_Z_bound (map (fun z => Z_to_bv 8 z) bs)) as BND. rewrite length_map, Hlen in BND.
  split; [exact BND|]. rewrite RD. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [rewrite length_map; exact Hlen | exact Hn].
Qed.
Lemma ex_u32 : forall (M : mem) a, L5.defined M a 4 -> 0 <= a -> a + 4 <= 2 ^ 64 -> exists v, 0 <= v < 2 ^ 32 /\ L5.u32_at segs M a v.
Proof. intros M a HD H0 H1. destruct (ex_un M a 4 ltac:(lia) HD H0 H1) as (v & Hv & RD). exists v. split; [exact Hv | exact RD]. Qed.
Lemma ex_u64 : forall (M : mem) a, L5.defined M a 8 -> 0 <= a -> a + 8 <= 2 ^ 64 -> exists v, 0 <= v < 2 ^ 64 /\ L5.u64_at segs M a v.
Proof. intros M a HD H0 H1. destruct (ex_un M a 8 ltac:(lia) HD H0 H1) as (v & Hv & RD). exists v. split; [exact Hv | exact RD]. Qed.
Lemma ex_u8 : forall (M : mem) a, L5.defined M a 1 -> 0 <= a -> a + 1 <= 2 ^ 64 -> exists v, 0 <= v < 2 ^ 8 /\ L5.u8_at segs M a v.
Proof.
  intros M a HD H0 H1. destruct (ex_un M a 1 ltac:(lia) HD H0 H1) as (v & Hv & RD). exists v. split; [exact Hv|].
  unfold L5.u8_at. rewrite RD. rewrite (CL5A.bytes1 v) by (clear - Hv; lia). reflexivity.
Qed.

Lemma defined_bytes_r : forall (M : mem) p (n : nat), L5.defined M p (Z.of_nat n) ->
  exists bs, length bs = n /\ L5.bytes_at segs M p bs /\ Forall (fun c => 0 <= c < 256) bs.
Proof.
  intros M p n HD.
  set (f := fun i : nat => match M (Z_to_bv 64 (p + Z.of_nat i)) with Some b => bv_unsigned b | None => 0 end).
  exists (map f (seq 0 n)). split; [rewrite length_map, length_seq; reflexivity|]. split.
  - intros i Hi. rewrite length_map, length_seq in Hi.
    rewrite (nth_indep (map f (seq 0 n)) (n:=i) 0 (f 0%nat) ltac:(rewrite length_map, length_seq; exact Hi)). rewrite map_nth. rewrite (seq_nth 0%nat 0%nat Hi). cbn [Nat.add].
    unfold f. destruct (M (Z_to_bv 64 (p + Z.of_nat i))) as [b|] eqn:Hb; [|exfalso; exact (HD (Z.of_nat i) ltac:(lia) Hb)].
    unfold L5.u8_at. cbn [rdn]. rewrite Hb. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (i & <- & _). unfold f. destruct (M (Z_to_bv 64 (p + Z.of_nat i))) as [b|]; [|clear; lia].
    pose proof (bv_unsigned_in_range 8 b) as R8. change (bv_modulus 8) with 256 in R8. exact R8.
Qed.
End Ex.
