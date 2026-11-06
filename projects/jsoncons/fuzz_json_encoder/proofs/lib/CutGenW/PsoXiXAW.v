(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm4PlanKit Pm4L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm4CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmLibSpecs PmEncSpecs PmLibSpecsXA PmLibSpecsX PmLibSpecsW PmRef PmRefFacts PmRefXA PmLibSpecsXAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_psome_xasan_T Cut_psome_xasan_D Cut_psome_xasan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import PsoInstXA PsoSemXA PsoKnXA ParseSomeChkXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGenW Require Import RelObsXA PsoWTabXA PsoBaseXAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmAsanKit Require Import PtKitA PtKitB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmRefAllow PmRefNonneg.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGenW Require Import PsoInstXAW.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module G := PSO.G.
Module GT := PSO.GT.
Import PSOC.
Abbreviation RSEGS := Pm4PlanKit.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation IC := PMLA.C_xasan.

Module PSOX.
Section X.
Context {SCFG_P : ScfgP}.
Variable I : PSOIW.inst.
Local Abbreviation L := (PSOIW.iL I).     Local Abbreviation ar := (PSOIW.iar I).    Local Abbreviation C := (PSOIW.iC I).     Local Abbreviation HI := (PSOIW.iHI I).
Local Abbreviation LBo := (PSOIW.iLBo I). Local Abbreviation FF := (PSOIW.iFF I).    Local Abbreviation LK := (PSOIW.iLK I).   Local Abbreviation cr := (PSOIW.icr I).
Local Abbreviation sp := (PSOIW.isp I).   Local Abbreviation P := (PSOIW.iP I).      Local Abbreviation V := (PSOIW.iV I).     Local Abbreviation E := (PSOIW.iE I).     Local Abbreviation B := (PSOIW.iB I).
Local Abbreviation kx := (PSOIW.ikx I).   Local Abbreviation bx := (PSOIW.ibx I).    Local Abbreviation g := (PSOIW.ig I).     Local Abbreviation ps := (PSOIW.ips I).
Local Abbreviation M0 := (PSOIW.iM I).    Local Abbreviation ch := (PSOIW.ich I).    Local Abbreviation gx := (PSOIW.ig1 I).      (* [comment removed for export] *)
Let E0 := PSOIW.E0 I.
Let st0 := PSOIW.st0 I.
Let wlen := PSOIW.wlen I.
Let wp0 := PSOIW.wp0 I.
Let we0 := PSOIW.we0 I.

(* [comment removed for export] *)
Definition bptrI (i : nat) (Ex : env) : Z := CL5A.uv Ex (fst (PSO.blk0 i)).
Definition bcapI (i : nat) (Ex : env) : Z := CL5A.uv Ex (snd (PSO.blk0 i)).
Definition sbI (i : nat) (Ex : env) : Z := CL5A.uv Ex (fst (PSO.blk1 i)).
Definition scapI (i : nat) (Ex : env) : Z := CL5A.uv Ex (snd (PSO.blk1 i)).
(* [comment removed for export] *)
Definition stk_kx (sc : Z) : Z := Z.log2 (1056 / sc) * hl_k_per_malloc L.
Definition stk_bx (sc : Z) : Z := hl_b_lin L * (2112 - 2 * sc) + Z.log2 (1056 / sc) * hl_b_overhead L.
Definition Cred (i : nat) (Ex : env) (cr1 : credit) : Prop := PMSA.bufcredA L cr1 (bcapI i Ex) (stk_kx (scapI i Ex) + PSOIW.KXG I gx) (stk_bx (scapI i Ex) + PSOIW.BXG I gx).      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition FLF (Ex : env) : Prop := ar_fs ar <= CL5A.uv Ex FLE < ar_fs ar + 11571200 /\ ~ aclient L ar LBo FF sp (CH.hd_scr GT.HDECL) (CL5A.uv Ex FLE).

(* [comment removed for export] *)
Definition WIN (ps1 : PML.pstate) : Prop :=
  match PML.ps_win ps with
  | Some (p0, e0) => exists p1, PML.ps_win ps1 = Some (p1, e0) /\ p0 <= p1 <= e0
  | None => PML.ps_win ps1 = None
  end.
(* [comment removed for export] *)
Definition QOK (ps1 : PML.pstate) : Prop := In (PML.ps_st ps1) QSTATES \/ (PML.ps_st ps1 = PML.ST_NUMBER /\ PMSA.win_exhausted ps1).
(* [comment removed for export] *)
Definition STOPOK (ps1 : PML.pstate) : Prop := PML.ps_more ps1 = false -> PML.ws_ok ps1 /\ PML.ps_done ps1 = true /\ PML.ps_st ps1 = PML.ST_DONE.
(* [comment removed for export] *)
Definition PTR (pc : Z) (ps1 : PML.pstate) (code : Z) : Prop :=
  code = 0 ->
  PML.ps_more ps1 = true /\
  (pc = PNUMBER -> In (PML.ps_st ps1) [PML.ST_NUMBER; PML.ST_ACCEPT; PML.ST_EXPECT_COMMA_OR_END] /\ (PML.ps_st ps1 = PML.ST_NUMBER -> PMSA.win_exhausted ps1)) /\
  (pc = ENDINT \/ pc = ENDFRAC -> In (PML.ps_st ps1) [PML.ST_ACCEPT; PML.ST_EXPECT_COMMA_OR_END]).
(* [comment removed for export] *)
Definition REL (ps1 : PML.pstate) (code : Z) : Prop :=
  (code <> 0 \/ PML.ps_more ps1 = false \/ PMSA.win_exhausted ps1) /\
  (PML.ps_st ps = PML.ST_ACCEPT -> code = 0 /\ PML.ps_more ps1 = false /\ PML.ps_done ps1 = true) /\
  (PMSA.win_exhausted ps -> code = 0 -> PML.ps_more ps1 = true -> In (PML.ps_st ps) [PML.ST_NUMBER; PML.ST_CR] /\ ~ In (PML.ps_st ps1) [PML.ST_NUMBER; PML.ST_CR]) /\
  (code = 0 -> PML.ws_ok ps1).


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition w0 : list Z := PSOIW.iwinb I.
Definition c0 : PMR.ctrl := PSOIW.ic0 I.
Local Abbreviation eg0 := (PSOIW.ieg I).
Definition XCELLS (M : mem) (cp cp2 tg : Z) : Prop := PMSA.u32 L M (P + 148) cp /\ PMSA.u32 L M (P + 152) cp2 /\ PMSA.u8 L M (P + 220) tg /\ 0 <= tg < 256.
(* [comment removed for export] *)
Definition MATCH (c : PMR.ctrl) (ps1 : PML.pstate) (cp cp2 tg : Z) : Prop :=
  PMR.rm_core c ps1 /\
  (PML.ps_st ps1 = PML.ST_STRING ->
     PMR.c_sst c = PML.ps_sst ps1 /\ PMR.c_dlen c = Z.of_nat (length (PML.ps_buf ps1)) /\ PMR.c_u8 c = PMR.u8_feeds PMR.u8_init (PMR.b256 (PML.ps_buf ps1)) /\
     (3 <= PMR.c_sst c <= 11 -> PMR.c_cp c = cp) /\ (9 <= PMR.c_sst c <= 11 -> PMR.c_cp2 c = cp2) /\ 0 <= tg <= 1) /\
  (PML.ps_st ps1 = PML.ST_NUMBER -> PMR.c_nst c = PML.ps_nst ps1 /\ PMR.c_dlen c = Z.of_nat (length (PML.ps_buf ps1))).
Lemma MATCH_A : forall c M ps1 cp cp2 tg, XCELLS M cp cp2 tg -> MATCH c ps1 cp cp2 tg -> PMRXA.rm_matchA L c M P ps1.
Proof.
  intros c M ps1 cp cp2 tg (X1 & X2 & X3 & X4) (R & S & N). split; [exact R|]. split; [|exact N]. intros Hs. destruct (S Hs) as (S1 & S2 & S3 & S4 & S5 & S6).
  split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [intros H; rewrite (S4 H); exact X1|]. split; [intros H; rewrite (S5 H); exact X2|]. exists tg. split; [exact X3 | exact S6].
Qed.
Lemma A_MATCH : forall c M ps1 cp cp2 tg, XCELLS M cp cp2 tg -> PMRXA.rm_matchA L c M P ps1 ->
  exists cp' cp2', XCELLS M cp' cp2' tg /\ MATCH c ps1 cp' cp2' tg.
Proof.
  intros c M ps1 cp cp2 tg (X1 & X2 & X3 & X4) (R & S & N).
  destruct (Z.eq_dec (PML.ps_st ps1) PML.ST_STRING) as [Hs|Hs].
  - destruct (S Hs) as (S1 & S2 & S3 & S4 & S5 & (t & T1 & T2)).
    assert (Et : t = tg).
    { unfold PMSA.u8, L5.u8_at in T1, X3. rewrite T1 in X3. assert (E8 : Z_to_bv 8 t = Z_to_bv 8 tg) by congruence. apply (f_equal bv_unsigned) in E8.
      rewrite !Z_to_bv_unsigned in E8. unfold bv_wrap in E8. change (bv_modulus 8) with 256 in E8. rewrite !Z.mod_small in E8 by lia. exact E8. }
    subst t.
    exists (if ((3 <=? PMR.c_sst c) && (PMR.c_sst c <=? 11))%bool then PMR.c_cp c else cp), (if ((9 <=? PMR.c_sst c) && (PMR.c_sst c <=? 11))%bool then PMR.c_cp2 c else cp2).
    split.
    + split; [|split; [|exact (conj X3 X4)]].
      * destruct (Z.leb_spec 3 (PMR.c_sst c)); destruct (Z.leb_spec (PMR.c_sst c) 11); cbn [andb]; try exact X1. exact (S4 ltac:(lia)).
      * destruct (Z.leb_spec 9 (PMR.c_sst c)); destruct (Z.leb_spec (PMR.c_sst c) 11); cbn [andb]; try exact X2. exact (S5 ltac:(lia)).
    + split; [exact R|]. split; [|exact N]. intros _. split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
      split; [intros H; destruct (Z.leb_spec 3 (PMR.c_sst c)); destruct (Z.leb_spec (PMR.c_sst c) 11); cbn [andb]; first [reflexivity | lia]|].
      split; [intros H; destruct (Z.leb_spec 9 (PMR.c_sst c)); destruct (Z.leb_spec (PMR.c_sst c) 11); cbn [andb]; first [reflexivity | lia] | exact T2].
  - exists cp, cp2. split; [exact (conj X1 (conj X2 (conj X3 X4)))|]. split; [exact R|]. split; [intros H; exfalso; exact (Hs H) | exact N].
Qed.
(* [comment removed for export] *)
Lemma XCELLS_ag : forall (M1 M2 : mem) cp cp2 tg, 0 <= P -> P + 272 <= 2 ^ 64 -> (forall a, P <= a < P + 272 -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  XCELLS M1 cp cp2 tg -> XCELLS M2 cp cp2 tg.
Proof.
  intros M1 M2 cp cp2 tg HP0 HP1 AG (X1 & X2 & X3 & X4). unfold PMSA.u32, PMSA.u8 in *.
  split; [|split; [|split; [|exact X4]]].
  - apply (PTA.u32_ag (hl_segs L) M1 M2 (fun a => P <= a < P + 272) AG); [split; [lia|]; split; [lia|]; intros y Hy; lia | exact X1].
  - apply (PTA.u32_ag (hl_segs L) M1 M2 (fun a => P <= a < P + 272) AG); [split; [lia|]; split; [lia|]; intros y Hy; lia | exact X2].
  - apply (PTA.u8_ag (hl_segs L) M1 M2 (fun a => P <= a < P + 272) AG); [split; [lia|]; split; [lia|]; intros y Hy; lia | exact X3].
Qed.
(* [comment removed for export] *)
Lemma win_bytesA_suffix : forall (M0 M' : mem) w p0 e0 p1 psa psb,
  PMXAW.win_bytesA L M0 psa w -> PML.ps_win psa = Some (p0, e0) -> PML.ps_win psb = Some (p1, e0) -> p0 <= p1 <= e0 ->
  (forall a, p0 <= a < e0 -> M' (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) -> PMXAW.win_bytesA L M' psb (skipn (Z.to_nat (p1 - p0)) w).
Proof.
  intros M0 M' w p0 e0 p1 psa psb HWB Ha Hb Hp AG. unfold PMXAW.win_bytesA in *. rewrite Ha in HWB. rewrite Hb. destruct HWB as (HB & HL & HF).
  split; [|split; [rewrite length_skipn; clear - HL Hp; lia | rewrite <- (firstn_skipn (Z.to_nat (p1 - p0)) w) in HF; apply Forall_app in HF as [_ HF]; exact HF]].
  intros i Hi. rewrite length_skipn in Hi. rewrite nth_skipn. unfold L5.u8_at. cbn [rdn]. rewrite (AG (p1 + Z.of_nat i)) by (clear - Hi HL Hp; lia).
  pose proof (HB (Z.to_nat (p1 - p0) + i)%nat ltac:(clear - Hi HL Hp; lia)) as X. unfold L5.u8_at in X. cbn [rdn] in X.
  replace (p0 + Z.of_nat (Z.to_nat (p1 - p0) + i)) with (p1 + Z.of_nat i) in X by (clear - Hp; lia). exact X.
Qed.
Lemma win_bytesA_none : forall (M0 M' : mem) w psa psb n, PMXAW.win_bytesA L M0 psa w -> PML.ps_win psa = None -> PML.ps_win psb = None -> PMXAW.win_bytesA L M' psb (skipn n w).
Proof. intros M0 M' w psa psb n HWB Ha Hb. unfold PMXAW.win_bytesA in *. rewrite Ha in HWB. rewrite Hb, HWB. destruct n; reflexivity. Qed.
(* [comment removed for export] *)
Lemma XCELLS_of_pa : forall (M : mem) psx tg, PMLA.parser_at (hl_segs L) IC M P psx -> PMSA.u8 L M (P + 220) tg -> 0 <= tg < 256 -> 0 <= P -> P + 272 <= 2 ^ 64 ->
  exists cp cp2, XCELLS M cp cp2 tg.
Proof.
  intros M psx tg HPA Ht Rt HP0 HP1.
  destruct (ex_u32 (hl_segs L) M (P + 148) ltac:(intros y Hy; replace (P + 148 + y) with (P + (148 + y)) by lia; apply (PTB.pa_def L IC M P psx HPA); lia) ltac:(lia) ltac:(lia)) as (cp & _ & H1).
  destruct (ex_u32 (hl_segs L) M (P + 152) ltac:(intros y Hy; replace (P + 152 + y) with (P + (152 + y)) by lia; apply (PTB.pa_def L IC M P psx HPA); lia) ltac:(lia) ltac:(lia)) as (cp2 & _ & H2).
  exists cp, cp2. exact (conj H1 (conj H2 (conj Ht Rt))).
Qed.
(* [comment removed for export] *)
Lemma wf_stack_ok : forall ps1 c, PML.wf_ps ps1 -> PML.ps_more ps1 = true -> PMR.rm_core c ps1 -> PMRF.stack_ok c.
Proof.
  intros ps1 c WF Hm (_ & _ & _ & _ & Hstk). unfold PMRF.stack_ok. rewrite Hstk.
  destruct WF as (_ & _ & _ & _ & C & T & HS & HC & HM). destruct (HM Hm) as (_ & _ & _ & HT & _). rewrite HS.
  constructor; [reflexivity|]. apply Forall_app. split.
  - apply Forall_impl with (P := PML.is_container); [|exact HC]. intros a [-> | ->]; reflexivity.
  - destruct HT as [[-> _] | [[-> _] | [(S & HS1 & -> & _) | (S & HS1 & -> & _)]]]; [constructor | constructor; [reflexivity | constructor] | |].
    + constructor; [|constructor]. destruct HS1 as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; reflexivity.
    + constructor; [|constructor; [reflexivity | constructor]]. destruct HS1 as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; reflexivity.
Qed.
Lemma wf_stack_nots : forall ps1, PML.wf_ps ps1 -> PML.ps_more ps1 = true -> Forall PMRA.nots (PML.ps_stack ps1).
Proof.
  intros ps1 WF Hm. destruct WF as (_ & _ & _ & _ & C & T & HS & HC & HM). destruct (HM Hm) as (_ & _ & _ & HT & _). rewrite HS. unfold PMRA.nots.
  constructor; [unfold PML.ST_ROOT, PML.ST_STRING, PML.ST_NUMBER; lia|]. apply Forall_app. split.
  - apply Forall_impl with (P := PML.is_container); [|exact HC]. intros a [-> | ->]; unfold PML.ST_OBJECT, PML.ST_ARRAY, PML.ST_STRING, PML.ST_NUMBER; lia.
  - destruct HT as [[-> _] | [[-> _] | [(S & HS1 & -> & _) | (S & HS1 & -> & _)]]];
      repeat first [apply Forall_nil | apply Forall_cons]; try (destruct HS1 as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]); cbv; lia.
Qed.
(* [comment removed for export] *)
Definition SYNC (evs : list PMW.evk) (al : Z) : Prop :=
  PMES.g_es gx = PMW.es_run (PMES.g_es eg0) evs /\ exists pay, 0 <= pay <= al /\ PMES.g_len gx = PMES.g_len eg0 + PMW.ind_run (PMES.g_es eg0) evs + pay.
Definition lpos (ps1 : PML.pstate) : Z := PSOIW.wlo (PML.ps_win ps1).
Definition rem (ps1 : PML.pstate) (off : Z) : list Z := skipn (Z.to_nat (lpos ps1 - wp0 + off)) w0.
(* [comment removed for export] *)
Definition ATH (c : PMR.ctrl) (ps1 : PML.pstate) (off : Z) (evs : list PMW.evk) (al : Z) : Prop := PMRF.hreach c0 w0 c (rem ps1 off) evs al.
(* [comment removed for export] *)
Definition MID (c : PMR.ctrl) (b : Z) (ps1 : PML.pstate) (off : Z) (evs : list PMW.evk) (al : Z) (a : PMR.act) : Prop :=
  rem ps1 off = b :: rem ps1 (off + 1) /\ PMRF.hreach c0 w0 c (rem ps1 off) evs al /\ PMR.c_more c = true /\ PMR.dispatch (PMR.c_st c) (PMR.top c) b = a.
(* [comment removed for export] *)
Definition RA (i : nat) : option PMR.act := PSOWT.ract i.
(* [comment removed for export] *)
Definition PAR (i : nat) (Ex : env) (c : PMR.ctrl) : Prop := forall v, In v (PSOWT.ppv i) -> CL5A.uv Ex (EVar v) = PMR.top c.
Definition BEF (i : nat) (Ex : env) (c : PMR.ctrl) (ps1 : PML.pstate) (off : Z) (evs : list PMW.evk) (al : Z) : Prop :=
  ATH c ps1 off evs al /\ SYNC evs al /\ PMR.c_more c = true /\ PSOIW.wp0 I <= lpos ps1 + off /\ rem ps1 off <> [] /\ PAR i Ex c.
Definition WO (i : nat) : Z := PSOWT.woff i.
(* [comment removed for export] *)
Definition ps_with (p : PML.pstate) (st : Z) (stack : list Z) : PML.pstate :=
  PML.PS st (PML.ps_sst p) (PML.ps_nst p) (PML.ps_more p) (PML.ps_done p) (PML.ps_level p) stack (PML.ps_sb p) (PML.ps_scap p) (PML.ps_bcap p) (PML.ps_bptr p) (PML.ps_buf p) (PML.ps_win p).
(* [comment removed for export] *)
Definition PTOFF (i : nat) : Z := match RA i with Some PMR.AComma => 1 | _ => 0 end.
Definition PTW (i : nat) (ps1 : PML.pstate) (code : Z) (cp cp2 tg : Z) : Prop :=
  exists evs al q, code = PMR.q_code q /\ SYNC (evs ++ PMR.q_evs q) (al + PMR.q_al q) /\
    (code <> 0 -> PMR.parse_some c0 w0 = PMRF.pre evs al q) /\
    (code = 0 -> MATCH (PMR.q_c q) ps1 cp cp2 tg /\ PMRF.hreach c0 w0 (PMR.q_c q) (rem ps1 (PTOFF i)) (evs ++ PMR.q_evs q) (al + PMR.q_al q) /\
                 (PTOFF i = 1 -> PMR.c_st (PMR.q_c q) <> PML.ST_STRING /\ PMR.c_st (PMR.q_c q) <> PML.ST_NUMBER)).
(* [comment removed for export] *)
Definition WERR (code : Z) : Prop := exists evs al q, PMR.parse_some c0 w0 = PMRF.pre evs al q /\ PMR.q_code q = code /\ code <> 0 /\ SYNC (evs ++ PMR.q_evs q) (al + PMR.q_al q).
(* [comment removed for export] *)
Definition WEXIT (ps1 : PML.pstate) (code : Z) (cp cp2 tg : Z) : Prop :=
  let rr := PMW.rm_step (PMRXA.the_rmA L) PMW.FParseSome c0 (PMW.inp_win ps w0 (PSOIW.ix I)) in
  code = PMW.r_code rr /\ PMES.g_es gx = PMW.es_run (PMES.g_es eg0) (PMW.r_evs rr) /\
  (exists pay, 0 <= pay <= PMW.r_allow rr /\ PMES.g_len gx = PMES.g_len eg0 + PMW.ind_run (PMES.g_es eg0) (PMW.r_evs rr) + pay) /\
  (code = 0 -> MATCH (PMW.r_ctrl rr) ps1 cp cp2 tg /\ PMW.r_used rr = PML.winlen ps - PML.winlen ps1).
(* [comment removed for export] *)
Definition WSIM (i : nat) (Ex : env) (ps1 : PML.pstate) (code : Z) (cp cp2 tg : Z) : Prop :=
  match PSO.kind_of i with
  | PSO.KEntry => True                                                                 (* [comment removed for export] *)
  | PSO.KSm => MATCH c0 ps1 cp cp2 tg /\ SYNC [] 0 /\ PMRF.stack_ok c0                  (* [comment removed for export] *)
  | PSO.KH | PSO.KHQ | PSO.KL | PSO.KLQ | PSO.KLZ | PSO.KL3 => exists c evs al, ATH c ps1 0 evs al /\ MATCH c ps1 cp cp2 tg /\ SYNC evs al
  | PSO.KL2 => exists c evs al, ATH c ps1 1 evs al /\ MATCH c ps1 cp cp2 tg /\ SYNC evs al /\ PMR.c_st c <> PML.ST_STRING /\ PMR.c_st c <> PML.ST_NUMBER   (* [comment removed for export] *)
  | PSO.KCsl => exists c evs al, BEF i Ex c ps1 (WO i) evs al /\ MATCH c ps1 cp cp2 tg               (* [comment removed for export] *)
  | PSO.KVis _ => exists c b evs al, MID c b ps1 (WO i) evs al PMR.ALitDone /\ MATCH c ps1 cp cp2 tg /\ SYNC (evs ++ [PMW.EkLit]) (al + PMR.AL_LIT)
  | PSO.KVpush => exists c b evs al a x old, RA i = Some a /\ MID c b ps1 (WO i) evs al a /\ SYNC evs al /\ PML.ps_stack ps1 = old ++ [x] /\
                  MATCH c (ps_with ps1 (PML.ps_st ps1) old) cp cp2 tg      (* [comment removed for export] *)
  | PSO.KPushb => exists c b evs al, MID c b ps1 (-1) evs al PMR.ANumber /\ SYNC evs al /\ PML.ps_buf ps1 = [b] /\
                  PMR.rm_core c (ps_with ps1 (PMR.c_st c) (PML.ps_stack ps1)) /\ PMR.c_st c <> PML.ST_STRING /\ PMR.c_st c <> PML.ST_NUMBER /\ 0 <= tg <= 255
                  (* [comment removed for export] *)
  | PSO.KPop => exists c evs al x, ATH c ps1 (WO i) evs al /\ SYNC evs al /\ CL5A.uv Ex (EVar (CC.cp_nx (PSO.cutn i) - APC.NCS - 2)) = x /\      (* [comment removed for export] *)
                MATCH c (ps_with ps1 x (PML.ps_stack ps1)) cp cp2 tg /\ x <> PML.ST_STRING /\ x <> PML.ST_NUMBER
                (* [comment removed for export] *)
  | PSO.KParent | PSO.KErrh =>
         (PSOWT.eofk i = false /\ exists c evs al, BEF i Ex c ps1 (WO i) evs al /\ MATCH c ps1 cp cp2 tg)
      \/ (PSOWT.eofk i = true /\ WERR PMR.E_EOF)
         (* [comment removed for export] *)
  | PSO.KSetec => WERR code
  | PSO.KSe => exists code', CL5A.uv Ex (EVar PSOWT.SEV) = code' /\ WERR code'      (* [comment removed for export] *)
  | PSO.KPt _ => PTW i ps1 code cp cp2 tg
  | PSO.KRetx | PSO.KSetsh => WEXIT ps1 code cp cp2 tg
  | PSO.KDead => True
  end.
(* [comment removed for export] *)
Definition WCORE (i : nat) (Ex : env) (M : mem) (ps1 : PML.pstate) (code : Z) : Prop := exists cp cp2 tg, XCELLS M cp cp2 tg /\ WSIM i Ex ps1 code cp cp2 tg.

(* [comment removed for export] *)
Definition a0reg (i : nat) : expr := nth 10 (CC.cp_regs (PSO.cutn i)) (ELit 0).
(* [comment removed for export] *)
Definition retk (k : PSO.kind) : bool := match k with PSO.KRetx | PSO.KSetsh => true | _ => false end.
Definition wlk (k : PSO.kind) : bool := match k with PSO.KRetx | PSO.KSetsh | PSO.KSe | PSO.KSetec => false | _ => true end.
(* [comment removed for export] *)
Definition vpx (i : nat) : Z :=
  match PSO.src_of i with
  | Some (i0, k0, _) => match CAX.cell_at (PSO.leaf_cells i0 k0) (EVar 2) (-105) 1 with Some (ELit z) => z | _ => -1 end
  | None => -1
  end.
Lemma set_win_self : forall psx, PML.ps_set_win psx (PML.ps_win psx) = psx.
Proof. intros psx; destruct psx; reflexivity. Qed.
Record CORE (i : nat) (Ex : env) (M : mem) (mw : option (Z * Z)) (ps1 : PML.pstate) (code : Z) (g1 : PML.ls_state) : Prop := MKCORE {
  c_pa : PMLA.parser_at (hl_segs L) IC M P (PML.ps_set_win ps1 mw);
  c_mw : (PSO.curk (PSO.kind_of i) = false /\ mw = PML.ps_win ps1) \/      (* [comment removed for export] *)
         (PSO.curk (PSO.kind_of i) = true /\ exists pm pn e, mw = Some (pm, e) /\ PML.ps_win ps1 = Some (pn, e) /\ pm <= pn /\ CL5A.uv Ex (a0reg i) = pn) \/
         (PSO.kind_of i = PSO.KPushb /\ exists p e, mw = Some (p, e) /\ PML.ps_win ps1 = Some (p + 1, e));      (* [comment removed for export] *)
  c_sh : PMLA.parser_sh M ps1;
  c_win : WIN ps1;
  c_bb : PML.buf_bound ps1 B;
  c_ec : PMLA.ec_at (hl_segs L) IC M E code;
  c_ls : PMLA.ls_ok (hl_segs L) IC g1 M;
  c_g : g1 = g \/ (g1 = PML.LS2 /\ code <> 0);
  c_blk : PML.ps_blocks ps1 = [(bptrI i Ex, bcapI i Ex); (sbI i Ex, scapI i Ex)];
  c_na : PSO.u0 i = false -> retk (PSO.kind_of i) = false -> st0 <> PML.ST_ACCEPT;      (* [comment removed for export] *)
  c_wl : PSO.u0 i = false -> wlk (PSO.kind_of i) = true -> 1 <= wlen;                (* [comment removed for export] *)
  c_e0 : PSO.u0 i = true -> env_agree 60 E0 Ex;
  (* [comment removed for export] *)
  c_x : PSOIW.xinv I M gx;
  c_sync : code = 0 -> PMXA.enc_sync ps1 gx }.

(* [comment removed for export] *)
Definition POSTP (i : nat) (Ex : env) (M : mem) : Prop :=
  exists ps1 code g1, CORE i Ex M (PML.ps_win ps1) ps1 code g1 /\ WCORE i Ex M ps1 code /\ PML.wf_ps ps1 /\ (code <> 0 -> PML.ps_more ps1 = false) /\ REL ps1 code.

(* [comment removed for export] *)
Record XI_R (i : nat) (Ex : env) (M : mem) : Prop := MKXI {
  xi_flf : (2 <= i)%nat -> FLF Ex;
  xi_entry : PSO.kind_of i = PSO.KEntry -> env_agree 60 E0 Ex /\ M = M0 /\ gx = PSOIW.ieg I;      (* [comment removed for export] *)
  xi_sm : PSO.kind_of i = PSO.KSm -> CORE i Ex M (PML.ps_win ps) ps 0 g /\ WCORE i Ex M ps 0;
  xi_loop : PSO.is_loopk (PSO.kind_of i) = true ->
      exists ps1 g1, CORE i Ex M (PML.ps_win ps1) ps1 0 g1 /\ WCORE i Ex M ps1 0 /\ PML.wf_ps ps1 /\ STOPOK ps1 /\ (PSO.isQcut i = true -> PML.ps_more ps1 = true -> QOK ps1);
  xi_errh : PSO.kind_of i = PSO.KErrh \/ PSO.kind_of i = PSO.KParent -> exists ps1 g1, CORE i Ex M (PML.ps_win ps1) ps1 0 g1 /\ WCORE i Ex M ps1 0 /\ PML.wf_ps ps1 /\ PML.ps_more ps1 = true;
  xi_se : PSO.kind_of i = PSO.KSe -> exists ps1 g1, CORE i Ex M (PML.ps_win ps1) ps1 0 g1 /\ WCORE i Ex M ps1 0 /\ PML.wf_ps ps1 /\ PML.ps_more ps1 = false;
  xi_setec : PSO.kind_of i = PSO.KSetec -> exists ps1 code g1, CORE i Ex M (PML.ps_win ps1) ps1 code g1 /\ WCORE i Ex M ps1 code /\ PML.wf_ps ps1 /\ 1 <= code <= 31 /\ g1 = PML.LS2;
  xi_pt : forall pc, PSO.kind_of i = PSO.KPt pc ->
      exists ps1 mw code g1, CORE i Ex M mw ps1 code g1 /\ WCORE i Ex M ps1 code /\ PML.wf_ps ps1 /\ (code <> 0 -> PML.ps_more ps1 = false) /\ 0 <= code <= 31 /\ PTR pc ps1 code;
  xi_pushb : PSO.kind_of i = PSO.KPushb ->      (* [comment removed for export] *)
      exists ps1 p e g1 c, CORE i Ex M (Some (p, e)) ps1 0 g1 /\ WCORE i Ex M ps1 0 /\ PML.ps_win ps1 = Some (p + 1, e) /\ PML.wf_ps ps1 /\ PML.ps_more ps1 = true /\
                           PML.ps_st ps1 <> PML.ST_NUMBER /\ PML.ps_buf ps1 = [c];
  xi_vpush : PSO.kind_of i = PSO.KVpush ->
      exists ps1 g1 x stk, CORE i Ex M (PML.ps_win ps1) ps1 0 g1 /\ WCORE i Ex M ps1 0 /\ PML.ps_more ps1 = true /\ PML.ps_stack ps1 = stk ++ [x] /\ (length stk <= 1026)%nat /\ x = vpx i /\
        PML.wf_ps (PML.PS (PML.ps_st ps1) (PML.ps_sst ps1) (PML.ps_nst ps1) true (PML.ps_done ps1) (PML.ps_level ps1) stk (PML.ps_sb ps1) (PML.ps_scap ps1)
                          (PML.ps_bcap ps1) (PML.ps_bptr ps1) (PML.ps_buf ps1) (PML.ps_win ps1)) /\
        ((PML.is_expect (PML.ps_st ps1) /\ x = PML.ps_st ps1) \/ (PML.ps_st ps1 = PML.ST_SLASH_STAR /\ x = PML.ST_SLASH_STAR) \/
         ((PML.ps_st ps1 = PML.ST_EXPECT_MEMBER_NAME_OR_END \/ PML.ps_st ps1 = PML.ST_EXPECT_MEMBER_NAME) /\ x = PML.ST_MEMBER_NAME));
  xi_pop : PSO.kind_of i = PSO.KPop ->
      exists ps1 g1 x, CORE i Ex M (PML.ps_win ps1) ps1 0 g1 /\ WCORE i Ex M ps1 0 /\ PML.ps_more ps1 = true /\ PML.comment_or_cr (PML.ps_st ps1) /\
        PML.wf_ps (PML.PS (PML.ps_st ps1) (PML.ps_sst ps1) (PML.ps_nst ps1) true (PML.ps_done ps1) (PML.ps_level ps1) (PML.ps_stack ps1 ++ [x]) (PML.ps_sb ps1) (PML.ps_scap ps1)
                          (PML.ps_bcap ps1) (PML.ps_bptr ps1) (PML.ps_buf ps1) (PML.ps_win ps1)) /\
        CL5A.uv Ex (EVar (CC.cp_nx (PSO.cutn i) - APC.NCS - 2)) = x /\      (* [comment removed for export] *)
        (In x (PML.ST_MEMBER_NAME :: PMXA.KEY_STATES) -> 1 <= PML.ps_level ps1);      (* [comment removed for export] *)
  (* [comment removed for export] *)
  xi_vis : forall pc, PSO.kind_of i = PSO.KVis pc -> exists ps1 g1, CORE i Ex M (PML.ps_win ps1) ps1 0 g1 /\ WCORE i Ex M ps1 0 /\ PML.wf_ps ps1 /\ PML.ps_more ps1 = true;
  xi_post : PSO.kind_of i = PSO.KRetx \/ PSO.kind_of i = PSO.KSetsh -> POSTP i Ex M;
  xi_dead : PSO.kind_of i = PSO.KDead -> False }.
Definition XI (i : nat) (Ex : env) (A1 : list (Z * Z)) (M : mem) (m1 : Model) : Prop := XI_R i Ex M.
End X.
End PSOX.
