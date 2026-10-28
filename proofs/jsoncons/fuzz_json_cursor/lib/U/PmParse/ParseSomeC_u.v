(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u PmCurDefs_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSums2_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSpecs_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseBridges_u ParseBridges2_u ParseBridges3_u ParseBridges4_u ParseBridges5_u ParseSomeAt_u ParseSomeSem_u ParseSomeSemC_u ParseSomeCurC_u ParseSomeChk_u ParseSomeChk2_u ParseSomeChk3_u ParseSomeA_u ParseSomeB_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Import PSMC.
Module PSX.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.

Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.

Lemma pa_fr_cur : forall (F : list L5.range) (M M' : mem), L5.frame_but F M M' -> mem_grows M M' -> forall P ps2 p e p',
  PB2.out F P 200 -> PB2.out F (P + 208) 64 -> PB2.out F (PML.ps_bptr ps2) (PML.ps_bcap ps2) -> PB2.out F (PML.ps_sb ps2) (PML.ps_scap ps2) ->
  PML.parser_at M P (PML.ps_set_win ps2 (Some (p, e))) -> PML.u64 M' (P + 200) p' -> p' <= e -> PML.parser_at M' P (PML.ps_set_win ps2 (Some (p', e))).
Proof.
  intros F M M' FR GR P ps2 p e p' HP1 HP2 HB HS H Hc Hle. destruct ps2 as [st sst nst mo dn lv stk sb sc bc bp buf w]. unfold PML.ps_set_win, PML.parser_at in *.
  cbn [PML.ps_st PML.ps_sst PML.ps_nst PML.ps_more PML.ps_done PML.ps_level PML.ps_stack PML.ps_sb PML.ps_scap PML.ps_bcap PML.ps_bptr PML.ps_buf PML.ps_win] in *.
  destruct H as (A0 & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30).
  assert (O8 : forall k, 0 <= k -> (k + 8 <= 200 \/ 208 <= k /\ k + 8 <= 272) -> PB2.out F (P + k) 8) by (intros k K0 [K1|K1]; [apply (PB2.out_sub F _ _ _ _ HP1) | apply (PB2.out_sub F _ _ _ _ HP2)]; lia).
  assert (O4 : forall k, 0 <= k -> (k + 4 <= 200 \/ 208 <= k /\ k + 4 <= 272) -> PB2.out F (P + k) 4) by (intros k K0 [K1|K1]; [apply (PB2.out_sub F _ _ _ _ HP1) | apply (PB2.out_sub F _ _ _ _ HP2)]; lia).
  assert (O1 : forall k, 0 <= k -> (k + 1 <= 200 \/ 208 <= k /\ k + 1 <= 272) -> PB2.out F (P + k) 1) by (intros k K0 [K1|K1]; [apply (PB2.out_sub F _ _ _ _ HP1) | apply (PB2.out_sub F _ _ _ _ HP2)]; lia).
  assert (O24 : forall k, 0 <= k -> (k + 24 <= 200 \/ 208 <= k /\ k + 24 <= 272) -> PB2.out F (P + k) 24) by (intros k K0 [K1|K1]; [apply (PB2.out_sub F _ _ _ _ HP1) | apply (PB2.out_sub F _ _ _ _ HP2)]; lia).
  split; [apply (PB2.u64_fr F M M' FR); [replace P with (P + 0) by lia; apply O8; lia | exact A0]|].
  split; [apply (PB2.u32_fr F M M' FR); [apply O4; lia | exact A1]|].
  split; [apply (PB2.u8_fr F M M' FR); [apply O1; lia | exact A2]|]. split; [apply (PB2.u8_fr F M M' FR); [apply O1; lia | exact A3]|]. split; [apply (PB2.u8_fr F M M' FR); [apply O1; lia | exact A4]|].
  split; [apply (PB2.u8_fr F M M' FR); [apply O1; lia | exact A5]|]. split; [apply (PB2.u8_fr F M M' FR); [apply O1; lia | exact A6]|]. split; [apply (PB2.u8_fr F M M' FR); [apply O1; lia | exact A7]|].
  split; [apply (PB2.u8_fr F M M' FR); [apply O1; lia | exact A8]|].
  split; [apply (PB2.lstr_short_nil_fr F M M' FR); [apply O24; lia | exact A9]|]. split; [apply (PB2.lstr_short_nil_fr F M M' FR); [apply O24; lia | exact A10]|]. split; [apply (PB2.lstr_short_nil_fr F M M' FR); [apply O24; lia | exact A11]|].
  split; [apply (PB2.u64_fr F M M' FR); [apply O8; lia | exact A12]|]. split; [apply (PB2.u64_fr F M M' FR); [apply O8; lia | exact A13]|].
  split; [apply (PB2.u32_fr F M M' FR); [apply O4; lia | exact A14]|].
  split; [destruct A15 as (X & Y & Z); split; [exact Hc | split; [apply (PB2.u64_fr F M M' FR); [apply O8; lia | exact Y] | exact Hle]]|].
  split; [apply (PB2.u8_fr F M M' FR); [apply O1; lia | exact A16]|]. split; [apply (PB2.u8_fr F M M' FR); [apply O1; lia | exact A17]|]. split; [apply (PB2.u8_fr F M M' FR); [apply O1; lia | exact A18]|].
  split; [apply (PB2.u8_fr F M M' FR); [apply O1; lia | exact A19]|]. split; [apply (PB2.u8_fr F M M' FR); [apply O1; lia | exact A20]|]. split; [apply (PB2.u8_fr F M M' FR); [apply O1; lia | exact A21]|].
  split; [apply (PB2.u32_fr F M M' FR); [apply O4; lia | exact A22]|].
  split; [apply (PB2.str_long_fr F M M' FR); [apply O24; lia | exact HB | exact A23]|]. split; [exact A24|].
  split; [apply (PB2.u64_fr F M M' FR); [apply O8; lia | exact A25]|]. split; [apply (PB2.u64_fr F M M' FR); [apply O8; lia | exact A26]|]. split; [apply (PB2.u64_fr F M M' FR); [apply O8; lia | exact A27]|].
  split; [apply (PB2.bytes_fr F M M' FR); [apply (PB2.out_sub F _ _ _ _ HS); lia | exact A28]|]. split; [exact A29|]. apply (PB2.def_fr M M' GR). exact A30.
Qed.

Lemma wf_upd_same : forall ps done bcap bptr buf' w, PML.wf_ps ps -> (PML.ps_st ps = PML.ST_NUMBER -> PML.ps_more ps = true -> buf' = PML.ps_buf ps) ->
  PML.wf_ps (PSS.upd ps (PML.ps_st ps) (PML.ps_sst ps) (PML.ps_nst ps) (PML.ps_more ps) done bcap bptr buf' w).
Proof.
  intros ps done bcap bptr buf' w (W1 & W2 & W3 & W4 & (C & T & W5 & W6 & W7)) Hb. unfold PML.wf_ps, PSS.upd. cbn [PML.ps_sst PML.ps_nst PML.ps_stack PML.ps_scap PML.ps_more PML.ps_level PML.ps_st PML.ps_buf].
  repeat (split; [assumption|]). exists C, T. split; [exact W5|]. split; [exact W6|]. intros Hm. destruct (W7 Hm) as (X1 & X2 & X3 & X4 & X5 & X6). repeat (split; [assumption|]).
  intros Hn. rewrite (Hb Hn Hm). exact (X6 Hn).
Qed.

Lemma ws_accept : forall ps sst nst done bcap bptr buf w, PML.wf_ps ps -> PML.ps_more ps = true -> PML.ps_st ps = PML.ST_ACCEPT -> PML.ws_ok (PSS.upd ps PML.ST_DONE sst nst false done bcap bptr buf w).
Proof.
  intros ps sst nst done bcap bptr buf w (W1 & W2 & W3 & W4 & (C & T & W5 & W6 & W7)) Hm Hst _. destruct (W7 Hm) as (X1 & X2 & X3 & X4 & X5 & X6).
  assert (HT : T = []).
  { unfold PML.transient in X4. rewrite Hst in X4. unfold PML.comment_or_cr, PML.ST_ACCEPT, PML.ST_STRING, PML.ST_CR in X4.
    destruct X4 as [[X _]|[[_ X]|[(S & _ & _ & X)|(S & _ & _ & X)]]]; [exact X | discriminate X | exfalso; lia | exfalso; lia]. }
  subst T. rewrite app_nil_r in W5. exists C. unfold PSS.upd. cbn [PML.ps_st PML.ps_stack PML.ps_level]. split; [exact W6|]. split; [lia|]. split; [left; split; [reflexivity | exact W5] | exact X2].
Qed.
Lemma ws_upd_same : forall ps done bcap bptr buf w, PML.ws_ok ps -> PML.ws_ok (PSS.upd ps (PML.ps_st ps) (PML.ps_sst ps) (PML.ps_nst ps) (PML.ps_more ps) done bcap bptr buf w).
Proof. intros ps done bcap bptr buf w H. exact H. Qed.

Section C.
Context {SCFG_P : ScfgP}.
Variable I : PSI.inst.
Local Abbreviation L := (PSI.iL I).      Local Abbreviation HI := (PSI.iHI I).    Local Abbreviation LBo := (PSI.iLBo I).  Local Abbreviation cr := (PSI.icr I).
Local Abbreviation sp := (PSI.isp I).    Local Abbreviation r := (PSI.ir I).      Local Abbreviation P := (PSI.iP I).      Local Abbreviation V := (PSI.iV I).      Local Abbreviation E := (PSI.iE I).
Local Abbreviation B := (PSI.iB I).      Local Abbreviation kx := (PSI.ikx I).    Local Abbreviation bx := (PSI.ibx I).    Local Abbreviation g := (PSI.ig I).      Local Abbreviation ps := (PSI.ips I).
Local Abbreviation fx := (PSI.ifx I).    Local Abbreviation R := (PSI.iR I).      Local Abbreviation M := (PSI.iM I).      Local Abbreviation model := (PSI.imodel I).  Local Abbreviation K := (PSI.iK I).
Local Abbreviation HIok := (PSI.iHIok I).  Local Abbreviation LAY := (PSI.iLAY I).
Local Abbreviation E0 := (PSI.E0 I).     Local Abbreviation W := (PSI.W I).       Local Abbreviation Cred := (PSI.Cred I). Local Abbreviation XI := (PSI.XI I).
Local Abbreviation seg := (PSI.seg I).   Local Abbreviation wend := (PSI.wend I). Local Abbreviation wlen := (PSI.wlen I). Local Abbreviation st0 := (PSI.st0 I).  Local Abbreviation more0 := (PSI.more0 I).
Local Abbreviation HAMB := (CH2.heap_amb L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred).
Local Abbreviation AMB3 := (CH2.amb3 L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred XI).
Local Abbreviation is_leaf := (CH2.is_leaf G.CPS G.TAGS).
Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.

Lemma ls_pre : forall i E1 (M1 : mem) model1, HAMB i E1 M1 model1 -> (forall a, PSI.statw a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> PML.ls_ok g M1.
Proof.
  intros i E1 M1 model1 (_ & _ & _ & _ & Hfr & _) HX. apply (PB2.ls_ok_keep M M1); [|exact (PSI.iHG I) | exact (PSI.iHLS I)].
  intros a Ha. destruct (Z_lt_dec a 0xd4dfa) as [D1|D1]; [destruct (Z_le_dec 0xd4df8 a) as [D2|D2]; [apply HX; left; lia|]|].
  2: destruct (Z_le_dec 0xf6848 a) as [D3|D3]; [destruct (Z_lt_dec a 0xf6a68) as [D4|D4]; [apply HX; right; unfold PB2.ls_foot, PML.IMG_RO_HI in Ha; lia|]|].
  all: apply Hfr; unfold PB2.ls_foot, PML.IMG_RO_HI in Ha; pose proof (PSI.OBJR I) as (O1 & O2 & O3 & O4 & O5 & O6 & O7); pose proof (PSI.SPF I) as (S1 & S2 & S3 & S4 & S5 & S6);
    (split; [lia|]); (split; [right; right; rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY); split; [lia | intros X; pose proof (PmLayout.ly_static L LAY a X); lia]|]);
    (split; [unfold in_errno; rewrite (PmLayout.ly_errno L LAY); lia|]);
    intros w Hw; unfold PSI.W, PMS.W_parc, PML.W_par in Hw; cbn [app] in Hw; destruct Hw as [<-|[<-|[<-|[<-|[<-|[]]]]]]; unfold L5.in_rng; cbn [fst snd]; lia.
Qed.

Lemma win_def : forall i E1 (M1 : mem) model1, HAMB i E1 M1 model1 -> L5.defined M1 seg wlen.
Proof.
  intros i E1 M1 model1 (_ & _ & _ & _ & _ & Hdf) q Hq. pose proof (PSI.WIN I) as (W0 & W1 & W2 & Hwd & [[W4 W5]|(ch & Hch & Hc1 & Hc2 & (B0 & B1 & B2 & B3 & B4))]); [unfold PSI.wlen in *; lia|].
  pose proof (PSB.CEIL I) as CL. rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY) in B1. unfold PSI.wlen in *.
  apply Hdf; [unfold hl_ceil in *; lia | | apply Hwd; exact Hq].
  split; [left; exists (ch, 16384); split; [exact Hch | cbn [fst snd]; lia] | unfold in_errno; rewrite (PmLayout.ly_errno L LAY); lia].
Qed.
Lemma win_ok_of : forall (M1 : mem) st sst nst m dn lv stk sb sc bc bp buf p, L5.defined M1 seg wlen -> seg <= p <= wend ->
  PML.win_ok M1 LBo (PML.PS st sst nst m dn lv stk sb sc bc bp buf (PB4.win_of p wend)).
Proof.
  intros M1 st sst nst m dn lv stk sb sc bc bp buf p Hd Hp. unfold PML.win_ok, PB4.win_of. cbn [PML.ps_win]. destruct (Z.eqb_spec wend 0) as [Hz|Hz]; [exact Logic.I|].
  pose proof (PSI.WIN I) as (W0 & W1 & W2 & _ & [[W4 W5]|(ch & Hch & Hc1 & Hc2 & _)]); [lia|]. exists ch. split; [exact Hch|]. split; [lia|]. split; [lia|].
  eapply (L5.defined_sub _ _ _ _ _ Hd); unfold PSI.wlen; lia.
Qed.
Lemma WEX : PMS.win_exhausted ps -> wlen = 0.
Proof. unfold PMS.win_exhausted, PSI.wlen, PSI.wend, PSI.seg, PSI.wend_of, PSI.seg_of. destruct (PML.ps_win ps) as [[p e]|]; cbn [PSA.wincells fst snd]; intros H; lia. Qed.

Lemma exit_gen : forall i c k ps1, is_leaf i c k ps1 (CC.TOther RETPC) -> PB.exit_base_chk GT.NF RETPC c ps1 = true ->
  (forall E1 R1 E' R' (M1 M' : mem) model1, CC.At (hl_segs L) c E1 R1 M1 -> HAMB i E1 M1 model1 -> XI i E1 M1 -> env_agree (CC.cp_nx c) E1 E' -> CC.leaf_facts (hl_segs L) c ps1 E' R' M1 M' ->
     HAMB i E1 M' model1 -> env_agree GT.NF E0 E' ->
     exists (ps' : PML.pstate) (code : Z) (g' : PML.ls_state),
       PML.parser_at M' P ps' /\ PMCUR.wf_c ps' /\ PML.win_ok M' LBo ps' /\ PML.buf_bound ps' B /\ PML.ec_at M' E code /\ (code <> 0 -> PML.ps_more ps' = false) /\
       PML.ls_ok g' M' /\ (g' = g \/ (g' = PML.regJ g /\ code <> 0)) /\ CH2.den E1 (nth i G.BLS []) = PML.ps_blocks ps' /\
       ((code <> 0 \/ PML.ps_more ps' = false \/ PMS.win_exhausted ps') /\
        (PML.ps_st ps = PML.ST_ACCEPT -> code = 0 /\ PML.ps_more ps' = false /\ PML.ps_done ps' = true) /\
        (PMS.win_exhausted ps -> code = 0 -> PML.ps_more ps' = true -> In (PML.ps_st ps) [PML.ST_NUMBER; PML.ST_CR] /\ ~ In (PML.ps_st ps') [PML.ST_NUMBER; PML.ST_CR])) /\
       PMCUR.cur_post RSEGS ps ps' code M' V) ->
  CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 IL Hbase USER fx' E1 R1 M1 model1 E' R' M' HAt [HAmb HX] HFP Hag HLF _.
  pose proof (PSI.SPF I) as (S1 & S2 & S3 & S4 & S5 & S6). pose proof (PSI.iHentry I) as (Hra & Hraok & _).
  apply (PB.exit_ret L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred (PSI.STKF I) PSI.SCRP PSI.NF32 (PSI.U2 I) (PSI.W_OK I) (PSI.WRS_OK I) G.CPS G.TAGS K XI (PSI.DEF0 I) (PSI.KXf I) (PSI.BXf I)
           (PMS.PSOME_SCR PSI.SSCR) ltac:(rewrite PSI.SCRV; change (PMS.PSOME_SCR PSI.SSCR) with 10096; lia) ltac:(change (PMS.PSOME_SCR PSI.SSCR) with 10096; unfold hl_ceil; lia) S5 R (PSI.EV0 I) r Hra Hraok heap_ok3
           RETPC i c k ps1 _ ret_at IL Hbase fx' E1 R1 M1 model1 E' R' M' HAt HAmb Hag HLF).
  intros HRP HP HA' HagE'.
  destruct (USER E1 R1 E' R' M1 M' model1 HAt HAmb HX Hag HLF HA' HagE') as (ps' & code & g' & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Hden & Q9 & Q12).
  pose proof HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr & Hdf).
  unfold CH2.cur in HH1. rewrite Hden in HH1.
  apply (PSI.iHcont I fx' R' M' model1 (PML.ps_blocks ps' ++ LBo) cr1 LBo W HFP); [| exact HRP | exact HP | exact Hbv1 | exact HH1].
  exists ps', code, g'. repeat (split; [assumption|]). split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [apply (PSI.cred_of_blocks I i E1 cr1 ps' Hden); [destruct Q2 as ((_ & _ & _ & W4 & _) & _); exact W4 | exact HC1]|].
  split; [exact Q9 | exact Q12].
Qed.

Lemma ldelta_lview : forall i c ps1 pv lv pe ce d, PSM2.ldelta i c ps1 = Some (pv, lv, pe, ce, d) -> PSM2.lview i c ps1 = Some (pv, lv, pe, ce).
Proof. intros i c ps1 pv lv pe ce d H. unfold PSM2.ldelta in H. destruct (PSM2.lview i c ps1) as [[[[a b] c0] d0]|]; [|discriminate]. destruct (PSM2.mkdelta _ a b); [|discriminate]. injection H as -> -> -> -> _. reflexivity. Qed.
Lemma ecell0 : forall E' (M' : mem) cells, know_ok RSEGS E' M' cells -> env_agree GT.NF E0 E' -> PB.has cells (KWord (SA Eb 0) 4 (ELit 0)) = true -> L5.defined M' E 16 -> PML.ec_at M' E 0.
Proof.
  intros E' M' cells HK Hag Y1 HdE'. destruct (PSB.FRZ I E' Hag) as (_ & _ & G3 & _). pose proof (PSI.OBJR I) as (_ & _ & _ & _ & _ & O6 & O7). pose proof (PSI.SPF I) as (_ & S2 & _).
  split; [|split; [exact HdE' | left; reflexivity]].
  pose proof (PB2.kword32_elim E' M' _ _ E (PB.has_ok E' M' _ _ HK Y1)) as T. rewrite PB2.uv_lit in T by lia. apply T. unfold estart. cbn [a_base a_off]. fold (uv E' Eb). rewrite G3. lia.
Qed.
Lemma geu_chk_sound : forall E' (M' : mem) cells a b, know_ok RSEGS E' M' cells -> PSM3.geu_chk cells a b = true -> uv E' b <= uv E' a.
Proof.
  intros E' M' cells a b HK H. unfold PSM3.geu_chk in H. pose proof (PB.has_ok E' M' cells _ HK H) as X. cbn [kentry_ok edenot] in X. rewrite AX2S.u_sltu64 in X.
  unfold PB.uv. destruct (Z.ltb_spec (bv_unsigned (edenot E' a)) (bv_unsigned (edenot E' b))); lia.
Qed.

Lemma exits : forall i c k ps1, is_leaf i c k ps1 (CC.TOther RETPC) -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 IL. pose proof (CH2.leaves_all_sound _ _ _ exit_ok _ _ _ _ _ IL) as X. unfold PSM3.exit_chk in X. rewrite Z.eqb_refl in X. apply andb_prop in X as [Hbase X].
  apply (exit_gen i c k ps1 IL Hbase). intros E1 R1 E' R' M1 M' model1 HAt HA HX Hag HLF HA' HagE'.
  unfold PSI.XI in HX. destruct HX as (X1 & X2 & X3 & HX).
  pose proof (PSB.leaf_know I c ps1 E' R' M1 M' HLF) as HKc.
  pose proof (PSI.OBJR I) as (O1 & O2 & O3 & O4 & O5 & O6 & O7). pose proof (PSI.SPF I) as (_ & S2 & _ & S4 & _).
  assert (HdE' : L5.defined M' E 16) by (apply (PSB.amb_def I i E1 M' model1 E 16 HA'); [destruct (PSI.iHEC I) as (_ & Y & _); exact Y | lia]).
  pose proof (win_def i E1 M' model1 HA') as HWD.
  destruct (kind_of i) eqn:K1.
  -
    destruct (PSM2.ldelta i c ps1) as [[[[[pv lv] pe] ce] d]|] eqn:HLD; [|discriminate].
    rewrite (PSB.lview_vw _ _ _ _ _ _ _ (ldelta_lview _ _ _ _ _ _ _ _ HLD)) in HX. destruct HX as (bm & bd & stack & buf & HC & HS & HW & HB & HWS & HR & HE).
    destruct (PSB.leaf_state I i c k ps1 _ pv lv pe ce d E1 R1 E' R' M1 M' model1 bm bd stack buf IL HLD HAt HA Hag HLF HC)
      as (_ & HK & _ & L1 & L2 & L3 & L4 & L5 & L6 & L7 & (AG1 & AG2 & AG3) & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16 & HSB & FR2 & FRI & HPAX & Hden & HEQ).
    pose proof HC as (HC1 & HC2 & HC3 & HC4 & HC5 & HC6 & HC6b & HC7 & HC8 & HC9).
    apply andb_prop in X as [X XK]. apply andb_prop in X as [X Dclr]. apply andb_prop in X as [Dsst Dnst]. apply andb_prop in XK as [Y1 XK].
    destruct (PSM2.d_sst d) eqn:Es; [discriminate|]. destruct (PSM2.d_nst d) eqn:En; [discriminate|]. destruct (PSM2.d_clr d) eqn:Ec; [discriminate|]. cbn [PSB.newv] in *.
    set (psc := PSI.ps_of pv pe ce E1 bm bd stack buf) in *.
    assert (HLSg : PML.ls_ok g M') by exact (PSB.ls_frame M1 M' g FRI (PSI.iHG I) HS).
    assert (HEC0 : PML.ec_at M' E 0) by exact (ecell0 E' M' _ HKc HagE' Y1 HdE').
    assert (Hwl1 : PML.winlen psc = wend - uv E1 (PB4.pv_wptr pv)) by (unfold psc, PSI.ps_of; rewrite HC4; apply PSB.winlen_of; pose proof (PSI.WIN I) as (W0 & _); lia).
    pose proof (PSB.buf_need_range psc HW) as Hbn. destruct HB as [HB1 HB2]. unfold psc at 1, PSI.ps_of in HB1. cbn [PML.ps_buf] in HB1.
    pose proof (PSI.WIN I) as (W0 & W1 & _).
    apply orb_prop in XK as [XK|XK].
    +
      apply andb_prop in XK as [XK A4]. apply andb_prop in XK as [XK A3c]. apply andb_prop in XK as [XK A3b]. apply andb_prop in XK as [XK A3a]. apply andb_prop in XK as [A1 A2]. apply Z.eqb_eq in A4. rewrite A4, Z.add_0_r in L14.
      destruct (PSM2.d_st d) as [[s'| | | | | | |]|] eqn:Dst; try discriminate. destruct (PSM2.d_more d) as [dm|] eqn:Dm; [|discriminate]. destruct (PSM2.d_done d) as [dd|] eqn:Dd; [|discriminate].
      cbn [PSM3.is_lit PSM3.is_z] in A3a, A3b, A3c. apply Z.eqb_eq in A3a, A3b, A3c. subst s' dm dd. cbn [PSB.newv] in *.
      destruct (HPAX false true L11 L12) as (bufm & HPA & Hlen & _). rewrite (HEQ false true bufm) in HPA. rewrite L8, L9, L10, PB2.uv_lit in HPA by lia.
      assert (Hst2 : PML.ps_st psc = PML.ST_ACCEPT) by (unfold psc, PSI.ps_of; cbn [PML.ps_st]; rewrite <- AG1; exact (PSB.rng_is_sound E' M' _ _ 2 HKc A2)).
      assert (Hbmt : PML.ps_more psc = true).
      { unfold psc, PSI.ps_of. cbn [PML.ps_more]. apply PSB.b2z_inj1. rewrite <- HC8. apply Nat.eqb_eq in A1. subst i.

        assert (Hpm : PB4.pv_more pv = EVar 45) by (pose proof (PSB.lview_vw _ _ _ _ _ _ _ (ldelta_lview _ _ _ _ _ _ _ _ HLD)) as Q; vm_compute in Q; injection Q as <- _ _; reflexivity).
        rewrite Hpm. destruct HA as (_ & _ & HagE & _). destruct (PSB.FRZ I E1 HagE) as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & _). rewrite F9.
        pose proof (PSI.NUM I) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Nm & _). exact Nm. }
      set (w' := PB4.win_of (uv E' (PB4.pv_wptr lv)) wend) in *.
      exists (PSS.upd psc PML.ST_DONE (PML.ps_sst psc) (PML.ps_nst psc) false true (uv E1 ce) (uv E1 pe) bufm w'), 0, g.
      split; [exact HPA|]. split; [split; [apply PSS.wf_stop; [exact HW | exact (proj1 HW) | exact (proj1 (proj2 HW))] | apply PSSC.lvl_stop]|].
      split; [unfold PSS.upd, w'; apply win_ok_of; [exact HWD | lia]|].
      split; [split; [|exact HB2]; unfold PSS.upd, w'; cbn [PML.ps_buf]; rewrite PSB.winlen_of by lia; unfold PML.buf_need; cbn [PML.ps_more andb]; rewrite L13 in Hlen; lia|].
      split; [exact HEC0|]. split; [intros Q; exfalso; apply Q; reflexivity|]. split; [exact HLSg|]. split; [left; reflexivity|].
      split; [rewrite Hden; unfold PSS.upd, psc, PSI.ps_of, PML.ps_blocks; cbn [PML.ps_bptr PML.ps_bcap PML.ps_sb PML.ps_scap]; reflexivity|].
      split; [split; [right; left; reflexivity|]; split; [intros _; repeat split | intros _ _ Q; discriminate Q]|].

      split; [intros _ Q; discriminate Q|]. intros _ _. left. split; [reflexivity|]. split; [reflexivity|]. exact (ws_accept psc _ _ true _ _ bufm w' HW Hbmt Hst2).
    +
      apply andb_prop in XK as [XK A8]. apply andb_prop in XK as [XK A7]. apply andb_prop in XK as [XK A6]. apply andb_prop in XK as [XK A5]. apply andb_prop in XK as [XK A4]. apply andb_prop in XK as [XK A3].
      apply andb_prop in XK as [A1 A2]. apply negb_true_iff in A1. apply Nat.eqb_neq in A1. apply Z.eqb_eq in A6. rewrite A6, Z.add_0_r in L14.
      destruct (PSM2.d_st d) eqn:Dst; [discriminate|]. destruct (PSM2.d_more d) eqn:Dm; [discriminate|]. destruct (PSM2.d_done d) eqn:Dd; [discriminate|]. cbn [PSB.newv] in *.
      destruct (HPAX bm bd ltac:(rewrite L11; exact HC8) ltac:(rewrite L12; exact HC9)) as (bufm & HPA & Hlen & Hbuf). rewrite (HEQ bm bd bufm) in HPA. rewrite L8, L9, L10 in HPA.
      set (w' := PB4.win_of (uv E' (PB4.pv_wptr lv)) wend) in *.
      change (uv E1 (PB4.pv_st pv)) with (PML.ps_st psc) in HPA. change (uv E1 (PB4.pv_sst pv)) with (PML.ps_sst psc) in HPA. change (uv E1 (PB4.pv_nst pv)) with (PML.ps_nst psc) in HPA.
      change bm with (PML.ps_more psc) in HPA at 1.
      assert (Hbufeq : PML.ps_st psc = PML.ST_NUMBER -> PML.ps_more psc = true -> bufm = PML.ps_buf psc).
      { intros Hn _. apply orb_prop in A8 as [A8|A8]; [exact (Hbuf eq_refl Hn A8)|]. exfalso. destruct (PSM2.rng_of (SR.ps_cells ps1) (PB4.pv_st pv)) as [lo hi] eqn:Hrg.
        pose proof (PSB.rng_of_sound E' M' _ _ lo hi HKc Hrg) as Q. rewrite AG1 in Q. change (uv E1 (PB4.pv_st pv)) with (PML.ps_st psc) in Q. unfold PML.ST_NUMBER in Hn. lia. }
      exists (PSS.upd psc (PML.ps_st psc) (PML.ps_sst psc) (PML.ps_nst psc) (PML.ps_more psc) bd (uv E1 ce) (uv E1 pe) bufm w'), 0, g.
      split; [exact HPA|]. split; [split; [exact (wf_upd_same psc bd _ _ bufm w' HW Hbufeq) | exact (PSSC.lvl_same psc _ (proj1 (proj1 HWS)) eq_refl eq_refl eq_refl eq_refl)]|].
      split; [unfold PSS.upd, w'; apply win_ok_of; [exact HWD | lia]|].
      split; [split; [|exact HB2]; unfold PSS.upd at 1 2, w'; cbn [PML.ps_buf]; rewrite PSB.winlen_of by lia;
              replace (PML.buf_need (PSS.upd psc _ _ _ _ _ _ _ _ _)) with (PML.buf_need psc) by reflexivity; rewrite L13 in Hlen; lia|].
      split; [exact HEC0|]. split; [intros Q; exfalso; apply Q; reflexivity|]. split; [exact HLSg|]. split; [left; reflexivity|].
      split; [rewrite Hden; unfold PSS.upd, psc, PSI.ps_of, PML.ps_blocks; cbn [PML.ps_bptr PML.ps_bcap PML.ps_sb PML.ps_scap]; reflexivity|].
      split; [split|].
      { right. apply orb_prop in A7 as [A7|A7].
        - left. unfold PSS.upd, psc, PSI.ps_of. cbn [PML.ps_more]. pose proof (PSB.rng_is_sound E' M' _ _ 0 HKc A7) as Q. rewrite AG2, HC8 in Q. destruct bm; [discriminate Q | reflexivity].
        - right. pose proof (geu_chk_sound E' M' _ _ _ HKc A7) as Q. destruct (PSB.FRZ I E' HagE') as (_ & _ & _ & _ & _ & _ & F7 & _). rewrite F7 in Q.
          unfold PMS.win_exhausted, PSS.upd, w', PB4.win_of. cbn [PML.ps_win]. destruct (Z.eqb_spec wend 0); [exact Logic.I | lia]. }
      split; [intros Q; exfalso; exact (X2 A1 Q)|].
      { intros Hwx _ Hmt. pose proof (WEX Hwx) as Hw0. apply orb_prop in A2 as [A2|A2]; [pose proof (X3 A2); lia|]. apply Nat.eqb_eq in A2. exact (HE A2 Hw0 Hmt). }

      destruct HWS as ((HLVc & HCL) & HSO). split.
      { intros _ Hm'. unfold PSS.upd in Hm' |- *. cbn [PML.ps_more PML.ps_level] in Hm' |- *. exact (HCL Hm'). }
      intros _ Hm'. unfold PSS.upd in Hm'. cbn [PML.ps_more] in Hm'. destruct (HSO Hm') as [(T1 & T2 & T3)|(T1 & T2)].
      { left. unfold PSS.upd. cbn [PML.ps_done PML.ps_st]. split; [exact T2|]. split; [exact T3|]. exact (ws_upd_same psc bd _ _ bufm w' T1). }
      right. split.
      { apply (PSCC.wfc_sm_same_nn psc); [exact T1 | exact (PSCC.evp_not_num _ _ _ _ _ _ T2) | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity]. }
      destruct (PSB.bls2 _ _ _ _ _ _ _ _ IL (PSB.lview_vw _ _ _ _ _ _ _ (ldelta_lview _ _ _ _ _ _ _ _ HLD))) as (sbe & sce & HBL). destruct (PSB.leaf_nf _ _ _ _ _ IL) as (_ & _ & Hfoot).
      pose proof (PSB.frame_vis I i c E1 E' M1 M' model1 pe ce _ Hfoot HBL HA HagE' Hag (CC.lf_frame _ _ _ _ _ _ _ HLF)) as FV.
      apply (PSCC.evp_same _ _ _ _ _ psc); [apply (PSCC.evp_agV _ V M1 M'); [exact FV | lia | lia | exact T2] | reflexivity | reflexivity | reflexivity|].
      unfold PSS.upd, psc, PSI.ps_of. cbn [PML.ps_buf]. apply Nat2Z.inj. rewrite Hlen, L13. exact (eq_sym HC6).
  -
    destruct (PSM2.ldelta i c ps1) as [[[[[pv lv] pe] ce] d]|] eqn:HLD; [|discriminate].
    rewrite (PSB.lview_vw _ _ _ _ _ _ _ (ldelta_lview _ _ _ _ _ _ _ _ HLD)) in HX. destruct HX as (bm & bd & stack & buf & HC & HLS2 & HW & HB1 & HB2 & (code & HEC & Hcode) & HBM).
    destruct (PSB.leaf_state I i c k ps1 _ pv lv pe ce d E1 R1 E' R' M1 M' model1 bm bd stack buf IL HLD HAt HA Hag HLF HC)
      as (_ & HK & _ & L1 & L2 & L3 & L4 & L5 & L6 & L7 & (AG1 & AG2 & AG3) & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16 & HSB & FR2 & FRI & HPAX & Hden & HEQ).
    pose proof HC as (HC1 & HC2 & HC3 & HC4 & HC5 & HC6 & HC6b & HC7 & HC8 & HC9).
    apply andb_prop in X as [X XK]. apply andb_prop in X as [X Dclr]. apply andb_prop in X as [Dsst Dnst].
    destruct (PSM2.d_sst d) eqn:Es; [discriminate|]. destruct (PSM2.d_nst d) eqn:En; [discriminate|]. destruct (PSM2.d_clr d) eqn:Ec; [discriminate|]. cbn [PSB.newv] in *.
    set (psf := PSI.ps_of pv pe ce E1 false bd stack buf) in *.
    assert (Hi0 : i <> 0%nat) by (intros ->; vm_compute in K1; discriminate K1).
    assert (Hm0 : uv E' (PB4.pv_more lv) = PML.b2z false /\ PSM2.d_st d = None /\ PSM2.d_done d = None).
    { apply andb_prop in XK as [XK D3]. apply andb_prop in XK as [D1 D2]. destruct (PSM2.d_st d); [discriminate|]. destruct (PSM2.d_more d) eqn:Dm; [discriminate|]. destruct (PSM2.d_done d); [discriminate|].
      split; [|split; reflexivity]. rewrite L11. cbn [PSB.newv]. rewrite HC8, (HBM eq_refl). reflexivity. }
    destruct Hm0 as (Hm0 & Dst & Dd). rewrite Dst in L8. rewrite Dd in L12. cbn [PSB.newv] in *.
    destruct (HPAX false bd Hm0 ltac:(rewrite L12; exact HC9)) as (bufm & HPA & Hlen & _). rewrite (HEQ false bd bufm) in HPA. rewrite L8, L9, L10 in HPA.
    set (w' := PB4.win_of (uv E' (PB4.pv_wptr lv)) wend) in *. pose proof (PSI.WIN I) as (W0 & W1 & _).
    assert (Hwl1 : PML.winlen psf = wend - uv E1 (PB4.pv_wptr pv)) by (unfold psf, PSI.ps_of; rewrite HC4; apply PSB.winlen_of; lia).
    exists (PSS.upd psf (PML.ps_st psf) (PML.ps_sst psf) (PML.ps_nst psf) false bd (uv E1 ce) (uv E1 pe) bufm w'), code, (PML.regJ g).
    split; [exact HPA|]. split; [split; [exact (wf_upd_same psf bd _ _ bufm w' HW ltac:(intros _ Q; discriminate Q)) | intros Q; unfold PSS.upd in Q; cbn in Q; discriminate Q]|].
    split; [unfold PSS.upd, w'; apply win_ok_of; [exact HWD | lia]|].
    split; [split; [|exact HB2]; unfold PSS.upd, w'; cbn [PML.ps_buf]; rewrite PSB.winlen_of by lia; unfold PML.buf_need; cbn [PML.ps_more andb]; rewrite L13 in Hlen; lia|].
    destruct (PSB.bls2' _ _ _ _ _ IL) as (pe2 & ce2 & sbe & sce & HBL). destruct (PSB.leaf_nf _ _ _ _ _ IL) as (_ & _ & Hfoot).
    split; [apply (PSB.ec_frame I M1 M' code); [exact (PSB.frame_ec I i c E1 E' M1 M' model1 pe2 ce2 _ Hfoot HBL HA HagE' Hag (CC.lf_frame _ _ _ _ _ _ _ HLF)) | exact (CC.lf_grows _ _ _ _ _ _ _ HLF) | exact HEC]|].
    split; [intros _; reflexivity|]. split; [exact (PSB.ls_frame M1 M' (PML.regJ g) FRI (PSSC.regJ_nz g) HLS2)|]. split; [right; split; [reflexivity | lia]|].
    split; [rewrite Hden; unfold PSS.upd, psf, PSI.ps_of, PML.ps_blocks; cbn [PML.ps_bptr PML.ps_bcap PML.ps_sb PML.ps_scap]; reflexivity|].
    split; [split; [left; lia|]; split; [intros Q; exfalso; exact (X2 Hi0 Q) | intros _ Q; exfalso; lia]|]. split; [intros Q; exfalso; lia | intros Q; exfalso; lia].
  - destruct (PSM2.ldelta i c ps1) as [[[[[? ?] ?] ?] ?]|]; [rewrite Bool.andb_false_r in X|]; discriminate X.
  - destruct (PSM2.ldelta i c ps1) as [[[[[? ?] ?] ?] ?]|]; [rewrite Bool.andb_false_r in X|]; discriminate X.
  - destruct (PSM2.ldelta i c ps1) as [[[[[? ?] ?] ?] ?]|]; [rewrite Bool.andb_false_r in X|]; discriminate X.
  - destruct (PSM2.ldelta i c ps1) as [[[[[? ?] ?] ?] ?]|]; [rewrite Bool.andb_false_r in X|]; discriminate X.
  -
    destruct (PSM2.ldelta i c ps1) as [[[[[pv lv] pe] ce] d]|] eqn:HLD; [|discriminate].
    rewrite (PSB.lview_vw _ _ _ _ _ _ _ (ldelta_lview _ _ _ _ _ _ _ _ HLD)) in HX. destruct HX as (bm & bd & stack & buf & HC & HLS2 & HW & HB1 & HB2 & (code & HEC & Hcode) & HBM).
    destruct (PSB.leaf_state I i c k ps1 _ pv lv pe ce d E1 R1 E' R' M1 M' model1 bm bd stack buf IL HLD HAt HA Hag HLF HC)
      as (_ & HK & _ & L1 & L2 & L3 & L4 & L5 & L6 & L7 & (AG1 & AG2 & AG3) & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16 & HSB & FR2 & FRI & HPAX & Hden & HEQ).
    pose proof HC as (HC1 & HC2 & HC3 & HC4 & HC5 & HC6 & HC6b & HC7 & HC8 & HC9).
    apply andb_prop in X as [X XK]. apply andb_prop in X as [X Dclr]. apply andb_prop in X as [Dsst Dnst].
    destruct (PSM2.d_sst d) eqn:Es; [discriminate|]. destruct (PSM2.d_nst d) eqn:En; [discriminate|]. destruct (PSM2.d_clr d) eqn:Ec; [discriminate|]. cbn [PSB.newv] in *.
    set (psf := PSI.ps_of pv pe ce E1 false bd stack buf) in *.
    assert (Hi0 : i <> 0%nat) by (intros ->; vm_compute in K1; discriminate K1).
    assert (Hm0 : uv E' (PB4.pv_more lv) = PML.b2z false /\ PSM2.d_st d = None /\ PSM2.d_done d = None).
    { apply andb_prop in XK as [XK D3]. apply andb_prop in XK as [D1 D2]. destruct (PSM2.d_st d); [discriminate|]. destruct (PSM2.d_done d); [discriminate|].
      split; [|split; reflexivity]. rewrite L11. apply orb_prop in D2 as [D2|D2].
      - destruct (PSM2.d_more d) as [z|]; [|discriminate]. cbn [PSM3.is_z] in D2. apply Z.eqb_eq in D2. subst z. reflexivity.
      - apply andb_prop in D2 as [D2 D2b]. destruct (PSM2.d_more d); [discriminate|]. cbn [PSB.newv]. apply expr_eqb_eq in D2b. rewrite D2b. change (PML.b2z false) with 0. apply PB2.uv_lit. lia. }
    destruct Hm0 as (Hm0 & Dst & Dd). rewrite Dst in L8. rewrite Dd in L12. cbn [PSB.newv] in *.
    destruct (HPAX false bd Hm0 ltac:(rewrite L12; exact HC9)) as (bufm & HPA & Hlen & _). rewrite (HEQ false bd bufm) in HPA. rewrite L8, L9, L10 in HPA.
    set (w' := PB4.win_of (uv E' (PB4.pv_wptr lv)) wend) in *. pose proof (PSI.WIN I) as (W0 & W1 & _).
    assert (Hwl1 : PML.winlen psf = wend - uv E1 (PB4.pv_wptr pv)) by (unfold psf, PSI.ps_of; rewrite HC4; apply PSB.winlen_of; lia).
    exists (PSS.upd psf (PML.ps_st psf) (PML.ps_sst psf) (PML.ps_nst psf) false bd (uv E1 ce) (uv E1 pe) bufm w'), code, (PML.regJ g).
    split; [exact HPA|]. split; [split; [exact (wf_upd_same psf bd _ _ bufm w' HW ltac:(intros _ Q; discriminate Q)) | intros Q; unfold PSS.upd in Q; cbn in Q; discriminate Q]|].
    split; [unfold PSS.upd, w'; apply win_ok_of; [exact HWD | lia]|].
    split; [split; [|exact HB2]; unfold PSS.upd, w'; cbn [PML.ps_buf]; rewrite PSB.winlen_of by lia; unfold PML.buf_need; cbn [PML.ps_more andb]; rewrite L13 in Hlen; lia|].
    destruct (PSB.bls2' _ _ _ _ _ IL) as (pe2 & ce2 & sbe & sce & HBL). destruct (PSB.leaf_nf _ _ _ _ _ IL) as (_ & _ & Hfoot).
    split; [apply (PSB.ec_frame I M1 M' code); [exact (PSB.frame_ec I i c E1 E' M1 M' model1 pe2 ce2 _ Hfoot HBL HA HagE' Hag (CC.lf_frame _ _ _ _ _ _ _ HLF)) | exact (CC.lf_grows _ _ _ _ _ _ _ HLF) | exact HEC]|].
    split; [intros _; reflexivity|]. split; [exact (PSB.ls_frame M1 M' (PML.regJ g) FRI (PSSC.regJ_nz g) HLS2)|]. split; [right; split; [reflexivity | lia]|].
    split; [rewrite Hden; unfold PSS.upd, psf, PSI.ps_of, PML.ps_blocks; cbn [PML.ps_bptr PML.ps_bcap PML.ps_sb PML.ps_scap]; reflexivity|].
    split; [split; [left; lia|]; split; [intros Q; exfalso; exact (X2 Hi0 Q) | intros _ Q; exfalso; lia]|]. split; [intros Q; exfalso; lia | intros Q; exfalso; lia].
  -
    apply andb_prop in X as [X Xo200]. apply andb_prop in X as [X Hnx70]. apply andb_prop in X as [Xne Xcur]. apply Nat.leb_le in Hnx70.
    pose proof (PSB.nth_cut _ _ _ _ _ IL) as Hcut. unfold PSI.pt_post in HX. rewrite Hcut in HX. cbv zeta in HX.
    destruct HX as (ps2 & code & g' & cw & T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & _ & T11 & T12).
    assert (AGV : forall v, (v < CC.cp_nx c)%nat -> bv_unsigned (ev E' v) = bv_unsigned (ev E1 v)) by (intros v Hv; destruct Hag as [Hev _]; rewrite (Hev v Hv); reflexivity).
    assert (Hcode : code <> 0).
    { pose proof (PSB.ne_chk_sound E' M' _ _ 0 HKc Xne ltac:(lia)) as Q. unfold PB.uv in Q. cbn [edenot] in Q. unfold PSM3.nxg_of in Q. rewrite AGV in Q by (unfold APC.NCS; lia). rewrite T9 in Q. exact Q. }
    destruct (PSB.bls2' _ _ _ _ _ IL) as (pe2 & ce2 & sbe & sce & HBL). destruct (PSB.leaf_nf _ _ _ _ _ IL) as (_ & _ & Hfoot).
    destruct (PSB.own_blocks I i E1 M1 model1 pe2 ce2 sbe sce HA HBL) as ((C0 & C1 & C2 & C3 & C4) & (D0 & D1 & D2 & D3 & D4) & _).
    rewrite HBL, !PB.den_cons in T10. change (CH2.den E1 []) with (@nil (Z * Z)) in T10. unfold PML.ps_blocks in T10. injection T10 as Eb1 Eb2 Eb3 Eb4.
    pose proof (PSB.CEIL I) as CL. destruct (PSB.FRZ I E' HagE') as (F1 & _ & _ & F4 & _).
    assert (GR : mem_grows M1 M') by exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
    assert (HWK : PML.win_ok M' LBo ps2) by exact (PB2.win_ok_fr M1 M' GR LBo ps2 T3).
    assert (ST : estart E' (SA (EVar 2) (-10096)) = sp - 10096) by (unfold estart; cbn [a_base a_off]; fold (uv E' (EVar 2)); rewrite F4; lia).
    assert (PT : forall o, estart E' (SA Pb o) = P + o) by (intros o; unfold estart; cbn [a_base a_off]; fold (uv E' Pb); rewrite F1; reflexivity).
    pose proof (PSI.iAP2 I) as AP2. unfold PML.apart in AP2.
    assert (Hi0 : i <> 0%nat) by (intros ->; vm_compute in K1; discriminate K1).
    assert (FIN : PML.parser_at M' P ps2 -> PML.ec_at M' E code -> PML.ls_ok g' M' ->
                  exists (ps' : PML.pstate) (code0 : Z) (g0 : PML.ls_state),
                    PML.parser_at M' P ps' /\ PMCUR.wf_c ps' /\ PML.win_ok M' LBo ps' /\ PML.buf_bound ps' B /\ PML.ec_at M' E code0 /\ (code0 <> 0 -> PML.ps_more ps' = false) /\
                    PML.ls_ok g0 M' /\ (g0 = g \/ (g0 = PML.regJ g /\ code0 <> 0)) /\ CH2.den E1 (nth i G.BLS []) = PML.ps_blocks ps' /\
                    ((code0 <> 0 \/ PML.ps_more ps' = false \/ PMS.win_exhausted ps') /\ (PML.ps_st ps = PML.ST_ACCEPT -> code0 = 0 /\ PML.ps_more ps' = false /\ PML.ps_done ps' = true) /\
                     (PMS.win_exhausted ps -> code0 = 0 -> PML.ps_more ps' = true -> In (PML.ps_st ps) [PML.ST_NUMBER; PML.ST_CR] /\ ~ In (PML.ps_st ps') [PML.ST_NUMBER; PML.ST_CR])) /\
                    PMCUR.cur_post RSEGS ps ps' code0 M' V).
    { intros Q1 Q2 Q3. exists ps2, code, g'. split; [exact Q1|]. split; [split; [exact T2 | intros Q; rewrite (T6 Hcode) in Q; discriminate Q]|].
      repeat (split; [assumption|]).
      split; [rewrite HBL, !PB.den_cons; change (CH2.den E1 []) with (@nil (Z * Z)); unfold PML.ps_blocks; rewrite Eb1, Eb2, Eb3, Eb4; reflexivity|].
      split; [split; [left; exact Hcode|]; split; [intros Q; exfalso; exact (X2 Hi0 Q) | intros _ Q; exfalso; exact (Hcode Q)]|].
      split; [intros Q; exfalso; exact (Hcode Q) | intros Q; exfalso; exact (Hcode Q)]. }
    assert (Hg' : g' <> PML.LS0) by (destruct T8 as [->|[-> _]]; [exact (PSI.iHG I) | apply PSSC.regJ_nz]).
    unfold PSM2.cur_cut in T11, Xcur. rewrite Hcut in T11, Xcur. unfold PSM2.foot_all in Hfoot. apply andb_prop in Hfoot as [Hfoot _]. unfold PSM2.foot_chk in Hfoot.
    destruct (CC.cp_F c) as [|r0 [|[[b1 o1] n1] [|]]] eqn:HF; try discriminate.
    +
      apply PSB.reg_eqb_eq in Hfoot. subst r0. subst cw.
      set (F := [(sp - 10096, 10096)] : list L5.range).
      assert (FR : L5.frame_but F M1 M').
      { intros x Hx. apply (CC.lf_frame _ _ _ _ _ _ _ HLF). unfold SGP.outside. rewrite HF. constructor; [|constructor]. unfold PSM2.STKREG. cbv beta iota. rewrite ST. unfold elenZ. cbn [edenot]. rewrite u64_of_Z by lia.
        pose proof (Hx (sp - 10096, 10096) ltac:(left; reflexivity)) as Q. unfold L5.in_rng in Q. cbn [fst snd] in Q. lia. }
      assert (OUTLO : forall a n, 0 <= a -> a + n <= sp - 10096 -> PB2.out F a n).
      { intros a n A0 A1. split; [lia|]. split; [lia|]. intros q Hq rg [<-|[]]; unfold L5.in_rng; cbn [fst snd]; lia. }
      assert (OUTHI : forall a n, sp <= a -> a + n <= 2 ^ 47 -> PB2.out F a n).
      { intros a n A0 A1. split; [lia|]. split; [lia|]. intros q Hq rg [<-|[]]; unfold L5.in_rng; cbn [fst snd]; lia. }
      apply FIN.
      * replace (PML.ps_set_win ps2 (PML.ps_win ps2)) with ps2 in T1 by (destruct ps2; reflexivity).
        apply (PB2.parser_at_fr F M1 M' FR GR P ps2); [apply OUTHI; lia | apply OUTLO; unfold hl_ceil in *; lia | apply OUTLO; unfold hl_ceil in *; lia | exact T1].
      * apply (PB2.ec_at_fr F M1 M' FR GR E code); [apply OUTHI; lia | exact T5].
      * apply (PB2.ls_ok_fr F M1 M' FR g' Hg'); [apply OUTLO; lia | exact T7].
    +
      apply andb_prop in Hfoot as [Hfoot H3]. apply andb_prop in Hfoot as [H1 H2]. apply PSB.reg_eqb_eq in H1. apply expr_eqb_eq in H2. subst r0 b1.
      apply orb_prop in H3 as [H3|H3]; apply andb_prop in H3 as [H3 H4]; apply Z.eqb_eq in H3; apply expr_eqb_eq in H4; subst o1 n1;
        [|discriminate Xo200].
      destruct T11 as (p0 & e0 & -> & Hw2 & Hp0).
      set (F := [(sp - 10096, 10096); (P + 200, 8)] : list L5.range).
      assert (FR : L5.frame_but F M1 M').
      { intros x Hx. apply (CC.lf_frame _ _ _ _ _ _ _ HLF). unfold SGP.outside. rewrite HF. constructor; [|constructor; [|constructor]]; unfold PSM2.STKREG; cbv beta iota.
        - rewrite ST. unfold elenZ. cbn [edenot]. rewrite u64_of_Z by lia. pose proof (Hx (sp - 10096, 10096) ltac:(left; reflexivity)) as Q. unfold L5.in_rng in Q. cbn [fst snd] in Q. lia.
        - rewrite PT. unfold elenZ. cbn [edenot]. rewrite u64_of_Z by lia. pose proof (Hx (P + 200, 8) ltac:(right; left; reflexivity)) as Q. unfold L5.in_rng in Q. cbn [fst snd] in Q. lia. }
      assert (OUTLO : forall a n, 0 <= a -> a + n <= sp - 10096 -> PB2.out F a n).
      { intros a n A0 A1. split; [lia|]. split; [lia|]. intros q Hq rg [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; lia. }
      assert (OUTHI : forall a n, sp <= a -> a + n <= 2 ^ 47 -> (a + n <= P + 200 \/ P + 208 <= a) -> PB2.out F a n).
      { intros a n A0 A1 A2. split; [lia|]. split; [lia|]. intros q Hq rg [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; lia. }
      apply FIN.
      * replace ps2 with (PML.ps_set_win ps2 (Some (bv_unsigned (ev E1 (CC.cp_nx c - APC.NCS + 4)), e0))) by (destruct ps2; cbn [PML.ps_win] in Hw2; cbn [PML.ps_set_win]; rewrite Hw2; reflexivity).
        apply (pa_fr_cur F M1 M' FR GR P ps2 p0 e0); [apply OUTHI; lia | apply OUTHI; lia | apply OUTLO; unfold hl_ceil in *; lia | apply OUTLO; unfold hl_ceil in *; lia | exact T1 | | lia].
        pose proof (PB2.kword64_elim E' M' _ _ (P + 200) (PB.has_ok E' M' _ _ HKc Xcur) (PT 200)) as Q. unfold PB.uv in Q. cbn [edenot] in Q. unfold PSM3.a0v_of in Q.
        rewrite AGV in Q by (unfold APC.NCS; lia). exact Q.
      * apply (PB2.ec_at_fr F M1 M' FR GR E code); [apply OUTHI; lia | exact T5].
      * apply (PB2.ls_ok_fr F M1 M' FR g' Hg'); [apply OUTLO; lia | exact T7].
  -
    destruct (PSM2.ldelta i c ps1) as [[[[[? ?] ?] ?] ?]|]; [rewrite Bool.andb_false_r in X|]; discriminate X.
Qed.

Lemma handledb_true : forall x, PML.handled x -> PSM2.handledb x = true.
Proof. intros x H. unfold PML.handled in H. unfold PSM2.handledb. lia. Qed.
Lemma dead : forall i c k ps1, is_leaf i c k ps1 (CC.TOther DEADPC) -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 IL fx' E1 R1 M1 model1 E' R' M' HAt [HA HX] HFP Hag HLF _. exfalso.
  pose proof (CH2.leaves_all_sound _ _ _ dead_ok _ _ _ _ _ IL) as X. unfold PSM3.dead_chk in X. rewrite Z.eqb_refl in X.
  destruct (kind_of i) eqn:K1; try discriminate. destruct (PSM2.ldelta i c ps1) as [[[[[pv lv] pe] ce] d]|] eqn:HLD; [|discriminate].
  destruct (PSM2.rng_of (SR.ps_cells ps1) (PB4.pv_st pv)) as [lo hi] eqn:Hrg. apply andb_prop in X as [X XS]. apply andb_prop in X as [Xm Xhi]. apply Z.leb_le in Xhi.
  unfold PSI.XI in HX. destruct HX as (_ & _ & _ & HX). rewrite K1, (PSB.lview_vw _ _ _ _ _ _ _ (ldelta_lview _ _ _ _ _ _ _ _ HLD)) in HX.
  destruct HX as (bm & bd & stack & buf & HC & _ & HW & _).
  destruct (PSB.leaf_state I i c k ps1 _ pv lv pe ce d E1 R1 E' R' M1 M' model1 bm bd stack buf IL HLD HAt HA Hag HLF HC) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (AG1 & AG2 & _) & _).
  pose proof (PSB.leaf_know I c ps1 E' R' M1 M' HLF) as HKc.
  destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & HC8 & _).
  pose proof (PSB.rng_is_sound E' M' _ _ 1 HKc Xm) as Q. rewrite AG2, HC8 in Q. apply PSB.b2z_inj1 in Q. subst bm.
  destruct HW as (_ & _ & _ & _ & (C & T & _ & _ & W7)). destruct (W7 eq_refl) as (_ & _ & Hh & _). unfold PSI.ps_of in Hh. cbn [PML.ps_st] in Hh.
  pose proof (PSB.rng_of_sound E' M' _ _ lo hi HKc Hrg) as Hr. rewrite AG1 in Hr. apply handledb_true in Hh. set (st := uv E1 (PB4.pv_st pv)) in *.
  apply orb_prop in XS as [XS|XS].
  - rewrite forallb_forall in XS. specialize (XS st (PSB.zseq_in lo hi st Hr)). rewrite Hh in XS. discriminate XS.
  - apply andb_prop in XS as [XF XS]. rewrite forallb_forall in XS. specialize (XS st (PSB.zseq_in lo hi st Hr)). rewrite Hh in XS. cbn [negb orb] in XS.
    pose proof (PB.has_ok E' M' _ _ HKc XF) as Y. cbn [kentry_ok edenot] in Y. rewrite AX2S.u_sltu64 in Y. rewrite u64_of_Z in Y by lia.
    fold (uv E' (APC.eaddz (PB4.pv_st pv) (-1))) in Y. rewrite PB.uv_eaddz, AG1 in Y. fold st in Y. rewrite Z.mod_small in Y by lia.
    destruct (Z.ltb_spec 27 (st + -1)); lia.
Qed.
End C.
End PSX.
