(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S07 (route add, B 0x8d2e8) of the walk of verbs_receive on the
   ASan+UBSan build of plugin-hostd/fuzz_command (lib/B/Prog/verbs_receive_iface.v, vr_s07_stmt): the add tail
   B 0x8d454-0x8d480: the two UBSan checks `li a0,-9; bltu a0,s3, 0x8d938` and `li a0,-17; bltu a0,s3, 0x8d938`
   (0x8d458, 0x8d460; refuted: s3 = tok = F+32 and F+1024 <= alloc_ceiling), `ld s11,8(s3); ld a0,16(s3);
   jal atoi` (a Theorem Labs lane's aatoi_realizes on tok[2], through art07), then `mv a1,a0; mv a0,s11; mv a2,s10; mv a3,s9;
   jal sup_add` (sup_add(tok[1], atoi(tok[2]), placement, client), PaFx.cl_callS_wideF through call07F), and the
   tail after it (verbs_receive_s07f.v legT2) at the FP state sup_add returned at. The B twin of
   lib/A/Prog/verbs_receive_s07g.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI00 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtNumber.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
descriptors_add_c sup_add_c sup_reply_code_c answer_c hand_back_c record_c arg_s_c xmalloc_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
verbs_receive_s07a verbs_receive_s07b verbs_receive_s07c verbs_receive_s07e verbs_receive_s07f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Module PV := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.Verbs.

(* a placement or client argument: NULL, or the word j of the copy *)
Definition otok07 (tp : list Z) (tks : list (list byte)) (p : Z) (o : option (list byte)) : Prop :=
(o = None /\ p = 0) \/ (exists j w, o = Some w /\ nth_error tp j = Some p /\ nth_error tks j = Some w).

Lemma darg_le07 : forall o, (forall w, o = Some w -> Z.of_nat (length w) <= 8192) ->
Z.of_nat (length (darg o (bstr "-"%string))) <= 8192.
Proof.
intros [w|] H; cbn [darg]; [exact (H w eq_refl)|]. change (length (bstr "-"%string)) with 1%nat. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis TSUP_ADD : tsup_add_spec B MT.
Hypothesis TSUP_REPLY_CODE : forall fx0 : YK11.FPState, @tsup_reply_code_spec fx0 rc SK PI B MT.
Hypothesis TDESCRIPTORS_ADD : forall fx0 : YK11.FPState, @tdescriptors_add_spec fx0 rc SK PI B MT.
Hypothesis AATOI : RtNumber.aatoi_realizes SEGS B (SIGMA CS___interceptor_trampoline_atoi) 0xae455 0xa6bf8 0x604158.
Hypothesis HB : YF0m.CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis BLKT : vr_blktail B.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let C07C := c07_call B MT TL ROA RECC RRO PROGU RPG.
Let RUN07 := run07 B MT TL ROA RRO RECC PROGU.
Let CALL07F := call07F B MT HB PROGU.
Let ART07 := art07 B MT TL ROA RRO RECC PROGU.
Let BR := paj_branch (L := cmd_listing) (PI := PI).
(* the add tail after sup_add (verbs_receive_s07f.v), at the FP state sup_add returned at *)
Let LEGT2 (fx0 : YK11.FPState) :=
  legT2 (fx := fx0) B MT (TSUP_REPLY_CODE fx0) (TDESCRIPTORS_ADD fx0) HB TL MTL SIGP BLKT ROA RRO RPG RECC PROGU.

Lemma rec_code_range07 : forall ly S rd R O, rec_repA B ly S rd R O -> -2 ^ 31 <= r_code R < 2 ^ 31.
Proof. intros ly S rd R O (Q & (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & HC & _) & _) & _). exact HC. Qed.

(* the facts sup_add asks of a placement or client argument, from the copy block *)
Lemma oarg07 : forall e F c tp lyc Sc Wc memc mdc Rc Oc tmps regs p o,
AR SEGS B lyc Sc Wc memc mdc -> vr_copy B e F c tp Wc memc ->
rec_repA B lyc Sc (rdW Wc memc) Rc Oc -> In (vr_cb e c) tmps ->
Permutation (ablocks B lyc Sc) (Oc ++ tmps ++ e_rest e) ->
alloc_ceiling <= spZ regs - 3 * ESTACK ->
otok07 tp (Verbs.toks (e_D e)) p o ->
astr_argA B lyc Sc (rdW Wc memc) (in_roP SEGS RLO RHI) Oc p o /\
(forall x, o = Some x -> atail_vis SEGS Wc memc (p + Z.of_nat (length x))) /\
0 <= p < 2 ^ 64 /\ (forall w, o = Some w -> Z.of_nat (length w) <= 8192).
Proof.
intros e F c tp lyc Sc Wc memc mdc Rc Oc tmps regs p o HAR Hcopy Hrec Hcbin Hperm Hsp Ho.
assert (Hcbin' : In (vr_cb e c) (ablocks B lyc Sc))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; apply in_or_app; left; exact Hcbin).
assert (Hcbno : ~ In (vr_cb e c) Oc) by exact (perm_tmp_notin B _ _ _ _ _ _ _ _ _ HAR Hperm Hcbin).
destruct Ho as [(-> & ->) | (j & w & -> & Hj & Hw)].
- split; [reflexivity|]. split; [intros x Hx; discriminate|]. split; [lia | intros w Hw; discriminate].
- destruct (tok_blk07 B e F c tp lyc Sc Wc memc mdc Rc Oc tmps j p w HAR Hcopy Hrec Hcbin Hperm Hj Hw)
    as (_ & _ & _ & _ & Hp4 & Hp64 & Hw8).
  destruct (tok_rt B BLKT e F c tp lyc Sc Wc memc mdc regs (3 * ESTACK) j p w HAR Hcopy Hcbin' Hj Hw Hsp) as (_ & _ & Htl).
  split; [exact (tok_argA B e F c tp lyc Sc Wc memc mdc Rc Oc tmps j p w HAR Hcopy Hrec Hcbin Hcbno Hperm Hj Hw)|].
  split; [intros x Hx; injection Hx as <-; exact Htl|]. split; [lia|]. intros w' Hw'. injection Hw' as <-. exact Hw8.
Qed.

Lemma legT : forall e W pos F q c tp lyc Sc regsc memc mdc k nm u wi rest pl cl pp cp,
vr_ent B MT e ->
PV.toks (e_D e) = PV.Lit.verb_add :: u :: wi :: rest ->
PV.add_m atoi_a (u :: wi :: rest) = PV.SAdd u (atoi_a wi) pl cl ->
otok07 tp (PV.toks (e_D e)) pp pl -> otok07 tp (PV.toks (e_D e)) cp cl ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
  [(18, q); (19, F + 32); (22, F); (25, cp); (26, pp)]
  (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
vr_line B e q W memc -> vr_copy B e F c tp W memc ->
SRr SEGS W (cfg_at SEGS (vr_pc 0x8d454) regsc memc mdc) (hdF07 B MT 0x8d4d0 e).
Proof.
intros e W pos F q c tp lyc Sc regsc memc mdc k nm u wi rest pl cl pp cp Hent Htk Hadd Hpl Hcl Hcore Hline Hcopy.
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & _ & HDn & _).
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcalls & _).
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlive0 & _).
pose proof Hcore as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & Hdat & Hperm & Hq).
pose proof (core_regs07 B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore)
  as (R2 & R3 & R4 & R8 & R9 & Hspz & Hs0 & Ho16 & Hs1 & Hceil & H47).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof vr_stk_ge as [Hstk4 Hstk5].
pose proof (proj1 HJ) as HAR.
pose proof Hcopy as (_ & (_ & Hlen & _ & _)).
rewrite Htk in Hlen. cbn [length] in Hlen.
destruct tp as [|t0 [|pu [|pw tp']]]; cbn [length] in Hlen; try lia.
assert (Hpu : nth_error (t0 :: pu :: pw :: tp') 1 = Some pu) by reflexivity.
assert (Hpw : nth_error (t0 :: pu :: pw :: tp') 2 = Some pw) by reflexivity.
assert (Hu : nth_error (PV.toks (e_D e)) 1 = Some u) by (rewrite Htk; reflexivity).
assert (Hwi : nth_error (PV.toks (e_D e)) 2 = Some wi) by (rewrite Htk; reflexivity).
assert (Hcb : In (vr_cb e c) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. apply in_or_app. left. right. left. reflexivity. }
pose proof (HF_bounds07 B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore) as HFb.
destruct (sup_add_m (e_R e) (Some u) (atoi_a wi) pl cl) as [R1 t] eqn:Hsa.
assert (EK : vr_k1 (e_R e) (e_D e) = 2 + (EV_SUP_ADD (e_R e) + EV_SUP_REPLY_CODE + EV_DESCRIPTORS_ADD R1)).
{ unfold vr_k1. rewrite (evr_add _ _ _ Htk), Hadd. cbn [ev_step]. rewrite Hsa. reflexivity. }
pose proof (EVd_nn07 R1) as HEVd.
assert (Hsf0 : rec_spill_frees (e_R e) = 0) by (unfold rec_spill_frees; rewrite Hcalls; reflexivity).
pose proof (atoi_range07 wi) as Hid.
pose proof (rec_code_range07 _ _ _ _ _ Hrec) as HC.
pose proof (add_text07 (e_R e) u (atoi_a wi) pl cl HC Hid) as Htl. rewrite Hsa in Htl. cbn [snd] in Htl.
assert (R19 : getr regsc (Z_to_bv 5 19) = w64 (F + 32)) by (apply (rv_get07 regsc _ 19 _ Hrv); cbn; tauto).
(* 0x8d454: li a0,-9; bltu a0,s3 (UBSan: tok + 8 overflows) *)
pose proof (seed_core B MT e pos F q c (t0 :: pu :: pw :: tp') _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 28452 [pu; pw]
  Hcore Hcopy ltac:(left; reflexivity) ltac:(right; left; reflexivity) R19
  ltac:(intros [|[|i]] p0 Hi; cbn in Hi |- *; [exact Hi | exact Hi | destruct i; discriminate])
  ltac:(cbn; lia)) as HS.
remember (E07 regsc (shadow_addr F + 4) F [pu; pw]) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply E07_env).
pose proof (env_agree07 regsc (shadow_addr F + 4) F [pu; pw]) as HAE. rewrite <- HE in HAE.
assert (X34 : ew E 34 = Z_to_bv 64 pu) by (rewrite HE; apply (E07_ext _ _ _ _ 2); [lia | reflexivity]).
assert (X35 : ew E 35 = Z_to_bv 64 pw) by (rewrite HE; apply (E07_ext _ _ _ _ 3); [lia | reflexivity]).
assert (EE19 : ew E 19 = Z_to_bv 64 (F + 32)) by (rewrite HE, (E07_reg _ _ _ _ 19 (Z_to_bv 5 19) eq_refl); exact R19).
clear HE.
unfold cfg_at, vr_pc, w64.
replace (BASE + (AF_verbs_receive + (0x8d454 - 0x8ce4c))) with (BASE + 28452) by (unfold AF_verbs_receive; lia).
paj_run_sh RUNP HS HJ.
{ awr07. }
mdv_set.
assert (V : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W memc a)
  by (intros a Ha; exact (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha)).
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
{ exfalso. pose proof HFb as [HFlo0 HFhi0]. pose proof asan_consts as (CC0 & _).
  rewrite branch_ltu_U, (U_atom E 19 _ EE19) in Hc by lia.
  match type of Hc with context [U E (SLit ?z)] =>
    replace (U E (SLit z)) with (2 ^ 64 - 9) in Hc by (vm_compute; reflexivity) end.
  apply Z.ltb_lt in Hc. lia. }
clear Hc.
(* 0x8d45c: li a0,-17; bltu a0,s3 (UBSan: tok + 16 overflows) *)
paj_run_sh RUNP HS HJ.
{ awr07. }
mdv_set.
assert (V' : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms0) a = rdW W memc a).
{ intros a Ha. rewrite (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha). exact (V a Ha). }
clear HF HFr HG V. rename V' into V.
psrr_branch_pi RUNP BR HS.
{ exfalso. pose proof HFb as [HFlo0 HFhi0]. pose proof asan_consts as (CC0 & _).
  rewrite branch_ltu_U, (U_atom E 19 _ EE19) in Hc by lia.
  match type of Hc with context [U E (SLit ?z)] =>
    replace (U E (SLit z)) with (2 ^ 64 - 17) in Hc by (vm_compute; reflexivity) end.
  apply Z.ltb_lt in Hc. lia. }
clear Hc.
(* 0x8d464: ld s11,8(s3); ld a0,16(s3); jal wrapper_atoi *)
paj_run_shc RUNP RUNC HS HJ.
{ awr07. }
mdv_set.
assert (V' : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms1) a = rdW W memc a).
{ intros a Ha. rewrite (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha). exact (V a Ha). }
clear HF HFr HG V. rename V' into V.
prreg HS (Z_to_bv 5 1) Q1. prreg HS (Z_to_bv 5 10) Q10. prreg HS (Z_to_bv 5 27) Q27.
rewrite X35 in Q10. rewrite X34 in Q27.
pose proof (kept_regs07 E _ _ regsc _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26] HS HAE
  ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
pmkst HS.
set (rl1 := [(18, q); (19, F + 32); (22, F); (25, cp); (26, pp); (27, pu)]).
assert (Hcs1 : cs07 rl1) by (unfold cs07, rl1; cs07_tac).
assert (Hrv1 : vr_rv (ms_regs ms1) (vr_base B e ++ rl1)).
{ rv07 Hrv KR regsc. }
destruct (RUN07 e pos F q c _ _ _ _ _ _ _ _ _ _ _ _ _ W regsc (ms_regs ms1) memc (ms_mem ms1) mdc mdv1
  Hcore Hline Hcopy HJ V Hrv1 ltac:(left; reflexivity) ltac:(right; left; reflexivity) HDn) as (Hc1 & Hl1 & Hcp1).
pose proof Hc1 as (HJ1 & Hk1 & Hmet1 & Hnm1 & Hfr1 & Hrv1' & Hsv1 & Hsp1 & Henv1 & Hrec1 & Hdat1 & Hperm1 & Hq1).
pose proof (proj1 HJ1) as HAR1.
destruct Henv1 as (HRO1 & _ & HROk1 & Hgd1 & Hfl1 & (ev & Herr1)).
pose proof (core_regs07 B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc1) as (_ & _ & _ & _ & _ & Hspz1 & _).
assert (Hsp3 : alloc_ceiling <= spZ (ms_regs ms1) - 3 * ESTACK) by (rewrite Hspz1; unfold ESTACK in *; lia).
destruct (tok_rt B BLKT e F c _ lyc Sc W (ms_mem ms1) mdv1 (ms_regs ms1) (3 * ESTACK) 2 pw wi HAR1 Hcp1 Hcb Hpw Hwi Hsp3)
  as (STR & RD & TAIL).
destruct (tok_blk07 B e F c _ lyc Sc W (ms_mem ms1) mdv1 (e_R e) (e_O e) [vr_lb e q; vr_cb e c] 2 pw wi HAR1 Hcp1 Hrec1
  ltac:(right; left; reflexivity) Hperm1 Hpw Hwi) as (Hblk & _ & _ & _ & Hpw4 & Hpw64 & _).
eapply (ART07 e pos F q c _ _ _ _ _ _ _ _ _ _ lyc Sc W (ms_regs ms1) (ms_mem ms1) mdv1 (3 * ESTACK) (aerrno_cell B) _ _
  (SIGMA CS___interceptor_trampoline_atoi) _ Hc1 Hl1 Hcp1 ltac:(left; reflexivity) ltac:(right; left; reflexivity) HDn Hcs1 Q1).
- lia.
- reflexivity.
- unfold ESTACK. lia.
- intros a Ha. exact Ha.
- intros HPRE. refine (AATOI lyc Sc W (ms_regs ms1) (ms_mem ms1) mdv1 pw wi ev Hfl1 Hgd1 HPRE Q10 ltac:(lia) STR RD
    (amem8_of_blockA SEGS B LAWS lyc Sc W (ms_mem ms1) mdv1 pw (astr_len wi) HAR1 Hblk ltac:(unfold astr_len; lia)) TAIL Herr1
    _ (vr_rtrom_ok B W (ms_mem ms1) HRO1)).
  (* tok[2] apart from the errno cell: its bytes are in a live block, not image bytes (blk_img); the errno cell's are
     (api_env) *)
  pose proof (pal_env B TL) as (_ & Hzi & _).
  destruct Hblk as (pz & kz & Hzin & Hza & Hzb).
  destruct (Z_le_gt_dec (pw + astr_len wi + 1) (as_errno B)) as [Hz1|Hz1]; [left; exact Hz1|].
  destruct (Z_le_gt_dec (as_errno B + 4) pw) as [Hz2|Hz2]; [right; exact Hz2|]. exfalso.
  apply (blk_img SEGS B LAWS lyc Sc W (ms_mem ms1) mdv1 pz kz (Z.max pw (as_errno B)) HAR1 Hzin);
    [| apply Hzi; clear - Hz1 Hz2; lia].
  unfold req_size. destruct (Z.eqb_spec kz 0) as [Hzk|Hzk]; cbv iota; clear - Hza Hzb Hz1 Hzk; unfold astr_len in *; lia.
- (* after atoi, 0x8d470: mv a1,a0; mv a0,s11; mv a2,s10; mv a3,s9; jal sup_add *)
  intros regs2 mem2 md2 Hc2 Hl2 Hcp2 (HA0 & _) HP2.
  assert (HA0' : getr regs2 (Z_to_bv 5 10) = w64 (atoi_a wi)) by exact HA0.
  pose proof Hc2 as (HJ2 & Hk2 & Hmet2 & Hnm2 & Hfr2 & Hrv2 & Hsv2 & Hsp2 & Henv2 & Hrec2 & Hdat2 & Hperm2 & Hq2).
  assert (R19b : getr regs2 (Z_to_bv 5 19) = w64 (F + 32)) by (apply (rv_get07 regs2 _ 19 _ Hrv2); unfold rl1; cbn; tauto).
  pose proof (seed_core B MT e pos F q c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 28480 []
    Hc2 Hcp2 ltac:(left; reflexivity) ltac:(right; left; reflexivity) R19b
    ltac:(intros [|i] p0 Hi; discriminate) ltac:(cbn; lia)) as HS2.
  remember (E07 regs2 (shadow_addr F + 4) F []) as E2 eqn:HE2.
  assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply E07_env).
  pose proof (env_agree07 regs2 (shadow_addr F + 4) F []) as HAE2. rewrite <- HE2 in HAE2.
  assert (EE : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E2 nn = getr regs2 rr)
    by (intros nn rr Hnn; rewrite HE2; apply E07_reg; exact Hnn).
  clear HE2.
  paj_run_shc RUNP RUNC HS2 HJ2.
  { awr07. }
  mdv_set.
  assert (V2 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms2) a = rdW W mem2 a)
    by (intros a Ha; exact (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha)).
  clear HF HFr HG.
  prreg HS2 (Z_to_bv 5 1) Q1b. prreg HS2 (Z_to_bv 5 10) Q10b. prreg HS2 (Z_to_bv 5 11) Q11b.
  prreg HS2 (Z_to_bv 5 12) Q12b. prreg HS2 (Z_to_bv 5 13) Q13b.
  rewrite (EE 27%nat (Z_to_bv 5 27) eq_refl) in Q10b. rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl) in Q11b.
  rewrite (EE 26%nat (Z_to_bv 5 26) eq_refl) in Q12b. rewrite (EE 25%nat (Z_to_bv 5 25) eq_refl) in Q13b.
  rewrite (rv_get07 regs2 _ 27 pu Hrv2 ltac:(unfold rl1; cbn; tauto)) in Q10b.
  rewrite HA0' in Q11b.
  rewrite (rv_get07 regs2 _ 26 pp Hrv2 ltac:(unfold rl1; cbn; tauto)) in Q12b.
  rewrite (rv_get07 regs2 _ 25 cp Hrv2 ltac:(unfold rl1; cbn; tauto)) in Q13b.
  pose proof (kept_regs07 E2 _ _ regs2 _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] HS2 HAE2
    ltac:(vm_compute; reflexivity)) as KR2. cbn [ms_regs restrict] in KR2.
  pose proof (ap_of_kept07 regs2 (ms_regs ms2) KR2) as HP3.
  pmkst HS2.
  rewrite (SIGP CS_sup_add) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
  change (cmd_af CS_sup_add) with AF_sup_add.
  destruct (RUN07 e pos F q c _ _ _ _ _ _ _ _ _ _ _ _ _ W regs2 (ms_regs ms2) mem2 (ms_mem ms2) md2 mdv2
    Hc2 Hl2 Hcp2 HJ2 V2 (rv_keep07 B e regs2 (ms_regs ms2) rl1 Hrv2 Hcs1 HP3)
    ltac:(left; reflexivity) ltac:(right; left; reflexivity) HDn) as (Hc3 & Hl3 & Hcp3).
  pose proof Hc3 as (HJ3 & Hk3 & Hmet3 & Hnm3 & Hfr3 & Hrv3 & Hsv3 & Hsp3' & Henv3 & Hrec3 & Hdat3 & Hperm3 & Hq3).
  pose proof (proj1 HJ3) as HAR3.
  pose proof (core_regs07 B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc3) as (_ & _ & _ & _ & _ & Hspz3 & _).
  assert (Hsp33 : alloc_ceiling <= spZ (ms_regs ms2) - 3 * ESTACK) by (rewrite Hspz3; unfold ESTACK in *; lia).
  destruct (tok_blk07 B e F c _ lyc Sc W (ms_mem ms2) mdv2 (e_R e) (e_O e) [vr_lb e q; vr_cb e c] 1 pu u HAR3 Hcp3 Hrec3
    ltac:(right; left; reflexivity) Hperm3 Hpu Hu) as (Hub & Huap & Hus & Hul & Hpu4 & Hpu64 & Hu8).
  destruct (oarg07 e F c _ lyc Sc W (ms_mem ms2) mdv2 (e_R e) (e_O e) [vr_lb e q; vr_cb e c] (ms_regs ms2) pp pl HAR3 Hcp3 Hrec3
    ltac:(right; left; reflexivity) Hperm3 Hsp33 Hpl) as (Hppa & Hppt & Hpp64 & Hpl8).
  destruct (oarg07 e F c _ lyc Sc W (ms_mem ms2) mdv2 (e_R e) (e_O e) [vr_lb e q; vr_cb e c] (ms_regs ms2) cp cl HAR3 Hcp3 Hrec3
    ltac:(right; left; reflexivity) Hperm3 Hsp33 Hcl) as (Hcpa & Hcpt & Hcp64 & Hcl8).
  pose proof (darg_le07 pl Hpl8) as Hdpl. pose proof (darg_le07 cl Hcl8) as Hdcl.
  pose proof (dec_length (atoi_a wi) Hid) as Hdec.
  pose proof (live07 B MT e pos F q c _ _ _ _ _ _ _ _ _ lyc Sc W _ _ _ Hent Hc3) as HL3.
  assert (HLA : LIVE_SUP_ADD (Some u) (atoi_a wi) pl cl t <= 3 * VERBS_RECEIVE_REQ + 100).
  { unfold LIVE_SUP_ADD, LIVE_ARG_S, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XMALLOC, sarg, VERBS_RECEIVE_REQ.
    rewrite Z.max_id. lia. }
  assert (HV1 : SUP_ADD_STK = ltac:(let v := eval vm_compute in SUP_ADD_STK in exact v)) by reflexivity.
  assert (HV0 : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
  assert (HXA : XM_SUP_ADD MT (e_R e) (Some u) (atoi_a wi) pl cl t <=
    6 * mo_malloc MT VERBS_RECEIVE_REQ + (rec_spill_frees (e_R e) + 1) * mo_free MT).
  { pose proof (xm_add_le MT MTL (e_R e) (Some u) (atoi_a wi) pl cl t ltac:(unfold sarg, LMAX; lia) Hid
      ltac:(unfold LMAX; lia) ltac:(unfold LMAX; lia) ltac:(unfold LMAX; lia)) as H. lia. }
  assert (HEA : 7 <= EV_SUP_ADD (e_R e)).
  { unfold EV_SUP_ADD, EV_RECORD, EV_ANSWER, EV_HAND_BACK, EV_ARG_S, EV_XMALLOC. rewrite Hsf0. lia. }
  eapply (CALL07F e pos F q c _ _ _ _ _ _ _ _ _ lyc Sc W (ms_regs ms2) (ms_mem ms2) mdv2 AF_sup_add SUP_ADD_STK _
    (EV_SUP_ADD (e_R e)) _ _ _ Hent Hc3 Q1b).
  + lia.
  + reflexivity.
  + lia.
  + lia.
  + exact (fp_add07 (e_O e)).
  + (* sup_add(tok[1], atoi(tok[2]), placement, client) *)
    intros ch HPRE.
    apply (TSUP_ADD lyc Sc W (ms_regs ms2) (ms_mem ms2) mdv2 ch pu (atoi_a wi) pp cp u pl cl (e_R e) (e_O e) HPRE
      (frm07 B MT e Hent)).
    * pose proof (frames07 B MT e pos lyc Sc W (ms_mem ms2) mdv2 k Hent HJ3). lia.
    * exact (proj1 Henv3).
    * exact (proj1 (proj2 (proj2 Henv3))).
    * exact Q10b.
    * lia.
    * exact Q11b.
    * exact Hid.
    * exact Q12b.
    * exact Hpp64.
    * exact Q13b.
    * exact Hcp64.
    * split; [exact Hub|]. split; [exact Huap|]. split; [exact Hus | exact Hul].
    * exact Hppa.
    * exact Hppt.
    * exact Hcpa.
    * exact Hcpt.
    * exact Hrec3.
    * apply (ev07 B MT e _ lyc Sc W (ms_mem ms2) mdv2 k (EV_SUP_ADD (e_R e)) Hent HJ3). rewrite EK. unfold EV_SUP_REPLY_CODE. lia.
    * rewrite Hsa. cbn [snd]. unfold LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ in *. lia.
    * rewrite Hsa. cbn [snd].
      apply (mok07 B MT MTL e Sc k nm 6 (rec_spill_frees (e_R e) + 1) _ (EV_SUP_ADD (e_R e)) Hent Hmet3).
      -- rewrite EK. unfold EV_SUP_REPLY_CODE. lia.
      -- exact HXA.
      -- lia.
      -- rewrite Hsf0. lia.
  + (* after the return, 0x8d484, at the FP state fx' sup_add returned at *)
    intros fx' ly2 S2 W2 regs4 mem4 md4 Hfx HJ4 HJc4 HP4 HK.
    rewrite Hsa in HK. cbn [snd] in HK.
    destruct HK as (R' & O' & tq & Hsa' & HK). cbv zeta in HK.
    destruct HK as (Ha0 & Htq & HrecO' & HO' & Hcl4 & Hkeep4 & HinT & Hne4 & HqO' & Hstr4 & Hbb4 & Hmle4).
    injection Hsa' as ER'. subst R'.
    assert (Ha0' : getr regs4 (Z_to_bv 5 10) = w64 tq) by exact Ha0.
    set (n := Z.of_nat (length t) + 1) in *.
    destruct (rec_nodup07 B _ _ _ _ _ HrecO') as (O2 & Hrec4 & HO2 & HndO2).
    assert (Hrv4 : vr_rv regs4 (vr_base B e ++ [(18, q); (19, F + 32); (22, F)])).
    { apply (rv_sub07 _ _ _ (rv_keep07 B e (ms_regs ms2) regs4 rl1 Hrv3 Hcs1 HP4)).
      intros x Hx. apply in_app_or in Hx as [Hx|Hx]; apply in_or_app; [left; exact Hx | right].
      unfold rl1. cbn in Hx |- *. tauto. }
    assert (Hmet4 : vr_meter MT e S2 (k + EV_SUP_ADD (e_R e)) (nm + 6)).
    { apply (meter_step MT MTL e Sc S2 k nm 6 (rec_spill_frees (e_R e) + 1) (XM_SUP_ADD MT (e_R e) (Some u) (atoi_a wi) pl cl t)
        (EV_SUP_ADD (e_R e)) Hmet3 Hmle4 HXA); [lia | rewrite Hsf0; lia]. }
    assert (HO2b : forall x, In x O2 -> In x (ablocks B ly2 S2)).
    { intros x Hx. exact (rec_repA_in_blocks B _ _ _ _ _ _ Hrec4 Hx). }
    assert (Hperm4 : Permutation (ablocks B ly2 S2) (O2 ++ [(tq, n); vr_lb e q; vr_cb e c] ++ e_rest e)).
    { apply (perm_text07 (ablocks B lyc Sc) (ablocks B ly2 S2) (e_O e) O2 ([vr_lb e q; vr_cb e c] ++ e_rest e) (tq, n)).
      - exact (RecBLemmas.recb_ablocks_nodup_m B _ _ _ _ _ (proj1 HJ4)).
      - exact Hperm3.
      - exact (Permutation_NoDup Hperm3 (RecBLemmas.recb_ablocks_nodup_m B _ _ _ _ _ HAR3)).
      - exact HndO2.
      - intros x Hx. apply HO'. apply HO2. exact Hx.
      - intros x Hx. destruct (Hcl4 x Hx) as [H1|[H1|H1]]; [left; exact H1 | right; left; apply HO2; exact H1 | right; right; exact H1].
      - exact Hkeep4.
      - exact HinT.
      - exact Hne4.
      - intros Hin. apply HO2 in Hin. apply HqO'. exact (in_map fst _ _ Hin).
      - exact HO2b. }
    assert (Hdat4 : ~ In (e_data e, Z.max (e_n e) 1) O2).
    { intros Hin. apply HO2 in Hin. destruct (HO' _ Hin) as [H1|H1]; [exact (Hdat3 H1)|]. apply H1.
      pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HinD & HnotO & _ & _ & _ & _ & _ & _ & _ & _ & Hperm0 & _).
      assert (HinR : In (e_data e, Z.max (e_n e) 1) (e_rest e)).
      { pose proof (Permutation_in _ Hperm0 HinD) as H0. apply in_app_or in H0 as [H0|H0]; [contradiction | exact H0]. }
      apply (Permutation_in _ (Permutation_sym Hperm3)). apply in_or_app. right. apply in_or_app. right. exact HinR. }
    destruct (C07C e pos F q c _ [vr_lb e q; vr_cb e c] [(tq, n); vr_lb e q; vr_cb e c] rl1
      [(18, q); (19, F + 32); (22, F)]
      (e_R e) R1 (e_O e) O2 (e_q0 e) k (k + EV_SUP_ADD (e_R e)) 2 (vr_k1 (e_R e) (e_D e)) nm (nm + 6) VR_NM_PRE VR_NM_HD
      lyc Sc W (ms_regs ms2) (ms_mem ms2) mdv2 ly2 S2 W2 regs4 mem4 md4 SUP_ADD_STK _ (EV_SUP_ADD (e_R e))
      Hc3 Hl3 Hcp3 HJ4 HJc4 ltac:(lia) (fp_add07 (e_O e)) Hkeep4
      ltac:(left; reflexivity) ltac:(right; left; reflexivity) HDn
      ltac:(rewrite EK; unfold EV_SUP_REPLY_CODE; lia) Hmet4 ltac:(unfold VR_NM_HD, VR_NM_PRE in *; lia) Hrv4 Hrec4 Hdat4 Hperm4)
      as (Hc4 & Hl4 & Hcp4).
    eapply SRr_mono.
    { exact (LEGT2 fx' e W2 pos F q c _ ly2 S2 regs4 mem4 md4 (k + EV_SUP_ADD (e_R e)) (nm + 6) (u :: wi :: rest) u
        (atoi_a wi) pl cl R1 t O2 tq pu (ent_fxr07 B MT fx fx' e Hent Hfx) Htk Hadd Hsa Hpu Hu ltac:(cbn [length]; lia)
        Hc4 Hl4 Hcp4 Ha0' ltac:(lia) Hstr4 ltac:(rewrite EK; lia) ltac:(unfold VR_NM_PRE in *; lia)
        ltac:(unfold LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ in *; lia)). }
    intros W' c' _ H. unfold hdF07. exists fx'. split; [exact Hfx | exact H].
Qed.

End e.
End f.
End d.
