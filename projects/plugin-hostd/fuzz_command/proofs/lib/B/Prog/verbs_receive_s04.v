(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S04 (TOK, 0x8d070-0x8d0f0) of the walk of verbs_receive on the ASan+UBSan
   build of plugin-hostd/fuzz_command (interface: lib/B/Prog/verbs_receive_iface.v, vr_s04_stmt), ported from the
   ASan walk's lib/A/Prog/verbs_receive_s04.v and redone on B's code: q spilled at s1+56 and copy = strdup(line)
   (verbs_receive_s04_a.v), the spill of the copy at s1+48 and the first strtok_r(copy, " \t", &save) at 0x8d08c
   (verbs_receive_s04_t.v), s2 = msg >> 3 and the test of the word at 0x8d094 and, when a word was cut, the set-up of
   B's spill map and of the word loop 0x8d098-0x8d0c4 and the loop itself 0x8d0c8-0x8d0f0 (verbs_receive_s04_l.v).
   Exits: 0x8d2bc with no word (vr_b4e) and 0x8d0f4 with the words cut and stored in tok[] (vr_b4t). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route verbs_receive_words strtok_r_c strspn_c strcspn_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtString RtAlloc04 RtAlloc.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_s04_k verbs_receive_s04_a verbs_receive_s04_t verbs_receive_s04_l.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the real frame's spill area s1 + [0, 80): written at s1 + 48 (copy) before the first strtok_r, at s1 + [0, 48)
   after it (the set-up 0x8d098-0x8d0c4) *)
Definition s4_spw1 : YP09.region := YP09.mkRegion (Some 9%nat) 0 80 48 56 [].
Definition s4_spw2 : YP09.region := YP09.mkRegion (Some 9%nat) 0 80 0 48 [].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma s4_sv_srl3 : forall (regs : bvmap 5 word) n (r : bv 5) v, Z.of_nat n = bv_unsigned r -> getr regs r = w64 v ->
0 <= v < 2 ^ 64 -> sv_denot (Eimg (Ereg regs [])) (SAlu ALU_SRL (SOff n 0) (SLit 3)) = w64 (v / 8).
Proof.
intros regs n r v Hn Hr Hv. apply bv_eq. fold (U (Eimg (Ereg regs [])) (SAlu ALU_SRL (SOff n 0) (SLit 3))).
rewrite U_srl3. rewrite (U_atom _ n v); [|rewrite (ew_seed regs n r Hn), Hr; reflexivity | lia].
unfold w64. rewrite unsigned_lit_small; [reflexivity|]. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Ltac s4in2 := cbn [vr_base vr_rl2 s4_rlL vr_sl2 vr_sl3 app In]; repeat first [left; reflexivity | right].
Ltac s4reg2 HS r Hr :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v in Hr
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v in Hr
end.
(* the spill region's write window, for a symbolic state the run computed *)
Ltac s4_awr2 E9 :=
  lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  lazymatch type of E9 with _ = ?bb => eapply awr_ok_cons_gen with (b := bb) end;
  [reflexivity | exact E9 | | apply awr_ok_nil];
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; left; lia.
Ltac s4_wr2 E9 :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr); vm_compute in Hin; destruct Hin as [<- | []];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite E9 in Hr; lia.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Variables PC_STRDUP_RA0 : Z.
Hypothesis STRTOK_R : forall fx0 : YK11.FPState, @RtString.astrtok_r_realizes fx0 rc SEGS B (SIGMA CS_strtok_r) 0xa6bf8 0x604158.
Hypothesis ASTRDUP : forall fx0 : YK11.FPState,
  @RtAlloc04.astrdup04_rule fx0 rc SK SEGS B MT (SIGMA CS___interceptor_trampoline_strdup) PC_STRDUP_RA0.
Hypothesis HB : YF0m.CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis RRO : vr_relro_img.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Hypothesis SHOK : vr_shadow_ok B.
Hypothesis BLKT : vr_blktail B.
Hypothesis ROA : vr_ro_of_aro B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTO := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (L := cmd_listing) (PI := PI).

(* msg's range: vr_ent's 13th conjunct (since pass 5) *)
Lemma s4_msg_range : forall e, vr_ent B MT e -> 0 <= e_msg e < 2 ^ 64.
Proof.
intros e Hent. unfold vr_ent in Hent; cbv zeta in Hent.
destruct Hent as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmsg & _). exact Hmsg.
Qed.

(* from the return of strdup, 0x8d07c: the spill of the copy at s1 + 48, the first strtok_r, s2 = msg >> 3, the test
   of its result, and either the exit with no word 0x8d2bc or the set-up of the word loop up to its head 0x8d0c8 *)
Lemma s4_B : forall e W cf, vr_ent B MT e -> s4_P1 B MT e W cf ->
SRr SEGS W cf (fun W' cf' => vr_b4e B MT e W' cf' \/ s4_L B MT e 0 W' cf').
Proof.
intros e W cf Hent HP.
destruct HP as (pos & F & q & c & lyc & Sc & regs & mem & md & k & nm & -> & Hcmn & Hrv & Hspl & Hcby & Hsv).
pose proof Hent as Hent'. unfold vr_ent in Hent'; cbv zeta in Hent'.
destruct Hent' as (HPRE & _ & _ & _ & _ & _ & _ & Hn & HDn & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & HVO & _).
pose proof (s4_msg_range e Hent) as Hmsg.
pose proof Hcmn as (HJ & Hk & HM & Hnm & Hst & HNd & HPm & Hfresh & HcO & Hcl).
pose proof Hst as (HVF & HSv & HARO & HRec & HQ & HLn).
pose proof HVF as (EF & Hfl & Hsh).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity.
assert (HSTK : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
destruct (s1_off e Hal16) as [Hs1o Hs1r].
assert (Hfr : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W mem md 4 pos HAR Hfr) as (Hf0 & Hfc & _).
change (fs_frame_bytes 4) with 1024 in Hfc. rewrite <- EF in Hf0, Hfc.
assert (Hcb : In (c, s4_n e) (ablocks B lyc Sc))
  by (apply (Permutation_in _ (Permutation_sym HPm)); apply in_or_app; right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcb) as (_ & Hc4096 & Hcc & _ & _ & _ & Hcn). unfold MALLOC_MAX in Hcn.
pose proof (req_size_pos (s4_n e) ltac:(unfold s4_n; lia)) as [Hrq1 Hrq2].
pose proof (sep_block_frame SEGS B LAWS lyc Sc W mem md _ _ 4 pos HAR Hcb Hfr) as Hcf.
unfold zdisjoint in Hcf. cbn [fst snd] in Hcf. change (fs_frame_bytes 4) with 1024 in Hcf. rewrite <- EF in Hcf.
assert (Hcnew : ~ In (c, s4_n e) (ablocks B (e_ly e) (e_S e))) by exact (proj2 Hfresh).
assert (Hlnz : ~ In (Z_to_bv 8 0) (Verbs.line (e_D e))) by exact (proj2 (proj2 HLn)).
(* the registers *)
assert (RG : forall r v, In (r, v) (vr_base B e ++ vr_rl2 e F q ++ [(10, c)]) -> getr regs (Z_to_bv 5 r) = w64 v)
  by (intros r v Hin; exact (rv_get regs _ r v Hrv Hin)).
pose proof (RG 2 _ ltac:(s4in2)) as R2. pose proof (RG 3 _ ltac:(s4in2)) as R3.
pose proof (RG 4 _ ltac:(s4in2)) as R4. pose proof (RG 8 _ ltac:(s4in2)) as R8.
pose proof (RG 9 _ ltac:(s4in2)) as R9. pose proof (RG 10 _ ltac:(s4in2)) as R10.
pose proof (RG 18 _ ltac:(s4in2)) as R18. pose proof (RG 19 _ ltac:(s4in2)) as R19.
pose proof (RG 20 _ ltac:(s4in2)) as R20. pose proof (RG 21 _ ltac:(s4in2)) as R21.
pose proof (RG 22 _ ltac:(s4in2)) as R22.
pose proof (RG 24 _ ltac:(s4in2)) as R24. pose proof (RG 25 _ ltac:(s4in2)) as R25.
pose proof (RG 26 _ ltac:(s4in2)) as R26. pose proof (RG 27 _ ltac:(s4in2)) as R27.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs []))) by apply Eimg_env.
assert (E9 : bv_unsigned (ew (Eimg (Ereg regs [])) 9) = vr_s1 e)
  by (rewrite (ew_seed regs 9 (Z_to_bv 5 9) eq_refl), R9; apply unsigned_lit_small; lia).
(* .str (" \t", 0x22500) is image object 92 of the listing (CmdAddr.v cmd_objs) *)
assert (V333 : VAL 333%nat = 0x22500) by exact (HVO 92%nat ltac:(vm_compute; lia)).
unfold cfg_at, vr_pc. change (w64 (BASE + (AF_verbs_receive + (0x8d07c - 0x8ce4c)))) with (Z_to_bv 64 (BASE + 27468)).
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (s4_ss 27468 [s4_spw1])
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 27468)) mem (seg_rom SEGS)))).
{ apply s4_seed; [vm_compute; reflexivity | | cbn; tauto].
  constructor; [|constructor]. unfold region_ok, s4_spw1.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
(* 0x8d07c .. 0x8d08c: a1 = .str, the copy spilled at s1 + 48, a2 = &save, the call of strtok_r(copy, " \t", &save) *)
paj_run_shc RUNP RUNC HS HJ.
{ change (ss_mem (s4_ss 27468 [s4_spw1])) with [s4_spw1].
  eapply awr_ok_cons_gen with (b := vr_s1 e); [reflexivity | exact E9 | | apply awr_ok_nil].
  intros a Ha. cbn [s4_spw1 YP09.r_wlo YP09.r_whi] in Ha. left. lia. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1.
s4reg2 HS (10%bv : bv 5) Q10. s4reg2 HS (11%bv : bv 5) Q11. s4reg2 HS (12%bv : bv 5) Q12.
s4reg2 HS (1%bv : bv 5) Q1. s4reg2 HS (2%bv : bv 5) Q2. s4reg2 HS (3%bv : bv 5) Q3. s4reg2 HS (4%bv : bv 5) Q4.
rewrite (sv_atom regs 10 (Z_to_bv 5 10) _ eq_refl R10) in Q10.
rewrite (sv_atom regs 26 (Z_to_bv 5 26) _ eq_refl R26) in Q12.
rewrite (sv_atom regs 2 (Z_to_bv 5 2) _ eq_refl R2) in Q2.
rewrite (sv_atom regs 3 (Z_to_bv 5 3) _ eq_refl R3) in Q3.
rewrite (sv_atom regs 4 (Z_to_bv 5 4) _ eq_refl R4) in Q4.
assert (Q11' : getr (ms_regs ms) 11%bv = w64 0x22500).
{ rewrite Q11. cbn [sv_denot]. rewrite (img_env_atomP _ 333 HEI ltac:(unfold A_TEXT, A_LIM; lia)), V333. reflexivity. }
change (SOff 240 27488) with (SOff A_TEXT 27488) in Q1. rewrite (codeptr_val _ 27488 HEI) in Q1.
assert (Hsp1 : spZ (ms_regs ms) = vr_s1 e) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
assert (Hra1 : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (HrvC : vr_rv (ms_regs ms) (vr_base B e ++ vr_rl2 e F q)).
{ unfold vr_rv, vr_base, vr_rl2. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  all: lazymatch goal with
  | |- getr _ (Z_to_bv 5 ?r) = _ =>
    let Q := fresh "Q" in s4reg2 HS (Z_to_bv 5 r) Q; rewrite Q; clear Q
  end.
  - exact (sv_atom regs 2 (Z_to_bv 5 2) _ eq_refl R2).
  - exact (sv_atom regs 3 (Z_to_bv 5 3) _ eq_refl R3).
  - exact (sv_atom regs 4 (Z_to_bv 5 4) _ eq_refl R4).
  - exact (sv_atom regs 8 (Z_to_bv 5 8) _ eq_refl R8).
  - exact (sv_atom regs 9 (Z_to_bv 5 9) _ eq_refl R9).
  - exact (sv_atom regs 18 (Z_to_bv 5 18) _ eq_refl R18).
  - exact (sv_atom regs 19 (Z_to_bv 5 19) _ eq_refl R19).
  - exact (sv_atom regs 20 (Z_to_bv 5 20) _ eq_refl R20).
  - exact (sv_atom regs 21 (Z_to_bv 5 21) _ eq_refl R21).
  - exact (sv_atom regs 22 (Z_to_bv 5 22) _ eq_refl R22).
  - exact (sv_atom regs 24 (Z_to_bv 5 24) _ eq_refl R24).
  - exact (sv_atom regs 25 (Z_to_bv 5 25) _ eq_refl R25).
  - exact (sv_atom regs 26 (Z_to_bv 5 26) _ eq_refl R26).
  - exact (sv_atom regs 27 (Z_to_bv 5 27) _ eq_refl R27). }
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (vr_s1 e + 48 <= a < vr_s1 e + 56) -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha Hnw. apply (aview_of_frame SEGS _ _ (w_H W) mem (ms_mem ms) HFr a Ha). intros (r & Hin & Hr).
  change (ss_mem (s4_ss 27468 [s4_spw1])) with [s4_spw1] in Hin. destruct Hin as [<- | []].
  cbn [s4_spw1 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E9 in Hr. lia. }
assert (S48 : aval_mem (rdW W (ms_mem ms)) (vr_s1 e + 48) 8 c).
{ eapply (s4_chunk_aval W _ _ ms 0%nat _ 9%nat 48 (SOff 10 0) (vr_s1 e) c HS); [reflexivity | reflexivity | | exact E9 |
    exact (sv_atom regs 10 (Z_to_bv 5 10) c eq_refl R10) | lia].
  cbn [YP09.r_chunks In]. repeat first [left; reflexivity | right]. }
assert (Hcmn1 : s4_cmn B MT e pos F q c lyc Sc W (ms_mem ms) md1 k nm).
{ apply (s4_cmn_keep B MT RRO PROGU e pos F q c lyc Sc W mem md k nm (ms_mem ms) md1 Hent Hcmn HJ).
  intros a Ha H1 H2 H3. apply KF; [exact Ha | lia]. }
pose proof Hcmn1 as (_ & _ & _ & _ & ((_ & _ & Hsh1) & _ & HARO1 & _) & _).
assert (Hsh76 : rdW W (ms_mem ms) (shadow_addr F + 76) = Some 0) by exact (Hsh1 76%nat ltac:(lia)).
assert (Hsv1 : rdword (rdW W (ms_mem ms)) (F + 608) = Some 0).
{ apply (rdword_agree (rdW W mem)); [exact Hsv|]. intros kk Hkk. apply KF; lia. }
assert (Hrem1 : s4_rem (rdW W (ms_mem ms)) c (s4_n e) c (s4_WS e)).
{ right. exists (Verbs.line (e_D e)). split; [lia|]. split.
  - split; [|exact Hlnz]. apply (abytes_atR_agree (rdW W mem) _ c _ (s4_n e) Hcby);
      [unfold s4_n; rewrite length_app; cbn [length]; lia|]. intros kk Hkk. apply KF; lia.
  - split; [lia|]. split; [unfold s4_n; lia | reflexivity]. }
assert (EC : c = (if c =? 0 then 0 else c)) by (replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
pmkst HS.
eapply SRr_bind.
{ exact (s4_tok_call B (STRTOK_R fx) RECC SHOK BLKT ROA e pos F c (s4_n e) lyc Sc W (ms_regs ms) (ms_mem ms) md1 k c 0 c
    (s4_WS e) HJ EF Hcb Hcnew Hsh76 Hsp1 Q3 Q4 Hra1 Q10 Q11' Q12 Hsv1 EC Hrem1 HARO1). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HK2 & a0 & sv2 & H10' & Hsv2 & Hres).
(* after the call *)
assert (HrvC2 : vr_rv regs2 (vr_base B e ++ vr_rl2 e F q)).
{ apply (rv_keep (ms_regs ms) regs2 _ HrvC HP2). unfold vr_base, vr_rl2.
  (repeat apply Forall_cons); try (apply Forall_nil); cbn [fst]; unfold acallee_saved; lia. }
assert (HK2' : forall a, 0 <= a < 2 ^ 64 -> a < vr_s1 e - 4 * ESTACK \/ vr_s1 e <= a -> ~ (F + 608 <= a < F + 616) ->
  ~ (c <= a < c + s4_n e) -> rdW W mem2 a = rdW W (ms_mem ms) a).
{ intros a Ha H1 H2 H3. apply HK2; [exact Ha | lia | exact H2 | intros (_ & Hb); exact (H3 Hb)]. }
clear HK2.
assert (Hcmn2 : s4_cmn B MT e pos F q c lyc Sc W mem2 md2 k nm).
{ apply (s4_cmn_keep B MT RRO PROGU e pos F q c lyc Sc W (ms_mem ms) md1 k nm mem2 md2 Hent Hcmn1 HJ2).
  intros a Ha H1 H2 H3. apply HK2'; [exact Ha | lia | lia | lia]. }
assert (S48' : aval_mem (rdW W mem2) (vr_s1 e + 48) 8 c).
{ apply (aval_mem_agree _ _ _ _ _ S48). intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply HK2'; lia. }
assert (S56' : aval_mem (rdW W mem2) (vr_s1 e + 56) 8 q).
{ assert (S56 : aval_mem (rdW W mem) (vr_s1 e + 56) 8 q)
    by (unfold vr_spill in Hspl; exact (proj1 (Forall_forall _ _) Hspl (56, q) ltac:(cbn [In]; left; reflexivity))).
  apply (aval_mem_agree _ _ _ _ _ S56). intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk.
  rewrite (HK2' (vr_s1 e + 56 + kk)) by lia. apply KF; lia. }
assert (S72' : aval_mem (rdW W mem2) (vr_s1 e + 72) 8 F).
{ assert (S72 : aval_mem (rdW W mem) (vr_s1 e + 72) 8 F)
    by (unfold vr_spill in Hspl; exact (proj1 (Forall_forall _ _) Hspl (72, F) ltac:(cbn [In]; right; left; reflexivity))).
  apply (aval_mem_agree _ _ _ _ _ S72). intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk.
  rewrite (HK2' (vr_s1 e + 72 + kk)) by lia. apply KF; lia. }
rewrite Q1.
assert (HEI2 : img_env VAL A_LIM (Eimg (Ereg regs2 []))) by apply Eimg_env.
assert (RG2 : forall r v, In (r, v) (vr_base B e ++ vr_rl2 e F q) -> getr regs2 (Z_to_bv 5 r) = w64 v)
  by (intros r v Hin; exact (rv_get regs2 _ r v HrvC2 Hin)).
pose proof (RG2 2 _ ltac:(s4in2)) as T2. pose proof (RG2 3 _ ltac:(s4in2)) as T3.
pose proof (RG2 4 _ ltac:(s4in2)) as T4. pose proof (RG2 8 _ ltac:(s4in2)) as T8.
pose proof (RG2 9 _ ltac:(s4in2)) as T9. pose proof (RG2 18 _ ltac:(s4in2)) as T18.
pose proof (RG2 19 _ ltac:(s4in2)) as T19. pose proof (RG2 20 _ ltac:(s4in2)) as T20.
pose proof (RG2 21 _ ltac:(s4in2)) as T21. pose proof (RG2 22 _ ltac:(s4in2)) as T22.
pose proof (RG2 24 _ ltac:(s4in2)) as T24.
pose proof (RG2 25 _ ltac:(s4in2)) as T25. pose proof (RG2 26 _ ltac:(s4in2)) as T26.
pose proof (RG2 27 _ ltac:(s4in2)) as T27.
assert (T10 : getr regs2 (Z_to_bv 5 10) = w64 a0)
  by (replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity); exact H10').
assert (E9' : bv_unsigned (ew (Eimg (Ereg regs2 [])) 9) = vr_s1 e)
  by (rewrite (ew_seed regs2 9 (Z_to_bv 5 9) eq_refl), T9; apply unsigned_lit_small; lia).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (HS2 : st_ok_pi SEGS VAL (Eimg (Ereg regs2 [])) (s4_ss 27488 [s4_spw2])
  (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (BASE + 27488)) mem2 (seg_rom SEGS)))).
{ apply s4_seed; [vm_compute; reflexivity | | cbn; tauto].
  constructor; [|constructor]. unfold region_ok, s4_spw2.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9'. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres2. lia. }
clear HS HF HFr HG mat HK2' KF S48 HrvC Hsv1 Hrem1 HARO1 Hsh1 Hsh76 Q1 Q2 Q3 Q4 Q10 Q11 Q11' Q12 Hsp1 Hra1 HP2 HJ Hcmn1 EC.
clear ms.
(* 0x8d090 .. 0x8d094: s2 = msg >> 3, the test of the word *)
paj_run_sh RUNP HS2 HJ2.
{ change (ss_mem (s4_ss 27488 [s4_spw2])) with [s4_spw2].
  eapply awr_ok_cons_gen with (b := vr_s1 e); [reflexivity | exact E9' | | apply awr_ok_nil].
  intros a Ha. cbn [s4_spw2 YP09.r_wlo YP09.r_whi] in Ha. left. lia. }
rename ms into ms3.
set (md3 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md3.
assert (K23 : forall a, 0 <= a < 2 ^ 64 -> ~ (vr_s1 e <= a < vr_s1 e + 48) -> rdW W (ms_mem ms3) a = rdW W mem2 a).
{ intros a Ha Hnw. apply (aview_of_frame SEGS _ _ (w_H W) mem2 (ms_mem ms3) HFr a Ha). intros (r & Hin & Hr).
  change (ss_mem (s4_ss 27488 [s4_spw2])) with [s4_spw2] in Hin. destruct Hin as [<- | []].
  cbn [s4_spw2 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E9' in Hr. lia. }
clear HF HFr HG mat.
assert (U10 : U (Eimg (Ereg regs2 [])) (SOff 10 0) = a0 mod 2 ^ 64).
{ unfold U. cbn [sv_denot]. rewrite (ew_seed regs2 10 (Z_to_bv 5 10) eq_refl), T10, Z.add_0_r. unfold w64.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_mod. lia. }
assert (Hlb : In (vr_lb e q) (ablocks B lyc Sc))
  by (apply (Permutation_in _ (Permutation_sym HPm)); apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hlb) as (_ & Hq4096 & Hqc & _).
cbn [fst snd vr_lb] in Hq4096, Hqc.
pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(pose proof (vr_l_range (e_n e) (e_D e) ltac:(lia)); lia)) as [Hrql1 Hrql].
assert (HshF : 0 <= shadow_addr F /\ shadow_addr F + 4 < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos F 8 ltac:(lia)). pose proof (Z.div_le_upper_bound F 8 F ltac:(lia) ltac:(lia)).
  lia. }
(* the words of the line: none, or a first word at a0 *)
revert Hres. destruct (s4_WS e) as [|w ws'] eqn:HWS; intros Hres; cbn [s4_tres] in Hres.
- (* no word: to 0x8d2bc *)
  subst a0.
  psrr_branch_pi RUNP BR HS2.
  + paj_run_to_sh RUNTO HS2 HJ2 28044.
    { s4_awr2 E9'. }
    rename ms into ms4.
    set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4.
    assert (K24 : forall a, 0 <= a < 2 ^ 64 -> ~ (vr_s1 e <= a < vr_s1 e + 48) -> rdW W (ms_mem ms4) a = rdW W mem2 a).
    { intros a Ha Hnw. rewrite <- (K23 a Ha Hnw). apply (aview_of_frame SEGS _ _ (w_H W) (ms_mem ms3) (ms_mem ms4) HFr a Ha).
      s4_wr2 E9'. }
    assert (Hrv4 : vr_rv (ms_regs ms4) (vr_base B e ++ vr_rl4e e F q)).
    { unfold vr_rv, vr_base, vr_rl4e. cbn [app].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      all: lazymatch goal with
      | |- getr _ (Z_to_bv 5 ?r) = _ =>
        let Q := fresh "Q" in s4reg2 HS2 (Z_to_bv 5 r) Q; rewrite Q; clear Q
      end.
      - exact (sv_atom regs2 2 (Z_to_bv 5 2) _ eq_refl T2).
      - exact (sv_atom regs2 3 (Z_to_bv 5 3) _ eq_refl T3).
      - exact (sv_atom regs2 4 (Z_to_bv 5 4) _ eq_refl T4).
      - exact (sv_atom regs2 8 (Z_to_bv 5 8) _ eq_refl T8).
      - exact (sv_atom regs2 9 (Z_to_bv 5 9) _ eq_refl T9).
      - exact (s4_sv_srl3 regs2 24 (Z_to_bv 5 24) _ eq_refl T24 Hmsg).
      - exact (sv_atom regs2 19 (Z_to_bv 5 19) _ eq_refl T19).
      - exact (sv_atom regs2 20 (Z_to_bv 5 20) _ eq_refl T20).
      - exact (sv_atom regs2 21 (Z_to_bv 5 21) _ eq_refl T21).
      - exact (sv_atom regs2 22 (Z_to_bv 5 22) _ eq_refl T22).
      - exact (sv_atom regs2 24 (Z_to_bv 5 24) _ eq_refl T24).
      - exact (sv_atom regs2 25 (Z_to_bv 5 25) _ eq_refl T25).
      - exact (sv_atom regs2 26 (Z_to_bv 5 26) _ eq_refl T26).
      - exact (sv_atom regs2 27 (Z_to_bv 5 27) _ eq_refl T27). }
    assert (Hcmn4 : s4_cmn B MT e pos F q c lyc Sc W (ms_mem ms4) md4 k nm).
    { apply (s4_cmn_keep B MT RRO PROGU e pos F q c lyc Sc W mem2 md2 k nm (ms_mem ms4) md4 Hent Hcmn2 HJ2).
      intros a Ha H1 _ _. apply K24; [exact Ha | lia]. }
    pmkst HS2. apply SRr_ret. left.
    exists pos, F, q, c, lyc, Sc, (ms_regs ms4), (ms_mem ms4), md4, k, nm.
    split; [apply s4_cfg; unfold AF_verbs_receive; lia|].
    split; [rewrite s4_toks_D, HWS; reflexivity|].
    split.
    { apply (s4_core B MT RECC ROA e pos F q c lyc Sc W _ _ md4 k nm _ _ Hcmn4 Hrv4).
      unfold vr_spill, vr_sl2. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - apply (aval_mem_agree _ _ _ _ _ S48'). intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply K24; lia.
      - apply (aval_mem_agree _ _ _ _ _ S56'). intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply K24; lia.
      - apply (aval_mem_agree _ _ _ _ _ S72'). intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply K24; lia. }
    pose proof Hcmn4 as (_ & _ & _ & _ & (_ & _ & _ & _ & _ & HLn4) & _ & _ & Hfresh4 & _).
    split; [exact HLn4 | exact Hfresh4].
  + exfalso. rewrite branch_eq_U, U10, U_SLit in Hc. vm_compute in Hc. discriminate Hc.
- (* the first word w at a0: B's spill map and the word loop's registers (0x8d098-0x8d0c4), to the head 0x8d0c8 *)
  destruct Hres as (Ha0 & Hca0 & Hw2 & Ha0e & Hrem2).
  assert (Hbnd2 : (if sv2 =? 0 then c + s4_n e else sv2) <= c + s4_n e).
  { destruct Hrem2 as [(-> & _) | (r & Hr0 & _ & Hcr & Hrn & _)]; [cbn; lia|].
    replace (sv2 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hr0). lia. }
  assert (Ha0m : a0 mod 2 ^ 64 = a0) by (apply Z.mod_small; lia).
  psrr_branch_pi RUNP BR HS2.
  + exfalso. rewrite branch_eq_U, U10, Ha0m, U_SLit in Hc. apply Z.eqb_eq in Hc. apply Ha0. rewrite Hc. reflexivity.
  + clear Hc. paj_run_to_sh RUNTO HS2 HJ2 27544.
    { s4_awr2 E9'. }
    rename ms into ms4.
    set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4.
    assert (K24 : forall a, 0 <= a < 2 ^ 64 -> ~ (vr_s1 e <= a < vr_s1 e + 48) -> rdW W (ms_mem ms4) a = rdW W mem2 a).
    { intros a Ha Hnw. rewrite <- (K23 a Ha Hnw). apply (aview_of_frame SEGS _ _ (w_H W) (ms_mem ms3) (ms_mem ms4) HFr a Ha).
      s4_wr2 E9'. }
    assert (Hrv4 : vr_rv (ms_regs ms4) (vr_base B e ++ s4_rlL e F 0 a0)).
    { unfold vr_rv, vr_base, s4_rlL. cbn [app].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      all: lazymatch goal with
      | |- getr _ (Z_to_bv 5 ?r) = _ =>
        let Q := fresh "Q" in s4reg2 HS2 (Z_to_bv 5 r) Q; rewrite Q; clear Q
      end.
      - exact (sv_atom regs2 2 (Z_to_bv 5 2) _ eq_refl T2).
      - exact (sv_atom regs2 3 (Z_to_bv 5 3) _ eq_refl T3).
      - exact (sv_atom regs2 4 (Z_to_bv 5 4) _ eq_refl T4).
      - exact (sv_atom regs2 8 (Z_to_bv 5 8) _ eq_refl T8).
      - exact (sv_atom regs2 9 (Z_to_bv 5 9) _ eq_refl T9).
      - exact (sv_atom regs2 10 (Z_to_bv 5 10) _ eq_refl T10).
      - exact (s4_sv_srl3 regs2 24 (Z_to_bv 5 24) _ eq_refl T24 Hmsg).
      - exact (sv_atom regs2 19 (Z_to_bv 5 19) _ eq_refl T19).
      - reflexivity.
      - rewrite (s4_sv_off regs2 22 (Z_to_bv 5 22) _ 32 eq_refl T22 ltac:(lia)). f_equal. lia.
      - reflexivity.
      - exact (sv_atom regs2 24 (Z_to_bv 5 24) _ eq_refl T24).
      - reflexivity.
      - exact (sv_atom regs2 26 (Z_to_bv 5 26) _ eq_refl T26).
      - cbn [sv_denot]. rewrite (img_env_atomP _ 333 HEI2 ltac:(unfold A_TEXT, A_LIM; lia)), V333. reflexivity. }
    assert (Hcmn4 : s4_cmn B MT e pos F q c lyc Sc W (ms_mem ms4) md4 k nm).
    { apply (s4_cmn_keep B MT RRO PROGU e pos F q c lyc Sc W mem2 md2 k nm (ms_mem ms4) md4 Hent Hcmn2 HJ2).
      intros a Ha H1 _ _. apply K24; [exact Ha | lia]. }
    (* B's spill map: s1+0 = s5 (0), +8 = s9 (shadow_addr F), +16 = s4 (F, the B-only store 0x8d0a4), +24 = s6 (F),
       +32 = s11 (shadow_addr F + 4), +40 = s6 + 32 (tok) from the set-up; +48, +56, +72 from before *)
    assert (Hsp4 : vr_spill e W (ms_mem ms4) (vr_sl3 F q c)).
    { unfold vr_spill, vr_sl3. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - eapply (s4_chunk_aval W _ _ ms4 0%nat _ 9%nat 0 (SOff 21 0) (vr_s1 e) _ HS2); [reflexivity | reflexivity | | exact E9' |
          exact (sv_atom regs2 21 (Z_to_bv 5 21) _ eq_refl T21) | lia].
        cbn [YP09.r_chunks In]. repeat first [left; reflexivity | right].
      - eapply (s4_chunk_aval W _ _ ms4 0%nat _ 9%nat 8 (SOff 25 0) (vr_s1 e) _ HS2); [reflexivity | reflexivity | | exact E9' |
          exact (sv_atom regs2 25 (Z_to_bv 5 25) _ eq_refl T25) | lia].
        cbn [YP09.r_chunks In]. repeat first [left; reflexivity | right].
      - eapply (s4_chunk_aval W _ _ ms4 0%nat _ 9%nat 16 (SOff 20 0) (vr_s1 e) _ HS2); [reflexivity | reflexivity | | exact E9' |
          exact (sv_atom regs2 20 (Z_to_bv 5 20) _ eq_refl T20) | lia].
        cbn [YP09.r_chunks In]. repeat first [left; reflexivity | right].
      - eapply (s4_chunk_aval W _ _ ms4 0%nat _ 9%nat 24 (SOff 22 0) (vr_s1 e) _ HS2); [reflexivity | reflexivity | | exact E9' |
          exact (sv_atom regs2 22 (Z_to_bv 5 22) _ eq_refl T22) | lia].
        cbn [YP09.r_chunks In]. repeat first [left; reflexivity | right].
      - eapply (s4_chunk_aval W _ _ ms4 0%nat _ 9%nat 32 (SOff 27 0) (vr_s1 e) _ HS2); [reflexivity | reflexivity | | exact E9' |
          exact (sv_atom regs2 27 (Z_to_bv 5 27) _ eq_refl T27) | lia].
        cbn [YP09.r_chunks In]. repeat first [left; reflexivity | right].
      - eapply (s4_chunk_aval W _ _ ms4 0%nat _ 9%nat 40 (SOff 22 32) (vr_s1 e) _ HS2); [reflexivity | reflexivity | | exact E9' |
          exact (s4_sv_off regs2 22 (Z_to_bv 5 22) F 32 eq_refl T22 ltac:(lia)) | lia].
        cbn [YP09.r_chunks In]. repeat first [left; reflexivity | right].
      - apply (aval_mem_agree _ _ _ _ _ S48'). intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply K24; lia.
      - apply (aval_mem_agree _ _ _ _ _ S56'). intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply K24; lia.
      - apply (aval_mem_agree _ _ _ _ _ S72'). intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply K24; lia. }
    pmkst HS2. apply SRr_ret. right.
    exists pos, F, q, c, lyc, Sc, (ms_regs ms4), (ms_mem ms4), md4, k, nm, [], a0, sv2, w.
    split; [apply s4_cfg; unfold AF_verbs_receive; lia|].
    split; [lia|]. split; [exact Hcmn4|]. split; [exact Hrv4|]. split; [exact Hsp4|].
    split; [exact (s4_toks_nil _ _ _ _)|].
    split; [rewrite HWS; reflexivity|].
    split; [apply (astr_atR_agree (rdW W mem2) _ a0 w (Z.of_nat (length w) + 1) Hw2); [lia|]; intros kk Hkk; apply K24; lia|].
    split; [lia|]. split; [exact Ha0e|].
    split; [apply (rdword_agree (rdW W mem2)); [exact Hsv2|]; intros kk Hkk; apply K24; lia|].
    rewrite HWS. apply (s4_rem_agree (rdW W mem2) _ c (s4_n e) sv2 ws' Hrem2). intros Hsv20 a Ha.
    destruct Hrem2 as [(? & _) | (r & _ & _ & Hcr & _)]; [contradiction|]. apply K24; lia.
Qed.

Lemma vr_s04 : vr_s04_stmt B MT.
Proof.
intros e W cf Hent Hb3.
eapply SRr_bind; [exact (s4_A B MT PC_STRDUP_RA0 (ASTRDUP fx) HB MTL RRO PROGU e W cf Hent Hb3)|].
intros W1 cf1 _ HP1.
eapply SRr_bind; [exact (s4_B e W1 cf1 Hent HP1)|].
intros W2 cf2 _ [H | H].
- apply SRr_ret. left. exact H.
- eapply SRr_mono; [exact (s4_loop B MT (STRTOK_R fx) RRO RECC PROGU SHOK BLKT ROA 63 e 0 W2 cf2 Hent eq_refl H)|].
  intros W3 cf3 _ H3. right. exact H3.
Qed.

End e.
End f.
End d.
