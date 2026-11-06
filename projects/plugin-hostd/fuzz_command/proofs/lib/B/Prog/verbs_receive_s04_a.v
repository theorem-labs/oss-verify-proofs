(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S04 (TOK, 0x8d070-0x8d0f0) of the walk of verbs_receive on the ASan+UBSan
   build of plugin-hostd/fuzz_command, first part, ported from the ASan walk's lib/A/Prog/verbs_receive_s04_a.v: from
   vr_b3 at 0x8d070, the spill of the line q at s1+56 (B-only, 0x8d070 `sd s2,56(s1)`), then copy = strdup(line)
   through a Theorem Labs lane's astrdup04_rule (0x8d078), to the return at 0x8d07c (s4_P1: the copy block (c, |line| + 1) holds
   the line). The strtok_r calls and the word loop are verbs_receive_s04_t.v, _l.v and verbs_receive_s04.v. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit verbs_receive_s04_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the real frame's spill area, s1 + [0, 80), writable at s1 + [56, 64) (the spill of the line, 0x8d070) *)
Definition s4_stk : YP09.region := YP09.mkRegion (Some 9%nat) 0 80 56 64 [].
(* the word tok[k] at F + 32 + 8k, held in s6 (B's register; A held it in s4) *)
Definition s4_tokr : YP09.region := YP09.mkRegion (Some 22%nat) 0 8 0 8 [].
Definition s4_ss (pc : Z) (rs : smem) : sstate := mkSS pc sr_atoms rs None (mkFacts [] [] []).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a symbolic state seeded from a machine state: the registers as atoms of their own values *)
Lemma s4_seed : forall (W : world SEGS) regs mem pc rs,
regions_wf rs = true -> Forall (region_ok SEGS (Eimg (Ereg regs [])) (mrestrict (w_H W) mem)) rs ->
pairwise_disjoint (Eimg (Ereg regs [])) rs ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (s4_ss pc rs)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc rs Hwf Hrs Hpd. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- exact Hwf. - exact Hrs. - exact Hpd.
- split; [exact I | split; exact I].
Qed.
Lemma ew_seed : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs [])) n = getr regs r.
Proof.
intros regs n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma rv_get : forall (regs : bvmap 5 word) l r v, vr_rv regs l -> In (r, v) l -> getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros regs l r v H Hin. exact (proj1 (Forall_forall _ _) H (r, v) Hin). Qed.
Lemma rv_keep : forall (regs regs' : bvmap 5 word) l, vr_rv regs l -> aregs_preserved regs regs' ->
Forall (fun rv => acallee_saved (fst rv)) l -> vr_rv regs' l.
Proof.
intros regs regs' l H HP Hc. unfold vr_rv in *. rewrite Forall_forall in *. intros [r v] Hin.
cbn [fst snd]. rewrite (HP r (Hc (r, v) Hin)). exact (H (r, v) Hin).
Qed.
Lemma sv_atom : forall (regs : bvmap 5 word) n (r : bv 5) v, Z.of_nat n = bv_unsigned r -> getr regs r = w64 v ->
sv_denot (Eimg (Ereg regs [])) (SOff n 0) = w64 v.
Proof. intros regs n r v Hn Hr. cbn [sv_denot]. rewrite (ew_seed regs n r Hn), Hr, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma stk_ge : ASTACK + 208 <= VERBS_RECEIVE_STK /\ 4 * ESTACK + 208 <= VERBS_RECEIVE_STK.
Proof.
unfold VERBS_RECEIVE_STK. pose proof (Z.le_max_r VR_CALLEE_STK (Z.max ASTACK (4 * ESTACK))).
pose proof (Z.le_max_l ASTACK (4 * ESTACK)). pose proof (Z.le_max_r ASTACK (4 * ESTACK)). lia.
Qed.
Lemma astr_agree : forall (rd rd' : reader) p s, astr_atR rd p s ->
(forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (p + i) = rd (p + i)) -> astr_atR rd' p s.
Proof.
intros rd rd' p s [H1 H2] Hk. split; [|exact H2]. intros i Hi. rewrite Hk; [exact (H1 i Hi)|].
rewrite length_app in Hi. cbn [length] in Hi. lia.
Qed.
Lemma rdword_agree : forall (rd rd' : reader) a v, rdword rd a = Some v ->
(forall k, 0 <= k < 8 -> rd' (a + k) = rd (a + k)) -> rdword rd' a = Some v.
Proof. intros rd rd' a v H Hk. rewrite (rdword_ext rd rd' a Hk). exact H. Qed.
Lemma spill_agree : forall e (W W' : world SEGS) m m' l, vr_spill e W m l ->
(forall ov k, In ov l -> 0 <= k < 8 -> rdW W' m' (vr_s1 e + fst ov + k) = rdW W m (vr_s1 e + fst ov + k)) ->
vr_spill e W' m' l.
Proof.
intros e W W' m m' l H Hk. unfold vr_spill in *. rewrite Forall_forall in *. intros ov Hin.
apply (aval_mem_agree _ _ _ _ _ (H ov Hin)). intros k Hk8. apply Hk; [exact Hin | lia].
Qed.

Lemma vr_l_range : forall n D, 0 <= n -> 0 <= vr_l n D <= n.
Proof.
intros n D Hn. unfold vr_l, StrFun.strnlen_res. destruct (StrFun.find_byte 0 (firstn (Z.to_nat n) D)) as [i|] eqn:Fb; [|lia].
destruct (StrFun.find_byte_Some _ _ _ Fb) as (Hl & _). rewrite length_firstn in Hl. lia.
Qed.
Ltac s4reg HS r Hr :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v in Hr
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v in Hr
end.
Ltac inlist := cbn [vr_base vr_rl2 vr_rl4e vr_rl4t vr_sl1 vr_sl2 vr_sl3 app In]; repeat first [left; reflexivity | right].
(* a word the run stored, read back from the symbolic state's chunk *)
Lemma s4_chunk_aval : forall (W : world SEGS) E ss ms i rg p off e a v,
st_ok SEGS E ss (restrict (w_H W) ms) -> nth_error (ss_mem ss) i = Some rg -> YP09.r_base rg = Some p ->
In (YP09.mkChunk off (CVal 8 e)) (YP09.r_chunks rg) -> bv_unsigned (ew E p) = a ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
aval_mem (rdW W (ms_mem ms)) (a + off) 8 v.
Proof.
intros W E ss ms i rg p off e a v HS Hi Hb Hin Hp He Hv.
pose proof (mem_ok_region SEGS E (ms_mem (restrict (w_H W) ms)) (ss_mem ss) rg (st_ok_mem_ok SEGS E ss _ HS)
  ltac:(eapply nth_error_In; exact Hi)) as HR.
destruct HR as (_ & _ & _ & Hcs). rewrite Hb in Hcs. cbn [base_val] in Hcs. rewrite Hp in Hcs.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc.
pose proof (val_of_chunk_ok SEGS E _ a off 8 e v Hc He ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(lia)) as HV.
exact (aval_of_val SEGS (w_H W) (ms_mem ms) (a + off) 8 v HV).
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Variables PC_STRDUP_RA0 : Z.
Hypothesis ASTRDUP : RtAlloc04.astrdup04_rule SEGS B MT (SIGMA CS___interceptor_trampoline_strdup) PC_STRDUP_RA0.
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

(* the state after strdup returns, 0x8d07c: the copy block (c, |line| + 1) holds the line, q is spilled at s1+56 *)
Definition s4_cmn (e : vrE) (pos F q c : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
  (mdc : Model) (k nm : Z) : Prop :=
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  lyc Sc Wc memc mdc k /\
k <= 2 /\ vr_meter MT e Sc k nm /\ nm <= 2 /\
s4_st B e pos F q lyc Sc Wc memc /\
~ In (e_data e, Z.max (e_n e) 1) (e_O e) /\
Permutation (ablocks B lyc Sc) (e_O e ++ [vr_lb e q; vr_cb e c] ++ e_rest e) /\
vr_fresh B e (vr_cb e c) /\ ~ In (vr_cb e c) (e_O e) /\ vr_cb e c <> vr_lb e q.
Definition s4_P1 (e : vrE) (W : world SEGS) (cf : config) : Prop :=
exists pos F q c lyc Sc regs memc mdc k nm,
cf = cfg_at SEGS (vr_pc 0x8d07c) regs memc mdc /\
s4_cmn e pos F q c lyc Sc W memc mdc k nm /\
vr_rv regs (vr_base B e ++ vr_rl2 e F q ++ [(10, c)]) /\
vr_spill e W memc [(56, q); (72, F)] /\
abytes_atR (rdW W memc) c (Verbs.line (e_D e) ++ [Z_to_bv 8 0]) /\
rdword (rdW W memc) (F + 608) = Some 0.

(* the footprint bytes of the call lie below the allocation ceiling *)
Lemma fp_low : forall e, (forall pn, In pn (e_O e) -> In pn (ablocks B (e_ly e) (e_S e))) ->
AR SEGS B (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) -> forall a, inFP (vr_fp e) a -> a < alloc_ceiling.
Proof.
intros e HO HAR a (r & Hin & Hr). pose proof asan_consts as (C1 & _).
unfold vr_fp, VERBS_RECEIVE_PG in Hin. apply in_app_or in Hin as [Hin | Hin].
- unfold A_G_REC, A_REC_SPILL, A_G_QUITTING, REC_SIZE, SC_SIZE in Hin.
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; lia.
- unfold ablocks_fp in Hin. apply in_map_iff in Hin as ([p n] & <- & Hpn).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HO _ Hpn)) as (_ & _ & Hc & _). cbn [fst snd] in Hr. lia.
Qed.

Lemma s4_A : forall e W cf, vr_ent B MT e -> vr_b3 B MT e W cf -> SRr SEGS W cf (s4_P1 e).
Proof.
intros e W cf Hent Hb3.
destruct Hb3 as (pos & F & q & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hcore & Hline & Hsave0).
destruct Hcore as (HJ & Hk & HM & Hnm & HVF & HRg & HSv & HSp & HEnv & HRec & HNd & HPm & HQ).
pose proof Hent as Hent0. unfold vr_ent in Hent; cbv zeta in Hent.
destruct Hent as (HPRE & HAROe & H10e & Hafobj & Hfd & Hdata & Hnv & Hn & HDn & Hdin & HdO & HDb & Hmsg & HRecE &
  Hcalls & Hans & Hrep & Hnrep & Hrefuse & HPmE & HQe & Hgot & Hro & HroIn & HVO & Herr & Hflag & Hguard & Hfr4 &
  Hnev & Hlive & Hmo & Hfrm0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof stk_ge as [Hstk1 Hstk2]. assert (HAS : ASTACK = 16384) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & Hnev' & Hk0 & HJ1 & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
destruct (s1_shape e Hal16) as [Hs1 Hs1al].
assert (Hs1r : vr_sp0 e - 208 <= vr_s1 e <= vr_sp0 e - 192) by lia.
assert (RG : forall r v, In (r, v) (vr_base B e ++ vr_rl2 e F q) -> getr regsc (Z_to_bv 5 r) = w64 v)
  by (intros r v Hin; exact (rv_get regsc _ r v HRg Hin)).
pose proof (RG 2 (vr_s1 e) ltac:(inlist)) as R2. pose proof (RG 3 (as_gp B) ltac:(inlist)) as R3.
pose proof (RG 4 (as_tp B) ltac:(inlist)) as R4. pose proof (RG 8 (vr_sp0 e) ltac:(inlist)) as R8.
pose proof (RG 9 (vr_s1 e) ltac:(inlist)) as R9. pose proof (RG 18 q ltac:(inlist)) as R18.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regsc []))) by apply Eimg_env.
assert (HAE : env_agree 32 (Ereg regsc []) (Eimg (Ereg regsc [])))
  by (split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E9 : bv_unsigned (ew (Eimg (Ereg regsc [])) 9) = vr_s1 e)
  by (rewrite (ew_seed regsc 9 (Z_to_bv 5 9) eq_refl), R9; apply unsigned_lit_small; lia).
unfold cfg_at, vr_pc. change (w64 (BASE + (AF_verbs_receive + (0x8d070 - 0x8ce4c)))) with (Z_to_bv 64 (BASE + 27456)).
(* 0x8d070 .. 0x8d078: q spilled at s1 + 56 (B-only), the call of strdup(q) *)
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regsc [])) (s4_ss 27456 [s4_stk])
  (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 27456)) memc (seg_rom SEGS)))).
{ apply s4_seed; [vm_compute; reflexivity | | cbn; tauto].
  constructor; [|constructor]. unfold region_ok, s4_stk.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
paj_run_shc RUNP RUNC HS HJ.
{ change (ss_mem (s4_ss 27456 [s4_stk])) with [s4_stk].
  eapply awr_ok_cons_gen with (b := vr_s1 e); [reflexivity | exact E9 | | apply awr_ok_nil].
  intros a Ha. cbn [s4_stk YP09.r_wlo YP09.r_whi] in Ha. left. lia. }
set (md1 := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody md1.
(* the registers at the call of strdup *)
s4reg HS (10%bv : bv 5) Q10. s4reg HS (1%bv : bv 5) Q1. s4reg HS (2%bv : bv 5) Q2.
s4reg HS (3%bv : bv 5) Q3. s4reg HS (4%bv : bv 5) Q4. s4reg HS (8%bv : bv 5) Q8.
rewrite (sv_atom regsc 18 (Z_to_bv 5 18) q eq_refl R18) in Q10.
rewrite (sv_atom regsc 2 (Z_to_bv 5 2) _ eq_refl R2) in Q2.
rewrite (sv_atom regsc 3 (Z_to_bv 5 3) _ eq_refl R3) in Q3.
rewrite (sv_atom regsc 4 (Z_to_bv 5 4) _ eq_refl R4) in Q4.
rewrite (sv_atom regsc 8 (Z_to_bv 5 8) _ eq_refl R8) in Q8.
change (SOff 240 27468) with (SOff A_TEXT 27468) in Q1. rewrite (codeptr_val _ 27468 HEI) in Q1.
assert (HP1 : aregs_preserved regsc (ms_regs ms))
  by (eapply aregs_preserved_of_st_ok; [exact HS | exact HAE | vm_compute; reflexivity]).
assert (Hsp1 : spZ (ms_regs ms) = vr_s1 e) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
(* the memory: the run wrote only the spill slot s1 + [56, 64) *)
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (vr_s1 e + 56 <= a < vr_s1 e + 64) -> rdW W (ms_mem ms) a = rdW W memc a).
{ intros a Ha Hnw. apply (aview_of_frame SEGS _ _ (w_H W) memc (ms_mem ms) HFr a Ha). intros (r & Hin & Hr).
  change (ss_mem (s4_ss 27456 [s4_stk])) with [s4_stk] in Hin. destruct Hin as [<- | []].
  cbn [s4_stk YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E9 in Hr. lia. }
pose proof HJ as (HAR1 & _).
assert (Hlb : In (vr_lb e q) (ablocks B lyc Sc))
  by (apply (Permutation_in _ (Permutation_sym HPm)); apply in_or_app; right; left; reflexivity).
assert (HOin : forall pn, In pn (e_O e) -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym HPm)); apply in_or_app; left; exact Hpn).
pose proof (line_le_l (e_D e)) as Hll. rewrite HDn in Hll.
pose proof (vr_l_range (e_n e) (e_D e) ltac:(lia)) as Hlr.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hlb) as (_ & Hq4096 & Hqc & _ & _ & _ & Hqn).
cbn [fst snd vr_lb] in Hq4096, Hqc, Hqn.
pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(lia)) as [_ Hrl].
(* the line q, spilled at s1 + 56 by the run (0x8d070) *)
assert (S56 : aval_mem (rdW W (ms_mem ms)) (vr_s1 e + 56) 8 q).
{ eapply (s4_chunk_aval W _ _ ms 0%nat _ 9%nat 56 (SOff 18 0) (vr_s1 e) q HS); [reflexivity | reflexivity | | exact E9 |
    exact (sv_atom regsc 18 (Z_to_bv 5 18) q eq_refl R18) | lia].
  cbn [YP09.r_chunks In]. repeat first [left; reflexivity | right]. }
destruct HEnv as (HARO & _).
assert (HlineT : astr_atR (rdW W (ms_mem ms)) q (Verbs.line (e_D e))).
{ destruct Hline as [_ HL]. apply (astr_agree _ _ _ _ HL). intros i Hi. apply KF; lia. }
assert (HRD : aread_ok SEGS ASTACK W (ms_regs ms) (ms_mem ms) q (astr_len (Verbs.line (e_D e)) + 1)).
{ apply (aread_ok_of_block SEGS B LAWS ASTACK lyc Sc W (ms_regs ms) (ms_mem ms) md1 q (vr_l (e_n e) (e_D e) + 1));
  [exact HAR1 | exact Hlb | lia | unfold astr_len; lia | unfold astr_len; lia | rewrite Hsp1; lia]. }
assert (HAROm : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms))).
{ apply (aro_keep B RRO _ _ HARO). intros a Hi _ _. pose proof (pa_img_range a Hi). apply KF; lia. }
pose proof (vr_rtrom_ok B W (ms_mem ms) HAROm) as HROM.
assert (HDK : forall a, q <= a < q + (astr_len (Verbs.line (e_D e)) + 1) -> RtAlloc.adup_src_kept SEGS B lyc Sc a).
(* the source is the line block: not the errno cell (HB places it at 0x5e4074, in the image, and a block lies off the
   image, blk_off_imgP), and a live block *)
{ intros a Ha. unfold astr_len in Ha. split.
  - intros He. unfold aerrno_cell in He. rewrite (YF0m.ts_errno B HB) in He. unfold YF0m.TFIB_ERRNO in He.
    pose proof (blk_off_imgP B lyc Sc W memc mdc _ _ HAR Hlb) as Hoff. unfold off_img in Hoff. cbn [fst snd vr_lb] in Hoff.
    lia.
  - right; right. exists q, (vr_l (e_n e) (e_D e) + 1). split; [exact Hlb | lia]. }
assert (HBB : blocks_bytes Sc + (astr_len (Verbs.line (e_D e)) + 1) <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B lyc Sc), (bsum_perm _ _ HPm).
  rewrite (blocks_bytes_bsum B (e_ly e) (e_S e)), (bsum_perm _ _ HPmE) in Hlive.
  rewrite !bsum_app, bsum_cons in *. replace (bsum []) with 0 in * by reflexivity. cbn [vr_lb snd] in *.
  unfold LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ in Hlive. unfold astr_len. lia. }
pose proof (meter_ok_dup B MT MTL e Sc k nm (astr_len (Verbs.line (e_D e)) + 1) Hent0 HM ltac:(lia)
  ltac:(unfold astr_len, VERBS_RECEIVE_REQ; lia)) as HMO.
(* the frame-pointer chain at the call *)
pose proof HPRE as (HARe & Hrae & Hra4e & Hgpe & Htpe & Hstke & Hprese & Hche & HQTe).
assert (HOe : forall pn, In pn (e_O e) -> In pn (ablocks B (e_ly e) (e_S e)))
  by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ pn HRecE Hpn)).
assert (Kup : forall a, vr_sp0 e <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW (e_W e) (e_mem e) a).
{ intros a Ha. rewrite KF by lia. apply HJ1; [lia | lia |]. intros Hf. pose proof (fp_low e HOe HARe a Hf). lia. }
pose proof (HSv 0%nat 1 eq_refl) as SV0. pose proof (HSv 1%nat 8 eq_refl) as SV1.
replace (vr_sp0 e - 8 - 8 * Z.of_nat 0) with (vr_sp0 e - 8) in SV0 by lia.
replace (vr_sp0 e - 8 - 8 * Z.of_nat 1) with (vr_sp0 e - 16) in SV1 by lia.
assert (EZ1 : Z_to_bv 5 1 = (1%bv : bv 5)) by (apply bv_eq; reflexivity).
assert (EZ8 : Z_to_bv 5 8 = (8%bv : bv 5)) by (apply bv_eq; reflexivity).
rewrite EZ1 in SV0. rewrite EZ8 in SV1.
assert (Hra64 : forall r : word, 0 <= bv_unsigned r < 2 ^ 64)
  by (intros r; pose proof (bv_unsigned_in_range 64 r) as HR; change (bv_modulus 64) with (2 ^ 64) in HR; exact HR).
assert (RW0 : rdword (rdW W (ms_mem ms)) (vr_sp0 e - 8) = Some (raZ (e_regs e))).
{ apply rdword_of_aval; [|apply Hra64]. apply (aval_mem_agree _ _ _ _ _ SV0). intros kk Hkk. apply KF; lia. }
assert (RW1 : rdword (rdW W (ms_mem ms)) (vr_sp0 e - 16) = Some (s0Z (e_regs e))).
{ apply rdword_of_aval; [|apply Hra64]. apply (aval_mem_agree _ _ _ _ _ SV1). intros kk Hkk. apply KF; lia. }
pose proof pa_B_ok as HBASE.
destruct (s4_chain (e_ly e) (rdW (e_W e) (e_mem e)) (vr_sp0 e) (s0Z (e_regs e)) (e_ch e) lyc (rdW W (ms_mem ms))
  (ms_regs ms) (raZ (e_regs e)) Hche) as (ch & Hch).
{ pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
{ lia. } { exact Kup. } { exact RW0. } { exact RW1. } { exact Hra4e. } { lia. }
{ pose proof (Z.div_mod (vr_sp0 e) 16 ltac:(lia)). rewrite Z.mod_divide by lia. exists (2 * (vr_sp0 e / 16)). lia. }
{ rewrite Hsp1. lia. } { rewrite Hsp1. lia. }
{ unfold s0Z. rewrite Q8. unfold w64. apply unsigned_lit_small. lia. }
{ unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia. }
pmkst HS.
eapply SRr_bind.
{ eapply (ASTRDUP W (ms_regs ms) (ms_mem ms) VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e)
    (e_md e) [(4, pos)] lyc Sc md1 k q (Verbs.line (e_D e)) (vr_s1 e - vr_sp0 e) (getr (ms_regs ms) 1) ch HJ Q10).
  - lia.
  - exact HlineT.
  - exact HRD.
  - exact HDK.
  - exact HROM.
  - unfold astr_len, MALLOC_MAX. lia.
  - exact HBB.
  - rewrite Hsp1. lia.
  - destruct Hs1 as [E1 | E1]; rewrite E1;
    [replace (vr_sp0 e - 192 - vr_sp0 e) with (-192) by lia | replace (vr_sp0 e - 208 - vr_sp0 e) with (-208) by lia];
    reflexivity.
  - lia.
  - lia.
  - exact Q3.
  - exact Q4.
  - reflexivity.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - pose proof (ev_vr_ge (e_R e) (e_D e)). lia.
  - exact Hch.
  - exact HMO. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & c & -> & HJ2 & HP2 & H10' & Hfr2 & Hc4096 & Hab2 & Hkept & Hbytes & Hmo2).
apply SRr_ret.
unfold astr_len in Hab2, Hkept, Hbytes, Hmo2.
pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & _).
assert (Hcb2 : In (vr_cb e c) (ablocks B ly2 S2)) by (rewrite Hab2; apply in_or_app; right; left; reflexivity).
assert (Hcnew : ~ In (vr_cb e c) (ablocks B lyc Sc)) by exact (blk_new B _ _ _ _ _ _ _ HAR2 Hab2).
assert (Hinc : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly2 S2))
  by (intros pn Hpn; rewrite Hab2; apply in_or_app; left; exact Hpn).
assert (Hcl : vr_cb e c <> vr_lb e q) by (intros E; apply Hcnew; rewrite E; exact Hlb).
assert (HcO : ~ In (vr_cb e c) (e_O e)) by (intros Hin; apply Hcnew; exact (HOin _ Hin)).
assert (EF2 : forall cid p, frame_addr ly2 cid p = frame_addr lyc cid p).
{ intros cid p. unfold frame_addr. pose proof Hly as (_ & _ & _ & _ & _ & EFa & _).
  pose proof Hly2 as (_ & _ & _ & _ & _ & EFb & _). rewrite EFa, EFb. reflexivity. }
assert (EG2 : forall cid p, flag_addr ly2 cid p = flag_addr lyc cid p).
{ intros cid p. unfold flag_addr. pose proof Hly as (_ & _ & _ & _ & _ & EFa & _).
  pose proof Hly2 as (_ & _ & _ & _ & _ & EFb & _). rewrite EFa, EFb. reflexivity. }
pose proof HVF as (EF & _).
assert (Hfr : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
assert (Hshi2 : vr_sp0 e + (vr_s1 e - vr_sp0 e) <= vr_sp0 e - 104) by lia.
assert (KC := keep_call B e pos F q c lyc Sc W (ms_mem ms) ly2 S2 W2 mem2 md2 _ _ Hkept HAR2 Hinc Hfr
  Hfr2 EF (eq_trans (EF2 4 pos) (eq_sym EF)) Hlb Hcb2 Hcl HcO HOin Hll ltac:(lia) ltac:(lia) Hshi2).
assert (Hfr2' : In (4, pos) (frames S2)) by (rewrite Hfr2; exact Hfr).
assert (EFF2 : F = frame_addr ly2 4 pos) by (rewrite EF2; exact EF).
assert (KD : forall a, s4_keepset B e F q a -> (0 <= a < alloc_ceiling \/ vr_sp0 e - 104 <= a < vr_sp0 e)).
{ intros a Ha. exact (proj1 (keep_disj B e pos F q c ly2 S2 W2 mem2 md2 a HAR2 Hfr2' EFF2 (Hinc _ Hlb) Hcb2 Hcl HcO
    (fun pn H => Hinc _ (HOin pn H)) Hll ltac:(lia) Ha)). }
assert (KS : forall a, s4_keepset B e F q a -> rdW W2 mem2 a = rdW W memc a).
{ intros a Ha. rewrite (KC a Ha). destruct (KD a Ha) as [Hl | Hl]; apply KF; lia. }
assert (Hst0 : s4_st B e pos F q lyc Sc W memc) by exact (conj HVF (conj HSv (conj HARO (conj HRec (conj HQ Hline))))).
assert (Hst2 : s4_st B e pos F q ly2 S2 W2 mem2).
{ apply (s4_st_keep B RRO PROGU e pos F q lyc Sc W memc ly2 S2 W2 mem2 Hst0 (EF2 4 pos) (EG2 4 pos)); [|exact KS].
  intros pn Hpn _. exact (Hinc _ (HOin _ Hpn)). }
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR Hfr) as (HF0 & HFc & _).
change (fs_frame_bytes 4) with 1024 in HFc. rewrite <- EF in HF0, HFc.
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 _ _ 4 pos HAR2 Hcb2 Hfr2') as Hcf.
unfold zdisjoint in Hcf. cbn [fst snd vr_cb] in Hcf. change (fs_frame_bytes 4) with 1024 in Hcf. rewrite <- EFF2 in Hcf.
exists pos, F, q, c, ly2, S2, regs2, mem2, md2, (k + 1), (nm + 1).
split; [unfold cfg_at, vr_pc; rewrite Q1; reflexivity|].
split.
{ split; [exact HJ2|]. split; [lia|].
  split; [exact (meter_malloc MT MTL e Sc S2 k nm _ HM Hmo2 ltac:(unfold VERBS_RECEIVE_REQ; lia))|].
  split; [lia|]. split; [exact Hst2|]. split; [exact HNd|]. split.
  - rewrite Hab2. eapply Permutation_trans; [apply Permutation_app_tail; exact HPm|].
    rewrite <- !app_assoc. apply Permutation_app_head. cbn. apply perm_skip. apply Permutation_sym, Permutation_cons_append.
  - split; [split; [cbn [fst vr_cb]; lia|]|].
    { intros Hin. apply Hcnew. apply (Permutation_in _ (Permutation_sym HPm)). apply (Permutation_in _ HPmE) in Hin.
      apply in_app_or in Hin as [H1|H1]; apply in_or_app; [left; exact H1 | right; right; exact H1]. }
    split; [exact HcO | exact Hcl]. }
split.
{ unfold vr_rv. rewrite app_assoc. apply Forall_app. split.
  - apply (rv_keep regsc regs2 _ HRg (aregs_preserved_trans _ _ _ HP1 HP2)).
    unfold vr_base, vr_rl2. (repeat apply Forall_cons); try (apply Forall_nil); cbn [fst]; unfold acallee_saved; lia.
  - constructor; [|constructor]. cbn [fst snd].
    replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity). exact H10'. }
split.
{ apply (spill_agree e W W2 (ms_mem ms) mem2 [(56, q); (72, F)]).
  - unfold vr_spill. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
    + exact S56.
    + assert (S72 : aval_mem (rdW W memc) (vr_s1 e + 72) 8 F)
        by (unfold vr_spill in HSp; exact (proj1 (Forall_forall _ _) HSp (72, F) ltac:(cbn [vr_sl1 In]; left; reflexivity))).
      apply (aval_mem_agree _ _ _ _ _ S72). intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KF; lia.
  - intros ov kk Hin Hk8. destruct Hkept as (K1 & _). cbn [In] in Hin.
    destruct Hin as [<- | [<- | []]]; cbn [fst]; apply K1; lia. }
split; [exact Hbytes|].
destruct Hkept as (_ & _ & _ & K4 & _).
apply (rdword_agree (rdW W memc)); [exact Hsave0|]. intros kk Hkk.
rewrite (K4 4 pos (F + 608 + kk) Hfr).
- apply KF; lia.
- left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 4) with 1024. rewrite <- EF. lia.
- cbv beta. lia.
Qed.

End e.
End f.
End d.
