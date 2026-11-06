(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S04 (TOK, 0x8d070-0x8d0f0) of the walk of verbs_receive on the ASan+UBSan
   build of plugin-hostd/fuzz_command, ported from the ASan walk's lib/A/Prog/verbs_receive_s04_l.v: the word loop
   (head 0x8d0c8, back edge 0x8d0f0). At the head of pass j the j words before are stored in tok[0..j) of the
   side-stack frame and the current word is in a0; a pass (`mv s4,s5; addi s5,s5,1; sd a0,0(s6)`) stores it in tok[j]
   (s6 = &tok[j]), calls strtok_r(NULL, " \t", &save) for the next word (verbs_receive_s04_t.v s4_tok_call), counts
   it in s9 (`addiw s9,s9,1`), and leaves for the dispatch 0x8d0f4 (no word left, or 64 words stored) or goes back
   to the head (`addi s6,s6,8; bltu s4,s7` with s7 = 63). One lemma proves a pass at any j; the passes are chained by
   induction on the passes left. The loop invariant is the plain proof's linv (lib/Prog/verbs_receive_tok.v:451-458)
   over the ASan reader. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_s04_k verbs_receive_s04_a verbs_receive_s04_t.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the words stored so far: tok[i] at F + 32 + 8 i points to word i, a string in the copy block ending by lim *)
Definition s4_toks (rd : reader) (F c lim : Z) (ps : list Z) (ws : list (list byte)) : Prop :=
length ps = length ws /\
(forall i q, nth_error ps i = Some q -> aval_mem rd (F + 32 + 8 * Z.of_nat i) 8 q) /\
(forall i q w, nth_error ps i = Some q -> nth_error ws i = Some w ->
  astr_atR rd q w /\ c <= q /\ q + Z.of_nat (length w) + 1 <= lim).

Lemma s4_toks_nil : forall rd F c lim, s4_toks rd F c lim [] [].
Proof. intros rd F c lim. split; [reflexivity|]. split; intros [|i]; discriminate. Qed.

Lemma s4_toks_keep : forall (rd rd' : reader) F c lim lim' ps ws, s4_toks rd F c lim ps ws -> lim <= lim' ->
(forall a, F + 32 <= a < F + 32 + 8 * Z.of_nat (length ps) -> rd' a = rd a) ->
(forall a, c <= a < lim -> rd' a = rd a) -> s4_toks rd' F c lim' ps ws.
Proof.
intros rd rd' F c lim lim' ps ws (HL & HA & HS) Hlim Ht Hs. split; [exact HL|]. split.
- intros i q Hq. assert (Hi : (i < length ps)%nat) by (apply nth_error_Some; rewrite Hq; discriminate).
  apply (aval_mem_agree _ _ _ _ _ (HA i q Hq)). intros kk Hkk. apply Ht. change (Z.of_nat 8) with 8 in Hkk. lia.
- intros i q w Hq Hw. destruct (HS i q w Hq Hw) as (Hs1 & Hc & Hl).
  split; [|split; [exact Hc | lia]].
  apply (astr_atR_agree rd rd' q w (Z.of_nat (length w) + 1) Hs1); [lia|]. intros kk Hkk. apply Hs. lia.
Qed.

Lemma s4_toks_snoc : forall rd F c lim ps ws q w, s4_toks rd F c lim ps ws ->
aval_mem rd (F + 32 + 8 * Z.of_nat (length ps)) 8 q -> astr_atR rd q w -> c <= q ->
q + Z.of_nat (length w) + 1 <= lim -> s4_toks rd F c lim (ps ++ [q]) (ws ++ [w]).
Proof.
intros rd F c lim ps ws q w (HL & HA & HS) Hq Hw Hc Hl.
split; [rewrite !length_app, HL; reflexivity|]. split.
- intros i q' Hq'. destruct (Nat.lt_ge_cases i (length ps)) as [Hi | Hi].
  + rewrite nth_error_app1 in Hq' by lia. exact (HA i q' Hq').
  + rewrite nth_error_app2 in Hq' by lia. destruct (i - length ps)%nat as [|t] eqn:Et.
    * cbn in Hq'. injection Hq' as <-. replace i with (length ps) by lia. exact Hq.
    * cbn in Hq'. destruct t; discriminate.
- intros i q' w' Hq' Hw'. destruct (Nat.lt_ge_cases i (length ps)) as [Hi | Hi].
  + rewrite nth_error_app1 in Hq' by lia. rewrite nth_error_app1 in Hw' by lia. exact (HS i q' w' Hq' Hw').
  + rewrite nth_error_app2 in Hq' by lia. rewrite nth_error_app2 in Hw' by lia. rewrite <- HL in Hw'.
    destruct (i - length ps)%nat as [|t] eqn:Et.
    * cbn in Hq', Hw'. injection Hq' as <-. injection Hw' as <-. split; [exact Hw|]. split; [exact Hc | exact Hl].
    * cbn in Hq'. destruct t; discriminate.
Qed.

Lemma s4_firstn_S : forall {A} (l : list A) n x, nth_error l n = Some x -> firstn (S n) l = firstn n l ++ [x].
Proof.
intros A l. induction l as [|y l IH]; intros n x H; [destruct n; discriminate|].
destruct n as [|n]; cbn in H |- *; [injection H as <-; reflexivity|]. rewrite (IH n x H). reflexivity.
Qed.
Lemma s4_nth_skipn : forall {A} (l : list A) n x y, skipn n l = x :: y -> nth_error l n = Some x /\ skipn (S n) l = y.
Proof.
intros A l n x y H. split.
- rewrite <- (Nat.add_0_r n), <- nth_error_skipn, H. reflexivity.
- replace (S n) with (1 + n)%nat by lia. rewrite <- skipn_skipn, H. reflexivity.
Qed.
Lemma s4_len_of_skipn : forall {A} (l : list A) n x, nth_error l n = Some x -> skipn (S n) l = [] -> length l = S n.
Proof.
intros A l n x H1 H2. pose proof (nth_error_Some l n) as [Hs _]. rewrite H1 in Hs. specialize (Hs ltac:(discriminate)).
apply (f_equal (@length A)) in H2. rewrite length_skipn in H2. cbn in H2. lia.
Qed.

Lemma s4_rem_agree : forall (rd rd' : reader) c n C ws, s4_rem rd c n C ws ->
(C <> 0 -> forall a, C <= a < c + n -> rd' a = rd a) -> s4_rem rd' c n C ws.
Proof.
intros rd rd' c n C ws [H0 | (r & Hr0 & Hr & Hcr & Hrn & Hw)] Hk; [left; exact H0|].
right. exists r. split; [exact Hr0|]. split; [|split; [exact Hcr | split; [exact Hrn | exact Hw]]].
apply (astr_atR_agree rd rd' C r (Z.of_nat (length r) + 1) Hr); [lia|]. intros kk Hkk. apply (Hk Hr0). lia.
Qed.

(* the words tokens of a line: the first 64 words *)
Lemma s4_atoks : forall rd F c n tp tks, s4_toks rd F c (c + n) tp tks -> F mod 64 = 0 -> n <= 8193 ->
atoks_atA rd (F + 32) tp tks c n.
Proof.
intros rd F c n tp tks (HL & HA & HS) H64 Hn.
split; [pose proof (Z.div_mod F 64 ltac:(lia)) as D; replace (F + 32) with ((8 * (F / 64) + 4) * 8) by lia;
  apply Z_mod_mult|].
split; [exact HL|]. split.
- exact HA.
- intros i q w Hq Hw. destruct (HS i q w Hq Hw) as (Hs & Hc & Hl). split; [exact Hs|]. split; [lia|]. split; [exact Hc | lia].
Qed.

Lemma s4_addw1 : forall v, 0 <= v < 2 ^ 31 - 1 ->
sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 v)) (low32 (Z_to_bv 64 1))) = Z_to_bv 64 (v + 1).
Proof.
intros v Hv. rewrite w_addw. unfold v_addw. rewrite !unsigned_lit_small by lia. f_equal.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
rewrite Z.mod_small by lia. lia.
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

Definition s4_WS (e : vrE) : list (list byte) := Verbs.words (Verbs.line (e_D e)).
Definition s4_n (e : vrE) : Z := Z.of_nat (length (Verbs.line (e_D e))) + 1.
(* the registers at the head of pass j (B's allocation): a0 = the current word, s2 = msg >> 3, s5 = s9 = j,
   s6 = &tok[j], s7 = 63, s10 = &save, s11 = " \t" *)
Definition s4_rlL (e : vrE) (F : Z) (j : nat) (p : Z) : list (Z * Z) :=
[(10, p); (18, e_msg e / 8); (19, SHADOW_OFF); (21, Z.of_nat j); (22, F + 32 + 8 * Z.of_nat j); (23, 63);
 (24, e_msg e); (25, Z.of_nat j); (26, F + 608); (27, 0x22500)].
(* the registers at the call of strtok_r in pass j: s4 = j, s5 = j + 1 *)
Definition s4_rlC (e : vrE) (F : Z) (j : nat) : list (Z * Z) :=
[(18, e_msg e / 8); (19, SHADOW_OFF); (20, Z.of_nat j); (21, Z.of_nat j + 1); (22, F + 32 + 8 * Z.of_nat j); (23, 63);
 (24, e_msg e); (25, Z.of_nat j); (26, F + 608); (27, 0x22500)].

Lemma s4_cfg : forall regs mem md pc off, off = AF_verbs_receive + (pc - 0x8ce4c) ->
mkCfg (mkst regs (Z_to_bv 64 (BASE + off)) mem (seg_rom SEGS)) md = cfg_at SEGS (vr_pc pc) regs mem md.
Proof. intros regs mem md pc off Ho. unfold cfg_at, vr_pc, w64. rewrite Ho. reflexivity. Qed.

Lemma s4_sv_off : forall (regs : bvmap 5 word) n (r : bv 5) v c, Z.of_nat n = bv_unsigned r -> getr regs r = w64 v ->
0 <= v < 2 ^ 64 -> sv_denot (Eimg (Ereg regs [])) (SOff n c) = w64 (v + c).
Proof.
intros regs n r v c Hn Hr Hv. cbn [sv_denot]. rewrite (ew_seed regs n r Hn), Hr. unfold w64.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.
Lemma s4_sv_addw1 : forall (regs : bvmap 5 word) n (r : bv 5) v, Z.of_nat n = bv_unsigned r -> getr regs r = w64 v ->
0 <= v < 2 ^ 31 - 1 -> sv_denot (Eimg (Ereg regs [])) (SAluw ALU_ADD (SOff n 0) (SLit 1)) = w64 (v + 1).
Proof.
intros regs n r v Hn Hr Hv. cbn [sv_denot]. rewrite (ew_seed regs n r Hn), Hr. unfold w64.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. apply s4_addw1. lia.
Qed.
Lemma s4_spill_keep : forall e (W : world SEGS) m m' sl, vr_spill e W m sl ->
(forall ov, In ov sl -> 0 <= fst ov <= 72) ->
(forall a, vr_s1 e <= a < vr_s1 e + 80 -> rdW W m' a = rdW W m a) -> vr_spill e W m' sl.
Proof.
intros e W m m' sl H Hsl Hk. apply (spill_agree e W W m m' sl H). intros ov kk Hin Hkk.
pose proof (Hsl ov Hin). apply Hk. lia.
Qed.
Lemma s4_sl3_off : forall F q c ov, In ov (vr_sl3 F q c) -> 0 <= fst ov <= 72.
Proof. intros F q c ov Hin. cbn [vr_sl3 In] in Hin. repeat destruct Hin as [<- | Hin]; cbn [fst]; try lia. Qed.
Lemma s4_toks_D : forall e, Verbs.toks (e_D e) = firstn 64 (s4_WS e).
Proof. intros e. reflexivity. Qed.

Ltac s4in := cbn [vr_base s4_rlL s4_rlC app In]; repeat first [left; reflexivity | right].
Ltac s4reg HS r Hr :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v in Hr
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v in Hr
end.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis STRTOK_R : RtString.astrtok_r_realizes SEGS B (SIGMA CS_strtok_r) 0xa6bf8 0x604158.
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

(* the boundary facts survive a memory change outside the stack below the saves, the side-stack frame's words below
   its flag pointer, and the copy block *)
Lemma s4_cmn_keep : forall e pos F q c lyc Sc W mem md k nm mem' md',
vr_ent B MT e -> s4_cmn B MT e pos F q c lyc Sc W mem md k nm ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  lyc Sc W mem' md' k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (alloc_ceiling <= a < vr_sp0 e - 104) -> ~ (F <= a < F + 1016) ->
  ~ (c <= a < c + req_size (s4_n e)) -> rdW W mem' a = rdW W mem a) ->
s4_cmn B MT e pos F q c lyc Sc W mem' md' k nm.
Proof.
intros e pos F q c lyc Sc W mem md k nm mem' md' Hent Hc HJ' Hk.
destruct Hc as (HJ & Hkk & HM & Hnm & Hst & HNd & HPm & Hfresh & HcO & Hcl).
split; [exact HJ'|]. split; [exact Hkk|]. split; [exact HM|]. split; [exact Hnm|].
split; [|split; [exact HNd|split; [exact HPm|split; [exact Hfresh|split; [exact HcO|exact Hcl]]]]].
apply (s4_st_keep B RRO PROGU e pos F q lyc Sc W mem lyc Sc W mem' Hst eq_refl eq_refl (fun pn _ H => H)).
intros a Ha.
pose proof Hent as Hent'. unfold vr_ent in Hent'; cbv zeta in Hent'.
destruct Hent' as (_ & _ & _ & _ & _ & _ & _ & Hn & HDn & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hst as ((EF & _) & _).
assert (HSTK : VERBS_RECEIVE_STK = ltac:(let v := eval vm_compute in VERBS_RECEIVE_STK in exact v)) by reflexivity.
assert (Hfr : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
assert (Hlb : In (vr_lb e q) (ablocks B lyc Sc))
  by (apply (Permutation_in _ (Permutation_sym HPm)); apply in_or_app; right; left; reflexivity).
assert (Hcb : In (vr_cb e c) (ablocks B lyc Sc))
  by (apply (Permutation_in _ (Permutation_sym HPm)); apply in_or_app; right; right; left; reflexivity).
assert (HOin : forall pn, In pn (e_O e) -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym HPm)); apply in_or_app; left; exact Hpn).
pose proof (line_le_l (e_D e)) as Hll. rewrite HDn in Hll.
destruct (keep_disj B e pos F q c lyc Sc W mem md a HAR Hfr EF Hlb Hcb Hcl HcO HOin Hll ltac:(lia) Ha)
  as (Hlow & Hnf & Hnc).
pose proof asan_consts as (C1 & _).
apply Hk; [clear Hk HOin; lia | clear Hk HOin; lia | exact Hnf | exact Hnc].
Qed.

(* the boundary facts and the registers and spill slots make vr_core *)
Lemma s4_core : forall e pos F q c lyc Sc W regs mem md k nm sl rl,
s4_cmn B MT e pos F q c lyc Sc W mem md k nm -> vr_rv regs (vr_base B e ++ rl) -> vr_spill e W mem sl ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 sl rl (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W regs mem md.
Proof.
intros e pos F q c lyc Sc W regs mem md k nm sl rl Hc Hrv Hsp.
destruct Hc as (HJ & Hkk & HM & Hnm & (HVF & HSv & HARO & HRec & HQ & _) & HNd & HPm & _).
split; [exact HJ|]. split; [exact Hkk|]. split; [exact HM|]. split; [unfold VR_NM_PRE; exact Hnm|].
split; [exact HVF|]. split; [exact Hrv|]. split; [exact HSv|]. split; [exact Hsp|].
split; [exact (env_of_aro B RECC ROA _ _ _ _ _ (proj1 HJ) HARO)|].
split; [exact HRec|]. split; [exact HNd|]. split; [exact HPm | exact HQ].
Qed.

(* the exit to the dispatch, 0x8d0f4 *)
Lemma s4_mk_b4t : forall e pos F q c lyc Sc W regs mem md k nm tp,
vr_ent B MT e -> s4_cmn B MT e pos F q c lyc Sc W mem md k nm ->
vr_rv regs (vr_base B e ++ vr_rl4t e) -> vr_spill e W mem (vr_sl3 F q c) ->
s4_toks (rdW W mem) F c (c + s4_n e) tp (Verbs.toks (e_D e)) -> Verbs.toks (e_D e) <> [] ->
vr_b4t B MT e W (cfg_at SEGS (vr_pc 0x8d0f4) regs mem md).
Proof.
intros e pos F q c lyc Sc W regs mem md k nm tp Hent Hc Hrv Hsp Htk Hne.
pose proof Hent as Hent'. unfold vr_ent in Hent'; cbv zeta in Hent'.
destruct Hent' as (_ & _ & _ & _ & _ & _ & _ & Hn & HDn & _).
pose proof Hc as (HJ & _ & _ & _ & (HVF & _ & _ & _ & _ & HLn) & _ & _ & Hfresh & _).
pose proof HVF as (EF & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfr : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
pose proof (frame_al64 SEGS B lyc Sc W mem md 4 pos HAR Hfr) as (H64 & _). rewrite <- EF in H64.
pose proof (line_le_l (e_D e)) as Hll. rewrite HDn in Hll.
pose proof (vr_l_range (e_n e) (e_D e) ltac:(lia)) as Hlr.
exists pos, F, q, c, tp, lyc, Sc, regs, mem, md, k, nm.
split; [reflexivity|]. split; [exact Hne|]. split; [exact (s4_core e pos F q c lyc Sc W regs mem md k nm _ _ Hc Hrv Hsp)|].
split; [exact HLn|]. split; [exact Hfresh|].
apply (s4_atoks _ F c (s4_n e) tp _ Htk H64). unfold s4_n. lia.
Qed.

(* the exit after word j: j + 1 words cut, and either none is left or 64 are stored *)
Lemma s4_exit : forall e pos F q c lyc Sc W regs mem md k nm ps p w j,
vr_ent B MT e -> s4_cmn B MT e pos F q c lyc Sc W mem md k nm ->
(S j <= 64)%nat -> (S j <= length (s4_WS e))%nat -> (S j = 64%nat \/ length (s4_WS e) = S j) ->
vr_rv regs (vr_base B e ++ [(18, e_msg e / 8); (19, SHADOW_OFF); (21, Z.of_nat j + 1); (24, e_msg e);
  (25, Z.of_nat j + 1)]) ->
vr_spill e W mem (vr_sl3 F q c) ->
s4_toks (rdW W mem) F c (c + s4_n e) ps (firstn j (s4_WS e)) ->
nth_error (s4_WS e) j = Some w -> aval_mem (rdW W mem) (F + 32 + 8 * Z.of_nat j) 8 p ->
astr_atR (rdW W mem) p w -> c <= p -> p + Z.of_nat (length w) + 1 <= c + s4_n e ->
vr_b4t B MT e W (cfg_at SEGS (vr_pc 0x8d0f4) regs mem md).
Proof.
intros e pos F q c lyc Sc W regs mem md k nm ps p w j Hent Hc Hj64 HjW Hcase Hrv Hsp Htk Hw TK Hpw Hcp Hpe.
assert (EF : firstn 64 (s4_WS e) = firstn (S j) (s4_WS e)).
{ destruct Hcase as [E | E]; [rewrite E; reflexivity|]. rewrite !firstn_all2 by lia. reflexivity. }
assert (Hnt : vr_ntok (e_D e) = Z.of_nat j + 1).
{ unfold vr_ntok. rewrite s4_toks_D, EF, length_firstn. lia. }
apply (s4_mk_b4t e pos F q c lyc Sc W regs mem md k nm (ps ++ [p]) Hent Hc).
- unfold vr_rl4t. rewrite Hnt. exact Hrv.
- exact Hsp.
- rewrite s4_toks_D, EF, (s4_firstn_S _ _ _ Hw). pose proof Htk as (HL & _).
  rewrite length_firstn, Nat.min_l in HL by lia.
  apply s4_toks_snoc; [exact Htk | rewrite HL; exact TK | exact Hpw | exact Hcp | exact Hpe].
- rewrite s4_toks_D, EF, (s4_firstn_S _ _ _ Hw). intros H. apply (f_equal (@length _)) in H.
  rewrite length_app in H. cbn in H. lia.
Qed.

(* the head of pass j of the word loop, 0x8d0c8 *)
Definition s4_L (e : vrE) (j : nat) (W : world SEGS) (cf : config) : Prop :=
exists pos F q c lyc Sc regs mem md k nm ps p sv w,
cf = cfg_at SEGS (vr_pc 0x8d0c8) regs mem md /\ (j < 64)%nat /\
s4_cmn B MT e pos F q c lyc Sc W mem md k nm /\
vr_rv regs (vr_base B e ++ s4_rlL e F j p) /\
vr_spill e W mem (vr_sl3 F q c) /\
s4_toks (rdW W mem) F c p ps (firstn j (s4_WS e)) /\
nth_error (s4_WS e) j = Some w /\ astr_atR (rdW W mem) p w /\ c <= p /\
p + Z.of_nat (length w) + 1 = (if sv =? 0 then c + s4_n e else sv) /\
rdword (rdW W mem) (F + 608) = Some sv /\
s4_rem (rdW W mem) c (s4_n e) sv (skipn (S j) (s4_WS e)).

Lemma s4_body : forall e j W cf, vr_ent B MT e -> s4_L e j W cf ->
SRr SEGS W cf (fun W' cf' => vr_b4t B MT e W' cf' \/ ((j < 63)%nat /\ s4_L e (S j) W' cf')).
Proof.
intros e j W cf Hent HL.
destruct HL as (pos & F & q & c & lyc & Sc & regs & mem & md & k & nm & ps & p & sv & w & -> & Hj & Hcmn & Hrv & Hspl
  & Htk & Hw & Hpw & Hcp & Hpe & Hsv & Hrem).
pose proof Hent as Hent'. unfold vr_ent in Hent'; cbv zeta in Hent'.
destruct Hent' as (HPRE & _ & _ & Hafobj & _ & _ & _ & Hn & HDn & _).
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
destruct (al_frames _ _ LAWS lyc Sc W mem md 4 pos HAR Hfr) as (_ & _ & Hfb & _).
change (fs_frame_bytes 4) with 1024 in Hfb. rewrite <- EF in Hfb.
assert (Hcb : In (c, s4_n e) (ablocks B lyc Sc))
  by (apply (Permutation_in _ (Permutation_sym HPm)); apply in_or_app; right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcb) as (_ & Hc4096 & Hcc & _ & _ & _ & Hcn). unfold MALLOC_MAX in Hcn.
pose proof (req_size_pos (s4_n e) ltac:(unfold s4_n; lia)) as [Hrq1 Hrq2].
pose proof (sep_block_frame SEGS B LAWS lyc Sc W mem md _ _ 4 pos HAR Hcb Hfr) as Hcf.
unfold zdisjoint in Hcf. cbn [fst snd] in Hcf. change (fs_frame_bytes 4) with 1024 in Hcf. rewrite <- EF in Hcf.
assert (Hcnew : ~ In (c, s4_n e) (ablocks B (e_ly e) (e_S e))) by exact (proj2 Hfresh).
assert (Hbnd : (if sv =? 0 then c + s4_n e else sv) <= c + s4_n e).
{ destruct Hrem as [(-> & _) | (r & Hr0 & _ & Hcr & Hrn & _)]; [cbn; lia|].
  replace (sv =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hr0). lia. }
(* the registers at the head *)
assert (RG : forall r v, In (r, v) (vr_base B e ++ s4_rlL e F j p) -> getr regs (Z_to_bv 5 r) = w64 v)
  by (intros r v Hin; exact (rv_get regs _ r v Hrv Hin)).
pose proof (RG 2 (vr_s1 e) ltac:(s4in)) as R2. pose proof (RG 3 (as_gp B) ltac:(s4in)) as R3.
pose proof (RG 4 (as_tp B) ltac:(s4in)) as R4. pose proof (RG 8 (vr_sp0 e) ltac:(s4in)) as R8.
pose proof (RG 9 (vr_s1 e) ltac:(s4in)) as R9. pose proof (RG 10 p ltac:(s4in)) as R10.
pose proof (RG 18 _ ltac:(s4in)) as R18. pose proof (RG 19 SHADOW_OFF ltac:(s4in)) as R19.
pose proof (RG 21 _ ltac:(s4in)) as R21. pose proof (RG 22 _ ltac:(s4in)) as R22.
pose proof (RG 23 63 ltac:(s4in)) as R23. pose proof (RG 24 _ ltac:(s4in)) as R24.
pose proof (RG 25 _ ltac:(s4in)) as R25. pose proof (RG 26 _ ltac:(s4in)) as R26.
pose proof (RG 27 _ ltac:(s4in)) as R27.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs []))) by apply Eimg_env.
assert (E22 : bv_unsigned (ew (Eimg (Ereg regs [])) 22) = F + 32 + 8 * Z.of_nat j)
  by (rewrite (ew_seed regs 22 (Z_to_bv 5 22) eq_refl), R22; apply unsigned_lit_small; lia).
unfold cfg_at, vr_pc. change (w64 (BASE + (AF_verbs_receive + (0x8d0c8 - 0x8ce4c)))) with (Z_to_bv 64 (BASE + 27544)).
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (s4_ss 27544 [s4_tokr])
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 27544)) mem (seg_rom SEGS)))).
{ apply s4_seed; [vm_compute; reflexivity | | cbn; tauto].
  constructor; [|constructor]. unfold region_ok, s4_tokr.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E22. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hfb (F + 32 + 8 * Z.of_nat j + o) ltac:(lia))). }
(* 0x8d0c8 .. 0x8d0e0: s4 = j, s5 = j + 1, tok[j] := a0, then the call of strtok_r(NULL, " \t", &save) *)
paj_run_shc RUNP RUNC HS HJ.
{ change (ss_mem (s4_ss 27544 [s4_tokr])) with [s4_tokr].
  eapply awr_ok_cons_gen with (b := F + 32 + 8 * Z.of_nat j); [reflexivity | exact E22 | | apply awr_ok_nil].
  intros a Ha. cbn [s4_tokr YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left.
  exists 4, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 4) with 1024.
  rewrite <- EF. lia. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1.
s4reg HS (10%bv : bv 5) Q10. s4reg HS (11%bv : bv 5) Q11. s4reg HS (12%bv : bv 5) Q12.
s4reg HS (1%bv : bv 5) Q1. s4reg HS (2%bv : bv 5) Q2. s4reg HS (3%bv : bv 5) Q3. s4reg HS (4%bv : bv 5) Q4.
rewrite (sv_atom regs 27 (Z_to_bv 5 27) _ eq_refl R27) in Q11.
rewrite (sv_atom regs 26 (Z_to_bv 5 26) _ eq_refl R26) in Q12.
rewrite (sv_atom regs 2 (Z_to_bv 5 2) _ eq_refl R2) in Q2.
rewrite (sv_atom regs 3 (Z_to_bv 5 3) _ eq_refl R3) in Q3.
rewrite (sv_atom regs 4 (Z_to_bv 5 4) _ eq_refl R4) in Q4.
change (SOff 240 27572) with (SOff A_TEXT 27572) in Q1. rewrite (codeptr_val _ 27572 HEI) in Q1.
assert (Q10' : getr (ms_regs ms) 10%bv = w64 0) by (rewrite Q10; reflexivity).
assert (Hsp1 : spZ (ms_regs ms) = vr_s1 e) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
assert (Hra1 : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]).
(* the registers at the call *)
assert (HrvC : vr_rv (ms_regs ms) (vr_base B e ++ s4_rlC e F j)).
{ unfold vr_rv, vr_base, s4_rlC. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  all: lazymatch goal with
  | |- getr _ (Z_to_bv 5 ?r) = _ =>
    let Q := fresh "Q" in s4reg HS (Z_to_bv 5 r) Q; rewrite Q; clear Q
  end.
  - exact (sv_atom regs 2 (Z_to_bv 5 2) _ eq_refl R2).
  - exact (sv_atom regs 3 (Z_to_bv 5 3) _ eq_refl R3).
  - exact (sv_atom regs 4 (Z_to_bv 5 4) _ eq_refl R4).
  - exact (sv_atom regs 8 (Z_to_bv 5 8) _ eq_refl R8).
  - exact (sv_atom regs 9 (Z_to_bv 5 9) _ eq_refl R9).
  - exact (sv_atom regs 18 (Z_to_bv 5 18) _ eq_refl R18).
  - exact (sv_atom regs 19 (Z_to_bv 5 19) _ eq_refl R19).
  - exact (sv_atom regs 21 (Z_to_bv 5 21) _ eq_refl R21).
  - exact (s4_sv_off regs 21 (Z_to_bv 5 21) _ 1 eq_refl R21 ltac:(lia)).
  - exact (sv_atom regs 22 (Z_to_bv 5 22) _ eq_refl R22).
  - exact (sv_atom regs 23 (Z_to_bv 5 23) _ eq_refl R23).
  - exact (sv_atom regs 24 (Z_to_bv 5 24) _ eq_refl R24).
  - exact (sv_atom regs 25 (Z_to_bv 5 25) _ eq_refl R25).
  - exact (sv_atom regs 26 (Z_to_bv 5 26) _ eq_refl R26).
  - exact (sv_atom regs 27 (Z_to_bv 5 27) _ eq_refl R27). }
(* the memory: the run wrote tok[j] only *)
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 + 8 * Z.of_nat j <= a < F + 32 + 8 * Z.of_nat j + 8) ->
  rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha Hnw. apply (aview_of_frame SEGS _ _ (w_H W) mem (ms_mem ms) HFr a Ha). intros (r & Hin & Hr).
  change (ss_mem (s4_ss 27544 [s4_tokr])) with [s4_tokr] in Hin. destruct Hin as [<- | []].
  cbn [s4_tokr YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E22 in Hr. lia. }
assert (TK : aval_mem (rdW W (ms_mem ms)) (F + 32 + 8 * Z.of_nat j) 8 p).
{ pose proof (s4_chunk_aval W _ _ ms 0%nat (YP09.mkRegion (Some 22%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 10 0))])
    22%nat 0 (SOff 10 0) (F + 32 + 8 * Z.of_nat j) p HS ltac:(reflexivity) ltac:(reflexivity)
    ltac:(cbn; left; reflexivity) E22 (sv_atom regs 10 (Z_to_bv 5 10) p eq_refl R10) ltac:(lia)) as Hc0.
  rewrite Z.add_0_r in Hc0. exact Hc0. }
assert (Hcmn1 : s4_cmn B MT e pos F q c lyc Sc W (ms_mem ms) md1 k nm).
{ apply (s4_cmn_keep e pos F q c lyc Sc W mem md k nm (ms_mem ms) md1 Hent Hcmn HJ).
  intros a Ha H1 H2 H3. apply KF; [exact Ha | lia]. }
pose proof Hcmn1 as (_ & _ & _ & _ & ((_ & _ & Hsh1) & _ & HARO1 & _) & _).
assert (Hsh76 : rdW W (ms_mem ms) (shadow_addr F + 76) = Some 0) by exact (Hsh1 76%nat ltac:(lia)).
assert (Hsv1 : rdword (rdW W (ms_mem ms)) (F + 608) = Some sv).
{ apply (rdword_agree (rdW W mem)); [exact Hsv|]. intros kk Hkk. apply KF; lia. }
assert (Hrem1 : s4_rem (rdW W (ms_mem ms)) c (s4_n e) sv (skipn (S j) (s4_WS e))).
{ apply (s4_rem_agree (rdW W mem)); [exact Hrem|]. intros Hsv0 a Ha.
  destruct Hrem as [(? & _) | (r & _ & _ & Hcr & _)]; [contradiction|]. apply KF; lia. }
pmkst HS.
eapply SRr_bind.
{ exact (s4_tok_call B STRTOK_R RECC SHOK BLKT ROA e pos F c (s4_n e) lyc Sc W (ms_regs ms) (ms_mem ms) md1 k 0 sv sv
    (skipn (S j) (s4_WS e)) HJ EF Hcb Hcnew Hsh76 Hsp1 Q3 Q4 Hra1 Q10' Q11 Q12 Hsv1 eq_refl Hrem1 HARO1). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HK2 & a0 & sv2 & H10' & Hsv2 & Hres).
(* after the call: the registers and the memory *)
assert (HrvC2 : vr_rv regs2 (vr_base B e ++ s4_rlC e F j)).
{ apply (rv_keep (ms_regs ms) regs2 _ HrvC HP2). unfold vr_base, s4_rlC.
  (repeat apply Forall_cons); try (apply Forall_nil); cbn [fst]; unfold acallee_saved; lia. }
assert (Hcsv : sv <> 0 -> c <= sv)
  by (intros H0; destruct Hrem as [(? & _) | (r & _ & _ & Hcr & _)]; [contradiction | exact Hcr]).
assert (Hpe1 : sv <> 0 -> p + Z.of_nat (length w) + 1 = sv).
{ intros H0. rewrite Hpe. replace (sv =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0). reflexivity. }
assert (Hpe2 : p + Z.of_nat (length w) + 1 <= c + s4_n e) by lia.
assert (HK2' : forall a, 0 <= a < 2 ^ 64 -> a < vr_s1 e - 4 * ESTACK \/ vr_s1 e <= a -> ~ (F + 608 <= a < F + 616) ->
  ~ (sv <> 0 /\ sv <= a < c + s4_n e) -> rdW W mem2 a = rdW W (ms_mem ms) a).
{ intros a Ha H1 H2 H3. apply HK2; [exact Ha | lia | exact H2 | exact H3]. }
clear HK2.
assert (Hcmn2 : s4_cmn B MT e pos F q c lyc Sc W mem2 md2 k nm).
{ apply (s4_cmn_keep e pos F q c lyc Sc W (ms_mem ms) md1 k nm mem2 md2 Hent Hcmn1 HJ2).
  intros a Ha H1 H2 H3. apply HK2'; [exact Ha | lia | lia |]. intros (Hsv0 & Hb). apply H3. pose proof (Hcsv Hsv0). lia. }
assert (K02 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 + 8 * Z.of_nat j <= a < F + 32 + 8 * Z.of_nat j + 8) ->
  a < vr_s1 e - 4 * ESTACK \/ vr_s1 e <= a -> ~ (F + 608 <= a < F + 616) ->
  ~ (sv <> 0 /\ sv <= a < c + s4_n e) -> rdW W mem2 a = rdW W mem a).
{ intros a Ha H0 H1 H2 H3. rewrite (HK2' a Ha H1 H2 H3). exact (KF a Ha H0). }
assert (TK2 : aval_mem (rdW W mem2) (F + 32 + 8 * Z.of_nat j) 8 p).
{ apply (aval_mem_agree _ _ _ _ _ TK). intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply HK2'; [lia | lia | lia |].
  intros (Hsv0 & Hb). pose proof (Hcsv Hsv0). lia. }
assert (Hsp2 : vr_spill e W mem2 (vr_sl3 F q c)).
{ apply (s4_spill_keep e W mem mem2 _ Hspl (s4_sl3_off F q c)). intros a Ha. apply K02; [lia | lia | lia | lia |].
  intros (Hsv0 & Hb). pose proof (Hcsv Hsv0). lia. }
assert (HjW : (j < length (s4_WS e))%nat) by (apply nth_error_Some; rewrite Hw; discriminate).
assert (HLps : length ps = j) by (pose proof Htk as (HL & _); rewrite length_firstn, Nat.min_l in HL by lia; exact HL).
assert (Htk2 : forall lim', p <= lim' -> s4_toks (rdW W mem2) F c lim' ps (firstn j (s4_WS e))).
{ intros lim' Hl. pose proof Htk as (HL & _). rewrite length_firstn, Nat.min_l in HL by lia.
  apply (s4_toks_keep (rdW W mem) _ F c p lim' ps _ Htk Hl).
  - intros a Ha. rewrite HL in Ha. apply K02; [lia | lia | lia | lia |]. intros (Hsv0 & Hb). pose proof (Hcsv Hsv0). lia.
  - intros a Ha. apply K02; [lia | lia | lia | lia |]. intros (Hsv0 & Hb). pose proof (Hcsv Hsv0). pose proof (Hpe1 Hsv0). lia. }
assert (Hpw2 : astr_atR (rdW W mem2) p w).
{ apply (astr_atR_agree (rdW W mem) _ p w (Z.of_nat (length w) + 1) Hpw); [lia|]. intros kk Hkk.
  apply K02; [lia | lia | lia | lia |]. intros (Hsv0 & Hb). pose proof (Hpe1 Hsv0). lia. }
rewrite Q1.
assert (HEI2 : img_env VAL A_LIM (Eimg (Ereg regs2 []))) by apply Eimg_env.
assert (RG2 : forall r v, In (r, v) (vr_base B e ++ s4_rlC e F j) -> getr regs2 (Z_to_bv 5 r) = w64 v)
  by (intros r v Hin; exact (rv_get regs2 _ r v HrvC2 Hin)).
pose proof (RG2 2 _ ltac:(s4in)) as T2. pose proof (RG2 3 _ ltac:(s4in)) as T3.
pose proof (RG2 4 _ ltac:(s4in)) as T4. pose proof (RG2 8 _ ltac:(s4in)) as T8.
pose proof (RG2 9 _ ltac:(s4in)) as T9. pose proof (RG2 18 _ ltac:(s4in)) as T18.
pose proof (RG2 19 _ ltac:(s4in)) as T19. pose proof (RG2 20 _ ltac:(s4in)) as T20.
pose proof (RG2 21 _ ltac:(s4in)) as T21. pose proof (RG2 22 _ ltac:(s4in)) as T22.
pose proof (RG2 23 _ ltac:(s4in)) as T23. pose proof (RG2 24 _ ltac:(s4in)) as T24.
pose proof (RG2 25 _ ltac:(s4in)) as T25. pose proof (RG2 26 _ ltac:(s4in)) as T26.
pose proof (RG2 27 _ ltac:(s4in)) as T27.
assert (T10 : getr regs2 (Z_to_bv 5 10) = w64 a0)
  by (replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity); exact H10').
assert (HS2 : st_ok_pi SEGS VAL (Eimg (Ereg regs2 [])) (s4_ss 27572 [])
  (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (BASE + 27572)) mem2 (seg_rom SEGS))))
  by (apply s4_seed; [reflexivity | constructor | exact I]).
clear HS HF HFr HG mat HK2' KF TK HrvC Hsv1 Hrem1 HARO1 Hsh1 Hsh76 Q1 Q2 Q3 Q4 Q10 Q10' Q11 Q12 Hsp1 Hra1 HP2 HJ Hcmn1.
clear ms.
revert Hres. destruct (skipn (S j) (s4_WS e)) as [|w' ws'] eqn:SKw; intros Hres; cbn [s4_tres] in Hres.
- (* no word left: a0 = 0 *)
  subst a0.
  assert (HlW : length (s4_WS e) = S j) by exact (s4_len_of_skipn _ _ _ Hw SKw).
  paj_run_sh RUNP HS2 HJ2.
  { change (ss_mem (s4_ss 27572 [])) with (@nil YP09.region). apply awr_ok_nil. }
  rename ms into ms3.
  set (md3 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md3.
  assert (K23 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms3) a = rdW W mem2 a).
  { intros a Ha. apply (aview_of_frame SEGS _ _ (w_H W) mem2 (ms_mem ms3) HFr a Ha). intros (r & Hin & _).
    change (ss_mem (s4_ss 27572 [])) with (@nil YP09.region) in Hin. destruct Hin. }
  clear HF HFr HG mat.
  psrr_branch_pi RUNP BR HS2.
  + paj_run_to_sh RUNTO HS2 HJ2 27588.
    { change (ss_mem (s4_ss 27572 [])) with (@nil YP09.region). apply awr_ok_nil. }
    rename ms into ms4.
    set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4.
    assert (K24 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms4) a = rdW W mem2 a).
    { intros a Ha. rewrite <- (K23 a Ha). apply (aview_of_frame SEGS _ _ (w_H W) (ms_mem ms3) (ms_mem ms4) HFr a Ha).
      intros (r & Hin & _). change (ss_mem (s4_ss 27572 [])) with (@nil YP09.region) in Hin. destruct Hin. }
    assert (Hrv4 : vr_rv (ms_regs ms4) (vr_base B e ++ [(18, e_msg e / 8); (19, SHADOW_OFF); (21, Z.of_nat j + 1);
      (24, e_msg e); (25, Z.of_nat j + 1)])).
    { unfold vr_rv, vr_base. cbn [app].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      all: lazymatch goal with
      | |- getr _ (Z_to_bv 5 ?r) = _ =>
        let Q := fresh "Q" in s4reg HS2 (Z_to_bv 5 r) Q; rewrite Q; clear Q
      end.
      - exact (sv_atom regs2 2 (Z_to_bv 5 2) _ eq_refl T2).
      - exact (sv_atom regs2 3 (Z_to_bv 5 3) _ eq_refl T3).
      - exact (sv_atom regs2 4 (Z_to_bv 5 4) _ eq_refl T4).
      - exact (sv_atom regs2 8 (Z_to_bv 5 8) _ eq_refl T8).
      - exact (sv_atom regs2 9 (Z_to_bv 5 9) _ eq_refl T9).
      - exact (sv_atom regs2 18 (Z_to_bv 5 18) _ eq_refl T18).
      - exact (sv_atom regs2 19 (Z_to_bv 5 19) _ eq_refl T19).
      - exact (sv_atom regs2 21 (Z_to_bv 5 21) _ eq_refl T21).
      - exact (sv_atom regs2 24 (Z_to_bv 5 24) _ eq_refl T24).
      - exact (s4_sv_addw1 regs2 25 (Z_to_bv 5 25) _ eq_refl T25 ltac:(lia)). }
    assert (Hcmn4 : s4_cmn B MT e pos F q c lyc Sc W (ms_mem ms4) md4 k nm).
    { apply (s4_cmn_keep e pos F q c lyc Sc W mem2 md2 k nm (ms_mem ms4) md4 Hent Hcmn2 HJ2).
      intros a Ha _ _ _. exact (K24 a Ha). }
    pmkst HS2. apply SRr_ret. left.
    rewrite (s4_cfg _ _ _ 0x8d0f4 27588 ltac:(unfold AF_verbs_receive; lia)).
    apply (s4_exit e pos F q c lyc Sc W (ms_regs ms4) (ms_mem ms4) md4 k nm ps p w j Hent Hcmn4 ltac:(lia) ltac:(lia)
      ltac:(right; exact HlW) Hrv4).
    * apply (s4_spill_keep e W mem2 _ _ Hsp2 (s4_sl3_off F q c)). intros a Ha. apply K24. lia.
    * apply (s4_toks_keep (rdW W mem2) _ F c (c + s4_n e) (c + s4_n e) ps _ (Htk2 (c + s4_n e) ltac:(lia)) ltac:(lia));
        intros a Ha; apply K24; lia.
    * exact Hw.
    * apply (aval_mem_agree _ _ _ _ _ TK2). intros kk Hkk. apply K24. change (Z.of_nat 8) with 8 in Hkk. lia.
    * apply (astr_atR_agree (rdW W mem2) _ p w (Z.of_nat (length w) + 1) Hpw2); [lia|]. intros kk Hkk. apply K24. lia.
    * exact Hcp.
    * exact Hpe2.
  + exfalso. rewrite branch_eq_U in Hc.
    rewrite (U_atom _ 10 0 ltac:(rewrite (ew_seed regs2 10 (Z_to_bv 5 10) eq_refl), T10; reflexivity) ltac:(lia)), U_SLit in Hc.
    vm_compute in Hc. discriminate Hc.
- (* the next word w' at a0 *)
  destruct Hres as (Ha0 & Hsva0 & Hw'2 & Ha0e & Hrem2).
  assert (Hsv0 : sv <> 0).
  { intros H0. destruct Hrem as [(_ & Hn0) | (r & Hr0 & _)]; [try rewrite SKw in Hn0; discriminate Hn0 | contradiction]. }
  pose proof (Hcsv Hsv0) as Hcsv'. pose proof (Hpe1 Hsv0) as Hpe1'.
  assert (Hbnd2 : (if sv2 =? 0 then c + s4_n e else sv2) <= c + s4_n e).
  { destruct Hrem2 as [(-> & _) | (r & Hr0 & _ & Hcr & Hrn & _)]; [cbn; lia|].
    replace (sv2 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hr0). lia. }
  destruct (s4_nth_skipn _ _ _ _ SKw) as [Hw' SKw'].
  paj_run_sh RUNP HS2 HJ2.
  { change (ss_mem (s4_ss 27572 [])) with (@nil YP09.region). apply awr_ok_nil. }
  rename ms into ms3.
  set (md3 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md3.
  assert (K23 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms3) a = rdW W mem2 a).
  { intros a Ha. apply (aview_of_frame SEGS _ _ (w_H W) mem2 (ms_mem ms3) HFr a Ha). intros (r & Hin & _).
    change (ss_mem (s4_ss 27572 [])) with (@nil YP09.region) in Hin. destruct Hin. }
  clear HF HFr HG mat.
  assert (U10 : U (Eimg (Ereg regs2 [])) (SOff 10 0) = a0)
    by (apply U_atom; [rewrite (ew_seed regs2 10 (Z_to_bv 5 10) eq_refl), T10; reflexivity | lia]).
  psrr_branch_pi RUNP BR HS2.
  + exfalso. rewrite branch_eq_U, U10, U_SLit in Hc. apply Z.eqb_eq in Hc. apply Ha0. rewrite Hc. reflexivity.
  + clear Hc. paj_run_sh RUNP HS2 HJ2.
    { change (ss_mem (s4_ss 27572 [])) with (@nil YP09.region). apply awr_ok_nil. }
    rename ms into ms4.
    set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4.
    assert (K24 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms4) a = rdW W mem2 a).
    { intros a Ha. rewrite <- (K23 a Ha). apply (aview_of_frame SEGS _ _ (w_H W) (ms_mem ms3) (ms_mem ms4) HFr a Ha).
      intros (r & Hin & _). change (ss_mem (s4_ss 27572 [])) with (@nil YP09.region) in Hin. destruct Hin. }
    clear HF HFr HG mat.
    assert (U20 : U (Eimg (Ereg regs2 [])) (SOff 20 0) = Z.of_nat j)
      by (apply U_atom; [rewrite (ew_seed regs2 20 (Z_to_bv 5 20) eq_refl), T20; reflexivity | lia]).
    assert (U23 : U (Eimg (Ereg regs2 [])) (SOff 23 0) = 63)
      by (apply U_atom; [rewrite (ew_seed regs2 23 (Z_to_bv 5 23) eq_refl), T23; reflexivity | lia]).
    psrr_branch_pi RUNP BR HS2.
    * (* j < 63: back to the head *)
      rewrite branch_ltu_U, U20, U23 in Hc. apply Z.ltb_lt in Hc.
      paj_run_to_sh RUNTO HS2 HJ2 27544.
      { change (ss_mem (s4_ss 27572 [])) with (@nil YP09.region). apply awr_ok_nil. }
      rename ms into ms5.
      set (md5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md5.
      assert (K25 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms5) a = rdW W mem2 a).
      { intros a Ha. rewrite <- (K24 a Ha). apply (aview_of_frame SEGS _ _ (w_H W) (ms_mem ms4) (ms_mem ms5) HFr a Ha).
        intros (r & Hin & _). change (ss_mem (s4_ss 27572 [])) with (@nil YP09.region) in Hin. destruct Hin. }
      assert (Hrv5 : vr_rv (ms_regs ms5) (vr_base B e ++ s4_rlL e F (S j) a0)).
      { unfold vr_rv, vr_base, s4_rlL. cbn [app].
        repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
        all: lazymatch goal with
        | |- getr _ (Z_to_bv 5 ?r) = _ =>
          let Q := fresh "Q" in s4reg HS2 (Z_to_bv 5 r) Q; rewrite Q; clear Q
        end.
        - exact (sv_atom regs2 2 (Z_to_bv 5 2) _ eq_refl T2).
        - exact (sv_atom regs2 3 (Z_to_bv 5 3) _ eq_refl T3).
        - exact (sv_atom regs2 4 (Z_to_bv 5 4) _ eq_refl T4).
        - exact (sv_atom regs2 8 (Z_to_bv 5 8) _ eq_refl T8).
        - exact (sv_atom regs2 9 (Z_to_bv 5 9) _ eq_refl T9).
        - exact (sv_atom regs2 10 (Z_to_bv 5 10) _ eq_refl T10).
        - exact (sv_atom regs2 18 (Z_to_bv 5 18) _ eq_refl T18).
        - exact (sv_atom regs2 19 (Z_to_bv 5 19) _ eq_refl T19).
        - rewrite (sv_atom regs2 21 (Z_to_bv 5 21) _ eq_refl T21). f_equal. lia.
        - rewrite (s4_sv_off regs2 22 (Z_to_bv 5 22) _ 8 eq_refl T22 ltac:(lia)). f_equal. lia.
        - exact (sv_atom regs2 23 (Z_to_bv 5 23) _ eq_refl T23).
        - exact (sv_atom regs2 24 (Z_to_bv 5 24) _ eq_refl T24).
        - rewrite (s4_sv_addw1 regs2 25 (Z_to_bv 5 25) _ eq_refl T25 ltac:(lia)). f_equal. lia.
        - exact (sv_atom regs2 26 (Z_to_bv 5 26) _ eq_refl T26).
        - exact (sv_atom regs2 27 (Z_to_bv 5 27) _ eq_refl T27). }
      assert (Hcmn5 : s4_cmn B MT e pos F q c lyc Sc W (ms_mem ms5) md5 k nm).
      { apply (s4_cmn_keep e pos F q c lyc Sc W mem2 md2 k nm (ms_mem ms5) md5 Hent Hcmn2 HJ2).
        intros a Ha _ _ _. exact (K25 a Ha). }
      pmkst HS2. apply SRr_ret. right. split; [lia|].
      exists pos, F, q, c, lyc, Sc, (ms_regs ms5), (ms_mem ms5), md5, k, nm, (ps ++ [p]), a0, sv2, w'.
      split; [apply s4_cfg; unfold AF_verbs_receive; lia|].
      split; [lia|]. split; [exact Hcmn5|]. split; [exact Hrv5|].
      split; [apply (s4_spill_keep e W mem2 _ _ Hsp2 (s4_sl3_off F q c)); intros a Ha; apply K25; lia|].
      split.
      { rewrite (s4_firstn_S _ _ _ Hw). pose proof Htk as (HL & _). rewrite length_firstn, Nat.min_l in HL by lia.
        apply s4_toks_snoc.
        - apply (s4_toks_keep (rdW W mem2) _ F c a0 a0 ps _ (Htk2 a0 ltac:(lia)) ltac:(lia)); intros a Ha; apply K25; lia.
        - rewrite HL. apply (aval_mem_agree _ _ _ _ _ TK2). intros kk Hkk. apply K25. change (Z.of_nat 8) with 8 in Hkk. lia.
        - apply (astr_atR_agree (rdW W mem2) _ p w (Z.of_nat (length w) + 1) Hpw2); [lia|]. intros kk Hkk. apply K25. lia.
        - exact Hcp.
        - lia. }
      split; [exact Hw'|].
      split; [apply (astr_atR_agree (rdW W mem2) _ a0 w' (Z.of_nat (length w') + 1) Hw'2); [lia|]; intros kk Hkk; apply K25; lia|].
      split; [lia|]. split; [exact Ha0e|].
      split; [apply (rdword_agree (rdW W mem2)); [exact Hsv2|]; intros kk Hkk; apply K25; lia|].
      rewrite SKw'. apply (s4_rem_agree (rdW W mem2) _ c (s4_n e) sv2 ws' Hrem2). intros Hsv20 a Ha. apply K25.
      destruct Hrem2 as [(? & _) | (r & _ & _ & Hcr & _)]; [contradiction | lia].
    * (* j = 63: 64 words stored, to the dispatch *)
      rewrite branch_ltu_U, U20, U23 in Hc. apply Z.ltb_ge in Hc.
      paj_run_to_sh RUNTO HS2 HJ2 27588.
      { change (ss_mem (s4_ss 27572 [])) with (@nil YP09.region). apply awr_ok_nil. }
      rename ms into ms5.
      set (md5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md5.
      assert (K25 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms5) a = rdW W mem2 a).
      { intros a Ha. rewrite <- (K24 a Ha). apply (aview_of_frame SEGS _ _ (w_H W) (ms_mem ms4) (ms_mem ms5) HFr a Ha).
        intros (r & Hin & _). change (ss_mem (s4_ss 27572 [])) with (@nil YP09.region) in Hin. destruct Hin. }
      assert (Hrv5 : vr_rv (ms_regs ms5) (vr_base B e ++ [(18, e_msg e / 8); (19, SHADOW_OFF); (21, Z.of_nat j + 1);
        (24, e_msg e); (25, Z.of_nat j + 1)])).
      { unfold vr_rv, vr_base. cbn [app].
        repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
        all: lazymatch goal with
        | |- getr _ (Z_to_bv 5 ?r) = _ =>
          let Q := fresh "Q" in s4reg HS2 (Z_to_bv 5 r) Q; rewrite Q; clear Q
        end.
        - exact (sv_atom regs2 2 (Z_to_bv 5 2) _ eq_refl T2).
        - exact (sv_atom regs2 3 (Z_to_bv 5 3) _ eq_refl T3).
        - exact (sv_atom regs2 4 (Z_to_bv 5 4) _ eq_refl T4).
        - exact (sv_atom regs2 8 (Z_to_bv 5 8) _ eq_refl T8).
        - exact (sv_atom regs2 9 (Z_to_bv 5 9) _ eq_refl T9).
        - exact (sv_atom regs2 18 (Z_to_bv 5 18) _ eq_refl T18).
        - exact (sv_atom regs2 19 (Z_to_bv 5 19) _ eq_refl T19).
        - exact (sv_atom regs2 21 (Z_to_bv 5 21) _ eq_refl T21).
        - exact (sv_atom regs2 24 (Z_to_bv 5 24) _ eq_refl T24).
        - exact (s4_sv_addw1 regs2 25 (Z_to_bv 5 25) _ eq_refl T25 ltac:(lia)). }
      assert (Hcmn5 : s4_cmn B MT e pos F q c lyc Sc W (ms_mem ms5) md5 k nm).
      { apply (s4_cmn_keep e pos F q c lyc Sc W mem2 md2 k nm (ms_mem ms5) md5 Hent Hcmn2 HJ2).
        intros a Ha _ _ _. exact (K25 a Ha). }
      pose proof (nth_error_Some (s4_WS e) (S j)) as [HjW' _]. rewrite Hw' in HjW'.
      specialize (HjW' ltac:(discriminate)).
      pmkst HS2. apply SRr_ret. left.
      rewrite (s4_cfg _ _ _ 0x8d0f4 27588 ltac:(unfold AF_verbs_receive; lia)).
      apply (s4_exit e pos F q c lyc Sc W (ms_regs ms5) (ms_mem ms5) md5 k nm ps p w j Hent Hcmn5 ltac:(lia) ltac:(lia)
        ltac:(left; lia) Hrv5).
      -- apply (s4_spill_keep e W mem2 _ _ Hsp2 (s4_sl3_off F q c)). intros a Ha. apply K25. lia.
      -- apply (s4_toks_keep (rdW W mem2) _ F c (c + s4_n e) (c + s4_n e) ps _ (Htk2 (c + s4_n e) ltac:(lia)) ltac:(lia));
           intros a Ha; apply K25; lia.
      -- exact Hw.
      -- apply (aval_mem_agree _ _ _ _ _ TK2). intros kk Hkk. apply K25. change (Z.of_nat 8) with 8 in Hkk. lia.
      -- apply (astr_atR_agree (rdW W mem2) _ p w (Z.of_nat (length w) + 1) Hpw2); [lia|]. intros kk Hkk. apply K25. lia.
      -- exact Hcp.
      -- exact Hpe2.
Qed.

(* the passes chained: from the head of pass j, the loop reaches the dispatch *)
Lemma s4_loop : forall d e j W cf, vr_ent B MT e -> (j + d = 63)%nat -> s4_L e j W cf -> SRr SEGS W cf (vr_b4t B MT e).
Proof.
induction d as [|d IH]; intros e j W cf Hent Hjd HL.
- eapply SRr_bind; [exact (s4_body e j W cf Hent HL)|].
  intros W' cf' _ [H | [Hj _]]; [apply SRr_ret; exact H | lia].
- eapply SRr_bind; [exact (s4_body e j W cf Hent HL)|].
  intros W' cf' _ [H | [_ H]]; [apply SRr_ret; exact H|].
  exact (IH e (S j) W' cf' Hent ltac:(lia) H).
Qed.

End e.
End f.
End d.
