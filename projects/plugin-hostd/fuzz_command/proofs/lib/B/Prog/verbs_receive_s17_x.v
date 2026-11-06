(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the boundary facts of the walk of verbs_receive on the ASan+UBSan build of
   plugin-hostd/fuzz_command (lib/B/Prog/verbs_receive_iface.v) carried across the atoi wrapper that segment S17
   POOL calls before sup_pool_config: the wrapper (a Theorem Labs lane's aatoi_realizes through PaArt.aj_art_at) writes only its
   window below the realigned stack pointer s1 and the errno cell, so the memory agrees below the allocation ceiling
   and from s1 up, except at the errno cell (v17_kx). The B twin of the A walk's verbs_receive_s17_x.v
   (a working branch), with the read-only environment at a journal state (vr_env_of_journal)
   and the offset of s1 (vr_o_facts) taken from the A walk's verbs_receive_s14_k.v / _s14_c.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_s18_kit verbs_receive_s18_call.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the atoi wrapper's value is an int *)
Lemma v17_swrap32_range : forall z, -2 ^ 31 <= bv_swrap 32 z < 2 ^ 31.
Proof.
intros z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
assert (E : 2 ^ Z.of_N 32 = 4294967296) by reflexivity. rewrite E.
change (Z.div 4294967296 2) with 2147483648.
pose proof (Z.mod_pos_bound (z + 2147483648) 4294967296 ltac:(lia)). lia.
Qed.

Lemma v17_PG_rec : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_G_REC, A_G_REC + 960). split; [unfold cmd_PG; left; reflexivity | unfold REC_SIZE in Ha; cbn; lia]. Qed.
Lemma v17_PG_spill : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_REC_SPILL, A_REC_SPILL + 56). split; [unfold cmd_PG; right; left; reflexivity | unfold SC_SIZE in Ha; cbn; lia]. Qed.
Lemma v17_PG_quit : forall a, A_G_QUITTING <= a < A_G_QUITTING + 4 -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_G_QUITTING, A_G_QUITTING + 4). split; [unfold cmd_PG; right; right; left; reflexivity | cbn; lia]. Qed.
Lemma v17_inFP_app_or : forall l1 l2 a, inFP (l1 ++ l2) a -> inFP l1 a \/ inFP l2 a.
Proof.
intros l1 l2 a (r & Hr & Ha). apply in_app_or in Hr as [Hr|Hr]; [left | right]; exists r; split; assumption.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the offset of s1 from the entry sp: 192 or 208 *)
Lemma vr_o_facts : forall e, vr_sp0 e mod 16 = 0 ->
(vr_s1 e - vr_sp0 e) mod 16 = 0 /\ -208 <= vr_s1 e - vr_sp0 e <= -192.
Proof.
intros e H.
assert (Hx : (vr_sp0 e - 192) mod 16 = 0) by (rewrite Zminus_mod, H; reflexivity).
pose proof (Z.div_mod (vr_sp0 e - 192) 32 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (vr_sp0 e - 192) 32 ltac:(lia)) as M1.
pose proof (Z.div_mod (vr_sp0 e - 192) 16 ltac:(lia)) as D2. rewrite Hx in D2.
assert (Hr : (vr_sp0 e - 192) mod 32 = 0 \/ (vr_sp0 e - 192) mod 32 = 16) by lia.
assert (Heq : vr_s1 e - vr_sp0 e = -192 - (vr_sp0 e - 192) mod 32) by (unfold vr_s1; lia).
rewrite Heq. destruct Hr as [Hr | Hr]; rewrite Hr; split; first [reflexivity | lia].
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis PROGU : vr_prog_unowned B.
Hypothesis TL : PALib B.

(* ---------------------------------------------------------------------------------------------------------------
   The read-only environment at any journal state of the walk (the A walk's verbs_receive_s14_k.v) *)
Lemma in_img_of_ro : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a.
Proof using RRO. intros a [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RRO a Hr)]. Qed.
Lemma vr_ent_O_blocks : forall e pn, vr_ent B MT e -> In pn (e_O e) -> In pn (ablocks B (e_ly e) (e_S e)).
Proof.
intros e pn He Hpn. destruct He as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HREC & _).
exact (rec_repA_in_blocks B _ _ _ _ _ _ HREC Hpn).
Qed.
Lemma vr_fp_spares : forall e a, vr_ent B MT e -> in_roP SEGS RLO RHI a -> fp_spares (vr_fp e) a.
Proof using RRO RPG LAWS.
intros e a He Hro. pose proof He as (HPRE & _). pose proof HPRE as (HAR & _).
apply fp_spares_closed.
- apply sink_closed_pos. unfold vr_fp, VERBS_RECEIVE_PG. apply Forall_app. split.
  + repeat constructor; cbn; unfold A_G_REC, A_REC_SPILL, A_G_QUITTING; lia.
  + unfold ablocks_fp. apply Forall_map. apply Forall_forall. intros [p n] Hpn. cbn [fst].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (vr_ent_O_blocks e _ He Hpn)) as (_ & H4 & _). lia.
- intros Hf. apply v17_inFP_app_or in Hf as [Hf | Hf].
  + apply (RPG a); [|exact Hro]. exact Hf.
  + destruct (inFP_ablocks_fp_inv (e_O e) a Hf) as (p & n & Hpn & Hr).
    exact (blk_img SEGS B LAWS _ _ _ _ _ p n a HAR (vr_ent_O_blocks e _ He Hpn) Hr (in_img_of_ro a Hro)).
Qed.
Lemma vr_env_of_journal : forall e own ly2 S2 (W2 : world SEGS) mem2 md2 k,
vr_ent B MT e ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) own ly2 S2 W2 mem2 md2 k ->
vr_env B W2 mem2.
Proof using RRO RPG RECC ROA LAWS.
intros e own ly2 S2 W2 mem2 md2 k He HJ.
pose proof He as (_ & HROD & _).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (HRO2 : arodata_okP SEGS RLO RHI B (rdW W2 mem2)).
{ intros a Hro Ho Herr. rewrite (F3 a (in_img_of_ro a Hro) Ho Herr (vr_fp_spares e a He Hro)). exact (HROD a Hro Ho Herr). }
pose proof (ROA ly2 S2 W2 mem2 md2 HAR2 HRO2) as HCR.
destruct (RECC ly2 S2 W2 mem2 md2 HAR2) as (Hfl & Hag & Her).
split; [exact HRO2|]. split; [exact (vr_got_of_ro _ HCR)|]. split; [exact HCR|].
split; [exact Hag|]. split; [exact Hfl | exact Her].
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   Memory that agrees below the allocation ceiling and from s1 up, except at the errno cell *)
Definition v17_kx (e : vrE) (W : world SEGS) (m m' : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> (a < alloc_ceiling \/ vr_s1 e <= a) -> ~ aerrno_cell B a -> rdW W m' a = rdW W m a.

Lemma v17_nerr_hi : forall a, kLowMemEnd <= a -> ~ aerrno_cell B a.
Proof using TL. intros a Ha He. pose proof (pal_env B TL) as ((E0 & E1) & _). unfold aerrno_cell in He. lia. Qed.
Lemma v17_nerr_img : forall a, ~ in_img SEGS a -> ~ aerrno_cell B a.
Proof using TL. intros a Ha He. pose proof (pal_env B TL) as (_ & EI & _). exact (Ha (EI a He)). Qed.
Lemma v17_nerr_frame : forall lyc Sc (W : world SEGS) mem md pos a, AR SEGS B lyc Sc W mem md -> In (4, pos) (frames Sc) ->
frame_addr lyc 4 pos <= a < frame_addr lyc 4 pos + 1024 -> ~ aerrno_cell B a.
Proof using TL LAWS.
intros lyc Sc W mem md pos a HAR Hin Ha. apply v17_nerr_img. apply (frm_img SEGS B LAWS lyc Sc W mem md 4 pos a HAR Hin).
change (fs_frame_bytes 4) with 1024. exact Ha.
Qed.
Lemma v17_nerr_block : forall lyc Sc (W : world SEGS) mem md p n a, AR SEGS B lyc Sc W mem md -> In (p, n) (ablocks B lyc Sc) ->
p <= a < p + req_size n -> ~ aerrno_cell B a.
Proof using TL LAWS.
intros lyc Sc W mem md p n a HAR Hin Ha. apply v17_nerr_img. exact (blk_img SEGS B LAWS lyc Sc W mem md p n a HAR Hin Ha).
Qed.
Lemma v17_nerr_pg : forall a, inFP cmd_PG a -> ~ aerrno_cell B a.
Proof using PROGU. intros a Ha. destruct (PROGU a Ha) as (_ & _ & He). exact He. Qed.
Lemma v17_img_pg : forall a, inFP cmd_PG a -> a < 0x606000.
Proof using PROGU. intros a Ha. destruct (PROGU a Ha) as (Hi & _). exact (proj2 (pa_img_range a Hi)). Qed.

(* a boundary state's vr_core carried to a state whose memory agrees by v17_kx and whose journal is the same *)
Lemma v17_core_kx : forall e pos F tmps sh sl rl rl' Rc Oc qv k kmax nm nmax lyc Sc W regs mem md regs' mem' md',
vr_ent B MT e ->
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
  [(4, pos)] lyc Sc W mem' md' k ->
v17_kx e W mem mem' ->
Forall (fun ov => 0 <= fst ov <= 200) sl ->
vr_rv regs' (vr_base B e ++ rl') ->
vr_core B MT e pos F tmps sh sl rl' Rc Oc qv k kmax nm nmax lyc Sc W regs' mem' md'.
Proof using RRO RPG RECC ROA PROGU TL LAWS.
intros e pos F tmps sh sl rl rl' Rc Oc qv k kmax nm nmax lyc Sc W regs mem md regs' mem' md'
  Hent (HJ & Hkm & Hmeter & Hnm & Hframe & Hrv & Hsaved & Hspill & Henv & Hrec & HdO & Hperm & Hquit) HJ' K Hsl Hrv'.
pose proof Hent as (HPRE0 & _). pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof asan_consts as (C1 & _ & _ & _ & C5).
destruct (vr_o_facts e Hal16) as [_ Hs1].
pose proof (proj1 HJ) as HAR. pose proof (proj1 HJ') as HAR'.
assert (Hin4 : In (4, pos) (frames Sc)) by (pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _); rewrite Hfrs; left; reflexivity).
split; [exact HJ'|]. split; [exact Hkm|]. split; [exact Hmeter|]. split; [exact Hnm|].
split.
{ destruct Hframe as (HF & Hfl & Hsh). subst F.
  destruct (frames_bounds SEGS B LAWS lyc Sc W mem md 4 pos HAR Hin4) as (B1 & B2 & _).
  change (fs_frame_bytes 4) with 1024 in B2.
  split; [reflexivity|]. split.
  - rewrite (rdword_ext (rdW W mem) (rdW W mem')); [exact Hfl|]. intros kk Hkk'.
    apply K; [lia | left; lia | apply (v17_nerr_frame lyc Sc W mem md pos _ HAR Hin4); lia].
  - intros i Hi.
    pose proof (Z.div_mod (frame_addr lyc 4 pos) 8 ltac:(lia)) as D.
    pose proof (Z.mod_pos_bound (frame_addr lyc 4 pos) 8 ltac:(lia)) as M.
    rewrite (K (shadow_addr (frame_addr lyc 4 pos) + Z.of_nat i)); [exact (Hsh i Hi) | | |];
      unfold shadow_addr, SHADOW_OFF in *.
    + lia.
    + left. lia.
    + apply v17_nerr_hi. unfold kLowMemEnd. lia. }
split; [exact Hrv'|].
split.
{ intros j r Hj.
  assert (Hj13 : (j < length vr_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  cbn [length vr_saved_regs] in Hj13.
  intros kk Hkk. rewrite K; [exact (Hsaved j r Hj kk Hkk) | lia | right; lia | apply v17_nerr_hi; lia]. }
split.
{ unfold vr_spill in *. rewrite Forall_forall in Hspill, Hsl |- *. intros ov Hov.
  pose proof (Hsl ov Hov) as Hb.
  intros kk Hkk. rewrite K; [exact (Hspill ov Hov kk Hkk) | lia | right; lia | apply v17_nerr_hi; lia]. }
split; [exact (vr_env_of_journal e _ _ _ _ _ _ _ Hent HJ')|].
split.
{ apply (rec_repA_agree B _ _ _ _ _ _ Rc Oc Hrec (fun pn _ Hb => Hb)).
  - intros kk Hk.
    assert (G : A_G_REC <= A_G_REC + kk < A_G_REC + REC_SIZE) by (unfold A_G_REC, REC_SIZE in *; lia).
    pose proof (v17_img_pg _ (v17_PG_rec _ G)).
    apply K; [unfold A_G_REC, REC_SIZE in *; lia | left; lia | exact (v17_nerr_pg _ (v17_PG_rec _ G))].
  - intros kk Hk.
    assert (G : A_REC_SPILL <= A_REC_SPILL + kk < A_REC_SPILL + SC_SIZE) by (unfold A_REC_SPILL, SC_SIZE in *; lia).
    pose proof (v17_img_pg _ (v17_PG_spill _ G)).
    apply K; [unfold A_REC_SPILL, SC_SIZE in *; lia | left; lia | exact (v17_nerr_pg _ (v17_PG_spill _ G))].
  - intros [p n] Hpn kk Hk. cbn [fst snd] in *.
    pose proof (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hpn) as Hin.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & H4 & Hc & _ & _ & _ & Hn).
    pose proof (req_size_pos n ltac:(lia)) as Hrq.
    apply K; [lia | left; lia | apply (v17_nerr_block lyc Sc W mem md p n _ HAR Hin); lia]. }
split; [exact HdO|]. split; [exact Hperm|].
intros kk Hkk.
assert (G : A_G_QUITTING <= A_G_QUITTING + Z.of_nat kk < A_G_QUITTING + 4) by lia.
pose proof (v17_img_pg _ (v17_PG_quit _ G)).
rewrite K; [exact (Hquit kk Hkk) | unfold A_G_QUITTING in *; lia | left; lia | exact (v17_nerr_pg _ (v17_PG_quit _ G))].
Qed.

Lemma v17_line_kx : forall e q lyc Sc (W : world SEGS) mem md mem', vr_ent B MT e ->
AR SEGS B lyc Sc W mem md -> In (vr_lb e q) (ablocks B lyc Sc) ->
vr_line B e q W mem -> v17_kx e W mem mem' -> vr_line B e q W mem'.
Proof using TL LAWS.
intros e q lyc Sc W mem md mem' Hent HAR Hin (Hfr & Hs) K. split; [exact Hfr|].
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & _).
pose proof asan_consts as (C1 & _).
unfold vr_lb in Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4 & Hc & _ & _ & _ & Hn).
pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(lia)) as Hrs.
assert (Hll : Z.of_nat (length (Verbs.line (e_D e))) <= vr_l (e_n e) (e_D e)).
{ unfold vr_l. rewrite <- HlenD. exact (vr_line_le_l (e_D e)). }
apply (astr_atR_agree (rdW W mem) (rdW W mem') q (Verbs.line (e_D e)) (vr_l (e_n e) (e_D e) + 1) Hs).
- lia.
- intros kk Hkk. apply K; [lia | left; lia | apply (v17_nerr_block lyc Sc W mem md q _ _ HAR Hin); lia].
Qed.

Lemma v17_copy_kx : forall e F c tp pos lyc Sc (W : world SEGS) mem md mem', AR SEGS B lyc Sc W mem md ->
In (4, pos) (frames Sc) -> F = frame_addr lyc 4 pos -> In (vr_cb e c) (ablocks B lyc Sc) ->
vr_copy B e F c tp W mem -> v17_kx e W mem mem' -> vr_copy B e F c tp W mem'.
Proof using TL LAWS.
intros e F c tp pos lyc Sc W mem md mem' HAR Hin4 HF Hin (Hfr & Hal & Hlen & Hptr & Hw) K. subst F.
pose proof asan_consts as (C1 & _).
destruct (frames_bounds SEGS B LAWS lyc Sc W mem md 4 pos HAR Hin4) as (B1 & B2 & _).
change (fs_frame_bytes 4) with 1024 in B2.
unfold vr_cb in Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4 & Hc & _ & _ & _ & Hn).
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as Hrq.
assert (Htk : (length (Verbs.toks (e_D e)) <= 64)%nat)
  by (unfold Verbs.toks; rewrite length_firstn; unfold Verbs.line_words_max; lia).
split; [exact Hfr|]. split; [exact Hal|]. split; [exact Hlen|]. split.
- intros i p Hi.
  assert (Hi64 : (i < 64)%nat)
    by (rewrite <- Hlen in Htk; pose proof (proj1 (nth_error_Some tp i) ltac:(rewrite Hi; discriminate)); lia).
  intros kk Hkk. rewrite K; [exact (Hptr i p Hi kk Hkk) | lia | left; lia |].
  apply (v17_nerr_frame lyc Sc W mem md pos _ HAR Hin4). lia.
- intros i p w Hi Hwi. destruct (Hw i p w Hi Hwi) as (Hs & Hl8 & Hp1 & Hp2).
  split; [|split; [exact Hl8 | split; [exact Hp1 | exact Hp2]]].
  apply (astr_atR_agree _ _ p w (Z.of_nat (length w) + 1) Hs); [lia|].
  intros kk Hkk. apply K; [lia | left; lia | apply (v17_nerr_block lyc Sc W mem md c _ _ HAR Hin); lia].
Qed.

End e.
End f.
End d.
