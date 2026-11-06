(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_contract_x.v, with its module paths changed; 43 of its 131 lines of code are new or changed and 1924 lines of the source are left out. *)
(* The two send_line contract texts of lib/B/W_contract_x.v (sl_post_x :672, sl_spec_x :690) at a world relation R.
   R is a Section variable right after ARx, and the SAME R is used in the post journal (W_journal_x.ajournal_gx_xR) and
   in the step relation (YA0nH.SRrG SEGS R). The instance for the re-hiding allocator calls is R := wle' SEGS RZ_cf
   (YA0nH.wle', YGcfRehidePost.RZ_cf), chosen at the use site.
   Against the strict texts only these change: the name, `ajournal_gx_x SEGS B PST ARx` -> `ajournal_gx_xR SEGS B PST
   ARx R`, `SRr SEGS` -> `SRrG SEGS R`, `sl_post_x` -> `sl_post_xR`, and `sl_line_ok_x ly` -> `sl_line_ok_x B ARx ly`
   (outside W_contract_x.v's Section s7 its section arguments are explicit; the term is the same).
   Instances (X = sl_post, sl_spec): at R := wle each R text IS its strict text (X_x_wle, by conversion); so the R
   text at wle gives the strict one (X_x_of_xR), and a strict text gives the R text at every R that contains wle
   (X_xR_of_x, from WLE_R). The satisfiability lemma at the real image is in W_send_line_xR_sat.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Setoid.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_kit W_journal W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YI00 YN0h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require next_line_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require send_line_c send_line_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayRunT drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require gesture_end_c relay_remove_b_c relay_instance_gone_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require gesture_end_b_c RelayRunF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YCe5x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require ListTr HarnessTr RelayRunF.
(* the import block above is W_contract_x.v's (lines 43-78), so every name of the texts resolves as there *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section s7R.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* the world relation of the post journal and of the step relation, and its laws (one Section set for every hand;
   the definitions below use none of the laws, so they do not take them) *)
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
(* W_contract_x.v:672 sl_post_x at R: the journal conjunct ajournal_gx_x -> ajournal_gx_xR R; every other conjunct verbatim *)
Definition sl_post_xR (regs : bvmap 5 word) ly S (Hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
(c : ctl) (O : list byte) (mx no cap out : Z) (Bl : list byte) (kr : nat) : world SEGS -> config -> Prop :=
fun W' c' => exists ly' S' Hp' regs' mem' md' k out',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
ajournal_gx_xR SEGS B PST ARx R (G_SL B RG) 0 [] SL_STK (spZ regs) (ablocks_fp (aout_blks cap out)) ly S Hp W mem md [] ly' S' Hp' W' mem' md' k /\
aregs_preserved regs regs' /\
apres_kept B W mem W' mem' /\
mo_le MT S S' (sl_cost MT c mx no cap (Z.of_nat (length Bl))) /\
rp_RM RP S' kr /\
(exists rest, Permutation (ablocks B ly S) (aout_blks cap out ++ rest) /\
 Permutation (ablocks B ly' S') (aout_blks (sl_cap c mx no cap (Z.of_nat (length Bl))) out' ++ rest)) /\
aout_at B RG ly' S' W' mem' (sl_ctl c (Z.of_nat (length Bl))) (sl_O c O Bl) mx
  (sl_no c no (Z.of_nat (length Bl))) (sl_cap c mx no cap (Z.of_nat (length Bl))) out' /\
(* an OFF send leaves g_out's block as it was (W_contract_x.v:685-687) *)
(sl_live c (Z.of_nat (length Bl)) = false -> out' = out).
(* W_contract_x.v:690 sl_spec_x at R: SRr SEGS -> SRrG SEGS R and the post sl_post_xR; every premise verbatim *)
Definition sl_spec_xR (pc : Z) : Prop :=
forall W ly S Hp regs mem md ch c O mx no cap out line Bl,
afn_pre_x SEGS B ARx SL_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 line -> getr regs 11 = w64 (Z.of_nat (length Bl)) ->
aout_at B RG ly S W mem c O mx no cap out ->
rom_view SEGS W mem ->
garr8 SEGS (arm W mem) line (bzs Bl) -> 0 <= line -> line + Z.of_nat (length Bl) < 2 ^ 63 ->
sl_line_ok_x B ARx ly S out line (Z.of_nat (length Bl)) ->
(* the line is no byte of G_SL (W_contract_x.v:698-699) *)
(forall a, line <= a < line + Z.of_nat (length Bl) -> ~ inG (G_SL B RG) a) ->
sl_maxr c mx no cap (Z.of_nat (length Bl)) < MMAX ->
blocks_bytes S + tr_peak (sl_tr c mx no cap (Z.of_nat (length Bl))) <= LIVE_MAX ->
mo_ok MT S (sl_cost MT c mx no cap (Z.of_nat (length Bl))) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (sl_cost MT_rk c mx no cap (Z.of_nat (length Bl))) + kr) ->
cnt_ok_pk RP sl_pk (ablocks B ly S) ->
SRrG SEGS R W (cfg_at SEGS pc regs mem md) (sl_post_xR regs ly S Hp W mem md c O mx no cap out Bl kr).
End s7R.

Section s7Ri.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
(* (a) at R := wle the R text IS the strict text (SRrG SEGS wle is SRr SEGS, ajournal_gx_xR at wle is ajournal_gx_x) *)
Lemma sl_post_x_wle : sl_post_x B PST ARx MT RP RG = sl_post_xR B PST ARx (@wle SEGS) MT RP RG.
Proof. reflexivity. Qed.
Lemma sl_spec_x_wle : sl_spec_x B PST ARx MT RP MMAX RG = sl_spec_xR B PST ARx (@wle SEGS) MT RP MMAX RG.
Proof. reflexivity. Qed.
(* (b) the R text at wle gives the strict text *)
Lemma sl_post_x_of_xR : forall regs ly S Hp W mem md c O mx no cap out Bl kr W' c',
  sl_post_xR B PST ARx (@wle SEGS) MT RP RG regs ly S Hp W mem md c O mx no cap out Bl kr W' c' ->
  sl_post_x B PST ARx MT RP RG regs ly S Hp W mem md c O mx no cap out Bl kr W' c'.
Proof. intros regs ly S Hp W mem md c O mx no cap out Bl kr W' c' H. exact H. Qed.
Lemma sl_spec_x_of_xR : forall pc,
  sl_spec_xR B PST ARx (@wle SEGS) MT RP MMAX RG pc -> sl_spec_x B PST ARx MT RP MMAX RG pc.
Proof. intros pc H. exact H. Qed.
(* (c) a strict text gives the R text at every R that contains wle (WLE_R); the post's journal is weakened by
   W_journal_x.ajournal_gx_xR_mono *)
Lemma sl_post_xR_of_x : forall regs ly S Hp W mem md c O mx no cap out Bl kr W' c',
  sl_post_x B PST ARx MT RP RG regs ly S Hp W mem md c O mx no cap out Bl kr W' c' ->
  sl_post_xR B PST ARx R MT RP RG regs ly S Hp W mem md c O mx no cap out Bl kr W' c'.
Proof.
intros regs ly S Hp W mem md c O mx no cap out Bl kr W' c'
  (ly' & S' & Hp' & regs' & mem' & md' & k & out' & Hc & HJ & REST).
exists ly', S', Hp', regs', mem', md', k, out'. split; [exact Hc|]. split; [|exact REST].
eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ].
Qed.
Lemma sl_spec_xR_of_x : forall pc, sl_spec_x B PST ARx MT RP MMAX RG pc -> sl_spec_xR B PST ARx R MT RP MMAX RG pc.
Proof.
intros pc H. unfold sl_spec_xR. intros.
eapply SRrG_mono; [eapply SRr_SRrG; [exact WLE_R | eapply H; eassumption] |].
intros W' c' _ HP. exact (sl_post_xR_of_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP).
Qed.
End s7Ri.
