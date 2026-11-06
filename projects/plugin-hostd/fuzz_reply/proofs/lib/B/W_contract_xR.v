(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_contract_x.v; 329 of its 634 lines of code are new or changed and 1707 lines of the source are left out. *)
(* Contract texts of lib/B/W_contract_x.v at a world relation R: relay_event (re_post_x :796, re_spec_x :811),
   list_push (lp_post_x :350, lp_spec_x :368, lp_spec_g_x :479), drain (dr_post_x :715, dr_spec_x :756), gesture_end
   (ge_post_x :1017, ge_spec_x :1031), gestures_end (gse_post_x :1047, gse_spec_x :1062) and relay_finish (rf_post_x
   :1151, rf_spec_x :1168).
   R is a Section variable right after ARx, with its laws R_refl, R_trans, WLE_R (the definitions use none of them), and
   the SAME R is used in the post journal (W_journal_x.ajournal_gx_xR) and in the step relation (YA0nH.SRrG SEGS R).
   The instance for the re-hiding allocator calls is R := wle' SEGS RZ_cf (YA0nH.wle', YGcfRehidePost.RZ_cf), chosen
   at the use site.
   Against the strict texts only these change: the name, `ajournal_gx_x SEGS B PST ARx` -> `ajournal_gx_xR SEGS B PST
   ARx R`, `SRr SEGS` -> `SRrG SEGS R`, the post name X_post_x -> X_post_xR, and in lp_spec_g_x `lp_spec_x B PST ARx`
   -> `lp_spec_xR B PST ARx R`. The comments inside the strict texts are left out.
   Instances (X = each text): at R := wle each R text IS its strict text (X_x_wle, by conversion); so the R text at
   wle gives the strict one (X_x_of_xR), and a strict text gives the R text at every R that contains wle (X_xR_of_x,
   from WLE_R). The satisfiability lemmas at the real image are in the W_*_xR_sat.v files beside the walks. *)
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

Section w5R.
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
Variable G : list (Z * Z).
Variable RG : rep_globals.
(* W_contract_x.v:796 re_post_x at R: the journal conjunct ajournal_gx_x -> ajournal_gx_xR R; every other conjunct verbatim *)
Definition re_post_xR (regs : bvmap 5 word) ly S (Hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
(c : ctl) (O : list byte) (mx no cap out : Z) (e : list byte) (kr : nat) : world SEGS -> config -> Prop :=
fun W' c' => exists ly' S' Hp' regs' mem' md' k out',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
ajournal_gx_xR SEGS B PST ARx R G 0 [] RE_STK (spZ regs) (ablocks_fp (aout_blks cap out)) ly S Hp W mem md [] ly' S' Hp' W' mem' md' k /\
aregs_preserved regs regs' /\
apres_kept B W mem W' mem' /\
mo_le MT S S' (sl_cost MT c mx no cap (re_len e)) /\
rp_RM RP S' kr /\
(exists rest, Permutation (ablocks B ly S) (aout_blks cap out ++ rest) /\
 Permutation (ablocks B ly' S') (aout_blks (sl_cap c mx no cap (re_len e)) out' ++ rest)) /\
aout_at B RG ly' S' W' mem' (sl_ctl c (re_len e)) (sl_O c O (e ++ [Z_to_bv 8 0])) mx
  (sl_no c no (re_len e)) (sl_cap c mx no cap (re_len e)) out' /\
alock_at RG W' mem' false.
(* W_contract_x.v:811 re_spec_x at R: SRr SEGS -> SRrG SEGS R and the post re_post_xR; every premise verbatim *)
Definition re_spec_xR (pc : Z) : Prop :=
forall W ly S Hp regs mem md ch c O mx no cap out line (e : list byte) q m,
afn_pre_x SEGS B ARx RE_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 line ->
garr8 SEGS (arm W mem) line (bzs (e ++ [Z_to_bv 8 0])) -> ~ In (Z_to_bv 8 0) e ->
In (q, m) (ablocks B ly S) -> q <> out -> q <= line ->
line + re_len e <= q + req_size m ->
(forall a, line + Z.of_nat (length e) < a < line + Z.of_nat (length e) - (line + Z.of_nat (length e)) mod 8 + 8 ->
 aview SEGS (w_H W) mem a <> None) ->
aout_at B RG ly S W mem c O mx no cap out ->
alock_at RG W mem false -> rom_view SEGS W mem ->
(forall a, rg_lock RG <= a < rg_lock RG + 12 -> inG G a) -> (forall a, inG (G_SL B RG) a -> inG G a) ->
(forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ (as_errno B <= a < as_errno B + 4)) ->
sl_maxr c mx no cap (re_len e) < MMAX ->
blocks_bytes S + tr_peak (sl_tr c mx no cap (re_len e)) <= LIVE_MAX ->
mo_ok MT S (sl_cost MT c mx no cap (re_len e)) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (sl_cost MT_rk c mx no cap (re_len e)) + kr) ->
cnt_ok_pk RP re_pk (ablocks B ly S) ->
SRrG SEGS R W (cfg_at SEGS pc regs mem md) (re_post_xR regs ly S Hp W mem md c O mx no cap out e kr).
End w5R.

Section w5Ri.
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
Variable G : list (Z * Z).
Variable RG : rep_globals.
(* (a) at R := wle the R text IS the strict text (SRrG SEGS wle is SRr SEGS, ajournal_gx_xR at wle is ajournal_gx_x) *)
Lemma re_post_x_wle : re_post_x B PST ARx MT RP G RG = re_post_xR B PST ARx (@wle SEGS) MT RP G RG.
Proof. reflexivity. Qed.
Lemma re_spec_x_wle : re_spec_x B PST ARx MT RP MMAX G RG = re_spec_xR B PST ARx (@wle SEGS) MT RP MMAX G RG.
Proof. reflexivity. Qed.
(* (b) the R text at wle gives the strict text *)
Lemma re_post_x_of_xR : forall regs ly S Hp W mem md c O mx no cap out e kr W' c',
  re_post_xR B PST ARx (@wle SEGS) MT RP G RG regs ly S Hp W mem md c O mx no cap out e kr W' c' ->
  re_post_x B PST ARx MT RP G RG regs ly S Hp W mem md c O mx no cap out e kr W' c'.
Proof. intros regs ly S Hp W mem md c O mx no cap out e kr W' c' H. exact H. Qed.
Lemma re_spec_x_of_xR : forall pc,
  re_spec_xR B PST ARx (@wle SEGS) MT RP MMAX G RG pc -> re_spec_x B PST ARx MT RP MMAX G RG pc.
Proof. intros pc H. exact H. Qed.
(* (c) a strict text gives the R text at every R that contains wle (WLE_R); the post's journal is weakened by
   W_journal_x.ajournal_gx_xR_mono *)
Lemma re_post_xR_of_x : forall regs ly S Hp W mem md c O mx no cap out e kr W' c',
  re_post_x B PST ARx MT RP G RG regs ly S Hp W mem md c O mx no cap out e kr W' c' ->
  re_post_xR B PST ARx R MT RP G RG regs ly S Hp W mem md c O mx no cap out e kr W' c'.
Proof.
intros regs ly S Hp W mem md c O mx no cap out e kr W' c'
  (ly' & S' & Hp' & regs' & mem' & md' & k & out' & Hc & HJ & REST).
exists ly', S', Hp', regs', mem', md', k, out'. split; [exact Hc|]. split; [|exact REST].
eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ].
Qed.
Lemma re_spec_xR_of_x : forall pc, re_spec_x B PST ARx MT RP MMAX G RG pc -> re_spec_xR B PST ARx R MT RP MMAX G RG pc.
Proof.
intros pc H. unfold re_spec_xR. intros.
eapply SRrG_mono; [eapply SRr_SRrG; [exact WLE_R | eapply H; eassumption] |].
intros W' c' _ HP. exact (re_post_xR_of_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP).
Qed.
End w5Ri.

(* list_push: W_contract_x.v Section w2 / w2g at R *)
Section w2R.
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
Variable G : list (Z * Z).
Variable MMAX : Z.
(* W_contract_x.v:350 lp_post_x at R *)
Definition lp_post_xR (regs : bvmap 5 word) ly S (Hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
(LA : Z) (l : hlist) (lines : bool) (x : list byte) (kr : nat) : world SEGS -> config -> Prop :=
fun W' c' => exists ly' S' Hp' regs' mem' md' kk (l' : hlist) (d : Z),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
ajournal_gx_xR SEGS B PST ARx R G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] ly' S' Hp' W' mem' md' kk /\
aregs_preserved regs regs' /\
alist_at B ly' S' W' mem' LA l' lines /\
hl_recs l' = hl_recs l ++ [(d, x)] /\ hl_cap l' = grow_cap (hl_n l) (hl_cap l) /\
(lp_grow l = false -> hl_v l' = hl_v l) /\
(forall rest,
 Permutation (ablocks B ly S) ((if lp_grow l && negb (hl_cap l =? 0) then [(hl_v l, AREC * hl_cap l)] else []) ++ rest) ->
 Permutation (ablocks B ly' S')
   ((d, Z.of_nat (length x) + 1) :: (if lp_grow l then [(hl_v l', AREC * hl_cap l')] else []) ++ rest)) /\
apres_kept B W mem W' mem' /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H W') mem' (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)) /\
frames S' = frames S /\
mo_le MT S S' (lp_cost MT l (Z.of_nat (length x))) /\ rp_RM RP S' kr.
(* W_contract_x.v:368 lp_spec_x at R *)
Definition lp_spec_xR (pc : Z) : Prop :=
forall W ly S Hp regs mem md ch LA SRC (l : hlist) (lines : bool) (x : list byte) q k,
afn_pre_x SEGS B ARx LP_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 LA -> getr regs 11 = w64 SRC -> getr regs 12 = w64 (Z.of_nat (length x)) ->
LA mod 8 = 0 ->
alist_at B ly S W mem LA l lines ->
(forall a, LA <= a < LA + 16 -> inG G a) -> azs B LA 16 ->
(lp_grow l = true -> lp_vbytes l < MMAX) -> Z.of_nat (length x) < 2 ^ 16 ->
blocks_bytes S + tr_peak (lp_tr l (Z.of_nat (length x))) <= LIVE_MAX ->
In (q, k) (ablocks B ly S) -> q <> hl_v l -> q <= SRC -> SRC + Z.of_nat (length x) <= q + req_size k ->
garr8 SEGS (mrestrict (w_H W) mem) SRC (bzs x) ->
(lines = true -> ~ In (Z_to_bv 8 0) x /\ Z.of_nat (length x) <= APARTIAL) ->
(lines = false -> (1 <= length x)%nat) ->
mo_ok MT S (lp_cost MT l (Z.of_nat (length x))) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (lp_cost MT_rk l (Z.of_nat (length x))) + kr) ->
cnt_ok_pk RP (lp_peak l (Z.of_nat (length x))) (ablocks B ly S) ->
SRrG SEGS R W (cfg_at SEGS pc regs mem md) (lp_post_xR regs ly S Hp W mem md LA l lines x kr).
End w2R.
Section w2gR.
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
(* W_contract_x.v:479 lp_spec_g_x at R *)
Definition lp_spec_g_xR (pc : Z) : Prop := forall G, gx_ok SEGS B G -> gx_rt B G -> lp_spec_xR B PST ARx R MT RP G MMAX pc.
End w2gR.

(* drain: W_contract_x.v Section s7 at R *)
Section s7dR.
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
(* W_contract_x.v:715 dr_post_x at R *)
Definition dr_post_xR (regs : bvmap 5 word) ly S (Hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
(SA HA : Z) (e : rentry) (h : hsrc) (c : ctl) (O : list byte) (mx no cap out : Z) (kr : nat) : world SEGS -> config -> Prop :=
fun W' c' => exists ly' S' Hp' regs' mem' md' k (e' : rentry) (h' : hsrc) (out' ev' : Z) (LB : list byte) rest,
let fin := dr_fin c mx no cap e h in
let live := dr_live c h in
let cap' := if live then drain_b_c.ds_ocap fin else cap in
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
ajournal_gx_xR SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (spZ regs) (dr_fp SA e h cap out) ly S Hp W mem md [] ly' S' Hp' W' mem' md' k /\
aregs_preserved regs regs' /\
apres_kept B W mem W' mem' /\
mo_le MT S S' (dr_cost MT c mx no cap e h) /\
rp_RM RP S' kr /\
Permutation (ablocks B ly S) (aentry_blks e ++ asrc_blks h ++ aout_blks cap out ++ rest) /\
Permutation (ablocks B ly' S') (aentry_blks e' ++ asrc_blks h' ++ aout_blks cap' out' ++ rest) /\
garr8 SEGS (arm W' mem') SA (bzs (entry_bytes e')) /\ awr W' mem' SA AENT /\ aentry_ok B ly' S' W' mem' e' /\
re_fd e' = re_fd e /\ re_eof e' = (if hs_closed h =? 1 then 1 else re_eof e) /\ 0 < re_cap e' /\
re_cap e' = drain_b_c.ds_cap fin /\ bzs (re_U e') = drain_b_c.ds_u fin /\
re_skip e' = (if drain_b_c.ds_skip fin then 1 else 0) /\
drain_b_c.keys_texts (re_keys e') = drain_b_c.ds_H fin /\ drain_b_c.ent_ka e' = drain_b_c.ds_ka fin /\
((re_hp e' = re_hp e /\ re_kh e' = re_kh e) \/ re_kh e' <= 2 ^ 30) /\
NoDup (drain_b_c.keys_texts (re_keys e')) /\
same_set (drain_b_c.keys_texts (re_keys e')) (upds (drain_b_c.keys_texts (re_keys e)) (dr_lines h)) /\
asrc_at B ly' S' W' mem' HA h' /\
(forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> ~ (HA <= a < HA + ASRC) -> abyte_kept W mem W' mem' a) /\
hl_cap (hs_expected h') = drain_b_c.ds_ecap fin /\
hl_cap (hs_expected h') <= Z.max 8 (Z.max (hl_cap (hs_expected h)) (2 * hl_n (hs_expected h'))) /\
hs_fd h' = hs_fd h /\ hs_closed h' = hs_closed h /\ hs_eintr h' = 0 /\
hl_recs (hs_pending h') = [] /\ hs_off h' = 0 /\
hl_v (hs_pending h') = hl_v (hs_pending h) /\ hl_cap (hs_pending h') = hl_cap (hs_pending h) /\
hs_partial h' = hs_partial h /\
hs_state h' = feed (hs_state h) (bzs (pending_stream h)) /\
map snd (hl_recs (hs_expected h')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) /\
firstn (length (hl_recs (hs_expected h))) (hl_recs (hs_expected h')) = hl_recs (hs_expected h) /\
hs_held h' = hs_held h /\
re_skip e' = hs_overlong h' /\ (re_skip e' = 0 -> bzs (re_U e') = bzs (hs_W h')) /\
bzs LB = with_nul (dr_lines h) /\
aout_at B RG ly' S' W' mem' (dr_ctl c h ev') (if live then O ++ LB else O) mx (if live then no + dr_tot h else no) cap' out'.
(* W_contract_x.v:756 dr_spec_x at R *)
Definition dr_spec_xR (pc : Z) : Prop :=
forall W ly S Hp regs mem md ch (G SA : Z) (e : rentry) (j : nat) (h : hsrc) (c : ctl) (O : list byte) (mx no cap out : Z),
let HA := rg_s RG + ASRC * Z.of_nat j in
afn_pre_x SEGS B ARx DRAIN_STK_x ly S Hp W regs mem md ch ->
getr regs 10 = w64 SA ->
In (G, ATABLE) (ablocks B ly S) -> G <= SA -> SA + AENT <= G + ATABLE ->
SA mod 8 = 0 ->
garr8 SEGS (arm W mem) SA (bzs (entry_bytes e)) -> awr W mem SA AENT -> aentry_ok B ly S W mem e ->
(j < 4)%nat -> asrc_at B ly S W mem HA h -> aothers_at RG W mem j (re_fd e) ->
hs_fd h = re_fd e -> re_skip e = hs_overlong h -> (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h)) ->
aout_at B RG ly S W mem c O mx no cap out ->
rom_view SEGS W mem ->
(exists rest, Permutation (ablocks B ly S) ((G, ATABLE) :: aentry_blks e ++ asrc_blks h ++ aout_blks cap out ++ rest)) ->
Z.of_nat (length (pending_stream h)) < 2 ^ 26 -> hl_cap (hs_expected h) < 2 ^ 26 ->
re_nheld e + Z.of_nat (length (pending_stream h)) < 2 ^ 26 ->
tr_max (dr_tr c mx no cap e h) < MMAX ->
blocks_bytes S + tr_peak (dr_tr c mx no cap e h) <= LIVE_MAX ->
mo_ok MT S (dr_cost MT c mx no cap e h) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (dr_cost MT_rk c mx no cap e h) + kr) ->
cnt_ok_pk RP (dr_pk c mx no cap e h) (ablocks B ly S) ->
SRrG SEGS R W (cfg_at SEGS pc regs mem md) (dr_post_xR regs ly S Hp W mem md SA HA e h c O mx no cap out kr).
End s7dR.

(* gesture_end and gestures_end: W_contract_x.v Section w4 at R *)
Section w4R.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Abbreviation VAL := (@pa_val _ fr_prog_listing PI).
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
(* W_contract_x.v:1017 ge_post_x at R *)
Definition ge_post_xR (regs : bvmap 5 word) ly S (Hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
(c : ctl) (O : list byte) (mx no cap out : Z) (x : list byte) (kr : nat) : world SEGS -> config -> Prop :=
fun W' c' => exists ly' S' Hp' regs' mem' md' k out',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
ajournal_gx_xR SEGS B PST ARx R (G_SL B RG) 0 [] GE_STK (spZ regs) (ablocks_fp (aout_blks cap out)) ly S Hp W mem md [] ly' S' Hp' W' mem' md' k /\
aregs_preserved regs regs' /\
apres_kept B W mem W' mem' /\
mo_le MT S S' (ge_cost MT c mx no cap (Z.of_nat (length x))) /\
rp_RM RP S' kr /\
(exists rest, Permutation (ablocks B ly S) (aout_blks cap out ++ rest) /\
 Permutation (ablocks B ly' S') (aout_blks (ge_cap c mx no cap (Z.of_nat (length x))) out' ++ rest)) /\
aout_at B RG ly' S' W' mem' (ge_ctl c (Z.of_nat (length x))) (ge_O c O x) mx
  (ge_no c no (Z.of_nat (length x))) (ge_cap c mx no cap (Z.of_nat (length x))) out'.
(* W_contract_x.v:1031 ge_spec_x at R *)
Definition ge_spec_xR (pc : Z) : Prop :=
forall W ly S Hp regs mem md ch c O mx no cap out Hk (x : list byte) q m,
afn_pre_x SEGS B ARx GE_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 Hk ->
aout_at B RG ly S W mem c O mx no cap out ->
garr8 SEGS (arm W mem) Hk (bzs (x ++ [Z_to_bv 8 0])) -> ~ In (Z_to_bv 8 0) x ->
14 <= Z.of_nat (length x) <= APARTIAL ->
In (q, m) (ablocks B ly S) -> q <> out -> q <= Hk -> Hk + Z.of_nat (length x) + 1 <= q + req_size m ->
garr8 SEGS (arm W mem) (VAL A_lit_end5) (bzs END5) -> rom_view SEGS W mem ->
ge_room MMAX (blocks_bytes S) c mx no cap (Z.of_nat (length x)) ->
mo_ok MT S (ge_cost MT c mx no cap (Z.of_nat (length x))) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (ge_cost MT_rk c mx no cap (Z.of_nat (length x))) + kr) ->
cnt_ok_pk RP ge_pk (ablocks B ly S) ->
SRrG SEGS R W (cfg_at SEGS pc regs mem md) (ge_post_xR regs ly S Hp W mem md c O mx no cap out x kr).
(* W_contract_x.v:1047 gse_post_x at R *)
Definition gse_post_xR (regs : bvmap 5 word) ly S (Hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
(SA TB : Z) (e : rentry) (c : ctl) (O : list byte) (mx no cap out : Z) (rest : list (Z * Z)) (kr : nat) : world SEGS -> config -> Prop :=
fun W' c' => exists ly' S' Hp' regs' mem' md' k out',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
ajournal_gx_xR SEGS B PST ARx R (G_SL B RG) 0 [] GSE_STK (spZ regs) ((SA + 40, SA + 52) :: ablocks_fp (gse_blks e ++ aout_blks cap out))
  ly S Hp W mem md [] ly' S' Hp' W' mem' md' k /\
aregs_preserved regs regs' /\
apres_kept B W mem W' mem' /\
mo_le MT S S' (gse_cost MT c mx no cap (gse_keys e)) /\
rp_RM RP S' kr /\
Permutation (ablocks B ly' S') ((TB, ATABLE) :: aout_blks (gse_cap (gse_run c O mx no cap (gse_keys e))) out' ++ rest) /\
aout_at B RG ly' S' W' mem' (gse_c (gse_run c O mx no cap (gse_keys e))) (gse_O (gse_run c O mx no cap (gse_keys e))) mx
  (gse_no (gse_run c O mx no cap (gse_keys e))) (gse_cap (gse_run c O mx no cap (gse_keys e))) out' /\
garr8 SEGS (arm W' mem') SA (bzs (entry_bytes (entry_cleared e))) /\ awr W' mem' SA AENT.
(* W_contract_x.v:1062 gse_spec_x at R *)
Definition gse_spec_xR (pc : Z) : Prop :=
forall W ly S Hp regs mem md ch SA TB e c O mx no cap out rest,
afn_pre_x SEGS B ARx GSE_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 SA ->
In (TB, ATABLE) (ablocks B ly S) -> TB <= SA -> SA + AENT <= TB + ATABLE -> SA mod 8 = 0 ->
garr8 SEGS (arm W mem) SA (bzs (entry_bytes e)) -> awr W mem SA AENT -> aheld_ok B ly S W mem e ->
aout_at B RG ly S W mem c O mx no cap out ->
Permutation (ablocks B ly S) ((TB, ATABLE) :: gse_blks e ++ aout_blks cap out ++ rest) ->
garr8 SEGS (arm W mem) (VAL A_lit_end5) (bzs END5) -> rom_view SEGS W mem ->
gse_room MMAX (blocks_bytes S) c mx no cap (gse_keys e) ->
mo_ok MT S (gse_cost MT c mx no cap (gse_keys e)) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (gse_cost MT_rk c mx no cap (gse_keys e)) + kr) ->
cnt_ok_pk RP gse_pk (ablocks B ly S) ->
SRrG SEGS R W (cfg_at SEGS pc regs mem md) (gse_post_xR regs ly S Hp W mem md SA TB e c O mx no cap out rest kr).
End w4R.

(* relay_finish: W_contract_x.v Section w5f / rfs at R *)
Section rfsR.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Abbreviation VAL := (@pa_val _ fr_prog_listing PI).
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
Variable G : list (Z * Z).
Variable RG : rep_globals.
Variable GTU GL : Z.
Variable CTX : list (list Z).
(* W_contract_x.v:1151 rf_post_x at R *)
Definition rf_post_xR (regs : bvmap 5 word) ly S (Hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
(T : Z) (es : list rentry) (c : ctl) (O : list byte) (mx no cap out : Z) (rest : list (Z * Z)) (kr : nat) : world SEGS -> config -> Prop :=
fun W' c' => exists ly' S' Hp' regs' mem' md' k out',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
ajournal_gx_xR SEGS B PST ARx R G 0 [] RF_STK (spZ regs) (rf_FP T es cap out) ly S Hp W mem md [] ly' S' Hp' W' mem' md' k /\
aregs_preserved regs regs' /\
apres_kept B W mem W' mem' /\
frames S' = frames S /\
mo_le MT S S' (rf_cost MT c O mx no cap es) /\
rp_RM RP S' kr /\
Permutation (ablocks B ly' S') (rf_tblk T ++ aout_blks (gse_cap (rf_run c O mx no cap es)) out' ++ rest) /\
aout_at B RG ly' S' W' mem' (rf_ctl (gse_c (rf_run c O mx no cap es))) (gse_O (rf_run c O mx no cap es)) mx
  (gse_no (rf_run c O mx no cap es)) (gse_cap (rf_run c O mx no cap es)) out' /\
alock_at RG W' mem' false /\
ra_rel B RG ly' S' W' mem' T [] /\
val_mem SEGS (arm W' mem') GL 4 (2 ^ 32 - 1) /\ awr W' mem' GL 4.
(* W_contract_x.v:1168 rf_spec_x at R *)
Definition rf_spec_xR (pc : Z) : Prop :=
forall W ly S Hp regs mem md ch T es c O mx no cap out rest,
afn_pre_x SEGS B ARx RF_STK ly S Hp W regs mem md ch -> spZ regs mod 32 = 0 ->
count_cid 0 (frames S) < fs_frames 0 ->
val_mem SEGS (arm W mem) GTU 1 0 ->
alock_at RG W mem false ->
ra_rel B RG ly S W mem T es ->
(exists lst, val_mem SEGS (arm W mem) GL 4 lst) -> awr W mem GL 4 ->
aout_at B RG ly S W mem c O mx no cap out ->
Permutation (ablocks B ly S) (rf_tblk T ++ rf_eblks es ++ aout_blks cap out ++ rest) ->
garr8 SEGS (arm W mem) (VAL A_lit_end5) (bzs END5) -> rom_view SEGS W mem ->
(forall a, inG (RF_G RG GL) a -> inG G a) -> (forall a, inG (G_SL B RG) a -> inG G a) ->
(forall a, inG (RF_G RG GL) a -> ~ (as_errno B <= a < as_errno B + 4)) ->
rf_room MMAX (blocks_bytes S) c O mx no cap es ->
In [pc + 200] CTX ->
mo_ok MT S (rf_cost MT c O mx no cap es) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (rf_cost MT_rk c O mx no cap es) + kr) ->
cnt_ok_pk RP rf_pk (ablocks B ly S) ->
SRrG SEGS R W (cfg_at SEGS pc regs mem md) (rf_post_xR regs ly S Hp W mem md T es c O mx no cap out rest kr).
End rfsR.

Section w2Ri.
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
Variable G : list (Z * Z).
Variable MMAX : Z.
(* list_push: (a) X_x_wle, (b) X_x_of_xR, (c) X_xR_of_x (from WLE_R; the post journal by W_journal_x.ajournal_gx_xR_mono) *)
Lemma lp_post_x_wle : lp_post_x B PST ARx MT RP G = lp_post_xR B PST ARx (@wle SEGS) MT RP G.
Proof. reflexivity. Qed.
Lemma lp_post_x_of_xR : forall regs ly S Hp W mem md LA l lines x kr W' c',
  lp_post_xR B PST ARx (@wle SEGS) MT RP G regs ly S Hp W mem md LA l lines x kr W' c' ->
  lp_post_x B PST ARx MT RP G regs ly S Hp W mem md LA l lines x kr W' c'.
Proof. intros regs ly S Hp W mem md LA l lines x kr W' c' H. exact H. Qed.
Lemma lp_post_xR_of_x : forall regs ly S Hp W mem md LA l lines x kr W' c',
  lp_post_x B PST ARx MT RP G regs ly S Hp W mem md LA l lines x kr W' c' ->
  lp_post_xR B PST ARx R MT RP G regs ly S Hp W mem md LA l lines x kr W' c'.
Proof.
intros regs ly S Hp W mem md LA l lines x kr W' c'
  (ly' & S' & Hp' & regs' & mem' & md' & kk & l' & d & Hc & HJ & REST).
exists ly', S', Hp', regs', mem', md', kk, l', d. split; [exact Hc|]. split; [|exact REST].
eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ].
Qed.
Lemma lp_spec_x_wle : lp_spec_x B PST ARx MT RP G MMAX = lp_spec_xR B PST ARx (@wle SEGS) MT RP G MMAX.
Proof. reflexivity. Qed.
Lemma lp_spec_x_of_xR : forall pc, lp_spec_xR B PST ARx (@wle SEGS) MT RP G MMAX pc -> lp_spec_x B PST ARx MT RP G MMAX pc.
Proof. intros pc H. exact H. Qed.
Lemma lp_spec_xR_of_x : forall pc, lp_spec_x B PST ARx MT RP G MMAX pc -> lp_spec_xR B PST ARx R MT RP G MMAX pc.
Proof.
intros pc H. unfold lp_spec_xR. intros.
eapply SRrG_mono; [eapply SRr_SRrG; [exact WLE_R | eapply H; eassumption] |].
intros W' c' _ HP. eapply lp_post_xR_of_x. exact HP.
Qed.
End w2Ri.

Section w2gRi.
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
Lemma lp_spec_g_x_wle : lp_spec_g_x B PST ARx MT RP MMAX = lp_spec_g_xR B PST ARx (@wle SEGS) MT RP MMAX.
Proof. reflexivity. Qed.
Lemma lp_spec_g_x_of_xR : forall pc, lp_spec_g_xR B PST ARx (@wle SEGS) MT RP MMAX pc -> lp_spec_g_x B PST ARx MT RP MMAX pc.
Proof. intros pc H. exact H. Qed.
Lemma lp_spec_g_xR_of_x : forall pc, lp_spec_g_x B PST ARx MT RP MMAX pc -> lp_spec_g_xR B PST ARx R MT RP MMAX pc.
Proof.
intros pc H G0 H1 H2. apply lp_spec_xR_of_x; [exact WLE_R | exact (H G0 H1 H2)].
Qed.
End w2gRi.

Section s7dRi.
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
(* drain *)
Lemma dr_post_x_wle : dr_post_x B PST ARx MT RP RG = dr_post_xR B PST ARx (@wle SEGS) MT RP RG.
Proof. reflexivity. Qed.
Lemma dr_post_x_of_xR : forall regs ly S Hp W mem md SA HA e h c O mx no cap out kr W' c',
  dr_post_xR B PST ARx (@wle SEGS) MT RP RG regs ly S Hp W mem md SA HA e h c O mx no cap out kr W' c' ->
  dr_post_x B PST ARx MT RP RG regs ly S Hp W mem md SA HA e h c O mx no cap out kr W' c'.
Proof. intros regs ly S Hp W mem md SA HA e h c O mx no cap out kr W' c' H. exact H. Qed.
Lemma dr_post_xR_of_x : forall regs ly S Hp W mem md SA HA e h c O mx no cap out kr W' c',
  dr_post_x B PST ARx MT RP RG regs ly S Hp W mem md SA HA e h c O mx no cap out kr W' c' ->
  dr_post_xR B PST ARx R MT RP RG regs ly S Hp W mem md SA HA e h c O mx no cap out kr W' c'.
Proof.
intros regs ly S Hp W mem md SA HA e h c O mx no cap out kr W' c'
  (ly' & S' & Hp' & regs' & mem' & md' & k & e' & h' & out' & ev' & LB & rest & H).
exists ly', S', Hp', regs', mem', md', k, e', h', out', ev', LB, rest. cbv zeta in H |- *. destruct H as (Hc & HJ & REST). split; [exact Hc|]. split; [|exact REST].
eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ].
Qed.
Lemma dr_spec_x_wle : dr_spec_x B PST ARx MT RP MMAX RG = dr_spec_xR B PST ARx (@wle SEGS) MT RP MMAX RG.
Proof. reflexivity. Qed.
Lemma dr_spec_x_of_xR : forall pc, dr_spec_xR B PST ARx (@wle SEGS) MT RP MMAX RG pc -> dr_spec_x B PST ARx MT RP MMAX RG pc.
Proof. intros pc H. exact H. Qed.
Lemma dr_spec_xR_of_x : forall pc, dr_spec_x B PST ARx MT RP MMAX RG pc -> dr_spec_xR B PST ARx R MT RP MMAX RG pc.
Proof.
intros pc H. unfold dr_spec_xR. unfold dr_spec_x in H. cbv zeta in H |- *. intros.
eapply SRrG_mono; [eapply SRr_SRrG; [exact WLE_R | eapply H; eassumption] |].
intros W' c' _ HP. eapply dr_post_xR_of_x. exact HP.
Qed.
End s7dRi.

Section w4Ri.
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
(* gesture_end and gestures_end *)
Lemma ge_post_x_wle : ge_post_x B PST ARx MT RP RG = ge_post_xR B PST ARx (@wle SEGS) MT RP RG.
Proof. reflexivity. Qed.
Lemma ge_post_x_of_xR : forall regs ly S Hp W mem md c O mx no cap out x kr W' c',
  ge_post_xR B PST ARx (@wle SEGS) MT RP RG regs ly S Hp W mem md c O mx no cap out x kr W' c' ->
  ge_post_x B PST ARx MT RP RG regs ly S Hp W mem md c O mx no cap out x kr W' c'.
Proof. intros regs ly S Hp W mem md c O mx no cap out x kr W' c' H. exact H. Qed.
Lemma ge_post_xR_of_x : forall regs ly S Hp W mem md c O mx no cap out x kr W' c',
  ge_post_x B PST ARx MT RP RG regs ly S Hp W mem md c O mx no cap out x kr W' c' ->
  ge_post_xR B PST ARx R MT RP RG regs ly S Hp W mem md c O mx no cap out x kr W' c'.
Proof.
intros regs ly S Hp W mem md c O mx no cap out x kr W' c'
  (ly' & S' & Hp' & regs' & mem' & md' & k & out' & Hc & HJ & REST).
exists ly', S', Hp', regs', mem', md', k, out'. split; [exact Hc|]. split; [|exact REST].
eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ].
Qed.
Lemma ge_spec_x_wle : ge_spec_x B PST ARx MT RP MMAX RG = ge_spec_xR B PST ARx (@wle SEGS) MT RP MMAX RG.
Proof. reflexivity. Qed.
Lemma ge_spec_x_of_xR : forall pc, ge_spec_xR B PST ARx (@wle SEGS) MT RP MMAX RG pc -> ge_spec_x B PST ARx MT RP MMAX RG pc.
Proof. intros pc H. exact H. Qed.
Lemma ge_spec_xR_of_x : forall pc, ge_spec_x B PST ARx MT RP MMAX RG pc -> ge_spec_xR B PST ARx R MT RP MMAX RG pc.
Proof.
intros pc H. unfold ge_spec_xR. intros.
eapply SRrG_mono; [eapply SRr_SRrG; [exact WLE_R | eapply H; eassumption] |].
intros W' c' _ HP. eapply ge_post_xR_of_x. exact HP.
Qed.
Lemma gse_post_x_wle : gse_post_x B PST ARx MT RP RG = gse_post_xR B PST ARx (@wle SEGS) MT RP RG.
Proof. reflexivity. Qed.
Lemma gse_post_x_of_xR : forall regs ly S Hp W mem md SA TB e c O mx no cap out rest kr W' c',
  gse_post_xR B PST ARx (@wle SEGS) MT RP RG regs ly S Hp W mem md SA TB e c O mx no cap out rest kr W' c' ->
  gse_post_x B PST ARx MT RP RG regs ly S Hp W mem md SA TB e c O mx no cap out rest kr W' c'.
Proof. intros regs ly S Hp W mem md SA TB e c O mx no cap out rest kr W' c' H. exact H. Qed.
Lemma gse_post_xR_of_x : forall regs ly S Hp W mem md SA TB e c O mx no cap out rest kr W' c',
  gse_post_x B PST ARx MT RP RG regs ly S Hp W mem md SA TB e c O mx no cap out rest kr W' c' ->
  gse_post_xR B PST ARx R MT RP RG regs ly S Hp W mem md SA TB e c O mx no cap out rest kr W' c'.
Proof.
intros regs ly S Hp W mem md SA TB e c O mx no cap out rest kr W' c'
  (ly' & S' & Hp' & regs' & mem' & md' & k & out' & Hc & HJ & REST).
exists ly', S', Hp', regs', mem', md', k, out'. split; [exact Hc|]. split; [|exact REST].
eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ].
Qed.
Lemma gse_spec_x_wle : gse_spec_x B PST ARx MT RP MMAX RG = gse_spec_xR B PST ARx (@wle SEGS) MT RP MMAX RG.
Proof. reflexivity. Qed.
Lemma gse_spec_x_of_xR : forall pc, gse_spec_xR B PST ARx (@wle SEGS) MT RP MMAX RG pc -> gse_spec_x B PST ARx MT RP MMAX RG pc.
Proof. intros pc H. exact H. Qed.
Lemma gse_spec_xR_of_x : forall pc, gse_spec_x B PST ARx MT RP MMAX RG pc -> gse_spec_xR B PST ARx R MT RP MMAX RG pc.
Proof.
intros pc H. unfold gse_spec_xR. intros.
eapply SRrG_mono; [eapply SRr_SRrG; [exact WLE_R | eapply H; eassumption] |].
intros W' c' _ HP. eapply gse_post_xR_of_x. exact HP.
Qed.
End w4Ri.

Section rfsRi.
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
Variable G : list (Z * Z).
Variable RG : rep_globals.
Variable GTU GL : Z.
Variable CTX : list (list Z).
(* relay_finish *)
Lemma rf_post_x_wle : rf_post_x B PST ARx MT RP G RG GL = rf_post_xR B PST ARx (@wle SEGS) MT RP G RG GL.
Proof. reflexivity. Qed.
Lemma rf_post_x_of_xR : forall regs ly S Hp W mem md T es c O mx no cap out rest kr W' c',
  rf_post_xR B PST ARx (@wle SEGS) MT RP G RG GL regs ly S Hp W mem md T es c O mx no cap out rest kr W' c' ->
  rf_post_x B PST ARx MT RP G RG GL regs ly S Hp W mem md T es c O mx no cap out rest kr W' c'.
Proof. intros regs ly S Hp W mem md T es c O mx no cap out rest kr W' c' H. exact H. Qed.
Lemma rf_post_xR_of_x : forall regs ly S Hp W mem md T es c O mx no cap out rest kr W' c',
  rf_post_x B PST ARx MT RP G RG GL regs ly S Hp W mem md T es c O mx no cap out rest kr W' c' ->
  rf_post_xR B PST ARx R MT RP G RG GL regs ly S Hp W mem md T es c O mx no cap out rest kr W' c'.
Proof.
intros regs ly S Hp W mem md T es c O mx no cap out rest kr W' c'
  (ly' & S' & Hp' & regs' & mem' & md' & k & out' & Hc & HJ & REST).
exists ly', S', Hp', regs', mem', md', k, out'. split; [exact Hc|]. split; [|exact REST].
eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ].
Qed.
Lemma rf_spec_x_wle : rf_spec_x B PST ARx MT RP MMAX G RG GTU GL CTX = rf_spec_xR B PST ARx (@wle SEGS) MT RP MMAX G RG GTU GL CTX.
Proof. reflexivity. Qed.
Lemma rf_spec_x_of_xR : forall pc, rf_spec_xR B PST ARx (@wle SEGS) MT RP MMAX G RG GTU GL CTX pc -> rf_spec_x B PST ARx MT RP MMAX G RG GTU GL CTX pc.
Proof. intros pc H. exact H. Qed.
Lemma rf_spec_xR_of_x : forall pc, rf_spec_x B PST ARx MT RP MMAX G RG GTU GL CTX pc -> rf_spec_xR B PST ARx R MT RP MMAX G RG GTU GL CTX pc.
Proof.
intros pc H. unfold rf_spec_xR. intros.
eapply SRrG_mono; [eapply SRr_SRrG; [exact WLE_R | eapply H; eassumption] |].
intros W' c' _ HP. eapply rf_post_xR_of_x. exact HP.
Qed.
End rfsRi.
