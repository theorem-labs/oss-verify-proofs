(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_contract_x.v; 195 of its 388 lines of code are new or changed and 1819 lines of the source are left out. *)
(* Contract texts of lib/A/W_contract_x.v at a world relation R, for list_free (lf_post_x :321, lf_spec_x :334,
   lf_spec_g_x :474), source_reset (sr_post_x :388, sr_spec_x :399, sr_spec_g_x :476), relay_add (ra_post_x :831,
   ra_spec_x :850, ra_spec_g_x :881) and check_shape_done (aleaf_post_x :106, csd_spec_x :128).  A beside-file of
   W_contract_xR.v (a Theorem Labs lane's), written in its form: R is a Section variable right after ARx, with its laws R_refl,
   R_trans, WLE_R (the definitions use none of them), and the SAME R is in the post journal
   (W_journal_x.ajournal_gx_xR) and in the step relation (YA0nH.SRrG SEGS R).
   Against the strict texts only these change: the name, `ajournal_gx_x SEGS B PST ARx` -> `ajournal_gx_xR SEGS B PST
   ARx R`, `SRr SEGS` -> `SRrG SEGS R`, the post name X_post_x -> X_post_xR, and in X_spec_g_x `X_spec_x B PST ARx` ->
   `X_spec_xR B PST ARx R`.  The comments inside the strict texts are left out.
   Instances: at R := wle each R text IS its strict text (X_x_wle, by conversion); the R text at wle gives the strict
   one (X_x_of_xR); a strict text gives the R text at every R that contains wle (X_xR_of_x, from WLE_R).
   rule 24: proves no function (kind: statement text; contract twins, no walk). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_kit W_journal W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YI00 YN0h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require next_line_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require send_line_c send_line_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayRunT drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require gesture_end_c relay_remove_b_c relay_instance_gone_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require gesture_end_b_c RelayRunF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YCe5x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require ListTr HarnessTr RelayRunF.
(* the import block above is W_contract_x.v's (lines 42-77), so every name of the texts resolves as there *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

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
(* W_contract_x.v:321 lf_post_x at R *)
Definition lf_post_xR (regs : bvmap 5 word) ly S (Hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
(LA : Z) (l : hlist) (lines : bool) (kr : nat) : world SEGS -> config -> Prop :=
fun W' c' => exists ly' S' Hp' regs' mem' md' kk,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
ajournal_gx_xR SEGS B PST ARx R G 0 [] LF_STK (spZ regs) (blk_FP (list_blks l)) ly S Hp W mem md [] ly' S' Hp' W' mem' md' kk /\
aregs_preserved regs regs' /\
alist_at B ly' S' W' mem' LA empty_list lines /\
(forall rest, Permutation (ablocks B ly S) (list_blks l ++ rest) -> Permutation (ablocks B ly' S') rest) /\
apres_kept B W mem W' mem' /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H W') mem' (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)) /\
frames S' = frames S /\
mo_le MT S S' (lf_cost MT l) /\ rp_RM RP S' kr.
(* W_contract_x.v:334 lf_spec_x at R *)
Definition lf_spec_xR (pc : Z) : Prop :=
forall W ly S Hp regs mem md ch LA (l : hlist) (lines : bool),
afn_pre_x SEGS B ARx LF_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 LA ->
LA mod 8 = 0 ->
alist_at B ly S W mem LA l lines ->
(forall a, LA <= a < LA + 16 -> inG G a) -> azs B LA 16 ->
rom_view SEGS W mem ->
mo_ok MT S (lf_cost MT l) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (lf_cost MT_rk l) + kr) ->
cnt_ok_pk RP lf_pk (ablocks B ly S) ->
SRrG SEGS R W (cfg_at SEGS pc regs mem md) (lf_post_xR regs ly S Hp W mem md LA l lines kr).
(* W_contract_x.v:388 sr_post_x at R *)
Definition sr_post_xR (regs : bvmap 5 word) ly S (Hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
(HA : Z) (o : option hsrc) (kr : nat) : world SEGS -> config -> Prop :=
fun W' c' => exists ly' S' Hp' regs' mem' md' kk,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
ajournal_gx_xR SEGS B PST ARx R G 0 [] SR_STK (spZ regs) (blk_FP (sr_blks o)) ly S Hp W mem md [] ly' S' Hp' W' mem' md' kk /\
aregs_preserved regs regs' /\
asrc_closed W' mem' HA /\
(forall rest, Permutation (ablocks B ly S) (sr_blks o ++ rest) -> Permutation (ablocks B ly' S') rest) /\
apres_kept B W mem W' mem' /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H W') mem' (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)) /\
frames S' = frames S /\
mo_le MT S S' (sr_cost MT o) /\ rp_RM RP S' kr.
(* W_contract_x.v:399 sr_spec_x at R *)
Definition sr_spec_xR (pc : Z) : Prop :=
forall W ly S Hp regs mem md ch HA (o : option hsrc),
afn_pre_x SEGS B ARx SR_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 HA ->
HA mod 8 = 0 ->
match o with Some h => asrc_at B ly S W mem HA h | None => asrc_closed W mem HA end ->
(forall a, HA <= a < HA + ASRC -> inG G a) -> azs B HA ASRC ->
rom_view SEGS W mem ->
mo_ok MT S (sr_cost MT o) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (sr_cost MT_rk o) + kr) ->
cnt_ok_pk RP sr_pk (ablocks B ly S) ->
SRrG SEGS R W (cfg_at SEGS pc regs mem md) (sr_post_xR regs ly S Hp W mem md HA o kr).
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
(* W_contract_x.v:474 lf_spec_g_x at R *)
Definition lf_spec_g_xR (pc : Z) : Prop := forall G, gx_prog_x B ARx G -> lf_spec_xR B PST ARx R MT RP G pc.
(* W_contract_x.v:476 sr_spec_g_x at R *)
Definition sr_spec_g_xR (pc : Z) : Prop := forall G, gx_prog_x B ARx G -> sr_spec_xR B PST ARx R MT RP G pc.
End w2gR.

(* ---- the instances ---- *)
Section w2Ri.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable G : list (Z * Z).
Lemma lf_post_x_wle : lf_post_x B PST ARx MT RP G = lf_post_xR B PST ARx (@wle SEGS) MT RP G.
Proof. reflexivity. Qed.
Lemma lf_spec_x_wle : lf_spec_x B PST ARx MT RP G = lf_spec_xR B PST ARx (@wle SEGS) MT RP G.
Proof. reflexivity. Qed.
Lemma lf_spec_x_of_xR : forall pc, lf_spec_xR B PST ARx (@wle SEGS) MT RP G pc -> lf_spec_x B PST ARx MT RP G pc.
Proof. intros pc H. exact H. Qed.
Lemma lf_post_xR_of_x : forall regs ly S Hp W mem md LA l lines kr W' c',
  lf_post_x B PST ARx MT RP G regs ly S Hp W mem md LA l lines kr W' c' ->
  lf_post_xR B PST ARx R MT RP G regs ly S Hp W mem md LA l lines kr W' c'.
Proof.
intros regs ly S Hp W mem md LA l lines kr W' c' (ly' & S' & Hp' & regs' & mem' & md' & kk & Hc & HJ & REST).
exists ly', S', Hp', regs', mem', md', kk. split; [exact Hc|]. split; [|exact REST].
eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ].
Qed.
Lemma lf_spec_xR_of_x : forall pc, lf_spec_x B PST ARx MT RP G pc -> lf_spec_xR B PST ARx R MT RP G pc.
Proof.
intros pc H. unfold lf_spec_xR. intros.
eapply SRrG_mono; [eapply SRr_SRrG; [exact WLE_R | eapply H; eassumption] |].
intros W' c' _ HP. eapply lf_post_xR_of_x. exact HP.
Qed.
Lemma sr_post_x_wle : sr_post_x B PST ARx MT RP G = sr_post_xR B PST ARx (@wle SEGS) MT RP G.
Proof. reflexivity. Qed.
Lemma sr_spec_x_wle : sr_spec_x B PST ARx MT RP G = sr_spec_xR B PST ARx (@wle SEGS) MT RP G.
Proof. reflexivity. Qed.
Lemma sr_spec_x_of_xR : forall pc, sr_spec_xR B PST ARx (@wle SEGS) MT RP G pc -> sr_spec_x B PST ARx MT RP G pc.
Proof. intros pc H. exact H. Qed.
Lemma sr_post_xR_of_x : forall regs ly S Hp W mem md HA o kr W' c',
  sr_post_x B PST ARx MT RP G regs ly S Hp W mem md HA o kr W' c' ->
  sr_post_xR B PST ARx R MT RP G regs ly S Hp W mem md HA o kr W' c'.
Proof.
intros regs ly S Hp W mem md HA o kr W' c' (ly' & S' & Hp' & regs' & mem' & md' & kk & Hc & HJ & REST).
exists ly', S', Hp', regs', mem', md', kk. split; [exact Hc|]. split; [|exact REST].
eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ].
Qed.
Lemma sr_spec_xR_of_x : forall pc, sr_spec_x B PST ARx MT RP G pc -> sr_spec_xR B PST ARx R MT RP G pc.
Proof.
intros pc H. unfold sr_spec_xR. intros.
eapply SRrG_mono; [eapply SRr_SRrG; [exact WLE_R | eapply H; eassumption] |].
intros W' c' _ HP. eapply sr_post_xR_of_x. exact HP.
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
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Variable MT : ameter_ops.
Variable RP : roomp.
Lemma lf_spec_g_x_wle : lf_spec_g_x B PST ARx MT RP = lf_spec_g_xR B PST ARx (@wle SEGS) MT RP.
Proof. reflexivity. Qed.
Lemma lf_spec_g_x_of_xR : forall pc, lf_spec_g_xR B PST ARx (@wle SEGS) MT RP pc -> lf_spec_g_x B PST ARx MT RP pc.
Proof. intros pc H. exact H. Qed.
Lemma lf_spec_g_xR_of_x : forall pc, lf_spec_g_x B PST ARx MT RP pc -> lf_spec_g_xR B PST ARx R MT RP pc.
Proof. intros pc H G0 HG. apply lf_spec_xR_of_x; [exact WLE_R | exact (H G0 HG)]. Qed.
Lemma sr_spec_g_x_wle : sr_spec_g_x B PST ARx MT RP = sr_spec_g_xR B PST ARx (@wle SEGS) MT RP.
Proof. reflexivity. Qed.
Lemma sr_spec_g_x_of_xR : forall pc, sr_spec_g_xR B PST ARx (@wle SEGS) MT RP pc -> sr_spec_g_x B PST ARx MT RP pc.
Proof. intros pc H. exact H. Qed.
Lemma sr_spec_g_xR_of_x : forall pc, sr_spec_g_x B PST ARx MT RP pc -> sr_spec_g_xR B PST ARx R MT RP pc.
Proof. intros pc H G0 HG. apply sr_spec_xR_of_x; [exact WLE_R | exact (H G0 HG)]. Qed.
End w2gRi.

(* ---- relay_add (W_contract_x.v Section w5 ra_post_x :831 / ra_spec_x :850, Section w5g ra_spec_g_x :881) at R, in
   the same form: R right after ARx, `ajournal_gx_x SEGS B PST ARx` -> `ajournal_gx_xR SEGS B PST ARx R`, `SRr SEGS`
   -> `SRrG SEGS R`, ra_post_x -> ra_post_xR, `ra_spec_x B PST ARx` -> `ra_spec_xR B PST ARx R`.  op_add's R walk
   (W_op_add.v pb_op_add_xR) takes relay_add as ra_spec_g_xR.  Owner a Theorem Labs lane (NAMES.md (sha256 4a0eb3e6fe06; internal record), 22:58Z). ---- *)
Section w5R.
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
Variable RG : rep_globals.
Variable CTX : list (list Z).
(* W_contract_x.v:831 ra_post_x at R *)
Definition ra_post_xR (regs : bvmap 5 word) ly S (Hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
(fd T : Z) (es : list rentry) (kr : nat) : world SEGS -> config -> Prop :=
fun W' c' => exists ly' S' Hp' regs' mem' md' k,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
ajournal_gx_xR SEGS B PST ARx R G 0 [] RA_STK (spZ regs) (ra_FP T es) ly S Hp W mem md [] ly' S' Hp' W' mem' md' k /\
aregs_preserved regs regs' /\
apres_kept B W mem W' mem' /\ frames S' = frames S /\ mo_le MT S S' (ra_cost MT T) /\
rp_RM RP S' kr /\
alock_at RG W' mem' false /\
((fd < 0 /\ getr regs' 10 = w64 (-1) /\ ablocks B ly' S' = ablocks B ly S) \/
 (0 <= fd /\ getr regs' 10 = w64 0 /\ exists T',
   arelay_at B RG ly' S' W' mem' T' (es ++ [ra_new fd]) /\
   ((T = 0 /\ Permutation (ablocks B ly' S') ((T', ATABLE) :: ablocks B ly S)) \/
    (T <> 0 /\ T' = T /\ ablocks B ly' S' = ablocks B ly S)))) /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H W') mem' (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)).
(* W_contract_x.v:850 ra_spec_x at R *)
Definition ra_spec_xR (pc : Z) : Prop :=
forall W ly S Hp regs mem md ch fd T es,
afn_pre_x SEGS B ARx RA_STK ly S Hp W regs mem md ch -> spZ regs mod 32 = 0 ->
count_cid 0 (frames S) < fs_frames 0 ->
getr regs 10 = Z_to_bv 64 fd -> - 2 ^ 31 <= fd < 2 ^ 31 ->
alock_at RG W mem false -> awake_at RG W mem -> rom_view SEGS W mem ->
ra_rel B RG ly S W mem T es ->
(0 <= fd -> (length es < 4)%nat /\ ~ In fd (map re_fd es)) ->
(forall a, inG (RA_G RG) a -> inG G a) ->
(forall a, inG (RA_G RG) a -> ~ (as_errno B <= a < as_errno B + 4)) ->
(0 <= fd -> T = 0 -> blocks_bytes S + ATABLE <= LIVE_MAX) ->
(0 <= fd -> T = 0 -> spZ regs + 16 < ly_top ly /\ In (pc + 332 :: raZ regs :: spine ch) CTX) ->
mo_ok MT S (ra_cost MT T) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (ra_cost MT_rk T) + kr) ->
cnt_ok_pk RP (ra_peak T) (ablocks B ly S) ->
SRrG SEGS R W (cfg_at SEGS pc regs mem md) (ra_post_xR regs ly S Hp W mem md fd T es kr).
End w5R.

Section w5gR.
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
Variable RG : rep_globals.
Variable CTX : list (list Z).
(* W_contract_x.v:881 ra_spec_g_x at R *)
Definition ra_spec_g_xR (pc : Z) : Prop :=
forall G, gx_ok SEGS B G -> gx_rt B G -> ra_spec_xR B PST ARx R MT RP G RG CTX pc.
End w5gR.

Section w5Ri.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable G : list (Z * Z).
Variable RG : rep_globals.
Variable CTX : list (list Z).
Lemma ra_post_x_wle : ra_post_x B PST ARx MT RP G RG = ra_post_xR B PST ARx (@wle SEGS) MT RP G RG.
Proof. reflexivity. Qed.
Lemma ra_spec_x_wle : ra_spec_x B PST ARx MT RP G RG CTX = ra_spec_xR B PST ARx (@wle SEGS) MT RP G RG CTX.
Proof. reflexivity. Qed.
Lemma ra_spec_x_of_xR : forall pc, ra_spec_xR B PST ARx (@wle SEGS) MT RP G RG CTX pc -> ra_spec_x B PST ARx MT RP G RG CTX pc.
Proof. intros pc H. exact H. Qed.
Lemma ra_post_xR_of_x : forall regs ly S Hp W mem md fd T es kr W' c',
  ra_post_x B PST ARx MT RP G RG regs ly S Hp W mem md fd T es kr W' c' ->
  ra_post_xR B PST ARx R MT RP G RG regs ly S Hp W mem md fd T es kr W' c'.
Proof.
intros regs ly S Hp W mem md fd T es kr W' c' (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & HJ & REST).
exists ly', S', Hp', regs', mem', md', k. split; [exact Hc|]. split; [|exact REST].
eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ].
Qed.
Lemma ra_spec_xR_of_x : forall pc, ra_spec_x B PST ARx MT RP G RG CTX pc -> ra_spec_xR B PST ARx R MT RP G RG CTX pc.
Proof.
intros pc H. unfold ra_spec_xR. intros.
eapply SRrG_mono; [eapply SRr_SRrG; [exact WLE_R | eapply H; eassumption] |].
intros W' c' _ HP. eapply ra_post_xR_of_x. exact HP.
Qed.
End w5Ri.

Section w5gRi.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable RG : rep_globals.
Variable CTX : list (list Z).
Lemma ra_spec_g_x_wle : ra_spec_g_x B PST ARx MT RP RG CTX = ra_spec_g_xR B PST ARx (@wle SEGS) MT RP RG CTX.
Proof. reflexivity. Qed.
Lemma ra_spec_g_x_of_xR : forall pc, ra_spec_g_xR B PST ARx (@wle SEGS) MT RP RG CTX pc -> ra_spec_g_x B PST ARx MT RP RG CTX pc.
Proof. intros pc H. exact H. Qed.
Lemma ra_spec_g_xR_of_x : forall pc, ra_spec_g_x B PST ARx MT RP RG CTX pc -> ra_spec_g_xR B PST ARx R MT RP RG CTX pc.
Proof. intros pc H G0 H1 H2. apply ra_spec_xR_of_x; [exact WLE_R | exact (H G0 H1 H2)]. Qed.
End w5gRi.

(* ---- check_shape_done (W_contract_x.v Section c: aleaf_post_x :106, csd_spec_x :128) at R, in the same form: R right
   after ARx, `ajournal_x SEGS B PST ARx` -> `ajournal_xR SEGS B PST ARx R` (aleaf_post_x's journal is the plain one,
   not the gx one), `SRr SEGS` -> `SRrG SEGS R`, aleaf_post_x -> aleaf_post_xR.  The comment inside the strict
   aleaf_post_x is left out.  Owner a Theorem Labs lane (NAMES.md (sha256 4a0eb3e6fe06; internal record), 22:55Z / 23:01Z). ---- *)
Section cR.
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
(* W_contract_x.v:106 aleaf_post_x at R *)
Definition aleaf_post_xR (STK : Z) (regs : bvmap 5 word) ly S (Hp : list Z) (W : world SEGS)
(mem : word -> option byte) (md : Model) (Pa0 : word -> Prop) : world SEGS -> config -> Prop :=
fun W' c' => exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
ajournal_xR SEGS B PST ARx R STK (spZ regs) [] ly S Hp W mem md [] ly S Hp W' mem' md' 0 /\
aregs_preserved regs regs' /\ Pa0 (getr regs' 10) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W') mem' a) /\
(forall j, 0 <= j < 4 -> aview SEGS (w_H W') mem' (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)).
(* W_contract_x.v:128 csd_spec_x at R *)
Definition csd_spec_xR (pc : Z) : Prop :=
forall W ly S Hp regs mem md ch n,
afn_pre_x SEGS B ARx CSD_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 n -> 0 <= n < 2 ^ 64 ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_nout) 8 n ->
SRrG SEGS R W (cfg_at SEGS pc regs mem md) (aleaf_post_xR CSD_STK regs ly S Hp W mem md (fun a => a = w64 n)).
End cR.

Section cRi.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Lemma aleaf_post_x_wle : aleaf_post_x B PST ARx = aleaf_post_xR B PST ARx (@wle SEGS).
Proof. reflexivity. Qed.
Lemma csd_spec_x_wle : csd_spec_x B PST ARx = csd_spec_xR B PST ARx (@wle SEGS).
Proof. reflexivity. Qed.
Lemma csd_spec_x_of_xR : forall pc, csd_spec_xR B PST ARx (@wle SEGS) pc -> csd_spec_x B PST ARx pc.
Proof. intros pc H. exact H. Qed.
Lemma aleaf_post_xR_of_x : forall STK regs ly S Hp W mem md Pa0 W' c',
  aleaf_post_x B PST ARx STK regs ly S Hp W mem md Pa0 W' c' ->
  aleaf_post_xR B PST ARx R STK regs ly S Hp W mem md Pa0 W' c'.
Proof.
intros STK regs ly S Hp W mem md Pa0 W' c' (regs' & mem' & md' & Hc & HJ & REST).
exists regs', mem', md'. split; [exact Hc|]. split; [|exact REST].
rewrite ajournal_x_wle in HJ. eapply ajournal_xR_mono; [exact WLE_R | exact HJ].
Qed.
Lemma csd_spec_xR_of_x : forall pc, csd_spec_x B PST ARx pc -> csd_spec_xR B PST ARx R pc.
Proof.
intros pc H. unfold csd_spec_xR. intros.
eapply SRrG_mono; [eapply SRr_SRrG; [exact WLE_R | eapply H; eassumption] |].
intros W' c' _ HP. eapply aleaf_post_xR_of_x. exact HP.
Qed.
End cRi.
