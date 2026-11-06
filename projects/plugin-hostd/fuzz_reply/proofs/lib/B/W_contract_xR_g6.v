(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_contract_x.v, with its module paths and numbers changed; 180 of its 421 lines of code are new or changed and 1771 lines of the source are left out. *)
(* Contract texts of lib/B/W_contract_x.v at a world relation R: gesture_model (gm_post_x :1079, gm_spec_x :1096,
   gm_spec_g_x :1128), check_shape_ends (cshe_post_x :1205, cshe_spec_x :1230) and check_no_loss (cnl_post_x :1311,
   cnl_spec_x :1338).  One owner per name: the other R contract texts live in their own files (W_contract_xR.v,
   W_send_line_xR.v and others), none of which this file changes; this file has the same form as W_contract_xR.v:
   R is a Section variable right after ARx, with its laws R_refl, R_trans, WLE_R (the definitions use none of them), and
   the SAME R is used in the post journal (W_journal_x.ajournal_gx_xR) and in the step relation (YA0nH.SRrG SEGS R).
   The instance for the re-hiding allocator calls is R := wle' SEGS RZ_cf (YA0nH.wle', YGcfRehidePost.RZ_cf), chosen
   at the use site.
   Against the strict texts only these change: the name, `ajournal_gx_x SEGS B PST ARx` -> `ajournal_gx_xR SEGS B PST
   ARx R`, `SRr SEGS` -> `SRrG SEGS R`, the post name X_post_x -> X_post_xR, and in gm_spec_g_x `gm_spec_x B PST ARx`
   -> `gm_spec_xR B PST ARx R`.  The comments inside the strict texts are left out.
   Instances (X = each text): at R := wle each R text IS its strict text (X_x_wle, by conversion); so the R text at
   wle gives the strict one (X_x_of_xR), and a strict text gives the R text at every R that contains wle (X_xR_of_x,
   from WLE_R; the post journal by W_journal_x.ajournal_gx_xR_mono).  The satisfiability lemmas at the real image are
   in the W_<walk>_xR_sat.v files beside the walks (W_gesture_model_xR_sat.v, W_gesture_model_g_xR_sat.v, W_check_shape_ends_xR_sat.v,
   W_check_no_loss_xR_sat.v).  This file Requires
   statement-side files only (W_contract_x.v's import block). *)
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

(* gesture_model: W_contract_x.v Section w4 / w4g at R *)
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
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable G : list (Z * Z).
(* W_contract_x.v:1079 gm_post_x at R *)
Definition gm_post_xR (regs : bvmap 5 word) ly S (Hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
(HA : Z) (H : hlist) (ln : list byte) (kr : nat) : world SEGS -> config -> Prop :=
fun W' c' => exists ly' S' Hp' regs' mem' md' kk (H' : hlist),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
ajournal_gx_xR SEGS B PST ARx R G 0 [] GM_STK (spZ regs) (blk_FP (list_blks H)) ly S Hp W mem md [] ly' S' Hp' W' mem' md' kk /\
aregs_preserved regs regs' /\
apres_kept B W mem W' mem' /\
(forall j, 0 <= j < 4 -> aview SEGS (w_H W') mem' (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)) /\
alist_at B ly' S' W' mem' (HA + 80) H' true /\ NoDup (texts H') /\ texts H' = RelayModel.upd (texts H) (bzs ln) /\
hl_cap H' = (if hl_n H <? hl_n H' then grow_cap (hl_n H) (hl_cap H) else hl_cap H) /\
(forall rest, Permutation (ablocks B ly S) (list_blks H ++ rest) -> Permutation (ablocks B ly' S') (list_blks H' ++ rest)) /\
frames S' = frames S /\
mo_le MT S S' (gm_cost MT H ln) /\ rp_RM RP S' kr.
(* W_contract_x.v:1096 gm_spec_x at R *)
Definition gm_spec_xR (pc : Z) : Prop :=
forall W ly S Hp regs mem md ch HA LINE (ln : list byte) H q k,
afn_pre_x SEGS B ARx GM_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 HA -> getr regs 11 = w64 LINE -> getr regs 12 = w64 (Z.of_nat (length ln)) ->
alist_at B ly S W mem (HA + 80) H true -> NoDup (texts H) ->
(forall a, HA + 80 <= a < HA + 96 -> inG G a) -> azs B (HA + 80) 16 ->
(HA + 80) mod 8 = 0 ->
garr8 SEGS (arm W mem) LINE (bzs ln) -> ~ In (Z_to_bv 8 0) ln -> Z.of_nat (length ln) <= APARTIAL ->
In (q, k) (ablocks B ly S) -> ~ In (q, k) (list_blks H) -> q <= LINE -> LINE + Z.of_nat (length ln) <= q + req_size k ->
garr8 SEGS (arm W mem) (VAL A_lit_gesture) RelayModel.K_GESTURE ->
garr8 SEGS (arm W mem) (VAL A_lit_begin) RelayModel.W_BEGIN ->
garr8 SEGS (arm W mem) (VAL A_lit_end) RelayModel.W_END -> rom_view SEGS W mem ->
(lp_grow H = true -> lp_vbytes H < MMAX) -> AREC * hl_cap H < 2 ^ 32 ->
blocks_bytes S + (if lp_grow H then lp_vbytes H else 0) + (Z.of_nat (length ln) + 1) <= LIVE_MAX ->
mo_ok MT S (gm_cost MT H ln) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (gm_cost MT_rk H ln) + kr) ->
cnt_ok_pk RP (gm_pk H) (ablocks B ly S) ->
SRrG SEGS R W (cfg_at SEGS pc regs mem md) (gm_post_xR regs ly S Hp W mem md HA H ln kr).
End w4R.

Section w4gR.
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
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
(* W_contract_x.v:1128 gm_spec_g_x at R *)
Definition gm_spec_g_xR (pc : Z) : Prop :=
forall G, gx_ok SEGS B G -> gx_rt B G -> rom_out SEGS B G -> gm_spec_xR B PST ARx R MT RP MMAX G pc.
End w4gR.

(* check_shape_ends: W_contract_x.v Section w3e at R *)
Section w3eR.
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
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable G : list (Z * Z).
(* W_contract_x.v:1205 cshe_post_x at R *)
Definition cshe_post_xR (regs : bvmap 5 word) ly S (Hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
(XO AT HA : Z) (h : hsrc) (P : list byte) (A0 gone : Z) (ob : list byte) (kr : nat) : world SEGS -> config -> Prop :=
fun W' c' => exists ly' S' Hp' regs' mem' md' kk (H' : hlist) (ds : list (Z * list byte)) (c : Z),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
ajournal_gx_xR SEGS B PST ARx R G XO [(AT, AT + 8)] CSHE_STK (spZ regs) (blk_FP (list_blks (hs_held h)))
  ly S Hp W mem md [] ly' S' Hp' W' mem' md' kk /\
aregs_preserved regs regs' /\
(forall j, 0 <= j < 4 -> aview SEGS (w_H W') mem' (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)) /\
asrc_at B ly' S' W' mem' HA (CheckRep.set_held h H') /\
hl_v H' = hl_v (hs_held h) /\ hl_cap H' = hl_cap (hs_held h) /\
NoDup (CheckRep.texts H') /\
((gone <> 0 /\
  hl_recs H' = filter (fun r => negb (CheckRep.prefixb P (snd r))) (hl_recs (hs_held h)) /\
  ds = filter (fun r => CheckRep.prefixb P (snd r)) (hl_recs (hs_held h)) /\ c = 0) \/
 (gone = 0 /\
  CheckRep.ends_run P (hl_recs (hs_held h)) (skipn (Z.to_nat A0) ob)
    (CheckRep.want_of P (hl_recs (hs_held h))) = Some (hl_recs H', ds, c))) /\
0 <= c /\
val_mem SEGS (mrestrict (w_H W') mem') AT 8 (A0 + c) /\
val_mem SEGS (mrestrict (w_H W') mem') (VAL A_g_gone) 1 gone /\
(forall rest, Permutation (ablocks B ly S) (cshe_ds_blks ds ++ rest) -> Permutation (ablocks B ly' S') rest) /\
frames S' = frames S /\
mo_le MT S S' (cshe_cost MT (hs_held h)) /\ rp_RM RP S' kr.
(* W_contract_x.v:1230 cshe_spec_x at R *)
Definition cshe_spec_xR (pc : Z) : Prop :=
forall W ly S Hp regs mem md ch XO AT HA (j : nat) PF h P A0 gone O OUT ob,
let H := hs_held h in
let PLEN := Z.of_nat (length P) in
afn_pre_x SEGS B ARx CSHE_STK ly S Hp W regs mem md ch ->
0 <= XO -> XO mod 16 = 0 -> spZ regs + XO <= ly_top ly ->
(forall a, spZ regs <= a < spZ regs + XO -> apresent (w_H W) mem a) ->
getr regs 10 = w64 HA -> getr regs 11 = w64 PF -> getr regs 12 = w64 AT ->
asrc_at B ly S W mem HA h ->
HA mod 8 = 0 -> 4096 <= HA -> HA + ASRC <= kLowMemEnd ->
(forall a, HA + 64 <= a < HA + 96 -> inG G a) -> azs B (HA + 64) 32 ->
HA = VAL (A_OBJ 19) + ASRC * Z.of_nat j -> (j < 4)%nat ->
(forall a, HA <= a < HA + ASRC -> ~ (spZ regs - CSHE_STK <= a < spZ regs + XO)) ->
(forall a, HA <= a < HA + ASRC -> cshe_home B ly S a) ->
NoDup (CheckRep.texts H) ->
hl_n H < 2 ^ 26 ->
(forall a, hl_v H <= a < hl_v H + AREC * hl_cap H -> ~ (spZ regs - CSHE_STK <= a < spZ regs + XO)) ->
(forall r, In r (hl_recs H) -> forall a, fst r <= a < fst r + Z.of_nat (length (snd r)) + 1 ->
  ~ (spZ regs - CSHE_STK <= a < spZ regs + XO)) ->
AT mod 8 = 0 -> spZ regs <= AT -> AT + 8 <= spZ regs + XO ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF AT 8 ->
val_mem SEGS (mrestrict (w_H W) mem) AT 8 A0 ->
~ In (Z_to_bv 8 0) P -> PLEN + 1 < 2 ^ 32 -> 0 < PF -> PF + PLEN + 8 <= 2 ^ 63 ->
(forall i, 0 <= i < PLEN -> aview SEGS (w_H W) mem (PF + i) = Some (bv_unsigned (nth (Z.to_nat i) P (Z_to_bv 8 0)))) ->
aview SEGS (w_H W) mem (PF + PLEN) = Some 0 ->
(forall a, PF <= a < PF + PLEN + 8 -> aview SEGS (w_H W) mem a <> None /\
  ~ (spZ regs - CSHE_STK <= a < spZ regs + XO)) ->
amem_range PF (PLEN + 1) -> amem_range PF 8 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF (PLEN + 1) ->
shadow_hull_vis (aview SEGS (w_H W) mem) PF (PLEN + 1) ->
((forall a, PF <= a < PF + PLEN + 8 -> in_rom SEGS a) /\ ashp_x ARx PF (PLEN + 1) \/
 exists cid pos, In (cid, pos) (frames S) /\ forall a, PF <= a < PF + PLEN + 8 -> in_zr a (frame_rng ly (cid, pos))) ->
garr8 SEGS (arm W mem) (VAL A_lit_end5) (bzs END5) -> rom_view SEGS W mem ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_gone) 1 gone -> 0 <= gone < 256 ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_nout) 8 O ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_out) 8 OUT ->
ob_at W mem OUT ob -> Z.of_nat (length ob) = O -> O <= 2 ^ 40 -> (0 < O -> O < 2 ^ 32) -> amem_range OUT (O + 8) ->
(ob = [] \/ exists CO, O <= CO /\ In (OUT, CO) (ablocks B ly S) /\ ~ In OUT (hs_blocks h)) ->
0 <= A0 <= O ->
(gone = 0 -> CheckRep.ends_run P (hl_recs H) (skipn (Z.to_nat A0) ob) (CheckRep.want_of P (hl_recs H)) <> None) ->
mo_ok MT S (cshe_cost MT H) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (cshe_cost MT_rk H) + kr) ->
cnt_ok_pk RP cshe_pk (ablocks B ly S) ->
SRrG SEGS R W (cfg_at SEGS pc regs mem md) (cshe_post_xR regs ly S Hp W mem md XO AT HA h P A0 gone ob kr).
End w3eR.

(* check_no_loss: W_contract_x.v Section w3n at R *)
Section w3nR.
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
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable G : list (Z * Z).
Variable MMAX : Z.
(* W_contract_x.v:1311 cnl_post_x at R *)
Definition cnl_post_xR (regs : bvmap 5 word) ly S (Hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
(XO HA AT : Z) (h : hsrc) (E H : hlist) (gone A0 NO OUT : Z) (ob : list byte) (kr : nat) : world SEGS -> config -> Prop :=
fun W' c' => exists ly' S' Hp' regs' mem' md' kk (E' H' : hlist),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
ajournal_gx_xR SEGS B PST ARx R G XO [(AT, AT + 8)] CNL_STK (spZ regs) (blk_FP (list_blks E ++ list_blks H))
  ly S Hp W mem md [] ly' S' Hp' W' mem' md' kk /\
aregs_preserved regs regs' /\ apres_kept B W mem W' mem' /\
(forall j, 0 <= j < 4 -> aview SEGS (w_H W') mem' (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)) /\
asrc_at B ly' S' W' mem' HA (set_exp_held h E' H') /\
hl_recs E' = [] /\ hl_v E' = hl_v E /\ hl_cap E' = hl_cap E /\
NoDup (texts H') /\ texts H' = RelayModel.upds (texts H) (texts E) /\
hl_cap H' <= Z.max 8 (Z.max (hl_cap H) (2 * (hl_n H + Z.of_nat (count_begin (texts E))))) /\
val_mem SEGS (arm W' mem') AT 8 (if gone =? 0 then A0 + Z.of_nat (length (bstream E)) else A0) /\
val_mem SEGS (arm W' mem') (VAL A_g_gone) 1 gone /\
val_mem SEGS (arm W' mem') (VAL A_g_nout) 8 NO /\ val_mem SEGS (arm W' mem') (VAL A_g_out) 8 OUT /\
ob_at W' mem' OUT ob /\
(forall rest, Permutation (ablocks B ly S) (list_blks E ++ list_blks H ++ rest) ->
 Permutation (ablocks B ly' S') (list_blks E' ++ list_blks H' ++ rest)) /\
frames S' = frames S /\
mo_le MT S S' (cnl_cost MT E H) /\ rp_RM RP S' kr /\
hl_cap H <= hl_cap H' /\
hl_cap H' = cnl_cap (texts H) (hl_cap H) (hl_recs E).
(* W_contract_x.v:1338 cnl_spec_x at R *)
Definition cnl_spec_xR (pc : Z) : Prop :=
forall W ly S Hp regs mem md ch XO HA (j : nat) AT (h : hsrc) gone A0 NO OUT (ob : list byte),
afn_pre_x SEGS B ARx CNL_STK ly S Hp W regs mem md ch ->
0 <= XO -> XO mod 16 = 0 -> spZ regs + XO <= ly_top ly ->
(forall a, spZ regs <= a < spZ regs + XO -> apresent (w_H W) mem a) ->
getr regs 10 = w64 HA -> getr regs 11 = w64 AT ->
HA = VAL A_g_s + ASRC * Z.of_nat j -> (j < 4)%nat ->
AT mod 8 = 0 -> spZ regs <= AT -> AT + 8 <= spZ regs + XO ->
asrc_at B ly S W mem HA h ->
(forall a, HA + 64 <= a < HA + 96 -> inG G a) -> azs B (HA + 64) 32 ->
NoDup (texts (hs_held h)) ->
hl_n (hs_expected h) < 2 ^ 26 ->
hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h))) < 2 ^ 22 ->
val_mem SEGS (arm W mem) AT 8 A0 -> 0 <= A0 <= NO ->
val_mem SEGS (arm W mem) (VAL A_g_gone) 1 gone -> 0 <= gone < 256 ->
val_mem SEGS (arm W mem) (VAL A_g_nout) 8 NO -> val_mem SEGS (arm W mem) (VAL A_g_out) 8 OUT ->
ob_at W mem OUT ob -> Z.of_nat (length ob) = NO -> NO <= 2 ^ 40 ->
(0 < NO -> NO < 2 ^ 32) -> amem_range OUT (NO + 8) ->
(ob = [] \/ exists CO, NO <= CO /\ In (OUT, CO) (ablocks B ly S) /\ ~ In OUT (hs_blocks h)) ->
(gone = 0 -> exists rest, skipn (Z.to_nat A0) ob = bstream (hs_expected h) ++ rest) ->
rom_view SEGS W mem ->
garr8 SEGS (arm W mem) (VAL A_lit_gesture) RelayModel.K_GESTURE ->
garr8 SEGS (arm W mem) (VAL A_lit_begin) RelayModel.W_BEGIN ->
garr8 SEGS (arm W mem) (VAL A_lit_end) RelayModel.W_END ->
cnl_room MMAX (blocks_bytes S) (texts (hs_held h)) (hl_cap (hs_held h)) (hl_recs (hs_expected h)) ->
mo_ok MT S (cnl_cost MT (hs_expected h) (hs_held h)) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (cnl_cost MT_rk (hs_expected h) (hs_held h)) + kr) ->
cnt_ok_pk RP (cnl_pk (hs_expected h) (hs_held h)) (ablocks B ly S) ->
AREC * capb (hs_held h) (hs_expected h) < 2 ^ 32 ->
(forall a, spZ regs <= a < ly_top ly -> aview SEGS (w_H W) mem a <> None) ->
SRrG SEGS R W (cfg_at SEGS pc regs mem md)
  (cnl_post_xR regs ly S Hp W mem md XO HA AT h (hs_expected h) (hs_held h) gone A0 NO OUT ob kr).
End w3nR.

(* the instances: (a) X_x_wle, (b) X_x_of_xR, (c) X_xR_of_x (from WLE_R; the post journal by
   W_journal_x.ajournal_gx_xR_mono) *)
Section w4Ri.
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
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable G : list (Z * Z).
Lemma gm_post_x_wle : gm_post_x B PST ARx MT RP G = gm_post_xR B PST ARx (@wle SEGS) MT RP G.
Proof. reflexivity. Qed.
Lemma gm_post_x_of_xR : forall regs ly S Hp W mem md HA H ln kr W' c',
  gm_post_xR B PST ARx (@wle SEGS) MT RP G regs ly S Hp W mem md HA H ln kr W' c' ->
  gm_post_x B PST ARx MT RP G regs ly S Hp W mem md HA H ln kr W' c'.
Proof. intros regs ly S Hp W mem md HA H ln kr W' c' HQ. exact HQ. Qed.
Lemma gm_post_xR_of_x : forall regs ly S Hp W mem md HA H ln kr W' c',
  gm_post_x B PST ARx MT RP G regs ly S Hp W mem md HA H ln kr W' c' ->
  gm_post_xR B PST ARx R MT RP G regs ly S Hp W mem md HA H ln kr W' c'.
Proof.
intros regs ly S Hp W mem md HA H ln kr W' c'
  (ly' & S' & Hp' & regs' & mem' & md' & kk & H' & Hc & HJ & REST).
exists ly', S', Hp', regs', mem', md', kk, H'. split; [exact Hc|]. split; [|exact REST].
eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ].
Qed.
Lemma gm_spec_x_wle : gm_spec_x B PST ARx MT RP MMAX G = gm_spec_xR B PST ARx (@wle SEGS) MT RP MMAX G.
Proof. reflexivity. Qed.
Lemma gm_spec_x_of_xR : forall pc, gm_spec_xR B PST ARx (@wle SEGS) MT RP MMAX G pc -> gm_spec_x B PST ARx MT RP MMAX G pc.
Proof. intros pc H. exact H. Qed.
Lemma gm_spec_xR_of_x : forall pc, gm_spec_x B PST ARx MT RP MMAX G pc -> gm_spec_xR B PST ARx R MT RP MMAX G pc.
Proof.
intros pc HS. unfold gm_spec_xR. cbv zeta. intros.
eapply SRrG_mono; [eapply SRr_SRrG; [exact WLE_R | eapply HS; eassumption] |].
intros W' c' _ HP. eapply gm_post_xR_of_x. exact HP.
Qed.
End w4Ri.

Section w4gRi.
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
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Lemma gm_spec_g_x_wle : gm_spec_g_x B PST ARx MT RP MMAX = gm_spec_g_xR B PST ARx (@wle SEGS) MT RP MMAX.
Proof. reflexivity. Qed.
Lemma gm_spec_g_x_of_xR : forall pc, gm_spec_g_xR B PST ARx (@wle SEGS) MT RP MMAX pc -> gm_spec_g_x B PST ARx MT RP MMAX pc.
Proof. intros pc H. exact H. Qed.
Lemma gm_spec_g_xR_of_x : forall pc, gm_spec_g_x B PST ARx MT RP MMAX pc -> gm_spec_g_xR B PST ARx R MT RP MMAX pc.
Proof.
intros pc HS G0 H1 H2 H3. apply gm_spec_xR_of_x; [exact WLE_R | exact (HS G0 H1 H2 H3)].
Qed.
End w4gRi.

Section w3eRi.
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
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable G : list (Z * Z).
Lemma cshe_post_x_wle : cshe_post_x B PST ARx MT RP G = cshe_post_xR B PST ARx (@wle SEGS) MT RP G.
Proof. reflexivity. Qed.
Lemma cshe_post_x_of_xR : forall regs ly S Hp W mem md XO AT HA h P A0 gone ob kr W' c',
  cshe_post_xR B PST ARx (@wle SEGS) MT RP G regs ly S Hp W mem md XO AT HA h P A0 gone ob kr W' c' ->
  cshe_post_x B PST ARx MT RP G regs ly S Hp W mem md XO AT HA h P A0 gone ob kr W' c'.
Proof. intros regs ly S Hp W mem md XO AT HA h P A0 gone ob kr W' c' HQ. exact HQ. Qed.
Lemma cshe_post_xR_of_x : forall regs ly S Hp W mem md XO AT HA h P A0 gone ob kr W' c',
  cshe_post_x B PST ARx MT RP G regs ly S Hp W mem md XO AT HA h P A0 gone ob kr W' c' ->
  cshe_post_xR B PST ARx R MT RP G regs ly S Hp W mem md XO AT HA h P A0 gone ob kr W' c'.
Proof.
intros regs ly S Hp W mem md XO AT HA h P A0 gone ob kr W' c'
  (ly' & S' & Hp' & regs' & mem' & md' & kk & H' & ds & c & Hc & HJ & REST).
exists ly', S', Hp', regs', mem', md', kk, H', ds, c. split; [exact Hc|]. split; [|exact REST].
eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ].
Qed.
Lemma cshe_spec_x_wle : cshe_spec_x B PST ARx MT RP G = cshe_spec_xR B PST ARx (@wle SEGS) MT RP G.
Proof. reflexivity. Qed.
Lemma cshe_spec_x_of_xR : forall pc, cshe_spec_xR B PST ARx (@wle SEGS) MT RP G pc -> cshe_spec_x B PST ARx MT RP G pc.
Proof. intros pc H. exact H. Qed.
Lemma cshe_spec_xR_of_x : forall pc, cshe_spec_x B PST ARx MT RP G pc -> cshe_spec_xR B PST ARx R MT RP G pc.
Proof.
intros pc HS. unfold cshe_spec_xR. cbv zeta. intros.
eapply SRrG_mono; [eapply SRr_SRrG; [exact WLE_R | eapply HS; eassumption] |].
intros W' c' _ HP. eapply cshe_post_xR_of_x. exact HP.
Qed.
End w3eRi.

Section w3nRi.
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
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable G : list (Z * Z).
Variable MMAX : Z.
Lemma cnl_post_x_wle : cnl_post_x B PST ARx MT RP G = cnl_post_xR B PST ARx (@wle SEGS) MT RP G.
Proof. reflexivity. Qed.
Lemma cnl_post_x_of_xR : forall regs ly S Hp W mem md XO HA AT h E H gone A0 NO OUT ob kr W' c',
  cnl_post_xR B PST ARx (@wle SEGS) MT RP G regs ly S Hp W mem md XO HA AT h E H gone A0 NO OUT ob kr W' c' ->
  cnl_post_x B PST ARx MT RP G regs ly S Hp W mem md XO HA AT h E H gone A0 NO OUT ob kr W' c'.
Proof. intros regs ly S Hp W mem md XO HA AT h E H gone A0 NO OUT ob kr W' c' HQ. exact HQ. Qed.
Lemma cnl_post_xR_of_x : forall regs ly S Hp W mem md XO HA AT h E H gone A0 NO OUT ob kr W' c',
  cnl_post_x B PST ARx MT RP G regs ly S Hp W mem md XO HA AT h E H gone A0 NO OUT ob kr W' c' ->
  cnl_post_xR B PST ARx R MT RP G regs ly S Hp W mem md XO HA AT h E H gone A0 NO OUT ob kr W' c'.
Proof.
intros regs ly S Hp W mem md XO HA AT h E H gone A0 NO OUT ob kr W' c'
  (ly' & S' & Hp' & regs' & mem' & md' & kk & E' & H' & Hc & HJ & REST).
exists ly', S', Hp', regs', mem', md', kk, E', H'. split; [exact Hc|]. split; [|exact REST].
eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ].
Qed.
Lemma cnl_spec_x_wle : cnl_spec_x B PST ARx MT RP G MMAX = cnl_spec_xR B PST ARx (@wle SEGS) MT RP G MMAX.
Proof. reflexivity. Qed.
Lemma cnl_spec_x_of_xR : forall pc, cnl_spec_xR B PST ARx (@wle SEGS) MT RP G MMAX pc -> cnl_spec_x B PST ARx MT RP G MMAX pc.
Proof. intros pc H. exact H. Qed.
Lemma cnl_spec_xR_of_x : forall pc, cnl_spec_x B PST ARx MT RP G MMAX pc -> cnl_spec_xR B PST ARx R MT RP G MMAX pc.
Proof.
intros pc HS. unfold cnl_spec_xR. cbv zeta. intros.
eapply SRrG_mono; [eapply SRr_SRrG; [exact WLE_R | eapply HS; eassumption] |].
intros W' c' _ HP. eapply cnl_post_xR_of_x. exact HP.
Qed.
End w3nRi.

