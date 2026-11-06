(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx-GENERIC twin of lib/A/W_send_line_grow_cx.v, the growth half of send_line's data round
   from 0x82824 to the join (a Theorem Labs lane's step 1 of route (b), 2026-10-29), from its text at a working branch
   a78a220dc8e (sha256 1766613f015b; internal record, W7's c98267ecbde; carried here by path). W_send_line_grow_cx.v is NOT edited.
   - The Section header is W_send_line_cx_x.v's (W_send_line_cx.v's over ARx, LAWS, PST).
   - SLN_x and sl_grow_stmt_x are the twins of SLN and sl_grow_stmt: the journal W_journal_x.ajournal_gx_x (the entry's
     Hp after S, the state's HpN an existential after SN), sl_line_ok_x, the continuation over
     W_send_line_datab_cx_x.v's SLM_x at the entry's Hp, the post W_contract_x.sl_post_x at the entry's Hp.
   - The AR-free name A_sl_n is CITED.
   - BRIDGES as W_send_line_cx_x.v's: Section br (ARi, iff, every Hp) and Section br0 (ARi0: SLN_x_AR0 / SLN_x_of_AR0,
     sl_grow_stmt_x_AR0 / sl_grow_stmt_x_of_AR0).
   No statement difference is forced by ARx.
   THE ROOM FORM (a Theorem Labs lane, row A-SL_x, 2026-10-30), as W_send_line_cx_x.v's: `Variable RP : roomp` after MT, AREALLOC
   (caller-context form, CTX_R / HCTX_slr) at RP, SLN_x with C3's peak (W_send_line_grow_cx.v SLN at 76be6190eff) and after frames the room budget of the
   rounds from this one on (sl_cost_run at MT_rk, on top of kr) and the entry's cnt_ok_pk RP sl_pk; SLN_x and
   sl_grow_stmt_x take the post's kr after n. The bridges are at RP := RP_AR. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require send_line_c send_line_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_rebase W_frame W_sites W_contract W_send_line_cx W_send_line_datab_cx
W_send_line_grow_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_journal_x W_sites_x W_contract_x W_send_line_cx_x W_send_line_datab_cx_x.
(* route R: the send_line contract texts at a world relation R (a Theorem Labs lane's W_send_line_xR.v) and SRrG *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_send_line_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Abbreviation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Abbreviation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* a Theorem Labs lane's HP0 ruling: the generic relation holds at the empty ghost list only *)
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
(* W_send_line_cx_x.v's header (W_send_line_grow_cx.v's is W_send_line_cx.v's) *)
Hypothesis HG : gx_ok SEGS B (G_SL B RG).
Hypothesis HGR : forall a, inG (G_SL B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_SL B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes_x B ARx (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
(* The realloc site rule in its caller-context form (W_journal_x.v Section hc), as the top's ARE_x states it
   (CTX_AREALLOC, ACk0.v:45, holds [0x82844]); send_line hands the rule a cut chain (ch = []), so the trace is the
   return address alone (W7's ccd62d4c6f6 form). *)
Variable CTX_R : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis HCTX_slr : In [BASE + AF_fr_send_line + 0x110] CTX_R.   (* realloc returns to 0x82844 *)
Hypothesis HERRNO : as_errno B = as_tp B - 164.
(* errno's 4 bytes in an 8-aligned zero-shadow range (W_contract.azs; W_drain_cx_x.v:189's form): the loop's errno
   stores need range_addressable of errno at an ARx state (W_contract_x.azs_range_addressable_x) *)
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV10 : VAL (A_OBJ 10) = rg_client_broken RG.
Hypothesis HV11 : VAL (A_OBJ 11) = rg_send_eintr RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HV13 : VAL (A_OBJ 13) = rg_nout RG.
Hypothesis HV14 : VAL (A_OBJ 14) = rg_capout RG.
Hypothesis HV15 : VAL (A_OBJ 15) = rg_out RG.
Hypothesis HH17 : VAL (A_HI 17) + 92 = rg_client_broken RG.
Hypothesis HH19 : VAL (A_HI 19) + 248 = rg_send_eintr RG.
Hypothesis HH21 : VAL (A_HI 21) + 140 = rg_send_max RG.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Hypothesis HH22 : VAL (A_HI 22) + 260 = rg_nout RG.
Hypothesis HH23 : VAL (A_HI 23) + 864 = rg_capout RG.
Hypothesis HH24 : VAL (A_HI 24) + 892 = rg_out RG.
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4)].

(* W_send_line_grow_cx.v:98 SLN: the state at 0x82824 of a round that has to grow g_out; kr is the post's *)
Definition SLN_x (regsE : bvmap 5 word) ly S (Hp : list Z) W mem md (c : ctl) (O : list byte) (mx no cap out line : Z)
(Bl : list byte) (WN : world SEGS) (regsN : bvmap 5 word) (memN : word -> option byte) (mdN : Model) (sent n : Z)
(kr : nat) : Prop :=
let len := Z.of_nat (length Bl) in
let sp0 := spZ regsE in
exists lyN SN HpN kN evL capN outN spent rest,
ajournal_gx_x SEGS B PST ARx (G_SL B RG) 0 [] SL_STK sp0 (ablocks_fp (aout_blks cap out)) ly S Hp W mem md []
  lyN SN HpN WN memN mdN kN /\
spZ regsN = sp0 - SL_FRAME /\ getr regsN 3 = getr regsE 3 /\ getr regsN 4 = getr regsE 4 /\
getr regsE 3 = w64 (as_gp B) /\ getr regsE 4 = w64 (as_tp B) /\
YK0s.ret_ok (getr regsE 1) /\ sl_regsM regsN len line sent n /\
val_mem SEGS (mrestrict (w_H WN) memN) (sp0 - SL_FRAME + 8) 8 (VAL (A_HI 17)) /\
val_mem SEGS (mrestrict (w_H WN) memN) (sp0 - SL_FRAME + 16) 8 (VAL (A_HI 21)) /\
sl_saved WN memN (sp0 - SL_FRAME) regsE /\
ct_cl c = 3 /\ ct_br c = 0 /\ ct_dd c = 0 /\ 0 <= sent < len /\ n = sl_n mx (len - sent) /\
evL = (if ct_ei c =? 1 then send_line_c.EINTR_V else ct_ev c) /\
aout_at B RG lyN SN WN memN (CTL 3 0 0 0 evL) (O ++ firstn (Z.to_nat sent) Bl) mx (no + sent) capN outN /\
capN < no + sent + n /\
garr8 SEGS (arm WN memN) line (bzs Bl) /\ 0 <= line /\ line + len < 2 ^ 63 /\ rom_view SEGS WN memN /\
sl_line_ok_x B ARx lyN SN outN line len /\ (forall a, line <= a < line + len -> ~ inG (G_SL B RG) a) /\
sl_cap c mx no cap len = send_line_b_c.send_line_cap true mx (no + sent) capN (len - sent) /\
sl_max_run (Z.to_nat (len - sent)) mx (no + sent) capN (len - sent) < MMAX /\
blocks_bytes SN + tr_peak (send_line_b_c.send_line_tr true mx (no + sent) capN (len - sent) 0 RelayRunF.adr0) <= LIVE_MAX /\
apres_kept B W mem WN memN /\
mo_ok MT S (sl_cost MT c mx no cap len) /\ mo_le MT S SN spent /\
spent + sl_cost_run MT (Z.to_nat (len - sent)) mx (no + sent) capN (len - sent) <= sl_cost MT c mx no cap len /\
Permutation (ablocks B ly S) (aout_blks cap out ++ rest) /\ Permutation (ablocks B lyN SN) (aout_blks capN outN ++ rest) /\
frames SN = frames S /\
rp_RM RP SN (Z.to_nat (sl_cost_run MT_rk (Z.to_nat (len - sent)) mx (no + sent) capN (len - sent)) + kr) /\
cnt_ok_pk RP sl_pk (ablocks B ly S).
(* W_send_line_grow_cx.v:125 sl_grow_stmt *)
Definition sl_grow_stmt_x : Prop :=
forall regsE ly S Hp W mem md c O mx no cap out line Bl WN regsN memN mdN sent n kr,
SLN_x regsE ly S Hp W mem md c O mx no cap out line Bl WN regsN memN mdN sent n kr ->
(forall WM regsM memM mdM,
  SLM_x B PST ARx MT RP MMAX RG regsE ly S Hp W mem md c O mx no cap out line Bl WM regsM memM mdM sent n kr ->
  SRr SEGS WM (mkCfg (mkst regsM (Z_to_bv 64 (BASE + A_sl_join)) memM (seg_rom SEGS)) mdM)
  (sl_post_x B PST ARx MT RP RG regsE ly S Hp W mem md c O mx no cap out Bl kr)) ->
SRr SEGS WN (mkCfg (mkst regsN (Z_to_bv 64 (BASE + A_sl_n)) memN (seg_rom SEGS)) mdN)
(sl_post_x B PST ARx MT RP RG regsE ly S Hp W mem md c O mx no cap out Bl kr).
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): this Section's texts at a world relation R.  Each <name>_xR below is <name>_x
   with the journal ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, sl_post_x / sl_spec_x -> their R
   twins (W_send_line_xR.v, R right after ARx), every carrier or walk it names -> its R twin, and the walk on
   W_journal_x.v's G chain (RUNG / RUNTOG, W_kit_x.v's paj_run_tok_xR / paj_run_to_tok_xR, W_kit.v's paj_branch_xR
   as BRR, SRrG_bind / SRrG_mono / SRrG_ret); every other token is the strict text's.  At R := wle each is its strict twin by conversion. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Variable HA : alayout -> astate -> bvmap 5 word -> list (Z * Z * Z) -> Z -> Z -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis HA_call : forall lyc Sc regsT ch p n, mo_ok MT Sc (mo_malloc MT n + mo_free MT) -> HA lyc Sc regsT ch p n.
Hypothesis AREALLOC_R : arealloc_cf_rule_c_xR SEGS B PST ARx MT MMAX RP RO HA CTX_R R (SIGMA WS_realloc).
(* W_send_line_grow_cx_x.v:110 SLN_x at R *)
Definition SLN_xR (regsE : bvmap 5 word) ly S (Hp : list Z) W mem md (c : ctl) (O : list byte) (mx no cap out line : Z)
(Bl : list byte) (WN : world SEGS) (regsN : bvmap 5 word) (memN : word -> option byte) (mdN : Model) (sent n : Z)
(kr : nat) : Prop :=
let len := Z.of_nat (length Bl) in
let sp0 := spZ regsE in
exists lyN SN HpN kN evL capN outN spent rest,
ajournal_gx_xR SEGS B PST ARx R (G_SL B RG) 0 [] SL_STK sp0 (ablocks_fp (aout_blks cap out)) ly S Hp W mem md []
  lyN SN HpN WN memN mdN kN /\
spZ regsN = sp0 - SL_FRAME /\ getr regsN 3 = getr regsE 3 /\ getr regsN 4 = getr regsE 4 /\
getr regsE 3 = w64 (as_gp B) /\ getr regsE 4 = w64 (as_tp B) /\
YK0s.ret_ok (getr regsE 1) /\ sl_regsM regsN len line sent n /\
val_mem SEGS (mrestrict (w_H WN) memN) (sp0 - SL_FRAME + 8) 8 (VAL (A_HI 17)) /\
val_mem SEGS (mrestrict (w_H WN) memN) (sp0 - SL_FRAME + 16) 8 (VAL (A_HI 21)) /\
sl_saved WN memN (sp0 - SL_FRAME) regsE /\
ct_cl c = 3 /\ ct_br c = 0 /\ ct_dd c = 0 /\ 0 <= sent < len /\ n = sl_n mx (len - sent) /\
evL = (if ct_ei c =? 1 then send_line_c.EINTR_V else ct_ev c) /\
aout_at B RG lyN SN WN memN (CTL 3 0 0 0 evL) (O ++ firstn (Z.to_nat sent) Bl) mx (no + sent) capN outN /\
capN < no + sent + n /\
garr8 SEGS (arm WN memN) line (bzs Bl) /\ 0 <= line /\ line + len < 2 ^ 63 /\ rom_view SEGS WN memN /\
sl_line_ok_x B ARx lyN SN outN line len /\ (forall a, line <= a < line + len -> ~ inG (G_SL B RG) a) /\
sl_cap c mx no cap len = send_line_b_c.send_line_cap true mx (no + sent) capN (len - sent) /\
sl_max_run (Z.to_nat (len - sent)) mx (no + sent) capN (len - sent) < MMAX /\
blocks_bytes SN + tr_peak (send_line_b_c.send_line_tr true mx (no + sent) capN (len - sent) 0 RelayRunF.adr0) <= LIVE_MAX /\
apres_kept B W mem WN memN /\
mo_ok MT S (sl_cost MT c mx no cap len) /\ mo_le MT S SN spent /\
spent + sl_cost_run MT (Z.to_nat (len - sent)) mx (no + sent) capN (len - sent) <= sl_cost MT c mx no cap len /\
Permutation (ablocks B ly S) (aout_blks cap out ++ rest) /\ Permutation (ablocks B lyN SN) (aout_blks capN outN ++ rest) /\
frames SN = frames S /\
rp_RM RP SN (Z.to_nat (sl_cost_run MT_rk (Z.to_nat (len - sent)) mx (no + sent) capN (len - sent)) + kr) /\
cnt_ok_pk RP sl_pk (ablocks B ly S).
(* W_send_line_grow_cx_x.v:141 sl_grow_stmt_x at R *)
Definition sl_grow_stmt_xR : Prop :=
forall regsE ly S Hp W mem md c O mx no cap out line Bl WN regsN memN mdN sent n kr,
SLN_xR regsE ly S Hp W mem md c O mx no cap out line Bl WN regsN memN mdN sent n kr ->
(forall WM regsM memM mdM,
  SLM_xR B PST ARx MT RP MMAX RG R regsE ly S Hp W mem md c O mx no cap out line Bl WM regsM memM mdM sent n kr ->
  SRrG SEGS R WM (mkCfg (mkst regsM (Z_to_bv 64 (BASE + A_sl_join)) memM (seg_rom SEGS)) mdM)
  (sl_post_xR B PST ARx R MT RP RG regsE ly S Hp W mem md c O mx no cap out Bl kr)) ->
SRrG SEGS R WN (mkCfg (mkst regsN (Z_to_bv 64 (BASE + A_sl_n)) memN (seg_rom SEGS)) mdN)
(sl_post_xR B PST ARx R MT RP RG regsE ly S Hp W mem md c O mx no cap out Bl kr).
End wR.
(* at R := wle the R texts are the strict ones (conversion) *)
Lemma SLN_x_wle : SLN_x = SLN_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma sl_grow_stmt_x_wle : sl_grow_stmt_x = sl_grow_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
End c.
End b.
End a.

(* THE BRIDGES at ARx := W_journal_x.ARi (cgif's AR, Hp ignored) and PST := []. *)
Section br.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
#[local] Abbreviation ARI := (ARi SEGS B).
Lemma SLN_x_AR : forall regsE ly S Hp W mem md c O mx no cap out line Bl WN regsN memN mdN sent n kr,
SLN_x B [] ARI MT RP_AR MMAX RG regsE ly S Hp W mem md c O mx no cap out line Bl WN regsN memN mdN sent n kr <->
SLN B MT MMAX RG regsE ly S W mem md c O mx no cap out line Bl WN regsN memN mdN sent n.
Proof.
intros. unfold SLN_x, SLN. cbv zeta.
setoid_rewrite (@ajournal_gx_x_AR fx rc SK). setoid_rewrite sl_line_ok_x_AR.
split.
- intros (l & s & h & kN & evL & capN & outN & spent & rest & HH).
  exists l, s, kN, evL, capN, outN, spent, rest. sl_decomp. sl_rebuild.
- intros (l & s & kN & evL & capN & outN & spent & rest & HH).
  exists l, s, [], kN, evL, capN, outN, spent, rest. sl_decomp. sl_rebuild_rm.
Qed.
Lemma sl_grow_stmt_x_AR : sl_grow_stmt_x B [] ARI MT RP_AR MMAX RG <-> sl_grow_stmt B MT MMAX RG.
Proof.
unfold sl_grow_stmt_x, sl_grow_stmt. setoid_rewrite SLN_x_AR. setoid_rewrite SLM_x_AR.
setoid_rewrite SRr_sl_post_x_AR.
split.
- intros H regsE ly S W mem md c O mx no cap out line Bl WN regsN memN mdN sent n.
  exact (H regsE ly S [] W mem md c O mx no cap out line Bl WN regsN memN mdN sent n 0%nat).
- intros H regsE ly S _ W mem md c O mx no cap out line Bl WN regsN memN mdN sent n _.
  exact (H regsE ly S W mem md c O mx no cap out line Bl WN regsN memN mdN sent n).
Qed.
End br.

(* THE ARi0 BRIDGES (a Theorem Labs lane's HP0 ruling): at ARx := W_journal_x.ARi0 (AR /\ Hp = []) and PST := []. *)
Section br0.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
#[local] Abbreviation ARI0 := (ARi0 SEGS B).
Lemma SLN_x_AR0 : forall regsE ly S Hp W mem md c O mx no cap out line Bl WN regsN memN mdN sent n kr,
SLN_x B [] ARI0 MT RP_AR MMAX RG regsE ly S Hp W mem md c O mx no cap out line Bl WN regsN memN mdN sent n kr ->
SLN B MT MMAX RG regsE ly S W mem md c O mx no cap out line Bl WN regsN memN mdN sent n.
Proof.
intros regsE ly S Hp W mem md c O mx no cap out line Bl WN regsN memN mdN sent n kr H.
unfold SLN_x in H. unfold SLN. cbv zeta in H |- *.
destruct H as (lyN & SN & HpN & kN & evL & capN & outN & spent & rest & H).
exists lyN, SN, kN, evL, capN, outN, spent, rest. sl_decomp.
repeat match goal with Hj : context [@ajournal_gx_x] |- _ => apply ajournal_gx_x_ARi0_AR in Hj end.
repeat match goal with Hl : context [@sl_line_ok_x] |- _ => apply sl_line_ok_of_x_ARi0 in Hl end.
sl_rebuild.
Qed.
Lemma SLN_x_of_AR0 : forall regsE ly S Hp W mem md c O mx no cap out line Bl WN regsN memN mdN sent n kr,
SLN B MT MMAX RG regsE ly S W mem md c O mx no cap out line Bl WN regsN memN mdN sent n ->
SLN_x B [] ARI0 MT RP_AR MMAX RG regsE ly S Hp W mem md c O mx no cap out line Bl WN regsN memN mdN sent n kr.
Proof.
intros regsE ly S Hp W mem md c O mx no cap out line Bl WN regsN memN mdN sent n kr H.
unfold SLN in H. unfold SLN_x. cbv zeta in H |- *.
destruct H as (lyN & SN & kN & evL & capN & outN & spent & rest & H).
exists lyN, SN, [], kN, evL, capN, outN, spent, rest. sl_decomp.
repeat match goal with Hj : context [@W_journal.ajournal_gx] |- _ => apply ajournal_gx_AR_x_ARi0 with (Hp := Hp) in Hj end.
repeat match goal with Hl : context [@sl_line_ok] |- _ => apply sl_line_ok_x_ARi0_of in Hl end.
sl_rebuild_rm.
Qed.
Lemma sl_grow_stmt_x_AR0 : sl_grow_stmt_x B [] ARI0 MT RP_AR MMAX RG -> sl_grow_stmt B MT MMAX RG.
Proof.
intros H regsE ly S W mem md c O mx no cap out line Bl WN regsN memN mdN sent n HN K.
eapply SRr_mono; [eapply (H regsE ly S [] W mem md c O mx no cap out line Bl WN regsN memN mdN sent n 0%nat);
  [apply SLN_x_of_AR0; exact HN |] |].
- intros WM regsM memM mdM HM. apply SLM_x_AR0 in HM.
  eapply SRr_mono; [exact (K WM regsM memM mdM HM)|].
  intros W' c' _ HQ. apply sl_post_x_of_AR0_hp. exact HQ.
- intros W' c' _ HQ. revert HQ. apply sl_post_x_AR0.
Qed.
Lemma sl_grow_stmt_x_of_AR0 : sl_grow_stmt B MT MMAX RG -> sl_grow_stmt_x B [] ARI0 MT RP_AR MMAX RG.
Proof.
intros H regsE ly S Hp W mem md c O mx no cap out line Bl WN regsN memN mdN sent n kr HN K.
eapply SRr_mono; [eapply (H regsE ly S W mem md c O mx no cap out line Bl WN regsN memN mdN sent n);
  [eapply SLN_x_AR0; exact HN |] |].
- intros WM regsM memM mdM HM.
  eapply SRr_mono; [apply K; apply SLM_x_of_AR0; exact HM|].
  intros W' c' _ HQ. revert HQ. apply sl_post_x_AR0.
- intros W' c' _ HQ. apply sl_post_x_of_AR0_hp. exact HQ.
Qed.
End br0.
