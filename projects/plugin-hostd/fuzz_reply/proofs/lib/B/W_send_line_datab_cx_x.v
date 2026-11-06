(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the IMAGE B (fuzz_reply.asan-ubsan) walk of fuzz_reply's send_line, in the
   form of the cgif walks of proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v (call sites), lib/A/AC8b.v (a loop over
   concrete cut states) and lib/A/ACfj.v (segments joined at cut points).
   REUSE (rule 24): proof-index send_line (2026-10-29T14:19Z) finds only the released UBSan proofs lib/U/Prog/
   send_line*.v (another image) and does not cover lib/B; git grep over origin/cold/* finds two donors and no lib/B
   W_send_line* or pb_send_line (checker line `R24BSendLine: CONFIRM`).  Ported here, STRUCTURE only (no theorem
   crosses either framework):
   - image A, new framework: a working branch 9367674296a lib/A/W_send_line_cx.v / _entry.v / _loop.v /
     _datab_cx.v / _grow_cx.v / W_send_line.v (pb_send_line_g, sl_grow_stmt its one premise) and the copy half
     a working branch 99ad96efcc6 lib/A/W_send_line_datab.v (sl_copy);
   - image B, old framework: a working branch 37280b674f71 lib/B/Prog/send_line_*.v (send_line_b.v:2283
     send_line_holds; its cuts, its trap handling and its data arm send_line_seg.v asl_grow_call / asl_copy_call).
   send_line (line, len) at 0x82854 (relay.c:66-86, fuzz_send inlined from fuzz_reply.c:278-313), 168 instructions,
   frame 144 (13 saved registers at 40(sp) .. 136(sp); the auipc values of g_client_broken, g_send_max, g_capout,
   g_out and g_send_dead spilled at 0(sp), 8(sp), 16(sp), 24(sp), 32(sp)).  Its cuts (offsets from send_line):
   - L    0x828f8 (+0xa4, A_sl_loop): the loop head, `sent < len`, before the UBSan pointer checks of line + sent;
   - N    0x829cc (+0x178, A_sl_n): a data round after n = min(len - sent, g_send_max or len - sent);
   - J    0x82a08 (+0x1b4, A_sl_join): the join of the grown and the not grown g_out, before the copy;
   - X    0x82aa0 (+0x24c, A_sl_epi): the epilogue.
   The statements below: sl_loop_stmt (from L), sl_grow_stmt (N to J through realloc), sl_copy_stmt (J to L or X),
   sl_entry_stmt (the entry, given the loop).  Image B differs from A where the UBSan checks are (11 trap sites, all
   to the `unimp` at 0x82adc, closed by lib/B/W_traps.v), where the globals are reached (B keeps fewer auipc values in
   registers and spills five), and in the errno tail: B re-reads errno after every store to it (0x82980) where A's
   compiler knew the value.
   Section hypotheses (each a kit name: W_journal.v, W_sites.v, W_kit.v, W_contract.v, W_shadow_pin.v):
   - runtime: AERRNO (aerrno_realizes at __errno_location), AMEMCPY (aintrin_realizes OCpy at __asan_memcpy),
     AREALLOC (arealloc_cf_rule at the realloc trampoline);
   - instance: LAWS, MTL (the meter's laws), TL (PALib), HG (gx_ok of G_SL), HGR (G_SL is no read-only byte), HROMO
     (rom_out of G_SL), HGO (gx_ok of aout_at's three read-only cells), HERRNO (as_errno = as_tp - 164), HERRZ (azs
     of errno), HERRW (errno's bytes writable), HERRAL (errno is 4-aligned: the ALIGN4 traps 0x82930 / 0x82964);
   - placement (the pinned PB_fr / fr_globals_b decide each by vm_compute): HV9 .. HV12 (the objects read by PLdHi)
     and HH18, HH20 .. HH25 (the kept and spilled auipc values the walk stores and loads through), HRGD (the cells
     pairwise apart). *)
(* Modified by Theorem Labs, 2026-10-30 (a Theorem Labs lane, row G-BSL-b):
   made from W_send_line_cx.v's copy-half cut (SLM, sl_copy_stmt): the same, over ARx in room form (the B twin of
   a Theorem Labs lane's lib/A/W_send_line_datab_cx_x.v) *)
(* Theorem Labs, 2026-10-30: the ARx-GENERIC twin of the copy half's statements in lib/B/W_send_line_cx.v (the cut J
   0x82a08 of image B's send_line data round, row G-BSL-b), from its text at 6df41a6c5267 (sha256 ec7655862ed0; internal record),
   transformed as image A's lib/A/W_send_line_datab_cx.v was into lib/A/W_send_line_datab_cx_x.v at
   a0c781b35e6 (sha256 a75c7842f804; internal record). B has no W_send_line_datab_cx.v: its one interface
   file W_send_line_cx.v holds SLM and sl_copy_stmt, so this file cites it. W_send_line_cx.v is NOT edited.
   proves no function (kind: statement text; plus the AR bridges).
   - The Section header is W_send_line_cx_x.v's (W_send_line_cx.v's over ARx, LAWS, PST, RP, HP0).
   - SLM_x and sl_copy_stmt_x are the twins of SLM and sl_copy_stmt: the journal W_journal_x.ajournal_gx_x (the entry's
     Hp after S, the join's HpM an existential after SM), sl_line_ok_x, the post W_contract_x.sl_post_x at the entry's
     Hp, W_send_line_cx_x.v's sl_loop_at_x for sl_loop_at (on B sl_loop_at_x sits in W_send_line_cx_x.v, as B's
     sl_loop_stmt is stated through sl_loop_at).
   - The AR-free names are CITED: sl_n, A_sl_join, sl_regsM, sl_spill, sl_saved.
   - BRIDGES as W_send_line_cx_x.v's: Section br (ARi, iff, every Hp) and Section br0 (ARi0: SLM_x_AR0 / SLM_x_of_AR0,
     sl_copy_stmt_x_AR0 / sl_copy_stmt_x_of_AR0).
   No statement difference is forced by ARx.
   THE ROOM FORM (image A's a0c781b35e6 / 0828d5d79f5), as W_send_line_cx_x.v's: `Variable RP : roomp` after MT,
   AREALLOC (caller-context form, CTX_R / HCTX_slr) at RP, HP0 (a Theorem Labs lane's HP0 ruling), BLKM (the copy's memcpy
   needs n < 2 ^ 32), SLM_x with C3's peak (W_send_line_cx.v SLM, unchanged) and after frames the room budget of the
   rounds after this one (sl_cost_run at MT_rk, on top of kr) and the entry's cnt_ok_pk RP sl_pk; SLM_x and
   sl_copy_stmt_x take the post's kr last. The bridges are at RP := RP_AR. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_sites W_contract W_frame W_shadow_pin W_send_line_rb W_send_line_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_journal_x W_sites_x W_contract_x W_send_line_cx_x.
(* route R: the send_line contract texts at a world relation R (a Theorem Labs lane's W_send_line_xR.v) and SRrG *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_send_line_xR.
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
(* a live block's request is below 2 ^ 30 (image A's BLKM text, W_LLVMFuzzerTestOneInput_exit_x.v:270; the top states it
   at ARX from the cf instance's AR_blocks_law_cf): the copy half's memcpy at 0x82a34 needs n < 2 ^ 32 *)
Hypothesis BLKM : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> n < 2 ^ 30.
(* W_send_line_cx_x.v's header (W_send_line_cx.v:97-140 over ARx, LAWS, PST, RP, HP0) *)
Hypothesis HG : gx_ok SEGS B (G_SL B RG).
Hypothesis HGR : forall a, inG (G_SL B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_SL B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes_x B ARx (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
(* The realloc site rule in its caller-context form (W_journal_x.v Section hc), as the top's ARE_x states it
   (CTX_AREALLOC, YCk0.v:34, holds [0x829f4]; YCk0.v:169 is send_line's edge to it); send_line hands the rule a cut
   chain (ch = []), so the trace is the return address alone (image A's a0c781b35e6..0828d5d79f5 form). *)
Variable CTX_R : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis HCTX_slr : In [BASE + AF_fr_send_line + 0x1a0] CTX_R.   (* realloc returns to 0x829f4 *)
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HERRAL : as_errno B mod 4 = 0.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV10 : VAL (A_OBJ 10) = rg_client_broken RG.
Hypothesis HV11 : VAL (A_OBJ 11) = rg_send_eintr RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_nout RG.
Hypothesis HH18 : VAL (A_HI 18) + 1212 = rg_client_broken RG.
Hypothesis HH20 : VAL (A_HI 20) + 1372 = rg_send_eintr RG.
Hypothesis HH21 : VAL (A_HI 21) + 1328 = rg_send_dead RG.
Hypothesis HH22 : VAL (A_HI 22) + 1252 = rg_send_max RG.
Hypothesis HH23 : VAL (A_HI 23) + 1372 = rg_nout RG.
Hypothesis HH24 : VAL (A_HI 24) + 1976 = rg_capout RG.
Hypothesis HH25 : VAL (A_HI 25) + 2000 = rg_out RG.
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4)].

(* W_send_line_cx.v:343 SLM: the state at J (0x82a08) of the round that sends n bytes from sent; kr is the post's *)
Definition SLM_x (regsE : bvmap 5 word) ly S (Hp : list Z) W mem md (c : ctl) (O : list byte) (mx no cap out line : Z)
(Bl : list byte) (WM : world SEGS) (regsM : bvmap 5 word) (memM : word -> option byte) (mdM : Model) (sent n : Z)
(kr : nat) : Prop :=
let len := Z.of_nat (length Bl) in
let sp0 := spZ regsE in
exists lyM SM HpM kM evL capM outM spent rest,
ajournal_gx_x SEGS B PST ARx (G_SL B RG) 0 [] SL_STK sp0 (ablocks_fp (aout_blks cap out)) ly S Hp W mem md []
  lyM SM HpM WM memM mdM kM /\
spZ regsM = sp0 - SL_FRAME /\ getr regsM 3 = getr regsE 3 /\ getr regsM 4 = getr regsE 4 /\
getr regsE 3 = w64 (as_gp B) /\ getr regsE 4 = w64 (as_tp B) /\
YK0s.ret_ok (getr regsE 1) /\ sl_regsM regsM len line sent n /\
sl_spill WM memM (sp0 - SL_FRAME) /\
sl_saved WM memM (sp0 - SL_FRAME) regsE /\
ct_cl c = 3 /\ ct_br c = 0 /\ ct_dd c = 0 /\ 0 <= sent < len /\ n = sl_n mx (len - sent) /\
evL = (if ct_ei c =? 1 then send_line_c.EINTR_V else ct_ev c) /\
aout_at B RG lyM SM WM memM (CTL 3 0 0 0 evL) (O ++ firstn (Z.to_nat sent) Bl) mx (no + sent) capM outM /\
no + sent + n <= capM /\
garr8 SEGS (arm WM memM) line (bzs Bl) /\ 0 <= line /\ line + len < 2 ^ 63 /\ rom_view SEGS WM memM /\
sl_line_ok_x B ARx lyM SM outM line len /\ (forall a, line <= a < line + len -> ~ inG (G_SL B RG) a) /\
sl_cap c mx no cap len = send_line_b_c.send_line_cap true mx (no + sent + n) capM (len - sent - n) /\
sl_max_run (Z.to_nat (len - sent - n)) mx (no + sent + n) capM (len - sent - n) < MMAX /\
blocks_bytes SM +
  tr_peak (send_line_b_c.send_line_tr true mx (no + sent + n) capM (len - sent - n) 0 RelayRunF.adr0) <= LIVE_MAX /\
apres_kept B W mem WM memM /\
mo_ok MT S (sl_cost MT c mx no cap len) /\ mo_le MT S SM spent /\
spent + sl_cost_run MT (Z.to_nat (len - sent - n)) mx (no + sent + n) capM (len - sent - n) <= sl_cost MT c mx no cap len /\
Permutation (ablocks B ly S) (aout_blks cap out ++ rest) /\ Permutation (ablocks B lyM SM) (aout_blks capM outM ++ rest) /\
frames SM = frames S /\
rp_RM RP SM (Z.to_nat (sl_cost_run MT_rk (Z.to_nat (len - sent - n)) mx (no + sent + n) capM (len - sent - n)) + kr) /\
cnt_ok_pk RP sl_pk (ablocks B ly S).
(* W_send_line_cx.v:370 sl_copy_stmt *)
Definition sl_copy_stmt_x : Prop :=
forall (n0 : nat) regsE ly S Hp W mem md c O mx no cap out line Bl WM regsM memM mdM sent n kr,
sl_loop_at_x B PST ARx MT RP MMAX RG n0 ->
SLM_x regsE ly S Hp W mem md c O mx no cap out line Bl WM regsM memM mdM sent n kr ->
2 * (Z.of_nat (length Bl) - sent) <= Z.of_nat (Datatypes.S n0) ->
SRr SEGS WM (mkCfg (mkst regsM (Z_to_bv 64 (BASE + A_sl_join)) memM (seg_rom SEGS)) mdM)
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
(* W_send_line_datab_cx_x.v:150 SLM_x at R *)
Definition SLM_xR (regsE : bvmap 5 word) ly S (Hp : list Z) W mem md (c : ctl) (O : list byte) (mx no cap out line : Z)
(Bl : list byte) (WM : world SEGS) (regsM : bvmap 5 word) (memM : word -> option byte) (mdM : Model) (sent n : Z)
(kr : nat) : Prop :=
let len := Z.of_nat (length Bl) in
let sp0 := spZ regsE in
exists lyM SM HpM kM evL capM outM spent rest,
ajournal_gx_xR SEGS B PST ARx R (G_SL B RG) 0 [] SL_STK sp0 (ablocks_fp (aout_blks cap out)) ly S Hp W mem md []
  lyM SM HpM WM memM mdM kM /\
spZ regsM = sp0 - SL_FRAME /\ getr regsM 3 = getr regsE 3 /\ getr regsM 4 = getr regsE 4 /\
getr regsE 3 = w64 (as_gp B) /\ getr regsE 4 = w64 (as_tp B) /\
YK0s.ret_ok (getr regsE 1) /\ sl_regsM regsM len line sent n /\
sl_spill WM memM (sp0 - SL_FRAME) /\
sl_saved WM memM (sp0 - SL_FRAME) regsE /\
ct_cl c = 3 /\ ct_br c = 0 /\ ct_dd c = 0 /\ 0 <= sent < len /\ n = sl_n mx (len - sent) /\
evL = (if ct_ei c =? 1 then send_line_c.EINTR_V else ct_ev c) /\
aout_at B RG lyM SM WM memM (CTL 3 0 0 0 evL) (O ++ firstn (Z.to_nat sent) Bl) mx (no + sent) capM outM /\
no + sent + n <= capM /\
garr8 SEGS (arm WM memM) line (bzs Bl) /\ 0 <= line /\ line + len < 2 ^ 63 /\ rom_view SEGS WM memM /\
sl_line_ok_x B ARx lyM SM outM line len /\ (forall a, line <= a < line + len -> ~ inG (G_SL B RG) a) /\
sl_cap c mx no cap len = send_line_b_c.send_line_cap true mx (no + sent + n) capM (len - sent - n) /\
sl_max_run (Z.to_nat (len - sent - n)) mx (no + sent + n) capM (len - sent - n) < MMAX /\
blocks_bytes SM +
  tr_peak (send_line_b_c.send_line_tr true mx (no + sent + n) capM (len - sent - n) 0 RelayRunF.adr0) <= LIVE_MAX /\
apres_kept B W mem WM memM /\
mo_ok MT S (sl_cost MT c mx no cap len) /\ mo_le MT S SM spent /\
spent + sl_cost_run MT (Z.to_nat (len - sent - n)) mx (no + sent + n) capM (len - sent - n) <= sl_cost MT c mx no cap len /\
Permutation (ablocks B ly S) (aout_blks cap out ++ rest) /\ Permutation (ablocks B lyM SM) (aout_blks capM outM ++ rest) /\
frames SM = frames S /\
rp_RM RP SM (Z.to_nat (sl_cost_run MT_rk (Z.to_nat (len - sent - n)) mx (no + sent + n) capM (len - sent - n)) + kr) /\
cnt_ok_pk RP sl_pk (ablocks B ly S).
(* W_send_line_datab_cx_x.v:181 sl_copy_stmt_x at R *)
Definition sl_copy_stmt_xR : Prop :=
forall (n0 : nat) regsE ly S Hp W mem md c O mx no cap out line Bl WM regsM memM mdM sent n kr,
sl_loop_at_xR B PST ARx MT RP MMAX RG R n0 ->
SLM_xR regsE ly S Hp W mem md c O mx no cap out line Bl WM regsM memM mdM sent n kr ->
2 * (Z.of_nat (length Bl) - sent) <= Z.of_nat (Datatypes.S n0) ->
SRrG SEGS R WM (mkCfg (mkst regsM (Z_to_bv 64 (BASE + A_sl_join)) memM (seg_rom SEGS)) mdM)
(sl_post_xR B PST ARx R MT RP RG regsE ly S Hp W mem md c O mx no cap out Bl kr).
End wR.
(* at R := wle the R texts are the strict ones (conversion) *)
Lemma SLM_x_wle : SLM_x = SLM_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma sl_copy_stmt_x_wle : sl_copy_stmt_x = sl_copy_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
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
Lemma SLM_x_AR : forall regsE ly S Hp W mem md c O mx no cap out line Bl WM regsM memM mdM sent n kr,
SLM_x B [] ARI MT RP_AR MMAX RG regsE ly S Hp W mem md c O mx no cap out line Bl WM regsM memM mdM sent n kr <->
SLM B MT MMAX RG regsE ly S W mem md c O mx no cap out line Bl WM regsM memM mdM sent n.
Proof.
intros. unfold SLM_x, SLM. cbv zeta.
setoid_rewrite (@ajournal_gx_x_AR fx rc SK). setoid_rewrite sl_line_ok_x_AR.
split.
- intros (l & s & h & kM & evL & capM & outM & spent & rest & HH).
  exists l, s, kM, evL, capM, outM, spent, rest. clear - HH. sl_decomp. sl_rebuild.
- intros (l & s & kM & evL & capM & outM & spent & rest & HH).
  exists l, s, [], kM, evL, capM, outM, spent, rest. clear - HH. sl_decomp. sl_rebuild_rm.
Qed.
Lemma sl_copy_stmt_x_AR : sl_copy_stmt_x B [] ARI MT RP_AR MMAX RG <-> sl_copy_stmt B MT MMAX RG.
Proof.
unfold sl_copy_stmt_x, sl_copy_stmt. setoid_rewrite sl_loop_at_x_AR. setoid_rewrite SLM_x_AR.
setoid_rewrite SRr_sl_post_x_AR.
split.
- intros H n0 regsE ly S W mem md c O mx no cap out line Bl WM regsM memM mdM sent n.
  exact (H n0 regsE ly S [] W mem md c O mx no cap out line Bl WM regsM memM mdM sent n 0%nat).
- intros H n0 regsE ly S _ W mem md c O mx no cap out line Bl WM regsM memM mdM sent n _.
  exact (H n0 regsE ly S W mem md c O mx no cap out line Bl WM regsM memM mdM sent n).
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
Lemma SLM_x_AR0 : forall regsE ly S Hp W mem md c O mx no cap out line Bl WM regsM memM mdM sent n kr,
SLM_x B [] ARI0 MT RP_AR MMAX RG regsE ly S Hp W mem md c O mx no cap out line Bl WM regsM memM mdM sent n kr ->
SLM B MT MMAX RG regsE ly S W mem md c O mx no cap out line Bl WM regsM memM mdM sent n.
Proof.
intros regsE ly S Hp W mem md c O mx no cap out line Bl WM regsM memM mdM sent n kr H.
unfold SLM_x in H. unfold SLM. cbv zeta in H |- *.
destruct H as (lyM & SM & HpM & kM & evL & capM & outM & spent & rest & H).
exists lyM, SM, kM, evL, capM, outM, spent, rest. clear - H fx rc SK. sl_decomp.
repeat match goal with Hj : context [@ajournal_gx_x] |- _ => apply ajournal_gx_x_ARi0_AR in Hj end.
repeat match goal with Hl : context [@sl_line_ok_x] |- _ => apply sl_line_ok_of_x_ARi0 in Hl end.
sl_rebuild.
Qed.
Lemma SLM_x_of_AR0 : forall regsE ly S Hp W mem md c O mx no cap out line Bl WM regsM memM mdM sent n kr,
SLM B MT MMAX RG regsE ly S W mem md c O mx no cap out line Bl WM regsM memM mdM sent n ->
SLM_x B [] ARI0 MT RP_AR MMAX RG regsE ly S Hp W mem md c O mx no cap out line Bl WM regsM memM mdM sent n kr.
Proof.
intros regsE ly S Hp W mem md c O mx no cap out line Bl WM regsM memM mdM sent n kr H.
unfold SLM in H. unfold SLM_x. cbv zeta in H |- *.
destruct H as (lyM & SM & kM & evL & capM & outM & spent & rest & H).
exists lyM, SM, [], kM, evL, capM, outM, spent, rest. clear - H fx rc SK. sl_decomp.
repeat match goal with Hj : context [@W_journal.ajournal_gx] |- _ => apply ajournal_gx_AR_x_ARi0 with (Hp := Hp) in Hj end.
repeat match goal with Hl : context [@sl_line_ok] |- _ => apply sl_line_ok_x_ARi0_of in Hl end.
sl_rebuild_rm.
Qed.
Lemma sl_copy_stmt_x_AR0 : sl_copy_stmt_x B [] ARI0 MT RP_AR MMAX RG -> sl_copy_stmt B MT MMAX RG.
Proof.
intros H n0 regsE ly S W mem md c O mx no cap out line Bl WM regsM memM mdM sent n Hl HM Hb.
eapply SRr_mono; [eapply (H n0 regsE ly S [] W mem md c O mx no cap out line Bl WM regsM memM mdM sent n 0%nat);
  [apply sl_loop_at_x_of_AR0; exact Hl | apply SLM_x_of_AR0; exact HM | exact Hb]|].
intros W' c' _ HQ. revert HQ. apply sl_post_x_AR0.
Qed.
Lemma sl_copy_stmt_x_of_AR0 : sl_copy_stmt B MT MMAX RG -> sl_copy_stmt_x B [] ARI0 MT RP_AR MMAX RG.
Proof.
intros H n0 regsE ly S Hp W mem md c O mx no cap out line Bl WM regsM memM mdM sent n kr Hl HM Hb.
eapply SRr_mono; [eapply (H n0 regsE ly S W mem md c O mx no cap out line Bl WM regsM memM mdM sent n);
  [apply sl_loop_at_x_AR0; exact Hl | eapply SLM_x_AR0; exact HM | exact Hb]|].
intros W' c' _ HQ. apply sl_post_x_of_AR0_hp. exact HQ.
Qed.
End br0.
