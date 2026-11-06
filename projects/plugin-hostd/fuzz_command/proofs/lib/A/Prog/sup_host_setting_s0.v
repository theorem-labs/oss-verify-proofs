(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the first half of the walk of sup_chain_clear on plugin-hostd/fuzz_command.asan
   (the entry and the two arms of the inlined record() up to their join), in the walk style of
   lib/A/Prog/sup_chain_clear_s2.v; the entry seed after lib/A/Prog/sup_worker_list.v.
   The join and the rest of the walk are sup_chain_clear_s2.v's `scc_join`.
   Statement passes 4, 4b and 5: the rounding-mode-0 premise in place of astack_pres,
   handed to scc_join; the callees' contracts at every FP state, rec_calls_free's taken at the entry's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_chain_clear.v, with its module paths and module names changed; 293 of its 329 lines of code are new or changed and 632 lines of the source are left out. *)
(* The program points of sup_host_setting's ASan walk (plugin-hostd/fuzz_command, entry BASE + AF_sup_host_setting =
   0x8b094), and what holds at each, in the form of cgif_file_fuzzer's cgif_close walk (one statement per point of
   the listing, a segment lemma from each point to the next: proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v CL_*_stmtX).

   The points (BASE = 0x864e4, so a point's offset is its address - 0x864e4):
     JOIN    0x8b12c  record()'s two arms meet; c := the slot (recorder.c:205-221)
     RCF     0x8b10c  back from rec_calls_free on the spill arm
     AL      0x8b168  back from arg_line
     AI      0x8b174  back from arg_i
     L1H n   0x8b190  the length loop's head, at token n (recorder.c:368)
     L1R n   0x8b1a0  back from the strlen wrapper on token n
     MAL     0x8b1d4  back from the malloc wrapper (xmalloc inlined, recorder.c:369)
     L2S n   0x8b20c  back from the strlen wrapper on the word list, in the join loop at token n >= 1
     L2C n   0x8b258  back from the strcat wrapper that appended token n (recorder.c:371-373)
     XS      0x8b2a8  back from xstrdup of the word list (arg_s inlined, recorder.c:374)
     FR      0x8b2e4  back from the free wrapper on the word list (recorder.c:375)
     MIX     0x8b2f0  back from mix_call (recorder.c:376)
   Each statement says: from the point, with the facts the point carries, the run ends in the statement's post.
   arg_i reaches the snprintf wrapper, so the statement's post is FP-existential (apost_baseF): the points before
   the arg_i call (JOIN, RCF, AL) end in hs_postF at the entry's FP state; the points from AI on end in hs_post
   (apost_base) at the FP state arg_i returned, which apost_base_liftF lifts to hs_postF (sup_host_setting_s4.v).

   The facts every point after JOIN carries (hs_mid): the journal of the whole call so far (cgif's ajournal) with an
   event bound, the meter spent so far, the 13 callee-saved registers in the frame, and the block accounting (the
   blocks this call made, the entry's blocks still live, and which of them the recorder owns). Inputs (the line,
   the token array and the tokens) need no fact of their own: the journal of the whole call keeps every byte
   outside its footprint (g_rec, record.spill, the recorder's blocks). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaLibF PaLibG PaLibH PaSB PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c arg_line_c arg_i_c xstrdup_c mix_call_c sup_host_setting_c sup_host_setting_s1.
(* the program's writable statics (recb_PG, RecBLemmas.v:33) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the points, as offsets from BASE *)
Definition HS_RCF : Z := 0x4c28.
Definition HS_JOIN : Z := 0x4c48.
Definition HS_AL : Z := 0x4c84.
Definition HS_AI : Z := 0x4c90.
Definition HS_L1H : Z := 0x4cac.
Definition HS_L1R : Z := 0x4cbc.
Definition HS_MAL : Z := 0x4cf0.
Definition HS_L2S : Z := 0x4d28.
Definition HS_L2C : Z := 0x4d74.
Definition HS_XS : Z := 0x4dc4.
Definition HS_FR : Z := 0x4e00.
Definition HS_MIX : Z := 0x4e0c.
Lemma hs_entry_off : AF_sup_host_setting = 0x4bb0. Proof. reflexivity. Qed.

(* the shadow base, 0x7fff8000 *)
Definition HS_SB : Z := 0x7fff8000.
(* the callee-saved registers the prologue stores, at sp0 - 8 - 8 * j for the j-th (0x8b098 .. 0x8b0c8) *)
Definition HS_SAVED : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
(* the whole call's footprint, the statement's *)
Definition hs_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.
(* the three recorded arguments *)
Definition hs_args (line : list byte) (toks : list (list byte)) : list (list byte) :=
[canon line; dec (Z.of_nat (length toks)); join_sp toks].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the entry's data *)
Record hs_in := mkHsIn {
  i_ly : alayout; i_S : astate; i_W : world SEGS; i_regs : bvmap 5 word; i_mem : word -> option byte;
  i_md : Model; i_ch : list (Z * Z * Z); i_pl : Z; i_ptok : Z; i_ps : list Z; i_line : list byte;
  i_toks : list (list byte); i_R : rstate; i_O : list (Z * Z) }.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* The Section hypotheses of the walk, as one record so that each segment file carries one hypothesis. The first
   ten are tsup_host_setting_spec's own (sup_host_setting_c.v:84-93), at every FP state as the statement takes
   them; the others are the per-binary facts and kit items the statement does not carry yet, with
   the walks' shared names and forms (the final file states each as its own Section hypothesis). No
   field names the ambient FP state, so the record holds at the FP state arg_i returns as at the entry's. *)
Record hs_hyps : Prop := {
  hh_rcf : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT;
  hh_arg_line : forall fx0 : YK11.FPState, @targ_line_spec fx0 rc SK PI B MT;
  hh_arg_i : forall fx0 : YK11.FPState, @targ_i_spec fx0 rc SK PI B MT;
  hh_xstrdup : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT;
  hh_mix : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT;
  hh_malloc : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT;
  hh_free : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT;
  hh_strlen : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen);
  hh_strcat : forall fx0 : YK11.FPState, @astrcat_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcat);
  hh_vobjs : cmd_val_objs;
  (* the per-binary record, the malloc/free trampolines and the shadow-base cells, the meter's laws *)
  hh_HB : CmdBSyms B;
  hh_TL : PALib B;
  hh_MTL : ameter_laws MT;
  (* CL_CALL_PG: cl_callS (PaCall.v:327-347) with the inner footprint widened to the program's statics, for a
     callee whose post is apost_base (it returns at the FP state of the call) *)
  hh_CL : forall (fx0 : YK11.FPState) W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1
    EV1 (o : Z) raw ch1
    (K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
    ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
    spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
    getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
    getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
    achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
    (afn_pre SEGS B STK1 lyc Sc W regsc memc mdc ch1 ->
     SRr SEGS W (mkCfg (@mkst fx0 regsc pc memc (seg_rom SEGS)) mdc)
     (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
      c2 = mkCfg (@mkst fx0 regs2 raw mem2 (seg_rom SEGS)) md2 /\
      ajournal SEGS B STK1 (spZ regsc) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
      aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
    (forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n)
      \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a
      \/ (inFP FP a /\ Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a)) ->
    SRr SEGS W (mkCfg (@mkst fx0 regsc pc memc (seg_rom SEGS)) mdc)
    (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
     c2 = mkCfg (@mkst fx0 regs2 raw mem2 (seg_rom SEGS)) md2 /\
     ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
     ajournal SEGS B STK1 (sp0 + o) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
     aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2);
  (* cmd_sig_prog (lib/A/Prog/CmdObj.v): each program callee's call target *)
  hh_sigp : cmd_sig_prog;
  hh_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a;
  hh_prog_writable : forall ly S (W : world SEGS) mem md a,
    AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a;
  (* cmd_ro_ok at any AR state from arodata_okP (its form over RLO RHI) *)
  hh_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
    arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem);
  (* arodata_ok_journalP's two facts (CmdBase.v), and the read-only range off the program's statics *)
  hh_RRO : ro_below_ofl SEGS RLO RHI;
  hh_RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a;
  hh_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG;
  hh_atail_kept : forall ly S (W : world SEGS) mem md ly' S' (W' : world SEGS) mem' md' p n e,
    AR SEGS B ly S W mem md -> AR SEGS B ly' S' W' mem' md' ->
    ((In (p, n) (ablocks B ly S) /\ In (p, n) (ablocks B ly' S') /\ p <= e < p + n) \/
     (in_roP SEGS RLO RHI e /\ ~ Exists (in_zr e) (as_owned_static B))) ->
    atail_vis SEGS W mem e -> atail_vis SEGS W' mem' e;
  hh_heap_tail : forall ly S (W : world SEGS) mem md p n e,
    AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e;
  hh_rom_view : forall (W : world SEGS) mem, arodata_okP SEGS RLO RHI B (rdW W mem) -> rt_rom_view SEGS B W mem
}.

(* the callee-saved registers of the entry, in the frame *)
Definition hs_frame (rd : reader) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
forall j r, nth_error HS_SAVED j = Some r -> aval_mem rd (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).

(* a string argument as the statement states it (inside a live block that is none of the
   recorder's), in astr_argA's block-arm shape *)
Definition hs_str (ly : alayout) (S : astate) (rd : reader) (O : list (Z * Z)) (p : Z) (x : list byte) : Prop :=
let n := Z.of_nat (length x) + 1 in
p <> 0 /\ astr_atR rd p x /\ n <= LMAX + 1 /\
(in_blockA (ablocks B ly S) p n /\ Forall (fun qk => iv_apart p n (fst qk) (snd qk)) O).

(* the premises of tsup_host_setting_spec at the entry, in the walk's order, and the token tails (the statement's
   G2 (b): each token's terminator lies in its block, so its tail by cmd_heap_tail_vis). The fourth is the
   statement's rounding-mode-0 premise at the ambient FP state: at the entry the statement's, from AI on the one
   fxrel_frm0 gives at the FP state arg_i returned (sup_host_setting_s4.v hs4_cx_fx). *)
Definition hs_cx (x : hs_in) : Prop :=
let ly := i_ly x in let S := i_S x in let W := i_W x in let regs := i_regs x in let mem := i_mem x in
let md := i_md x in let ch := i_ch x in let pl := i_pl x in let ptok := i_ptok x in let ps := i_ps x in
let line := i_line x in let toks := i_toks x in let R := i_R x in let O := i_O x in
afn_pre SEGS B SUP_HOST_SETTING_STK ly S W regs mem md ch /\
arodata_okP SEGS RLO RHI B (rdW W mem) /\
cmd_ro_ok (rdW W mem) /\ Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 /\
(0 <= pl < 2 ^ 64 /\ 0 <= ptok < 2 ^ 64) /\
getr regs 10 = w64 pl /\ getr regs 11 = w64 ptok /\
getr regs 12 = w64 (Z.of_nat (length toks)) /\ (1 <= length toks <= 64)%nat /\
hs_str ly S (rdW W mem) O pl line /\
ptok <> 0 /\ ptok mod 8 = 0 /\
(afobj SEGS B ly S W mem ptok (8 * Z.of_nat (length toks)) \/
 (in_blockA (ablocks B ly S) ptok (8 * Z.of_nat (length toks)) /\
  Forall (fun qk => iv_apart ptok (8 * Z.of_nat (length toks)) (fst qk) (snd qk)) O)) /\
length ps = length toks /\
(forall i p, nth_error ps i = Some p -> aval_mem (rdW W mem) (ptok + 8 * Z.of_nat i) 8 p) /\
Forall2 (fun p w => hs_str ly S (rdW W mem) O p w) ps toks /\
hs_words_len toks <= LMAX + 1 /\
rec_repA B ly S (rdW W mem) R O /\
Z.of_nat (length (frames S)) <= 8 /\
st_nev S + EV_SUP_HOST_SETTING R <= EV_MAX /\ blocks_bytes S + LIVE_SUP_HOST_SETTING R line toks <= LIVE_MAX /\
mo_ok MT S (XM_SUP_HOST_SETTING MT R line toks) /\
(forall i p w, nth_error ps i = Some p -> nth_error toks i = Some w -> atail_vis SEGS W mem (p + Z.of_nat (length w))).

(* the post of tsup_host_setting_spec: its frame part hs_Q, in apost_base at the ambient FP state (hs_post, the
   points from AI on) and in apost_baseF (hs_postF, the statement's post) *)
Definition hs_Q (x : hs_in) : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
let ly := i_ly x in let S := i_S x in let line := i_line x in let toks := i_toks x in let R := i_R x in
let O := i_O x in
fun ly' S' W' regs' mem' md' => exists O' : list (Z * Z),
 rec_repA B ly' S' (rdW W' mem') (sup_host_setting_m R line toks) O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O') /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_HOST_SETTING R line toks /\
 mo_le MT S S' (XM_SUP_HOST_SETTING MT R line toks).
Definition hs_post (x : hs_in) : world SEGS -> config -> Prop :=
let ly := i_ly x in let S := i_S x in let W := i_W x in let regs := i_regs x in let mem := i_mem x in
let md := i_md x in let R := i_R x in let O := i_O x in
apost_base SEGS B SUP_HOST_SETTING_STK
 ((A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O)
 regs ly S W mem md (EV_SUP_HOST_SETTING R) (hs_Q x).
Definition hs_postF (x : hs_in) : world SEGS -> config -> Prop :=
let ly := i_ly x in let S := i_S x in let W := i_W x in let regs := i_regs x in let mem := i_mem x in
let md := i_md x in let R := i_R x in let O := i_O x in
apost_baseF SEGS B SUP_HOST_SETTING_STK
 ((A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O)
 regs ly S W mem md (EV_SUP_HOST_SETTING R) (hs_Q x).

(* the block accounting at a point: Nw the blocks this call made that are live, Rest the entry's blocks still
   live; the call frees only the recorder's (O) blocks, and O1 is what the recorder still owns of O *)
Definition hs_ba (x : hs_in) (lyc : alayout) (Sc : astate) (O1 Nw Rest : list (Z * Z)) : Prop :=
let ly := i_ly x in let S := i_S x in let O := i_O x in
Permutation (ablocks B lyc Sc) (Nw ++ Rest) /\
(forall pn, In pn Rest -> In pn (ablocks B ly S)) /\
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn Rest) /\
(forall pn, In pn Rest -> In pn O -> In pn O1) /\
(forall pn, In pn O1 -> In pn O) /\
(forall pn, In pn Nw -> In pn (ablocks B ly S) -> In pn O) /\
(forall pn, In pn O1 -> In pn Rest).

(* what every point from JOIN on carries: the journal of the call so far with at most kb events, the meter
   spent (at most ma), the frame, and the block accounting *)
Definition hs_mid (x : hs_in) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte) (mdc : Model)
  (k kb ma : Z) (O1 Nw Rest : list (Z * Z)) : Prop :=
let ly := i_ly x in let S := i_S x in let W := i_W x in let regs := i_regs x in let mem := i_mem x in
let md := i_md x in let O := i_O x in
ajournal SEGS B SUP_HOST_SETTING_STK (spZ regs) (hs_FP O) ly S W mem md [] lyc Sc Wc memc mdc k /\
0 <= k <= kb /\ mo_le MT S Sc ma /\ blocks_bytes Sc <= blocks_bytes S + bsum Nw /\
hs_frame (rdW Wc memc) (spZ regs) regs /\
hs_ba x lyc Sc O1 Nw Rest.

(* the registers every point from JOIN on has: the frame, gp/tp, c in s0, ntok in s1, g_rec in s6, the
   shadow base in s7 *)
Definition hs_regs0 (x : hs_in) (regs1 : bvmap 5 word) : Prop :=
let regs := i_regs x in let toks := i_toks x in let R := i_R x in
getr regs1 2 = w64 (spZ regs - 112) /\ getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4 /\
getr regs1 8 = w64 (hs_slot R) /\ getr regs1 9 = w64 (Z.of_nat (length toks)) /\
getr regs1 22 = w64 A_G_REC /\ getr regs1 23 = w64 HS_SB.
(* from AI on: s3 = c + 4 and s8 = its shadow byte's address *)
Definition hs_regs1 (x : hs_in) (regs1 : bvmap 5 word) : Prop :=
hs_regs0 x regs1 /\
getr regs1 19 = w64 (hs_slot (i_R x) + 4) /\ getr regs1 24 = w64 (HS_SB + (hs_slot (i_R x) + 4) / 8).

(* the run from a point ends in the post: hs_at from AI on, hs_atF before the arg_i call *)
Definition hs_at (x : hs_in) (pc : Z) (regs1 : bvmap 5 word) (Wc : world SEGS) (memc : word -> option byte) (mdc : Model) : Prop :=
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)) mdc) (hs_post x).
Definition hs_atF (x : hs_in) (pc : Z) (regs1 : bvmap 5 word) (Wc : world SEGS) (memc : word -> option byte) (mdc : Model) : Prop :=
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)) mdc) (hs_postF x).

(* the recorded arguments after arg_line and arg_i *)
Definition hs_A2 (x : hs_in) : list (list byte) := [canon (i_line x); dec (Z.of_nat (length (i_toks x)))].

(* the event and meter budgets spent at each point *)
Definition hs_k0 (x : hs_in) : Z := rec_spill_frees (i_R x).
Definition hs_m0 (x : hs_in) : Z := rec_spill_frees (i_R x) * mo_free MT.
Definition hs_k2 (x : hs_in) : Z := hs_k0 x + EV_ARG_LINE + EV_ARG_I.
Definition hs_m2 (x : hs_in) : Z := hs_m0 x + XM_ARG_LINE MT (i_line x) + XM_ARG_I MT (Z.of_nat (length (i_toks x))).
Definition hs_k3 (x : hs_in) : Z := hs_k2 x + 1.
Definition hs_m3 (x : hs_in) : Z := hs_m2 x + mo_malloc MT (hs_words_len (i_toks x) + 1).
Definition hs_k4 (x : hs_in) : Z := hs_k3 x + EV_XSTRDUP.
Definition hs_m4 (x : hs_in) : Z := hs_m3 x + XM_XSTRDUP MT (join_sp (i_toks x)).
Definition hs_k5 (x : hs_in) : Z := hs_k4 x + 1.
Definition hs_m5 (x : hs_in) : Z := hs_m4 x + mo_free MT.

(* the word list's block *)
Definition hs_wsz (x : hs_in) : Z := hs_words_len (i_toks x) + 1.
(* the nth token pointer and the bytes so far *)
Definition hs_tok (x : hs_in) (n : nat) : list byte := nth n (i_toks x) [].
Definition hs_ptr (x : hs_in) (n : nat) : Z := nth n (i_ps x) 0.

(* ---- the statements, one per point ---- *)

(* JOIN 0x8b12c: c := the slot; the recorder is record()'s up to its two stores *)
Definition ST_JOIN (x : hs_in) : Prop :=
forall lyc Sc Wc memc mdc regs1 k O1 Rest,
hs_cx x -> hs_mid x lyc Sc Wc memc mdc k (hs_k0 x) (hs_m0 x) O1 [] Rest ->
rec_repJ B lyc Sc (rdW Wc memc) (i_R x) O1 ->
hs_regs0 x regs1 -> getr regs1 18 = w64 (i_ptok x) -> getr regs1 20 = w64 (i_pl x) ->
hs_atF x HS_JOIN regs1 Wc memc mdc.

(* AL 0x8b168: canon line recorded in block b0 *)
Definition ST_AL (x : hs_in) : Prop :=
forall lyc Sc Wc memc mdc regs1 k O1 Rest b0,
hs_cx x -> hs_mid x lyc Sc Wc memc mdc k (hs_k0 x + EV_ARG_LINE) (hs_m0 x + XM_ARG_LINE MT (i_line x)) O1 [b0] Rest ->
snd b0 = LIVE_ARG_LINE (i_line x) ->
rec_repA B lyc Sc (rdW Wc memc) (rec_record (i_R x) REC_HOST_SETTING [canon (i_line x)]) (O1 ++ [b0]) ->
hs_regs1 x regs1 -> getr regs1 18 = w64 (i_ptok x) ->
hs_atF x HS_AL regs1 Wc memc mdc.

(* AI 0x8b174: dec ntok recorded in block b1 *)
Definition ST_AI (x : hs_in) : Prop :=
forall lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1,
hs_cx x -> hs_mid x lyc Sc Wc memc mdc k (hs_k2 x) (hs_m2 x) O1 [b0; b1] Rest ->
snd b0 = LIVE_ARG_LINE (i_line x) -> snd b1 = LIVE_ARG_I (Z.of_nat (length (i_toks x))) ->
rec_repA B lyc Sc (rdW Wc memc) (rec_record (i_R x) REC_HOST_SETTING (hs_A2 x)) (O1 ++ [b0; b1]) ->
hs_regs1 x regs1 -> getr regs1 18 = w64 (i_ptok x) ->
hs_at x HS_AI regs1 Wc memc mdc.

(* L1H n 0x8b190: the length loop at token n; s9 = the bytes of tokens 0..n-1 with their NULs, s10 = the tokens
   left, s11 = s4 = &tok[n], s5 = its shadow byte's address *)
Definition ST_L1H (x : hs_in) (n : nat) : Prop :=
forall lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1,
(n < length (i_toks x))%nat ->
hs_cx x -> hs_mid x lyc Sc Wc memc mdc k (hs_k2 x) (hs_m2 x) O1 [b0; b1] Rest ->
snd b0 = LIVE_ARG_LINE (i_line x) -> snd b1 = LIVE_ARG_I (Z.of_nat (length (i_toks x))) ->
rec_repA B lyc Sc (rdW Wc memc) (rec_record (i_R x) REC_HOST_SETTING (hs_A2 x)) (O1 ++ [b0; b1]) ->
hs_regs1 x regs1 -> getr regs1 18 = w64 (i_ptok x) ->
getr regs1 25 = w64 (hs_words_len (firstn n (i_toks x))) ->
getr regs1 26 = w64 (Z.of_nat (length (i_toks x) - n)) ->
getr regs1 27 = w64 (i_ptok x + 8 * Z.of_nat n) ->
getr regs1 20 = w64 (i_ptok x + 8 * Z.of_nat n) ->
getr regs1 21 = w64 (HS_SB + (i_ptok x + 8 * Z.of_nat n) / 8) ->
hs_at x HS_L1H regs1 Wc memc mdc.

(* L1R n 0x8b1a0: a0 = |tok[n]| *)
Definition ST_L1R (x : hs_in) (n : nat) : Prop :=
forall lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1,
(n < length (i_toks x))%nat ->
hs_cx x -> hs_mid x lyc Sc Wc memc mdc k (hs_k2 x) (hs_m2 x) O1 [b0; b1] Rest ->
snd b0 = LIVE_ARG_LINE (i_line x) -> snd b1 = LIVE_ARG_I (Z.of_nat (length (i_toks x))) ->
rec_repA B lyc Sc (rdW Wc memc) (rec_record (i_R x) REC_HOST_SETTING (hs_A2 x)) (O1 ++ [b0; b1]) ->
hs_regs1 x regs1 -> getr regs1 18 = w64 (i_ptok x) ->
getr regs1 10 = w64 (Z.of_nat (length (hs_tok x n))) ->
getr regs1 25 = w64 (hs_words_len (firstn n (i_toks x))) ->
getr regs1 26 = w64 (Z.of_nat (length (i_toks x) - n)) ->
getr regs1 27 = w64 (i_ptok x + 8 * Z.of_nat n) ->
getr regs1 20 = w64 (i_ptok x + 8 * Z.of_nat n) ->
getr regs1 21 = w64 (HS_SB + (i_ptok x + 8 * Z.of_nat n) / 8) ->
hs_at x HS_L1R regs1 Wc memc mdc.

(* MAL 0x8b1d4: a0 = w, the word list's block of hs_wsz bytes *)
Definition ST_MAL (x : hs_in) : Prop :=
forall lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 w,
hs_cx x -> hs_mid x lyc Sc Wc memc mdc k (hs_k3 x) (hs_m3 x) O1 [b0; b1; (w, hs_wsz x)] Rest ->
snd b0 = LIVE_ARG_LINE (i_line x) -> snd b1 = LIVE_ARG_I (Z.of_nat (length (i_toks x))) ->
rec_repA B lyc Sc (rdW Wc memc) (rec_record (i_R x) REC_HOST_SETTING (hs_A2 x)) (O1 ++ [b0; b1]) ->
hs_regs1 x regs1 -> getr regs1 18 = w64 (i_ptok x) ->
getr regs1 10 = w64 w -> 4096 <= w ->
hs_at x HS_MAL regs1 Wc memc mdc.

(* L2C n 0x8b258: the word list holds tokens 0..n joined; s9 = n, s5 = s2 = &tok[n], s4 = w, s10 = ' ' *)
Definition ST_L2C (x : hs_in) (n : nat) : Prop :=
forall lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 w,
(n < length (i_toks x))%nat ->
hs_cx x -> hs_mid x lyc Sc Wc memc mdc k (hs_k3 x) (hs_m3 x) O1 [b0; b1; (w, hs_wsz x)] Rest ->
snd b0 = LIVE_ARG_LINE (i_line x) -> snd b1 = LIVE_ARG_I (Z.of_nat (length (i_toks x))) ->
rec_repA B lyc Sc (rdW Wc memc) (rec_record (i_R x) REC_HOST_SETTING (hs_A2 x)) (O1 ++ [b0; b1]) ->
astr_atR (rdW Wc memc) w (join_sp (firstn (S n) (i_toks x))) ->
hs_regs1 x regs1 -> getr regs1 20 = w64 w -> 4096 <= w ->
getr regs1 25 = w64 (Z.of_nat n) -> getr regs1 26 = w64 32 ->
getr regs1 18 = w64 (i_ptok x + 8 * Z.of_nat n) -> getr regs1 21 = w64 (i_ptok x + 8 * Z.of_nat n) ->
hs_at x HS_L2C regs1 Wc memc mdc.

(* L2S n 0x8b20c (1 <= n): the word list holds tokens 0..n-1 joined, a0 its length *)
Definition ST_L2S (x : hs_in) (n : nat) : Prop :=
forall lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 w,
(1 <= n < length (i_toks x))%nat ->
hs_cx x -> hs_mid x lyc Sc Wc memc mdc k (hs_k3 x) (hs_m3 x) O1 [b0; b1; (w, hs_wsz x)] Rest ->
snd b0 = LIVE_ARG_LINE (i_line x) -> snd b1 = LIVE_ARG_I (Z.of_nat (length (i_toks x))) ->
rec_repA B lyc Sc (rdW Wc memc) (rec_record (i_R x) REC_HOST_SETTING (hs_A2 x)) (O1 ++ [b0; b1]) ->
astr_atR (rdW Wc memc) w (join_sp (firstn n (i_toks x))) ->
hs_regs1 x regs1 -> getr regs1 20 = w64 w -> 4096 <= w ->
getr regs1 10 = w64 (Z.of_nat (length (join_sp (firstn n (i_toks x))))) ->
getr regs1 25 = w64 (Z.of_nat n) -> getr regs1 26 = w64 32 ->
getr regs1 18 = w64 (i_ptok x + 8 * Z.of_nat n) -> getr regs1 21 = w64 (i_ptok x + 8 * Z.of_nat n) ->
hs_at x HS_L2S regs1 Wc memc mdc.

(* XS 0x8b2a8: a0 = q, xstrdup's copy of the joined word list *)
Definition ST_XS (x : hs_in) : Prop :=
forall lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 w q,
hs_cx x -> hs_mid x lyc Sc Wc memc mdc k (hs_k4 x) (hs_m4 x) O1
  [b0; b1; (w, hs_wsz x); (q, LIVE_XSTRDUP (join_sp (i_toks x)))] Rest ->
snd b0 = LIVE_ARG_LINE (i_line x) -> snd b1 = LIVE_ARG_I (Z.of_nat (length (i_toks x))) ->
rec_repA B lyc Sc (rdW Wc memc) (rec_record (i_R x) REC_HOST_SETTING (hs_A2 x)) (O1 ++ [b0; b1]) ->
astr_atR (rdW Wc memc) q (join_sp (i_toks x)) ->
Forall (fun qk => iv_apart q (LIVE_XSTRDUP (join_sp (i_toks x))) (fst qk) (snd qk)) (O1 ++ [b0; b1]) ->
hs_regs1 x regs1 -> getr regs1 20 = w64 w -> 4096 <= w ->
getr regs1 10 = w64 q -> 4096 <= q ->
hs_at x HS_XS regs1 Wc memc mdc.

(* FR 0x8b2e4: the call recorded with its three arguments, the word list freed *)
Definition ST_FR (x : hs_in) : Prop :=
forall lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 b2,
hs_cx x -> hs_mid x lyc Sc Wc memc mdc k (hs_k5 x) (hs_m5 x) O1 [b0; b1; b2] Rest ->
snd b0 = LIVE_ARG_LINE (i_line x) -> snd b1 = LIVE_ARG_I (Z.of_nat (length (i_toks x))) ->
snd b2 = LIVE_XSTRDUP (join_sp (i_toks x)) ->
rec_repA B lyc Sc (rdW Wc memc) (rec_record (i_R x) REC_HOST_SETTING (hs_args (i_line x) (i_toks x))) (O1 ++ [b0; b1; b2]) ->
hs_regs0 x regs1 ->
hs_at x HS_FR regs1 Wc memc mdc.

(* MIX 0x8b2f0: a0 = the new host-settings digest *)
Definition ST_MIX (x : hs_in) : Prop :=
forall lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 b2,
hs_cx x -> hs_mid x lyc Sc Wc memc mdc k (hs_k5 x) (hs_m5 x) O1 [b0; b1; b2] Rest ->
snd b0 = LIVE_ARG_LINE (i_line x) -> snd b1 = LIVE_ARG_I (Z.of_nat (length (i_toks x))) ->
snd b2 = LIVE_XSTRDUP (join_sp (i_toks x)) ->
rec_repA B lyc Sc (rdW Wc memc) (rec_record (i_R x) REC_HOST_SETTING (hs_args (i_line x) (i_toks x))) (O1 ++ [b0; b1; b2]) ->
hs_regs0 x regs1 ->
getr regs1 10 = w64 (mixcall (r_host (i_R x)) REC_HOST_SETTING (hs_args (i_line x) (i_toks x))) ->
hs_at x HS_MIX regs1 Wc memc mdc.

(* RCF 0x8b10c (spill arm): rec_calls_free emptied the spill; s0 = record.spill *)
Definition ST_RCF (x : hs_in) : Prop :=
forall lyc Sc Wc memc mdc regs1 k O1 Rest,
(16 <= length (r_calls (i_R x)))%nat ->
hs_cx x -> hs_mid x lyc Sc Wc memc mdc k (hs_k0 x) (hs_m0 x) O1 [] Rest ->
rec_repA B lyc Sc (rdW Wc memc) (set_spill (i_R x) (fst (r_spill (i_R x)), [])) O1 ->
hs_regs0 x regs1 -> getr regs1 18 = w64 (i_ptok x) -> getr regs1 20 = w64 (i_pl x) ->
hs_atF x HS_RCF regs1 Wc memc mdc.
End e.
End f.
End d.
