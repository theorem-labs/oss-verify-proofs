(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the fifth segment of check_reply's walk (fuzz_command.asan, 0x86d78), the
   strcmp call of the refusal path (0x86fb8) and the branch into the epilogue, ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (the step through a call and back) and A/ACh5.v (a segment that ends
   in another segment's statement), at c8557374ad2e.

   The code of the segment is
     0x86fb8  jal  wrapper_strcmp       a0 = g_rec.reply, a1 = s3 = F + 32, which holds "resp <code>"
     0x86fbc  beqz a0, 0x86ff8          equal: the epilogue; else j 0x870d8, the abort
   The entry facts give `xr = refusal_text (reply_code_a xr)` for a negative code (reply_okA), and the frame holds
   `refusal_text code ++ [0]` (the snprintf step of segment 4), so the two strings are equal, the interceptor
   returns 0, and the abort edge 0x86fc0 is not taken.

   The walk runs with the symbolic regions dropped (`st_ok_pi_submem` with []): the two instructions write no
   memory, so the engine's frame is empty and every byte the walk reads is the byte of the state the segment was
   entered in. The interceptor's own writes are the ones its contract allows, inside its scratch window below sp. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s5.v, with its module paths and module names changed; 304 of its 336 lines of code are new or changed and 380 lines of the source are left out. *)
(* The program points of sup_host_setting's ASan+UBSan walk (plugin-hostd/fuzz_command, fuzz_command.asan-ubsan,
   entry BASE + AF_sup_host_setting = 0x8b53c), and what holds at each: the B re-walk of the ASan walk's
   lib/A/Prog/sup_host_setting_s0.v (a working branch e323bbe76d2), in the same form (one statement
   per point of the listing, a segment lemma from each point to the next), at B's points.

   B's code differs from A's (a Theorem Labs lane's gen/dis/sup_host_setting.s; measured with capstone on the pin, 239
   instructions, 0x8b53c .. 0x8b8f8): B calls record(), arg_s() and xmalloc() where A inlines them, inlines arg_i
   (a class-0 side-stack frame from __asan_stack_malloc_0, b[16] at frame + 32, the snprintf wrapper), keeps a
   160-byte frame realigned by `andi sp,sp,-32`, spills c and the frame to the realigned stack across the loops, and
   carries four UBSan checks of &tok[n]. The points (BASE = 0x86530, a point's offset is its address - 0x86530):
     REC     0x8b64c  back from record(6): a0 = c, the slot (recorder.c:357)
     AL      0x8b658  back from arg_line(c, line) (recorder.c:358)
     AS1     0x8b684  back from arg_s(c, b) after snprintf(b, 16, "%d", ntok) (arg_i inlined, recorder.c:359)
     L1H n   0x8b6bc  the length loop's head at token n (recorder.c:365): the three UBSan checks, the load8 check
     L1R n   0x8b6e8  back from the strlen wrapper on token n
     XM      0x8b708  back from xmalloc(len + 1) (recorder.c:369)
     L2S n   0x8b744  back from the strlen wrapper on the word list, at token n >= 1 (recorder.c:371)
     L2C n   0x8b798  back from the strcat wrapper that appended token n (recorder.c:372-373)
     AS2     0x8b804  back from arg_s(c, words) (recorder.c:374)
     FR      0x8b80c  back from the free wrapper on the word list (recorder.c:375)
     MIX     0x8b81c  back from mix_call (recorder.c:376)
   Each statement says: from the point, with the facts the point carries, the run ends in the statement's post
   (hs_post, the post of tsup_host_setting_spec).

   What every point carries (hs_mid): the journal of the whole call so far, from the entry state, owning the
   side-stack frame (0, fpos) that __asan_stack_malloc_0 gave (frame F = frame_addr ly 0 fpos, flag FL =
   flag_addr ly 0 fpos), with an event bound, the meter spent so far, a bound of the live bytes added, the 13
   callee-saved registers in the 160-byte frame, the frame's flag pointer at F + 56 (read back at the release,
   0x8b854), and the block accounting (A's hs_ba). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaLibF PaLibG PaLibH PaSB PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
rec_calls_free_c record_c arg_line_c arg_s_c xmalloc_c mix_call_c sup_host_setting_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the points, as offsets from BASE *)
Definition HS_REC : Z := 0x511c.
Definition HS_AL : Z := 0x5128.
Definition HS_AS1 : Z := 0x5154.
Definition HS_L1H : Z := 0x518c.
Definition HS_L1R : Z := 0x51b8.
Definition HS_XM : Z := 0x51d8.
Definition HS_L2S : Z := 0x5214.
Definition HS_L2C : Z := 0x5268.
Definition HS_AS2 : Z := 0x52d4.
Definition HS_FR : Z := 0x52dc.
Definition HS_MIX : Z := 0x52ec.
Lemma hs_entry_off : AF_sup_host_setting = 0x500c. Proof. reflexivity. Qed.

(* the shadow base, 0x7fff8000 *)
Definition HS_SB : Z := 0x7fff8000.
(* the program's writable statics as a Theorem Labs lane's as_prog_static lists them (lib/B/YF0m.v TFIB_PROG_STATIC) *)
Definition recb_PG : list (Z * Z) := [(A_G_REC, REC_SIZE); (A_REC_SPILL, SC_SIZE); (A_G_QUITTING, 4)].
(* the callee-saved registers the prologue stores, at sp0 - 8 - 8 * j for the j-th (0x8b544 .. 0x8b574) *)
Definition HS_SAVED : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
(* the whole call's footprint, the statement's *)
Definition hs_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.
(* the three recorded arguments *)
Definition hs_args (line : list byte) (toks : list (list byte)) : list (list byte) :=
[canon line; dec (Z.of_nat (length toks)); join_sp toks].
(* the realigned stack pointer of the body: (sp0 - 160) & -32 (0x8b53c `addi sp,sp,-160`, 0x8b57c `andi sp,sp,-32`) *)
Definition hs_sp1 (sp0 : Z) : Z := 32 * ((sp0 - 160) / 32).

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
  i_toks : list (list byte); i_R : rstate; i_O : list (Z * Z); i_fx : YK11.FPState }.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* The Section hypotheses of the walk, as one record so that each segment file carries one hypothesis. The first
   twelve are tsup_host_setting_spec's own (sup_host_setting_c.v Section e, a Theorem Labs lane 92195a003c6: every callee and
   runtime rule taken at every FP state); the others are the walk's, with a Theorem Labs lane's names (lib/B/Prog/CmdRecFacts.v
   on 92195a003c6, a Theorem Labs lane's 09:0xZ convention; the model is a working branch c79a9f2daf7): the
   per-binary allocator record HB, the trampolines' and the side-stack entries' pcs TL / TLF, the meter's laws MTL /
   MTLF, the call targets SIGP, the auipc values VHIS (a Theorem Labs lane 08:12Z), the image facts IMG (a Theorem Labs lane's
   cmd_img_facts_tfib at this image, which also gives the snprintf contract's rt_rom_view by cmd_consts_view_snp), and
   the program statics' writability PRW, and the side-stack frames' flag law FFL (A's name; CmdRecRest's
   cmd_frame_flag_law at the pinned image). The final file states each as its own Section hypothesis; the facts the
   walk used to carry by name (cmd_prog_img, cmd_ro_ok_of_aro, RRO, cmd_ro_prog_apart, cmd_heap_tail_vis,
   cmd_rec_cells, ...) are a Theorem Labs lane's lemmas over IMG, below. *)
Record hs_hyps : Prop := {
  hh_record : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT;
  hh_arg_line : forall fx0 : YK11.FPState, @targ_line_spec fx0 rc SK PI B MT;
  hh_arg_s : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT;
  hh_xmalloc : forall fx0 : YK11.FPState, @txmalloc_spec fx0 rc SK PI B MT;
  hh_mix : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT;
  hh_smalloc0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0;
  hh_free_law : astack_free_law SEGS B;
  hh_snprintf : forall fx0 : YK11.FPState,
    @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158;
  hh_free : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT;
  hh_strlen : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen);
  hh_strcat : forall fx0 : YK11.FPState, @astrcat_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcat);
  hh_vobjs : cmd_val_objs;
  hh_HB : CmdBSyms B;
  hh_TL : PALib B;
  hh_TLF : PALibF B;
  hh_MTL : ameter_laws MT;
  hh_MTLF : ameter_fs_laws MT;
  hh_sigp : cmd_sig_prog;
  hh_vhis : cmd_val_his;
  hh_img : @cmd_img_facts SK SEGS B;
  hh_prw : prog_rw SEGS B;
  hh_FFL : frame_flag_lawP SEGS B
}.

Lemma hs_prog_static : TFIB_PROG_STATIC = recb_PG.
Proof. reflexivity. Qed.

(* the facts the walk names, from a Theorem Labs lane's lemmas over IMG (lib/B/Prog/CmdRec*.v on 92195a003c6) *)
Section hh.
Hypothesis HH : hs_hyps.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Lemma hh_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Proof. intros a Ha. rewrite <- hs_prog_static in Ha. exact (cmd_prog_img SEGS B LAWS (hh_HB HH) (hh_img HH) a Ha). Qed.
Lemma hh_prog_writable : forall ly S (W : world SEGS) mem md a,
  AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Proof.
intros ly S W mem md a _ Ha. apply (hh_prw HH). rewrite (ts_prog B (hh_HB HH)), hs_prog_static. exact Ha.
Qed.
Lemma hh_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Proof. exact (cmd_ro_ok_of_aro SEGS B LAWS (hh_HB HH) (hh_img HH)). Qed.
Lemma hh_RRO : ro_below_ofl SEGS RLO RHI.
Proof. exact (ROB SEGS B LAWS (hh_HB HH) (hh_img HH)). Qed.
Lemma hh_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Proof. rewrite <- hs_prog_static. exact (cmd_ro_prog_apart SEGS B LAWS (hh_HB HH) (hh_img HH)). Qed.
Lemma hh_heap_tail : forall ly S (W : world SEGS) mem md p n e,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e.
Proof.
intros ly S W mem md p n e HAR Hin He.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [_ Hr].
exact (cmd_heap_tail_vis SEGS B LAWS (hh_HB HH) ly S W mem md p n e HAR Hin ltac:(lia)).
Qed.
Lemma hh_rec_cells : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> aguard_ok SEGS W mem 0xa6bf8 0x604158.
Proof.
intros ly S W mem md HAR. exact (proj1 (proj2 (cmd_rec_cells SEGS B LAWS (hh_HB HH) (hh_img HH) ly S W mem md HAR))).
Qed.
End hh.

(* the callee-saved registers of the entry, in the frame *)
Definition hs_frame (rd : reader) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
forall j r, nth_error HS_SAVED j = Some r -> aval_mem rd (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).

(* a string argument as the statement states it (inside a live block that is none of the recorder's) *)
Definition hs_str (ly : alayout) (S : astate) (rd : reader) (O : list (Z * Z)) (p : Z) (x : list byte) : Prop :=
let n := Z.of_nat (length x) + 1 in
p <> 0 /\ astr_atR rd p x /\ n <= LMAX + 1 /\
(in_blockA (ablocks B ly S) p n /\ Forall (fun qk => iv_apart p n (fst qk) (snd qk)) O).

(* the premises of tsup_host_setting_spec at the entry, in the walk's order, and the token tails (each token's
   terminator lies in its block, so its tail by cmd_heap_tail_vis) *)
Definition hs_cx (x : hs_in) : Prop :=
let ly := i_ly x in let S := i_S x in let W := i_W x in let regs := i_regs x in let mem := i_mem x in
let md := i_md x in let ch := i_ch x in let pl := i_pl x in let ptok := i_ptok x in let ps := i_ps x in
let line := i_line x in let toks := i_toks x in let R := i_R x in let O := i_O x in
afn_pre SEGS B SUP_HOST_SETTING_STK ly S W regs mem md ch /\
arodata_okP SEGS RLO RHI B (rdW W mem) /\
cmd_ro_ok (rdW W mem) /\
(0 <= pl < 2 ^ 64 /\ 0 <= ptok < 2 ^ 64) /\
getr regs 10 = w64 pl /\ getr regs 11 = w64 ptok /\
getr regs 12 = w64 (Z.of_nat (length toks)) /\ (1 <= length toks <= 64)%nat /\
hs_str ly S (rdW W mem) O pl line /\
ptok <> 0 /\ ptok mod 8 = 0 /\
(afobj SEGS B ly S W mem ptok (8 * Z.of_nat (length toks)) \/
 (in_blockA (ablocks B ly S) ptok (8 * Z.of_nat (length toks)) /\
  Forall (fun qk => iv_apart ptok (8 * Z.of_nat (length toks)) (fst qk) (snd qk)) O)) /\
length ps = length toks /\
(forall i p, nth_error ps i = Some p -> 0 <= p < 2 ^ 64 /\ aval_mem (rdW W mem) (ptok + 8 * Z.of_nat i) 8 p) /\
Forall2 (fun p w => hs_str ly S (rdW W mem) O p w) ps toks /\
hs_words_len toks <= LMAX + 1 /\
rec_repA B ly S (rdW W mem) R O /\
Z.of_nat (length (frames S)) <= 8 /\
st_nev S + EV_SUP_HOST_SETTING R <= EV_MAX /\ blocks_bytes S + LIVE_SUP_HOST_SETTING R line toks <= LIVE_MAX /\
mo_ok MT S (XM_SUP_HOST_SETTING MT R line toks) /\
(forall i p w, nth_error ps i = Some p -> nth_error toks i = Some w -> atail_vis SEGS W mem (p + Z.of_nat (length w))) /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr (i_fx x))) 5) 7 = 0.

(* the post of tsup_host_setting_spec: FP-existential, against the entry's FP state *)
Definition hs_post (x : hs_in) : world SEGS -> config -> Prop :=
let ly := i_ly x in let S := i_S x in let W := i_W x in let regs := i_regs x in let mem := i_mem x in
let md := i_md x in let line := i_line x in let toks := i_toks x in let R := i_R x in let O := i_O x in
apost_baseF (fx := i_fx x) SEGS B SUP_HOST_SETTING_STK
 ((A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O)
 regs ly S W mem md (EV_SUP_HOST_SETTING R)
(fun ly' S' W' regs' mem' md' => exists O' : list (Z * Z),
 rec_repA B ly' S' (rdW W' mem') (sup_host_setting_m R line toks) O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O') /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_HOST_SETTING R line toks /\
 mo_le MT S S' (XM_SUP_HOST_SETTING MT R line toks)).

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

(* the frame and its flag *)
Definition hs_F (x : hs_in) (fpos : Z) : Z := frame_addr (i_ly x) 0 fpos.
Definition hs_FL (x : hs_in) (fpos : Z) : Z := flag_addr (i_ly x) 0 fpos.

(* what every point from REC on carries: the journal of the call so far (owning the frame) with at most kb events,
   the meter spent (at most ma), the live bytes added (at most lb), the saved registers, the frame's flag pointer,
   and the block accounting *)
Definition hs_mid (x : hs_in) (fpos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
  (mdc : Model) (k kb ma lb : Z) (O1 Nw Rest : list (Z * Z)) : Prop :=
let ly := i_ly x in let S := i_S x in let W := i_W x in let regs := i_regs x in let mem := i_mem x in
let md := i_md x in let O := i_O x in
ajournal SEGS B SUP_HOST_SETTING_STK (spZ regs) (hs_FP O) ly S W mem md [(0, fpos)] lyc Sc Wc memc mdc k /\
0 <= k <= kb /\ mo_le MT S Sc ma /\ blocks_bytes Sc <= blocks_bytes S + lb /\
hs_frame (rdW Wc memc) (spZ regs) regs /\
aval_mem (rdW Wc memc) (hs_F x fpos + 56) 8 (hs_FL x fpos) /\
hs_ba x lyc Sc O1 Nw Rest.

(* the registers every point from REC on has: the realigned sp and s1, s0 = the entry sp, gp/tp, ptok in s8, the
   frame's shadow in s9, the shadow base in s10 *)
Definition hs_regsK (x : hs_in) (fpos : Z) (regs1 : bvmap 5 word) : Prop :=
let regs := i_regs x in
getr regs1 2 = w64 (hs_sp1 (spZ regs)) /\ getr regs1 9 = w64 (hs_sp1 (spZ regs)) /\
getr regs1 8 = w64 (spZ regs) /\ getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4 /\
getr regs1 24 = w64 (i_ptok x) /\
getr regs1 25 = w64 (HS_SB + hs_F x fpos / 8) /\ getr regs1 26 = w64 HS_SB.
(* from REC to AS1: s2 = f8 (the poison byte), s3 = s4 = F, s5 = ntok, s6 = the line, s7 = b = F + 32 *)
Definition hs_regsF (x : hs_in) (fpos : Z) (regs1 : bvmap 5 word) : Prop :=
hs_regsK x fpos regs1 /\
getr regs1 18 = w64 (-8) /\ getr regs1 19 = w64 (hs_F x fpos) /\ getr regs1 20 = w64 (hs_F x fpos) /\
getr regs1 21 = w64 (Z.of_nat (length (i_toks x))) /\ getr regs1 22 = w64 (i_pl x) /\
getr regs1 23 = w64 (hs_F x fpos + 32).
(* in the loops: the slot c and the frame spilled to the realigned stack (0x8b690 .. 0x8b698) *)
Definition hs_spill (x : hs_in) (fpos : Z) (rd : reader) : Prop :=
let sp1 := hs_sp1 (spZ (i_regs x)) in
aval_mem rd (sp1 + 8) 8 (rec_slot (i_R x)) /\ aval_mem rd (sp1 + 16) 8 (hs_F x fpos) /\
aval_mem rd (sp1 + 24) 8 (hs_F x fpos).
(* the length loop's registers at token n: s2 = (tok <> 0) = 1, s7 = 1 (the UBSan facts of 0x8b6a0 .. 0x8b6ac),
   s5 = ntok, s3 = s6 = &tok[n], s4 = the bytes of tokens 0..n-1 with their NULs, s11 = the tokens left *)
Definition hs_regsL1 (x : hs_in) (fpos : Z) (n : nat) (regs1 : bvmap 5 word) : Prop :=
hs_regsK x fpos regs1 /\
getr regs1 18 = w64 1 /\ getr regs1 23 = w64 1 /\ getr regs1 21 = w64 (Z.of_nat (length (i_toks x))) /\
getr regs1 19 = w64 (i_ptok x + 8 * Z.of_nat n) /\ getr regs1 22 = w64 (i_ptok x + 8 * Z.of_nat n) /\
getr regs1 20 = w64 (hs_words_len (firstn n (i_toks x))) /\
getr regs1 27 = w64 (Z.of_nat (length (i_toks x) - n)).
(* the join loop's registers at token n: s6 = w, s7 = 8n, s11 = n, s5 = ~tok, s2 = ntok, s4 = ' ' *)
Definition hs_regsL2 (x : hs_in) (fpos : Z) (n : nat) (w : Z) (regs1 : bvmap 5 word) : Prop :=
hs_regsK x fpos regs1 /\
getr regs1 22 = w64 w /\ getr regs1 23 = w64 (8 * Z.of_nat n) /\ getr regs1 27 = w64 (Z.of_nat n) /\
getr regs1 21 = w64 (2 ^ 64 - 1 - i_ptok x) /\ getr regs1 18 = w64 (Z.of_nat (length (i_toks x))) /\
getr regs1 20 = w64 32.
(* after the loops: s3 = s4 = F (reloaded, 0x8b7c8 .. 0x8b7d0), s11 = c *)
Definition hs_regsE (x : hs_in) (fpos : Z) (regs1 : bvmap 5 word) : Prop :=
hs_regsK x fpos regs1 /\
getr regs1 19 = w64 (hs_F x fpos) /\ getr regs1 20 = w64 (hs_F x fpos) /\ getr regs1 27 = w64 (rec_slot (i_R x)).

(* the current FP state against the entry's: the f registers but f10 are the entry's, and fcsr is the entry's or
   has rounding mode 0 (apost_baseF's relation; reflexive and transitive) *)
Definition hs_fxrel (fxe fx' : YK11.FPState) : Prop :=
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fxe) k) /\
(@fp_csr fx' = @fp_csr fxe \/ Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0).

(* the run from a point ends in the post *)
Definition hs_at (x : hs_in) (pc : Z) (regs1 : bvmap 5 word) (Wc : world SEGS) (memc : word -> option byte) (mdc : Model) : Prop :=
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)) mdc) (hs_post x).

(* the recorded arguments after arg_line and the inlined arg_i *)
Definition hs_A1 (x : hs_in) : list (list byte) := [canon (i_line x)].
Definition hs_A2 (x : hs_in) : list (list byte) := [canon (i_line x); dec (Z.of_nat (length (i_toks x)))].

(* the event, meter and live-byte budgets spent at each point *)
Definition hs_k0 (x : hs_in) : Z := EV_RECORD (i_R x).
Definition hs_m0 (x : hs_in) : Z := XM_RECORD MT (i_R x).
Definition hs_k1 (x : hs_in) : Z := hs_k0 x + EV_ARG_LINE.
Definition hs_m1 (x : hs_in) : Z := hs_m0 x + XM_ARG_LINE MT (i_line x).
Definition hs_l1 (x : hs_in) : Z := LIVE_ARG_LINE (i_line x).
Definition hs_k2 (x : hs_in) : Z := hs_k1 x + EV_ARG_S.
Definition hs_m2 (x : hs_in) : Z := hs_m1 x + XM_ARG_S MT (Some (dec (Z.of_nat (length (i_toks x))))).
Definition hs_l2 (x : hs_in) : Z := hs_l1 x + LIVE_ARG_S (Some (dec (Z.of_nat (length (i_toks x))))).
Definition hs_wsz (x : hs_in) : Z := hs_words_len (i_toks x) + 1.
Definition hs_k3 (x : hs_in) : Z := hs_k2 x + EV_XMALLOC.
Definition hs_m3 (x : hs_in) : Z := hs_m2 x + XM_XMALLOC MT (hs_wsz x).
Definition hs_l3 (x : hs_in) : Z := hs_l2 x + LIVE_XMALLOC (hs_wsz x).
Definition hs_k4 (x : hs_in) : Z := hs_k3 x + EV_ARG_S.
Definition hs_m4 (x : hs_in) : Z := hs_m3 x + XM_ARG_S MT (Some (join_sp (i_toks x))).
Definition hs_l4 (x : hs_in) : Z := hs_l3 x + LIVE_ARG_S (Some (join_sp (i_toks x))).
Definition hs_k5 (x : hs_in) : Z := hs_k4 x + 1.
Definition hs_m5 (x : hs_in) : Z := hs_m4 x + mo_free MT.

(* the nth token and its pointer *)
Definition hs_tok (x : hs_in) (n : nat) : list byte := nth n (i_toks x) [].
Definition hs_ptr (x : hs_in) (n : nat) : Z := nth n (i_ps x) 0.

(* the sizes of the recorder's new blocks *)
Definition hs_b0 (x : hs_in) : Z := Z.of_nat (length (i_line x)) + 1.
Definition hs_b1 (x : hs_in) : Z := Z.of_nat (length (dec (Z.of_nat (length (i_toks x))))) + 1.
Definition hs_b3 (x : hs_in) : Z := Z.of_nat (length (join_sp (i_toks x))) + 1.

(* ---- the statements, one per point ---- *)

(* REC 0x8b64c: c = the slot; the recorder holds (6, []) there; record() freed only blocks of O *)
Definition ST_REC (x : hs_in) : Prop :=
forall fpos lyc Sc Wc memc mdc regs1 k O1 Rest,
hs_cx x -> hs_fxrel (i_fx x) fx -> hs_mid x fpos lyc Sc Wc memc mdc k (hs_k0 x) (hs_m0 x) 0 O1 [] Rest ->
rec_repA B lyc Sc (rdW Wc memc) (rec_record (i_R x) REC_HOST_SETTING []) O1 ->
hs_regsF x fpos regs1 -> getr regs1 10 = w64 (rec_slot (i_R x)) ->
hs_at x HS_REC regs1 Wc memc mdc.

(* AL 0x8b658: canon line recorded in block b0 *)
Definition ST_AL (x : hs_in) : Prop :=
forall fpos lyc Sc Wc memc mdc regs1 k O1 Rest b0,
hs_cx x -> hs_fxrel (i_fx x) fx -> hs_mid x fpos lyc Sc Wc memc mdc k (hs_k1 x) (hs_m1 x) (hs_l1 x) O1 [(b0, hs_b0 x)] Rest ->
rec_repA B lyc Sc (rdW Wc memc) (rec_record (i_R x) REC_HOST_SETTING (hs_A1 x)) ((b0, hs_b0 x) :: O1) ->
hs_regsF x fpos regs1 -> getr regs1 27 = w64 (rec_slot (i_R x)) ->
hs_at x HS_AL regs1 Wc memc mdc.

(* AS1 0x8b684: dec ntok recorded in block b1 *)
Definition ST_AS1 (x : hs_in) : Prop :=
forall fpos lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1,
hs_cx x -> hs_fxrel (i_fx x) fx -> hs_mid x fpos lyc Sc Wc memc mdc k (hs_k2 x) (hs_m2 x) (hs_l2 x) O1 [(b0, hs_b0 x); (b1, hs_b1 x)] Rest ->
rec_repA B lyc Sc (rdW Wc memc) (rec_record (i_R x) REC_HOST_SETTING (hs_A2 x)) ((b1, hs_b1 x) :: (b0, hs_b0 x) :: O1) ->
hs_regsF x fpos regs1 -> getr regs1 27 = w64 (rec_slot (i_R x)) ->
hs_at x HS_AS1 regs1 Wc memc mdc.

(* L1H n 0x8b6bc: the length loop at token n *)
Definition ST_L1H (x : hs_in) (n : nat) : Prop :=
forall fpos lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1,
(n < length (i_toks x))%nat ->
hs_cx x -> hs_fxrel (i_fx x) fx -> hs_mid x fpos lyc Sc Wc memc mdc k (hs_k2 x) (hs_m2 x) (hs_l2 x) O1 [(b0, hs_b0 x); (b1, hs_b1 x)] Rest ->
rec_repA B lyc Sc (rdW Wc memc) (rec_record (i_R x) REC_HOST_SETTING (hs_A2 x)) ((b1, hs_b1 x) :: (b0, hs_b0 x) :: O1) ->
hs_spill x fpos (rdW Wc memc) ->
hs_regsL1 x fpos n regs1 ->
hs_at x HS_L1H regs1 Wc memc mdc.

(* L1R n 0x8b6e8: a0 = |tok[n]| *)
Definition ST_L1R (x : hs_in) (n : nat) : Prop :=
forall fpos lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1,
(n < length (i_toks x))%nat ->
hs_cx x -> hs_fxrel (i_fx x) fx -> hs_mid x fpos lyc Sc Wc memc mdc k (hs_k2 x) (hs_m2 x) (hs_l2 x) O1 [(b0, hs_b0 x); (b1, hs_b1 x)] Rest ->
rec_repA B lyc Sc (rdW Wc memc) (rec_record (i_R x) REC_HOST_SETTING (hs_A2 x)) ((b1, hs_b1 x) :: (b0, hs_b0 x) :: O1) ->
hs_spill x fpos (rdW Wc memc) ->
hs_regsL1 x fpos n regs1 -> getr regs1 10 = w64 (Z.of_nat (length (hs_tok x n))) ->
hs_at x HS_L1R regs1 Wc memc mdc.

(* XM 0x8b708: a0 = w, the word list's block of hs_wsz bytes; s4 = the bytes of all tokens with their NULs *)
Definition ST_XM (x : hs_in) : Prop :=
forall fpos lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 w,
hs_cx x -> hs_fxrel (i_fx x) fx -> hs_mid x fpos lyc Sc Wc memc mdc k (hs_k3 x) (hs_m3 x) (hs_l3 x) O1
  [(b0, hs_b0 x); (b1, hs_b1 x); (w, LIVE_XMALLOC (hs_wsz x))] Rest ->
rec_repA B lyc Sc (rdW Wc memc) (rec_record (i_R x) REC_HOST_SETTING (hs_A2 x)) ((b1, hs_b1 x) :: (b0, hs_b0 x) :: O1) ->
hs_spill x fpos (rdW Wc memc) ->
hs_regsK x fpos regs1 -> getr regs1 21 = w64 (Z.of_nat (length (i_toks x))) ->
getr regs1 10 = w64 w -> 4096 <= w ->
hs_at x HS_XM regs1 Wc memc mdc.

(* L2C n 0x8b798: the word list holds tokens 0..n joined *)
Definition ST_L2C (x : hs_in) (n : nat) : Prop :=
forall fpos lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 w,
(n < length (i_toks x))%nat ->
hs_cx x -> hs_fxrel (i_fx x) fx -> hs_mid x fpos lyc Sc Wc memc mdc k (hs_k3 x) (hs_m3 x) (hs_l3 x) O1
  [(b0, hs_b0 x); (b1, hs_b1 x); (w, LIVE_XMALLOC (hs_wsz x))] Rest ->
rec_repA B lyc Sc (rdW Wc memc) (rec_record (i_R x) REC_HOST_SETTING (hs_A2 x)) ((b1, hs_b1 x) :: (b0, hs_b0 x) :: O1) ->
hs_spill x fpos (rdW Wc memc) ->
astr_atR (rdW Wc memc) w (join_sp (firstn (S n) (i_toks x))) -> 4096 <= w ->
hs_regsL2 x fpos n w regs1 ->
hs_at x HS_L2C regs1 Wc memc mdc.

(* L2S n 0x8b744 (1 <= n): the word list holds tokens 0..n-1 joined, a0 its length *)
Definition ST_L2S (x : hs_in) (n : nat) : Prop :=
forall fpos lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 w,
(1 <= n < length (i_toks x))%nat ->
hs_cx x -> hs_fxrel (i_fx x) fx -> hs_mid x fpos lyc Sc Wc memc mdc k (hs_k3 x) (hs_m3 x) (hs_l3 x) O1
  [(b0, hs_b0 x); (b1, hs_b1 x); (w, LIVE_XMALLOC (hs_wsz x))] Rest ->
rec_repA B lyc Sc (rdW Wc memc) (rec_record (i_R x) REC_HOST_SETTING (hs_A2 x)) ((b1, hs_b1 x) :: (b0, hs_b0 x) :: O1) ->
hs_spill x fpos (rdW Wc memc) ->
astr_atR (rdW Wc memc) w (join_sp (firstn n (i_toks x))) -> 4096 <= w ->
hs_regsL2 x fpos n w regs1 ->
getr regs1 10 = w64 (Z.of_nat (length (join_sp (firstn n (i_toks x))))) ->
hs_at x HS_L2S regs1 Wc memc mdc.

(* AS2 0x8b804: the joined words recorded in block b3; s6 = w still live *)
Definition ST_AS2 (x : hs_in) : Prop :=
forall fpos lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 w b3,
hs_cx x -> hs_fxrel (i_fx x) fx -> hs_mid x fpos lyc Sc Wc memc mdc k (hs_k4 x) (hs_m4 x) (hs_l4 x) O1
  [(b0, hs_b0 x); (b1, hs_b1 x); (w, LIVE_XMALLOC (hs_wsz x)); (b3, hs_b3 x)] Rest ->
rec_repA B lyc Sc (rdW Wc memc) (rec_record (i_R x) REC_HOST_SETTING (hs_args (i_line x) (i_toks x)))
  ((b3, hs_b3 x) :: (b1, hs_b1 x) :: (b0, hs_b0 x) :: O1) ->
4096 <= w ->
hs_regsE x fpos regs1 -> getr regs1 22 = w64 w ->
hs_at x HS_AS2 regs1 Wc memc mdc.

(* FR 0x8b80c: the word list freed *)
Definition ST_FR (x : hs_in) : Prop :=
forall fpos lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 b3,
hs_cx x -> hs_fxrel (i_fx x) fx -> hs_mid x fpos lyc Sc Wc memc mdc k (hs_k5 x) (hs_m5 x) (hs_l4 x) O1
  [(b0, hs_b0 x); (b1, hs_b1 x); (b3, hs_b3 x)] Rest ->
rec_repA B lyc Sc (rdW Wc memc) (rec_record (i_R x) REC_HOST_SETTING (hs_args (i_line x) (i_toks x)))
  ((b3, hs_b3 x) :: (b1, hs_b1 x) :: (b0, hs_b0 x) :: O1) ->
hs_regsE x fpos regs1 ->
hs_at x HS_FR regs1 Wc memc mdc.

(* MIX 0x8b81c: a0 = the new host-settings digest, s2 = the auipc value 0x5e380c (A_HI 151) *)
Definition ST_MIX (x : hs_in) : Prop :=
forall fpos lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 b3,
hs_cx x -> hs_fxrel (i_fx x) fx -> hs_mid x fpos lyc Sc Wc memc mdc k (hs_k5 x) (hs_m5 x) (hs_l4 x) O1
  [(b0, hs_b0 x); (b1, hs_b1 x); (b3, hs_b3 x)] Rest ->
rec_repA B lyc Sc (rdW Wc memc) (rec_record (i_R x) REC_HOST_SETTING (hs_args (i_line x) (i_toks x)))
  ((b3, hs_b3 x) :: (b1, hs_b1 x) :: (b0, hs_b0 x) :: O1) ->
hs_regsE x fpos regs1 -> getr regs1 18 = w64 0x5e380c ->
getr regs1 10 = w64 (mixcall (r_host (i_R x)) REC_HOST_SETTING (hs_args (i_line x) (i_toks x))) ->
hs_at x HS_MIX regs1 Wc memc mdc.
End e.
End f.
End d.
