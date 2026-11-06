(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the shared vocabulary of the walk of chain_words (0x8dfd4) on the ASan build of
   plugin-hostd/fuzz_command, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACa3.v (the context record, the
   entry facts, the post and the "from a cut point" predicates of cgif_raw_addframe's walk), with the cut points
   stated over the machine state, not over a symbolic state: each segment file builds its own symbolic state.
   The cut points (offsets from chain_words' entry):
     KC 0x218 (0x8e1ec)  the frame is set up and ntok >= 3; the first inline check is next
     KL 0x260 (0x8e234)  the head of the member loop, pass j
     KD 0x290 (0x8e264)  every word parsed; the sup_chain call is next
     KR 0x2a4 (0x8e278)  the refusal: sup_resp(-902) is next
     KJ 0x2ac (0x8e280)  the join after the recorder call; the release of the frame is next
   The program calls compose through cl_callS_wide (lib/A/Prog/PaNoChain.v, over the core's ajournal_sub_wide,
   YCbq.v), and the recorder calls through its FP form cl_callS_wideF (lib/A/Prog/PaFx.v): number writes id in the
   caller's stack window and ids[j] in the caller's own frame, sup_chain writes g_rec and record.spill, all of them
   awr_byte bytes of chain_words' journal.
   Statement passes 4 and 5: the post cw_post is apost_baseF; the two recorder callees
   (sup_chain, sup_resp) return at some FP state fx1 with fxrel fx fx1, so the join KJ and the last segment S6 are
   stated at every FP state (from_KJ at fx1 proves apost_base at fx1, cw_postB, which srr_after_callF_base lifts);
   the rounding-mode premise (frm0 fx) is a premise of the two segments that call them (cw_S4P, cw_S5P). No
   statement assumes astack_pres any more: the entry facts and the callers' objects carry none. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaSB PaCall PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import number_c sup_chain_c sup_resp_c chain_words_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(* the cut points, as offsets from the listing's start (BASE + CW_K* is the address) *)
Definition CW_KC : Z := AF_chain_words + 0x218.
Definition CW_KL : Z := AF_chain_words + 0x260.
Definition CW_KD : Z := AF_chain_words + 0x290.
Definition CW_KR : Z := AF_chain_words + 0x2a4.
Definition CW_KJ : Z := AF_chain_words + 0x2ac.
(* the registers the prologue saves, in the order of their slots: slot j at sp0 - 8 - 8 j (ra at 120(sp), s0 at
   112(sp), ..., s11 at 24(sp), with sp = sp0 - 128) *)
Definition cw_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the values the walk keeps from chain_words' entry: the statement's binders, and the position of the class-3
   side-stack frame that __asan_stack_malloc_3 hands back (x_fpos; any value before that call) *)
Record cwx : Type := mkCWX {
  x_ly : alayout; x_S : astate; x_W : world SEGS; x_regs : bvmap 5 word; x_mem : word -> option byte; x_md : Model;
  x_ch : list (Z * Z * Z); x_tok : Z; x_ntok : Z; x_cb : Z; x_ncb : Z;
  x_ptrs : list Z; x_tks : list (list byte); x_R : rstate; x_O : list (Z * Z); x_fpos : Z }.
Definition cw_setpos (c : cwx) (f : Z) : cwx :=
  mkCWX (x_ly c) (x_S c) (x_W c) (x_regs c) (x_mem c) (x_md c) (x_ch c) (x_tok c) (x_ntok c) (x_cb c) (x_ncb c)
    (x_ptrs c) (x_tks c) (x_R c) (x_O c) f.
(* the entry stack pointer, the realigned one (andi sp,sp,-32 at 0x8e014 after addi sp,sp,-128; it is sp0 - 128 or
   sp0 - 144), the frame and its flag *)
Definition cw_sp0 (c : cwx) : Z := spZ (x_regs c).
Definition cw_s1 (c : cwx) : Z := (cw_sp0 c - 128) - (cw_sp0 c - 128) mod 32.
Definition cw_F (c : cwx) : Z := frame_addr (x_ly c) 3 (x_fpos c).
Definition cw_FL (c : cwx) : Z := flag_addr (x_ly c) 3 (x_fpos c).
Lemma cw_s1_facts : forall c, cw_sp0 c mod 16 = 0 ->
  cw_s1 c mod 32 = 0 /\ (cw_s1 c = cw_sp0 c - 128 \/ cw_s1 c = cw_sp0 c - 144).
Proof.
intros c H. unfold cw_s1. pose proof (Z.mod_pos_bound (cw_sp0 c - 128) 32 ltac:(lia)) as M.
assert (Hm : (cw_sp0 c - 128) mod 32 = 0 \/ (cw_sp0 c - 128) mod 32 = 16).
{ pose proof (Z.div_mod (cw_sp0 c - 128) 32 ltac:(lia)) as D. pose proof (Z.div_mod (cw_sp0 c) 16 ltac:(lia)) as D2.
  rewrite H in D2. lia. }
split; [|lia].
replace ((cw_sp0 c - 128) - (cw_sp0 c - 128) mod 32) with (32 * ((cw_sp0 c - 128) / 32))
  by (pose proof (Z.div_mod (cw_sp0 c - 128) 32 ltac:(lia)); lia).
rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Variables RLO RHI : Z.
Definition cw_FP (c : cwx) : list (Z * Z) := CHAIN_WORDS_PG ++ ablocks_fp (x_O c).
(* tchain_words_spec's premises over the context (chain_words_c.v:97-116), but the rounding-mode premise, which is
   about the FP state of the configuration and is a premise of cw_S4P / cw_S5P *)
Record cw_pre (c : cwx) : Prop := mkCWPre {
  cp_afn : afn_pre SEGS B CHAIN_WORDS_STK (x_ly c) (x_S c) (x_W c) (x_regs c) (x_mem c) (x_md c) (x_ch c);
  cp_rod : arodata_okP SEGS RLO RHI B (rdW (x_W c) (x_mem c));
  cp_a0 : getr (x_regs c) 10 = w64 (x_tok c);
  cp_tok64 : 0 <= x_tok c < 2 ^ 64;
  cp_a1 : getr (x_regs c) 11 = w64 (x_ntok c);
  cp_tokobj : afobj SEGS B (x_ly c) (x_S c) (x_W c) (x_mem c) (x_tok c) (8 * x_ntok c);
  cp_toks : atoks_atA (rdW (x_W c) (x_mem c)) (x_tok c) (x_ptrs c) (x_tks c) (x_cb c) (x_ncb c);
  cp_cb : In (x_cb c, x_ncb c) (ablocks B (x_ly c) (x_S c));
  cp_cbO : ~ In (x_cb c, x_ncb c) (x_O c);
  cp_ntok : x_ntok c = Z.of_nat (length (x_tks c));
  cp_ntokr : 1 <= x_ntok c <= 64;
  cp_verb : nth_error (x_tks c) 0 = Some Verbs.Lit.verb_chain;
  cp_rec : rec_repA B (x_ly c) (x_S c) (rdW (x_W c) (x_mem c)) (x_R c) (x_O c);
  cp_refuse : r_refuse (x_R c) <> 0 -> declared (r_code (x_R c)) = true;
  cp_calls : (length (r_calls (x_R c)) + 1 <= 16)%nat;
  cp_ro : cmd_ro_ok (rdW (x_W c) (x_mem c));
  cp_vobjs : cmd_val_objs;
  cp_frames : Z.of_nat (length (frames (x_S c))) <= 5;
  cp_nev : st_nev (x_S c) + EV_CHAIN_WORDS (x_R c) <= EV_MAX;
  cp_live : blocks_bytes (x_S c) + LIVE_CHAIN_WORDS <= LIVE_MAX;
  cp_meter : mo_ok MT (x_S c) (XM_CHAIN_WORDS MT (x_R c)) }.
(* what the walk gives at the return: tchain_words_spec's post (chain_words_c.v:119-134): the returned block's size
   is exact, n = |x| + 1, as both recorder callees return it (sup_chain_c.v, sup_resp_c.v) *)
Definition cw_Q (c : cwx) : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' =>
 let '(R', x) := VerbsRun.chain_run (x_R c) (tl (x_tks c)) in
 exists (O' : list (Z * Z)) (p n : Z),
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 getr regs' 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\ In (p, n) (ablocks B ly' S') /\ ~ In (p, n) O' /\
 astr_atR (rdW W' mem') p x /\ n = Z.of_nat (length x) + 1 /\
 (forall pn, In pn (ablocks B (x_ly c) (x_S c)) -> ~ In pn (x_O c) -> iv_apart (fst pn) (snd pn) p n) /\
 (forall pn, In pn (ablocks B (x_ly c) (x_S c)) -> ~ In pn (x_O c) -> In pn (ablocks B ly' S')) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B (x_ly c) (x_S c)) /\ ~ In pn (x_O c)) \/ In pn O' \/ pn = (p, n)) /\
 (forall pn, In pn O' -> In pn (x_O c) \/ ~ In pn (ablocks B (x_ly c) (x_S c))) /\
 blocks_bytes S' <= blocks_bytes (x_S c) + LIVE_CHAIN_WORDS /\
 mo_le MT (x_S c) S' (XM_CHAIN_WORDS MT (x_R c)).
(* the statement's post (FP-existential, apost_baseF), and the post at the FP state the recorder call returned
   (apost_base, proved by the last segment from the join KJ on) *)
Definition cw_post (c : cwx) : world SEGS -> config -> Prop :=
  apost_baseF SEGS B CHAIN_WORDS_STK (cw_FP c) (x_regs c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    (EV_CHAIN_WORDS (x_R c)) (cw_Q c).
Definition cw_postB (c : cwx) : world SEGS -> config -> Prop :=
  apost_base SEGS B CHAIN_WORDS_STK (cw_FP c) (x_regs c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    (EV_CHAIN_WORDS (x_R c)) (cw_Q c).
(* the frame part of every cut: the walk's journal from the entry with the class-3 frame as its own frame, the
   registers the code keeps (sp = s1 = the realigned sp, s0 = sp0, s2 = the frame's shadow, s3 = s8 = the frame),
   the saved registers in their slots, and the frame's flag pointer at frame + 504 (the release reads it) *)
Record cw_fi (c : cwx) (k : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (regs3 : bvmap 5 word)
  (mem3 : word -> option byte) (md3 : Model) : Prop := mkCWFi {
  fi_j : ajournal SEGS B CHAIN_WORDS_STK (cw_sp0 c) (cw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] ly3 S3 W3 mem3 md3 k;
  fi_sp : getr regs3 2 = w64 (cw_s1 c);
  fi_gp : getr regs3 3 = w64 (as_gp B);
  fi_tp : getr regs3 4 = w64 (as_tp B);
  fi_s0 : getr regs3 8 = w64 (cw_sp0 c);
  fi_s1 : getr regs3 9 = w64 (cw_s1 c);
  fi_s2 : getr regs3 18 = w64 (SB + cw_F c / 8);
  fi_s3 : getr regs3 19 = w64 (cw_F c);
  fi_s8 : getr regs3 24 = w64 (cw_F c);
  fi_saved : forall j r, nth_error cw_saved j = Some r ->
    rdword (rdW W3 mem3) (cw_sp0 c - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr (x_regs c) (Z_to_bv 5 r)));
  fi_flag : rdword (rdW W3 mem3) (cw_F c + 504) = Some (cw_FL c) }.
(* the part of every cut before the recorder call: nothing the caller can see has changed (the image outside the
   runtime's own statics and errno, every live block, every side-stack frame of the entry and its shadow), the
   blocks and the meter are those of the entry, no allocator event has happened (the journal's count is 0), and
   the shadow of ids[64] (frame + 32 .. frame + 288) says "usable" *)
Record cw_un (c : cwx) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (mem3 : word -> option byte) : Prop := mkCWUn {
  un_img : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
    rdW W3 mem3 a = rdW (x_W c) (x_mem c) a;
  un_blk : forall p n i, In (p, n) (ablocks B (x_ly c) (x_S c)) -> 0 <= i < req_size n ->
    rdW W3 mem3 (p + i) = rdW (x_W c) (x_mem c) (p + i);
  un_frm : forall cid pos a, In (cid, pos) (frames (x_S c)) ->
    (in_zr a (frame_rng (x_ly c) (cid, pos)) \/ in_zr a (shadow_addr (frame_addr (x_ly c) cid pos), fs_frame_bytes cid / 8)) ->
    rdW W3 mem3 a = rdW (x_W c) (x_mem c) a;
  un_perm : Permutation (ablocks B ly3 S3) (ablocks B (x_ly c) (x_S c));
  un_nev : st_nev S3 <= st_nev (x_S c);
  un_bb : blocks_bytes S3 = blocks_bytes (x_S c);
  un_meter : mo_le MT (x_S c) S3 0;
  un_ids_sh : forall i, 4 <= i < 36 -> rdW W3 mem3 (SB + cw_F c / 8 + i) = Some 0 }.
Definition cw_pc (c : cwx) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (regs3 : bvmap 5 word)
  (mem3 : word -> option byte) (md3 : Model) : Prop :=
  cw_fi c 0 ly3 S3 W3 regs3 mem3 md3 /\ cw_un c ly3 S3 W3 mem3.
(* the cut invariants *)
Definition INV_KC (c : cwx) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  cw_pc c ly3 S3 W3 regs3 mem3 md3 /\
  getr regs3 20 = w64 (x_ntok c) /\ getr regs3 21 = w64 (x_tok c) /\ getr regs3 23 = w64 SB /\
  3 <= x_ntok c.
(* pass j of the loop: s4 = ntok, s5 = &ids[j], s6 = ids, s7 = s9 = &tok[2 + j], s10 = its shadow byte,
   s11 = ntok - 2 - j; id holds tks[1]'s value and ids[0..j) the values of tks[2..2+j) *)
Definition INV_KL (c : cwx) (j : Z) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  cw_pc c ly3 S3 W3 regs3 mem3 md3 /\
  0 <= j < x_ntok c - 2 /\
  getr regs3 20 = w64 (x_ntok c) /\ getr regs3 21 = w64 (cw_F c + 32 + 4 * j) /\
  getr regs3 22 = w64 (cw_F c + 32) /\ getr regs3 23 = w64 (x_tok c + 16 + 8 * j) /\
  getr regs3 25 = w64 (x_tok c + 16 + 8 * j) /\ getr regs3 26 = w64 (SB + (x_tok c + 16 + 8 * j) / 8) /\
  getr regs3 27 = w64 (x_ntok c - 2 - j) /\
  exists id vs, Verbs.number_m (nth 1 (x_tks c) []) = Some id /\
    Verbs.numbers_m (firstn (Z.to_nat j) (skipn 2 (x_tks c))) = Some vs /\
    aval_mem (rdW W3 mem3) (cw_s1 c + 20) 4 id /\
    abytes_atR (rdW W3 mem3) (cw_F c + 32) (concat (map le32 vs)).
Definition INV_KD (c : cwx) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  cw_pc c ly3 S3 W3 regs3 mem3 md3 /\
  getr regs3 20 = w64 (x_ntok c) /\ getr regs3 22 = w64 (cw_F c + 32) /\ 3 <= x_ntok c /\
  exists id vs, Verbs.number_m (nth 1 (x_tks c) []) = Some id /\
    Verbs.numbers_m (skipn 2 (x_tks c)) = Some vs /\
    aval_mem (rdW W3 mem3) (cw_s1 c + 20) 4 id /\
    abytes_atR (rdW W3 mem3) (cw_F c + 32) (concat (map le32 vs)).
Definition INV_KR (c : cwx) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  cw_pc c ly3 S3 W3 regs3 mem3 md3 /\
  VerbsRun.chain_run (x_R c) (tl (x_tks c)) = sup_resp_m (x_R c) Verbs.err_invalid_operation.
Definition INV_KJ (c : cwx) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  exists k, 0 <= k <= EV_CHAIN_WORDS (x_R c) /\
  cw_fi c k ly3 S3 W3 regs3 mem3 md3 /\ cw_Q c ly3 S3 W3 regs3 mem3 md3.
(* "from this cut point the walk reaches the post": before the recorder call, the statement's post at the current
   FP state; from the join KJ on, apost_base at the current FP state (no FP change follows) *)
Definition cw_from (pc : Z) (INV : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (c : cwx) : Prop :=
  forall ly3 S3 W3 regs3 mem3 md3, INV ly3 S3 W3 regs3 mem3 md3 ->
  SRr SEGS W3 (cfg_at SEGS (BASE + pc) regs3 mem3 md3) (cw_post c).
Definition from_KC (c : cwx) : Prop := cw_from CW_KC (INV_KC c) c.
Definition from_KL (c : cwx) (j : Z) : Prop := cw_from CW_KL (INV_KL c j) c.
Definition from_KD (c : cwx) : Prop := cw_from CW_KD (INV_KD c) c.
Definition from_KR (c : cwx) : Prop := cw_from CW_KR (INV_KR c) c.
Definition from_KJ (c : cwx) : Prop :=
  forall ly3 S3 W3 regs3 mem3 md3, INV_KJ c ly3 S3 W3 regs3 mem3 md3 ->
  SRr SEGS W3 (cfg_at SEGS (BASE + CW_KJ) regs3 mem3 md3) (cw_postB c).
Lemma cw_pre_setpos : forall c f, cw_pre c -> cw_pre (cw_setpos c f).
Proof. intros c f H. destruct H. constructor; assumption. Qed.
Lemma cw_post_setpos : forall c f, cw_post (cw_setpos c f) = cw_post c.
Proof. reflexivity. Qed.
(* the named per-binary facts the walk takes (cgif's and CmdRecFacts' names): the read-only range lies in the image
   (CmdRecRo.v relro_img); g_rec / record.spill / g_quitting are image bytes outside the runtime's statics and errno
   (cmd_prog_unowned, CmdRecFacts group (c)); at every state, cmd_ro_ok follows from arodata_okP (CmdRecRo.v
   cmd_ro_ok_of_aro: the program's literals and their tails are unowned read-only bytes) *)
Definition cw_ro_imgP : Prop := forall a, RLO <= a < RHI -> in_img SEGS a.
Definition cw_prog_unownedP : Prop := forall a, inFP cmd_PG a ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Definition cw_ro_of_rodP : Prop := forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
(* the call targets of the three program callees, from the kit's cmd_sig_prog (CmdObj.v; the walk hypothesis SIGP) *)
Lemma cw_sig_of : cmd_sig_prog ->
  SIGMA CS_number = BASE + AF_number /\ SIGMA CS_sup_chain = BASE + AF_sup_chain /\ SIGMA CS_sup_resp = BASE + AF_sup_resp.
Proof.
intros H.
assert (H1 : In CS_number cmd_prog_syms) by (cbv [cmd_prog_syms In]; tauto).
assert (H2 : In CS_sup_chain cmd_prog_syms) by (cbv [cmd_prog_syms In]; tauto).
assert (H3 : In CS_sup_resp cmd_prog_syms) by (cbv [cmd_prog_syms In]; tauto).
rewrite (H _ H1), (H _ H2), (H _ H3).
split; [|split]; f_equal; vm_compute; reflexivity.
Qed.
(* the caller's objects at a cut before the recorder call, as the callee statements ask for them: the token array
   and its words (number takes each word in its block, number_c.v:89; sup_chain takes the member array), the
   recorder and the read-only bytes *)
Definition cw_caller (c : cwx) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
  afobj SEGS B ly3 S3 W3 mem3 (x_tok c) (8 * x_ntok c) /\
  atoks_atA (rdW W3 mem3) (x_tok c) (x_ptrs c) (x_tks c) (x_cb c) (x_ncb c) /\
  In (x_cb c, x_ncb c) (ablocks B ly3 S3) /\
  rec_repA B ly3 S3 (rdW W3 mem3) (x_R c) (x_O c) /\
  arodata_okP SEGS RLO RHI B (rdW W3 mem3) /\
  cmd_ro_ok (rdW W3 mem3).
(* carrying them from the entry to a cut (proved in chain_words_j.v) *)
Definition cw_transportP : Prop :=
  forall c k ly3 S3 W3 regs3 mem3 md3, cw_pre c -> cw_fi c k ly3 S3 W3 regs3 mem3 md3 -> cw_un c ly3 S3 W3 mem3 ->
  cw_caller c ly3 S3 W3 mem3.
End e.
End f.
End d.
(* the segments of the walk (one file each); chain_words_a.v chains them. Each is a lemma of a closed section, so it
   holds at every ambient FP state fx. The recorder calls (S4: sup_chain, S5: sup_resp) return at some fx1 with
   fxrel fx fx1: they take the join at every FP state, and rounding mode 0 at fx (the callees' premise). *)
Section sp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Variables RLO RHI : Z.
Definition cw_S1P : Prop := forall c, cw_pre B MT RLO RHI c ->
  (forall f, from_KR B MT (cw_setpos c f)) -> (forall f, from_KC B MT (cw_setpos c f)) ->
  SRr SEGS (x_W c) (cfg_at SEGS (BASE + AF_chain_words) (x_regs c) (x_mem c) (x_md c)) (cw_post B MT c).
Definition cw_S2P : Prop := forall c, cw_pre B MT RLO RHI c -> from_KR B MT c -> from_KL B MT c 0 -> from_KC B MT c.
Definition cw_S3P : Prop := forall c j, cw_pre B MT RLO RHI c -> from_KR B MT c -> from_KD B MT c ->
  from_KL B MT c (j + 1) -> from_KL B MT c j.
Definition cw_S4P : Prop := forall c, frm0 fx -> cw_pre B MT RLO RHI c ->
  (forall fx0 : YK11.FPState, from_KJ (fx := fx0) B MT c) -> from_KD B MT c.
Definition cw_S5P : Prop := forall c, frm0 fx -> cw_pre B MT RLO RHI c ->
  (forall fx0 : YK11.FPState, from_KJ (fx := fx0) B MT c) -> from_KR B MT c.
Definition cw_S6P : Prop := forall c, cw_pre B MT RLO RHI c -> from_KJ B MT c.
End sp.
