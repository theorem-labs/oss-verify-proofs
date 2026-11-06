(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the shared vocabulary of the walk of chain_words (0x8da84, 298 instructions)
   on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan), the B twin of
   lib/A/Prog/chain_words_d.v (the A walk is a working branch 5e2cdad423e). Same shape as A's: the
   context record, the entry facts, the post and the "from a cut point" predicates, with the cut points over the
   machine state (each segment file builds its own symbolic state).

   What B changes against A (measured; recorded in section chain_words of a Theorem Labs lane's B-PREP.md, not in this tree):
   - the real frame is 160 bytes (A 128), so the realigned frame pointer s1 is sp0 - 160 or sp0 - 176;
   - the registers: s8 (x24) holds the shadow base SB (A: s7), s6 (x22) holds the class-3 frame F (A: s8), and the
     member loop re-uses s3 (x19, the 65 counter) and s6 (x22, ids = F + 32), so F and the frame flag live in the
     realigned-frame slots s1 + 8 and s1 + 16 over the loop (A kept them in registers throughout);
   - ntok lives in the realigned-frame slot s1 + 24 (A: s4) and number's out cell at s1 + 52 (A: s1 + 20);
   - UBSan adds 5 trap checks inside the parse of tok[1] and the member loop (B +0x214..+0x2f8), and the whole
     region is re-laid, so that region is a new walk;
   - the post is apost_baseF (the printf wrappers' FP-existential post), so the two recorder callees return at
     SOME FP state related to the entry's by cw_fxr; the join KJ is reached at such a state.
   The cut points (offsets from chain_words' entry 0x8da84):
     KC  0x21c (0x8dca0)  the frame is set up and ntok >= 3; the spills of F and the flag are next
     KL  0x278 (0x8dcfc)  the head of the member loop, pass j
     KD  0x2c0 (0x8dd44)  every word parsed; the sup_chain call is next
     KR1 0x2d8 (0x8dd5c)  the refusal with F in s3 / s6: sup_resp(-902) is next, then the jump to KJ
     KR2 0x2e8 (0x8dd6c)  the refusal inside the loop (F in the frame slots): sup_resp(-902) is next
     KJ  0x2fc (0x8dd80)  the join after the recorder call; the release of the frame is next
   The program calls compose through cl_callS_wide (lib/B/Prog/PaNoChain.v, over a Theorem Labs lane's ajournal_sub_wide,
   YCbq.v) for number (apost_base), and through the same rule in its FP-existential form for sup_chain and
   sup_resp (apost_baseF): number writes id in the caller's stack window and ids[j] in the caller's own frame,
   sup_chain writes g_rec and record.spill, all of them awr_byte bytes of chain_words' journal. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaSB PaCall PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import number_c sup_chain_c sup_resp_c chain_words_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(* the cut points, as offsets from the listing's start (BASE + CW_K* is the address) *)
Definition CW_KC : Z := AF_chain_words + 0x21c.
Definition CW_KL : Z := AF_chain_words + 0x278.
Definition CW_KD : Z := AF_chain_words + 0x2c0.
Definition CW_KR1 : Z := AF_chain_words + 0x2d8.
Definition CW_KR2 : Z := AF_chain_words + 0x2e8.
Definition CW_KJ : Z := AF_chain_words + 0x2fc.
(* the registers the prologue saves, in the order of their slots: slot j at sp0 - 8 - 8 j (ra at 152(sp), s0 at
   144(sp), ..., s11 at 56(sp), with sp = sp0 - 160) *)
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
(* the entry stack pointer, the realigned one (andi sp,sp,-32 at 0x8dac4 after addi sp,sp,-160; it is sp0 - 160 or
   sp0 - 176), the frame and its flag *)
Definition cw_sp0 (c : cwx) : Z := spZ (x_regs c).
Definition cw_s1 (c : cwx) : Z := (cw_sp0 c - 160) - (cw_sp0 c - 160) mod 32.
Definition cw_F (c : cwx) : Z := frame_addr (x_ly c) 3 (x_fpos c).
Definition cw_FL (c : cwx) : Z := flag_addr (x_ly c) 3 (x_fpos c).
Lemma cw_s1_facts : forall c, cw_sp0 c mod 16 = 0 ->
  cw_s1 c mod 32 = 0 /\ (cw_s1 c = cw_sp0 c - 160 \/ cw_s1 c = cw_sp0 c - 176).
Proof.
intros c H. unfold cw_s1. pose proof (Z.mod_pos_bound (cw_sp0 c - 160) 32 ltac:(lia)) as M.
assert (Hm : (cw_sp0 c - 160) mod 32 = 0 \/ (cw_sp0 c - 160) mod 32 = 16).
{ pose proof (Z.div_mod (cw_sp0 c - 160) 32 ltac:(lia)) as D. pose proof (Z.div_mod (cw_sp0 c) 16 ltac:(lia)) as D2.
  rewrite H in D2. lia. }
split; [|lia].
replace ((cw_sp0 c - 160) - (cw_sp0 c - 160) mod 32) with (32 * ((cw_sp0 c - 160) / 32))
  by (pose proof (Z.div_mod (cw_sp0 c - 160) 32 ltac:(lia)); lia).
rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
(* The rounding mode and the FP relation are the kit's (lib/B/Prog/PaFx.v, the B twin of A/Prog/PaFx.v):
   `frm0 fx` is the statement's pre (chain_words_c.v:123) and `fxrel fx fq` is apost_baseF's pair of FP clauses.
   fxrel_refl / fxrel_trans / fxrel_frm0 / apost_baseF_lift / srr_after_callF are the kit's lemmas; the two
   recorder calls (S4, S5) use cl_callS_wideF and srr_after_callF. *)
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Definition cw_FP (c : cwx) : list (Z * Z) := CHAIN_WORDS_PG ++ ablocks_fp (x_O c).
(* tchain_words_spec's premises over the context (chain_words_c.v:119-145), except the rounding mode (`frm0 fx`,
   which only the two recorder calls take): this record carries no FP state, so a segment proved over it holds at
   every FP state the walk reaches. Pass 5 (a working branch f490061c104) removed the statement's astack_pres, so it
   is not a field: a callee's frame chain comes from afn_pre's own chain (PASS4-REFIT.md section B, class B:
   achain_push with the ra and entry-s0 words the prologue stored at sp0 - 8 and sp0 - 16). *)
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
(* what the walk gives at the return: tchain_words_spec's post (chain_words_c.v:147-166) with the returned block's
   size exact, n = |x| + 1, as both recorder callees return it (sup_chain_c.v, sup_resp_c.v); r is the register
   that holds the text pointer (a0 at the return, s4 from the recorder call to the epilogue's `mv a0,s4`) *)
Definition cw_Qr (r : bv 5) (c : cwx)
  : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' =>
 let '(R', x) := VerbsRun.chain_run (x_R c) (tl (x_tks c)) in
 exists (O' : list (Z * Z)) (p n : Z),
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 getr regs' r = w64 p /\ 4096 <= p < 2 ^ 64 /\ In (p, n) (ablocks B ly' S') /\ ~ In (p, n) O' /\
 (In (p, n) (ablocks B (x_ly c) (x_S c)) -> In (p, n) (x_O c)) /\
 astr_atR (rdW W' mem') p x /\ n = Z.of_nat (length x) + 1 /\
 (forall pn, In pn (ablocks B (x_ly c) (x_S c)) -> ~ In pn (x_O c) -> iv_apart (fst pn) (snd pn) p n) /\
 (forall pn, In pn (ablocks B (x_ly c) (x_S c)) -> ~ In pn (x_O c) -> In pn (ablocks B ly' S')) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B (x_ly c) (x_S c)) /\ ~ In pn (x_O c)) \/ In pn O' \/ pn = (p, n)) /\
 (forall pn, In pn O' -> In pn (x_O c) \/ ~ In pn (ablocks B (x_ly c) (x_S c))) /\
 blocks_bytes S' <= blocks_bytes (x_S c) + LIVE_CHAIN_WORDS /\
 mo_le MT (x_S c) S' (XM_CHAIN_WORDS MT (x_R c)).
(* at the return the text is in a0 (10); from the recorder call to the epilogue it is in s4 (20) *)
Definition cw_Q (c : cwx) := cw_Qr 10 c.
Definition cw_QJ (c : cwx) := cw_Qr 20 c.
Definition cw_post (c : cwx) : world SEGS -> config -> Prop :=
  apost_baseF SEGS B CHAIN_WORDS_STK (cw_FP c) (x_regs c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    (EV_CHAIN_WORDS (x_R c)) (cw_Q c).
(* the frame part of every cut: the walk's journal from the entry with the class-3 frame as its own frame, the
   registers the code keeps from the prologue to the epilogue (sp = s1 = the realigned sp, s0 = sp0,
   s2 = the frame's shadow base, s8 = SB), ntok in its slot, the saved registers in their slots, and the frame's
   flag pointer at frame + 504 (the release reads it). F itself is NOT here: the member loop re-uses s3 and s6 *)
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
  fi_s8 : getr regs3 24 = w64 SB;
  fi_ntok : rdword (rdW W3 mem3) (cw_s1 c + 24) = Some (x_ntok c);
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
(* F in the frame slots s1 + 8 (sd s6,8(s1) at 0x8dca0) and s1 + 16 (sd s3,16(s1) at 0x8dca4): the loop needs s3
   and s6, and the release reloads them *)
Definition cw_spills (c : cwx) (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
  rdword (rdW W3 mem3) (cw_s1 c + 8) = Some (cw_F c) /\ rdword (rdW W3 mem3) (cw_s1 c + 16) = Some (cw_F c).
(* the cut invariants *)
Definition INV_KC (c : cwx) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  cw_pc c ly3 S3 W3 regs3 mem3 md3 /\
  getr regs3 10 = w64 (2 ^ 64 - 8) /\ getr regs3 11 = w64 3 /\
  getr regs3 19 = w64 (cw_F c) /\ getr regs3 21 = w64 (x_tok c) /\ getr regs3 22 = w64 (cw_F c) /\
  3 <= x_ntok c.
(* pass j of the loop: s3 = 65 - j, s4 = ~ids, s5 = tok, s6 = ids = F + 32, s7 = 67, s9 = 4 j,
   s10 = ~tok, s11 = 16 + 8 j; id holds tks[1]'s value and ids[0..j) the values of tks[2..2+j) *)
Definition INV_KL (c : cwx) (j : Z) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  cw_pc c ly3 S3 W3 regs3 mem3 md3 /\ cw_spills c W3 mem3 /\
  0 <= j < x_ntok c - 2 /\
  getr regs3 19 = w64 (65 - j) /\ getr regs3 20 = w64 (2 ^ 64 - 1 - (cw_F c + 32)) /\
  getr regs3 21 = w64 (x_tok c) /\ getr regs3 22 = w64 (cw_F c + 32) /\ getr regs3 23 = w64 67 /\
  getr regs3 25 = w64 (4 * j) /\ getr regs3 26 = w64 (2 ^ 64 - 1 - x_tok c) /\ getr regs3 27 = w64 (16 + 8 * j) /\
  exists id vs, Verbs.number_m (nth 1 (x_tks c) []) = Some id /\
    Verbs.numbers_m (firstn (Z.to_nat j) (skipn 2 (x_tks c))) = Some vs /\
    aval_mem (rdW W3 mem3) (cw_s1 c + 52) 4 id /\
    abytes_atR (rdW W3 mem3) (cw_F c + 32) (concat (map le32 vs)).
Definition INV_KD (c : cwx) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  cw_pc c ly3 S3 W3 regs3 mem3 md3 /\ cw_spills c W3 mem3 /\
  getr regs3 22 = w64 (cw_F c + 32) /\ 3 <= x_ntok c /\
  exists id vs, Verbs.number_m (nth 1 (x_tks c) []) = Some id /\
    Verbs.numbers_m (skipn 2 (x_tks c)) = Some vs /\
    aval_mem (rdW W3 mem3) (cw_s1 c + 52) 4 id /\
    abytes_atR (rdW W3 mem3) (cw_F c + 32) (concat (map le32 vs)).
(* the refusal before the loop (0x8dd5c): F is still in s3 and s6, so the join needs no reload *)
Definition INV_KR1 (c : cwx) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  cw_pc c ly3 S3 W3 regs3 mem3 md3 /\
  getr regs3 19 = w64 (cw_F c) /\ getr regs3 22 = w64 (cw_F c) /\
  VerbsRun.chain_run (x_R c) (tl (x_tks c)) = sup_resp_m (x_R c) Verbs.err_invalid_operation.
(* the refusal inside the loop (0x8dd6c): F is in the frame slots, which the join reloads *)
Definition INV_KR2 (c : cwx) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  cw_pc c ly3 S3 W3 regs3 mem3 md3 /\ cw_spills c W3 mem3 /\
  VerbsRun.chain_run (x_R c) (tl (x_tks c)) = sup_resp_m (x_R c) Verbs.err_invalid_operation.
(* the join (0x8dd80): the recorder call is done, F is back in s3 and s6 and the text in s4 *)
Definition INV_KJ (c : cwx) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  exists k, 0 <= k <= EV_CHAIN_WORDS (x_R c) /\
  cw_fi c k ly3 S3 W3 regs3 mem3 md3 /\
  getr regs3 19 = w64 (cw_F c) /\ getr regs3 22 = w64 (cw_F c) /\
  cw_QJ c ly3 S3 W3 regs3 mem3 md3.
(* "from this cut point the walk reaches the post" *)
Definition cw_from (pc : Z) (INV : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (c : cwx) : Prop :=
  forall ly3 S3 W3 regs3 mem3 md3, INV ly3 S3 W3 regs3 mem3 md3 ->
  SRr SEGS W3 (cfg_at SEGS (BASE + pc) regs3 mem3 md3) (cw_post c).
Definition from_KC (c : cwx) : Prop := cw_from CW_KC (INV_KC c) c.
Definition from_KL (c : cwx) (j : Z) : Prop := cw_from CW_KL (INV_KL c j) c.
Definition from_KD (c : cwx) : Prop := cw_from CW_KD (INV_KD c) c.
Definition from_KR1 (c : cwx) : Prop := cw_from CW_KR1 (INV_KR1 c) c.
Definition from_KR2 (c : cwx) : Prop := cw_from CW_KR2 (INV_KR2 c) c.
Definition from_KJ (c : cwx) : Prop := cw_from CW_KJ (INV_KJ c) c.
Lemma cw_pre_setpos : forall c f, cw_pre c -> cw_pre (cw_setpos c f).
Proof. intros c f H. destruct H. constructor; assumption. Qed.
Lemma cw_post_setpos : forall c f, cw_post (cw_setpos c f) = cw_post c.
Proof. reflexivity. Qed.
(* the named per-binary facts the walk takes (a Theorem Labs lane's RULING-STMT.md section 1-2): the read-only range lies in the
   image (CmdRecRo.v relro_img); g_rec / record.spill / g_quitting are image bytes outside the runtime's statics
   and errno (cmd_prog_unowned, CmdRecImg.v); at every state, cmd_ro_ok follows from arodata_okP (CmdRecRo.v
   cmd_ro_ok_of_aro) *)
Definition cw_ro_imgP : Prop := forall a, RLO <= a < RHI -> in_img SEGS a.
Definition cw_prog_unownedP : Prop := forall a, inFP cmd_PG a ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Definition cw_ro_of_rodP : Prop := forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
(* the call targets of the three program callees, from the kit's cmd_sig_prog (CmdObj.v) *)
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
(* the caller's objects at a cut before a call, as the callee statements ask for them: the token array and its
   words (number takes each word in its block, number_c.v; sup_chain takes the member array), the recorder and
   the read-only bytes. Pass 5 dropped the callees' astack_pres, so it is not here either. *)
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
(* the segments that make no call to a printf-reaching callee: they stay at the FP state they start from, so each
   is stated at the section's fx and instantiated at whatever FP state the walk has reached *)
Definition cw_S1P : Prop := forall c, cw_pre c ->
  (forall f, from_KR1 (cw_setpos c f)) -> (forall f, from_KC (cw_setpos c f)) ->
  SRr SEGS (x_W c) (cfg_at SEGS (BASE + AF_chain_words) (x_regs c) (x_mem c) (x_md c)) (cw_post c).
Definition cw_S2P : Prop := forall c, cw_pre c -> from_KR1 c -> from_KL c 0 -> from_KC c.
Definition cw_S3P : Prop := forall c j, cw_pre c -> from_KR2 c -> from_KD c -> from_KL c (j + 1) -> from_KL c j.
Definition cw_S6P : Prop := forall c, cw_pre c -> from_KJ c.
End e.
End f.
End d.
(* ---------------------------------------------------------------------------------------------------------------
   The two segments that call a printf-reaching callee (sup_chain, sup_resp: their post is apost_baseF). They end
   at the join KJ at SOME FP state related to theirs by the kit's fxrel (PaFx.v), so they take the join segment at
   every such state (from_KJq) and give back the post at their own, through the kit's srr_after_callF. *)
Section d2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f2.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
Section e2.
Variable B : asyms.
Variable MT : ameter_ops.
(* the join, at every FP state the recorder call may return at *)
Definition from_KJq (c : cwx) : Prop := forall fq : YK11.FPState, fxrel fx fq -> from_KJ (fx := fq) B MT c.
Definition cw_S4P : Prop := forall c, cw_pre B MT c -> frm0 fx -> from_KJq c -> from_KD B MT c.
Definition cw_S5P : Prop := forall c, cw_pre B MT c -> frm0 fx -> from_KJq c ->
  from_KR1 B MT c /\ from_KR2 B MT c.
End e2.
End f2.
End d2.
