(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: sup_chain's ASan walk, assembled.  The four segments are
   lib/A/Prog/sup_chain.v (`sc_segA`, the entry 0x8c2b4 to the join 0x8c34c, record()'s two arms),
   lib/A/Prog/sup_chain_s4.v (`sc_segB`, the join to the loop test 0x8c3c4: the list text's malloc and the two
   arg_i calls), lib/A/Prog/sup_chain_s5.v (`sc_loop`, 0x8c3c4 to 0x8c438: one sprintf per member) and
   lib/A/Prog/sup_chain_s6.v (`sc_segC`, 0x8c438 to the tail jump `j answer` at 0x8c4e4 and the post).
   This file carries the facts from one to the next (lib/A/Prog/sup_chain_s7.v) and proves the contract
   lib/A/Prog/sup_chain_c.v's `tsup_chain_spec`. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaSB PaArt
PaLibF PaLibG PaLibH PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr CmdZsh CmdRecBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c arg_i_c xstrdup_c rec_shape_of_c hand_back_c answer_c sup_chain_c RecBLemmas
sup_chain_s1 sup_chain_s2 sup_chain_s3 sup_chain sup_chain_s4 sup_chain_s5 sup_chain_s6 sup_chain_s7.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
(* the per-binary record and the meter laws *)
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis SIGP : cmd_sig_prog.
(* the program's writable statics (the recorder walks' shared form) *)
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
(* the read-only image: arodata_ok_journalP's two facts, the read-only bytes outside the program's statics,
   cmd_ro_ok from arodata, and the read-only membership the record's string checks ask of a literal *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a ->
in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis CMD_RO_IN : cmd_ro_in (in_roP SEGS RLO RHI).
(* the cells the musl bodies under the sprintf and snprintf wrappers read, and a live block's rounded tail *)
Hypothesis cmd_rec_cells : forall ly S W mem md, AR SEGS B ly S W mem md ->
rdW W mem A_FLAG_REPLACE_STR = Some 1 /\ aguard_ok SEGS W mem 0xa7098 0x6045d8 /\
exists ev, rd32 (rdW W mem) (as_errno B) ev.
Hypothesis cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e.
(* the two format literals the sprintf wrapper reads: " %d" (0x21ee0, 4 bytes) and "%d" (0x21f00, 3).  They are
   not in the record's zero-shadow table, so their shadow comes from the const cells
   (the recorder walks' shared form for literals); the verb "chain" (0x21f20) goes through astr_argA's read-only arm,
   decided on the record's lists *)
Hypothesis ZSH_lit_21ee0 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
range_addressable (rdW W mem) SHADOW_OFF 0x21ee0 4.
Hypothesis ZSH_lit_21f00 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
range_addressable (rdW W mem) SHADOW_OFF 0x21f00 3.
Hypothesis HULL_lit_21ee0 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
shadow_hull_vis (rdW W mem) 0x21ee0 4.
Hypothesis HULL_lit_21f00 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
shadow_hull_vis (rdW W mem) 0x21f00 3.
(* the image facts the shared sprintf contract's read-only ranges come from (CmdRecImg.v cmd_consts_view_sp) *)
Hypothesis IMG : cmd_img_facts SEGS B.
(* the statement's own hypotheses (sup_chain_c.v:80-87), at every FP state *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TARG_I : forall fx0 : YK11.FPState, @targ_i_spec fx0 rc SK PI B MT.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis ASPRINTF : forall fx0 : YK11.FPState,
  @asprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_sprintf) 0xa7098 0x6045d8.

(* the meter of each piece is non-negative, so each segment's share is below the whole *)
Lemma sc8_xm_parts : forall (R : rstate) (id : Z) (ids : list Z),
(1 <= length ids <= 62)%nat -> Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) ids ->
0 <= rec_spill_frees R * mo_free MT /\
0 <= mo_malloc MT (12 * Z.of_nat (length ids) + 1) /\
0 <= XM_ARG_I MT id /\ 0 <= XM_ARG_I MT (Z.of_nat (length ids)) /\
0 <= XM_XSTRDUP MT (dec_list ids) /\ 0 <= mo_free MT /\
0 <= XM_ANSWER MT (snd (sup_chain_m R id ids)).
Proof.
intros R id ids Hn HF.
pose proof (mo_free_nonneg MT MTL) as Hf.
assert (Hsp : 0 <= rec_spill_frees R)
  by (unfold rec_spill_frees; destruct (Nat.ltb (length (r_calls R)) 16); [lia | apply Zle_0_nat]).
split; [apply Z.mul_nonneg_nonneg; lia|].
split; [apply (mo_malloc_nonneg MT MTL); lia|].
split; [unfold XM_ARG_I, XM_XSTRDUP; apply (mo_malloc_nonneg MT MTL); lia|].
split; [unfold XM_ARG_I, XM_XSTRDUP; apply (mo_malloc_nonneg MT MTL); lia|].
split; [unfold XM_XSTRDUP; apply (mo_malloc_nonneg MT MTL); lia|].
split; [lia|].
unfold XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP.
pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (snd (sup_chain_m R id ids))) + 1) ltac:(lia)). lia.
Qed.

(* the text block's bytes are bytes this walk may write: either the block is new in this call, or record()'s
   spill arm freed one of the recorder's blocks and the malloc handed its address back *)
Lemma sc8_wr_text : forall STK sp0 O ly SE lyL SL own lst m a,
In (lst, m) (ablocks B lyL SL) ->
(~ In (lst, m) (ablocks B ly SE) \/ In (lst, m) O) ->
0 <= m -> lst <= a < lst + m ->
awr_byte SEGS B STK sp0 (sc_FP O) (ablocks B ly SE) (ablocks B lyL SL) (frames SE) lyL own a.
Proof.
intros STK sp0 O ly SE lyL SL own lst m a Hin Hcase Hm Ha.
pose proof (req_size_pos m Hm) as [_ Hrq].
destruct Hcase as [Hfresh | HO].
- right. right. left. exists lst, m. split; [exact Hin|]. split; [exact Hfresh | lia].
- right. left. split.
  + exists (lst, lst + req_size m). split; [| cbn [fst snd]; lia].
    right. right. unfold ablocks_fp.
    exact (in_map (fun b : Z * Z => (fst b, fst b + req_size (snd b))) O (lst, m) HO).
  + exists lst, m. split; [exact Hin | lia].
Qed.

Lemma sc8_pair_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. intros x y. decide equality; apply Z.eq_dec. Qed.

(* What the tail segment asks about the blocks, from what the join and the join-to-loop segment say.  The
   state at the loop is the join's blocks with the two recorded numbers and the list text added; the join
   freed only blocks the recorder owned (record()'s spill arm), so every other block of the entry is still
   there, and a block of the entry that is gone was one of the recorder's. *)
Lemma sc8_lineage : forall ly S lyc Sc ly' S' (W' : world SEGS) mem' md' O O1 (p1 p2 lstb : Z * Z),
AR SEGS B ly' S' W' mem' md' ->
Permutation (ablocks B ly' S') (p2 :: p1 :: ablocks B lyc Sc ++ [lstb]) ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
(forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly S)) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
(forall pn, In pn O1 -> In pn O) ->
(forall pn, In pn O1 -> In pn (ablocks B lyc Sc)) ->
(forall pn, In pn O -> In pn (ablocks B lyc Sc) -> In pn O1) ->
In lstb (ablocks B ly' S') /\
~ In lstb (O1 ++ [p1; p2]) /\
(~ In lstb (ablocks B ly S) \/ In lstb O) /\
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
(forall pn, In pn (ablocks B ly' S') -> In pn (ablocks B ly S) \/ In pn (O1 ++ [p1; p2]) \/ pn = lstb) /\
(forall pn, In pn (O1 ++ [p1; p2]) -> In pn O \/ ~ In pn (ablocks B ly S)) /\
(forall pn, In pn O -> In pn (ablocks B ly' S') -> In pn (O1 ++ [p1; p2]) \/ pn = lstb) /\
(In lstb (ablocks B ly S) -> In lstb O).
Proof.
intros ly S lyc Sc ly' S' W' mem' md' O O1 p1 p2 lstb HAR' HP HOlive HJ1 HJ2 HO1O HO1c HOO1.
destruct (sc7_perm_apart B ly' S' W' mem' md' p2 p1 lstb (ablocks B lyc Sc) HAR' HP)
  as (Hp2L & Hp1L & HlL & Hp21 & Hp2l & Hp1l).
assert (HPin : forall pn, In pn (p2 :: p1 :: ablocks B lyc Sc ++ [lstb]) -> In pn (ablocks B ly' S'))
  by (intros pn Hpn; apply (Permutation_in pn (Permutation_sym HP)); exact Hpn).
(* a block that is live at the entry and gone at the join was one the recorder owned *)
assert (GONE : forall pn, In pn (ablocks B ly S) -> ~ In pn (ablocks B lyc Sc) -> In pn O).
{ intros pn Hpn Hnc. destruct (in_dec sc8_pair_dec pn O) as [Hy | Hn]; [exact Hy|].
  exfalso. exact (Hnc (HJ2 pn Hpn Hn)). }
assert (HlstIn : In lstb (ablocks B ly' S'))
  by (apply HPin; right; right; apply in_or_app; right; left; reflexivity).
assert (HlstO1 : ~ In lstb (O1 ++ [p1; p2])).
{ intros Hin. apply in_app_or in Hin as [Hin | Hin].
  - exact (HlL (HO1c lstb Hin)).
  - destruct Hin as [<- | [<- | []]]; [exact (Hp1l eq_refl) | exact (Hp2l eq_refl)]. }
assert (HlstCase : ~ In lstb (ablocks B ly S) \/ In lstb O).
{ destruct (in_dec sc8_pair_dec lstb O) as [Hy | Hn]; [right; exact Hy|].
  left. intros Hin. exact (HlL (HJ2 lstb Hin Hn)). }
(* the two recorded numbers are blocks the call made, or addresses the spill arm's frees gave back *)
assert (NEW : forall x, (x = p1 \/ x = p2) -> In x O \/ ~ In x (ablocks B ly S)).
{ intros x Hx. destruct (in_dec sc8_pair_dec x (ablocks B ly S)) as [Hy | Hn]; [| right; exact Hn].
  left. apply (GONE x Hy). destruct Hx as [-> | ->]; [exact Hp1L | exact Hp2L]. }
split; [exact HlstIn|]. split; [exact HlstO1|]. split; [exact HlstCase|].
split; [intros pn Hpn Hno; apply HPin; right; right; apply in_or_app; left; exact (HJ2 pn Hpn Hno)|].
split.
{ intros pn Hpn. pose proof (Permutation_in pn HP Hpn) as Hc.
  destruct Hc as [<- | [<- | Hc]].
  - right. left. apply in_or_app. right. right. left. reflexivity.
  - right. left. apply in_or_app. right. left. reflexivity.
  - apply in_app_or in Hc as [Hc | Hc]; [left; exact (HJ1 pn Hc)|].
    destruct Hc as [<- | []]. right. right. reflexivity. }
split.
{ intros pn Hpn. apply in_app_or in Hpn as [Hpn | Hpn].
  - left. exact (HO1O pn Hpn).
  - destruct Hpn as [<- | [<- | []]]; [exact (NEW p1 (or_introl eq_refl)) | exact (NEW p2 (or_intror eq_refl))]. }
split.
{ intros pn HpO Hpn. pose proof (Permutation_in pn HP Hpn) as Hc.
  destruct Hc as [<- | [<- | Hc]].
  - left. apply in_or_app. right. right. left. reflexivity.
  - left. apply in_or_app. right. left. reflexivity.
  - apply in_app_or in Hc as [Hc | Hc].
    + left. apply in_or_app. left. exact (HOO1 pn HpO Hc).
    + destruct Hc as [<- | []]. right. reflexivity. }
intros Hin. destruct HlstCase as [Hno | Hy]; [exfalso; exact (Hno Hin) | exact Hy].
Qed.

(* the member array is apart from the list text: both lie in the record's separated objects *)
Lemma sc8_apart_of_loc : forall ly' S' (W' : world SEGS) mem' md' pids nids lst m,
AR SEGS B ly' S' W' mem' md' ->
((exists cid pos, In (cid, pos) (frames S') /\ frame_addr ly' cid pos <= pids /\
    pids + nids <= frame_addr ly' cid pos + fs_frame_bytes cid) \/
 (exists pb nb, In (pb, nb) (ablocks B ly' S') /\ (pb, nb) <> (lst, m) /\
    pb <= pids /\ pids + nids <= pb + nb)) ->
In (lst, m) (ablocks B ly' S') -> 0 <= m ->
iv_apart pids nids lst m.
Proof.
intros ly' S' W' mem' md' pids nids lst m HAR Hloc Hlin Hm.
pose proof (req_size_pos m Hm) as [_ Hrm].
destruct Hloc as [(cid & pos & Hfin & Hlo & Hhi) | (pb & nb & Hbin & Hne & Hlo & Hhi)].
- pose proof (sep_block_frame SEGS B LAWS ly' S' W' mem' md' lst m cid pos HAR Hlin Hfin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold iv_apart. lia.
- destruct (al_blocks _ _ LAWS ly' S' W' mem' md' pb nb HAR Hbin) as (_ & _ & _ & _ & _ & _ & Hnb).
  pose proof (req_size_pos nb ltac:(lia)) as [_ Hrb].
  pose proof (sep_blocks SEGS B LAWS ly' S' W' mem' md' pb nb lst m HAR Hbin Hlin Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold iv_apart. lia.
Qed.

(* the loop writes only the list text and its own stack window, so the recorder's representation is the one
   the segment before it left: g_rec, record.spill and the recorder's blocks are apart from both *)
Lemma sc8_repA_loop : forall ly' S' (W' : world SEGS) mem' md' mem2 R1 O1C lst m sp0 STK,
AR SEGS B ly' S' W' mem' md' ->
rec_repA B ly' S' (rdW W' mem') R1 O1C ->
In (lst, m) (ablocks B ly' S') -> 0 <= m ->
~ In (lst, m) O1C ->
(forall pn, In pn O1C -> In pn (ablocks B ly' S')) ->
alloc_ceiling <= sp0 - STK ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lst <= a < lst + m) -> ~ (sp0 - STK <= a < sp0) ->
   rdW W' mem2 a = rdW W' mem' a) ->
rec_repA B ly' S' (rdW W' mem2) R1 O1C.
Proof.
intros ly' S' W' mem' md' mem2 R1 O1C lst m sp0 STK HAR HREP Hlin Hm HlO HOin Hstk KEEP.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (req_size_pos m Hm) as [_ Hrm].
destruct (al_blocks _ _ LAWS ly' S' W' mem' md' lst m HAR Hlin) as (_ & Hl4096 & Hlceil & _).
apply (sc7_repA_keep B ly' S' (rdW W' mem') ly' S' (rdW W' mem2) R1 O1C HREP).
- (* g_rec and record.spill: image bytes, so none of the text block's and below the walk's window *)
  intros a Ha. apply KEEP.
  + unfold sc7_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha. lia.
  + intros Hin. assert (Hin' : lst <= a < lst + req_size m) by lia.
    apply (sc7_client_apart B cmd_prog_img ly' S' W' mem' md' a HAR
      (or_introl (ex_intro _ lst (ex_intro _ m (conj Hlin Hin'))))).
    exact Ha.
  + unfold sc7_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha. lia.
- (* the recorder's own blocks: live, apart from the text block, and below the allocator's ceiling *)
  intros pn Hpn. pose proof (HOin pn Hpn) as HpnIn. split; [exact HpnIn|].
  intros i Hi. destruct pn as [q nq]. cbn [fst snd] in Hi |- *.
  destruct (al_blocks _ _ LAWS ly' S' W' mem' md' q nq HAR HpnIn) as (_ & Hq4096 & Hqceil & _ & _ & _ & Hnq).
  pose proof (req_size_pos nq ltac:(lia)) as [_ Hrq].
  assert (Hne : (q, nq) <> (lst, m)) by (intros Hx; apply HlO; rewrite <- Hx; exact Hpn).
  pose proof (sep_blocks SEGS B LAWS ly' S' W' mem' md' q nq lst m HAR HpnIn Hlin Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  apply KEEP; lia.
Qed.
(* where the member array lies at a later state of the walk: the same frame (the walk takes none of its own
   and the layout keeps the frames' addresses), or the same block, which the walk kept *)
Lemma sc8_loc_later : forall ly S (W : world SEGS) mem ly' S' O pids nids,
(afobj SEGS B ly S W mem pids nids \/
 (in_blockA (ablocks B ly S) pids nids /\
  Forall (fun qk => iv_apart pids nids (fst qk) (snd qk)) O)) ->
frames S' = frames S -> (forall cid pos, frame_addr ly' cid pos = frame_addr ly cid pos) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) ->
0 < nids ->
(exists cid pos, In (cid, pos) (frames S') /\ frame_addr ly' cid pos <= pids /\
   pids + nids <= frame_addr ly' cid pos + fs_frame_bytes cid) \/
(exists pb nb, In (pb, nb) (ablocks B ly' S') /\ In (pb, nb) (ablocks B ly S) /\ ~ In (pb, nb) O /\
   pb <= pids /\ pids + nids <= pb + nb).
Proof.
intros ly S W mem ly' S' O pids nids Harr Hfrs Hfa HKEEP Hn.
destruct Harr as [Hfo | [(pb & nb & Hin & Hlo & Hhi) HF]].
- destruct Hfo as ((cid & pos & Hfin & _ & _ & Hflo & Hfhi) & _ & _).
  left. exists cid, pos. rewrite Hfrs, (Hfa cid pos). split; [exact Hfin | lia].
- assert (HnO : ~ In (pb, nb) O).
  { intros HbO. pose proof (proj1 (Forall_forall _ _) HF (pb, nb) HbO) as Hap. cbn [fst snd] in Hap.
    unfold iv_apart in Hap. lia. }
  right. exists pb, nb. split; [exact (HKEEP (pb, nb) Hin HnO)|].
  split; [exact Hin|]. split; [exact HnO | lia].
Qed.

(* the live bytes at the loop: the join's, plus the two recorded numbers and the list text *)
Lemma sc8_bb_after : forall lyc Sc ly' S' (p1 p2 lst n1 n2 m : Z),
Permutation (ablocks B ly' S') ((p2, n2) :: (p1, n1) :: ablocks B lyc Sc ++ [(lst, m)]) ->
blocks_bytes S' = blocks_bytes Sc + n1 + n2 + m.
Proof.
intros lyc Sc ly' S' p1 p2 lst n1 n2 m HP.
rewrite (blocks_bytes_bsum B ly' S'), (bsum_perm _ _ HP), !bsum_cons, bsum_app.
rewrite <- (blocks_bytes_bsum B lyc Sc). cbn [snd].
replace (bsum [(lst, m)]) with m by (unfold bsum; cbn [fold_right snd]; lia).
lia.
Qed.

(* the member array's bytes: four per member (lib/Prog/SupChainA.v's sc_ids_len) *)
Lemma sc8_ids_len : forall ids, length (concat (map le32 ids)) = (4 * length ids)%nat.
Proof.
assert (H4 : forall v : Z, length (le32 v) = 4%nat) by (intros v; reflexivity).
induction ids as [|x ids IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH, (H4 x). lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The walk: entry -> join (sc_segA) -> loop test (sc_segB) -> loop exit (sc_loop) -> the tail jump and the
   post (sc_segC).  --------------------------------------------------------------------------------------- *)

Theorem tsup_chain_holds : tsup_chain_spec B MT.
Proof.
unfold tsup_chain_spec.
intros ly S W regs mem md ch id pids ids R O
  HPRE HFRM HROD HROK H10 Hid H11 Hpids H12 Hn62 HidR Hpnz Hp4 HARR HBYT HREP HFRS0 HEV HLIVE HMOK.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (sc8_xm_parts R id ids Hn62 HidR) as (X1 & X2 & X3 & X4 & X5 & X6 & X7).
assert (Hnn : 1 <= Z.of_nat (length ids) <= 62) by lia.
(* what the first segment asks of the events and of the meter *)
assert (HEVa : st_nev S + rec_spill_frees R <= EV_MAX).
{ unfold EV_SUP_CHAIN, EV_ARG_I, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in HEV. lia. }
assert (HMOKa : mo_ok MT S (rec_spill_frees R * mo_free MT)).
{ apply (mo_ok_le MT MTL S (rec_spill_frees R * mo_free MT) (XM_SUP_CHAIN MT R id ids) HMOK).
  unfold XM_SUP_CHAIN. lia. }
(* the blocks the recorder owns are live *)
assert (HOlive : forall pn, In pn O -> In pn (ablocks B ly S))
  by (intros pn Hpn; exact (scA_own_live B ly S (rdW W mem) R O HREP pn Hpn)).
(* a read-only byte is none of the walk's footprint (sup_chain.v's APART) *)
assert (APART : forall a, in_roP SEGS RLO RHI a -> ~ inFP (sc_FP O) a).
{ intros a Hro Hfp. destruct (cmd_ro_prog_apart a Hro) as [Himg Hpg].
  unfold sc_FP in Hfp. destruct Hfp as (r & Hr & Hra2).
  destruct Hr as [<- | [<- | Hr]].
  - cbn [fst snd] in Hra2. apply Hpg. apply recb_grec_in. exact Hra2.
  - cbn [fst snd] in Hra2. apply Hpg. apply recb_spill_in. exact Hra2.
  - destruct (inFP_ablocks_fp_inv O a ltac:(exists r; split; [exact Hr | exact Hra2]))
      as (q & nq & Hin & Hr2).
    exact (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR
                    (or_introl (ex_intro _ q (ex_intro _ nq (conj (HOlive (q, nq) Hin) Hr2))))) Himg). }
(* the member array lies below the allocator's ceiling (the loop's HPIDC) *)
assert (HPIDC : pids + 4 * Z.of_nat (length ids) <= alloc_ceiling).
{ destruct HARR as [Hfo | [(pb & nb & Hinb & Hlob & Hhib) _]].
  - destruct Hfo as ((cid & pos & Hfin & _ & _ & Hflo & Hfhi) & _ & _).
    destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (_ & Hfc & _). lia.
  - destruct (al_blocks _ _ LAWS ly S W mem md pb nb HAR Hinb) as (_ & _ & Hbc & _ & _ & _ & Hnb).
    pose proof (req_size_pos nb ltac:(lia)) as [_ Hrb]. lia. }
(* segment A: the entry through record()'s two arms to the join *)
apply (sc_segA B MT TRCF VOBJS TL HB MTL cmd_prog_img cmd_prog_writable SIGP RELRO_IMG RRO cmd_ro_prog_apart
         ly S W regs mem md ch id pids ids R O _ HPRE HROD H10 H11 H12 HREP HEVa HMOKa).
intros lyc Sc Wc regsc memc mdc k c HJc Hk Hspc Hgpc Htpc H8c H22c H9c H18c H21c HFRc Hslot HMLEc HBBc HARMc.
(* the block lineage at the join, the same on both arms of record() *)
assert (HJ1 : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly S)).
{ destruct HARMc as [(_ & -> & -> & _) | (_ & _ & (O1 & _ & _ & HL & _))]; [tauto | exact HL]. }
assert (HJ2 : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)).
{ destruct HARMc as [(_ & -> & -> & _) | (_ & _ & (O1 & _ & _ & _ & HL & _))]; [tauto | exact HL]. }
(* segment B: the join through the list text's malloc and the two arg_i calls to the loop test *)
apply (sc_segB B MT TARG_I AMALLOC4 TL HB MTL cmd_prog_img cmd_prog_writable SIGP
         cmd_ro_ok_of_aro RRO RELRO_IMG cmd_ro_prog_apart
         ly S W regs mem md ch id pids ids R O lyc Sc Wc regsc memc mdc k c _
         HPRE HFRM HROD Hid Hn62 HREP HFRS0 HEV HLIVE HMOK
         HJc Hk Hspc Hgpc Htpc H8c H22c H9c H18c H21c HFRc Hslot HMLEc HBBc HARMc).
intros fx2 ly' S' W' regs' mem' md' lst p1 p2 O1 Hfx2
  HJ' Hsp' Hgp' Htp' H8' H9' H18' H19' H20' H21' H22' H23' HFR' Hlst4096 HPERM Hlst0
  HO1O HO1c HOO1 HTGT HREP' HMLE'.
pose proof (proj1 HJ') as HAR'.
(* the blocks at the loop: the join's, the two recorded numbers and the list text *)
destruct (sc8_lineage ly S lyc Sc ly' S' W' mem' md' O O1
            (p1, Z.of_nat (length (dec id)) + 1)
            (p2, Z.of_nat (length (dec (Z.of_nat (length ids)))) + 1)
            (lst, 12 * Z.of_nat (length ids) + 1)
            HAR' HPERM HOlive HJ1 HJ2 HO1O HO1c HOO1)
  as (HLIN & HLO1 & HLCASE & HKEEP & HBL & HOC & HOC2 & HL0).
(* the walk may write the list text's bytes *)
assert (HWR : forall a, lst <= a < lst + 12 * Z.of_nat (length ids) + 1 ->
  awr_byte SEGS B SUP_CHAIN_STK (spZ regs) (sc_FP O) (ablocks B ly S) (ablocks B ly' S') (frames S) ly' [] a).
{ intros a Ha. apply (sc8_wr_text SUP_CHAIN_STK (spZ regs) O ly S ly' S' [] lst
    (12 * Z.of_nat (length ids) + 1) a HLIN HLCASE ltac:(lia) ltac:(lia)). }
(* the member array is apart from the list text *)
pose proof HJ' as (_ & Hly' & _ & _ & _ & Hfrs' & _).
destruct (al_layout _ _ LAWS ly S W mem md ly' HAR Hly') as (_ & Hfa' & _).
assert (HAPART : iv_apart pids (4 * Z.of_nat (length ids)) lst (12 * Z.of_nat (length ids) + 1)).
{ destruct (sc8_loc_later ly S W mem ly' S' O pids (4 * Z.of_nat (length ids)) HARR
              ltac:(rewrite Hfrs'; reflexivity) Hfa' HKEEP ltac:(lia))
    as [(cid & pos & Hfin & Hflo & Hfhi) | (pb & nb & Hb' & Hb & HbO & Hlo & Hhi)].
  - apply (sc8_apart_of_loc ly' S' W' mem' md' pids (4 * Z.of_nat (length ids)) lst
             (12 * Z.of_nat (length ids) + 1) HAR'
             (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hfin (conj Hflo Hfhi)))))
             HLIN ltac:(lia)).
  - assert (Hne : (pb, nb) <> (lst, 12 * Z.of_nat (length ids) + 1)).
    { intros Hx. injection Hx as Hp Hn2. subst pb. rewrite Hn2 in Hb, HbO.
      destruct HLCASE as [Hno | Hy]; [exact (Hno Hb) | exact (HbO Hy)]. }
    apply (sc8_apart_of_loc ly' S' W' mem' md' pids (4 * Z.of_nat (length ids)) lst
             (12 * Z.of_nat (length ids) + 1) HAR'
             (or_intror (ex_intro _ pb (ex_intro _ nb (conj Hb' (conj Hne (conj Hlo Hhi))))))
             HLIN ltac:(lia)). }
(* the member array's bytes and shadow at the loop's memory *)
assert (HBYT' : abytes_atR (rdW W' mem') pids (concat (map le32 ids))).
{ apply (sc3_bytes_keep (rdW W mem)); [exact HBYT|].
  intros i Hi. apply (sc7_arr_bytes B cmd_prog_img SUP_CHAIN_STK (spZ regs) O ly S W mem md []
    ly' S' W' mem' md' (k + 1 + EV_ARG_I + EV_ARG_I) pids (4 * Z.of_nat (length ids))
    HAR HJ' HARR HOlive HKEEP ltac:(lia)).
  rewrite sc8_ids_len in Hi. lia. }
(* the member array's shadow, the read-only image and the live bytes at the loop's memory *)
assert (HSHA : range_addressable (rdW W' mem') SHADOW_OFF pids (4 * Z.of_nat (length ids))).
{ exact (sc7_arr_shadow B SUP_CHAIN_STK (spZ regs) O ly S W mem md []
           ly' S' W' mem' md' (k + 1 + EV_ARG_I + EV_ARG_I) pids (4 * Z.of_nat (length ids))
           HAR HJ' HARR HOlive HKEEP ltac:(lia)). }
assert (HROD' : arodata_okP SEGS RLO RHI B (rdW W' mem')).
{ eapply (arodata_ok_journalP (RO:=RRO) SEGS RLO RHI RELRO_IMG B SUP_CHAIN_STK (spZ regs) (sc_FP O)
            ly S W mem md [] ly' S' W' mem' md' (k + 1 + EV_ARG_I + EV_ARG_I));
    [exact HJ' | exact APART | exact HROD]. }
assert (HFRS' : frames S' = frames S) by (rewrite Hfrs'; reflexivity).
assert (HBB' : blocks_bytes S' = blocks_bytes Sc + (Z.of_nat (length (dec id)) + 1)
                 + (Z.of_nat (length (dec (Z.of_nat (length ids)))) + 1)
                 + (12 * Z.of_nat (length ids) + 1))
  by (exact (sc8_bb_after lyc Sc ly' S' p1 p2 lst _ _ _ HPERM)).
assert (HSTK : 112 + 3 * ESTACK <= SUP_CHAIN_STK).
{ unfold SUP_CHAIN_STK, SUP_CHAIN_OWN. lia. }
(* what the tail segment asks of the events, the meter and the model *)
assert (HEVc : k + 1 + EV_ARG_I + EV_ARG_I + EV_XSTRDUP + 1 + EV_REC_SHAPE_OF + EV_ANSWER
                 <= EV_SUP_CHAIN R).
{ unfold EV_SUP_CHAIN, EV_REC_SHAPE_OF, EV_ARG_I, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP. lia. }
assert (HXMc : rec_spill_frees R * mo_free MT + mo_malloc MT (12 * Z.of_nat (length ids) + 1) +
                 XM_ARG_I MT id + XM_ARG_I MT (Z.of_nat (length ids)) +
                 (XM_XSTRDUP MT (dec_list ids) + mo_free MT +
                  XM_ANSWER MT (snd (sup_chain_m R id ids)))
               <= XM_SUP_CHAIN MT R id ids)
  by (unfold XM_SUP_CHAIN; lia).
assert (HMODEL : sc_push_arg (sc_R2 R id (Z.of_nat (length ids))) (sc_k R) (dec_list ids)
                 = rec_record R REC_CHAIN [dec id; dec (Z.of_nat (length ids)); dec_list ids]).
{ unfold sc_R2, sc_k. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hlt | Hge].
  - exact (sc_record3 R REC_CHAIN (dec id) (dec (Z.of_nat (length ids))) (dec_list ids) Hlt).
  - assert (H16 : length (r_calls R) = 16%nat)
      by (pose proof (scA_slot_in B ly S (rdW W mem) R O HREP); lia).
    exact (sc_record3_spill R REC_CHAIN (dec id) (dec (Z.of_nat (length ids))) (dec_list ids) H16). }
assert (HDECLEN : Z.of_nat (length (dec_list ids)) <= 12 * Z.of_nat (length ids))
  by (pose proof (sc_dec_list_len ids HidR ltac:(lia)); lia).
(* the recorder's blocks are live at the loop *)
assert (HO1live : forall pn, In pn (O1 ++ [(p1, Z.of_nat (length (dec id)) + 1);
                                       (p2, Z.of_nat (length (dec (Z.of_nat (length ids)))) + 1)]) ->
                   In pn (ablocks B ly' S'))
  by (intros pn Hpn; exact (scA_own_live B ly' S' (rdW W' mem') _ _ HREP' pn Hpn)).
(* segment C, from what the loop leaves at its exit: the same journal (the loop allocates nothing), the
   registers it keeps, the frame, the list text, and every byte outside the text and the stack window; it runs at
   the FP state fx3 the last sprintf returned, and its post at fx3 is the function's post at fx *)
lazymatch goal with |- SRr _ _ _ ?Qpost =>
assert (TAIL : forall (fx3 : YK11.FPState) (regsx : bvmap 5 word) memx mdx,
  fxrel fx fx3 ->
  ajournal SEGS B SUP_CHAIN_STK (spZ regs) (sc_FP O) ly S W mem md [] ly' S' W' memx mdx
    (k + 1 + EV_ARG_I + EV_ARG_I) ->
  spZ regsx = spZ regs - 112 ->
  getr regsx 3 = w64 (as_gp B) -> getr regsx 4 = w64 (as_tp B) ->
  getr regsx 8 = w64 c -> getr regsx 19 = w64 (c + 4) -> getr regsx 20 = w64 lst ->
  getr regsx 22 = w64 SB -> getr regsx 23 = w64 ((c + 4) / 8 + SB) ->
  sc_frame_at (mrestrict (w_H W') memx) (spZ regs) regs ->
  abytes_atR (rdW W' memx) lst (dec_list (firstn (length ids) ids) ++ [Z_to_bv 8 0]) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lst <= a < lst + 12 * Z.of_nat (length ids) + 1) ->
     ~ (spZ regs - SUP_CHAIN_STK <= a < spZ regs) -> rdW W' memx a = rdW W' mem' a) ->
  SRr SEGS W' (@cfg_at fx3 SEGS (BASE + SC_TAILSEG) regsx memx mdx) Qpost) end.
{ intros fx3 regsx memx mdx Hfx3 HJx Hspx H3x H4x H8x H19x H20x H22x H23x HFRx HTXT HAGR.
  assert (HREPx : rec_repA B ly' S' (rdW W' memx) (sc_R2 R id (Z.of_nat (length ids)))
            (O1 ++ [(p1, Z.of_nat (length (dec id)) + 1);
                    (p2, Z.of_nat (length (dec (Z.of_nat (length ids)))) + 1)])).
  { apply (sc8_repA_loop ly' S' W' mem' md' memx _ _ lst (12 * Z.of_nat (length ids) + 1)
             (spZ regs) SUP_CHAIN_STK HAR' HREP' HLIN ltac:(lia) HLO1 HO1live ltac:(lia)
             ltac:(intros a Ha Hn Hs; apply HAGR; [exact Ha | intros Hx; apply Hn; lia | exact Hs])). }
  assert (HSTR : astr_atR (rdW W' memx) lst (dec_list ids)).
  { split; [| exact (sc_dec_list_nz ids)]. rewrite firstn_all in HTXT. exact HTXT. }
  assert (H23x' : getr regsx 23 = w64 (SB + (c + 4) / 8)) by (rewrite H23x; f_equal; lia).
  apply (srr_apost_baseF_lift (fx := fx) SEGS fx3); [exact Hfx3|].
  apply (sc_segC (fx := fx3) B MT HB cmd_prog_img cmd_prog_writable TL MTL VOBJS SIGP TXSTRDUP TREC_SHAPE_OF
           TANSWER AFREE4 cmd_ro_ok_of_aro RRO RELRO_IMG cmd_ro_prog_apart CMD_RO_IN cmd_heap_tail_vis
           ly S W regs mem md ch id ids R (sc_R2 R id (Z.of_nat (length ids))) O
           (O1 ++ [(p1, Z.of_nat (length (dec id)) + 1);
                   (p2, Z.of_nat (length (dec (Z.of_nat (length ids)))) + 1)])
           (sc_k R) (REC_CHAIN, [dec id; dec (Z.of_nat (length ids))])
           ly' S' W' regsx memx mdx (k + 1 + EV_ARG_I + EV_ARG_I)
           (rec_spill_frees R * mo_free MT + mo_malloc MT (12 * Z.of_nat (length ids) + 1) +
            XM_ARG_I MT id + XM_ARG_I MT (Z.of_nat (length ids)))
           c lst
           HPRE (fxrel_frm0 fx fx3 HFRM Hfx3) HROD Hn62 HJx HEVc HEV ltac:(rewrite HFRS'; exact HFRS0) HLIVE
           ltac:(rewrite HBB'; unfold LIVE_ARG_I, LIVE_XSTRDUP; lia)
           HMOK HMLE' HXMc Hspx H3x H4x H8x Hslot H19x H20x H22x H23x' HFRx
           HREPx HTGT eq_refl eq_refl HMODEL HLIN HLO1 HSTR HDECLEN
           HOlive HKEEP HBL HOC HOC2 HL0). }
(* the loop: one sprintf per member, from the skip test to the exit, then segment C *)
apply (sc_loop (fx := fx2) B VOBJS ASPRINTF cmd_ro_ok_of_aro RELRO_IMG cmd_rec_cells
         ZSH_lit_21ee0 ZSH_lit_21f00 HULL_lit_21ee0 HULL_lit_21f00 HB IMG
         SUP_CHAIN_STK (spZ regs) (sc_FP O) ly ly' S S' W W' mem mem' md []
         (k + 1 + EV_ARG_I + EV_ARG_I) pids lst c ids regs
         Hn62 HidR ltac:(lia) HLIN HWR HAPART HPIDC HSTK
         regs' md' _ (fxrel_frm0 fx fx2 HFRM Hfx2)
         HJ' Hsp' Hgp' Htp' H8' H9' H18' H19' H20' H22' H23' HFR' Hlst0 HBYT' HSHA HROD').
intros fx3 regsx memx mdx Hfx23 HINV.
destruct HINV as (_ & HJx & Hspx & H3x & H4x & H8x & _ & H19x & H20x & H22x & H23x & _ & _ & _ & _ & _ & _ &
                  HFRx & HTXT & _ & _ & _ & HAGR).
exact (TAIL fx3 regsx memx mdx (fxrel_trans fx fx2 fx3 Hfx2 Hfx23)
         HJx Hspx H3x H4x H8x H19x H20x H22x H23x HFRx HTXT HAGR).
Qed.

End e.
End f.
End d.
