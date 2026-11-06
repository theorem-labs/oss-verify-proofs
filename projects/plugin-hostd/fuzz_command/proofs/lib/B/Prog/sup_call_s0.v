(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: sup_call's ASan walk (plugin-hostd/fuzz_command, 0x8a95c, 67 instructions),
   assembled from its three parts (sup_call_s3.v): the prologue to the join of record()'s two arms (sup_call_a.v
   sc_prologue), the body to answer's entry (sup_call_b.v sc_body) and the tail through answer's contract
   (sup_call_t.v sc_tail_ok).

   The theorem is sup_call_c.v's tsup_call_spec as the statement states it (statement
   passes 4, 4b and 5): the line is a live block that is none of the recorder's (in_blockA + iv_apart against O),
   the entry carries rounding mode 0, the post is FP-existential (apost_baseF) and carries the live-bytes bound and
   the settled freshness conjunct, and the callee contracts hold at every FP state. The parts take the image's
   per-binary facts as IMG and PRW and apply CmdRecFacts' lemmas (CmdRecBase.v, CmdRecCells.v, CmdRecRo.v) by
   exact. The body applies the tail at the FP state arg_i returns (sup_call_b.v sc_body), so the tail goes in as
   sc_tail_ok at every FP state. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_call.v, with its module paths and module names changed; 107 of its 137 lines of code are new or changed and 74 lines of the source are left out. *)
(* sup_call's walk on the ASan+UBSan build of plugin-hostd/fuzz_command, part 0: facts the parts share.
   - sup_call's footprint (sup_call_s3.v SC_FP): its bytes are program statics or bytes of the recorder's blocks O,
     all below alloc_ceiling;
   - the recorder's blocks are live (RecBLemmas.v lay_blocks_in);
   - the read-only bytes and the bytes at and above the entry sp are the entry's at every state of the walk (the
     journal from the entry, CmdRecRest.v cmd_rodata_kept and the journal's kept-bytes clause);
   - the frame chain at a program call: s0 is this call's frame pointer sp0, under which the prologue saved ra and
     the caller's s0 (0x8af3c, 0x8af40), so the callee's chain is afn_pre's chain pushed at sp0 (YCbq.v achain_push;
     the class of the frame-pointer functions), or the empty chain when sp0 is within 16 bytes of the stack top;
   - the saved registers and the flag-byte word read through another reader that agrees on their bytes. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04 YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdObj CmdRo PaSB PaFx PaLibF.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase CmdRecRest RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c arg_s_c arg_line_c answer_c sup_call_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_call_s3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* a byte of sup_call's footprint is a byte of g_rec or record.spill, or of one of the recorder's blocks *)
Lemma sc_fp_cases : forall O a, inFP (SC_FP O) a ->
Exists (in_zr a) TFIB_PROG_STATIC \/ exists p n, In (p, n) O /\ p <= a < p + req_size n.
Proof.
intros O a Ha. unfold SC_FP in Ha.
repeat rewrite inFP_cons in Ha.
unfold TFIB_PROG_STATIC, A_G_REC, A_REC_SPILL, OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_STATE, SC_SIZE in *.
destruct Ha as [H | [H | [H | [H | H]]]].
- left. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- left. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- left. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- left. apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- right. exact (inFP_ablocks_fp_inv O a H).
Qed.

(* the realigned stack pointer lies 96 to 112 bytes below the entry sp, 32-aligned *)
Lemma sc_sp1_bounds : forall x, x - 128 < sc_sp1 x <= x - 96 /\ sc_sp1 x mod 32 = 0.
Proof.
intros x. unfold sc_sp1. pose proof (Z.div_mod (x - 96) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (x - 96) 32 ltac:(lia)) as M.
split; [lia|]. rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

(* the saved registers and an 8-byte word read through a reader that agrees on their bytes *)
Lemma sc_frame_ext : forall (rd rd' : reader) sp0 (regs0 : bvmap 5 word),
(forall a, sp0 - 88 <= a < sp0 -> rd' a = rd a) -> sc_frame rd sp0 regs0 -> sc_frame rd' sp0 regs0.
Proof.
intros rd rd' sp0 regs0 HK HF j r Hj k Hk.
assert (Hj11 : (j < length sc_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
change (length sc_saved) with 11%nat in Hj11.
rewrite HK by lia. exact (HF j r Hj k Hk).
Qed.
Lemma sc_rdword_ext : forall (rd rd' : reader) a v,
(forall x, a <= x < a + 8 -> rd' x = rd x) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof.
intros rd rd' a v HK H. rewrite (rdword_ext rd rd' a); [exact H|]. intros k Hk. apply HK. lia.
Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis IMG : cmd_img_facts SEGS B.

(* the recorder's blocks are live *)
Lemma sc_O_live : forall ly S (rd : reader) R O, rec_repA B ly S rd R O -> forall pn, In pn O -> In pn (ablocks B ly S).
Proof.
intros ly S rd R O (Q & HA & HO) pn Hpn. exact (lay_blocks_in _ rd _ _ R Q HA pn (proj1 (HO pn) Hpn)).
Qed.

(* every footprint byte lies below alloc_ceiling *)
Lemma sc_fp_low : forall ly S (W : world SEGS) mem md (O : list (Z * Z)),
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
forall a, inFP (SC_FP O) a -> a < alloc_ceiling.
Proof.
intros ly S W mem md O HAR HO a Ha. pose proof asan_consts as (C1 & _).
destruct (sc_fp_cases O a Ha) as [Hp | (p & n & Hpn & Hr)].
- apply Exists_exists in Hp as (r & Hr & Har). unfold TFIB_PROG_STATIC in Hr. unfold in_zr in Har.
  destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Har; lia.
- pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR (HO _ Hpn)) as (_ & _ & Hc & _). cbn [fst snd] in Hc. lia.
Qed.

(* the read-only bytes keep the image's values at every state of the walk *)
Lemma sc_aro : forall ly S (W : world SEGS) mem md (O : list (Z * Z)) STK sp0 own lyc Sc (Wc : world SEGS) memc mdc k,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
ajournal SEGS B STK sp0 (SC_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
arodata_okP SEGS CMD_RLO CMD_RHI B (rdW W mem) -> arodata_okP SEGS CMD_RLO CMD_RHI B (rdW Wc memc).
Proof.
intros ly S W mem md O STK sp0 own lyc Sc Wc memc mdc k HAR HO HJ HR.
apply (cmd_rodata_kept SEGS B LAWS HB IMG ly S W mem md lyc Sc Wc memc mdc STK sp0 (SC_FP O) own k HAR HJ); [|exact HR].
intros a Ha. destruct (sc_fp_cases O a Ha) as [Hp | (p & n & Hpn & Hr)]; [left; exact Hp|].
right. exists p, n. split; [apply in_or_app; left; exact (HO _ Hpn) | exact Hr].
Qed.

(* the bytes at and above the entry sp are the entry's at every state of the walk *)
Lemma sc_above_kept : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch (O : list (Z * Z)) own lyc Sc
  (Wc : world SEGS) memc mdc k,
afn_pre SEGS B SUP_CALL_STK ly S W regs mem md ch -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
ajournal SEGS B SUP_CALL_STK (spZ regs) (SC_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
forall a, spZ regs <= a < 2 ^ 64 -> rdW Wc memc a = rdW W mem a.
Proof.
intros ly S W regs mem md ch O own lyc Sc Wc memc mdc k HPRE HO HJ a Ha.
pose proof HPRE as (HAR & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & _) & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
apply F1; [lia | lia |]. intros Hf. pose proof (sc_fp_low ly S W mem md O HAR HO a Hf). lia.
Qed.

(* the frame chain a program call at sp1 takes for s0 = sp0 *)
Lemma sc_chain : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch (O : list (Z * Z)) fpos F FL lyc Sc
  (Wc : world SEGS) (regsc : bvmap 5 word) memc mdc k,
afn_pre SEGS B SUP_CALL_STK ly S W regs mem md ch -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
sc_live B ly S W regs mem md O fpos F FL lyc Sc Wc regsc memc mdc k ->
exists ch1, achain lyc (rdW Wc memc) (sc_sp1 (spZ regs)) (s0Z regsc) ch1.
Proof.
intros ly S W regs mem md ch O fpos F FL lyc Sc Wc regsc memc mdc k HPRE HO HL.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & _).
destruct HL as (HJ & _ & _ & (Esp & E8 & _) & HFR & _).
pose proof HJ as (_ & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
assert (S0 : s0Z regsc = spZ regs) by (unfold s0Z, spZ; rewrite E8; reflexivity).
pose proof (sc_above_kept ly S W regs mem md ch O [(0, fpos)] lyc Sc Wc memc mdc k HPRE HO HJ) as KEEP.
pose proof (sc_sp1_bounds (spZ regs)) as (Hsp1 & _).
assert (RA : rdword (rdW Wc memc) (spZ regs - 8) = Some (raZ regs)).
{ apply (rdword_of_val_mem SEGS); [|unfold raZ; apply bv_unsigned_in_range].
  apply val_mem_of_aval. replace (spZ regs - 8) with (spZ regs - 8 - 8 * Z.of_nat 0) by lia.
  exact (HFR 0%nat 1 eq_refl). }
assert (RS0 : rdword (rdW Wc memc) (spZ regs - 16) = Some (s0Z regs)).
{ apply (rdword_of_val_mem SEGS); [|unfold s0Z; apply bv_unsigned_in_range].
  apply val_mem_of_aval. replace (spZ regs - 16) with (spZ regs - 8 - 8 * Z.of_nat 1) by lia.
  exact (HFR 1%nat 8 eq_refl). }
assert (H8 : spZ regs mod 8 = 0).
{ pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D. rewrite Hal16 in D. rewrite D.
  replace (16 * (spZ regs / 16) + 0) with ((2 * (spZ regs / 16)) * 8) by lia. apply Z_mod_mult. }
rewrite S0.
destruct (Z_lt_le_dec (spZ regs) (ly_top ly - 16)) as [Hlt | Hge].
- exists ((spZ regs, raZ regs, s0Z regs) :: ch).
  apply (achain_ly_top ly lyc); [exact Etop|].
  apply (achain_push ly (rdW W mem) (rdW Wc memc) (spZ regs) (s0Z regs) (raZ regs) ch (sc_sp1 (spZ regs)) Hch);
  [lia | exact KEEP | exact RA | exact RS0 | exact Hra4 | lia | exact H8 | exact Hlt | lia].
- exists []. left. split; [right; left; rewrite Etop; lia | reflexivity].
Qed.
End e.
End f.
End w.
