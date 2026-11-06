(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 558 of its 606 lines of code are new or changed and 405 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a5_k.v; 258 of its 441 lines of code are new or changed and 423 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A: the transport of reac_segconf_parse_file's cut facts (pf_base, and segment A11a's
   a11_cx) across a step or a call that writes one object of the class-5 frame and some cells of the frame's shadow.
   Part of segment A11a's proof, by the G3 walk owner, 2026-10-30. No Section hypothesis.

   WHY. pf_a5_k.v's a5_move0 rebuilds pf_base only for a step whose writes lie in A5's write set a5_Wrx (the stack
   window below s1, slot 0xb0, buf, buf's 64 shadow cells). Segment A11a also writes low146 (F + 0x2e0, 24 bytes:
   the fold stores 0x882b8 and the NUL store 0x88530) and low146's three shadow cells (SH + 92 .. SH + 94, the scope
   stores 0x8826c-0x88274). So this file restates pf_a5_k.v's keep lemmas (a5_out, a5_heap_out,
   a5_heap_shadow_out, a5_heap_tail_out, a5_img_out, a5_low_out, a5_keep_addr / _hstr / _lit / _img_word / _cat /
   _rod0 / _ssp / _obj0 / _st / _sl / _saved / _flag) and a5_move0 over the write set pfw_X: the stack window below
   s1, the frame bytes [F + o, F + o + n) and the shadow cells [SH + so, SH + so + sn), for any o n so sn with
   pfw_ok (the object before the frame's flag word, the cells inside the frame's 256). The proofs are pf_a5_k.v's
   (segment A5's proof), with the write set changed.
   a11m_X / a11m_base / a11m_cx are the instance at low146 and its three shadow cells. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0p YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs RtShadow.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA
  pf_pieces pf_a5_d pf_a2_k pf_a5_k pf_a11a_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require pf_a6_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the frame object [F + o, F + o + n) lies before the flag word at F + 2040; the cells [SH + so, SH + so + sn)
   among the frame's 256 *)
Definition pfw_ok (o n so sn : Z) : Prop := 0 <= o /\ o + n <= 2040 /\ 0 <= so /\ so + sn <= 256.
Lemma a11m_ok : pfw_ok PF_O_L146 24 92 3.
Proof. unfold pfw_ok, PF_O_L146. lia. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* ======================= the write set ======================= *)
Definition pfw_X (v : pfv) (pos o n so sn a : Z) : Prop :=
  (pf_sp0 v - STK_reac_segconf_parse_file <= a < pf_s1 v) \/
  (pf_F v pos + o <= a < pf_F v pos + o + n) \/
  (pf_SH v pos + so <= a < pf_SH v pos + so + sn).
(* A11a's: the stack window below s1, low146, low146's three shadow cells *)
Definition a11m_X (v : pfv) (pos a : Z) : Prop :=
  (pf_sp0 v - STK_reac_segconf_parse_file <= a < pf_s1 v) \/
  (pf_F v pos + PF_O_L146 <= a < pf_F v pos + PF_O_L146 + 24) \/
  (pf_SH v pos + 92 <= a < pf_SH v pos + 95).
Lemma a11m_X_pfw : forall v pos a, a11m_X v pos a <-> pfw_X v pos PF_O_L146 24 92 3 a.
Proof.
intros v pos a. unfold a11m_X, pfw_X. replace (pf_SH v pos + 92 + 3) with (pf_SH v pos + 95) by lia. tauto.
Qed.

(* the classes of bytes a cut fact reads, each off pfw_X (pf_a5_k.v a5_out and its callers) *)
(* below alloc_ceiling, outside the frame and outside the shadow band *)
Lemma pfw_out : forall v pos o n so sn a, a5_G v pos -> pfw_ok o n so sn -> a < alloc_ceiling ->
  ~ (pf_F v pos <= a < pf_F v pos + 2048) -> ~ (kLowMemEnd <= a < kHighShadowEnd) -> ~ pfw_X v pos o n so sn a.
Proof.
intros v pos o n so sn a G (Ho & Hon & Hso & Hsn) Hc Hf Hs W. pose proof STK_values as (_ & _ & _ & SPF & _).
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
unfold pfw_X in W. rewrite SPF in G1, W.
destruct W as [W | [W | W]]; lia.
Qed.
(* at or above s1 (the slots, the saved registers) *)
Lemma pfw_stack_out : forall v pos o n so sn a, a5_G v pos -> pfw_ok o n so sn -> pf_s1 v <= a ->
  ~ pfw_X v pos o n so sn a.
Proof.
intros v pos o n so sn a G (Ho & Hon & Hso & Hsn) Ha W.
pose proof STK_values as (_ & _ & _ & SPF & _). pose proof asan_consts as (C1 & _).
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
unfold pfw_X in W. rewrite SPF in G1. unfold kHighShadowEnd in G12.
destruct W as [W | [W | W]]; lia.
Qed.
(* a byte of the frame outside the object *)
Lemma pfw_frame_out : forall v pos o n so sn a, a5_G v pos -> pfw_ok o n so sn ->
  pf_F v pos <= a < pf_F v pos + 2048 -> ~ (pf_F v pos + o <= a < pf_F v pos + o + n) -> ~ pfw_X v pos o n so sn a.
Proof.
intros v pos o n so sn a G (Ho & Hon & Hso & Hsn) Ha Hn W.
pose proof STK_values as (_ & _ & _ & SPF & _).
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9. unfold kLowMemEnd, kHighShadowEnd in G11, G12.
unfold pfw_X in W. rewrite SPF in G1.
destruct W as [W | [W | W]]; lia.
Qed.
(* a cell of the frame's shadow outside the written cells *)
Lemma pfw_fsh_out : forall v pos o n so sn i, a5_G v pos -> pfw_ok o n so sn -> 0 <= i < 256 ->
  ~ (so <= i < so + sn) -> ~ pfw_X v pos o n so sn (pf_SH v pos + i).
Proof.
intros v pos o n so sn i G (Ho & Hon & Hso & Hsn) Hi Hn W.
pose proof STK_values as (_ & _ & _ & SPF & _). pose proof asan_consts as (C1 & _).
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9. unfold kLowMemEnd, kHighShadowEnd in G11, G12.
unfold pfw_X in W. rewrite SPF in G1.
destruct W as [W | [W | W]]; lia.
Qed.

(* ======================= the reader facts kept off pfw_X (pf_a5_k.v a5_keep_sl / _saved / _flag) ======================= *)
Lemma pfw_keep_sl : forall v pos o n so sn (rd rd' : reader), a5_G v pos -> pfw_ok o n so sn ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pfw_X v pos o n so sn a -> rd' a = rd a) ->
  forall L, Forall (fun ov => 0 <= fst ov /\ fst ov + 8 <= 0x100) L ->
  pf_sl rd (pf_s1 v) L -> pf_sl rd' (pf_s1 v) L.
Proof.
intros v pos o n so sn rd rd' G Hok HK L HL H.
pose proof G as (G1 & G2 & G3 & G4 & G5 & _).
pose proof STK_values as (_ & _ & _ & SPF & _). pose proof asan_consts as (C1 & _).
unfold pf_sl in *. rewrite Forall_forall in *. intros [off val] Hov. specialize (H _ Hov). specialize (HL _ Hov).
cbn [fst snd] in *. rewrite rdword_ext with (rd := rd); [exact H|].
intros k Hk. rewrite SPF in G1. apply HK; [lia|]. apply (pfw_stack_out v pos o n so sn _ G Hok). lia.
Qed.
Lemma pfw_keep_saved : forall v pos o n so sn (rd rd' : reader) regs, a5_G v pos -> pfw_ok o n so sn ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pfw_X v pos o n so sn a -> rd' a = rd a) ->
  pf_saved rd (pf_sp0 v) regs -> pf_saved rd' (pf_sp0 v) regs.
Proof.
intros v pos o n so sn rd rd' regs G Hok HK H j r Hj.
pose proof G as (G1 & G2 & G3 & G4 & G5 & _).
pose proof STK_values as (_ & _ & _ & SPF & _). pose proof asan_consts as (C1 & _).
assert (Hj13 : (j < 13)%nat) by (change 13%nat with (length PF_SAVED); apply nth_error_Some; rewrite Hj; discriminate).
rewrite rdword_ext with (rd := rd); [exact (H j r Hj)|]. intros k Hk. rewrite SPF in G1. apply HK; [lia|].
apply (pfw_stack_out v pos o n so sn _ G Hok). lia.
Qed.
Lemma pfw_keep_flag : forall v pos o n so sn (rd rd' : reader) x, a5_G v pos -> pfw_ok o n so sn ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pfw_X v pos o n so sn a -> rd' a = rd a) ->
  rdword rd (pf_F v pos + fs_frame_bytes 5 - 8) = Some x -> rdword rd' (pf_F v pos + fs_frame_bytes 5 - 8) = Some x.
Proof.
intros v pos o n so sn rd rd' x G Hok HK H.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & _).
pose proof asan_consts as (C1 & _). pose proof Hok as (Ho & Hon & _).
change (fs_frame_bytes 5) with 2048 in *.
rewrite rdword_ext with (rd := rd); [exact H|]. intros k Hk. apply HK; [lia|].
apply (pfw_frame_out v pos o n so sn _ G Hok); lia.
Qed.
(* a string in buf (pf_inb), its bytes and its tail inside the frame below F + 0x240 *)
Lemma pfw_keep_buf : forall v pos o n so sn (rd rd' : reader) p s, a5_G v pos -> pfw_ok o n so sn -> 0x240 <= o ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pfw_X v pos o n so sn a -> rd' a = rd a) ->
  pf_inb (pf_F v pos + PF_O_BUF) p s -> sa_str rd p s -> sa_str rd' p s.
Proof.
intros v pos o n so sn rd rd' p s G Hok Ho2 HK [Hb1 Hb2] ((Hz & Hn) & Ht).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof asan_consts as (C1 & _).
pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)) as DF. rewrite G8, Z.add_0_r in DF.
unfold PF_O_BUF in *.
split; [split; [|exact Hn]|].
- intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
  rewrite HK; [exact (Hz i Hi) | lia |]. apply (pfw_frame_out v pos o n so sn _ G Hok); lia.
- intros x Hx. pose proof (Z.div_mod (p + Z.of_nat (length s)) 8 ltac:(lia)) as De.
  pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)) as Me.
  rewrite HK; [exact (Ht x Hx) | lia |]. apply (pfw_frame_out v pos o n so sn _ G Hok); lia.
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* ======================= the bytes of a state's objects, off pfw_X (pf_a5_k.v) ======================= *)
Lemma pfw_heap_out : forall v pos o n so sn lyc Sc Wc memc mdc b m a,
  a5_G v pos -> pfw_ok o n so sn -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m -> ~ pfw_X v pos o n so sn a.
Proof.
intros v pos o n so sn lyc Sc Wc memc mdc b m a G Hok HAR Hin Hly Hb Ha. subst lyc.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & Hceil & Happ & _).
pose proof (sep_block_frame SEGS B LAWS (p_ly v) Sc Wc memc mdc b m 5 pos HAR Hb Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in Hd.
change (fs_frame_bytes 5) with 2048 in Hd.
apply (pfw_out v pos o n so sn a G Hok); [lia | lia |].
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold kLowMemEnd, kHighShadowEnd. lia.
Qed.
Lemma pfw_heap_shadow_out : forall v pos o n so sn lyc Sc Wc memc mdc b m x,
  a5_G v pos -> pfw_ok o n so sn -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  In (b, m) (ablocks B lyc Sc) -> b <= x < b + req_size m -> ~ pfw_X v pos o n so sn (SHADOW_OFF + x / 8).
Proof.
intros v pos o n so sn lyc Sc Wc memc mdc b m x G (Ho & Hon & Hso & Hsn) HAR Hin Hly Hb Hx. subst lyc.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & Hceil & Happ & _).
pose proof (sep_block_frame SEGS B LAWS (p_ly v) Sc Wc memc mdc b m 5 pos HAR Hb Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in Hd.
change (fs_frame_bytes 5) with 2048 in Hd.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _).
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)) as DF.
assert (MF : pf_F v pos mod 8 = 0).
{ apply Z.mod_divide in G8; [|lia]. destruct G8 as [k Hk]. rewrite Hk. replace (k * 32) with ((4 * k) * 8) by lia.
  apply Z_mod_mult. }
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ, G9.
unfold pfw_X. rewrite SPF in *. rewrite G10. unfold kLowMemEnd, kHighShadowEnd, SHADOW_OFF in *.
intros [W | [W | W]]; lia.
Qed.
Lemma pfw_heap_tail_out : forall v pos o n so sn lyc Sc Wc memc mdc b m e x,
  a5_G v pos -> pfw_ok o n so sn -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  In (b, m) (ablocks B lyc Sc) -> b <= e < b + req_size m -> e < x < e - e mod 8 + 8 -> ~ pfw_X v pos o n so sn x.
Proof.
intros v pos o n so sn lyc Sc Wc memc mdc b m e x G Hok HAR Hin Hly Hb He Hx. subst lyc.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & Hceil & Happ & _).
pose proof (sep_block_frame SEGS B LAWS (p_ly v) Sc Wc memc mdc b m 5 pos HAR Hb Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in Hd.
change (fs_frame_bytes 5) with 2048 in Hd.
pose proof (alloc_ceiling_value) as (_ & AC4).
pose proof (Z.div_mod e 8 ltac:(lia)) as De. pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as Me.
pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)) as DA.
pose proof G as (_ & _ & _ & _ & _ & _ & _ & G8 & _).
pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)) as DF.
apply (pfw_out v pos o n so sn x G Hok).
- lia.
- lia.
- unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold kLowMemEnd, kHighShadowEnd. lia.
Qed.
Lemma pfw_img_out : forall v pos o n so sn lyc Sc Wc memc mdc a,
  a5_G v pos -> pfw_ok o n so sn -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  in_img SEGS a -> ~ pfw_X v pos o n so sn a.
Proof.
intros v pos o n so sn lyc Sc Wc memc mdc a G Hok HAR Hin Hly Hi. subst lyc.
pose proof (pa_img_range a Hi) as Hr. unfold kImgEnd in Hr.
pose proof (frm_img SEGS B LAWS (p_ly v) Sc Wc memc mdc 5 pos a HAR Hin) as Hf.
change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in Hf. change (fs_frame_bytes 5) with 2048 in Hf.
pose proof asan_consts as (C1 & _).
apply (pfw_out v pos o n so sn a G Hok); [lia | intros Ha; exact (Hf Ha Hi) | unfold kLowMemEnd; lia].
Qed.
Lemma pfw_low_out : forall v pos o n so sn lyc Sc Wc memc mdc a,
  a5_G v pos -> pfw_ok o n so sn -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  0x10000 <= a < kImgEnd -> ~ pfw_X v pos o n so sn a.
Proof.
intros v pos o n so sn lyc Sc Wc memc mdc a G Hok HAR Hin Hly Ha. subst lyc.
pose proof HAR as (M & LG & _).
pose proof (pa_img_cover (p_ly v) Sc mdc LG) as [IC1 IC2].
pose proof asan_consts as (AC & _).
apply (pfw_out v pos o n so sn a G Hok).
- unfold kImgEnd in *. lia.
- intros Hf. destruct (al_client_img _ _ LAWS (p_ly v) Sc Wc memc mdc a HAR) as [Hz _].
  { right. left. exists 5, pos. split; [exact Hin|].
    change (frame_addr (p_ly v) 5 pos) with (pf_F v pos). change (fs_frame_bytes 5) with 2048. exact Hf. }
  apply Hz. unfold in_zr. unfold kImgEnd in *. lia.
- unfold kLowMemEnd, kImgEnd in *. lia.
Qed.

(* ======================= what a step that keeps every byte off pfw_X carries (pf_a5_k.v Section k) ======================= *)
Lemma pfw_keep_addr : forall v pos o n so sn lyc Sc Wc memc mdc (rd' : reader) q k,
  a5_G v pos -> pfw_ok o n so sn -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pfw_X v pos o n so sn a -> rd' a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rd' a <> None) ->
  sa_heap B lyc Sc q k -> sa_addr (rdW Wc memc) q k -> sa_addr rd' q k.
Proof.
intros v pos o n so sn lyc Sc Wc memc mdc rd' q k G Hok HAR Hin Hly HK HV (b & m & Hb & H1 & H2)
  (A0 & A1 & A2 & A3 & A4).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & _ & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m (proj1 Hm)) as [_ Hreq].
split; [exact A0|]. split; [exact A1|]. split; [exact A2|]. split.
- intros x Hx. destruct (A3 x Hx) as (s & Hs & Hsk). exists s. split; [|exact Hsk].
  unfold shadow_of_addr in *. rewrite HK; [exact Hs | |].
  + pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound x 8 x ltac:(lia) ltac:(lia)).
    unfold SHADOW_OFF. lia.
  + exact (pfw_heap_shadow_out v pos o n so sn lyc Sc Wc memc mdc b m x G Hok HAR Hin Hly Hb ltac:(lia)).
- intros Hn s Hs. apply HV. exact (A4 Hn s Hs).
Qed.
Lemma pfw_keep_hstr : forall v pos o n so sn lyc Sc Wc memc mdc (rd' : reader) q s,
  a5_G v pos -> pfw_ok o n so sn -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pfw_X v pos o n so sn a -> rd' a = rdW Wc memc a) ->
  sa_heap B lyc Sc q (Z.of_nat (length s) + 1) -> sa_str (rdW Wc memc) q s -> sa_str rd' q s.
Proof.
intros v pos o n so sn lyc Sc Wc memc mdc rd' q s G Hok HAR Hin Hly HK (b & m & Hb & H1 & H2) ((Hz & Hn) & Ht).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m (proj1 Hm)) as [_ Hreq].
pose proof asan_consts as (C1 & _).
split; [split; [|exact Hn]|].
- intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
  rewrite HK; [exact (Hz i Hi) | lia |].
  refine (pfw_heap_out v pos o n so sn lyc Sc Wc memc mdc b m _ G Hok HAR Hin Hly Hb _). lia.
- intros x Hx. pose proof (Z.mod_pos_bound (q + Z.of_nat (length s)) 8 ltac:(lia)).
  rewrite HK; [exact (Ht x Hx) | lia |].
  exact (pfw_heap_tail_out v pos o n so sn lyc Sc Wc memc mdc b m (q + Z.of_nat (length s)) x G Hok HAR Hin Hly Hb
    ltac:(lia) Hx).
Qed.
Lemma pfw_keep_lit : forall v pos o n so sn lyc Sc Wc memc mdc (Wc' : world SEGS) (memc' : word -> option byte) a s,
  a5_G v pos -> pfw_ok o n so sn -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pfw_X v pos o n so sn a -> rdW Wc' memc' a = rdW Wc memc a) ->
  sa_lit SEGS B (rdW Wc memc) a s -> sa_lit SEGS B (rdW Wc' memc') a s.
Proof.
intros v pos o n so sn lyc Sc Wc memc mdc Wc' memc' a s G Hok HAR Hin Hly HK (Ha & ((Hz & Hn) & Ht) & Hp & Hr & Hi).
split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
split; [split; [|exact Hn] | exact (sa_tail_of_romtail SEGS _ _ _ Hr)].
intros i Hi'. pose proof Hi' as Hl. rewrite length_app in Hl. cbn [length] in Hl.
destruct (Hi (a + Z.of_nat i) ltac:(lia)) as (Himg & _ & _).
pose proof (pa_img_range _ Himg) as Hrg. unfold kImgEnd in Hrg.
rewrite HK; [exact (Hz i Hi') | lia | exact (pfw_img_out v pos o n so sn lyc Sc Wc memc mdc _ G Hok HAR Hin Hly Himg)].
Qed.
Lemma pfw_keep_img_word : forall v pos o n so sn lyc Sc Wc memc mdc (rd' : reader) a,
  a5_G v pos -> pfw_ok o n so sn -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pfw_X v pos o n so sn a -> rd' a = rdW Wc memc a) ->
  (forall k, 0 <= k < 8 -> in_img SEGS (a + k)) -> rdword rd' a = rdword (rdW Wc memc) a.
Proof.
intros v pos o n so sn lyc Sc Wc memc mdc rd' a G Hok HAR Hin Hly HK Hi. apply rdword_ext. intros k Hk.
pose proof (pa_img_range _ (Hi k Hk)) as Hrg. unfold kImgEnd in Hrg.
apply HK; [lia | exact (pfw_img_out v pos o n so sn lyc Sc Wc memc mdc _ G Hok HAR Hin Hly (Hi k Hk))].
Qed.
Lemma pfw_keep_cat : forall v pos o n so sn lyc Sc Wc memc mdc (Wc' : world SEGS) (memc' : word -> option byte),
  a5_G v pos -> pfw_ok o n so sn -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pfw_X v pos o n so sn a -> rdW Wc' memc' a = rdW Wc memc a) ->
  sa_cat SEGS B (rdW Wc memc) catA -> sa_cat SEGS B (rdW Wc' memc') catA.
Proof.
intros v pos o n so sn lyc Sc Wc memc mdc Wc' memc' G Hok HAR Hin Hly HK (Hp & Hi & Hrows).
split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp.
split; [|exact (pfw_keep_lit v pos o n so sn lyc Sc Wc memc mdc Wc' memc' tp _ G Hok HAR Hin Hly HK Hl)].
rewrite (pfw_keep_img_word v pos o n so sn lyc Sc Wc memc mdc (rdW Wc' memc') _ G Hok HAR Hin Hly HK); [exact Htp|].
intros k Hk. assert (Hn' : Z.of_nat i < 11) by (unfold pin_spec.CAT_N in Hn; lia).
refine (proj1 (Hi (pin_spec.row_addr catA i + k) _)). unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES.
lia.
Qed.
Lemma pfw_keep_rod0 : forall v pos o n so sn lyc Sc Wc memc mdc (rd' : reader),
  a5_G v pos -> pfw_ok o n so sn -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pfw_X v pos o n so sn a -> rd' a = rdW Wc memc a) ->
  arodata_okP SEGS RLO_A RHI_A B (rdW Wc memc) -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof.
intros v pos o n so sn lyc Sc Wc memc mdc rd' G Hok HAR Hin Hly HK HR a Hro Ho He.
assert (Hlow : 0x10000 <= a < kImgEnd /\ ~ pfw_X v pos o n so sn a).
{ destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
  - assert (Hi : in_img SEGS a) by (exists sg; split; [exact Hsg | exact Hr]).
    pose proof (pa_img_range _ Hi) as Hrg.
    split; [exact Hrg | exact (pfw_img_out v pos o n so sn lyc Sc Wc memc mdc _ G Hok HAR Hin Hly Hi)].
  - unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Hr.
    assert (Hl : 0x10000 <= a < kImgEnd) by (unfold kImgEnd; lia).
    split; [exact Hl | exact (pfw_low_out v pos o n so sn lyc Sc Wc memc mdc _ G Hok HAR Hin Hly Hl)]. }
rewrite HK; [exact (HR a Hro Ho He) | unfold kImgEnd in *; lia | exact (proj2 Hlow)].
Qed.
Lemma pfw_keep_ssp : forall v pos o n so sn lyc Sc Wc memc mdc (rd' : reader),
  a5_G v pos -> pfw_ok o n so sn -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pfw_X v pos o n so sn a -> rd' a = rdW Wc memc a) ->
  sa_ssp (rdW Wc memc) gotwA guardA -> sa_ssp rd' gotwA guardA.
Proof.
intros v pos o n so sn lyc Sc Wc memc mdc rd' G Hok HAR Hin Hly HK (S1 & g & S2).
assert (KW : forall a, 0x10000 <= a -> a + 8 <= kImgEnd -> rdword rd' a = rdword (rdW Wc memc) a).
{ intros a H1 H2. apply rdword_ext. intros k Hk. apply HK; [unfold kImgEnd in *; lia|].
  apply (pfw_low_out v pos o n so sn lyc Sc Wc memc mdc _ G Hok HAR Hin Hly). unfold kImgEnd in *; lia. }
split; [rewrite KW; [exact S1 | unfold gotwA; lia | unfold gotwA, kImgEnd; lia]|].
exists g. rewrite KW; [exact S2 | unfold guardA; lia | unfold guardA, kImgEnd; lia].
Qed.
Lemma pfw_keep_obj0 : forall v pos o n so sn lyc Sc Wc memc mdc (Wc' : world SEGS) (memc' : word -> option byte),
  a5_G v pos -> pfw_ok o n so sn -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pfw_X v pos o n so sn a -> rdW Wc' memc' a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW Wc' memc' a <> None) ->
  pf_obj B v lyc Sc (rdW Wc memc) -> pf_obj B v lyc Sc (rdW Wc' memc').
Proof.
intros v pos o n so sn lyc Sc Wc memc mdc Wc' memc' G Hok HAR Hin Hly HK HV
  (T1 & T2 & T3 & C1 & C2 & CA & LI & RO & SS).
split; [exact (pfw_keep_hstr v pos o n so sn lyc Sc Wc memc mdc (rdW Wc' memc') _ _ G Hok HAR Hin Hly HK T3 T1)|].
split; [exact (pfw_keep_addr v pos o n so sn lyc Sc Wc memc mdc (rdW Wc' memc') _ _ G Hok HAR Hin Hly HK HV T3 T2)|].
split; [exact T3|].
split; [exact (pfw_keep_addr v pos o n so sn lyc Sc Wc memc mdc (rdW Wc' memc') _ _ G Hok HAR Hin Hly HK HV C2 C1)|].
split; [exact C2|].
split; [exact (pfw_keep_cat v pos o n so sn lyc Sc Wc memc mdc Wc' memc' G Hok HAR Hin Hly HK CA)|].
split; [intros x Hx; exact (pfw_keep_lit v pos o n so sn lyc Sc Wc memc mdc Wc' memc' _ _ G Hok HAR Hin Hly HK
  (LI x Hx))|].
split; [exact (pfw_keep_rod0 v pos o n so sn lyc Sc Wc memc mdc (rdW Wc' memc') G Hok HAR Hin Hly HK RO)|].
exact (pfw_keep_ssp v pos o n so sn lyc Sc Wc memc mdc (rdW Wc' memc') G Hok HAR Hin Hly HK SS).
Qed.
(* c's bytes and cur_name (F + 0x20, 16 bytes: the object lies after it) *)
Lemma pfw_keep_st : forall v pos o n so sn lyc Sc Wc memc mdc (rd' : reader) cf cur nm k,
  a5_G v pos -> pfw_ok o n so sn -> 0x30 <= o -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) ->
  lyc = p_ly v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pfw_X v pos o n so sn a -> rd' a = rdW Wc memc a) ->
  sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE ->
  pf_st v pos (rdW Wc memc) cf cur nm k -> pf_st v pos rd' cf cur nm k.
Proof.
intros v pos o n so sn lyc Sc Wc memc mdc rd' cf cur nm k G Hok Ho3 HAR Hin Hly HK (b & m & Hb & H1 & H2)
  ((bs & Hbs & Henc) & HC & (f & Hf & Hfe) & HN).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m (proj1 Hm)) as [_ Hreq].
pose proof asan_consts as (AC1 & _).
split; [|split; [exact HC|split; [|exact HN]]].
- exists bs. split; [|exact Henc]. intros i Hi. destruct Henc as [Hl _].
  rewrite HK; [exact (Hbs i Hi) | unfold seg_spec.SEG_C_SIZE in *; lia |].
  refine (pfw_heap_out v pos o n so sn lyc Sc Wc memc mdc b m _ G Hok HAR Hin Hly Hb _).
  unfold seg_spec.SEG_C_SIZE in *. lia.
- exists f. split; [|exact Hfe]. intros i Hi. destruct Hfe as [Hl _].
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
  rewrite HK; [exact (Hf i Hi) | unfold PF_O_CN; lia |].
  apply (pfw_frame_out v pos o n so sn _ G Hok); unfold PF_O_CN; lia.
Qed.

(* ======================= the cut state after the step ======================= *)
(* pf_base after a step or a call that kept every byte off pfw_X (and every visible byte visible), with the
   journal it returned at the same layout, the frame state changed at most (set_fs), the live blocks permuted, and
   the frame's shadow at the new reader for the new scope sc' (pf_a5_k.v a5_move0, at pfw_X) *)
Lemma pfw_base : forall o n so sn v pos lyc Sc Wc rX memc mdc sc Sc' Wc' rX' memc' mdc' sc',
  pfw_ok o n so sn ->
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc' Wc' memc' mdc' 0 ->
  (exists f, Sc' = set_fs f Sc) -> Permutation (ablocks B lyc Sc') (ablocks B lyc Sc) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pfw_X v pos o n so sn a -> rdW Wc' memc' a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW Wc' memc' a <> None) ->
  pf_rg rX' (a5_FI B v) ->
  pf_fsh (rdW Wc' memc') (pf_SH v pos) sc' ->
  pf_base B v pos lyc Sc' Wc' rX' memc' mdc' sc'.
Proof.
intros o n so sn v pos lyc Sc Wc rX memc mdc sc Sc' Wc' rX' memc' mdc' sc' Hok HB HJ' [f HSf] HPerm HK HV HRG HFSH.
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & _).
destruct HB as (HCX & HFI & HOBJ & HSL & _).
destruct HFI as (_ & _ & (f0 & HS0) & HP0 & HSV & HFL & HFRM & _).
split; [exact HCX|].
split.
{ split; [exact HJ'|]. split; [exact Hly|]. split; [exists f; rewrite HSf, HS0; apply a5_set_fs2|].
  split; [exact (Permutation_trans HPerm HP0)|].
  split; [exact (pfw_keep_saved v pos o n so sn _ _ _ G Hok HK HSV)|].
  split; [exact (pfw_keep_flag v pos o n so sn _ _ _ G Hok HK HFL)|].
  split; [exact HFRM | exact HRG]. }
split.
{ pose proof (pfw_keep_obj0 v pos o n so sn lyc Sc Wc memc mdc Wc' memc' G Hok HAR Hin Hly HK HV HOBJ)
    as (T1 & T2 & T3 & C1 & C2 & REST).
  assert (TR : forall q k, sa_heap B lyc Sc q k -> sa_heap B lyc Sc' q k).
  { intros q k (b & m & Hb & H1 & H2). exists b, m. split; [|lia].
    exact (Permutation_in _ (Permutation_sym HPerm) Hb). }
  exact (conj T1 (conj T2 (conj (TR _ _ T3) (conj C1 (conj (TR _ _ C2) REST))))). }
split; [exact (pfw_keep_sl v pos o n so sn _ _ G Hok HK _ (pf_a6_k.a6_PF_SL_offs v pos) HSL) | exact HFSH].
Qed.

(* ======================= A11a's instance: low146 and its three shadow cells ======================= *)
Lemma a11m_base : forall v pos lyc Sc Wc rX memc mdc sc Sc' Wc' rX' memc' mdc' sc',
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc' Wc' memc' mdc' 0 ->
  (exists f, Sc' = set_fs f Sc) -> Permutation (ablocks B lyc Sc') (ablocks B lyc Sc) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ a11m_X v pos a -> rdW Wc' memc' a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW Wc' memc' a <> None) ->
  pf_rg rX' (a5_FI B v) ->
  pf_fsh (rdW Wc' memc') (pf_SH v pos) sc' ->
  pf_base B v pos lyc Sc' Wc' rX' memc' mdc' sc'.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc Sc' Wc' rX' memc' mdc' sc' HB HJ' HSf HPerm HK HV HRG HFSH.
apply (pfw_base PF_O_L146 24 92 3 v pos lyc Sc Wc rX memc mdc sc Sc' Wc' rX' memc' mdc' sc' a11m_ok HB HJ' HSf HPerm);
  [| exact HV | exact HRG | exact HFSH].
intros a Ha Hn. apply HK; [exact Ha|]. rewrite a11m_X_pfw. exact Hn.
Qed.
(* the state every internal cut of A11a carries (pf_a11a_k.v a11_cx): pf_base at PF_SC_L146, the line, c and
   cur_name, the value in buf, slot 0xb0 *)
Lemma a11m_cx : forall n0 v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val Sc' Wc' rX' memc' mdc',
  a11_cx B n0 v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc' Wc' memc' mdc' 0 ->
  (exists f, Sc' = set_fs f Sc) -> Permutation (ablocks B lyc Sc') (ablocks B lyc Sc) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ a11m_X v pos a -> rdW Wc' memc' a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW Wc' memc' a <> None) ->
  pf_rg rX' (a5_FI B v) ->
  pf_fsh (rdW Wc' memc') (pf_SH v pos) PF_SC_L146 ->
  a11_cx B n0 v pos lyc Sc' Wc' rX' memc' mdc' cf nm o ln d gi vp val.
Proof.
intros n0 v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val Sc' Wc' rX' memc' mdc'
  (HB & HM & HST & HV1 & HIB & HSL) HJ' HSf HPerm HK HV HRG HFSH.
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & _).
pose proof (a5_text B _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & _ & _ & HC).
assert (HK' : forall a, 0 <= a < 2 ^ 64 -> ~ pfw_X v pos PF_O_L146 24 92 3 a -> rdW Wc' memc' a = rdW Wc memc a)
  by (intros a Ha Hn; apply HK; [exact Ha | rewrite a11m_X_pfw; exact Hn]).
split; [exact (a11m_base v pos lyc Sc Wc rX memc mdc PF_SC_L146 Sc' Wc' rX' memc' mdc' PF_SC_L146 HB HJ' HSf HPerm HK
  HV HRG HFSH)|].
split; [exact HM|].
split; [exact (pfw_keep_st v pos PF_O_L146 24 92 3 lyc Sc Wc memc mdc _ cf (Some gi) nm _ G a11m_ok
  ltac:(unfold PF_O_L146; lia) HAR Hin Hly HK' HC HST)|].
split; [exact (pfw_keep_buf v pos PF_O_L146 24 92 3 _ _ vp val G a11m_ok ltac:(unfold PF_O_L146; lia) HK' HIB HV1)|].
split; [exact HIB|].
exact (pfw_keep_sl v pos PF_O_L146 24 92 3 _ _ G a11m_ok HK' [(0xb0, seg_spec.rseg_addr (p_c v) gi)]
  ltac:(repeat constructor; cbn [fst]; lia) HSL).
Qed.
End e.
End f.
End d.
