(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/DMrecLRh.v (commit ce1a656b52b7, file sha256 6c0c51763def) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 5 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 3 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* F1 priming row R3 (re-hide at a secondary recycle): the STATES of Quarantine::DoRecycle (0x33cf8) for
   DMwalkIFRh.dorecycle_spec_rh, made from lib/A/DMrecL.v.  QuarantineCallback::Recycle's re-hide post
   (YGcfRehidePost.acall_post_x_rh) lets the hidden set grow inside dead_shadow_new ly S S' (the slots live at the
   call's entry S and dead at its exit S') and frames the view outside that set only, so the accumulated frame of
   DMrecL.accr changes in its two clauses that state them, and gains one:
   - [ar_wle]   wle_in (dead_shadow_new ly X0 X) W0 W in place of wle W0 W;
   - [ar_frame] the view kept outside dead_shadow_new ly X0 X too (one more premise, the last);
   - [ar_step]  YGcfRecStep.rec_step ly X0 X: the dead slots of the entry stay dead with their length, and a slot live
     at X is the same entry at X0.  Successive calls compose by it: the set of one call joins the walk's set (rs_left /
     rs_right below), so the walk's leaf names ONE set, from DoRecycle's entry to its exit.
   Every other clause of accr, and every clause of the five states (ostr, rcstr, rstr, cdstr, qstr -> *h), is
   DMrecL's, word for word.  A new file, so that DMrecL.v stays byte-unchanged.
   rule 24: proves function __sanitizer::Quarantine<__asan::QuarantineCallback, __asan::AsanChunk>::DoRecycle (states
   at the re-hide twins). *)
(* Theorem Labs, 2026-10-30 (a prior worker): the image-B (asan-ubsan) twin of lib/A/DMrecLRh.v at ddad1b506f1b, relocated by a Theorem Labs lane alreloc a5c53bb2bed4ad03 (every moved numeral a Quarantine::DoRecycle pc, +0x58) with the A twins A<r> renamed to the B twins Y<r>; the comment blocks above keep the A file's text and its A pcs. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YP09 YN3v YI04 YK04 YA0i YA0n YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m YF0x YFl1 YFeq YFeu YFf2 YFh9 YFhd.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif DGif0cgif. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DIfaceR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DMwalkIF. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ErrnoG MemnormT. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DMrecL. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YGcfRecStep.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The composition facts of the per-call set, from YGcfRecStep.rec_step alone.                                     *)
Section rs.
Variable ly : alayout.
Local Notation DSN := (YGcfRehidePost.dead_shadow_new ly).
Lemma rs_refl : forall S, YGcfRecStep.rec_step ly S S.
Proof. intros S. split; [intros r sm H; exists sm; split; [exact H | reflexivity] | intros r sm0 H _; exact H]. Qed.
Lemma rs_trans : forall S1 S2 S3, YGcfRecStep.rec_step ly S1 S2 -> YGcfRecStep.rec_step ly S2 S3 ->
YGcfRecStep.rec_step ly S1 S3.
Proof.
intros S1 S2 S3 [D12 E12] [D23 E23]. split.
- intros r sm H. destruct (D12 r sm H) as (sm2 & H2 & L2). destruct (D23 r sm2 H2) as (sm3 & H3 & L3).
  exists sm3. split; [exact H3 | rewrite L3; exact L2].
- intros r sm0 H L. exact (E12 r sm0 (E23 r sm0 H L) L).
Qed.
(* a slot dead at S2 stays dead at S3: the set from S1 to S2 lies in the set from S1 to S3 *)
Lemma rs_left : forall S1 S2 S3 a, YGcfRecStep.rec_step ly S2 S3 -> DSN S1 S2 a -> DSN S1 S3 a.
Proof.
intros S1 S2 S3 a [D23 _] (r & sm & sm0 & Hd & Hn & Hl & Hlen & Hr). destruct (D23 r sm Hd) as (sm' & Hd' & L).
exists r, sm', sm0. rewrite L. exact (conj Hd' (conj Hn (conj Hl (conj Hlen Hr)))).
Qed.
(* a slot live at S2 is the same entry at S1: the set from S2 to S3 lies in the set from S1 to S3
   (YGcfRehidePost.dead_shadow_new_mono_l, its premise from rec_step's index clause) *)
Lemma rs_right : forall S1 S2 S3 a, YGcfRecStep.rec_step ly S1 S2 -> DSN S2 S3 a -> DSN S1 S3 a.
Proof.
intros S1 S2 S3 a [_ E12]. apply YGcfRehidePost.dead_shadow_new_mono_l.
intros r sm0 Hn Hl. exists sm0. exact (conj (E12 r sm0 Hn Hl) (conj Hl eq_refl)).
Qed.
End rs.

(* the hidden set across two steps: the first grows in D1, the second in D2 *)
Lemma wle_in_join : forall (segs : list Segment) (D1 D2 : Z -> Prop) (W1 W2 W3 : world segs),
wle_in segs D1 W1 W2 -> wle_in segs D2 W2 W3 -> wle_in segs (fun a => D1 a \/ D2 a) W1 W3.
Proof.
intros segs D1 D2 W1 W2 W3 H12 H23 a Ha. destruct (H23 a Ha) as [H2 | Hz]; [|right; right; exact Hz].
destruct (H12 a H2) as [H1 | Hy]; [left; exact H1 | right; left; exact Hy].
Qed.

Section e.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variables (ly : alayout) (X0 : astate) (W0 : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Local Notation sp0 := (YFhd.sp0 regs0).
Local Notation sp1 := (YFhd.sp1 regs0).
Local Notation DRSTACK_X := DMwalkIF.DRSTACK_X.
Local Notation SYr := (DMrecL.SYr regs0).
Local Notation blen_ok := DMrecL.blen_ok.
(* DMrecL.accr at the re-hide twins (header). *)
Record accrh (X : astate) (W : world tfibsegs) (mem : word -> option byte) (md : Model) : Prop := {
ar_AR : ARXr (as_inst B) ly X W mem md;
ar_wle : wle_in tfibsegs (YGcfRehidePost.dead_shadow_new ly X0 X) W0 W;
ar_io : same_io md0 md;
ar_own : forall a, AOX ly X a -> AOX ly X0 a;
ar_frame : forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly X0 a -> ~ AOX ly X a -> ~ ascratch B DRSTACK_X regs0 a -> ~ (sp0 <= a < sp0 + 32) ->
  ~ YGcfRehidePost.dead_shadow_new ly X0 X a ->
  aview tfibsegs (w_H W) mem a = aview tfibsegs (w_H W0) mem0 a;
ar_pres : forall a, SYr a -> apresent (w_H W) mem a;
ar_inited : st_cache_inited X = true;
ar_raw : forall x : word, ~ AOX ly X0 (bv_unsigned x) -> ~ AOX ly X (bv_unsigned x) -> ~ ascratch B DRSTACK_X regs0 (bv_unsigned x) ->
  ~ (sp0 <= bv_unsigned x < sp0 + 32) -> mem x = mem0 x;
ar_ek : ErrnoG.errno_kept B mem0 mem;
ar_mk : MemnormT.memnorm_keep tfibsegs mem0 mem;
ar_step : YGcfRecStep.rec_step ly X0 X
}.
Local Notation common_regs := (YFhd.common_regs regs0).
Local Notation loop_regs := (YFhd.loop_regs regs0).
Local Notation frame_cells := (YFhd.frame_cells ly regs0).
Local Notation tmp_cells := (YFhd.tmp_cells ly regs0).
Local Notation batch_regs := (YFhd.batch_regs ly).
Local Notation zlen := (@YFhd.zlen _).
Local Notation hdra := (YFhd.hdra B ly).
(* the outer loop head 0x3483c *)
Record ostrh (X : astate) (rest : list batch) (lz qb : Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop := {
o_acc : accrh X W mem md;
o_drq : DRq X (flat_map b_items rest) (map b_self rest);
o_bl : blen_ok rest;
o_ne : rest <> [];
o_len : zlen rest < 2 ^ 40;
o_cregs : common_regs regs;
o_lregs : loop_regs regs;
o_a0 : getr regs 10 = w64 (zlen rest);
o_frame : frame_cells W mem;
o_tmp : tmp_cells W mem rest lz qb;
o_cells : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (batch_cells rest)
}.
(* the item loop's call of QuarantineCallback::Recycle (A_RChunk) *)
Record rcstrh (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (lz qb : Z)
(W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop := {
rc_acc : accrh X W mem md;
rc_drq : DRq X (its ++ flat_map b_items t) (b_self b :: map b_self t);
rc_bl : blen_ok t;
rc_items : exists done, b_items b = done ++ its /\ length done = i;
rc_ne : its <> [];
rc_blen : (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat;
rc_len : zlen t < 2 ^ 40;
rc_cregs : common_regs regs;
rc_lregs : loop_regs regs;
rc_bregs : batch_regs regs b;
rc_ra : getr regs 1 = w64 0x34888;
rc_a0 : getr regs 10 = w64 (sp1 + 8);
rc_a1 : forall k ks, its = k :: ks -> getr regs 11 = w64 (hdra k);
rc_s7 : getr regs 23 = w64 (ly_space ly + b_self b + 152 + 8 * Z.of_nat i);
rc_s9 : getr regs 25 = w64 (16 + Z.of_nat i);
rc_frame : frame_cells W mem;
rc_tmp : tmp_cells W mem t lz qb;
rc_cells : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (batch_cells (b :: t))
}.
(* the item loop's return point 0x34888 *)
Record rstrh (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (lz qb : Z)
(W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop := {
r_acc : accrh X W mem md;
r_drq : DRq X (its ++ flat_map b_items t) (b_self b :: map b_self t);
r_bl : blen_ok t;
r_items : exists done, b_items b = done ++ its /\ length done = i;
r_i : (1 <= i)%nat;
r_blen : (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat;
r_len : zlen t < 2 ^ 40;
r_cregs : common_regs regs;
r_lregs : loop_regs regs;
r_bregs : batch_regs regs b;
r_s7 : getr regs 23 = w64 (ly_space ly + b_self b + 144 + 8 * Z.of_nat i);
r_s9 : getr regs 25 = w64 (15 + Z.of_nat i);
r_frame : frame_cells W mem;
r_tmp : tmp_cells W mem t lz qb;
r_cells : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (batch_cells (b :: t))
}.
(* the call of CacheDealloc for the batch object (A_CDealloc), from the item loop's end or the count-0 arm *)
Record cdstrh (X : astate) (b : batch) (t : list batch) (lz qb : Z)
(W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop := {
cd_acc : accrh X W mem md;
cd_drq : DRq X (flat_map b_items t) (b_self b :: map b_self t);
cd_bl : blen_ok t;
cd_len : zlen t < 2 ^ 40;
cd_cregs : common_regs regs;
cd_lregs : loop_regs regs;
cd_ra : getr regs 1 = w64 0x348c0;
cd_a0 : getr regs 10 = w64 (ly_T ly + t_cache);
cd_a1 : getr regs 11 = w64 A_ALLOCATOR;
cd_a2 : getr regs 12 = w64 kBatchClass;
cd_a3 : getr regs 13 = w64 (ly_space ly + b_self b);
cd_frame : frame_cells W mem;
cd_tmp : tmp_cells W mem t lz qb;
cd_cells : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (batch_cells t)
}.
(* CacheDealloc's return point 0x348c0 *)
Record qstrh (X : astate) (t : list batch) (lz qb : Z)
(W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop := {
q_acc : accrh X W mem md;
q_drq : DRq X (flat_map b_items t) (map b_self t);
q_bl : blen_ok t;
q_len : zlen t < 2 ^ 40;
q_cregs : common_regs regs;
q_lregs : loop_regs regs;
q_frame : frame_cells W mem;
q_tmp : tmp_cells W mem t lz qb;
q_cells : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (batch_cells t)
}.
Definition OSTrh (X : astate) (rest : list batch) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs 0x3483c regs mem md /\ ostrh X rest lz qb W regs mem md.
Definition RCSTrh (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs A_RChunk regs mem md /\ rcstrh X b t its i lz qb W regs mem md.
Definition RSTrh (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs 0x34888 regs mem md /\ rstrh X b t its i lz qb W regs mem md.
Definition CDSTrh (X : astate) (b : batch) (t : list batch) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs A_CDealloc regs mem md /\ cdstrh X b t lz qb W regs mem md.
Definition QSTrh (X : astate) (t : list batch) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs 0x348c0 regs mem md /\ qstrh X t lz qb W regs mem md.

(* A released accumulated frame whose state is one step from the entry gives the twin (the walk's first state). *)
Lemma accrh_of : forall X W mem md,
DMrecL.accr B ARXr AOX ly X0 W0 regs0 mem0 md0 X W mem md -> YGcfRecStep.rec_step ly X0 X -> accrh X W mem md.
Proof.
intros X W mem md [aAR aWLE aIO aOWN aFR aPRS aINI aRAW aEK aMK] STP. constructor.
- exact aAR.
- intros a Ha. left. exact (aWLE a Ha).
- exact aIO.
- exact aOWN.
- intros a Ha N0 N1 NS NT _. exact (aFR a Ha N0 N1 NS NT).
- exact aPRS.
- exact aINI.
- exact aRAW.
- exact aEK.
- exact aMK.
- exact STP.
Qed.
Lemma OSTrh_of : forall X rest W c,
DMrecL.OSTr B ARXr AOX DRq ly X0 W0 regs0 mem0 md0 X rest W c -> YGcfRecStep.rec_step ly X0 X -> OSTrh X rest W c.
Proof.
intros X rest W c (lz & qb & regs & mem & md & Hc & [AC DQ BL NE LEN CR LR A0 FRc TM CE]) STP.
exists lz, qb, regs, mem, md. split; [exact Hc|].
constructor; [exact (accrh_of X W mem md AC STP) | exact DQ | exact BL | exact NE | exact LEN | exact CR | exact LR | exact A0
| exact FRc | exact TM | exact CE].
Qed.
End e.
End d.
