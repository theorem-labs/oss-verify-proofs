(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/DMdrainT7.v (commit ce1a656b52b7, file sha256 1e1b45345109) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainT7.v (commit 9259077395a9, Quarantine::Drain walk set; file sha256 11311498a3cd) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainT7.v at commit 257c1d78b5c, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), taken by path: no numeral of it names an image address that differs in fuzz_reply.asan-ubsan. *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the quarantine's batch objects are APART from everything Drain's
   entry walk writes (YFgj.WIN, YFgj.v:171-174: Drain's 80-byte frame, the image's quarantine header, the thread
   cache's header, and the global list's last next word) - except that last word itself.  So the walk's frame
   YFgj.MEQ keeps every batch cell but the relinked one, which is what the drain cut's batch cells rest on
   (DMdrainT3.lcn_keep, DMdrainT4.bcell_relink).
   rule 24: no function proved (kind: layout arithmetic; the lane's reuse search is the internal file LOOKUP-B1-drain.txt,
   `proof-index MergeBatches Recycle QuarantineCallback_Recycle Drain` 2026-10-29T23:07:48Z exit 0, rule-24
   check B1LookupCheck CONFIRM).
   Additive: no existing file is touched. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1w YFeq YFew YFeu YFey YFgj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DMdrainG1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The primary space is apart from the thread object and from the stack (layout_ok's lo_disj). *)
Lemma prim_apart : forall ly, layout_ok ly ->
(ly_prim ly + kPrimResvSize <= ly_T ly \/ ly_T ly + kThreadObjSize <= ly_prim ly) /\
(ly_prim ly + kPrimResvSize <= ly_stk_lo ly \/ ly_stk_hi ly <= ly_prim ly).
Proof.
intros ly LY. pose proof (lo_disj ly LY) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & _).
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PT DP].
do 5 (apply Forall_cons_iff in DP as [_ DP]). apply Forall_cons_iff in DP as [PSTK _].
unfold zdisjoint in PT, PSTK. cbn [fst snd] in PT, PSTK. split; lia.
Qed.

Section g.
Variables (W : world tfibsegs) (ly : alayout) (regs0 : bvmap 5 word) (X : astate).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Local Notation SB := (ly_space ly).
Local Notation gq := (st_qglobal X).
Local Notation G := (qc_list (st_qglobal X)).
Hypothesis LY : layout_ok ly.
Hypothesis HSP : ly_stk_lo ly + DSTACK <= sp0 /\ sp0 <= ly_stk_hi ly.
Hypothesis BADDR : forall b, In b (all_batches X) ->
  ly_prim ly <= SB + b_self b /\ SB + b_self b + kBatchBytes <= SB + kSpaceSize /\ (SB + b_self b) mod 8192 = 0 /\
  0 <= SB + b_self b < ASAN_CEIL.

Theorem batch_off_win : forall b, In b (all_batches X) -> forall a, SB + b_self b <= a < SB + b_self b + kBatchBytes ->
(forall lastb initr, rev G = lastb :: initr -> In lastb (all_batches X) -> b_self b <> b_self lastb \/ YFgj.GLv ly gq + 8 <= a) ->
~ YFgj.WIN ly regs0 gq a.
Proof.
intros b Hb a Ha HL. destruct (BADDR b Hb) as (A1 & A2 & A3 & A4).
pose proof (DMdrainG1.LYB2 ly LY) as (P1 & P2 & P3 & P4 & _).
pose proof (prim_apart ly LY) as [PT PS].
unfold YFgj.WIN, YFgj.WINF, YFgj.WINA. fold sp0.
ceil. unfold A_QUAR, A_ALLOCATOR, o_quar, ASAN_CEIL, kHighMemBeg, kSpaceSize, kPrimResvSize, kBatchBytes, kThreadObjSize, t_qc, DSTACK in *.
intros [H | [[H | [H | H]] | [Hne H]]].
- lia.
- lia.
- lia.
- lia.
- destruct (rev G) as [|lastb initr] eqn:ER.
  + apply Hne. rewrite <- (rev_involutive G), ER. reflexivity.
  + assert (Hin : In lastb (all_batches X)).
    { unfold all_batches. apply in_app_iff. right. rewrite <- (rev_involutive G), ER. cbn [rev]. apply in_app_iff. right. left. reflexivity. }
    assert (EG : YFgj.GLv ly gq = SB + b_self lastb) by (unfold YFgj.GLv; rewrite ER; reflexivity).
    destruct (BADDR lastb Hin) as (L1 & L2 & L3 & L4).
    destruct (HL lastb initr eq_refl Hin) as [NE | GE].
    * rewrite EG in H. lia.
    * lia.
Qed.
End g.
End f.
