(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/DMdrainU4.v (commit ce1a656b52b7, file sha256 54aca0eef3eb) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainU4.v (commit 9259077395a9, Quarantine::Drain walk set; file sha256 63c4d7ab56c5) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainU4.v at commit 257c1d78b5c, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (1 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the drain's cut relation DMiface.dmem_q (DMiface.v:117-124) at
   the RECYCLE cut - Recycle's call of DoRecycle (0x345c8) - the twin of DMdrainTC.dmem_q_cut, which states the
   same relation at the return cut.  Two walk stages stand between the entry memory and this cut: Drain's entry
   walk (frame off YFgj.WIN, presence inside it) and the dequeue loop (frame off DMdeq.DW, presence off the
   quarantine header), and both written sets are inside DMiface.dwin_q: the stack part inside the drain's stack
   window, the header parts inside qhdr, and a popped batch's next word inside that batch's cells.
   - [win_in_dwin] / [dw_in_dwin]: the two written sets are inside the cut's window.
   - [cut_frame]: the composed frame.
   - [cut_pres]: presence off the header, composed through the two stages; the walk's own presence clause
     covers the window, the frame covers the rest, and the loop's clause carries both to the cut.
   - [dmem_q_recyc]: DMiface.dmem_q at the recycle cut.
   No premise on the header's own presence: DMiface.dmem_q's presence clause is stated for 0 <= a < 2 ^ 64
   (DMiface.v:121-125, the dmiface-wrap narrowing), and in that range it excludes the header words.
   rule 24: no function proved (kind: the memory relation of a cut of segments already walked; the lane's reuse
   search is the internal file LOOKUP-B1-drain.txt, `proof-index MergeBatches Recycle QuarantineCallback_Recycle
   Drain` 2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM).
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DMwalkIF DMdrainG1 DMdrainU2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* presence depends only on the byte at the address *)
Lemma apresent_eq : forall (H : word -> bool) (m m2 : word -> option byte) a,
m2 (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> apresent H m a -> apresent H m2 a.
Proof. intros H m m2 a E [H1 [b Hb]]. split; [exact H1|]. exists b. rewrite E. exact Hb. Qed.

Section g.
Variable B : asyms.
Variables (W : world tfibsegs) (ly : alayout) (X S' : astate) (P : list batch).
Variables (regs0 : bvmap 5 word) (mem mem1 mem' : word -> option byte).
Variable inst : Z.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let sp1 : Z := sp0 - 80.
Let m' := mrestrict (w_H W) mem'.
Local Notation SB := (ly_space ly).
Local Notation G := (qc_list (st_qglobal X)).

Hypothesis Hinst : as_inst B = inst.
Hypothesis AQ : inst + o_quar = A_QUAR.
Hypothesis LY : layout_ok ly.
Hypothesis HSP : ly_stk_lo ly + YFeuC.DSTACK <= sp0 /\ sp0 <= ly_stk_hi ly.
Hypothesis BADDR : forall b, In b (all_batches X) ->
  ly_prim ly <= SB + b_self b /\ SB + b_self b + kBatchBytes <= SB + kSpaceSize /\ (SB + b_self b) mod 8192 = 0 /\
  0 <= SB + b_self b < ASAN_CEIL.
Hypothesis Hglast : forall lastb initr, rev G = lastb :: initr ->
  YFgj.GLv ly (st_qglobal X) = ly_space ly + b_self lastb /\ In lastb (all_batches X).
(* the temp list's batch objects are in the primary space (DMdrainU9.recyc_cut_in) *)
Hypothesis BADDR_P : forall b, In b P -> ly_prim ly <= addrb ly b /\ addrb ly b + kBatchBytes <= SB + kSpaceSize /\
  addrb ly b mod 8192 = 0 /\ 0 <= addrb ly b < ASAN_CEIL.
(* stage 1, the arm's walk from Drain's entry to the loop's head (DMdrainU9.recyc_cut_in): its written set
   [F1], inside the cut's window, and presence kept off the header *)
Variable F1 : Z -> Prop.
Hypothesis HM1 : forall x : word, ~ F1 (bv_unsigned x) -> mem1 x = mem x.
Hypothesis HF1 : forall a, F1 a -> dwin_q inst ly sp0 X S' P a.
Hypothesis HPR1 : forall a, 0 <= a < 2 ^ 64 -> ~ qhdr inst ly a -> apresent (w_H W) mem a -> apresent (w_H W) mem1 a.
(* stage 2: the dequeue loop (DMdeq.ATDR, DMdeq.v:198-199) *)
Hypothesis HM2 : forall x : word,
  ~ (sp1 <= bv_unsigned x < sp1 + 32) ->
  ~ (A_QUAR + 152 <= bv_unsigned x < A_QUAR + 156) ->
  ~ (A_QUAR + 160 <= bv_unsigned x < A_QUAR + 192) ->
  (forall b, In b P -> ~ (addrb ly b <= bv_unsigned x < addrb ly b + 8)) ->
  mem' x = mem1 x.
Hypothesis HPR2 : forall a, 0 <= a < 2 ^ 64 -> apresent (w_H W) mem1 a ->
  ~ (A_QUAR + 152 <= a < A_QUAR + 192) -> apresent (w_H W) mem' a.
(* the cut's own facts *)
Hypothesis HCELLS : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem')) (quar_cells S').
Hypothesis HMUT2 : val_mem tfibsegs m' (A_QUAR + 152 + 2) 2 0.

(* The dequeue loop's written set is inside the cut's window. *)
Lemma dw_in_dwin : forall a,
(sp1 <= a < sp1 + 32) \/ (A_QUAR + 152 <= a < A_QUAR + 156) \/ (A_QUAR + 160 <= a < A_QUAR + 192) \/
(exists b, In b P /\ addrb ly b <= a < addrb ly b + 8) ->
dwin_q inst ly sp0 X S' P a.
Proof.
intros a [H | [H | [H | (b & Hb & H)]]].
- left. unfold sp1, YFeuC.DSTACK in *. lia.
- right; left. unfold qhdr. rewrite AQ. left. lia.
- right; left. unfold qhdr. rewrite AQ. right; left. lia.
- right; right. exists b. split; [apply in_app_iff; right; apply in_app_iff; right; exact Hb | unfold addrb, zl in *; lia].
Qed.

Lemma cut_frame : forall x : word, ~ dwin_q inst ly sp0 X S' P (bv_unsigned x) -> mem' x = mem x.
Proof.
intros x HN.
rewrite (HM2 x).
- apply HM1. intros HW. apply HN. exact (HF1 _ HW).
- intros HD. apply HN. apply dw_in_dwin. left. exact HD.
- intros HD. apply HN. apply dw_in_dwin. right; left. exact HD.
- intros HD. apply HN. apply dw_in_dwin. right; right; left. exact HD.
- intros b Hb HD. apply HN. apply dw_in_dwin. right; right; right. exists b. split; [exact Hb | exact HD].
Qed.

Lemma cut_pres : forall a, 0 <= a < 2 ^ 64 -> ~ qhdr inst ly a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a.
Proof.
intros a RA HQ HP.
(* stage 1 *)
pose proof (HPR1 a RA HQ HP) as HP1.
(* stage 2: the dequeue loop.  The two words between the mutex word and the size field are in neither
   written set, so there the frame carries presence; everywhere else off the header the loop's own
   presence clause does. *)
destruct (DMdrainU2.zrange_dec (A_QUAR + 156) a (A_QUAR + 160)) as [HG|HG].
- apply (apresent_eq (w_H W) mem1 mem' a); [|exact HP1].
  pose proof (DMdrainG1.LYB2 ly LY) as (L1 & L2 & L3 & L4 & _).
  pose proof (DMdrainG1.STKR ly LY) as [K1 K2].
  pose proof HSP as [S1 S2].
  apply (HM2 (Z_to_bv 64 a)); rewrite (unsigned_lit_small a ltac:(lia)).
  + unfold sp1, sp0, A_QUAR, A_ALLOCATOR, o_quar, kHighMemBeg, YFeuC.DSTACK in *. lia.
  + lia.
  + lia.
  + intros b Hb HX. destruct (BADDR_P b Hb) as (B1 & B2 & B3 & B4).
    unfold addrb, A_QUAR, A_ALLOCATOR, o_quar, kHighMemBeg in *. lia.
- apply (HPR2 a RA HP1).
  intros HX. apply HQ. unfold qhdr. rewrite <- AQ in HX, HG.
  destruct (Z_lt_ge_dec a (inst + o_quar + 156)); [left; lia | right; left; lia].
Qed.

Theorem dmem_q_recyc : dmem_q B W inst ly sp0 X S' P mem mem'.
Proof.
unfold dmem_q. splits.
- exact cut_frame.
- exact HCELLS.
- exact cut_pres.
- match goal with |- val_mem _ _ ?a _ _ =>
    replace a with (A_QUAR + 152 + 2) by (rewrite <- AQ; unfold o_quar, o_q_cmutex; lia) end.
  exact HMUT2.
Qed.
End g.

(* The no-merge arm's stage 1 is Drain's entry walk, whose written set is YFgj.WIN (YFgj.at_L0): the window
   lies inside the cut's window, and the walk's presence clause (in high memory) with its frame gives presence
   off the header. *)
Section w.
Variable B : asyms.
Variables (W : world tfibsegs) (ly : alayout) (X S' : astate) (P : list batch).
Variables (regs0 : bvmap 5 word) (mem mem1 : word -> option byte).
Variable inst : Z.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Local Notation SB := (ly_space ly).
Local Notation G := (qc_list (st_qglobal X)).
Hypothesis AQ : inst + o_quar = A_QUAR.
Hypothesis LY : layout_ok ly.
Hypothesis HSP : ly_stk_lo ly + YFeuC.DSTACK <= sp0 /\ sp0 <= ly_stk_hi ly.
Hypothesis BADDR : forall b, In b (all_batches X) ->
  ly_prim ly <= SB + b_self b /\ SB + b_self b + kBatchBytes <= SB + kSpaceSize /\ (SB + b_self b) mod 8192 = 0 /\
  0 <= SB + b_self b < ASAN_CEIL.
Hypothesis Hglast : forall lastb initr, rev G = lastb :: initr ->
  YFgj.GLv ly (st_qglobal X) = ly_space ly + b_self lastb /\ In lastb (all_batches X).
Hypothesis HM1w : forall x : word, ~ YFgj.WIN ly regs0 (st_qglobal X) (bv_unsigned x) -> mem1 x = mem x.
Hypothesis HWP1w : forall a, YFgj.WIN ly regs0 (st_qglobal X) a -> kHighMemBeg <= a -> apresent (w_H W) mem1 a.

(* Drain's entry window is inside the cut's window. *)
Lemma win_in_dwin : forall a, YFgj.WIN ly regs0 (st_qglobal X) a -> dwin_q inst ly sp0 X S' P a.
Proof.
intros a HW. unfold dwin_q, qhdr, bcellw. unfold YFgj.WIN, YFgj.WINF, YFgj.WINA in HW. fold sp0 in HW.
destruct HW as [HW | [[HW | [HW | HW]] | [Hne HW]]].
- left. unfold YFeuC.DSTACK. lia.
- right; left; left. rewrite AQ. lia.
- right; left; right; left. rewrite AQ. lia.
- right; left; right; right. lia.
- destruct (rev G) as [|lastb initr] eqn:ER.
  + exfalso. apply Hne. rewrite <- (rev_involutive G), ER. reflexivity.
  + destruct (Hglast lastb initr eq_refl) as [EG HIN].
    right; right. exists lastb. split.
    * apply in_app_iff. left. exact HIN.
    * rewrite EG in HW. unfold zl. lia.
Qed.

(* the part of Drain's window that is NOT the quarantine's header is in high memory *)
Lemma win_hi : forall a, YFgj.WIN ly regs0 (st_qglobal X) a -> ~ qhdr inst ly a -> kHighMemBeg <= a.
Proof.
intros a HW HQ. pose proof (DMdrainG1.LYB2 ly LY) as (P1 & _ & _ & _ & _ & _ & _ & _ & K9).
pose proof HSP as [S1 S2].
unfold YFgj.WIN, YFgj.WINF, YFgj.WINA, qhdr in *. fold sp0 in HW.
destruct HW as [HW | [[HW | [HW | HW]] | [Hne HW]]].
- unfold YFeuC.DSTACK in *. lia.
- exfalso. apply HQ. left. rewrite AQ. lia.
- exfalso. apply HQ. right; left. rewrite AQ. lia.
- exfalso. apply HQ. right; right. lia.
- destruct (rev G) as [|lastb initr] eqn:ER.
  + exfalso. apply Hne. rewrite <- (rev_involutive G), ER. reflexivity.
  + destruct (Hglast lastb initr eq_refl) as [EG HIN]. destruct (BADDR lastb HIN) as (A1 & A2 & A3 & A4).
    rewrite EG in HW. unfold kBatchBytes in *. lia.
Qed.

Lemma pres1_of_win : forall a, 0 <= a < 2 ^ 64 -> ~ qhdr inst ly a -> apresent (w_H W) mem a -> apresent (w_H W) mem1 a.
Proof.
intros a RA HQ HP.
destruct (DMdrainU2.win_dec ly regs0 (st_qglobal X) a) as [HW|HW].
- apply (HWP1w a HW). exact (win_hi a HW HQ).
- apply (apresent_eq (w_H W) mem mem1 a); [|exact HP].
  apply (HM1w (Z_to_bv 64 a)). rewrite (unsigned_lit_small a ltac:(lia)). exact HW.
Qed.
End w.
End f.
