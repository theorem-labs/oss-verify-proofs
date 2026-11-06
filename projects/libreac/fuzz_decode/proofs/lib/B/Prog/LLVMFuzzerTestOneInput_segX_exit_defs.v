(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segX_exit_defs: the exit group's own cut points between +0x96c and +0xae0 of image B's
   LLVMFuzzerTestOneInput, and the facts every step of the group uses to carry the interface's frame invariant
   (dec_b_core of lib/B/Prog/LLVMFuzzerTestOneInput_segs.v) across a symbolic run or a call.
   The cut points follow the interface's state shape (an existential FP state, the configuration at the cut pc,
   dec_b_core, the blocks, the meter, the fake frame's spill slots and its shadow): ex_fr at +0xab8 / +0xac0 /
   +0xac8 (before free #2, before free #3, after both). *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YP09 YI00 YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr check_round_trip_cg
  LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* lib/Reusable/YM03.v:182-189 redefines lia / nia globally (context pruning and retries); this file uses the
   plain ones (YM03.v:179-180 lf_lia_orig / lf_nia_orig). *)
Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := decodesegsB0.
Local Abbreviation rd W mem := (mrestrict (w_H W) mem).

(* A cut point of the free steps: at DEC_A_LLVMF + X, journal count k, the caller's blocks plus bl, the meter
   spent / still available, the fake frame's three spill slots and its shadow (local live, bytes 0 / 4), and the
   register facts R the next step reads. *)
Definition ex_fr (X k : Z) (bl : list (Z * Z)) (spent rest : Z) (R : bvmap 5 word -> Prop) (cx : dctx)
    : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md',
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + X)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    dec_b_core B cx ly' S' W' regs' mem' md' k /\
    Permutation (ablocks B ly' S') (ablocks B (d_ly cx) (d_S cx) ++ bl) /\
    mo_le MT (d_S cx) S' spent /\ mo_ok MT S' rest /\
    dec_b_frs cx (aview segs (w_H W') mem') /\
    dec_b_fsh cx (aview segs (w_H W') mem') 0 4 /\
    R regs'.

(* +0xab8, before free #2, on both paths out of +0x96c (check_round_trip #2 and check_braid run, or the scan loop
   L6 showed the refusing call wrote nothing): the frame invariant at k <= 16 events, the caller's blocks plus the
   body copy res (s11) and the upstream buffer upb (s7), and a meter that still pays both frees within
   dec_spent_ae0. *)
Definition ex_ab8 (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' k (res upb spent rest : Z),
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + 0xab8)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    dec_b_core B cx ly' S' W' regs' mem' md' k /\ 0 <= k <= 16 /\
    Permutation (ablocks B ly' S') (ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_b_len (d_n cx))] ++
                                    [(upb, dec_b_uolen (CChan.upstream_result (dec_b_len (d_n cx))))]) /\
    mo_le MT (d_S cx) S' spent /\ 0 <= rest /\ mo_ok MT S' (mo_free MT + (mo_free MT + rest)) /\
    spent + mo_free MT + mo_free MT <= dec_spent_ae0 MT (d_n cx) /\
    dec_b_frs cx (aview segs (w_H W') mem') /\
    dec_b_fsh cx (aview segs (w_H W') mem') 0 4 /\
    YK11.getr regs' 23 = w64 upb /\ YK11.getr regs' 27 = w64 res.

Hypothesis LAWS : AR_laws segs B.

(* cgif lib/A/ACf6.v:84-103 ablocks_perm_twice, copied (segs := image B's): AR's blocks are pairwise disjoint and
   none is empty, so no block occurs twice in a list the live blocks are a permutation of. *)
Lemma ex_perm_twice : forall ly S W mem md l1 l2 x,
  AR segs B ly S W mem md -> Permutation (ablocks B ly S) (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros ly S W mem md l1 l2 x HAR HP H1 H2.
apply in_split in H1 as (a1 & a2 & E1). apply in_split in H2 as (c1 & c2 & E2). subst l1 l2.
assert (HP2 : Permutation (ablocks B ly S) (x :: x :: ((a1 ++ a2) ++ c1) ++ c2)).
{ eapply Permutation_trans; [exact HP|].
  eapply Permutation_trans. { apply Permutation_app; [apply Permutation_sym; apply (Permutation_middle a1 a2 x) | apply Permutation_refl]. }
  change ((x :: a1 ++ a2) ++ c1 ++ x :: c2) with (x :: ((a1 ++ a2) ++ (c1 ++ x :: c2))).
  apply perm_skip.
  replace ((a1 ++ a2) ++ (c1 ++ x :: c2)) with (((a1 ++ a2) ++ c1) ++ x :: c2) by (first [rewrite app_assoc; reflexivity | rewrite <- app_assoc; reflexivity]).
  change (x :: ((a1 ++ a2) ++ c1) ++ c2) with (x :: (((a1 ++ a2) ++ c1) ++ c2)).
  apply Permutation_sym. apply (Permutation_middle ((a1 ++ a2) ++ c1) c2 x). }
assert (Hx : In x (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HP2 | left; reflexivity]).
destruct x as [b m].
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hx) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (sep_blocks_perm segs B LAWS ly S W mem md _ _ _ HAR HP2) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
pose proof (req_size_pos m ltac:(lia)). lia.
Qed.

(* cgif lib/A/ACey.v:91-96 garr8_kept_aview, restated at image B's segments. *)
Lemma ex_garr8_kept : forall (H H' : word -> bool) (m m' : word -> option byte) base l,
  (forall i, 0 <= i < Z.of_nat (length l) -> aview segs H' m' (base + i) = aview segs H m (base + i)) ->
  garr8 segs (mrestrict H m) base l -> garr8 segs (mrestrict H' m') base l.
Proof.
intros H H' m m' base l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk8. rewrite <- (Hv k Hk8). apply (mbyte_of_aview segs).
replace (base + Z.of_nat j + Z.of_nat k) with (base + (Z.of_nat j + Z.of_nat k)) by lia. apply Hk. lia.
Qed.

(* The frame invariant across a step that kept the bytes it reads: the 13 saved words, the fake frame and its
   flag-pointer word, the payload; the journal and the registers come from the step. *)
Lemma ex_core_kept : forall cx ly S W regs mem md k ly2 S2 W2 regs2 mem2 md2 k2,
  dec_b_core B cx ly S W regs mem md k ->
  @ajournal rc dec_B_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly2 S2 W2 mem2 md2 k2 ->
  frames S2 = [(DEC_FCLASS, d_fpos cx)] ->
  YK11.getr regs2 8 = YK11.getr regs 8 -> YK11.getr regs2 9 = YK11.getr regs 9 -> spZ regs2 = spZ regs ->
  YK11.getr regs2 3 = YK11.getr regs 3 -> YK11.getr regs2 4 = YK11.getr regs 4 ->
  (forall a, d_sp0 cx - 104 <= a < d_sp0 cx -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  (forall a, d_F cx <= a < d_F cx + 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  (forall a, d_F cx <= a < d_F cx + 64 -> apresent (w_H W2) mem2 a) ->
  (0 < d_n cx -> In (d_p cx, d_n cx) (ablocks B ly2 S2)) ->
  (forall i, 0 <= i < Z.of_nat (length (d_pl cx)) ->
     aview segs (w_H W2) mem2 (d_p cx + i) = aview segs (w_H W) mem (d_p cx + i)) ->
  dec_b_core B cx ly2 S2 W2 regs2 mem2 md2 k2.
Proof.
intros cx ly S W regs mem md k ly2 S2 W2 regs2 mem2 md2 k2 Hcore HJ2 Hfr2 E8 E9 Esp E3 E4 Ksv KF PF Hpay2 Kpay.
destruct Hcore as (HJ & Hfrs & Hs0 & Hs1 & Hsp & Hsp1r & Hsp1al & Hgp & Htp & Hsaved & HF4096 & HFal & HFpres &
  HFLw & Hpay & Hgarr).
unfold dec_b_core.
split; [exact HJ2|]. split; [exact Hfr2|].
split; [rewrite E8; exact Hs0|]. split; [rewrite E9; exact Hs1|]. split; [rewrite Esp; exact Hsp|].
split; [exact Hsp1r|]. split; [exact Hsp1al|]. split; [rewrite E3; exact Hgp|]. split; [rewrite E4; exact Htp|].
split.
{ unfold dec_b_saved in *. rewrite Forall_forall in Hsaved |- *. intros o Hin. specialize (Hsaved o Hin).
  assert (Hb : 8 <= fst o <= 104).
  { unfold dec_b_saved_at in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst]; lia|]). destruct Hin. }
  rewrite <- Hsaved. apply rdword_ext. intros j Hj. apply Ksv. lia. }
split; [exact HF4096|]. split; [exact HFal|]. split; [exact PF|].
split; [rewrite <- HFLw; apply rdword_ext; intros j Hj; apply KF; lia|].
split; [exact Hpay2|].
apply (ex_garr8_kept (w_H W) (w_H W2) mem mem2); [|exact Hgarr].
rewrite length_map. exact Kpay.
Qed.

(* The frame-pointer chain every call of this function sees: s0 holds the entry sp from +0x03c on, and the frame
   record below it holds the caller's ra and s0 (dec_b_saved's first two words); the caller's own chain is empty
   (the slot pre's afn_pre ... []). cgif lib/A/ACf5.v:128 rt_ch, at this function's frame. *)
Definition ex_ch (cx : dctx) : list (Z * Z * Z) :=
  if d_sp0 cx + 16 <? ly_top (d_ly cx) then [(d_sp0 cx, raZ (d_regs cx), s0Z (d_regs cx))] else [].

(* cgif lib/A/ACf5.v:172-186 rt_chain, at the current state: the chain from sp1 through the entry sp. *)
Lemma ex_achain : forall cx ly S W regs mem md k,
  @achain rc (d_ly cx) (aview segs (w_H (d_W cx)) (d_mem cx)) (d_sp0 cx) (s0Z (d_regs cx)) [] ->
  astk_ok DEC_LLVMF_STK (d_ly cx) (d_sp0 cx) -> 4096 <= raZ (d_regs cx) ->
  dec_b_core B cx ly S W regs mem md k ->
  @achain rc ly (aview segs (w_H W) mem) (d_sp1 cx) (d_sp0 cx) (ex_ch cx).
Proof.
intros cx ly S W regs mem md k Hch Hstk Hra Hcore.
destruct Hcore as (HJ & _ & _ & _ & _ & Hsp1r & Hsp1al & _ & _ & Hsaved & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hstk as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Htop & _).
pose proof asan_consts as (C1 & _).
assert (FFS : DEC_LLVMF_STK = 32768) by reflexivity.
unfold dec_b_saved, dec_b_saved_at in Hsaved.
apply Forall_cons_iff in Hsaved as [Hra8 Hsaved]. apply Forall_cons_iff in Hsaved as [Hs16 _].
cbn [fst snd] in Hra8, Hs16.
apply (achain_ly_top (d_ly cx) ly); [exact Htop|].
unfold ex_ch. destruct (Z.ltb_spec (d_sp0 cx + 16) (ly_top (d_ly cx))) as [Hlt | Hge].
- apply (achain_push (d_ly cx) (aview segs (w_H (d_W cx)) (d_mem cx))); [exact Hch | lia | | | | exact Hra | lia | | lia | unfold d_sp0 in *; lia].
  + intros a Ha. apply F1; lia.
  + unfold raZ. exact Hra8.
  + unfold s0Z. exact Hs16.
  + rewrite Z.mod_divide in Hsp0al |- * by lia. destruct Hsp0al as [q Hq]. exists (2 * q). lia.
- left. split; [right; left; lia | reflexivity].
Qed.

(* What a call that keeps the caller's bytes outside its stack window and outside Er leaves of the bytes this
   function reads afterwards: the stack above the call's sp, the fake frame (still present) and its shadow. *)
Lemma ex_acall_keep : forall cx ly S W regs mem md k W2 mem2 slo shi (Er : Z -> Prop),
  dec_b_core B cx ly S W regs mem md k ->
  @acall_kept rc segs B ly S W mem W2 mem2 slo shi Er -> shi <= d_sp1 cx ->
  (forall a, d_F cx <= a < d_F cx + 64 -> ~ Er a) -> (forall a, d_SH cx <= a < d_SH cx + 8 -> ~ Er a) ->
  (forall a, d_sp1 cx <= a < d_sp0 cx -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) /\
  (forall a, d_F cx <= a < d_F cx + 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a /\ apresent (w_H W2) mem2 a) /\
  (forall a, d_SH cx <= a < d_SH cx + 8 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a).
Proof.
intros cx ly S W regs mem md k W2 mem2 slo shi Er Hcore HK Hshi HnF HnS.
destruct Hcore as (HJ & Hfrs & _ & _ & _ & Hsp1r & _ & _ & _ & _ & HF4096 & _ & HFpres & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi' & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & HlyF & _).
pose proof asan_consts as (C1 & _).
assert (FFS : DEC_LLVMF_STK = 32768) by reflexivity.
destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
assert (Hin0 : In (DEC_FCLASS, d_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx) by (unfold d_F, frame_addr; rewrite HlyF; reflexivity).
assert (FB : fs_frame_bytes DEC_FCLASS = 64) by reflexivity.
split; [|split].
- intros a Ha. apply K1; [lia | lia].
- intros a Ha.
  assert (Hv : aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a).
  { apply (K4 DEC_FCLASS (d_fpos cx) a Hin0); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA, FB; lia | exact (HnF a Ha)]. }
  split; [exact Hv|].
  destruct (frames_bounds segs B LAWS ly S W mem md DEC_FCLASS (d_fpos cx) HAR Hin0) as (Hb1 & Hb2 & _).
  rewrite EFA in Hb1. rewrite EFA, FB in Hb2.
  apply (apresent_transfer segs (w_H W) (w_H W2) mem mem2 a); [lia | | exact Hv | exact (HFpres a Ha)].
  apply (frm_img segs B LAWS ly S W mem md DEC_FCLASS (d_fpos cx) a HAR Hin0). rewrite EFA, FB. lia.
- intros a Ha. apply (K4 DEC_FCLASS (d_fpos cx) a Hin0); [right; unfold in_zr; cbn [fst snd]; rewrite EFA, FB; unfold d_SH in Ha; change (64 / 8) with 8; lia | exact (HnS a Ha)].
Qed.

(* The frame invariant at another memory and model that the journal reaches with the same bytes visible: a run
   that wrote nothing (only the model's materialization and the journal moved). *)
Lemma ex_core_md : forall cx ly S W regs mem md k mem' md',
  dec_b_core B cx ly S W regs mem md k ->
  @ajournal rc dec_B_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly S W mem' md' k ->
  mem' = mem ->
  dec_b_core B cx ly S W regs mem' md' k.
Proof.
intros cx ly S W regs mem md k mem' md' Hcore HJ' ->.
destruct Hcore as (HJ & REST). split; [exact HJ' | exact REST].
Qed.

(* The fake frame and its eight shadow bytes are this function's own bytes: a run may write them (YCbq.v awr_byte,
   the in_frames disjunct). *)
Lemma ex_awr_frame : forall cx ly S W regs mem md k a,
  dec_b_core B cx ly S W regs mem md k ->
  (d_F cx <= a < d_F cx + 64 \/ d_SH cx <= a < d_SH cx + 8) ->
  awr_byte DEC_LLVMF_STK (d_sp0 cx) [] (ablocks B (d_ly cx) (d_S cx)) (ablocks B ly S) ly
    [(DEC_FCLASS, d_fpos cx)] a.
Proof.
intros cx ly S W regs mem md k a Hcore Ha.
pose proof (proj1 Hcore) as HJ. pose proof HJ as (_ & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & HlyF & _).
assert (EFA : frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx) by (unfold d_F, frame_addr; rewrite HlyF; reflexivity).
assert (FB : fs_frame_bytes DEC_FCLASS = 64) by reflexivity.
right; right; right. exists DEC_FCLASS, (d_fpos cx). split; [left; reflexivity|].
unfold in_zr; cbn [fst snd]. rewrite EFA, FB. change (64 / 8) with 8. unfold d_SH in Ha. lia.
Qed.

(* A one-byte value the memory holds is the byte the view shows. *)
Lemma ex_aview_of_val1 : forall (H : word -> bool) (m : word -> option byte) a v,
  val_mem segs (mrestrict H m) a 1 v -> 0 <= v < 256 -> aview segs H m a = Some v.
Proof.
intros H m a v Hv Hr. pose proof (Hv 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
assert (L : bv_unsigned (Z_to_bv 8 (le_byte v 1 0)) = v).
{ unfold le_byte.
  change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  rewrite Z.mod_mod by lia. rewrite Z.mod_mod by lia. apply Z.mod_small. lia. }
unfold aview. cbv beta. rewrite H0. cbn [option_map]. f_equal. exact L.
Qed.

(* The read-only bytes the walks read (check_round_trip_cg.v DEC_RO_RD) lie in a read-only segment of the image. *)
Definition ex_rom_covers (a n : Z) : bool :=
  existsb (fun s : Segment => negb (seg_writable s) && (Z.of_N (seg_base s) <=? a) &&
    (a + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool segs.
Lemma ex_ro_rd_covered : forallb (fun r => ex_rom_covers (fst r) (snd r)) DEC_RO_RD = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ex_in_rom : forall a, dec_in_ro_rd a -> in_rom segs a /\ in_img segs a.
Proof.
intros a Ha. unfold dec_in_ro_rd in Ha. apply Exists_exists in Ha as ([lo n] & Hin & Hz).
pose proof ex_ro_rd_covered as Hc. rewrite forallb_forall in Hc. specialize (Hc _ Hin).
unfold ex_rom_covers in Hc. cbn [fst snd] in Hc. apply existsb_exists in Hc as (sg & Hsg & Hb).
apply andb_true_iff in Hb as [Hb Hhi]. apply andb_true_iff in Hb as [Hw Hlo].
apply negb_true_iff in Hw. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
unfold in_zr in Hz. cbn [fst snd] in Hz.
split; exists sg; (split; [exact Hsg|]); [split; [exact Hw|] |]; lia.
Qed.

(* The scoped read-only view check_round_trip asks (dec_rom_view_rd) at any state the slot's journal reaches, from
   the entry's rom_view (dec_b_rom), the journal's image clause (YCbq.v:362) and dec_ro_rd_scoped. *)
Lemma ex_rom_rd : forall cx STK own ly' S' W' mem' md' k,
  dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  rom_view segs (d_W cx) (d_mem cx) ->
  @ajournal rc dec_B_sink_head segs B STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    own ly' S' W' mem' md' k ->
  dec_rom_view_rd W' mem'.
Proof.
intros cx STK own ly' S' W' mem' md' k HO HE HR HJ a Ha.
destruct (dec_ro_rd_scoped B HO HE a Ha) as [Hno Hne]. destruct (ex_in_rom a Ha) as [Hr Hi].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a Hi Hno Hne); [exact (HR a Hr)|].
apply fp_spares_closed. intros Ho. exact (sink_closed_nil Ho).
Qed.
End d.

(* The facts of the slot pre (dec_b_base, lib/B/Prog/LLVMFuzzerTestOneInput_cg.v dec_lib_pre_x) the exit group
   reads, out of one destruct, so that a change of the pre's shape is one edit here. *)
Section e. Context {rc : YM05.RunCeil}.
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := decodesegsB0.
Lemma ex_base : forall cx,
  @dec_b_base rc asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  YK0s.ret_ok (YK11.getr (d_regs cx) 1) /\ raZ (d_regs cx) = RA_LLVMF /\
  YK11.getr (d_regs cx) 3 = w64 (as_gp B) /\ YK11.getr (d_regs cx) 4 = w64 (as_tp B) /\
  astk_ok DEC_LLVMF_STK (d_ly cx) (d_sp0 cx) /\
  @achain rc (d_ly cx) (aview segs (w_H (d_W cx)) (d_mem cx)) (d_sp0 cx) (s0Z (d_regs cx)) [] /\
  ((d_n cx = 0 /\ d_p cx = A_EMPTY) \/ (0 < d_n cx < 2 ^ 26 /\ In (d_p cx, d_n cx) (ablocks B (d_ly cx) (d_S cx)))) /\
  d_n cx = Z.of_nat (length (d_pl cx)) /\ frames (d_S cx) = [] /\
  st_nev (d_S cx) + DEC_EV_LIB <= EV_MAX /\ blocks_bytes (d_S cx) + DEC_LIVE_LIB <= LIVE_MAX /\
  asink_none segs tfib_K (mrestrict (w_H (d_W cx)) (d_mem cx)) (d_md cx) /\
  Fs.fs_sorted (m_fs (d_md cx)) = true /\
  ameta_inv segs tfib_K (d_ly cx) (mrestrict (w_H (d_W cx)) (d_mem cx)) (d_M cx) /\
  4096 <= raZ (d_regs cx).
Proof.
intros cx HB. unfold dec_b_base, dec_lib_pre_x in HB.
destruct HB as ((_ & Hret & Hra4 & Hgp & Htp & Hstk & _ & Hch & _) & Hra & _ & _ & Hpn & Hnlen & _ & Hfr & Hnev & Hlive &
  _ & _ & Hsink & _ & Hfss & Hmeta & _ & _).
exact (conj Hret (conj Hra (conj Hgp (conj Htp (conj Hstk (conj Hch (conj Hpn (conj Hnlen (conj Hfr (conj Hnev
  (conj Hlive (conj Hsink (conj Hfss (conj Hmeta Hra4)))))))))))))).
Qed.
End e.
