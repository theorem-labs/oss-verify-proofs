(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: region_kept_tcj_stack and region_kept_tcj_frame are the text of lib/A/ACem.v's
   region_kept_ownframe_aj (copied there from projects/libreac/fuzz_knock/proofs/lib/A/ACem.v) with the call's acall_kept
   replaced by a callee's tcj_kept (lib/A/Prog/CodecCJ.v), cpw_apresent_of_writable that of lib/A/AE7f.v's
   apresent_of_writable; the re-seat in cpw_call_reseat and cpw_rebase is the text of lib/A/AWalkFw2.v's reseatL (copied
   there from projects/libreac/fuzz_knock/proofs/lib/A/AWalkFw2.v) with the environment equation kept for env_agree,
   cpw_kept_std that of lib/A/AWalkFw1.v's aconstsF with the region_kept_val cases of
   projects/reac-pw/fuzz_qdisc/proofs/lib/A/QPgMain3.v:186-194, and cpw_leaf that of lib/A/Prog/CPgWalk.v's cw_leaf with the
   state's layout, astate and model taken through the calls' chain; for libdiginet/fuzz_codec's ASan build (image A).
   cpw_call, cpw_entry, cpw_kept_run, cpw_io, cpw_keep and cpw_sp_off are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgWalkCall.v; 414 of its 450 lines of code are new or changed and 242 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/check_text_counter_A_lib.v, with its module paths and module names changed; 184 of its 241 lines of code are new or changed and 393 lines of the source are left out. *)
(* The facts every segment of check_text_counter's walk in image B takes from a boundary
   (check_text_counter_B_inv.v): the stack of the call, the walk's own frame, the freshness of the frame's bytes and
   of their shadow, the image tables a callee reads at a later state, and the lengths of the two counter texts. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU CPgWalkKeptU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkFrameU check_text_scribble_B_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_counter_B_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- the two counter texts: a 0 result has eight digits -------------------------------------------------------- *)
Lemma cc_ct2_len : forall n s dot k i seg d r seg' d', ct2_go n s dot i k seg d = (r, seg', d') -> r = 0 ->
  length seg' = (length seg + k)%nat.
Proof.
intros n s dot k. induction k as [|k IH]; intros i seg d r seg' d' H Hr; cbn [ct2_go] in H.
- injection H as <- <- <-. lia.
- destruct ((0 <=? i - (8 - n)) && negb (nth (Z.to_nat (i - (8 - n))) dot 0 =? 0)).
  + destruct (i =? 7).
    * injection H as <- _ _. unfold E_RANGE in Hr. lia.
    * rewrite (IH _ _ _ _ _ _ H Hr), length_app. cbn [length]. lia.
  + rewrite (IH _ _ _ _ _ _ H Hr), length_app. cbn [length]. lia.
Qed.
Lemma cc_lib_len : forall tb r s d, counter_text_spec tb = (r, s, d) -> r = 0 -> length s = 8%nat.
Proof.
intros tb r s d H Hr. unfold counter_text_spec in H.
destruct (ct1_lib tb 0 [] (repeat 0 8)) as [[[n s0] dot]|].
- exact (cc_ct2_len n s0 dot 8 0 [] 0 r s d H Hr).
- injection H as <- _ _. unfold E_RANGE in Hr. lia.
Qed.
Lemma cc_owed_len : forall tb r s d, owed_counter_text_spec tb = (r, s, d) -> r = 0 -> length s = 8%nat.
Proof.
intros tb r s d H Hr. unfold owed_counter_text_spec in H.
destruct (ct1_owe tb 0 [] (repeat 0 8)) as [[[n s0] dot]|].
- exact (cc_ct2_len n s0 dot 8 0 [] 0 r s d H Hr).
- injection H as <- _ _. unfold E_RANGE in Hr. lia.
Qed.

(* ---- the image tables ------------------------------------------------------------------------------------------ *)
(* a byte of the read-only window is a byte of the image *)
Lemma cc_ro_img : forall a, in_roP tfibsegs CB_RLO CB_RHI a -> in_img tfibsegs a.
Proof.
intros a [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr]|].
unfold in_img. eexists. split; [right; right; left; reflexivity|].
match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in let h := eval vm_compute in sz in
change lo with l; change sz with h end. unfold CB_RLO, CB_RHI in Hgot. lia.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).
(* The tables a call reads, at a later state and a deeper window, for a sub-list of the rows. *)
Lemma cc_cimg_up : forall B lyc Sc (W : world tfibsegs) memc W2 mem2 T sp Ew,
  tcj_kept tfibsegs B T lyc Sc W memc W2 mem2 sp Ew ->
  forall spc Tc sp' T' l l', cimg_rd tfibsegs B CB_RLO CB_RHI W memc spc Tc l ->
  spc - Tc <= sp' - T' -> sp' <= spc -> incl l' l -> cimg_rd tfibsegs B CB_RLO CB_RHI W2 mem2 sp' T' l'.
Proof.
intros B lyc Sc W memc W2 mem2 T sp Ew (_ & _ & K3 & _) spc Tc sp' T' l l' (HR & HF) Hw Hs Hinc.
split.
- intros a Hro Ho He. rewrite (K3 a (cc_ro_img a Hro) Ho He). exact (HR a Hro Ho He).
- apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HF r (Hinc r Hr)) as (Hi & Hc).
  split; [exact Hi|]. destruct Hc as (H1 & H2 & H3 & H4 & H5 & H6 & H7).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  split; [unfold coff_win in *; lia|]. split; [exact H6 | exact H7].
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables SEG7TBL GLYPHA : Z.
Variable ROSTRS : list (Z * Z).
Hypothesis LAWS : AR_laws tfibsegs B.

(* The stack of the call: the entry sp, the realigned sp1, the window. *)
Lemma cc_stack : forall g, cc_pre B SEG7TBL GLYPHA ROSTRS g ->
  alloc_ceiling <= cc_sp g - 8384 /\ cc_sp g <= 2 ^ 47 /\ 2 ^ 46 + 8384 <= cc_sp g /\
  cc_sp g mod 16 = 0 /\ cc_sp g - 176 <= cc_sp1 g <= cc_sp g - 160 /\ cc_sp1 g mod 32 = 0 /\
  cc_sp0 g - cc_STK g <= cc_sp g - 8384 /\ cc_sp g <= cc_sp0 g.
Proof.
intros g Hpre. pose proof Hpre as (HE & _).
pose proof (cw_entry_stack B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TB_check_text_counter HE
  ltac:(unfold TB_check_text_counter, ESTACK; lia)) as (Hceil & H47 & H46 & Hal & _).
pose proof HE as (_ & _ & _ & _ & _ & _ & Hwin & Hwhi & _).
assert (TT : TB_check_text_counter = 8384) by reflexivity. rewrite TT in *.
unfold cc_sp1. fold (cc_sp g) in *. unfold spZ in *. fold (cc_sp g) in *.
destruct (sp1_facts (cc_sp g - 160) ltac:(lia) ltac:(rewrite <- Zminus_mod_idemp_l, Hal; reflexivity))
  as (Hr & Ha32 & _).
split; [exact Hceil|]. split; [exact H47|]. split; [exact H46|]. split; [exact Hal|].
split; [lia|]. split; [exact Ha32|]. split; assumption.
Qed.

(* want[8] at F + 32: its one granule of shadow is 0 *)
Lemma cc_want_bs : forall (H : word -> bool) (m : word -> option byte) F, F mod 64 = 0 -> 0 <= F ->
  garr8 tfibsegs (mrestrict H m) (SB + F / 8) BS_FRAME_SHADOW ->
  block_shadow (aview tfibsegs H m) SHADOW_OFF (F + 32) 8.
Proof.
intros H m F HF HF0 Hsh.
pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF, Z.add_0_r in D. set (k := F / 64) in *.
assert (Hk : 0 <= k) by (subst k; apply Z.div_pos; lia).
assert (EF8 : F / 8 = 8 * k) by (rewrite D; replace (64 * k) with ((8 * k) * 8) by lia; apply Z.div_mul; lia).
split; [rewrite D; replace (64 * k + 32) with ((8 * k + 4) * 8) by lia; apply Z_mod_mult|].
split; [lia|].
intros i Hi. change ((8 + 7) / 8) with 1 in Hi. assert (i = 0) by lia. subst i.
replace (if 0 <? 8 / 8 then 0 else 8 mod 8) with 0 by reflexivity.
assert (Es : shadow_of_addr SHADOW_OFF (F + 32) + 0 = SB + F / 8 + 4).
{ unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF. rewrite EF8. rewrite D.
  replace (64 * k + 32) with ((8 * k + 4) * 8) by lia. rewrite Z.div_mul by lia. lia. }
rewrite Es. destruct (Hsh 4%nat ltac:(cbn; lia)) as (V4 & _).
cbn [nth BS_FRAME_SHADOW Z.of_nat] in V4.
exact (aview_of_val_mem1 tfibsegs H m _ _ V4 ltac:(lia)).
Qed.

(* What every boundary carries, at a later state whose registers of cc_common are the same and whose bytes of the
   save area, the flag word, the frame's shadow and the spill slot 24(s1) are the same. *)
Lemma cc_common_keep : forall g pos regs2 mem2 (W2 : world tfibsegs) regs3 mem3 (W3 : world tfibsegs),
  cc_common g pos regs2 mem2 W2 ->
  getr regs3 8 = getr regs2 8 -> getr regs3 2 = getr regs2 2 -> getr regs3 9 = getr regs2 9 ->
  getr regs3 3 = getr regs2 3 -> getr regs3 4 = getr regs2 4 -> getr regs3 25 = getr regs2 25 ->
  getr regs3 22 = getr regs2 22 -> getr regs3 26 = getr regs2 26 -> getr regs3 24 = getr regs2 24 ->
  getr regs3 21 = getr regs2 21 -> getr regs3 20 = getr regs2 20 ->
  (forall a, (cc_sp g - 104 <= a < cc_sp g) \/ (cc_F g pos + 56 <= a < cc_F g pos + 64) \/
     (SB + cc_F g pos / 8 <= a < SB + cc_F g pos / 8 + 8) \/ (cc_sp1 g + 24 <= a < cc_sp1 g + 32) ->
     aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
  cc_common g pos regs3 mem3 W3.
Proof.
intros g pos regs2 mem2 W2 regs3 mem3 W3 HC E8 E2 E9 E3 E4 E25 E22 E26 E24 E21 E20 KE.
destruct HC as (R8 & R2 & R9 & R3 & R4 & R25 & R22 & R26 & R24 & R21 & R20 & V1 & V2 & V3 & V4 & V5 & V6 & V7 &
  V8 & V9 & V10 & V11 & V12 & V13 & Hfl & Hsh & Hsp).
split; [rewrite E8; exact R8|]. split; [rewrite E2; exact R2|]. split; [rewrite E9; exact R9|].
split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|]. split; [rewrite E25; exact R25|].
split; [rewrite E22; exact R22|]. split; [rewrite E26; exact R26|]. split; [rewrite E24; exact R24|].
split; [rewrite E21; exact R21|]. split; [rewrite E20; exact R20|].
repeat (split; [apply (cw_val_mem_kept (w_H W2) (w_H W3) mem2 mem3); [intros x Hx; apply KE; left; cbn in Hx; lia | assumption]|]).
split; [|split].
- unfold rdword in *.
  rewrite (KE (cc_F g pos + 56)), (KE (cc_F g pos + 56 + 1)), (KE (cc_F g pos + 56 + 2)), (KE (cc_F g pos + 56 + 3)),
    (KE (cc_F g pos + 56 + 4)), (KE (cc_F g pos + 56 + 5)), (KE (cc_F g pos + 56 + 6)), (KE (cc_F g pos + 56 + 7))
    by (right; left; lia).
  exact Hfl.
- intros j Hj. destruct (Hsh j Hj) as (Vj & Bj). split; [|exact Bj].
  apply (cw_val_mem_kept (w_H W2) (w_H W3) mem2 mem3 _ 1 _); [|exact Vj].
  intros x Hx. cbn [length BS_FRAME_SHADOW] in Hj. apply KE. right; right; left. cbn in Hx. lia.
- apply (cw_val_mem_kept (w_H W2) (w_H W3) mem2 mem3 _ 8 _); [|exact Hsp].
  intros x Hx. apply KE. right; right; right. cbn in Hx. lia.
Qed.

(* The walk's own frame at a boundary state. *)
Lemma cc_frame : forall g pos ly2 S2 W2 mem2 md2, cc_pre B SEG7TBL GLYPHA ROSTRS g ->
  ajournal tfibsegs B (cc_STK g) (cc_sp0 g) (cc_FP g) (cc_ly g) (cc_S g) (cc_W0 g) (cc_mem0 g) (cc_md0 g)
    ((0, pos) :: cc_own g) ly2 S2 W2 mem2 md2 (cc_k g) ->
  frames S2 = (0, pos) :: frames (cc_Sc g) /\
  (forall c p, frame_addr ly2 c p = frame_addr (cc_lyc g) c p) /\
  (forall c p, flag_addr ly2 c p = flag_addr (cc_lyc g) c p) /\
  4096 <= cc_F g pos /\ cc_F g pos + 64 <= alloc_ceiling /\ cc_F g pos mod 64 = 0 /\ in_app (cc_F g pos) 64 /\
  (forall a, cc_F g pos <= a < cc_F g pos + 64 -> apresent (w_H W2) mem2 a).
Proof.
intros g pos ly2 S2 W2 mem2 md2 Hpre HJ.
pose proof Hpre as ((HJc & _) & _).
pose proof HJc as (_ & Hlyc & _ & _ & _ & Hfrsc & _).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & _).
assert (EF : ly_F ly2 = ly_F (cc_lyc g)).
{ destruct Hly2 as (_ & _ & _ & _ & _ & E1 & _). destruct Hlyc as (_ & _ & _ & _ & _ & E2 & _). rewrite E1, E2. reflexivity. }
assert (Efa : forall c p, frame_addr ly2 c p = frame_addr (cc_lyc g) c p) by (intros c p; unfold frame_addr; rewrite EF; reflexivity).
assert (Efl : forall c p, flag_addr ly2 c p = flag_addr (cc_lyc g) c p) by (intros c p; unfold flag_addr; rewrite EF; reflexivity).
assert (Hfr : frames S2 = (0, pos) :: frames (cc_Sc g)) by (rewrite Hfrs2, Hfrsc; reflexivity).
assert (Hin : In (0, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 mem2 md2 0 pos HAR2 Hin) as (H4096 & Hceil & Happ).
destruct (frame_al64 tfibsegs B ly2 S2 W2 mem2 md2 0 pos HAR2 Hin) as (H64 & _ & _).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 0 pos HAR2 Hin) as (_ & _ & HFp & _).
change (fs_frame_bytes 0) with 64 in Hceil, Happ, HFp.
rewrite Efa in H4096, Hceil, Happ, H64, HFp. fold (cc_F g pos) in H4096, Hceil, Happ, H64, HFp.
split; [exact Hfr|]. split; [exact Efa|]. split; [exact Efl|].
split; [exact H4096|]. split; [exact Hceil|]. split; [exact H64|]. split; [exact Happ|].
intros a Ha. exact (proj1 (HFp a Ha)).
Qed.

(* The bytes of the walk's own frame and of its shadow are fresh for the call state. *)
Lemma cc_fresh : forall g pos ly2 S2 W2 mem2 md2 a, cc_pre B SEG7TBL GLYPHA ROSTRS g ->
  ajournal tfibsegs B (cc_STK g) (cc_sp0 g) (cc_FP g) (cc_ly g) (cc_S g) (cc_W0 g) (cc_mem0 g) (cc_md0 g)
    ((0, pos) :: cc_own g) ly2 S2 W2 mem2 md2 (cc_k g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (cc_lyc g) (cc_Sc g)) ->
  (cc_F g pos <= a < cc_F g pos + 64) \/ (SB + cc_F g pos / 8 <= a < SB + cc_F g pos / 8 + 8) ->
  cw_fresh B (cc_lyc g) (cc_Sc g) a.
Proof.
intros g pos ly2 S2 W2 mem2 md2 a Hpre HJ HP Ha.
destruct (cc_frame g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (Hfr & Efa & _ & _ & _ & _ & _ & _).
pose proof HJ as (HAR2 & _).
apply (cw_fresh_own B LAWS (cc_lyc g) (cc_Sc g) ly2 S2 W2 mem2 md2 0 pos a HAR2 Hfr HP Efa).
assert (HSB : shadow_addr (cc_F g pos) = SB + cc_F g pos / 8)
  by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; reflexivity).
unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa. fold (cc_F g pos). rewrite HSB.
change (fs_frame_bytes 0) with 64. change (64 / 8) with 8. destruct Ha; [left | right]; lia.
Qed.

(* a byte of an object of the call state is not a fresh byte *)
Lemma cc_obj_not_fresh : forall lyc Sc q n a, cobj_ok B lyc Sc q n -> q <= a < q + n -> cw_fresh B lyc Sc a -> False.
Proof.
intros lyc Sc q n a Hc Ha (_ & _ & Hfb & Hff).
destruct Hc as [(bb & m & Hin & H1 & H2) | (cid & p & Hin & H1 & H2)].
- exact (Hfb bb m (a - bb) Hin ltac:(lia) ltac:(lia)).
- apply (proj1 (Hff cid p Hin)). unfold in_zr, frame_rng. cbn [fst snd]. lia.
Qed.
(* an object of the call state is apart from a range of fresh bytes *)
Lemma cc_fresh_disj : forall lyc Sc q n x m, cobj_ok B lyc Sc q n ->
  (forall a, x <= a < x + m -> cw_fresh B lyc Sc a) -> 0 < n -> 0 < m -> x + m <= q \/ q + n <= x.
Proof.
intros lyc Sc q n x m Hc Hf Hn Hm.
destruct (Z_le_gt_dec (x + m) q) as [H|H]; [left; exact H|].
destruct (Z_le_gt_dec (q + n) x) as [H2|H2]; [right; exact H2|].
exfalso. exact (cc_obj_not_fresh lyc Sc q n (Z.max q x) Hc ltac:(lia) (Hf (Z.max q x) ltac:(lia))).
Qed.
(* an object of the call state is one of a later state with the call state's blocks and more frames *)
Lemma cc_cobj_mono : forall lyc Sc ly4 S4 q n, cobj_ok B lyc Sc q n ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly4 S4)) ->
  (forall c p, In (c, p) (frames Sc) -> In (c, p) (frames S4)) ->
  (forall c p, frame_addr ly4 c p = frame_addr lyc c p) -> cobj_ok B ly4 S4 q n.
Proof.
intros lyc Sc ly4 S4 q n [(b & m & Hin & H1 & H2) | (c & p & Hin & H1 & H2)] Hb Hf Efa.
- left. exists b, m. split; [exact (Hb b m Hin)|]. lia.
- right. exists c, p. split; [exact (Hf c p Hin)|]. rewrite Efa. lia.
Qed.
(* A callee's post keeps the save area, the spill slot 24(s1) (above its window, off its write set), the flag word
   and the frame's shadow (a frame of its call state, off its write set). *)
Lemma cc_koff_cj : forall g pos ly2 S2 (W2 : world tfibsegs) mem2 md2 W3 mem3 T1 (E1 : Z -> Prop),
  cc_pre B SEG7TBL GLYPHA ROSTRS g ->
  ajournal tfibsegs B (cc_STK g) (cc_sp0 g) (cc_FP g) (cc_ly g) (cc_S g) (cc_W0 g) (cc_mem0 g) (cc_md0 g)
    ((0, pos) :: cc_own g) ly2 S2 W2 mem2 md2 (cc_k g) ->
  tcj_kept tfibsegs B T1 ly2 S2 W2 mem2 W3 mem3 (cc_sp1 g) E1 -> 0 <= T1 ->
  (forall a, E1 a -> ~ ((cc_sp g - 104 <= a < cc_sp g) \/ (cc_F g pos + 56 <= a < cc_F g pos + 64) \/
     (SB + cc_F g pos / 8 <= a < SB + cc_F g pos / 8 + 8) \/ (cc_sp1 g + 24 <= a < cc_sp1 g + 32))) ->
  forall a, (cc_sp g - 104 <= a < cc_sp g) \/ (cc_F g pos + 56 <= a < cc_F g pos + 64) \/
     (SB + cc_F g pos / 8 <= a < SB + cc_F g pos / 8 + 8) \/ (cc_sp1 g + 24 <= a < cc_sp1 g + 32) ->
     aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a.
Proof.
intros g pos ly2 S2 W2 mem2 md2 W3 mem3 T1 E1 Hpre HJ (K1 & _ & _ & K4 & _) HT HE a Ha.
destruct (cc_stack g Hpre) as (Hceil & H47 & H46 & Hal & Hsp1 & Hsp1a & Hwin & Hsp0).
destruct (cc_frame g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (Hfr & Efa & _ & HF0 & HFc & HF64 & _ & _).
assert (HnE : ~ E1 a) by (intros He; exact (HE a He Ha)).
assert (Hin : In (0, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
assert (HSB : shadow_addr (cc_F g pos) = SB + cc_F g pos / 8)
  by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; reflexivity).
destruct Ha as [Ha | [Ha | [Ha | Ha]]].
- apply K1; [lia | lia | exact HnE].
- apply (K4 0 pos a Hin); [left | exact HnE].
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa. change (fs_frame_bytes 0) with 64. fold (cc_F g pos). lia.
- apply (K4 0 pos a Hin); [right | exact HnE].
  unfold in_zr. cbn [fst snd]. rewrite Efa. fold (cc_F g pos). rewrite HSB. change (fs_frame_bytes 0 / 8) with 8. lia.
- apply K1; [lia | lia | exact HnE].
Qed.
End h.
End d.
