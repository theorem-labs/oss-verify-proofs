(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 1684 of its 1797 lines of code are new or changed and 898 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R6.v; 287 of its 360 lines of code are new or changed and 1724 lines of the source are left out. *)
(* Round-trip model facts of fuzz_ctrl LLVMFuzzerTestOneInput, image B (asan-ubsan, libreac v1.9.0), for the segments
   R17-R21: the image-B port of lib/A/Prog/Seg/B3Rtm.v (a working branch) over lib/B/Prog/SlotModel.v
   (catalogue CAT = 0x9f620, BOX_CATALOGUE of the v1.9.0 binary; round-trip box 0x21140). Every round-trip value is
   a function of OUR and i* only (rb_cn below rebuilds an input with the same two), so each fact is computed over
   the 11 catalogue rows of the v1.9.0 image with the 6 bytes of OUR left as variables. Also the 11 rows
   themselves: their bytes in the image, has_identity_record at + 56, the name pointer at + 280 and the name string
   (read-only image bytes inside frame_AG), the lengths of the round-trip model (rb_rtn, the image-B twin of
   lib/A/Prog/Seg/Tac_rt2_b2.v a_rtn) and the row words at + 16 / + 20 that ports_parse's two counts match.
   rule 24: no function proved (model facts of slot segments). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require YL0g.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcParse RcReply RcIdentModel RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLeaf RcPorts RcEmit RcSynth RcDecl RcMatch.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcEmitLib RcSynthLib RcLay RcFinLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel.
Import ListNotations.
Open Scope Z_scope.

Module AFm := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module YLg := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YL0g.

Lemma rb_istar_range : forall inp, 0 <= istar inp < 11.
Proof. intros inp. unfold istar, CAT_N. apply Z.mod_pos_bound. lia. Qed.

(* ---- Every round-trip value depends on the input only through OUR and i* ---- *)

Section Cong.
Variables inp inp' : list byte.
Hypothesis HO : OUR inp = OUR inp'.
Hypothesis HI : istar inp = istar inp'.

Lemma rbc_mrow : mrow inp = mrow inp'.
Proof using HO HI. unfold mrow. rewrite HI. reflexivity. Qed.

Lemma rbc_mb : rt_mb inp = rt_mb inp'.
Proof using HO HI. unfold rt_mb. rewrite HI. reflexivity. Qed.

Lemma rbc_nb : rt_nb inp = rt_nb inp'.
Proof using HO HI. unfold rt_nb. rewrite rbc_mb. reflexivity. Qed.

Lemma rbc_n : forall b, rt_n inp b = rt_n inp' b.
Proof using HO HI. intros b. unfold rt_n, rt_E, rt_uw. rewrite rbc_mrow, rbc_mb. reflexivity. Qed.

Lemma rbc_X : forall b, rt_X inp b = rt_X inp' b.
Proof using HO HI. intros b. unfold rt_X. rewrite rbc_mrow, rbc_mb, rbc_nb. reflexivity. Qed.

Lemma rbc_F : forall b, rt_F inp b = rt_F inp' b.
Proof using HO HI. intros b. unfold rt_F. rewrite HO, rbc_X, rbc_n. reflexivity. Qed.

Lemma rbc_g : forall b, rt_g inp b = rt_g inp' b.
Proof using HO HI. intros b. unfold rt_g. rewrite rbc_F. reflexivity. Qed.

Lemma rbc_k : forall b, rt_k inp b = rt_k inp' b.
Proof using HO HI. intros b. unfold rt_k. rewrite rbc_n, rbc_g. reflexivity. Qed.

Lemma rbc_pbs : rt_pbs inp = rt_pbs inp'.
Proof using HO HI. unfold rt_pbs. rewrite rbc_g. reflexivity. Qed.

Lemma rbc_st : forall b, rt_st inp b = rt_st inp' b.
Proof using HO HI.
  induction b as [|b IH]; [reflexivity|].
  cbn [rt_st]. rewrite IH, !rbc_n, !rbc_g. reflexivity.
Qed.

Lemma rbc_RID : forall b, RID inp b = RID inp' b.
Proof using HO HI. intros b. unfold RID. rewrite rbc_st. reflexivity. Qed.

Lemma rbc_RFG : forall b, RFG inp b = RFG inp' b.
Proof using HO HI. intros b. unfold RFG. rewrite rbc_st. reflexivity. Qed.

End Cong.

(* The canonical input: OUR, then the mode byte 2 i. *)
Definition rb_cn (our : list byte) (i : Z) : list byte := our ++ [zb (2 * i)].

Lemma rb_cn_OUR : forall our i, length our = 6%nat -> OUR (rb_cn our i) = our.
Proof.
  intros our i H. destruct our as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|? ?]]]]]]]; try discriminate H.
  reflexivity.
Qed.

Lemma rb_cn_istar : forall our i, length our = 6%nat -> 0 <= i < 11 -> istar (rb_cn our i) = i.
Proof.
  intros our i H Hi. destruct our as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|? ?]]]]]]]; try discriminate H.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]; vm_compute; reflexivity.
Qed.

(* Rewrite every round-trip value at inp to the canonical input of (OUR inp, istar inp), then split into the 11
   rows with OUR = 6 variables. The goal must mention inp only through the functions rewritten here. *)
Ltac rb_rows inp :=
  let HO := fresh "HO" in let HI := fresh "HI" in
  assert (HO : OUR inp = OUR (rb_cn (OUR inp) (istar inp)))
    by (symmetry; apply rb_cn_OUR, OUR_length);
  assert (HI : istar inp = istar (rb_cn (OUR inp) (istar inp)))
    by (symmetry; apply rb_cn_istar; [apply OUR_length | apply rb_istar_range]);
  rewrite ?(rbc_k _ _ HO HI), ?(rbc_n _ _ HO HI), ?(rbc_g _ _ HO HI), ?(rbc_F _ _ HO HI), ?(rbc_X _ _ HO HI),
    ?(rbc_RID _ _ HO HI), ?(rbc_RFG _ _ HO HI), ?(rbc_pbs _ _ HO HI), ?(rbc_mb _ _ HO HI),
    ?(rbc_nb _ _ HO HI), ?(rbc_mrow _ _ HO HI);
  clear HO HI;
  generalize (OUR_length inp) (rb_istar_range inp);
  generalize (OUR inp) (istar inp);
  let our := fresh "our" in let i := fresh "i" in let HL := fresh "HL" in let Hi := fresh "Hi" in
  intros our i HL Hi;
  destruct our as [|?x0 [|?x1 [|?x2 [|?x3 [|?x4 [|?x5 [|? ?]]]]]]]; try discriminate HL; clear HL;
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10)
    by lia;
  clear Hi;
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]].

(* Close a computed goal: `P`, `x <> y`, `A -> P` with A false or true, conjunctions, iff of two decided facts. *)
Ltac rb_fin :=
  vm_compute;
  first [ reflexivity
        | intros ?H; discriminate H
        | intros ?H; exfalso; apply H; reflexivity
        | intros _; reflexivity
        | intros _; repeat split; reflexivity
        | repeat split; reflexivity
        | split; intros ?H ?E; discriminate E
        | split; intros ?H; exact H ].

(* ---- RTM (a): which turns emit a frame ---- *)

Lemma rb_rtm_n_on : forall inp b, 0 <= b <= 4 -> rt_n inp b <> 0.
Proof.
  intros inp b Hb.
  assert (E : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4) by lia.
  destruct E as [->|[->|[->|[->| ->]]]]; rb_rows inp; rb_fin.
Qed.

Lemma rb_rtm_n56 : forall inp, rt_n inp 6 = rt_n inp 5.
Proof. intros inp. rb_rows inp; rb_fin. Qed.

(* E(5) = E(6) is has_identity_record(m) != 0 (the s32 at m + 56). *)
Lemma rb_rtm_hid : forall inp, rt_n inp 6 <> 0 <-> RcEmit.em_hid (rt_mb inp) <> 0.
Proof. intros inp. rb_rows inp; rb_fin. Qed.

(* ---- RTM (b): k_b = 9, 5, 5, 5, 5, 11, 11 ---- *)

Lemma rb_rtm_k0 : forall inp, rt_k inp 0 = 9.
Proof. intros inp. rb_rows inp; rb_fin. Qed.

Lemma rb_rtm_k5 : forall inp b, 1 <= b <= 4 -> rt_k inp b = 5.
Proof.
  intros inp b Hb.
  assert (E : b = 1 \/ b = 2 \/ b = 3 \/ b = 4) by lia.
  destruct E as [->|[->|[->| ->]]]; rb_rows inp; rb_fin.
Qed.

Lemma rb_rtm_k11 : forall inp b, (b = 5 \/ b = 6) -> rt_n inp b <> 0 -> rt_k inp b = 11.
Proof.
  intros inp b Hb. destruct Hb as [->| ->]; rb_rows inp; rb_fin.
Qed.

(* ---- RTM (c): the block sums of X(0), X(1), X(2) close ---- *)

Lemma rb_rtm_sum : forall inp b, 0 <= b <= 2 -> blocksum (skipn 18 (rt_g inp b)) = 0.
Proof.
  intros inp b Hb.
  assert (E : b = 0 \/ b = 1 \/ b = 2) by lia.
  destruct E as [->|[->| ->]]; rb_rows inp; rb_fin.
Qed.

(* ---- RTM (d): CONFIG (b = 0): match, ports, declaration ---- *)

Lemma rb_rtm_want : forall inp, RcMatch.want CAT (rt_n inp 0) (rt_g inp 0) = mrow inp.
Proof. intros inp. rb_rows inp; rb_fin. Qed.

Lemma rb_rtm_decl : forall inp, RcLeaf.decl (rt_pbs inp) = true.
Proof. intros inp. rb_rows inp; rb_fin. Qed.

Lemma rb_rtm_in : forall inp, 4 * RcLeaf.n_in (rt_pbs inp) = RcDecl.box_ic (rt_mb inp).
Proof. intros inp. rb_rows inp; rb_fin. Qed.

Lemma rb_rtm_out : forall inp, 4 * RcLeaf.n_out (rt_pbs inp) = RcDecl.box_oc (rt_mb inp).
Proof. intros inp. rb_rows inp; rb_fin. Qed.

Lemma rb_rtm_declok : forall inp, RcDecl.decl_ok (rt_mb inp) = true.
Proof. intros inp. rb_rows inp; rb_fin. Qed.

Lemma rb_rtm_X0 : forall inp, bsl (rt_g inp 0) 18 32 = RcDecl.decl (rt_mb inp).
Proof. intros inp. rb_rows inp; rb_fin. Qed.

(* ---- RTM (e): b = 3, 4: IR, the reply's outputs, ING's result 1 ---- *)

Lemma rb_rtm_ir : forall inp b, (b = 3 \/ b = 4) -> ir (rt_n inp b) (rt_g inp b) = true.
Proof. intros inp b Hb. destruct Hb as [->| ->]; rb_rows inp; rb_fin. Qed.

Lemma rb_rtm_reply : forall inp,
  r_addr (rt_g inp 3) = 0x0000 /\ r_pll (rt_g inp 3) = 4 /\ r_addr (rt_g inp 4) = 0x0600 /\ r_pll (rt_g inp 4) = 8.
Proof. intros inp. rb_rows inp; rb_fin. Qed.

Lemma rb_rtm_ing34 : forall inp (b : nat), (b = 3 \/ b = 4)%nat ->
  fst (ING (RID inp b) (r_addr (rt_g inp (Z.of_nat b))) (r_pl (rt_g inp (Z.of_nat b)))) = 1.
Proof. intros inp b Hb. destruct Hb as [->| ->]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; rb_rows inp; rb_fin. Qed.

(* ---- RTM (f): b = 5 FIRST, b = 6 CLOSE on RFG_6, ING's result 1 ---- *)

Lemma rb_rtm_first : forall inp, rt_n inp 5 <> 0 -> fcls (rt_n inp 5) (RFG inp 5) (rt_g inp 5) = FgFirst.
Proof. intros inp. rb_rows inp; rb_fin. Qed.

Lemma rb_rtm_close : forall inp, rt_n inp 6 <> 0 -> fcls (rt_n inp 6) (RFG inp 6) (rt_g inp 6) = FgClose.
Proof. intros inp. rb_rows inp; rb_fin. Qed.

Lemma rb_rtm_close_vals : forall inp, rt_n inp 6 <> 0 ->
  fg_addr (RFG inp 6) (rt_g inp 6) = 0x1000 /\ f_pll (RFG inp 6) (rt_g inp 6) = 17.
Proof. intros inp. rb_rows inp; rb_fin. Qed.

Lemma rb_rtm_ing6 : forall inp, rt_n inp 6 <> 0 ->
  fst (ING (RID inp 6) (fg_addr (RFG inp 6) (rt_g inp 6)) (f_pl (rt_n inp 6) (RFG inp 6) (rt_g inp 6))) = 1.
Proof. intros inp. rb_rows inp; rb_fin. Qed.

(* ---- RTM (g): RID_7 holds the row's firmware, version and (with an identity record) name ---- *)

Lemma rb_rtm_fw : forall inp, has_fw (RID inp 7) = 1 /\
  fw_milli (RID inp 7) = RcDecl.rval (rt_mb inp) 266 + 256 * RcDecl.rval (rt_mb inp) 267.
Proof. intros inp. rb_rows inp; rb_fin. Qed.

Lemma rb_rtm_ver : forall inp, has_reac_version (RID inp 7) = 1 /\
  major (RID inp 7) = RcDecl.rval (rt_mb inp) 268 + 256 * RcDecl.rval (rt_mb inp) 269 /\
  minor (RID inp 7) = RcDecl.rval (rt_mb inp) 270 + 256 * RcDecl.rval (rt_mb inp) 271 /\
  patch (RID inp 7) = RcDecl.rval (rt_mb inp) 272 + 256 * RcDecl.rval (rt_mb inp) 273.
Proof. intros inp. rb_rows inp; rb_fin. Qed.

Lemma rb_rtm_name : forall inp, rt_n inp 6 <> 0 ->
  has_model_name (RID inp 7) = 1 /\ firstn (length (rt_nb inp)) (model_name (RID inp 7)) = rt_nb inp /\
  last (rt_nb inp) (zb 1) = zb 0 /\ forallb (fun x => negb (bz x =? 0)) (removelast (rt_nb inp)) = true /\
  (Nat.leb 2 (length (rt_nb inp)) && Nat.leb (length (rt_nb inp)) 16)%bool = true.
Proof. intros inp. rb_rows inp; rb_fin. Qed.

(* ---- The round-trip state across turn b (no computation) ---- *)

Lemma rb_st_S : forall inp (b : nat), rt_st inp (S b) =
  let s := rt_st inp b in let x := Z.of_nat b in
  if rt_n inp x =? 0 then s
  else if (x =? 3) || (x =? 4) then (rp_id (fst s) (rt_n inp x) (rt_g inp x), snd s)
  else if (x =? 5) || (x =? 6) then (fg_id (fst s) (rt_n inp x) (snd s) (rt_g inp x), fg_st (rt_n inp x) (snd s) (rt_g inp x))
  else s.
Proof. intros inp b. reflexivity. Qed.

Lemma rb_RS_012 : forall inp (b : nat), (b <= 2)%nat -> RID inp (S b) = RID inp b /\ RFG inp (S b) = RFG inp b.
Proof.
  intros inp b Hb. unfold RID, RFG. rewrite rb_st_S. cbv zeta.
  destruct (rt_n inp (Z.of_nat b) =? 0); [split; reflexivity|].
  replace ((Z.of_nat b =? 3) || (Z.of_nat b =? 4)) with false by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; lia).
  replace ((Z.of_nat b =? 5) || (Z.of_nat b =? 6)) with false by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; lia).
  split; reflexivity.
Qed.

Lemma rb_RS_34 : forall inp (b : nat), (b = 3 \/ b = 4)%nat -> rt_n inp (Z.of_nat b) <> 0 ->
  RID inp (S b) = rp_id (RID inp b) (rt_n inp (Z.of_nat b)) (rt_g inp (Z.of_nat b)) /\ RFG inp (S b) = RFG inp b.
Proof.
  intros inp b Hb Hn. unfold RID, RFG. rewrite rb_st_S. cbv zeta.
  rewrite (proj2 (Z.eqb_neq _ 0) Hn).
  replace ((Z.of_nat b =? 3) || (Z.of_nat b =? 4)) with true
    by (symmetry; apply orb_true_iff; destruct Hb as [->| ->]; [left | right]; reflexivity).
  split; reflexivity.
Qed.

Lemma rb_RS_56 : forall inp (b : nat), (b = 5 \/ b = 6)%nat -> rt_n inp (Z.of_nat b) <> 0 ->
  RID inp (S b) = fg_id (RID inp b) (rt_n inp (Z.of_nat b)) (RFG inp b) (rt_g inp (Z.of_nat b)) /\
  RFG inp (S b) = fg_st (rt_n inp (Z.of_nat b)) (RFG inp b) (rt_g inp (Z.of_nat b)).
Proof.
  intros inp b Hb Hn. unfold RID, RFG. rewrite rb_st_S. cbv zeta.
  rewrite (proj2 (Z.eqb_neq _ 0) Hn).
  replace ((Z.of_nat b =? 3) || (Z.of_nat b =? 4)) with false
    by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; lia).
  replace ((Z.of_nat b =? 5) || (Z.of_nat b =? 6)) with true
    by (symmetry; apply orb_true_iff; destruct Hb as [->| ->]; [left | right]; reflexivity).
  split; reflexivity.
Qed.

(* ---- The 11 catalogue rows of image B (v1.9.0: CAT = 0x9f620) ---- *)

Lemma rb_row_img : forall i, 0 <= i < 11 -> Image.image_bytes rsegs (CAT + CAT_ROW * i) 296 = Some (rowb i).
Proof.
  intros i Hi.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]];
    unfold rowb, img; (destruct (Image.image_bytes _ _ _) eqn:E; [reflexivity | vm_compute in E; discriminate E]).
Qed.

(* An address inside one of the registered globals of frame_AG (boolean form). *)
Definition rb_inAG (a : Z) : bool :=
  existsb (fun p => (fst p <=? a) && (a <? fst p + snd p)) AFm.frame_AG.

Lemma rb_inAG_sound : forall a, rb_inAG a = true -> YLg.in_globals AFm.frame_AG a.
Proof.
  intros a H. unfold rb_inAG in H. apply existsb_exists in H. destruct H as ([lo len] & Hin & Hb).
  cbn [fst snd] in Hb. apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists lo, len. split; [exact Hin | lia].
Qed.

(* Per row: the s32 at + 56 is a u32 that is 0 exactly when em_hid is; with an identity record the name pointer
   (+ 280) is a nonzero low-image address whose C string (the round trip's rt_nb) is read-only image bytes, inside
   frame_AG byte by byte. *)
Definition rb_rowchk (i : Z) : bool :=
  let r := rowb i in let h := RcSynth.rw32 r 56 in let nm := RcSynth.rname r in
  (0 <=? h) && (h <? 2 ^ 32) && Bool.eqb (RcEmit.em_hid r =? 0) (h =? 0) &&
  ((RcEmit.em_hid r =? 0) ||
   ((0 <? nm) && (nm + 17 <=? 6283264) && Image.ro_bytes_b rsegs nm (img_cstr nm 16) &&
    forallb (fun k => rb_inAG (nm + Z.of_nat k)) (seq 0 (length (img_cstr nm 16))))).

Lemma rb_rowchk_all : forallb rb_rowchk (map Z.of_nat (seq 0 11)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rb_rowchk_i : forall i, 0 <= i < 11 -> rb_rowchk i = true.
Proof.
  intros i Hi. pose proof rb_rowchk_all as H. rewrite forallb_forall in H. apply H.
  apply in_map_iff. exists (Z.to_nat i). split; [lia | apply in_seq; lia].
Qed.

Lemma rb_bytes_eq : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

(* The u32 at + 56 and the u64 at + 280 of each row as little-endian words. *)
Lemma rb_row_le : forall i, 0 <= i < 11 ->
  firstn 4 (skipn 56 (rowb i)) = le4 (Z_to_bv 64 (RcSynth.rw32 (rowb i) 56)) /\
  firstn 8 (skipn 280 (rowb i)) = le8 (Z_to_bv 64 (RcSynth.rname (rowb i))).
Proof.
  intros i Hi.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]];
    split; apply rb_bytes_eq; vm_compute; reflexivity.
Qed.

Lemma rb_row_facts : forall i, 0 <= i < 11 ->
  0 <= RcSynth.rw32 (rowb i) 56 < 2 ^ 32 /\
  (RcEmit.em_hid (rowb i) = 0 <-> RcSynth.rw32 (rowb i) 56 = 0) /\
  (RcEmit.em_hid (rowb i) <> 0 ->
     0 < RcSynth.rname (rowb i) /\ RcSynth.rname (rowb i) + 17 <= 6283264 /\
     Image.ro_bytes_b rsegs (RcSynth.rname (rowb i)) (img_cstr (RcSynth.rname (rowb i)) 16) = true /\
     forall k, (k < length (img_cstr (RcSynth.rname (rowb i)) 16))%nat ->
       YLg.in_globals AFm.frame_AG (RcSynth.rname (rowb i) + Z.of_nat k)).
Proof.
  intros i Hi. pose proof (rb_rowchk_i i Hi) as H. unfold rb_rowchk in H. cbv zeta in H.
  rewrite !andb_true_iff in H. destruct H as [[[H1 H2] H3] H4].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Bool.eqb_prop in H3.
  split; [lia|]. split.
  - destruct (Z.eqb_spec (RcEmit.em_hid (rowb i)) 0) as [E|E];
      destruct (Z.eqb_spec (RcSynth.rw32 (rowb i) 56) 0) as [E'|E']; try discriminate H3; tauto.
  - intros Hn. apply orb_true_iff in H4. destruct H4 as [H4|H4]; [apply Z.eqb_eq in H4; contradiction|].
    rewrite !andb_true_iff in H4. destruct H4 as [[[H5 H6] H7] H8].
    apply Z.ltb_lt in H5. apply Z.leb_le in H6. split; [lia|]. split; [lia|]. split; [exact H7|].
    intros k Hk. apply rb_inAG_sound. rewrite forallb_forall in H8. apply H8. apply in_seq. lia.
Qed.

(* ---- Lengths of the round-trip model (the image-B twins of lib/A/Prog/Seg/Tac_rt2_b2.v) ---- *)

Lemma rb_row_len : forall i, length (rowb i) = 296%nat.
Proof.
  intros i. unfold rowb, img. destruct (Image.image_bytes rsegs (CAT + CAT_ROW * i) 296) eqn:E.
  - exact (Image.image_bytes_length rsegs 296 _ _ E).
  - apply repeat_length.
Qed.

Lemma rb_rtX_len : forall inp b, length (rt_X inp b) = 32%nat.
Proof.
  intros inp b. unfold rt_X, reac_ctrl_build_as_c.ba_X, RcLay.ly_Z.
  assert (HZ : length (if mrow inp =? 0 then RcLay.ly_zero
                       else if RcSynth.rc (rt_mb inp) b =? 1 then RcSynth.synth (rt_mb inp) b (rt_nb inp)
                       else RcLay.ly_zero) = 32%nat).
  { destruct (mrow inp =? 0); [reflexivity|].
    destruct (RcSynth.rc (rt_mb inp) b =? 1); [|reflexivity].
    apply RcSynthLib.rs_synth_len. apply rb_row_len. }
  destruct (b <=? 1); [apply RcFinLib.rcf_stamp32_len; exact HZ | exact HZ].
Qed.

(* n_b != 0: E(b), 124 <= n_b <= 1492, and F_b has n_b bytes. *)
Lemma rb_rtn : forall inp b, rt_n inp b <> 0 ->
  rt_E inp b = true /\ 124 <= rt_n inp b <= 1492 /\ length (rt_F inp b) = Z.to_nat (rt_n inp b).
Proof.
  intros inp b H. unfold rt_n in *. destruct (rt_E inp b) eqn:E; [|congruence].
  pose proof E as E'. unfold rt_E, reac_ctrl_build_as_c.ba_E in E'. apply andb_true_iff in E' as [Ew _].
  destruct (RcEmitLib.em_wok_range _ Ew) as [R _].
  split; [reflexivity|]. split; [lia|].
  unfold rt_F, RcEmit.em_fr, RcEmit.em_hdr, box6. unfold rt_n. rewrite E.
  rewrite !length_app, OUR_length, length_map, rb_rtX_len, repeat_length. cbn [length]. lia.
Qed.

(* The identity record has 38 bytes at every turn. *)
Lemma rb_RID_len : forall inp b, length (RID inp b) = 38%nat.
Proof.
  intros inp b. unfold RID. induction b as [|b IH]; [reflexivity|].
  cbn [rt_st].
  destruct (rt_n inp (Z.of_nat b) =? 0); [exact IH|].
  destruct ((Z.of_nat b =? 3) || (Z.of_nat b =? 4)); cbn [fst snd].
  - unfold rp_id. destruct (ir _ _); [apply RcIdentModel.ING_length; exact IH | exact IH].
  - destruct ((Z.of_nat b =? 5) || (Z.of_nat b =? 6)); cbn [fst snd]; [|exact IH].
    unfold fg_id. destruct (fg_rf _ _ _ =? 1); [apply RcIdentModel.ING_length; exact IH | exact IH].
Qed.

(* The fragment state has 72 bytes at every round-trip turn (computed over the 11 catalogue rows). *)
Lemma rb_RFG_len : forall inp b, (b <= 7)%nat -> length (RFG inp b) = 72%nat.
Proof.
  intros inp b Hb.
  assert (E : (b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7)%nat) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; rb_rows inp; rb_fin.
Qed.

(* ---- The catalogue row of the round trip: its place, its words at + 16 / + 20, its declaration ---- *)

Lemma rb_mrow_range : forall inp, CAT <= mrow inp /\ mrow inp + 296 <= CAT + 3256 /\ mrow inp mod 8 = 0.
Proof.
  intros inp. pose proof (rb_istar_range inp) as Hi. unfold mrow, CAT, CAT_ROW in *.
  split; [lia|]. split; [lia|]. Z.div_mod_to_equations. lia.
Qed.

Lemma rb_mb_img : forall inp, Image.image_bytes rsegs (mrow inp) 296 = Some (rt_mb inp).
Proof. intros inp. unfold mrow, rt_mb. apply rb_row_img. apply rb_istar_range. Qed.

Lemma rb_mb_len : forall inp, length (rt_mb inp) = 296%nat.
Proof. intros inp. unfold rt_mb. apply rb_row_len. Qed.

Lemma rb_decl_len : forall inp, length (RcDecl.decl (rt_mb inp)) = 32%nat.
Proof. intros inp. rb_rows inp; rb_fin. Qed.

(* The row's words at + 16 and + 20 as little-endian 4-byte runs (computed over the 11 catalogue rows). *)
Lemma rb_row_words : forall i, 0 <= i < 11 ->
  firstn 4 (skipn 16 (rowb i)) = le4 (Z_to_bv 64 (RcDecl.box_ic (rowb i))) /\
  firstn 4 (skipn 20 (rowb i)) = le4 (Z_to_bv 64 (RcDecl.box_oc (rowb i))).
Proof.
  intros i Hi.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]];
    split; apply rb_bytes_eq; vm_compute; reflexivity.
Qed.

(* The round trip's row words at + 16 / + 20 are the two port counts ports_parse wrote. *)
Lemma rb_row_ic : forall inp,
  firstn 4 (skipn 16 (rt_mb inp)) = le4 (Z_to_bv 64 (4 * RcLeaf.n_in (rt_pbs inp))).
Proof.
  intros inp. rewrite (rb_rtm_in inp). unfold rt_mb.
  exact (proj1 (rb_row_words (istar inp) (rb_istar_range inp))).
Qed.

Lemma rb_row_oc : forall inp,
  firstn 4 (skipn 20 (rt_mb inp)) = le4 (Z_to_bv 64 (4 * RcLeaf.n_out (rt_pbs inp))).
Proof.
  intros inp. rewrite (rb_rtm_out inp). unfold rt_mb.
  exact (proj2 (rb_row_words (istar inp) (rb_istar_range inp))).
Qed.

(* Turn 0 emits a frame, so its 50 frame bytes are the first 50 of F_0, and the port bytes and the block are its
   slices at 18. *)
Lemma rb_F0_len : forall inp, (50 <= length (rt_F inp 0))%nat.
Proof.
  intros inp. destruct (rb_rtn inp 0 (rb_rtm_n_on inp 0 ltac:(lia))) as (_ & Hn & HL). rewrite HL. lia.
Qed.

Lemma rb_pbs_F : forall inp, rt_pbs inp = firstn 20 (skipn 18 (rt_F inp 0)).
Proof.
  intros inp. pose proof (rb_F0_len inp) as H.
  unfold rt_pbs, RcFrag.bsl, rt_g, fr50.
  change (Z.to_nat 20) with 20%nat. change (Z.to_nat 18) with 18%nat.
  rewrite firstn_app. replace (50 - length (rt_F inp 0))%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r, skipn_firstn_comm, firstn_firstn.
  rewrite Nat.min_l by lia. reflexivity.
Qed.

Lemma rb_pbs_len : forall inp, length (rt_pbs inp) = 20%nat.
Proof.
  intros inp. pose proof (rb_F0_len inp) as H. rewrite rb_pbs_F, length_firstn, length_skipn. lia.
Qed.

Lemma rb_X0_F : forall inp, firstn 32 (skipn 18 (rt_F inp 0)) = RcDecl.decl (rt_mb inp).
Proof.
  intros inp. pose proof (rb_F0_len inp) as H.
  rewrite <- (rb_rtm_X0 inp). unfold RcFrag.bsl, rt_g, fr50.
  change (Z.to_nat 32) with 32%nat. change (Z.to_nat 18) with 18%nat.
  rewrite firstn_app. replace (50 - length (rt_F inp 0))%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r, skipn_firstn_comm, firstn_firstn. reflexivity.
Qed.
