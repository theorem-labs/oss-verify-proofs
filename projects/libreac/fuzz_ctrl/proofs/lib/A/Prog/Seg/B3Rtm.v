(* Round-trip model facts RTM of fuzz_ctrl LLVMFuzzerTestOneInput, image A (asan), for the batch-B3 segments
   R14-R21: the port of lib/U/Prog/Seg/Tac_u2.v (slot-plan.md 6.3 (a working note, not in this delivery)) to the image-A model
   lib/A/Prog/SlotModel.v (catalogue CAT = 0x9e800, round-trip box 0x21140). Every round-trip value is a function of
   OUR and i* only (a_cn below rebuilds an input with the same two), so each fact is computed over the 11 catalogue
   rows of image A with the 6 bytes of OUR left as variables. Also the 11 rows themselves: their bytes in the image,
   has_identity_record at + 56, the name pointer at + 280 and the name string (read-only image bytes inside
   frame_AG). Lengths of rt_F / rt_n: Tac_rt2_b2.a_rtn with a_rtm_n_on below. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require YL0g.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcParse RcReply RcIdentModel RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLeaf RcPorts RcEmit RcSynth RcDecl RcMatch.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel.
Import ListNotations.
Open Scope Z_scope.

Module AFm := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module YLg := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YL0g.

Lemma a_istar_range : forall inp, 0 <= istar inp < 11.
Proof. intros inp. unfold istar, CAT_N. apply Z.mod_pos_bound. lia. Qed.

(* ---- Every round-trip value depends on the input only through OUR and i* ---- *)

Section Cong.
Variables inp inp' : list byte.
Hypothesis HO : OUR inp = OUR inp'.
Hypothesis HI : istar inp = istar inp'.

Lemma ac_mrow : mrow inp = mrow inp'.
Proof using HO HI. unfold mrow. rewrite HI. reflexivity. Qed.

Lemma ac_mb : rt_mb inp = rt_mb inp'.
Proof using HO HI. unfold rt_mb. rewrite HI. reflexivity. Qed.

Lemma ac_nb : rt_nb inp = rt_nb inp'.
Proof using HO HI. unfold rt_nb. rewrite ac_mb. reflexivity. Qed.

Lemma ac_n : forall b, rt_n inp b = rt_n inp' b.
Proof using HO HI. intros b. unfold rt_n, rt_E, rt_uw. rewrite ac_mrow, ac_mb. reflexivity. Qed.

Lemma ac_X : forall b, rt_X inp b = rt_X inp' b.
Proof using HO HI. intros b. unfold rt_X. rewrite ac_mrow, ac_mb, ac_nb. reflexivity. Qed.

Lemma ac_F : forall b, rt_F inp b = rt_F inp' b.
Proof using HO HI. intros b. unfold rt_F. rewrite HO, ac_X, ac_n. reflexivity. Qed.

Lemma ac_g : forall b, rt_g inp b = rt_g inp' b.
Proof using HO HI. intros b. unfold rt_g. rewrite ac_F. reflexivity. Qed.

Lemma ac_k : forall b, rt_k inp b = rt_k inp' b.
Proof using HO HI. intros b. unfold rt_k. rewrite ac_n, ac_g. reflexivity. Qed.

Lemma ac_pbs : rt_pbs inp = rt_pbs inp'.
Proof using HO HI. unfold rt_pbs. rewrite ac_g. reflexivity. Qed.

Lemma ac_st : forall b, rt_st inp b = rt_st inp' b.
Proof using HO HI.
  induction b as [|b IH]; [reflexivity|].
  cbn [rt_st]. rewrite IH, !ac_n, !ac_g. reflexivity.
Qed.

Lemma ac_RID : forall b, RID inp b = RID inp' b.
Proof using HO HI. intros b. unfold RID. rewrite ac_st. reflexivity. Qed.

Lemma ac_RFG : forall b, RFG inp b = RFG inp' b.
Proof using HO HI. intros b. unfold RFG. rewrite ac_st. reflexivity. Qed.

End Cong.

(* The canonical input: OUR, then the mode byte 2 i. *)
Definition a_cn (our : list byte) (i : Z) : list byte := our ++ [zb (2 * i)].

Lemma a_cn_OUR : forall our i, length our = 6%nat -> OUR (a_cn our i) = our.
Proof.
  intros our i H. destruct our as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|? ?]]]]]]]; try discriminate H.
  reflexivity.
Qed.

Lemma a_cn_istar : forall our i, length our = 6%nat -> 0 <= i < 11 -> istar (a_cn our i) = i.
Proof.
  intros our i H Hi. destruct our as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|? ?]]]]]]]; try discriminate H.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]; vm_compute; reflexivity.
Qed.

(* Rewrite every round-trip value at inp to the canonical input of (OUR inp, istar inp), then split into the 11
   rows with OUR = 6 variables. The goal must mention inp only through the functions rewritten here. *)
Ltac a_rows inp :=
  let HO := fresh "HO" in let HI := fresh "HI" in
  assert (HO : OUR inp = OUR (a_cn (OUR inp) (istar inp)))
    by (symmetry; apply a_cn_OUR, OUR_length);
  assert (HI : istar inp = istar (a_cn (OUR inp) (istar inp)))
    by (symmetry; apply a_cn_istar; [apply OUR_length | apply a_istar_range]);
  rewrite ?(ac_k _ _ HO HI), ?(ac_n _ _ HO HI), ?(ac_g _ _ HO HI), ?(ac_F _ _ HO HI), ?(ac_X _ _ HO HI),
    ?(ac_RID _ _ HO HI), ?(ac_RFG _ _ HO HI), ?(ac_pbs _ _ HO HI), ?(ac_mb _ _ HO HI),
    ?(ac_nb _ _ HO HI), ?(ac_mrow _ _ HO HI);
  clear HO HI;
  generalize (OUR_length inp) (a_istar_range inp);
  generalize (OUR inp) (istar inp);
  let our := fresh "our" in let i := fresh "i" in let HL := fresh "HL" in let Hi := fresh "Hi" in
  intros our i HL Hi;
  destruct our as [|?x0 [|?x1 [|?x2 [|?x3 [|?x4 [|?x5 [|? ?]]]]]]]; try discriminate HL; clear HL;
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10)
    by lia;
  clear Hi;
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]].

(* Close a computed goal: `P`, `x <> y`, `A -> P` with A false or true, conjunctions, iff of two decided facts. *)
Ltac a_fin :=
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

Lemma a_rtm_n_on : forall inp b, 0 <= b <= 4 -> rt_n inp b <> 0.
Proof.
  intros inp b Hb.
  assert (E : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4) by lia.
  destruct E as [->|[->|[->|[->| ->]]]]; a_rows inp; a_fin.
Qed.

Lemma a_rtm_n56 : forall inp, rt_n inp 6 = rt_n inp 5.
Proof. intros inp. a_rows inp; a_fin. Qed.

(* E(5) = E(6) is has_identity_record(m) != 0 (the s32 at m + 56). *)
Lemma a_rtm_hid : forall inp, rt_n inp 6 <> 0 <-> RcEmit.em_hid (rt_mb inp) <> 0.
Proof. intros inp. a_rows inp; a_fin. Qed.

(* ---- RTM (b): k_b = 9, 5, 5, 5, 5, 11, 11 ---- *)

Lemma a_rtm_k0 : forall inp, rt_k inp 0 = 9.
Proof. intros inp. a_rows inp; a_fin. Qed.

Lemma a_rtm_k5 : forall inp b, 1 <= b <= 4 -> rt_k inp b = 5.
Proof.
  intros inp b Hb.
  assert (E : b = 1 \/ b = 2 \/ b = 3 \/ b = 4) by lia.
  destruct E as [->|[->|[->| ->]]]; a_rows inp; a_fin.
Qed.

Lemma a_rtm_k11 : forall inp b, (b = 5 \/ b = 6) -> rt_n inp b <> 0 -> rt_k inp b = 11.
Proof.
  intros inp b Hb. destruct Hb as [->| ->]; a_rows inp; a_fin.
Qed.

(* ---- RTM (c): the block sums of X(0), X(1), X(2) close ---- *)

Lemma a_rtm_sum : forall inp b, 0 <= b <= 2 -> blocksum (skipn 18 (rt_g inp b)) = 0.
Proof.
  intros inp b Hb.
  assert (E : b = 0 \/ b = 1 \/ b = 2) by lia.
  destruct E as [->|[->| ->]]; a_rows inp; a_fin.
Qed.

(* ---- RTM (d): CONFIG (b = 0): match, ports, declaration ---- *)

Lemma a_rtm_want : forall inp, RcMatch.want CAT (rt_n inp 0) (rt_g inp 0) = mrow inp.
Proof. intros inp. a_rows inp; a_fin. Qed.

Lemma a_rtm_decl : forall inp, RcLeaf.decl (rt_pbs inp) = true.
Proof. intros inp. a_rows inp; a_fin. Qed.

Lemma a_rtm_in : forall inp, 4 * RcLeaf.n_in (rt_pbs inp) = RcDecl.box_ic (rt_mb inp).
Proof. intros inp. a_rows inp; a_fin. Qed.

Lemma a_rtm_out : forall inp, 4 * RcLeaf.n_out (rt_pbs inp) = RcDecl.box_oc (rt_mb inp).
Proof. intros inp. a_rows inp; a_fin. Qed.

Lemma a_rtm_declok : forall inp, RcDecl.decl_ok (rt_mb inp) = true.
Proof. intros inp. a_rows inp; a_fin. Qed.

Lemma a_rtm_X0 : forall inp, bsl (rt_g inp 0) 18 32 = RcDecl.decl (rt_mb inp).
Proof. intros inp. a_rows inp; a_fin. Qed.

(* ---- RTM (e): b = 3, 4: IR, the reply's outputs, ING's result 1 ---- *)

Lemma a_rtm_ir : forall inp b, (b = 3 \/ b = 4) -> ir (rt_n inp b) (rt_g inp b) = true.
Proof. intros inp b Hb. destruct Hb as [->| ->]; a_rows inp; a_fin. Qed.

Lemma a_rtm_reply : forall inp,
  r_addr (rt_g inp 3) = 0x0000 /\ r_pll (rt_g inp 3) = 4 /\ r_addr (rt_g inp 4) = 0x0600 /\ r_pll (rt_g inp 4) = 8.
Proof. intros inp. a_rows inp; a_fin. Qed.

Lemma a_rtm_ing34 : forall inp (b : nat), (b = 3 \/ b = 4)%nat ->
  fst (ING (RID inp b) (r_addr (rt_g inp (Z.of_nat b))) (r_pl (rt_g inp (Z.of_nat b)))) = 1.
Proof. intros inp b Hb. destruct Hb as [->| ->]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; a_rows inp; a_fin. Qed.

(* ---- RTM (f): b = 5 FIRST, b = 6 CLOSE on RFG_6, ING's result 1 ---- *)

Lemma a_rtm_first : forall inp, rt_n inp 5 <> 0 -> fcls (rt_n inp 5) (RFG inp 5) (rt_g inp 5) = FgFirst.
Proof. intros inp. a_rows inp; a_fin. Qed.

Lemma a_rtm_close : forall inp, rt_n inp 6 <> 0 -> fcls (rt_n inp 6) (RFG inp 6) (rt_g inp 6) = FgClose.
Proof. intros inp. a_rows inp; a_fin. Qed.

Lemma a_rtm_close_vals : forall inp, rt_n inp 6 <> 0 ->
  fg_addr (RFG inp 6) (rt_g inp 6) = 0x1000 /\ f_pll (RFG inp 6) (rt_g inp 6) = 17.
Proof. intros inp. a_rows inp; a_fin. Qed.

Lemma a_rtm_ing6 : forall inp, rt_n inp 6 <> 0 ->
  fst (ING (RID inp 6) (fg_addr (RFG inp 6) (rt_g inp 6)) (f_pl (rt_n inp 6) (RFG inp 6) (rt_g inp 6))) = 1.
Proof. intros inp. a_rows inp; a_fin. Qed.

(* ---- RTM (g): RID_7 holds the row's firmware, version and (with an identity record) name ---- *)

Lemma a_rtm_fw : forall inp, has_fw (RID inp 7) = 1 /\
  fw_milli (RID inp 7) = RcDecl.rval (rt_mb inp) 266 + 256 * RcDecl.rval (rt_mb inp) 267.
Proof. intros inp. a_rows inp; a_fin. Qed.

Lemma a_rtm_ver : forall inp, has_reac_version (RID inp 7) = 1 /\
  major (RID inp 7) = RcDecl.rval (rt_mb inp) 268 + 256 * RcDecl.rval (rt_mb inp) 269 /\
  minor (RID inp 7) = RcDecl.rval (rt_mb inp) 270 + 256 * RcDecl.rval (rt_mb inp) 271 /\
  patch (RID inp 7) = RcDecl.rval (rt_mb inp) 272 + 256 * RcDecl.rval (rt_mb inp) 273.
Proof. intros inp. a_rows inp; a_fin. Qed.

Lemma a_rtm_name : forall inp, rt_n inp 6 <> 0 ->
  has_model_name (RID inp 7) = 1 /\ firstn (length (rt_nb inp)) (model_name (RID inp 7)) = rt_nb inp /\
  last (rt_nb inp) (zb 1) = zb 0 /\ forallb (fun x => negb (bz x =? 0)) (removelast (rt_nb inp)) = true /\
  (Nat.leb 2 (length (rt_nb inp)) && Nat.leb (length (rt_nb inp)) 16)%bool = true.
Proof. intros inp. a_rows inp; a_fin. Qed.

(* ---- The round-trip state across turn b (no computation) ---- *)

Lemma a_st_S : forall inp (b : nat), rt_st inp (S b) =
  let s := rt_st inp b in let x := Z.of_nat b in
  if rt_n inp x =? 0 then s
  else if (x =? 3) || (x =? 4) then (rp_id (fst s) (rt_n inp x) (rt_g inp x), snd s)
  else if (x =? 5) || (x =? 6) then (fg_id (fst s) (rt_n inp x) (snd s) (rt_g inp x), fg_st (rt_n inp x) (snd s) (rt_g inp x))
  else s.
Proof. intros inp b. reflexivity. Qed.

Lemma a_RS_012 : forall inp (b : nat), (b <= 2)%nat -> RID inp (S b) = RID inp b /\ RFG inp (S b) = RFG inp b.
Proof.
  intros inp b Hb. unfold RID, RFG. rewrite a_st_S. cbv zeta.
  destruct (rt_n inp (Z.of_nat b) =? 0); [split; reflexivity|].
  replace ((Z.of_nat b =? 3) || (Z.of_nat b =? 4)) with false by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; lia).
  replace ((Z.of_nat b =? 5) || (Z.of_nat b =? 6)) with false by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; lia).
  split; reflexivity.
Qed.

Lemma a_RS_34 : forall inp (b : nat), (b = 3 \/ b = 4)%nat -> rt_n inp (Z.of_nat b) <> 0 ->
  RID inp (S b) = rp_id (RID inp b) (rt_n inp (Z.of_nat b)) (rt_g inp (Z.of_nat b)) /\ RFG inp (S b) = RFG inp b.
Proof.
  intros inp b Hb Hn. unfold RID, RFG. rewrite a_st_S. cbv zeta.
  rewrite (proj2 (Z.eqb_neq _ 0) Hn).
  replace ((Z.of_nat b =? 3) || (Z.of_nat b =? 4)) with true
    by (symmetry; apply orb_true_iff; destruct Hb as [->| ->]; [left | right]; reflexivity).
  split; reflexivity.
Qed.

Lemma a_RS_56 : forall inp (b : nat), (b = 5 \/ b = 6)%nat -> rt_n inp (Z.of_nat b) <> 0 ->
  RID inp (S b) = fg_id (RID inp b) (rt_n inp (Z.of_nat b)) (RFG inp b) (rt_g inp (Z.of_nat b)) /\
  RFG inp (S b) = fg_st (rt_n inp (Z.of_nat b)) (RFG inp b) (rt_g inp (Z.of_nat b)).
Proof.
  intros inp b Hb Hn. unfold RID, RFG. rewrite a_st_S. cbv zeta.
  rewrite (proj2 (Z.eqb_neq _ 0) Hn).
  replace ((Z.of_nat b =? 3) || (Z.of_nat b =? 4)) with false
    by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; lia).
  replace ((Z.of_nat b =? 5) || (Z.of_nat b =? 6)) with true
    by (symmetry; apply orb_true_iff; destruct Hb as [->| ->]; [left | right]; reflexivity).
  split; reflexivity.
Qed.

(* ---- The 11 catalogue rows of image A ---- *)

Lemma a_row_img : forall i, 0 <= i < 11 -> Image.image_bytes rsegs (CAT + CAT_ROW * i) 296 = Some (rowb i).
Proof.
  intros i Hi.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]];
    unfold rowb, img; (destruct (Image.image_bytes _ _ _) eqn:E; [reflexivity | vm_compute in E; discriminate E]).
Qed.

(* An address inside one of the registered globals of frame_AG (boolean form). *)
Definition a_inAG (a : Z) : bool :=
  existsb (fun p => (fst p <=? a) && (a <? fst p + snd p)) AFm.frame_AG.

Lemma a_inAG_sound : forall a, a_inAG a = true -> YLg.in_globals AFm.frame_AG a.
Proof.
  intros a H. unfold a_inAG in H. apply existsb_exists in H. destruct H as ([lo len] & Hin & Hb).
  cbn [fst snd] in Hb. apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists lo, len. split; [exact Hin | lia].
Qed.

(* Per row: the s32 at + 56 is a u32 that is 0 exactly when em_hid is; with an identity record the name pointer
   (+ 280) is a nonzero low-image address whose C string (the round trip's rt_nb) is read-only image bytes, inside
   frame_AG byte by byte. *)
Definition a_rowchk (i : Z) : bool :=
  let r := rowb i in let h := RcSynth.rw32 r 56 in let nm := RcSynth.rname r in
  (0 <=? h) && (h <? 2 ^ 32) && Bool.eqb (RcEmit.em_hid r =? 0) (h =? 0) &&
  ((RcEmit.em_hid r =? 0) ||
   ((0 <? nm) && (nm + 17 <=? 6283264) && Image.ro_bytes_b rsegs nm (img_cstr nm 16) &&
    forallb (fun k => a_inAG (nm + Z.of_nat k)) (seq 0 (length (img_cstr nm 16))))).

Lemma a_rowchk_all : forallb a_rowchk (map Z.of_nat (seq 0 11)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma a_rowchk_i : forall i, 0 <= i < 11 -> a_rowchk i = true.
Proof.
  intros i Hi. pose proof a_rowchk_all as H. rewrite forallb_forall in H. apply H.
  apply in_map_iff. exists (Z.to_nat i). split; [lia | apply in_seq; lia].
Qed.

Lemma a_bytes_eq : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

(* The u32 at + 56 and the u64 at + 280 of each row as little-endian words. *)
Lemma a_row_le : forall i, 0 <= i < 11 ->
  firstn 4 (skipn 56 (rowb i)) = lib.Lib.Mem.le4 (Z_to_bv 64 (RcSynth.rw32 (rowb i) 56)) /\
  firstn 8 (skipn 280 (rowb i)) = lib.Lib.Mem.le8 (Z_to_bv 64 (RcSynth.rname (rowb i))).
Proof.
  intros i Hi.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]];
    split; apply a_bytes_eq; vm_compute; reflexivity.
Qed.

Lemma a_row_facts : forall i, 0 <= i < 11 ->
  0 <= RcSynth.rw32 (rowb i) 56 < 2 ^ 32 /\
  (RcEmit.em_hid (rowb i) = 0 <-> RcSynth.rw32 (rowb i) 56 = 0) /\
  (RcEmit.em_hid (rowb i) <> 0 ->
     0 < RcSynth.rname (rowb i) /\ RcSynth.rname (rowb i) + 17 <= 6283264 /\
     Image.ro_bytes_b rsegs (RcSynth.rname (rowb i)) (img_cstr (RcSynth.rname (rowb i)) 16) = true /\
     forall k, (k < length (img_cstr (RcSynth.rname (rowb i)) 16))%nat ->
       YLg.in_globals AFm.frame_AG (RcSynth.rname (rowb i) + Z.of_nat k)).
Proof.
  intros i Hi. pose proof (a_rowchk_i i Hi) as H. unfold a_rowchk in H. cbv zeta in H.
  rewrite !andb_true_iff in H. destruct H as [[[H1 H2] H3] H4].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Bool.eqb_prop in H3.
  split; [lia|]. split.
  - destruct (Z.eqb_spec (RcEmit.em_hid (rowb i)) 0) as [E|E];
      destruct (Z.eqb_spec (RcSynth.rw32 (rowb i) 56) 0) as [E'|E']; try discriminate H3; tauto.
  - intros Hn. apply orb_true_iff in H4. destruct H4 as [H4|H4]; [apply Z.eqb_eq in H4; contradiction|].
    rewrite !andb_true_iff in H4. destruct H4 as [[[H5 H6] H7] H8].
    apply Z.ltb_lt in H5. apply Z.leb_le in H6. split; [lia|]. split; [lia|]. split; [exact H7|].
    intros k Hk. apply a_inAG_sound. rewrite forallb_forall in H8. apply H8. apply in_seq. lia.
Qed.
