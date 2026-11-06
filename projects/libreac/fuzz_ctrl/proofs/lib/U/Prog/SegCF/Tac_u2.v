(* Batch u2 helpers of the fuzz_ctrl LLVMFuzzerTestOneInput slot proof (ubsan).
   RTM (slot-plan.md 6.3, slot-plan-ubsan.md 6.3): the round-trip model facts, for every catalogue row of this
   build (T' = 0x1fcc8, the ubsan image and build_as contract). Every round-trip value is a function of OUR and
   i* only (u2_cn below rebuilds an input with the same two), so each fact is computed over the 11 rows with the
   6 bytes of OUR left as variables. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcParse RcReply RcIdentModel RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLeaf RcPorts RcEmit RcSynth RcDecl RcMatch.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require reac_ctrl_build_as_c.
Import ListNotations.
Open Scope Z_scope.

Lemma u2_istar_range : forall inp, 0 <= istar inp < 11.
Proof. intros inp. unfold istar, CAT_N. apply Z.mod_pos_bound. lia. Qed.

(* ---- Every round-trip value depends on the input only through OUR and i* ---- *)

Section Cong.
Variables inp inp' : list byte.
Hypothesis HO : OUR inp = OUR inp'.
Hypothesis HI : istar inp = istar inp'.

Lemma u2c_mrow : mrow inp = mrow inp'.
Proof using HO HI. unfold mrow. rewrite HI. reflexivity. Qed.

Lemma u2c_mb : rt_mb inp = rt_mb inp'.
Proof using HO HI. unfold rt_mb. rewrite HI. reflexivity. Qed.

Lemma u2c_nb : rt_nb inp = rt_nb inp'.
Proof using HO HI. unfold rt_nb. rewrite u2c_mb. reflexivity. Qed.

Lemma u2c_n : forall b, rt_n inp b = rt_n inp' b.
Proof using HO HI. intros b. unfold rt_n, rt_E, rt_uw. rewrite u2c_mrow, u2c_mb. reflexivity. Qed.

Lemma u2c_X : forall b, rt_X inp b = rt_X inp' b.
Proof using HO HI. intros b. unfold rt_X. rewrite u2c_mrow, u2c_mb, u2c_nb. reflexivity. Qed.

Lemma u2c_F : forall b, rt_F inp b = rt_F inp' b.
Proof using HO HI. intros b. unfold rt_F. rewrite HO, u2c_X, u2c_n. reflexivity. Qed.

Lemma u2c_g : forall b, rt_g inp b = rt_g inp' b.
Proof using HO HI. intros b. unfold rt_g. rewrite u2c_F. reflexivity. Qed.

Lemma u2c_k : forall b, rt_k inp b = rt_k inp' b.
Proof using HO HI. intros b. unfold rt_k. rewrite u2c_n, u2c_g. reflexivity. Qed.

Lemma u2c_pbs : rt_pbs inp = rt_pbs inp'.
Proof using HO HI. unfold rt_pbs. rewrite u2c_g. reflexivity. Qed.

Lemma u2c_st : forall b, rt_st inp b = rt_st inp' b.
Proof using HO HI.
  induction b as [|b IH]; [reflexivity|].
  cbn [rt_st]. rewrite IH, !u2c_n, !u2c_g. reflexivity.
Qed.

Lemma u2c_RID : forall b, RID inp b = RID inp' b.
Proof using HO HI. intros b. unfold RID. rewrite u2c_st. reflexivity. Qed.

Lemma u2c_RFG : forall b, RFG inp b = RFG inp' b.
Proof using HO HI. intros b. unfold RFG. rewrite u2c_st. reflexivity. Qed.

End Cong.

(* The canonical input: OUR, then the mode byte 2 i. *)
Definition u2_cn (our : list byte) (i : Z) : list byte := our ++ [zb (2 * i)].

Lemma u2_cn_OUR : forall our i, length our = 6%nat -> OUR (u2_cn our i) = our.
Proof.
  intros our i H. destruct our as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|? ?]]]]]]]; try discriminate H.
  reflexivity.
Qed.

Lemma u2_cn_istar : forall our i, length our = 6%nat -> 0 <= i < 11 -> istar (u2_cn our i) = i.
Proof.
  intros our i H Hi. destruct our as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|? ?]]]]]]]; try discriminate H.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]; vm_compute; reflexivity.
Qed.

(* Rewrite every round-trip value at inp to the canonical input of (OUR inp, istar inp), then split into the 11
   rows with OUR = 6 variables. The goal must mention inp only through the functions rewritten here. *)
Ltac u2_rows inp :=
  let HO := fresh "HO" in let HI := fresh "HI" in
  assert (HO : OUR inp = OUR (u2_cn (OUR inp) (istar inp)))
    by (symmetry; apply u2_cn_OUR, OUR_length);
  assert (HI : istar inp = istar (u2_cn (OUR inp) (istar inp)))
    by (symmetry; apply u2_cn_istar; [apply OUR_length | apply u2_istar_range]);
  rewrite ?(u2c_k _ _ HO HI), ?(u2c_n _ _ HO HI), ?(u2c_g _ _ HO HI), ?(u2c_F _ _ HO HI), ?(u2c_X _ _ HO HI),
    ?(u2c_RID _ _ HO HI), ?(u2c_RFG _ _ HO HI), ?(u2c_pbs _ _ HO HI), ?(u2c_mb _ _ HO HI),
    ?(u2c_nb _ _ HO HI), ?(u2c_mrow _ _ HO HI);
  clear HO HI;
  generalize (OUR_length inp) (u2_istar_range inp);
  generalize (OUR inp) (istar inp);
  let our := fresh "our" in let i := fresh "i" in let HL := fresh "HL" in let Hi := fresh "Hi" in
  intros our i HL Hi;
  destruct our as [|?x0 [|?x1 [|?x2 [|?x3 [|?x4 [|?x5 [|? ?]]]]]]]; try discriminate HL; clear HL;
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10)
    by lia;
  clear Hi;
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]].

(* Close a computed goal: `P`, `x <> y`, `A -> P` with A false or true, conjunctions, iff of two decided facts. *)
Ltac u2_fin :=
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

Lemma u2_rtm_n_on : forall inp b, 0 <= b <= 4 -> rt_n inp b <> 0.
Proof.
  intros inp b Hb.
  assert (E : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4) by lia.
  destruct E as [->|[->|[->|[->| ->]]]]; u2_rows inp; u2_fin.
Qed.

Lemma u2_rtm_n56 : forall inp, rt_n inp 6 = rt_n inp 5.
Proof. intros inp. u2_rows inp; u2_fin. Qed.

(* E(5) = E(6) is has_identity_record(m) != 0 (the s32 at m + 56). *)
Lemma u2_rtm_hid : forall inp, rt_n inp 6 <> 0 <-> RcEmit.em_hid (rt_mb inp) <> 0.
Proof. intros inp. u2_rows inp; u2_fin. Qed.

(* ---- RTM (b): k_b = 9, 5, 5, 5, 5, 11, 11 ---- *)

Lemma u2_rtm_k0 : forall inp, rt_k inp 0 = 9.
Proof. intros inp. u2_rows inp; u2_fin. Qed.

Lemma u2_rtm_k5 : forall inp b, 1 <= b <= 4 -> rt_k inp b = 5.
Proof.
  intros inp b Hb.
  assert (E : b = 1 \/ b = 2 \/ b = 3 \/ b = 4) by lia.
  destruct E as [->|[->|[->| ->]]]; u2_rows inp; u2_fin.
Qed.

Lemma u2_rtm_k11 : forall inp b, (b = 5 \/ b = 6) -> rt_n inp b <> 0 -> rt_k inp b = 11.
Proof.
  intros inp b Hb. destruct Hb as [->| ->]; u2_rows inp; u2_fin.
Qed.

(* ---- RTM (c): the block sums of X(0), X(1), X(2) close ---- *)

Lemma u2_rtm_sum : forall inp b, 0 <= b <= 2 -> blocksum (skipn 18 (rt_g inp b)) = 0.
Proof.
  intros inp b Hb.
  assert (E : b = 0 \/ b = 1 \/ b = 2) by lia.
  destruct E as [->|[->| ->]]; u2_rows inp; u2_fin.
Qed.

(* ---- RTM (d): CONFIG (b = 0): match, ports, declaration ---- *)

Lemma u2_rtm_want : forall inp, RcMatch.want CAT (rt_n inp 0) (rt_g inp 0) = mrow inp.
Proof. intros inp. u2_rows inp; u2_fin. Qed.

Lemma u2_rtm_decl : forall inp, RcLeaf.decl (rt_pbs inp) = true.
Proof. intros inp. u2_rows inp; u2_fin. Qed.

Lemma u2_rtm_in : forall inp, 4 * RcLeaf.n_in (rt_pbs inp) = RcDecl.box_ic (rt_mb inp).
Proof. intros inp. u2_rows inp; u2_fin. Qed.

Lemma u2_rtm_out : forall inp, 4 * RcLeaf.n_out (rt_pbs inp) = RcDecl.box_oc (rt_mb inp).
Proof. intros inp. u2_rows inp; u2_fin. Qed.

Lemma u2_rtm_declok : forall inp, RcDecl.decl_ok (rt_mb inp) = true.
Proof. intros inp. u2_rows inp; u2_fin. Qed.

Lemma u2_rtm_X0 : forall inp, bsl (rt_g inp 0) 18 32 = RcDecl.decl (rt_mb inp).
Proof. intros inp. u2_rows inp; u2_fin. Qed.

(* ---- RTM (e): b = 3, 4: IR, the reply's outputs, ING's result 1 ---- *)

Lemma u2_rtm_ir : forall inp b, (b = 3 \/ b = 4) -> ir (rt_n inp b) (rt_g inp b) = true.
Proof. intros inp b Hb. destruct Hb as [->| ->]; u2_rows inp; u2_fin. Qed.

Lemma u2_rtm_reply : forall inp,
  r_addr (rt_g inp 3) = 0x0000 /\ r_pll (rt_g inp 3) = 4 /\ r_addr (rt_g inp 4) = 0x0600 /\ r_pll (rt_g inp 4) = 8.
Proof. intros inp. u2_rows inp; u2_fin. Qed.

Lemma u2_rtm_ing34 : forall inp (b : nat), (b = 3 \/ b = 4)%nat ->
  fst (ING (RID inp b) (r_addr (rt_g inp (Z.of_nat b))) (r_pl (rt_g inp (Z.of_nat b)))) = 1.
Proof. intros inp b Hb. destruct Hb as [->| ->]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u2_rows inp; u2_fin. Qed.

(* ---- RTM (f): b = 5 FIRST, b = 6 CLOSE on RFG_6, ING's result 1 ---- *)

Lemma u2_rtm_first : forall inp, rt_n inp 5 <> 0 -> fcls (rt_n inp 5) (RFG inp 5) (rt_g inp 5) = FgFirst.
Proof. intros inp. u2_rows inp; u2_fin. Qed.

Lemma u2_rtm_close : forall inp, rt_n inp 6 <> 0 -> fcls (rt_n inp 6) (RFG inp 6) (rt_g inp 6) = FgClose.
Proof. intros inp. u2_rows inp; u2_fin. Qed.

Lemma u2_rtm_close_vals : forall inp, rt_n inp 6 <> 0 ->
  fg_addr (RFG inp 6) (rt_g inp 6) = 0x1000 /\ f_pll (RFG inp 6) (rt_g inp 6) = 17.
Proof. intros inp. u2_rows inp; u2_fin. Qed.

Lemma u2_rtm_ing6 : forall inp, rt_n inp 6 <> 0 ->
  fst (ING (RID inp 6) (fg_addr (RFG inp 6) (rt_g inp 6)) (f_pl (rt_n inp 6) (RFG inp 6) (rt_g inp 6))) = 1.
Proof. intros inp. u2_rows inp; u2_fin. Qed.

(* ---- RTM (g): RID_7 holds the row's firmware, version and (with an identity record) name ---- *)

Lemma u2_rtm_fw : forall inp, has_fw (RID inp 7) = 1 /\
  fw_milli (RID inp 7) = RcDecl.rval (rt_mb inp) 266 + 256 * RcDecl.rval (rt_mb inp) 267.
Proof. intros inp. u2_rows inp; u2_fin. Qed.

Lemma u2_rtm_ver : forall inp, has_reac_version (RID inp 7) = 1 /\
  major (RID inp 7) = RcDecl.rval (rt_mb inp) 268 + 256 * RcDecl.rval (rt_mb inp) 269 /\
  minor (RID inp 7) = RcDecl.rval (rt_mb inp) 270 + 256 * RcDecl.rval (rt_mb inp) 271 /\
  patch (RID inp 7) = RcDecl.rval (rt_mb inp) 272 + 256 * RcDecl.rval (rt_mb inp) 273.
Proof. intros inp. u2_rows inp; u2_fin. Qed.

Lemma u2_rtm_name : forall inp, rt_n inp 6 <> 0 ->
  has_model_name (RID inp 7) = 1 /\ firstn (length (rt_nb inp)) (model_name (RID inp 7)) = rt_nb inp /\
  last (rt_nb inp) (zb 1) = zb 0 /\ forallb (fun x => negb (bz x =? 0)) (removelast (rt_nb inp)) = true /\
  (Nat.leb 2 (length (rt_nb inp)) && Nat.leb (length (rt_nb inp)) 16)%bool = true.
Proof. intros inp. u2_rows inp; u2_fin. Qed.

(* ---- The round-trip state across turn b (no computation) ---- *)

Lemma u2_st_S : forall inp (b : nat), rt_st inp (S b) =
  let s := rt_st inp b in let x := Z.of_nat b in
  if rt_n inp x =? 0 then s
  else if (x =? 3) || (x =? 4) then (rp_id (fst s) (rt_n inp x) (rt_g inp x), snd s)
  else if (x =? 5) || (x =? 6) then (fg_id (fst s) (rt_n inp x) (snd s) (rt_g inp x), fg_st (rt_n inp x) (snd s) (rt_g inp x))
  else s.
Proof. intros inp b. reflexivity. Qed.

Lemma u2_RS_012 : forall inp (b : nat), (b <= 2)%nat -> RID inp (S b) = RID inp b /\ RFG inp (S b) = RFG inp b.
Proof.
  intros inp b Hb. unfold RID, RFG. rewrite u2_st_S. cbv zeta.
  destruct (rt_n inp (Z.of_nat b) =? 0); [split; reflexivity|].
  replace ((Z.of_nat b =? 3) || (Z.of_nat b =? 4)) with false by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; lia).
  replace ((Z.of_nat b =? 5) || (Z.of_nat b =? 6)) with false by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; lia).
  split; reflexivity.
Qed.

Lemma u2_RS_34 : forall inp (b : nat), (b = 3 \/ b = 4)%nat -> rt_n inp (Z.of_nat b) <> 0 ->
  RID inp (S b) = rp_id (RID inp b) (rt_n inp (Z.of_nat b)) (rt_g inp (Z.of_nat b)) /\ RFG inp (S b) = RFG inp b.
Proof.
  intros inp b Hb Hn. unfold RID, RFG. rewrite u2_st_S. cbv zeta.
  rewrite (proj2 (Z.eqb_neq _ 0) Hn).
  replace ((Z.of_nat b =? 3) || (Z.of_nat b =? 4)) with true
    by (symmetry; apply orb_true_iff; destruct Hb as [->| ->]; [left | right]; reflexivity).
  split; reflexivity.
Qed.

Lemma u2_RS_56 : forall inp (b : nat), (b = 5 \/ b = 6)%nat -> rt_n inp (Z.of_nat b) <> 0 ->
  RID inp (S b) = fg_id (RID inp b) (rt_n inp (Z.of_nat b)) (RFG inp b) (rt_g inp (Z.of_nat b)) /\
  RFG inp (S b) = fg_st (rt_n inp (Z.of_nat b)) (RFG inp b) (rt_g inp (Z.of_nat b)).
Proof.
  intros inp b Hb Hn. unfold RID, RFG. rewrite u2_st_S. cbv zeta.
  rewrite (proj2 (Z.eqb_neq _ 0) Hn).
  replace ((Z.of_nat b =? 3) || (Z.of_nat b =? 4)) with false
    by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; lia).
  replace ((Z.of_nat b =? 5) || (Z.of_nat b =? 6)) with true
    by (symmetry; apply orb_true_iff; destruct Hb as [->| ->]; [left | right]; reflexivity).
  split; reflexivity.
Qed.
