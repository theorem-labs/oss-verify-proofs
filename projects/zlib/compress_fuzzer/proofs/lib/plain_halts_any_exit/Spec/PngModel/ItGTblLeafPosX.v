(** * OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.ItGTblLeafPosX — leaf value positivity for EVERY table type

    the LENS and CODES analogues of
    [ItGTblLeafPos.it_model_leafpos] (which is DISTS-only), obtained by
    generalising the loop lemmas over ANY context whose [it_here] entries are
    leaf-positive, plus the write-back lemma [leafpos_codes_wb] and the fixed
    tables.  Theory-only header: this leaf is meant to be Required by the
    ReachCore home (StepReach) for the row [rc_leafpos : LeafPosT (t_codes ...)]
    (MEASURE-dcside.md ; q7's rm_off1 supplier of record). *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base Inftrees Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import ItGTblRev ItGTblGeom ItGTblSortWin ItGTblCover ItGTblRepl ItGTblLeafPos.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Open Scope Z_scope.

(** ** 1. Any context whose [it_here] is leaf-positive at every state *)
Definition HereLP (c : ItCtx) : Prop := forall st, LeafPosE (it_here c st).

Lemma leafpos_step_cont_g : forall c cnt0 st st',
  CovCtxOk c cnt0 -> CovInv c cnt0 st -> CovInv c cnt0 st' -> HereLP c ->
  LeafPosT (s_tbl st) -> it_step c st = ItCont st' -> LeafPosT (s_tbl st').
Proof.
  intros c cnt0 st st' Hctx Hinv Hinv' Hhere Ht Hstep.
  destruct Hctx as (Hroot & _ & Hmx & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  destruct Hinv as (Hlen & _ & _ & _ & _ & _ & _ & Hphase).
  assert (Hdrop : 0 <= s_drop st <= x_root c)
    by (destruct Hphase as [(Hd & _) | (Hd & _)]; lia).
  assert (Hfill : LeafPosT (it_fill
      (Z.to_nat (Z.shiftl 1 (s_curr st) / Z.shiftl 1 (s_len st - s_drop st)))
      (s_tbl st) (s_next st + Z.shiftr (s_huff st) (s_drop st))
      (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st)))
    by (apply leafpos_fill; [exact Ht | exact (Hhere st)]).
  pose proof (ptr_shape c st Hdrop) as Hsh. rewrite Hstep in Hsh.
  cbn [PtrShape] in Hsh.
  destruct Hsh as [Htbl | (cv & nx & Htbl & Hcv)].
  - rewrite Htbl. exact Hfill.
  - rewrite Htbl. apply leafpos_tset; [exact Hfill|].
    apply leafpos_ptr.
    destruct Hinv' as (Hlen' & _ & _ & _ & _ & _ & _ & Hphase').
    destruct Hphase' as [(Hd' & _) | (Hd' & Hrl' & _)]; lia.
Qed.

Lemma leafpos_step_break_g : forall c cnt0 st st1,
  CovInv c cnt0 st -> CovCtxOk c cnt0 -> HereLP c ->
  LeafPosT (s_tbl st) -> it_step c st = ItBreak st1 -> LeafPosT (s_tbl st1).
Proof.
  intros c cnt0 st st1 Hinv Hctx Hhere Ht Hstep.
  destruct Hctx as (Hroot & _).
  destruct Hinv as (Hlen & _ & _ & _ & _ & _ & _ & Hphase).
  assert (Hdrop : 0 <= s_drop st <= x_root c)
    by (destruct Hphase as [(Hd & _) | (Hd & _)]; lia).
  pose proof (ptr_shape c st Hdrop) as Hsh. rewrite Hstep in Hsh.
  cbn [PtrShape] in Hsh. rewrite Hsh.
  apply leafpos_fill; [exact Ht | exact (Hhere st)].
Qed.

Lemma leafpos_step_over_g : forall c cnt0 st t,
  CovInv c cnt0 st -> CovCtxOk c cnt0 -> HereLP c ->
  LeafPosT (s_tbl st) -> it_step c st = ItOverflow t -> LeafPosT t.
Proof.
  intros c cnt0 st t Hinv Hctx Hhere Ht Hstep.
  destruct Hctx as (Hroot & _).
  destruct Hinv as (Hlen & _ & _ & _ & _ & _ & _ & Hphase).
  assert (Hdrop : 0 <= s_drop st <= x_root c)
    by (destruct Hphase as [(Hd & _) | (Hd & _)]; lia).
  pose proof (ptr_shape c st Hdrop) as Hsh. rewrite Hstep in Hsh.
  cbn [PtrShape] in Hsh. rewrite Hsh.
  apply leafpos_fill; [exact Ht | exact (Hhere st)].
Qed.

Lemma leafpos_loop_g : forall n c cnt0 st r,
  CovCtxOk c cnt0 -> CovInv c cnt0 st -> HereLP c ->
  LeafPosT (s_tbl st) -> it_loop n c st = Some r -> LeafPosT (step_tbl r).
Proof.
  induction n as [|k IH]; intros c cnt0 st r Hctx Hinv Hhere Ht Hloop;
    cbn [it_loop] in Hloop; [discriminate Hloop|].
  destruct (it_step c st) as [st'|st1|t] eqn:Hs.
  - apply (IH c cnt0 st' r Hctx (cov_step_cont c cnt0 st st' Hctx Hinv Hs) Hhere
            (leafpos_step_cont_g c cnt0 st st' Hctx Hinv
               (cov_step_cont c cnt0 st st' Hctx Hinv Hs) Hhere Ht Hs)
            Hloop).
  - injection Hloop as <-. cbn [step_tbl].
    exact (leafpos_step_break_g c cnt0 st st1 Hinv Hctx Hhere Ht Hs).
  - injection Hloop as <-. cbn [step_tbl].
    exact (leafpos_step_over_g c cnt0 st t Hinv Hctx Hhere Ht Hs).
Qed.

(** ** 2. The three [it_here] shapes *)

(** LENS: the base arm reads [lbase]/[lext]; rows 0..28 are leaves with
    [lbase >= 3], rows 29/30 carry bit 64 ([lext] 203/77), above 30 the
    [zlist] default 0 is excluded, and a negative index aliases row 0. *)
Definition len_leaf_b (k : Z) : bool :=
  Z.eqb (Z.land (u8 (lext k)) 240) 0
  || negb (Z.eqb (Z.land (u8 (lext k)) 64) 0)
  || Z.leb 1 (u16 (lbase k)).

Lemma len_leaf_b_all : forallb len_leaf_b (map Z.of_nat (seq 0 31)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma len_leaf_in_range : forall k, 0 <= k < 31 -> len_leaf_b k = true.
Proof.
  intros k Hk.
  exact (forallb_range len_leaf_b 31%nat len_leaf_b_all k ltac:(cbn; lia)).
Qed.

Lemma lext_above : forall k, 31 <= k -> lext k = 0.
Proof.
  intros k Hk. unfold lext, zlist. apply nth_overflow.
  change (length lext_l) with 31%nat. lia.
Qed.

Lemma lext_below : forall k, k <= 0 -> lext k = lext 0.
Proof.
  intros k Hk. unfold lext, zlist.
  assert (H : Z.to_nat k = Z.to_nat 0) by lia. rewrite H. reflexivity.
Qed.

Lemma lbase_below : forall k, k <= 0 -> lbase k = lbase 0.
Proof.
  intros k Hk. unfold lbase, zlist.
  assert (H : Z.to_nat k = Z.to_nat 0) by lia. rewrite H. reflexivity.
Qed.

Theorem leafpos_len_entry : forall k b, LeafPosE (mkCodeT (lext k) b (lbase k)).
Proof.
  intros k b.
  destruct (Z_lt_le_dec k 0) as [Hneg | Hnn].
  - rewrite (lext_below k ltac:(lia)), (lbase_below k ltac:(lia)).
    intros _ _.
    assert (Hv : c_val (mkCodeT (lext 0) b (lbase 0)) = 3)
      by (vm_compute; reflexivity).
    rewrite Hv. lia.
  - destruct (Z_lt_le_dec k 31) as [Hlt | Hge].
    + pose proof (len_leaf_in_range k ltac:(lia)) as Hb.
      unfold len_leaf_b in Hb.
      intros H240 H64. unfold mkCodeT in *. cbn [c_op c_val] in *.
      apply orb_true_iff in Hb. destruct Hb as [Hb | Hv].
      * apply orb_true_iff in Hb. destruct Hb as [H0 | Hm].
        -- exfalso. apply H240. apply Z.eqb_eq. exact H0.
        -- exfalso. apply negb_true_iff, Z.eqb_neq in Hm. exact (Hm H64).
      * apply Z.leb_le. exact Hv.
    + rewrite (lext_above k Hge). apply leafpos_op_zero.
Qed.

Theorem leafpos_here_lens : forall c,
  x_match c = 257 -> x_base c = lbase -> x_extra c = lext -> HereLP c.
Proof.
  intros c Hm Hb He st. unfold it_here. cbv zeta.
  destruct (Z.ltb (x_work c (s_sym st) + 1) (x_match c)).
  - apply leafpos_op_zero.
  - destruct (Z.leb (x_match c) (x_work c (s_sym st))).
    + rewrite He, Hb. apply leafpos_len_entry.
    + apply leafpos_marker. vm_compute. discriminate.
Qed.

(** CODES (and any other [ty]): [it_pre] points base and extra at the SAME
    array ([wk]), so the base arm's entry has [op = val] up to the [u8]/[u16]
    casts, and a nonzero low byte in [0xF0] forces the value to be at least 16. *)
Theorem leafpos_same_entry : forall v b, LeafPosE (mkCodeT v b v).
Proof.
  intros v b H240 _. unfold mkCodeT in *. cbn [c_op c_val] in *.
  pose proof (Z.mod_pos_bound v 65536 ltac:(lia)) as Hr. unfold u16.
  destruct (Z.eq_dec (v mod 65536) 0) as [Hz|Hnz]; [|lia].
  exfalso. apply H240. unfold u8.
  assert (Hd : (65536 | v)) by (apply Z.mod_divide; [lia|exact Hz]).
  assert (Hd2 : (256 | v)) by (eapply Z.divide_trans; [exists 256; reflexivity|exact Hd]).
  rewrite (proj2 (Z.mod_divide v 256 ltac:(lia)) Hd2). reflexivity.
Qed.

Theorem leafpos_here_same : forall c,
  x_base c = x_extra c -> HereLP c.
Proof.
  intros c Hbe st. unfold it_here. cbv zeta.
  destruct (Z.ltb (x_work c (s_sym st) + 1) (x_match c)).
  - apply leafpos_op_zero.
  - destruct (Z.leb (x_match c) (x_work c (s_sym st))).
    + rewrite Hbe. apply leafpos_same_entry.
    + apply leafpos_marker. vm_compute. discriminate.
Qed.

(** ** 3. [it_pre]'s context fields, for every type *)
Lemma it_pre_go_ctx : forall ty lens codes root0 t0 c st,
  it_pre ty lens codes root0 t0 = PreGo c st ->
  (ty = CT_LENS /\ x_match c = 257 /\ x_base c = lbase /\ x_extra c = lext)
  \/ (ty = CT_DISTS /\ x_match c = 0 /\ x_base c = dbase /\ x_extra c = dext)
  \/ (ty <> CT_LENS /\ ty <> CT_DISTS /\ x_base c = x_extra c).
Proof.
  intros ty lens codes root0 t0 c st H.
  unfold it_pre in H. cbv zeta in H.
  destruct (Z.eqb (it_findmax 15%nat MAXBITS (it_count (Z.to_nat codes) 0 lens zzero)) 0);
    [discriminate H|].
  destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero)) as [lft|];
    [|discriminate H].
  destruct (it_incomplete ty lft _); [discriminate H|].
  destruct (it_enough ty _); [discriminate H|].
  injection H as Hc _. rewrite <- Hc. cbn [x_match x_base x_extra].
  destruct (Z.eqb ty CT_LENS) eqn:EL.
  - left. apply Z.eqb_eq in EL. repeat split; assumption || reflexivity.
  - destruct (Z.eqb ty CT_DISTS) eqn:ED.
    + right; left. apply Z.eqb_eq in ED. repeat split; assumption || reflexivity.
    + right; right. apply Z.eqb_neq in EL. apply Z.eqb_neq in ED.
      repeat split; assumption || reflexivity.
Qed.

Lemma it_pre_go_herelp : forall ty lens codes root0 t0 c st,
  it_pre ty lens codes root0 t0 = PreGo c st -> HereLP c.
Proof.
  intros ty lens codes root0 t0 c st H.
  destruct (it_pre_go_ctx ty lens codes root0 t0 c st H)
    as [(_ & Hm & Hb & He) | [(_ & Hm & Hb & He) | (_ & _ & Hbe)]].
  - exact (leafpos_here_lens c Hm Hb He).
  - intros st'. exact (leafpos_here_dists c st' Hm Hb He).
  - exact (leafpos_here_same c Hbe).
Qed.

(** ** 4. THE THEOREM, for every [ty] *)
Theorem it_model_leafpos_any : forall ty lens codes root0 t0 out,
  0 <= codes ->
  (forall i, 0 <= i < codes -> 0 <= lens i <= 15) ->
  1 <= root0 <= 15 ->
  LeafPosT t0 ->
  it_model ty lens codes root0 t0 = Some out ->
  LeafPosT (o_tbl out).
Proof.
  intros ty lens codes root0 t0 out Hcodes Hlens Hroot0 Ht0 Hmodel.
  unfold it_model in Hmodel.
  destruct (it_pre ty lens codes root0 t0) as [ | temp | | c st] eqn:Hpre.
  - injection Hmodel as <-. cbn [o_tbl]. exact Ht0.
  - rewrite (it_pre_empty_shape ty lens codes root0 t0 temp Hpre) in Hmodel.
    injection Hmodel as <-. cbn [o_tbl].
    apply leafpos_tset; [apply leafpos_tset; [exact Ht0|]|];
      apply leafpos_marker; vm_compute; discriminate.
  - injection Hmodel as <-. cbn [o_tbl]. exact Ht0.
  - destruct (cov_pre ty lens codes root0 t0 c st Hcodes Hlens Hroot0 Hpre)
      as [Hctx Hinv].
    pose proof (it_pre_go_herelp ty lens codes root0 t0 c st Hpre) as Hhere.
    assert (Htbl : LeafPosT (s_tbl st))
      by (rewrite (it_pre_go_tbl ty lens codes root0 t0 c st Hpre); exact Ht0).
    destruct (it_loop (S (Z.to_nat codes)) c st) as [[st'|st'|tt]|] eqn:Hloop;
      try discriminate Hmodel; injection Hmodel as <-; cbn [o_tbl].
    + apply leafpos_finish.
      exact (leafpos_loop_g (S (Z.to_nat codes)) c (sw_cnt lens codes) st
               (ItBreak st') Hctx Hinv Hhere Htbl Hloop).
    + exact (leafpos_loop_g (S (Z.to_nat codes)) c (sw_cnt lens codes) st
               (ItOverflow tt) Hctx Hinv Hhere Htbl Hloop).
Qed.

(** The [it_wf] form the installer sites hold. *)
Corollary it_model_leafpos_wf : forall ty lens codes root0 t0 out,
  it_wf ty lens codes root0 ->
  LeafPosT t0 ->
  it_model ty lens codes root0 t0 = Some out ->
  LeafPosT (o_tbl out).
Proof.
  intros ty lens codes root0 t0 out (Hc & Hl & Hr & _) Ht0 Hm.
  refine (it_model_leafpos_any ty lens codes root0 t0 out _ _ _ Ht0 Hm); unfold MAXBITS in *; [lia|exact Hl|lia].
Qed.

(** ** 5. Write-back and the fixed tables *)
Lemma leafpos_shift : forall cs k, LeafPosT cs -> LeafPosT (fun i => cs (k + i)).
Proof. intros cs k H i. exact (H (k + i)). Qed.

Lemma leafpos_codes_wb : forall cs k t,
  LeafPosT cs -> LeafPosT t -> LeafPosT (codes_wb cs k t).
Proof.
  intros cs k t Hcs Ht i. unfold codes_wb.
  destruct (Z.leb k i); [exact (Ht (i - k)) | exact (Hcs i)].
Qed.

(* [tbl_of_list] builds RAW [mkCode] entries (no casts), so the check is raw too. *)
Definition lp3 (t : Z*Z*Z) : bool :=
  let '(op,_,val) := t in
  (Z.land op 240 =? 0) || negb (Z.land op 64 =? 0) || (1 <=? val).

Lemma distfix_lp : forallb lp3 distfix_list = true. Proof. vm_compute. reflexivity. Qed.
Lemma lenfix_lp  : forallb lp3 lenfix_list  = true. Proof. vm_compute. reflexivity. Qed.

Lemma tbl_of_list_lp : forall l, forallb lp3 l = true -> LeafPosT (tbl_of_list l).
Proof.
  intros l Hl i. unfold LeafPosE, tbl_of_list.
  destruct (nth (Z.to_nat i) l (0,0,0)) as [[op b] v] eqn:E.
  assert (Hlp : lp3 (op,b,v) = true).
  { destruct (Nat.ltb (Z.to_nat i) (length l)) eqn:Hlt.
    - apply Nat.ltb_lt in Hlt. rewrite <- E. eapply (proj1 (forallb_forall _ _) Hl). apply nth_In. exact Hlt.
    - apply Nat.ltb_ge in Hlt. rewrite nth_overflow in E by exact Hlt. injection E as <- <- <-. reflexivity. }
  unfold lp3 in Hlp. cbn. intros H240 H64.
  apply orb_true_iff in Hlp as [Hlp|Hlp]; [apply orb_true_iff in Hlp as [Hlp|Hlp]|].
  - apply Z.eqb_eq in Hlp. contradiction.
  - apply negb_true_iff, Z.eqb_neq in Hlp. contradiction.
  - apply Z.leb_le. exact Hlp.
Qed.

Theorem distfix_leafpos : LeafPosT distfix. Proof. apply tbl_of_list_lp, distfix_lp. Qed.
Theorem lenfix_leafpos  : LeafPosT lenfix.  Proof. apply tbl_of_list_lp, lenfix_lp.  Qed.
