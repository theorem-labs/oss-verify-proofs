(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import ExFlushIface FL4Inst.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  Prog ZIface DeflateState Deflate InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateGarbFast InflateGarb ModelRel
  InflateInv InflateInvRun InflateInvTab InflateInvKit InflateInvApi InflateInvLoop InflateInvCall InflateLeave InflateCall InflateFirst2
  InflateSync InflateSyncPost
  DeflateInvKeep RefDeflateRel RefDeflatePost RefDeflateHdr4 RefDeflateHdr5 DeflateInv DeflInvTally DeflInvFbo DeflInvCore DeflInvMain
  BoundArith BoundTfb BoundInv BoundSlow BoundCore BoundCall
  HarnessKit HarnessFacts HarnessSmallStages HarnessSmallFacts HarnessSmallInfl HarnessFlush HarnessFlushFacts.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec Require Import FlushStages FlushM FlushBound.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma arr_to_list_len : forall {A} (a : parr A), length (arr_to_list a) = Z.to_nat (arr_len a).
Proof. intros A a. unfold arr_to_list, arr_slice. apply arr_slice_nat_length. Qed.
Lemma arr_to_list_nth : forall {A} (a : parr A) k (dflt : A), (k < Z.to_nat (arr_len a))%nat ->
  nth k (arr_to_list a) dflt = arr_get a (Z.of_nat k).
Proof. intros A a k dflt Hk. unfold arr_to_list, arr_slice. rewrite arr_slice_nat_nth by exact Hk. f_equal. Qed.
Lemma arr_to_list_upd : forall (a : arr) ofs l, 0 <= ofs -> ofs + zlength l <= arr_len a ->
  arr_to_list (arr_upd a ofs l) = firstn (Z.to_nat ofs) (arr_to_list a) ++ l ++ skipn (Z.to_nat (ofs + zlength l)) (arr_to_list a).
Proof.
  intros a ofs l Ho Hl. pose proof (zlength_nonneg l) as L0. unfold zlength in *.
  assert (LA : length (arr_to_list a) = Z.to_nat (arr_len a)) by apply arr_to_list_len.
  apply (nth_ext _ _ 0 0).
  - rewrite arr_to_list_len, arr_len_upd, !length_app, length_firstn, length_skipn, LA. lia.
  - intros k Hk. rewrite arr_to_list_len, arr_len_upd in Hk.
    rewrite arr_to_list_nth by (rewrite arr_len_upd; exact Hk).
    rewrite (arr_get_upd l a ofs (Z.of_nat k) 0). unfold arr_inb, zlength.
    destruct (Nat.lt_ge_cases k (Z.to_nat ofs)) as [K1|K1].
    + rewrite app_nth1 by (rewrite length_firstn, LA; lia). rewrite nth_firstn. replace (k <? Z.to_nat ofs)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
      replace (ofs <=? Z.of_nat k) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb]. symmetry. apply arr_to_list_nth. lia.
    + rewrite app_nth2 by (rewrite length_firstn, LA; lia). rewrite length_firstn, LA.
      replace (Nat.min (Z.to_nat ofs) (Z.to_nat (arr_len a))) with (Z.to_nat ofs) by lia.
      destruct (Nat.lt_ge_cases (k - Z.to_nat ofs) (length l)) as [K2|K2].
      * rewrite app_nth1 by exact K2.
        replace (ofs <=? Z.of_nat k) with true by (symmetry; apply Z.leb_le; lia).
        replace (Z.of_nat k <? ofs + Z.of_nat (length l)) with true by (symmetry; apply Z.ltb_lt; lia).
        replace (0 <=? Z.of_nat k) with true by (symmetry; apply Z.leb_le; lia).
        replace (Z.of_nat k <? arr_len a) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb]. f_equal. lia.
      * rewrite app_nth2 by exact K2. rewrite nth_skipn.
        replace (Z.of_nat k <? ofs + Z.of_nat (length l)) with false by (symmetry; apply Z.ltb_ge; lia). rewrite Bool.andb_false_r. cbn [andb].
        rewrite arr_to_list_nth by lia. f_equal. lia.
Qed.
Lemma arr_to_list_set : forall (a : arr) i v, 0 <= i < arr_len a ->
  arr_to_list (arr_set a i v) = firstn (Z.to_nat i) (arr_to_list a) ++ [v] ++ skipn (Z.to_nat (i + 1)) (arr_to_list a).
Proof.
  intros a i v Hi. change (arr_set a i v) with (arr_upd a i [v]). rewrite arr_to_list_upd; [| lia | change (zlength [v]) with 1; lia]. reflexivity.
Qed.
Lemma skipn_repeat : forall {A} (x : A) n m, skipn n (repeat x m) = repeat x (m - n).
Proof. intros A x n. induction n as [|n IH]; intros [|m]; cbn; try reflexivity. apply IH. Qed.
Lemma firstn_repeat : forall {A} (x : A) n m, (n <= m)%nat -> firstn n (repeat x m) = repeat x n.
Proof. intros A x n. induction n as [|n IH]; intros [|m] H; cbn; try reflexivity; [lia|]. rewrite IH by lia. reflexivity. Qed.
Lemma Forall_firstn_ : forall {A} (P : A -> Prop) n l, Forall P l -> Forall P (firstn n l).
Proof. intros A P n. induction n as [|n IH]; intros [|x l] H; cbn; [constructor|constructor|constructor|]. inversion H; subst. constructor; [assumption| apply IH; assumption]. Qed.
Lemma Forall_skipn_ : forall {A} (P : A -> Prop) n l, Forall P l -> Forall P (skipn n l).
Proof. intros A P n. induction n as [|n IH]; intros [|x l] H; cbn; [exact H|exact H|constructor|]. inversion H; subst. apply IH; assumption. Qed.
Lemma arr_to_list_make : forall n (v : Z), arr_to_list (arr_make n v) = repeat v (Z.to_nat n).
Proof.
  intros n v. apply (nth_ext _ _ v v).
  - rewrite arr_to_list_len, arr_len_make, repeat_length. reflexivity.
  - intros k Hk. rewrite arr_to_list_len, arr_len_make in Hk. rewrite arr_to_list_nth by (rewrite arr_len_make; exact Hk).
    rewrite arr_get_make, nth_repeat_lt by exact Hk. reflexivity.
Qed.
Lemma arr_get_to_list : forall (a : arr) i, 0 <= i < arr_len a -> arr_get a i = nth (Z.to_nat i) (arr_to_list a) 0.
Proof. intros a i Hi. rewrite arr_to_list_nth by lia. f_equal. lia. Qed.
Lemma arr_to_list_of_list : forall l, arr_to_list (arr_of_list l) = l.
Proof.
  intros l. unfold arr_of_list, parr_of_list. rewrite arr_to_list_upd; [| lia | rewrite arr_len_make; lia].
  rewrite arr_to_list_make. cbn [Z.to_nat firstn app]. rewrite skipn_all2; [apply app_nil_r|]. rewrite repeat_length. unfold zlength. lia.
Qed.
Lemma arr_slice_of_list_skipn : forall l ofs n, 0 <= ofs -> 0 <= n -> (Z.to_nat (ofs + n) <= length l)%nat ->
  arr_slice (arr_of_list l) ofs n = firstn (Z.to_nat n) (skipn (Z.to_nat ofs) l).
Proof.
  intros l ofs n Ho Hn HL. apply (nth_ext _ _ 0 0).
  - unfold arr_slice. rewrite arr_slice_nat_length, length_firstn, length_skipn. lia.
  - intros k Hk. unfold arr_slice in Hk |- *. rewrite arr_slice_nat_length in Hk. rewrite arr_slice_nat_nth by exact Hk.
    rewrite nth_firstn. replace (k <? Z.to_nat n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hk). rewrite nth_skipn.
    rewrite <- (arr_to_list_of_list l) at 2. rewrite arr_to_list_nth by (rewrite arr_len_of_list; unfold zlength; lia). f_equal. lia.
Qed.

Section NOWIN.
  Variable iv : ivariant.
  Ltac modesel :=
    cbn [Z.eqb Pos.eqb BAD HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE
         LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE MEM SYNC].
  Ltac next_dispatch := rewrite (iterK_gstep_S iv Z_NO_FLUSH); unfold dispatch; wred; modesel.
  Ltac fin := split; [reflexivity | split; [reflexivity | split; reflexivity]].
  Ltac bad_tail := wred; next_dispatch; unfold arm_BAD; wred; fin.

  Lemma head2_loop_nw : forall s c,
    is_mode s = HEAD -> is_wrap s = 5 -> is_hold s = 0 -> is_bits s = 0 -> is_wbits s = 15 -> is_last s = 0 ->
    ic_next_in c = 0 -> ic_avail_in c = 2 -> 0 <= ic_avail_out c ->
    let '(stop, w') := inf_loop iv Z_NO_FLUSH (W1M s c) in
    stop = SLeave /\ ir_out (w_r w') = ir_left (w_r w') /\ is_wsize (w_s w') = is_wsize s /\ is_window_blk (w_s w') = is_window_blk s.
  Proof.
    intros s c Hm Hw Hh Hb Hwb Hl Hni Hai Hao.
    rewrite (inf_loop_iter iv Z_NO_FLUSH).
    assert (HF : exists n, Z.to_nat (gfuel (W1M s c)) = S (S (S n))).
    { unfold gfuel, W1M. cbn [w_c]. rewrite Hai. exists (Z.to_nat (64 * (2 + ic_avail_out c + 64) - 3)). lia. }
    destruct HF as [n ->].
    ds s. destruct c as [ci cni cai cob cno cao cti cto cad cdt cmsg]. cbn in Hm, Hw, Hh, Hb, Hwb, Hl, Hni, Hai, Hao. subst.
    unfold W1M, s_entryM. cbn [is_mode Z.eqb Pos.eqb HEAD TYPE]. cbn [is_hold is_bits ic_next_in ic_avail_in ic_next_out ic_avail_out].
    next_dispatch. unfold arm_HEAD. wred.
    rewrite NEEDBITS16_2. cbn [ic_input]. set (h := wrap64 _). clearbody h. wred.
    change (Z.land 5 2) with 0. change (Z.land 5 1) with 1. bsimp. wred.
    destruct (wrap64 (shl32 (BITSv h 8) 8 + Z.shiftr h 8) mod 31 =? 0); bsimp; [| bad_tail].
    wred. destruct (BITSv h 4 =? Z_DEFLATED); bsimp; [| bad_tail].
    wred. change (wrap32 (16 - 4)) with 12.
    destruct (15 <? BITSv (Z.shiftr h 4) 4 + 8); bsimp; [bad_tail|].
    wred. destruct (iv_aux iv); wred.
    all: destruct (Z.land (Z.shiftr h 4) 512 =? 0); bsimp; next_dispatch.
    1,3: unfold arm_TYPE; change ((Z_NO_FLUSH =? Z_BLOCK) || (Z_NO_FLUSH =? Z_TREES)) with false; rewrite Bool.andb_false_r;
         unfold arm_TYPEDO; wred; rewrite NEEDBITS_noinput by lia; wred; fin.
    all: unfold arm_DICTID; wred; rewrite NEEDBITS_noinput by lia; wred; fin.
  Qed.

  Lemma inf_leave_p_nowin : forall ans flush w,
    ir_out (w_r w) = ir_left (w_r w) -> is_wsize (w_s w) = 0 -> snd (inf_leave_p ans flush w) = None.
  Proof.
    intros ans flush [s c r] Ho Hw. cbn [w_r w_s] in Ho, Hw. unfold inf_leave_p. rewrite RESTORE_eq. cbn [w_s w_c w_r]. unfold leave_need.
    replace (is_wsize (iset_bits (iset_hold s (ir_hold r)) (ir_bits r))) with (is_wsize s) by (destruct s; reflexivity).
    replace (ic_avail_out (cRest c r)) with (ir_left r) by (destruct c; reflexivity).
    rewrite Hw, Ho, !Z.eqb_refl. reflexivity.
  Qed.

  Theorem inflate1_nowindow : forall ans s zc,
    is_mode s = HEAD -> is_wrap s = 5 -> is_hold s = 0 -> is_bits s = 0 -> is_wbits s = 15 -> is_last s = 0 -> is_wsize s = 0 ->
    zlength (zc_input zc) = 2 -> 0 <= zc_avail_out zc ->
    snd (inflate_p iv ans s zc Z_NO_FLUSH) = None.
  Proof.
    intros ans s zc Hm Hw Hh Hb Hwb Hl Hws Hlen Hao.
    assert (CK : inflateStateCheck s = false) by (unfold inflateStateCheck; rewrite Hm; reflexivity).
    rewrite (inflate_p_W1M iv ans s zc Z_NO_FLUSH CK).
    pose proof (head2_loop_nw s (icall_of_zcall zc) Hm Hw Hh Hb Hwb Hl eq_refl ltac:(cbn; exact Hlen) ltac:(cbn; exact Hao)) as L.
    destruct (inf_loop iv Z_NO_FLUSH (W1M s (icall_of_zcall zc))) as [stop w']. destruct L as (-> & Ho & Hws' & _).
    apply inf_leave_p_nowin; [exact Ho | rewrite Hws'; exact Hws].
  Qed.
End NOWIN.

Definition DZS0 : zstrm := mkZS 0 0 1 2 MSG_NULL.
Definition IZS0 : zstrm := mkZS 0 0 1 0 MSG_NULL.
Definition WANS8 : option (blk * (Z -> Z)) := Some (8%N, fun _ : Z => 0).

Section LINKS.
  Variable d : list Z.
  Hypothesis Hn : 4 <= zlength d <= 2 ^ 20.
  Hypothesis Hb : Forall (fun b => 0 <= b < 256) d.
  Let n : Z := zlength d.
  Let cl0 : Z := CLEN (zlength d).

  Definition L_DZC1 : ZCall := mkZCall (firstn 3 d) cl0 DZS0.
  Definition L_DSV1 : deflate_state := set_strm ds0 (cstrm_of_call L_DZC1).
  Definition L_DX1 : deflate_state := fst (deflate_core L_DSV1 3).
  Definition L_DRC1 : Z := snd (deflate_core L_DSV1 3).
  Definition L_DOUT1 : list Z := cs_output (ds_strm L_DX1).
  Definition L_DNOUT1 : Z := Z.of_nat (length (cs_out_rev (ds_strm L_DX1))).
  Definition L_DNIN1 : Z := cs_next_in (ds_strm L_DX1).
  Definition L_DZR1 : zstrm := zr_strm (zret_of_cs (ds_strm L_DX1) L_DRC1).
  Definition L_LC1 : list Z := L_DOUT1 ++ repeat 0 (Z.to_nat (cl0 - L_DNOUT1)).
  Definition L_B3 : Z := nth 3 L_LC1 0.
  Definition L_LC1' : list Z := firstn 3 L_LC1 ++ [(L_B3 + 1) mod 256] ++ skipn 4 L_LC1.
  Definition L_DZC2 : ZCall := mkZCall (firstn (Z.to_nat (n - 3)) (skipn (Z.to_nat L_DNIN1) d)) (cl0 - L_DNOUT1) L_DZR1.
  Definition L_DSV2 : deflate_state := set_strm L_DX1 (cstrm_of_call L_DZC2).
  Definition L_DX2 : deflate_state := fst (deflate_core L_DSV2 4).
  Definition L_DRC2 : Z := snd (deflate_core L_DSV2 4).
  Definition L_DOUT2 : list Z := cs_output (ds_strm L_DX2).
  Definition L_DNOUT2 : Z := Z.of_nat (length (cs_out_rev (ds_strm L_DX2))).
  Definition L_DZR2 : zstrm := zr_strm (zret_of_cs (ds_strm L_DX2) L_DRC2).
  Definition L_LC2 : list Z := firstn (Z.to_nat L_DNOUT1) L_LC1' ++ L_DOUT2 ++ skipn (Z.to_nat (L_DNOUT1 + L_DNOUT2)) L_LC1'.
  Definition L_DTOT : Z := zs_total_out L_DZR2.
  Local Strategy expand [L_DZC1 L_DSV1 L_DX1 L_DRC1 L_DOUT1 L_DNOUT1 L_DNIN1 L_DZR1 L_LC1 L_B3 L_LC1' L_DZC2 L_DSV2 L_DX2 L_DRC2 L_DOUT2 L_DNOUT2 L_DZR2 L_LC2 L_DTOT].

  Lemma L_n : 4 <= n <= 2 ^ 20. Proof. exact Hn. Qed.
  Lemma len_d : length d = Z.to_nat (zlength d). Proof. unfold zlength. lia. Qed.
  Lemma cl0_eq : fl_clen (zlength d) = cl0. Proof. unfold cl0. apply fl_clen_CLEN. lia. Qed.
  Lemma cl0_range : 126 <= cl0 < 2 ^ 22. Proof. rewrite <- cl0_eq. apply fl_clen_range. lia. Qed.

  Lemma L_DZC1_eq : L_DZC1 = fl_zc1 d.
  Proof.
    rewrite fl_zc1_eq. unfold L_DZC1. rewrite wrap32_fl_clen by lia. rewrite cl0_eq, zr0_strm.
    rewrite arr_slice_of_list_firstn; [reflexivity | lia | rewrite len_d; lia].
  Qed.
  Lemma L_DSV1_eq : L_DSV1 = fl_ds1 d.
  Proof. unfold L_DSV1, fl_ds1. rewrite L_DZC1_eq. reflexivity. Qed.
  Lemma L_DX1_eq : L_DX1 = fl_s1 d /\ zret_of_cs (ds_strm L_DX1) L_DRC1 = fl_r1 d.
  Proof.
    unfold L_DX1, L_DRC1, fl_s1, fl_r1. rewrite L_DSV1_eq, fl_call1_core. change Z_FULL_FLUSH with 3.
    destruct (deflate_core (fl_ds1 d) 3) as [s rc]. split; reflexivity.
  Qed.

  Theorem links_rc1 : L_DRC1 = Z_OK.
  Proof. unfold L_DRC1. rewrite L_DSV1_eq. apply flush1_rc. lia. Qed.

  Lemma out1_facts : L_DNOUT1 = zlength (zr_output (fl_r1 d)) /\ L_DNIN1 = zr_consumed (fl_r1 d) /\ L_DZR1 = zr_strm (fl_r1 d)
    /\ L_DOUT1 = zr_output (fl_r1 d) /\ 0 <= L_DNIN1 <= 3 /\ 0 <= L_DNOUT1 <= 19 /\ Forall (fun b => 0 <= b < 256) L_DOUT1.
  Proof.
    destruct L_DX1_eq as [E1 E2]. unfold L_DNOUT1, L_DNIN1, L_DZR1, L_DOUT1. rewrite <- E2. unfold zret_of_cs. cbn [zr_output zr_consumed zr_strm].
    rewrite zlength_cs_output. unfold zlength. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    destruct (flush1_post d Hn Hb) as (_ & _ & _ & _ & _ & M1 & O1 & OA1 & NI1 & _ & _ & OB1 & _). rewrite E1.
    destruct (flush2_entry d Hn Hb) as (_ & _ & _ & _ & LO1). unfold zlength in LO1.
    split; [exact NI1|]. split; [lia|]. rewrite cs_output_rev. apply Forall_rev. exact OB1.
  Qed.

  Lemma L_DZC2_eq : L_DZC2 = fl_zc2 d.
  Proof.
    rewrite fl_zc2_eq. unfold L_DZC2. destruct out1_facts as (E1 & E2 & E3 & _ & NI & NO & _).
    rewrite wrap32_fl_clen by lia. rewrite cl0_eq. rewrite (wrap32_id (zlength d)) by lia. unfold n. rewrite (wrap32_id (zlength d - 3)) by lia.
    rewrite <- E1, <- E2, <- E3. rewrite Z.add_0_l.
    rewrite arr_slice_of_list_skipn; [reflexivity | lia | lia | rewrite len_d; lia].
  Qed.
  Lemma L_DSV2_eq : L_DSV2 = fl_ds2 d.
  Proof. unfold L_DSV2, fl_ds2. rewrite L_DZC2_eq, (proj1 L_DX1_eq). reflexivity. Qed.
  Lemma L_DX2_eq : L_DX2 = fl_s2 d /\ zret_of_cs (ds_strm L_DX2) L_DRC2 = fl_r2 d.
  Proof.
    unfold L_DX2, L_DRC2, fl_s2, fl_r2. rewrite L_DSV2_eq, fl_call2_core. change Z_FINISH with 4.
    destruct (deflate_core (fl_ds2 d) 4) as [s rc]. split; reflexivity.
  Qed.

  Theorem links_rc2 : L_DRC2 = Z_OK \/ L_DRC2 = Z_STREAM_END.
  Proof.
    destruct L_DX2_eq as [_ E]. replace L_DRC2 with (zr_rc (fl_r2 d)) by (rewrite <- E; reflexivity). apply flush2_zr_rc; [lia | exact Hb].
  Qed.

  Theorem links_st2 : ds_status L_DX2 = 113 \/ ds_status L_DX2 = 666.
  Proof. rewrite (proj1 L_DX2_eq). apply status2_range; [lia | exact Hb]. Qed.

  Theorem links_busy : fm_busy FL4 d = (ds_status L_DX2 =? 113).
  Proof. rewrite fl4_busy_eq, (proj1 L_DX2_eq). apply fl_busy_status; [lia | exact Hb]. Qed.

  Lemma out2_facts : L_DNOUT2 = zlength (zr_output (fl_r2 d)) /\ L_DOUT2 = zr_output (fl_r2 d) /\ L_DTOT = fl_tot d
    /\ 0 <= L_DNOUT2 /\ L_DNOUT1 + L_DNOUT2 <= cl0 /\ Forall (fun b => 0 <= b < 256) L_DOUT2.
  Proof.
    destruct L_DX2_eq as [E1 E2]. unfold L_DNOUT2, L_DOUT2, L_DTOT, L_DZR2. rewrite <- E2. unfold zret_of_cs. cbn [zr_output zr_strm].
    rewrite zlength_cs_output. unfold zlength. split; [reflexivity|]. split; [reflexivity|].
    split; [rewrite fl_tot_eq, E1; reflexivity|]. split; [lia|].
    destruct out1_facts as (F1 & _). rewrite F1, E1.
    destruct (flush1_post d Hn Hb) as (DI1 & B1 & C1 & SB1 & SZ1 & M1 & O1 & OA1 & NI1 & ZS1 & AD1 & OB1 & HS1 & [P1 PO1] & TO1).
    destruct (flush2_dcore d Hn Hb) as (D2 & B2 & C2 & SB2 & AO2 & ZC2 & P2 & AI2 & OUT2).
    destruct (flush2_entry d Hn Hb) as (_ & _ & _ & EAO2 & LO1).
    assert (HPBL : 2048 <= ds_lit_bufsize (fl_s1 d) * 4) by (destruct SZ1 as [_ EE]; rewrite EE; lia).
    assert (HF16 : 0 <= Z_FINISH < 16) by (unfold Z_FINISH; lia).
    assert (AD1' : DADLER2 (ds_wrap (fl_s1 d)) (zs_adler (zc_strm (fl_zc2 d)))) by (rewrite fl_zc2_eq; cbn [zc_strm]; exact AD1).
    pose proof (deflate_DI (fl_s1 d) (fl_zc2 d) Z_FINISH HPBL (DI_dwf _ DI1) DI1 ZC2 HF16 AD1') as (OK & _ & _).
    destruct OK as (_ & _ & _ & _ & ZP). cbv zeta in ZP.
    change (set_strm (fl_s1 d) (cstrm_of_call (fl_zc2 d))) with (fl_ds2 d) in ZP.
    assert (ES2 : fst (deflate_core (fl_ds2 d) Z_FINISH) = fl_s2 d).
    { unfold fl_s2. rewrite fl_call2_core. destruct (deflate_core (fl_ds2 d) Z_FINISH); reflexivity. }
    rewrite ES2 in ZP. unfold zpost_ok in ZP. destruct ZP as (_ & (OO2 & OA2') & _ & _ & OB2 & _).
    change (zc_avail_out (fl_zc2 d)) with (cs_avail_out (ds_strm (fl_ds2 d))) in OA2'. rewrite EAO2, cl0_eq in OA2'.
    split; [rewrite zr_output_fl_r1; assert (ZL : forall l : list Z, Z.of_nat (length l) = zlength l) by (intros; reflexivity); rewrite ZL; clear - OA2' OO2; lia|].
    rewrite cs_output_rev. apply Forall_rev. exact OB2.
  Qed.

  Theorem links_tot : fm_busy FL4 d = false -> fm_tot FL4 d = L_DTOT.
  Proof.
    intros NB. destruct out2_facts as (_ & _ & -> & _). rewrite fl4_busy_eq in NB.
    destruct (tot_range d Hn Hb) as [T1 T2]. rewrite cl0_eq in T1. apply fl4_tot_eq. unfold cl0. split; [exact (T2 NB) | exact T1].
  Qed.

  Lemma compr1_list : arr_to_list (fl_compr1 d) = L_LC1 /\ arr_len (fl_compr1 d) = cl0.
  Proof.
    destruct out1_facts as (F1 & _ & _ & F4 & _ & NO & _). pose proof cl0_range as CR.
    unfold fl_compr1, fl_ret1, cz_ret. cbn [fst snd]. unfold fl_c0. cbn [cz_next_out]. rewrite cl0_eq.
    split; [| rewrite arr_len_upd; unfold zero_buf; rewrite arr_len_make; reflexivity].
    unfold zero_buf. rewrite arr_to_list_upd; [| lia | rewrite arr_len_make, <- F1; lia]. rewrite arr_to_list_make.
    change (Z.to_nat 0) with 0%nat. rewrite firstn_O, app_nil_l.
    unfold L_LC1. rewrite Z.add_0_l, <- F1, <- F4, skipn_repeat. f_equal. f_equal. lia.
  Qed.
  Lemma LC1_length : length L_LC1 = Z.to_nat cl0.
  Proof. destruct compr1_list as [E L]. rewrite <- E, arr_to_list_len, L. reflexivity. Qed.

  Lemma compr1'_list : arr_to_list (fl_compr1' d) = L_LC1' /\ arr_len (fl_compr1' d) = cl0.
  Proof.
    destruct compr1_list as [E L]. pose proof cl0_range as CR. unfold fl_compr1'. split; [| rewrite arr_len_set; exact L].
    rewrite arr_to_list_set by (rewrite L; lia). rewrite E. unfold L_LC1', L_B3. change (Z.to_nat (3 + 1)) with 4%nat. change (Z.to_nat 3) with 3%nat.
    f_equal. f_equal. f_equal. rewrite wrap8_mod. rewrite (arr_get_to_list (fl_compr1 d) 3) by (rewrite L; lia). rewrite E. reflexivity.
  Qed.

  Theorem fl4_compr_links : fm_compr FL4 d = L_LC2.
  Proof.
    destruct compr1'_list as [E L]. destruct out1_facts as (F1 & _ & _ & _ & _ & NO & _). destruct out2_facts as (G1 & G2 & _ & NO2 & SUM & _).
    pose proof cl0_range as CR.
    assert (EL : arr_to_list (fl_compr2 d) = L_LC2 /\ arr_len (fl_compr2 d) = cl0).
    { unfold fl_compr2, fl_ret2, cz_ret. cbn [fst snd].
      replace (cz_next_out (fl_c1' d)) with L_DNOUT1
        by (unfold fl_c1', cz_set_avail_in; cbn [cz_next_out]; unfold fl_c1, fl_ret1, cz_ret; cbn [fst snd cz_next_out]; unfold fl_c0; cbn [cz_next_out]; lia).
      split; [| rewrite arr_len_upd; exact L].
      rewrite arr_to_list_upd; [| lia | rewrite L, <- G1; lia]. rewrite E, <- G1, <- G2. reflexivity. }
    destruct EL as [E2 L2]. rewrite (fl4_compr_eq d); [exact E2|].
    pose proof (CLEN_nonneg (zlength d) ltac:(lia)) as H. unfold cl0, zlength in *. rewrite arr_to_list_len, L2. lia.
  Qed.

  Lemma fl4_compr_bytes : Forall (fun b => 0 <= b < 256) (fm_compr FL4 d) /\ zlength (fm_compr FL4 d) = cl0.
  Proof.
    split.
    2:{ pose proof (fl4_compr_len d) as X. cbn [fm_compr FL4]. unfold zlength in *. rewrite X. unfold cl0. reflexivity. }
    rewrite fl4_compr_links. destruct out1_facts as (F1 & _ & _ & F4 & _ & NO & OB). destruct out2_facts as (G1 & G2 & _ & NO2 & SUM & OB2).
    assert (B1 : Forall (fun b => 0 <= b < 256) L_LC1).
    { unfold L_LC1. apply Forall_app. split; [exact OB|]. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia. }
    assert (B1' : Forall (fun b => 0 <= b < 256) L_LC1').
    { unfold L_LC1'. apply Forall_app. split; [apply Forall_firstn_; exact B1|]. apply Forall_app. split; [| apply Forall_skipn_; exact B1].
      constructor; [| constructor]. pose proof (Z.mod_pos_bound (L_B3 + 1) 256). lia. }
    unfold L_LC2. apply Forall_app. split; [apply Forall_firstn_; exact B1'|]. apply Forall_app. split; [exact OB2 | apply Forall_skipn_; exact B1'].
  Qed.
  Let c : list Z := fm_compr FL4 d.
  Let clen : Z := fm_clen FL4 d.
  Definition L_IZC1 : ZCall := mkZCall (firstn 2 c) n IZS0.
  Definition L_ICALL1 := inflate_p ivar_ref WANS8 (is0 KI) L_IZC1 0.
  Definition L_IS1 : inflate_state := fst (fst L_ICALL1).
  Definition L_IR1 : ZRet := snd (fst L_ICALL1).
  Definition L_ICONS1 : Z := zr_consumed L_IR1.
  Definition L_INOUT1 : Z := zlength (zr_output L_IR1).
  Definition L_IZC2 : ZCall := mkZCall (firstn (Z.to_nat (clen - 2)) (skipn (Z.to_nat L_ICONS1) c)) (n - L_INOUT1) (zr_strm L_IR1).
  Definition L_ISYNC := inflateSync_m ivar_ref L_IS1 L_IZC2.
  Definition L_IS2 : inflate_state := fst L_ISYNC.
  Definition L_IR2 : ZRet := snd L_ISYNC.
  Definition L_ICONS2 : Z := zr_consumed L_IR2.
  Definition L_IZC3 : ZCall :=
    mkZCall (firstn (Z.to_nat (clen - 2 - L_ICONS2)) (skipn (Z.to_nat (L_ICONS1 + L_ICONS2)) c)) (n - L_INOUT1) (zr_strm L_IR2).
  Definition L_ICALL3 := inflate_p ivar_ref WANS8 L_IS2 L_IZC3 4.
  Definition L_IS3 : inflate_state := fst (fst L_ICALL3).
  Definition L_IR3 : ZRet := snd (fst L_ICALL3).
  Local Strategy expand [L_IZC1 L_ICALL1 L_IS1 L_IR1 L_ICONS1 L_INOUT1 L_IZC2 L_ISYNC L_IS2 L_IR2 L_ICONS2 L_IZC3 L_ICALL3 L_IS3 L_IR3].

  Lemma c_facts : Forall (fun b => 0 <= b < 256) c /\ zlength c = cl0 /\ length c = Z.to_nat cl0 /\ carr c = arr_of_list c.
  Proof.
    unfold c. destruct fl4_compr_bytes as [B L]. split; [exact B|]. split; [exact L|]. split; [unfold zlength in L; lia|]. apply carr_bytes. exact B.
  Qed.
  Lemma clen_range : 2 <= clen <= cl0.
  Proof. unfold clen, cl0, zlength. apply fm_clen_range. Qed.
  Lemma hans_eq : hans O4 KW = WANS8.
  Proof. reflexivity. Qed.
  Lemma is0_facts : is_mode (is0 KI) = HEAD /\ is_wrap (is0 KI) = 5 /\ is_hold (is0 KI) = 0 /\ is_bits (is0 KI) = 0 /\ is_wbits (is0 KI) = 15
    /\ is_last (is0 KI) = 0 /\ is_wsize (is0 KI) = 0.
  Proof. repeat split; reflexivity. Qed.
  Lemma IRCS_cases : forall rc, In rc IRCS -> rc = 0 \/ In rc INFL_ERRS.
  Proof. intros rc H. unfold IRCS, Z_OK, Z_STREAM_END, Z_NEED_DICT, Z_STREAM_ERROR, Z_DATA_ERROR, Z_MEM_ERROR, Z_BUF_ERROR in H. unfold INFL_ERRS. cbn in H |- *. lia. Qed.
  Lemma SYNC_cases : forall rc, In rc [Z_OK; Z_STREAM_ERROR; Z_BUF_ERROR; Z_DATA_ERROR] -> rc = 0 \/ In rc SYNC_ERRS.
  Proof. intros rc H. unfold Z_OK, Z_STREAM_ERROR, Z_DATA_ERROR, Z_BUF_ERROR in H. unfold SYNC_ERRS. cbn in H |- *. lia. Qed.

  Lemma L_IZC1_eq : L_IZC1 = fl_izc1 (carr c) n.
  Proof.
    rewrite fl_izc1_eq. destruct c_facts as (B & L & LN & ->). pose proof cl0_range as CR. unfold L_IZC1.
    rewrite (wrap32_id n) by (unfold n; lia). rewrite fl_iz0_eq.
    rewrite arr_slice_of_list_firstn; [reflexivity | lia | rewrite LN; lia].
  Qed.
  Lemma L_ICALL1_eq : L_ICALL1 = fl_icall1 (carr c) n.
  Proof. unfold L_ICALL1, fl_icall1, fl_i0, Z_NO_FLUSH. rewrite L_IZC1_eq, hans_eq. reflexivity. Qed.
  Lemma L_I1_eq : L_IS1 = fl_is1 (carr c) n /\ L_IR1 = fl_ir1 (carr c) n.
  Proof. unfold L_IS1, L_IR1, fl_is1, fl_ir1. rewrite L_ICALL1_eq. split; reflexivity. Qed.
  Lemma zc1_ok : InflateInvCall.zcall_ok L_IZC1 /\ zlength (zc_input L_IZC1) = 2 /\ zc_avail_out L_IZC1 = n.
  Proof.
    destruct c_facts as (B & L & LN & _). pose proof cl0_range as CR.
    assert (L2 : zlength (firstn 2 c) = 2) by (unfold zlength; rewrite length_firstn, LN; lia).
    unfold InflateInvCall.zcall_ok, L_IZC1. cbn [zc_input zc_avail_out zc_strm zs_total_in zs_total_out zs_adler zs_data_type IZS0]. rewrite L2.
    split; [| split; reflexivity]. split; [apply Forall_firstn_; exact B|]. unfold n. lia.
  Qed.
  Lemma call1_post : UI L_IS1 /\ IPOST L_IZC1 L_IR1.
  Proof.
    destruct zc1_ok as (ZC & _ & _). pose proof (inflate_p_post ivar_ref WANS8 (is0 KI) L_IZC1 0 (UI_is0 KI) ZC) as X.
    unfold L_IS1, L_IR1, L_ICALL1. destruct (inflate_p ivar_ref WANS8 (is0 KI) L_IZC1 0) as [p asked]. exact X.
  Qed.
  Theorem links_nw1 : snd L_ICALL1 = None.
  Proof.
    destruct is0_facts as (M & W & Ho & Bi & Wb & La & Ws). destruct zc1_ok as (_ & L2 & AO). unfold L_ICALL1.
    apply (inflate1_nowindow ivar_ref); try assumption. rewrite AO. unfold n. lia.
  Qed.
  Theorem links_i1 : fm_i1 FL4 c n = (if zr_rc L_IR1 =? 0 then I1_OK else I1_E (zr_rc L_IR1)).
  Proof.
    destruct L_I1_eq as [_ E]. pose proof (fl4_i1_eq c n) as X. cbv zeta in X. rewrite <- E in X. apply X.
    apply IRCS_cases. destruct call1_post as [_ (_ & _ & _ & R & _)]. exact R.
  Qed.
  Lemma ir1_facts : 0 <= zr_consumed L_IR1 <= 2 /\ 0 <= zlength (zr_output L_IR1) <= n /\ zret_ok L_IR1.
  Proof.
    destruct zc1_ok as (_ & L2 & AO). destruct call1_post as [_ (ZR & C1 & O1 & _)]. rewrite L2 in C1. rewrite AO in O1.
    split; [exact C1|]. split; [exact O1 | exact ZR].
  Qed.

  Lemma L_IZC2_eq : L_IZC2 = fl_izc2 (carr c) clen n.
  Proof.
    rewrite fl_izc2_eq. destruct L_I1_eq as [_ E]. rewrite <- E. destruct c_facts as (B & L & LN & ->). pose proof cl0_range as CR. pose proof clen_range as CL.
    destruct ir1_facts as (C1 & O1 & _). unfold L_IZC2, L_ICONS1, L_INOUT1.
    rewrite (wrap32_id clen) by lia. rewrite (wrap32_id (clen - 2)) by lia. rewrite (wrap32_id n) by (unfold n; lia). rewrite Z.add_0_l.
    rewrite arr_slice_of_list_skipn; [reflexivity | lia | lia | rewrite LN; lia].
  Qed.
  Lemma L_ISYNC_eq : L_ISYNC = fl_sync (carr c) clen n.
  Proof. unfold L_ISYNC, fl_sync. rewrite L_IZC2_eq, (proj1 L_I1_eq). reflexivity. Qed.
  Lemma L_I2_eq : L_IS2 = fl_is2 (carr c) clen n /\ L_IR2 = fl_ir2 (carr c) clen n.
  Proof. unfold L_IS2, L_IR2, fl_is2, fl_ir2. rewrite L_ISYNC_eq. split; reflexivity. Qed.
  Lemma zc2_ok : InflateInvCall.zcall_ok L_IZC2 /\ zlength (zc_input L_IZC2) = clen - 2 /\ zc_avail_out L_IZC2 = n - zlength (zr_output L_IR1).
  Proof.
    destruct c_facts as (B & L & LN & _). pose proof cl0_range as CR. pose proof clen_range as CL. destruct ir1_facts as (C1 & O1 & ZR).
    assert (L2 : zlength (firstn (Z.to_nat (clen - 2)) (skipn (Z.to_nat (zr_consumed L_IR1)) c)) = clen - 2) by (unfold zlength; rewrite length_firstn, length_skipn, LN; lia).
    unfold InflateInvCall.zcall_ok, L_IZC2, L_ICONS1, L_INOUT1. cbn [zc_input zc_avail_out zc_strm]. rewrite L2.
    split; [| split; reflexivity]. destruct ZR as (_ & T1 & T2 & A1 & D1).
    split; [apply Forall_firstn_; apply Forall_skipn_; exact B|]. unfold n. repeat split; try lia.
  Qed.
  Lemma sync_post : UI L_IS2 /\ SPOST L_IZC2 L_IR2.
  Proof.
    destruct zc2_ok as (ZC & _ & _). pose proof (inflateSync_post ivar_ref L_IS1 L_IZC2 (proj1 call1_post) ZC) as X.
    unfold L_IS2, L_IR2, L_ISYNC. destruct (inflateSync_m ivar_ref L_IS1 L_IZC2) as [s' r]. destruct X as (U & P & _). split; [exact U | exact P].
  Qed.
  Theorem links_is : fm_is FL4 c clen n = (if zr_rc L_IR2 =? 0 then IS_OK else IS_E (zr_rc L_IR2)).
  Proof.
    destruct L_I2_eq as [_ E]. pose proof (fl4_is_eq c clen n) as X. cbv zeta in X. rewrite <- E in X. apply X.
    apply SYNC_cases. destruct sync_post as [_ (_ & _ & _ & R & _)]. exact R.
  Qed.
  Lemma ir2_facts : 0 <= zr_consumed L_IR2 <= clen - 2 /\ zr_output L_IR2 = [] /\ zret_ok L_IR2.
  Proof.
    destruct zc2_ok as (_ & L2 & AO). destruct sync_post as [_ (ZR & C2 & O2 & _)]. rewrite L2 in C2.
    split; [exact C2|]. split; [exact O2 | exact ZR].
  Qed.

  Lemma L_IZC3_eq : L_IZC3 = fl_izc3 (carr c) clen n.
  Proof.
    rewrite fl_izc3_eq. destruct L_I1_eq as [_ E1]. destruct L_I2_eq as [_ E2]. rewrite <- E1, <- E2.
    destruct c_facts as (B & L & LN & ->). pose proof cl0_range as CR. pose proof clen_range as CL.
    destruct ir1_facts as (C1 & O1 & _). destruct ir2_facts as (C2 & OUT2 & _). unfold L_IZC3, L_ICONS1, L_ICONS2, L_INOUT1. rewrite OUT2.
    rewrite (wrap32_id clen) by lia. rewrite (wrap32_id (clen - 2)) by lia. rewrite (wrap32_id n) by (unfold n; lia). rewrite Z.add_0_l.
    change (zlength []) with 0. rewrite Z.sub_0_r.
    rewrite arr_slice_of_list_skipn; [reflexivity | lia | lia | rewrite LN; lia].
  Qed.
  Lemma L_ICALL3_eq : L_ICALL3 = fl_icall3 (carr c) clen n.
  Proof.
    unfold L_ICALL3, fl_icall3, Z_FINISH.
    replace (fl_iasked1 (carr c) n) with (@None Z) by (unfold fl_iasked1; rewrite <- L_ICALL1_eq; symmetry; exact links_nw1). cbn [hstep_n].
    rewrite L_IZC3_eq, hans_eq, (proj1 L_I2_eq). reflexivity.
  Qed.
  Lemma L_I3_eq : L_IS3 = fl_is3 (carr c) clen n /\ L_IR3 = fl_ir3 (carr c) clen n /\ snd L_ICALL3 = fl_iasked3 (carr c) clen n.
  Proof. unfold L_IS3, L_IR3, fl_is3, fl_ir3, fl_iasked3. rewrite L_ICALL3_eq. repeat split; reflexivity. Qed.
  Lemma zc3_ok : InflateInvCall.zcall_ok L_IZC3.
  Proof.
    destruct c_facts as (B & L & LN & _). pose proof cl0_range as CR. pose proof clen_range as CL. destruct ir1_facts as (C1 & O1 & _).
    destruct ir2_facts as (C2 & _ & ZR).
    assert (L3 : zlength (firstn (Z.to_nat (clen - 2 - zr_consumed L_IR2)) (skipn (Z.to_nat (zr_consumed L_IR1 + zr_consumed L_IR2)) c)) = clen - 2 - zr_consumed L_IR2)
      by (unfold zlength; rewrite length_firstn, length_skipn, LN; lia).
    unfold InflateInvCall.zcall_ok, L_IZC3, L_ICONS1, L_ICONS2, L_INOUT1. cbn [zc_input zc_avail_out zc_strm]. rewrite L3. destruct ZR as (_ & T1 & T2 & A1 & D1).
    split; [apply Forall_firstn_; apply Forall_skipn_; exact B|]. unfold n. repeat split; try lia.
  Qed.
  Lemma call3_post : UI L_IS3 /\ IPOST L_IZC3 L_IR3.
  Proof.
    pose proof (inflate_p_post ivar_ref WANS8 L_IS2 L_IZC3 4 (proj1 sync_post) zc3_ok) as X.
    unfold L_IS3, L_IR3, L_ICALL3. destruct (inflate_p ivar_ref WANS8 L_IS2 L_IZC3 4) as [p asked]. exact X.
  Qed.
  Theorem links_i2 : fm_i2 FL4 c clen n = match snd L_ICALL3 with Some _ => I2_W | None => I2_R (zr_rc L_IR3) end.
  Proof.
    destruct L_I3_eq as (_ & E & EA). rewrite EA. pose proof (fl4_i2_eq c clen n) as X. rewrite <- E in X. apply X.
    destruct call3_post as [_ (_ & _ & _ & R & _)]. exact R.
  Qed.
  Theorem links_i2b : snd L_ICALL3 <> None -> fm_i2b FL4 c clen n = zr_rc L_IR3.
  Proof.
    intros _. destruct L_I3_eq as (_ & E & _). pose proof (fl4_i2b_eq c clen n) as X. rewrite <- E in X. apply X.
    destruct call3_post as [_ (_ & _ & _ & R & _)]. exact R.
  Qed.

  Theorem links_rcs : In (zr_rc L_IR1) IRCS /\ In (zr_rc L_IR2) [Z_OK; Z_STREAM_ERROR; Z_BUF_ERROR; Z_DATA_ERROR] /\ In (zr_rc L_IR3) IRCS.
  Proof.
    destruct call1_post as [_ (_ & _ & _ & R1 & _)]. destruct sync_post as [_ (_ & _ & _ & R2 & _)]. destruct call3_post as [_ (_ & _ & _ & R3 & _)].
    split; [exact R1 | split; [exact R2 | exact R3]].
  Qed.
End LINKS.
