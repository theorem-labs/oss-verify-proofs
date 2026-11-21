(** * Bridge.Infl.ITreeStep — pair I15, part 2: one trip of RT's [it_step].

    S5's [ItSim2.trip_spec] shows one trip of S5's loop moves the abstract state [StM k] to
    [StM (k+1)] and appends [trip_writes k] to the table.  [rt_trip] below is the same
    statement for RT's [Inftrees.it_step]: [RStM k] (RT's loop state is the abstract
    state at trip [k], RT's view of the table is the S5 table after [trips_writes k]) goes
    to [RStM (k+1)], or to the break/overflow exits exactly when S5's trip takes them.
    Every fact about the abstract quantities comes from S5's theory. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees InftreesCoverage ItDefs ItGen ItMath ItSort ItSimPre ItSim1 ItSim2 ItShape ItCover.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Inftrees Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv ITreePre.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(** RT's loop state at trip [k] is S5's abstract state at trip [k]; RT's table view is
    the S5 table [a] after the first [k] trips' writes. *)
Definition RStM (wl ll : list Z) (root : Z) (ty : IS.codetype) (tc : RBa.ztbl) (table : Z)
                (k : Z) (st : RIT.ItSt) (a : arr) : Prop :=
  RIT.s_huff st = hf wl k /\ RIT.s_sym st = k /\ RIT.s_len st = len_at wl k /\
  RIT.s_next st = noff wl root k /\ RIT.s_curr st = curr wl root k /\ RIT.s_drop st = drop wl root k /\
  RIT.s_low st = low wl root k /\ RIT.s_used st = used wl root k /\
  (forall l, 1 <= l <= 15 -> RIT.s_count st l = REM wl k l) /\
  TRel tc table (applyw (trips_writes wl ll root ty table k) a) (RIT.s_tbl st) /\ TRng (RIT.s_tbl st).

(** RT's loop context as [it_pre] builds it. *)
Definition CtxOk (ty : IS.codetype) (lens : arr) (lens_ofs codes : Z) (wl ll : list Z) (root : Z)
                 (c : RIT.ItCtx) : Prop :=
  RIT.x_type c = rtype ty /\
  (forall i, 0 <= i < codes -> RIT.x_lens c i = arr_get lens (lens_ofs + i)) /\
  RIT.x_root c = root /\ RIT.x_max c = MAXL wl /\ RIT.x_mask c = 2 ^ root - 1 /\
  (forall j, 0 <= j < NZ wl -> RIT.x_work c j = wsym wl ll j) /\
  RIT.x_match c = it_match ty /\
  (ty <> IS.CODES -> forall i, 0 <= i ->
     RIT.x_base c i = it_base ty (arr_make 0 0) i /\ RIT.x_extra c i = it_extra ty (arr_make 0 0) i).

(* ------------------------------------------------------------------------- *)
(* 1.  RT's sub-table sizing ([inftrees.c:249-255])                          *)
(* ------------------------------------------------------------------------- *)

Section Sub.
  Variable wl : list Z.
  Hypothesis HW : forall l, 0 <= W wl l.
  Hypothesis HL : length wl = 16%nat.
  Variable root : Z.
  Hypothesis Hroot : MINL wl <= root <= MAXL wl.
  Hypothesis HM1 : 1 <= MAXL wl.
  #[local] Set Default Proof Using "HW HL Hroot HM1".

  (** The RT twin of S5's [ItSim1.subtable_curr_spec]. *)
  Lemma rt_subsz_spec : forall (cnt : RBa.zarr) k, 0 <= k < NZ wl -> newtable wl root k = true ->
    (forall l, len_at wl k <= l <= 15 -> cnt l = REM wl k l) ->
    RIT.it_subsz 16 cnt root (MAXL wl) (len_at wl k - root) (2 ^ (len_at wl k - root)) =
    cstar wl root (Pfx wl root k) (len_at wl k - root).
  Proof.
    intros cnt k Hk HN Hcnt.
    pose proof (root_range wl HW HL root Hroot HM1) as RR. pose proof (MAXL_spec wl HW HL) as [MM _].
    pose proof (newtable_long wl HW HL root Hroot HM1 k HN) as HLg. pose proof HLg as HLg'.
    unfold islong in HLg'. apply Z.ltb_lt in HLg'.
    pose proof (len_at_range wl HW HL k Hk) as LR. pose proof (rank_at_spec wl HW HL k Hk) as RK.
    pose proof (group_start wl HW HL root Hroot HM1 k Hk HN) as GS.
    pose proof (GR_pos wl HW HL root Hroot HM1) as GP.
    set (L := len_at wl k) in *. set (c0 := L - root).
    pose proof (cstar_spec wl HW HL root Hroot HM1 (Pfx wl root k) c0 ltac:(lia)) as [C1 [C2 C3]].
    set (cs := cstar wl root (Pfx wl root k) c0) in *.
    set (RM := fun l => if l <? L then 0 else TM wl l - Apos wl k).
    assert (RM_step : forall c, c0 <= c <= MAXL wl - root ->
              cnt (root + c) * 2 ^ (MAXL wl - root - c) = RM (root + c) - RM (root + c - 1)).
    { intros c Hc. rewrite Hcnt by lia. unfold REM, RM. fold L.
      destruct (Z.ltb_spec (root + c) L); [lia|].
      destruct (Z.eqb_spec (root + c) L) as [E|NE].
      - destruct (Z.ltb_spec (root + c - 1) L); [|lia]. rewrite E.
        unfold Apos. fold L. rewrite (TM_step' wl HW HL L) by lia.
        replace (MAXL wl - root - c) with (MAXL wl - L) by lia. nia.
      - destruct (Z.ltb_spec (root + c - 1) L); [lia|].
        rewrite (TM_step' wl HW HL (root + c)) by lia.
        replace (MAXL wl - root - c) with (MAXL wl - (root + c)) by lia. nia. }
    assert (RM_c0 : RM (root + c0 - 1) = 0).
    { unfold RM. destruct (Z.ltb_spec (root + c0 - 1) L); [reflexivity|lia]. }
    assert (RM_TM : forall c, c0 <= c -> RM (root + c) = TM wl (root + c) - Apos wl k).
    { intros c Hc. unfold RM. destruct (Z.ltb_spec (root + c) L); [lia|reflexivity]. }
    assert (LOOP : forall (fuel : nat) c lft, c0 <= c <= cs ->
              lft * 2 ^ (MAXL wl - root - c) = GR wl root - RM (root + c - 1) ->
              cs - c + 1 <= Z.of_nat fuel ->
              RIT.it_subsz fuel cnt root (MAXL wl) c lft = cs).
    { induction fuel as [|fuel IH]; intros c lft Hc Hinv Hf; [lia|].
      cbn [RIT.it_subsz]. replace (c + root) with (root + c) by lia.
      destruct (Z.eq_dec c cs) as [->|NE].
      - destruct (Z.ltb_spec (root + cs) (MAXL wl)); [|reflexivity].
        destruct C2 as [C2|C2]; [lia|].
        pose proof (RM_step cs ltac:(lia)) as RS. pose proof (RM_TM cs ltac:(lia)) as RTM.
        pose proof (pow2_pos (MAXL wl - root - cs) ltac:(lia)) as PP.
        assert ((lft - cnt (root + cs)) * 2 ^ (MAXL wl - root - cs) <= 0).
        { rewrite Z.mul_sub_distr_r, RS, Hinv, RTM, GS. lia. }
        destruct (Z.leb_spec (lft - cnt (root + cs)) 0); [reflexivity| nia].
      - destruct (C3 c ltac:(lia)) as [D1 D2].
        destruct (Z.ltb_spec (root + c) (MAXL wl)); [|lia].
        pose proof (RM_step c ltac:(lia)) as RS. pose proof (RM_TM c ltac:(lia)) as RTM.
        pose proof (pow2_pos (MAXL wl - root - c) ltac:(lia)) as PP.
        assert (HP : 0 < (lft - cnt (root + c)) * 2 ^ (MAXL wl - root - c)).
        { rewrite Z.mul_sub_distr_r, RS, Hinv, RTM, GS. lia. }
        destruct (Z.leb_spec (lft - cnt (root + c)) 0); [nia|].
        apply IH; try lia.
        replace (root + (c + 1) - 1) with (root + c) by lia.
        replace ((lft - cnt (root + c)) * 2 * 2 ^ (MAXL wl - root - (c + 1)))
          with ((lft - cnt (root + c)) * 2 ^ (MAXL wl - root - c)).
        2:{ rewrite <- Z.mul_assoc. f_equal. rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
        rewrite Z.mul_sub_distr_r, RS, Hinv. lia. }
    apply LOOP; [lia | | lia].
    fold c0. rewrite RM_c0, <- Z.pow_add_r by lia. unfold GR. rewrite Z.sub_0_r. f_equal. lia.
  Qed.
End Sub.

(* ------------------------------------------------------------------------- *)
(* 2.  One trip                                                              *)
(* ------------------------------------------------------------------------- *)

Section Trip.
  Variable ty : IS.codetype.
  Variable lens : arr.
  Variable lens_ofs codes : Z.
  Variable ll wl : list Z.
  Variable table root : Z.
  Hypothesis Hcodes : 0 <= codes <= 288.
  Hypothesis Hlens : forall i, lens_ofs <= i < lens_ofs + codes -> 0 <= arr_get lens i <= 15.
  Hypothesis Ell : ll = lens_list lens lens_ofs codes.
  Hypothesis Ewl : wl = wl_of ll.
  Hypothesis Hroot : MINL wl <= root <= MAXL wl.
  Hypothesis HM1 : 1 <= MAXL wl.
  Hypothesis HK : TM wl (MAXL wl) <= 2 ^ MAXL wl.
  Hypothesis Hty : ty = IS.CODES -> codes <= 19.
  Variable tc : RBa.ztbl.
  Hypothesis Htab : 0 <= table.
  Variable c : RIT.ItCtx.
  Hypothesis HCX : CtxOk ty lens lens_ofs codes wl ll root c.
  #[local] Set Default Proof Using "Hcodes Hlens Ell Ewl Hroot HM1 HK Hty Htab HCX".

  Let HW := HW lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl.
  Let HL := HL lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl.

  Lemma here_eq : forall st k, 0 <= k < NZ wl -> RIT.s_sym st = k ->
    RIT.s_len st - RIT.s_drop st = len_at wl k - drop wl root k ->
    RBa.code_enc (RIT.it_here c st) = here wl ll root ty k /\ code_rng (RIT.it_here c st).
  Proof.
    intros st k Hk Hs Hb. destruct HCX as (Hcty & Hclens & Hcroot & Hcmax & Hcmask & Hcwork & Hcmt & Hcbe).
    pose proof (wsym_facts ty lens lens_ofs codes ll wl root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty k Hk) as [WR _].
    pose proof (entry_eq ty lens lens_ofs codes ll wl root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty (arr_make 0 0) k Hk) as EE.
    unfold RIT.it_here, here. cbv zeta. rewrite Hs, Hb, (Hcwork k Hk), Hcmt. rewrite <- EE.
    destruct (Z.ltb_spec (wsym wl ll k + 1) (it_match ty)); cbv beta iota.
    - split; [symmetry; apply code_pack_enc | apply code_rng_mk].
    - destruct (Z.leb_spec (it_match ty) (wsym wl ll k)); cbv beta iota.
      + assert (NC : ty <> IS.CODES).
        { intros E. pose proof (Hty E) as H19. rewrite E in *. cbn [it_match] in *. lia. }
        destruct (Hcbe NC (wsym wl ll k - it_match ty) ltac:(lia)) as [B E]. rewrite B, E.
        split; [|apply code_rng_mk]. rewrite <- code_pack_enc. unfold IS.code_pack. rewrite wrap8_idem. reflexivity.
      + split; [|apply code_rng_mk]. rewrite <- code_pack_enc. reflexivity.
  Qed.

  Lemma rt_cnt_step : forall (cnt : RBa.zarr) k, 0 <= k -> k + 1 < NZ wl ->
    (forall l, 1 <= l <= 15 -> cnt l = REM wl k l) ->
    forall l, 1 <= l <= 15 ->
      RBa.zset cnt (len_at wl k) (W wl (len_at wl k) - rank_at wl k - 1) l = REM wl (k + 1) l.
  Proof.
    intros cnt k Hk Hk1 Hc l Hl.
    rewrite <- (cnt_step ty lens lens_ofs codes ll wl root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty
                 (arr_init 16 cnt) k Hk Hk1 (arr_len_init 16 cnt)
                 ltac:(intros l' Hl'; rewrite arr_get_init; apply Hc; exact Hl') l Hl).
    rewrite arr_get_set. unfold arr_inb. rewrite arr_len_init, arr_get_init. unfold RBa.zset.
    pose proof (len_at_spec wl HW HL k ltac:(lia)) as [L1 _].
    destruct (Z.eqb_spec l (len_at wl k)) as [->|NE].
    - rewrite Z.eqb_refl. destruct (Z.leb_spec 0 (len_at wl k)); [|lia].
      destruct (Z.ltb_spec (len_at wl k) 16); [|lia]. reflexivity.
    - destruct (Z.eqb_spec (len_at wl k) l); [congruence|]. reflexivity.
  Qed.

  Lemma rt_trip : forall k st a, 0 <= k < NZ wl -> RStM wl ll root ty tc table k st a ->
    match RIT.it_step c st with
    | RIT.ItCont st' => k + 1 < NZ wl /\ fails_at wl root ty k = false /\ RStM wl ll root ty tc table (k + 1) st' a
    | RIT.ItBreak st' => k + 1 = NZ wl /\ RIT.s_huff st' = hf wl (NZ wl) /\ RIT.s_len st' = len_at wl k /\
        RIT.s_drop st' = drop wl root k /\ RIT.s_next st' = noff wl root k /\ RIT.s_used st' = used wl root k /\
        TRel tc table (applyw (trips_writes wl ll root ty table (k + 1)) a) (RIT.s_tbl st') /\ TRng (RIT.s_tbl st')
    | RIT.ItOverflow _ => k + 1 < NZ wl /\ fails_at wl root ty k = true
    end.
  Proof.
    intros k st a Hk SM.
    pose proof HCX as (Hcty & Hclens & Hcroot & Hcmax & Hcmask & Hcwork & Hcmt & Hcbe).
    pose proof (root_range wl HW HL root Hroot HM1) as RR. pose proof (MAXL_spec wl HW HL) as [MM _].
    pose proof (len_at_spec wl HW HL k Hk) as [L1 _]. pose proof (len_at_range wl HW HL k Hk) as LR.
    pose proof (rank_at_spec wl HW HL k Hk) as RK.
    pose proof (curr_range wl HW HL root Hroot HM1 k Hk) as [CR1 [CR2 CR3]].
    pose proof (hf_div_bound wl root HW HL Hroot HM1 HK k Hk) as HFB.
    assert (Hdrop : 0 <= drop wl root k <= root) by (unfold drop; destruct (islong wl root k); lia).
    pose proof (last_iff wl HW HL k Hk) as LI.
    destruct SM as (Eh & Es & El & En & Ec & Ed & Elw & Eu & Hc & HT & HR).
    pose proof (here_eq st k Hk Es ltac:(rewrite El, Ed; reflexivity)) as [Hh1 Hh2].
    cbv beta zeta delta [RIT.it_step].
    rewrite Eh, Es, El, En, Ec, Ed, Elw, Eu, Hcroot, Hcmax, Hcmask, Hcty.
    rewrite !Z.shiftl_1_l.
    set (hc := RIT.it_here c st) in *. clearbody hc.
    assert (HF : TRel tc table (applyw (fill_writes wl ll root ty table k) (applyw (trips_writes wl ll root ty table k) a))
                   (RIT.it_fill (Z.to_nat (2 ^ curr wl root k / 2 ^ (len_at wl k - drop wl root k))) (RIT.s_tbl st)
                      (noff wl root k + Z.shiftr (hf wl k) (drop wl root k)) (2 ^ (len_at wl k - drop wl root k)) hc) /\
                 TRng (RIT.it_fill (Z.to_nat (2 ^ curr wl root k / 2 ^ (len_at wl k - drop wl root k))) (RIT.s_tbl st)
                      (noff wl root k + Z.shiftr (hf wl k) (drop wl root k)) (2 ^ (len_at wl k - drop wl root k)) hc)).
    { rewrite (fill_writes_eq ty lens lens_ofs codes ll wl table root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty k).
      rewrite <- Hh1, (Z.pow_sub_r 2 (curr wl root k) (len_at wl k - drop wl root k)) by lia.
      replace (table + noff wl root k + hf wl k / 2 ^ drop wl root k)
        with (table + (noff wl root k + Z.shiftr (hf wl k) (drop wl root k)))
        by (rewrite Z.shiftr_div_pow2 by lia; lia).
      apply TRel_fill; try assumption.
      - rewrite Z.shiftr_div_pow2 by lia. lia.
      - pose proof (Z.pow_nonneg 2 (len_at wl k - drop wl root k)). lia. }
    set (tbl1 := RIT.it_fill _ _ _ _ _) in *. clearbody tbl1. destruct HF as [HF1 HF2].
    rewrite (rt_rev_incr (hf wl k) (len_at wl k)) by lia.
    rewrite (hf_step ty lens lens_ofs codes ll wl root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty k Hk).
    rewrite (Hc (len_at wl k)) by lia.
    rewrite (REM_self ty lens lens_ofs codes ll wl root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty k Hk).
    rewrite RBa.zset_same.
    set (cnt1 := RBa.zset (RIT.s_count st) (len_at wl k) (W wl (len_at wl k) - rank_at wl k - 1)).
    destruct ((W wl (len_at wl k) - rank_at wl k - 1 =? 0) && (len_at wl k =? MAXL wl)) eqn:HB; cbn beta iota.
    - (* [inftrees.c:221] break *)
      apply andb_prop in HB as [HB1 HB2]. apply Z.eqb_eq in HB1, HB2.
      assert (Hk1 : k + 1 = NZ wl).
      { apply proj2 in LI. assert (X : rank_at wl k + 1 = W wl (len_at wl k)) by lia. specialize (LI (conj X HB2)). lia. }
      cbn [RIT.s_huff RIT.s_len RIT.s_drop RIT.s_next RIT.s_used RIT.s_tbl].
      split; [exact Hk1|]. split; [rewrite Hk1; reflexivity|].
      do 4 (split; [reflexivity|]). split; [|exact HF2].
      rewrite (trips_writes_S ty lens lens_ofs codes ll wl table root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty k) by lia.
      rewrite (trip_writes_nolink ty lens lens_ofs codes ll wl table root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty k).
      + rewrite applyw_app. exact HF1.
      + unfold link_writes. rewrite Hk1, Z.ltb_irrefl. reflexivity.
    - assert (Hk1 : k + 1 < NZ wl).
      { destruct (Z.eq_dec k (NZ wl - 1)) as [E|E]; [|lia]. apply proj1 in LI. specialize (LI E) as [X1 X2].
        destruct (Z.eqb_spec (W wl (len_at wl k) - rank_at wl k - 1) 0);
          destruct (Z.eqb_spec (len_at wl k) (MAXL wl)); cbn in HB; try discriminate; lia. }
      assert (Hcnt1 : forall l, 1 <= l <= 15 -> cnt1 l = REM wl (k + 1) l)
        by (apply rt_cnt_step; [lia | exact Hk1 | exact Hc]).
      assert (EL1 : (if W wl (len_at wl k) - rank_at wl k - 1 =? 0 then RIT.x_lens c (RIT.x_work c (k + 1))
                     else len_at wl k) = len_at wl (k + 1)).
      { destruct (Z.eqb_spec (W wl (len_at wl k) - rank_at wl k - 1) 0) as [H0|H0].
        - rewrite (Hcwork (k + 1)) by lia.
          pose proof (wsym_facts ty lens lens_ofs codes ll wl root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty
                        (k + 1) ltac:(lia)) as [WR WL].
          rewrite Hclens by lia. rewrite <- (LofS_ll lens lens_ofs codes ll wl Hcodes Hlens Ell Ewl) by lia. exact WL.
        - destruct (len_at_step wl HW HL k ltac:(lia) Hk1) as [[A [B C]]|[A _]]; [|lia]. symmetry; exact B. }
      rewrite EL1.
      rewrite (newtable_test ty lens lens_ofs codes ll wl root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty k ltac:(lia) Hk1).
      destruct (newtable wl root (k + 1)) eqn:HN; cbn beta iota.
      + (* [inftrees.c:243-268] a new sub-table *)
        rewrite (drop0_root ty lens lens_ofs codes ll wl root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty k).
        pose proof (lay_S_new wl HW HL root Hroot HM1 k ltac:(lia) HN) as [En1 [Ec1 Eu1]].
        pose proof (drop_low_new ty lens lens_ofs codes ll wl root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty k HN)
          as [Ed1 Elw1].
        pose proof (newtable_long wl HW HL root Hroot HM1 (k + 1) HN) as HLg.
        pose proof (len_at_spec wl HW HL (k + 1) ltac:(lia)) as [L2 _].
        rewrite (rt_subsz_spec wl HW HL root Hroot HM1 cnt1 (k + 1) ltac:(lia) HN)
          by (intros l Hl; apply Hcnt1; lia).
        rewrite <- Ec1, <- Eu1, rt_enough.
        destruct (it_not_enough ty (used wl root (k + 1))) eqn:NE; cbn beta iota.
        * split; [exact Hk1|]. unfold fails_at. rewrite HN, NE.
          destruct (Z.ltb_spec (k + 1) (NZ wl)); [reflexivity|lia].
        * split; [exact Hk1|]. split; [unfold fails_at; rewrite HN, NE; apply andb_false_r|].
          rewrite (low_val ty lens lens_ofs codes ll wl root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty (k + 1) ltac:(lia) HLg).
          unfold RStM.
          cbn [RIT.s_huff RIT.s_sym RIT.s_len RIT.s_next RIT.s_curr RIT.s_drop RIT.s_low RIT.s_used RIT.s_count RIT.s_tbl].
          rewrite En1, Ed1, Elw1.
          do 8 (split; [reflexivity|]). split; [exact Hcnt1|].
          rewrite (trips_writes_S ty lens lens_ofs codes ll wl table root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty k) by lia.
          unfold trip_writes. rewrite !applyw_app.
          unfold link_writes. rewrite HN, NE. destruct (Z.ltb_spec (k + 1) (NZ wl)); [|lia]. cbn [andb negb].
          rewrite applyw_cons. change (applyw [] ?x) with x. rewrite En1, code_pack_enc.
          split.
          -- apply TRel_set; [exact Htab | apply rev_bound; lia | exact HF1].
          -- apply TRng_set; [apply code_rng_mk | exact HF2].
      + (* no new sub-table *)
        pose proof (lay_same_proj wl HW HL root Hroot HM1 k ltac:(lia) HN) as [En1 [Ec1 Eu1]].
        pose proof (drop_low_same ty lens lens_ofs codes ll wl root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty
                      k ltac:(lia) Hk1 HN) as [Ed1 Elw1].
        split; [exact Hk1|]. split; [unfold fails_at; rewrite HN, andb_false_r; reflexivity|].
        unfold RStM.
        cbn [RIT.s_huff RIT.s_sym RIT.s_len RIT.s_next RIT.s_curr RIT.s_drop RIT.s_low RIT.s_used RIT.s_count RIT.s_tbl].
        rewrite En1, Ec1, Eu1, Ed1, Elw1.
        do 8 (split; [reflexivity|]). split; [exact Hcnt1|].
        rewrite (trips_writes_S ty lens lens_ofs codes ll wl table root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty k) by lia.
        rewrite (trip_writes_nolink ty lens lens_ofs codes ll wl table root Hcodes Hlens Ell Ewl Hroot HM1 HK Hty k)
          by (unfold link_writes; rewrite HN, andb_false_r; reflexivity).
        rewrite applyw_app. split; [exact HF1 | exact HF2].
  Qed.
End Trip.
