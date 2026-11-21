(** * A1trip — DYN ROUND Leg A3: the trip seam and the trip twin
    (q7-decode, dyn round, 2026-08-20; statements = A1StmtsV3, chase =
    A1core).  The split lemmas are the landed Q6P splits with the read
    layer swapped to [zr_decode_hdecode_two] (marker DecOks route to the
    existing M_BAD arms via the op=64 dispatch; the align implication is
    the chase's own conjunct, replacing the zr_decode_align calls); the
    trip twin is the landed zr_sym_trip body VERBATIM except the two
    split calls and the ownership transport (root_own -> two_own_v3). *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff DeflateSpec Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZReproQ6A ZReproQ6I ZReproQ6N ZReproQ6P.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtBrAlign.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import A1StmtsV3 A1core.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require W2Stream.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

Lemma zrA_len_split_two : zr_len_split_two_STMT.
Proof.
  unfold zr_len_split_two_STMT.
  intros q ll entl Hwf HV Hown Hrb Hents Hpop Hg.
  assert (Hsub : forall sym cw, code_for ll 15%nat sym = Some cw ->
                     sub_len (entl sym) = false)
    by (apply zrA_lents_sub_len; exact Hents).
  unfold inf_LEN. cbv zeta.
  rewrite Hg. cbv beta iota.
  pose proof zr_decode_hdecode_two as HD0.
  unfold zr_decode_hdecode_two_STMT in HD0.
  specialize (HD0 sub_len
       (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
       (t_lenbits (s_tab (q_st q))) ll entl (q_br q)
       Hrb HV Hown Hsub zrA_sub_len_ptr zrA_sub_len_marker Hwf).
  destruct (inf_decode sub_len
              (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
              (t_lenbits (s_tab (q_st q))) (q_br q))
    as [h b' nb|b'|] eqn:ED; cbv beta iota.
  - destruct HD0
      as (Hwf' & Hal' & [ (sym & cw & C1 & C2 & C6) | (Hrec & _) ]).
    + destruct (Z.eqb_spec (c_op h) 0) as [E0|N0]; cbv beta iota.
      * (* literal *)
        right; right; right; left.
        eexists. exists sym, cw.
        split; [reflexivity|].
        split; [exact C1|].
        split; [exact C6|].
        split. { rewrite <- C2. exact E0. }
        split. { rewrite <- C2. reflexivity. }
        split. { reflexivity. }
        split; [exact Hwf'|].
        split. { intro Hal. exact (Hal' Hal). }
        repeat split; reflexivity.
      * destruct (Z.eqb_spec (Z.land (c_op h) 32) 0) as [E32|N32];
          cbn [negb]; cbv beta iota.
        -- destruct (Z.eqb_spec (Z.land (c_op h) 64) 0) as [E64|N64];
             cbn [negb]; cbv beta iota.
           ++ (* length: fall through to LENEXT *)
              right; right; right; right; right.
              eexists. exists sym, cw.
              split; [reflexivity|].
              split; [exact C1|].
              split; [exact C6|].
              split. { rewrite <- C2. exact N0. }
              split. { rewrite <- C2. exact E32. }
              split. { rewrite <- C2. exact E64. }
              split. { rewrite <- C2. reflexivity. }
              split. { rewrite <- C2. reflexivity. }
              split; [exact Hwf'|].
              split. { intro Hal. exact (Hal' Hal). }
              repeat split; reflexivity.
           ++ (* invalid lit/len code *)
              right; right; left.
              eexists. split; [reflexivity | reflexivity].
        -- (* end of block *)
           right; right; right; right; left.
           eexists. exists sym, cw.
           split; [reflexivity|].
           split; [exact C1|].
           split; [exact C6|].
           split. { rewrite <- C2. exact N0. }
           split. { rewrite <- C2. exact N32. }
           split. { reflexivity. }
           split; [exact Hwf'|].
           split. { intro Hal. exact (Hal' Hal). }
           repeat split; reflexivity.
    + (* MARKER read: the machine BADs *)
      assert (E0 : (c_op h =? 0) = false) by (rewrite Hrec; reflexivity).
      assert (E32 : (Z.land (c_op h) 32 =? 0) = true)
        by (rewrite Hrec; reflexivity).
      assert (E64 : (Z.land (c_op h) 64 =? 0) = false)
        by (rewrite Hrec; reflexivity).
      rewrite E0, E32, E64. cbn [negb]. cbv beta iota.
      right; right; left.
      eexists. split; [reflexivity | reflexivity].
  - right; left. eexists. split; [reflexivity | reflexivity].
  - left. reflexivity.
Qed.

Lemma zrA_dist_split_two : zr_dist_split_two_STMT.
Proof.
  unfold zr_dist_split_two_STMT.
  intros q dl entd Hwf HV Hown Hrb Hents Hpop.
  assert (Hsub : forall sym cw, code_for dl 15%nat sym = Some cw ->
                     sub_dist (entd sym) = false)
    by (apply zrA_dents_sub_dist; exact Hents).
  unfold inf_DIST. cbv zeta.
  pose proof zr_decode_hdecode_two as HD0.
  unfold zr_decode_hdecode_two_STMT in HD0.
  specialize (HD0 sub_dist
       (tbl_of (q_st q) (t_distcode (s_tab (q_st q))))
       (t_distbits (s_tab (q_st q))) dl entd (q_br q)
       Hrb HV Hown Hsub zrA_sub_dist_ptr zrA_sub_dist_marker Hwf).
  destruct (inf_decode sub_dist
              (tbl_of (q_st q) (t_distcode (s_tab (q_st q))))
              (t_distbits (s_tab (q_st q))) (q_br q))
    as [h b' nb|b'|] eqn:ED; cbv beta iota.
  - destruct HD0
      as (Hwf' & Hal' & [ (dsym & cw & C1 & C2 & C6) | (Hrec & _) ]).
    + destruct (Z.eqb_spec (Z.land (c_op h) 64) 0) as [E64|N64];
        cbn [negb]; cbv beta iota.
      * (* progress into DISTEXT *)
        right; right; right.
        eexists. exists dsym, cw.
        split; [reflexivity|].
        split; [exact C1|].
        split; [exact C6|].
        split. { rewrite <- C2. reflexivity. }
        split. { rewrite <- C2. reflexivity. }
        split. { reflexivity. }
        split. { rewrite <- C2. exact E64. }
        split; [exact Hwf'|].
        split. { intro Hal. exact (Hal' Hal). }
        repeat split; reflexivity.
      * (* invalid distance code *)
        right; right; left.
        eexists. split; [reflexivity | reflexivity].
    + (* MARKER read: the machine BADs *)
      assert (E64 : (Z.land (c_op h) 64 =? 0) = false)
        by (rewrite Hrec; reflexivity).
      rewrite E64. cbn [negb]. cbv beta iota.
      right; right; left.
      eexists. split; [reflexivity | reflexivity].
  - right; left. eexists. split; [reflexivity | reflexivity].
  - left. reflexivity.
Qed.

(** The trip twin: the landed [zr_sym_trip] body verbatim modulo the
    intro line, the two split calls, and the ownership transport. *)
Lemma zr_sym_trip_dyn : zr_sym_trip_dyn_STMT.
Proof.
  unfold zr_sym_trip_dyn_STMT.
  intros c q ll dl entl entd HVl HVd Hownl Hownd Hrbl Hrbd
         Hentsl Hentsd Hpopl Hpopd Hwf Hput Hleft Htie Hcap Hwh Hsn Hm Hg.
  assert (HSTEP : inf_step c q = inf_LEN q) by (apply zr_step_at_len; exact Hm).
  destruct (zrA_len_split_two q ll entl Hwf HVl Hownl Hrbl Hentsl Hpopl Hg)
    as [ EF
       | [ (q2 & EL & ERet)
         | [ (qb & EB & HMb)
           | [ (qL & sym & cw & EC & Hcf & Hhd & Hop0 & HlenL & HmL
                & HwfL & HhaL & HfrL)
             | [ (qT & sym & cw & EC & Hcf & Hhd & HopN & Hl32 & HmT
                  & HwfT & HhaT & HfrT)
               | (qE & sym & cw & EC & Hcf & Hhd & HopN & Hl32 & Hl64
                  & HlenE & HextE & HwfE & HhaE & HfrE) ] ] ] ] ].
  - (* decode fuel *)
    right; right. exists 1%nat, InfFuel.
    split; [ apply inf_loop_one_exit; [ rewrite HSTEP; exact EF | exact I ]
           | exact I ].
  - (* decode starvation leave *)
    right; right. exists 1%nat, (InfLeave q2).
    split; [ apply inf_loop_one_exit; [ rewrite HSTEP; exact EL | exact I ]
           | exact ERet ].
  - (* invalid lit/len code *)
    right; left. exists 1%nat, qb.
    split; [ apply inf_iter_one; rewrite HSTEP; exact EB | exact HMb ].
  - (* ---- literal ---- *)
    destruct (Hentsl sym cw Hcf)
      as [ (Hs256 & _ & Hval)
         | [ (_ & HopC & _) | [ (_ & (b0 & e0 & _ & _ & HopC & _))
           | (HopC & _ & _) ] ] ];
      try (exfalso; congruence);
      try (exfalso; rewrite Hop0 in HopC; lia).
    destruct HfrL as (HObL & HRetL & HInL & HOutL & HTabL & HWinL
                      & HLastL & HWrapL & HFlagL & HCheckL & HTotalL).
    assert (HI1 : inf_iter 1 c q = Some qL)
      by (apply inf_iter_one; rewrite HSTEP; exact EC).
    assert (HlenLv : 0 <= u_length (s_cur (q_st qL)) < 256)
      by (rewrite HlenL, Hval; lia).
    assert (HSTEP2 : inf_step c qL = inf_LIT qL)
      by (apply zr_step_at_lit; exact HmL).
    destruct (zr_lit_split qL ltac:(rewrite HObL; exact Hput) HlenLv)
      as [ (Elz & ELV) | (qL' & ECw & HSl & HPutw & HLeftw & HMw & HBrw
                          & HRetw & HInw & HOutw & HTabw & HWinw & HLastw
                          & HWrapw & HFlagw & HCheckw & HTotalw) ].
    + (* output full: starve on the LIT step *)
      right; right. exists 2%nat, (InfLeave qL).
      split.
      { apply (inf_loop_after_iter 1 c q qL 1 (InfLeave qL) HI1).
        apply inf_loop_one_exit; [ rewrite HSTEP2; exact ELV | exact I ]. }
      rewrite HRetL. reflexivity.
    + (* the literal byte *)
      left. exists 2%nat, qL', (LzLit (Z.of_nat sym)).
      split.
      { change 2%nat with (1 + 1)%nat.
        rewrite (inf_iter_add 1 1 c q qL HI1).
        apply inf_iter_one. rewrite HSTEP2. exact ECw. }
      split.
      { unfold decode_lit_len. rewrite Hhd. cbv beta iota.
        rewrite (proj2 (Nat.ltb_lt sym 256) Hs256). cbv beta iota.
        rewrite HBrw. reflexivity. }
      split.
      { split.
        - rewrite HSl, HObL, HlenL, Hval. reflexivity.
        - exact HMw. }
      split. { rewrite HBrw. exact HwfL. }
      split. { rewrite HPutw, HObL. lia. }
      split.
      { rewrite HLeftw, HObL.
        destruct (Z.eqb_spec (o_left (q_ob qL)) 0) as [E|N].
        - exfalso. unfold inf_LIT in ECw.
          rewrite (proj2 (Z.eqb_eq _ 0) E) in ECw. discriminate.
        - rewrite HObL in N. lia. }
      split. { rewrite HPutw, HLeftw, HObL. lia. }
      split. { rewrite HTabw. exact HTabL. }
      split. { rewrite HWinw. exact HWinL. }
      split. { rewrite HLastw. exact HLastL. }
      split. { rewrite HWrapw. exact HWrapL. }
      split. { rewrite HRetw. exact HRetL. }
      split. { rewrite HInw. exact HInL. }
      split. { rewrite HOutw. exact HOutL. }
      split. { intro Hal. rewrite HBrw. exact (HhaL Hal). }
      split. { rewrite HFlagw. exact HFlagL. }
      split. { rewrite HCheckw. exact HCheckL. }
      rewrite HTotalw. exact HTotalL.
  - (* ---- end of block ---- *)
    destruct (Hentsl sym cw Hcf)
      as [ (_ & HopC & _)
         | [ (Hs256 & _ & _) | [ (_ & (b0 & e0 & _ & _ & _ & Hl32C & _))
           | (_ & Hl32C & _) ] ] ];
      try (exfalso; congruence).
    destruct HfrT as (HObT & HRetT & HInT & HOutT & HTabT & HWinT
                      & HLastT & HWrapT & HFlagT & HCheckT & HTotalT).
    left. exists 1%nat, qT, LzEnd.
    split.
    { apply inf_iter_one. rewrite HSTEP. exact EC. }
    split.
    { unfold decode_lit_len. rewrite Hhd. cbv beta iota.
      rewrite (proj2 (Nat.ltb_ge sym 256) ltac:(lia)).
      rewrite (proj2 (Nat.eqb_eq sym 256) Hs256). cbv beta iota.
      reflexivity. }
    split. { split; [exact HObT | exact HmT]. }
    split. { exact HwfT. }
    split. { rewrite HObT. exact Hput. }
    split. { rewrite HObT. exact Hleft. }
    split. { rewrite HObT. reflexivity. }
    split. { exact HTabT. }
    split. { exact HWinT. }
    split. { exact HLastT. }
    split. { exact HWrapT. }
    split. { exact HRetT. }
    split. { exact HInT. }
    split. { exact HOutT. }
    split. { intro Hal. exact (HhaT Hal). }
    split. { exact HFlagT. }
    split. { exact HCheckT. }
    exact HTotalT.
  - (* ---- length/distance reference ---- *)
    destruct (Hentsl sym cw Hcf)
      as [ (_ & HopC & _)
         | [ (_ & _ & Hl32C & _) | [ (Hs257 & (b0 & e0 & Hb0 & He0 & HopC
              & _ & _ & Hl15 & Hval & _ & Hb0b & He0b & _))
           | (_ & _ & _ & Hl64C) ] ] ];
      try (exfalso; congruence).
    destruct HfrE as (HObE & HRetE & HInE & HOutE & HTabE & HWinE
                      & HLastE & HWrapE & HFlagE & HCheckE & HTotalE).
    (* stage: LENEXT *)
    assert (HextEv : 0 <= u_extra (s_cur (q_st qE)) <= 13)
      by (rewrite HextE, Hl15; lia).
    destruct (zr_lenext_split qE HwfE HextEv)
      as [ (b2 & ELV)
         | (qD & v1 & ECD & HRd1 & Hv1 & HlenD & HwfD & HhaD & HfrD) ].
    { (* starved on length extra *)
      right; right. exists 1%nat, (InfLeave (qset_br qE b2)).
      split.
      { apply inf_loop_one_exit;
          [ rewrite HSTEP, EC; exact ELV | exact I ]. }
      cbn [q_ret qset_br]. exact HRetE. }
    rewrite HextE, Hl15, Nat2Z.id in HRd1.
    destruct HfrD as (HObD & HRetD & HInD & HOutD & HTabD & HWinD
                      & HLastD & HWrapD & HFlagD & HCheckD & HTotalD).
    (* stage: DIST — transport the table hypotheses to qD *)
    assert (HstD : s_tab (q_st qD) = s_tab (q_st q))
      by (rewrite HTabD; exact HTabE).
    assert (HownDq : zr_two_own_v3
              (tbl_of (q_st qD) (t_distcode (s_tab (q_st qD))))
              (t_distbits (s_tab (q_st qD))) dl entd).
    { rewrite HstD, (tbl_of_stable (q_st q) (q_st qD) _ HstD).
      exact Hownd. }
    assert (HrbDq : 0 < t_distbits (s_tab (q_st qD)) <= 15)
      by (rewrite HstD; exact Hrbd).
    destruct (zrA_dist_split_two qD dl entd HwfD HVd HownDq HrbDq Hentsd Hpopd)
      as [ EFd
         | [ (q2d & ELd & ERetd)
           | [ (qbd & EBd & HMbd)
             | (qX & dsym & cwd & ECX & Hcfd & Hhdd & HoffX & HextX
                & HlenX & Hl64d & HwfX & HhaX & HfrX) ] ] ].
    { (* dist decode fuel *)
      right; right. exists 1%nat, InfFuel.
      split; [ apply inf_loop_one_exit;
               [ rewrite HSTEP, EC, ECD; exact EFd | exact I ]
             | exact I ]. }
    { (* dist decode starvation *)
      right; right. exists 1%nat, (InfLeave q2d).
      split.
      { apply inf_loop_one_exit;
          [ rewrite HSTEP, EC, ECD; exact ELd | exact I ]. }
      rewrite ERetd, HRetD. exact HRetE. }
    { (* invalid distance code *)
      right; left. exists 1%nat, qbd.
      split; [ apply inf_iter_one; rewrite HSTEP, EC, ECD; exact EBd
             | exact HMbd ]. }
    destruct (Hentsd dsym cwd Hcfd)
      as [ (b0d & e0d & Hb0d & He0d & HopCd & _ & Hl15d & Hvald
            & Hb0db & He0db)
         | (Hl64Cd & _) ];
      [ | exfalso; congruence ].
    destruct HfrX as (HObX & HRetX & HInX & HOutX & HTabX & HWinX
                      & HLastX & HWrapX & HFlagX & HCheckX & HTotalX).
    (* stage: DISTEXT *)
    assert (HextXv : 0 <= u_extra (s_cur (q_st qX)) <= 13)
      by (rewrite HextX, Hl15d; lia).
    destruct (zr_distext_split qX HwfX HextXv)
      as [ (b2 & ELX)
         | (qM & v2 & ECM & HRd2 & Hv2 & HoffM & HlenM & HmM & HwfM
            & HhaM & HfrM) ].
    { (* starved on distance extra *)
      right; right. exists 1%nat, (InfLeave (qset_br qX b2)).
      split.
      { apply inf_loop_one_exit;
          [ rewrite HSTEP, EC, ECD, ECX; exact ELX | exact I ]. }
      cbn [q_ret qset_br].
      rewrite HRetX, HRetD. exact HRetE. }
    rewrite HextX, Hl15d, Nat2Z.id in HRd2.
    destruct HfrM as (HObM & HRetM & HInM & HOutM & HTabM & HWinM
                      & HLastM & HWrapM & HFlagM & HCheckM & HTotalM).
    (* the composite frame q -> qM *)
    assert (HObQ : q_ob qM = q_ob q) by congruence.
    assert (HRetQ : q_ret qM = q_ret q) by congruence.
    assert (HInQ : q_in qM = q_in q) by congruence.
    assert (HOutQ : q_out qM = q_out q) by congruence.
    assert (HTabQ : s_tab (q_st qM) = s_tab (q_st q)) by congruence.
    assert (HWinQ : s_win (q_st qM) = s_win (q_st q)) by congruence.
    assert (HLastQ : h_last (s_hdr (q_st qM)) = h_last (s_hdr (q_st q)))
      by congruence.
    assert (HWrapQ : h_wrap (s_hdr (q_st qM)) = h_wrap (s_hdr (q_st q)))
      by congruence.
    assert (HFlagQ : h_flags (s_hdr (q_st qM)) = h_flags (s_hdr (q_st q)))
      by congruence.
    assert (HCheckQ : h_check (s_hdr (q_st qM)) = h_check (s_hdr (q_st q)))
      by congruence.
    assert (HTotalQ : h_total (s_hdr (q_st qM)) = h_total (s_hdr (q_st q)))
      by congruence.
    (* values at qM *)
    assert (HoffMv : u_offset (s_cur (q_st qM)) = Z.of_nat b0d + v2)
      by (rewrite HoffM, HoffX, Hvald; reflexivity).
    assert (HlenMv : u_length (s_cur (q_st qM)) = Z.of_nat b0 + v1)
      by (rewrite HlenM, HlenX, HlenD, HlenE, Hval; reflexivity).
    (* concrete extra-value bounds (the 2^atom forms are lia-opaque) *)
    assert (Hv1b : 0 <= v1 < 32).
    { split; [lia|].
      apply (Z.lt_le_trans _ (2 ^ u_extra (s_cur (q_st qE)))); [lia|].
      replace 32 with (2 ^ 5) by reflexivity.
      apply Z.pow_le_mono_r; [lia|].
      rewrite HextE, Hl15. lia. }
    assert (Hv2b : 0 <= v2 < 8192).
    { split; [lia|].
      apply (Z.lt_le_trans _ (2 ^ u_extra (s_cur (q_st qX)))); [lia|].
      replace 8192 with (2 ^ 13) by reflexivity.
      apply Z.pow_le_mono_r; [lia|].
      rewrite HextX, Hl15d. lia. }
    (* MATCH *)
    destruct (zr_match_cases qM
                ltac:(rewrite HObQ; exact Hput)
                ltac:(rewrite HObQ; exact Hleft)
                ltac:(rewrite HObQ, HOutQ; exact Htie)
                ltac:(rewrite HOutQ; exact Hcap)
                ltac:(rewrite HWinQ; exact Hwh)
                ltac:(rewrite HTabQ; exact Hsn)
                ltac:(rewrite HoffMv; lia)
                ltac:(rewrite HlenMv; lia))
      as [ (ElM & ELM)
         | [ (qbm & EBm & HMbm)
           | [ (q' & ECf & Hoffle & Hlenle & HSlf & HPutf & HSumf & HMf
                & HBrf & HLastf & HWrapf & HFlagf & HCheckf & HTotalf
                & HWinf & HTabf & HRetf & HInf & HOutf)
             | (q4 & ECp & HLeft4 & HMode4 & HRet4) ] ] ].
    + (* starved at MATCH entry *)
      right; right. exists 1%nat, (InfLeave qM).
      split.
      { apply inf_loop_one_exit;
          [ rewrite HSTEP, EC, ECD, ECX, ECM; exact ELM | exact I ]. }
      rewrite HRetQ. reflexivity.
    + (* distance too far *)
      right; left. exists 1%nat, qbm.
      split; [ apply inf_iter_one; rewrite HSTEP, EC, ECD, ECX, ECM;
               exact EBm
             | exact HMbm ].
    + (* FULL copy: the LzRef agreement *)
      left.
      exists 1%nat, q',
        (LzRef (b0 + Z.to_nat v1)%nat (b0d + Z.to_nat v2)%nat).
      assert (HI1 : inf_iter 1 c q = Some q')
        by (apply inf_iter_one; rewrite HSTEP, EC, ECD, ECX, ECM;
            exact ECf).
      assert (HlenN : Z.to_nat (u_length (s_cur (q_st qM)))
                      = (b0 + Z.to_nat v1)%nat)
        by (rewrite HlenMv, Z2Nat.inj_add by lia; rewrite Nat2Z.id;
            reflexivity).
      assert (HoffN : Z.to_nat (u_offset (s_cur (q_st qM)))
                      = (b0d + Z.to_nat v2)%nat)
        by (rewrite HoffMv, Z2Nat.inj_add by lia; rewrite Nat2Z.id;
            reflexivity).
      split. { exact HI1. }
      split.
      { unfold decode_lit_len. rewrite Hhd. cbv beta iota.
        rewrite (proj2 (Nat.ltb_ge sym 256) ltac:(lia)).
        rewrite (proj2 (Nat.eqb_neq sym 256) ltac:(lia)).
        cbv beta iota.
        unfold read_extra. rewrite Hb0, He0. cbv beta iota.
        rewrite HRd1. cbv beta iota.
        rewrite Hhdd. cbv beta iota.
        rewrite Hb0d, He0d. cbv beta iota.
        rewrite HRd2. cbv beta iota.
        rewrite HBrf. reflexivity. }
      split.
      { split.
        { apply (proj2 (Nat.eqb_neq _ 0)). lia. }
        split.
        { replace (Z.of_nat (b0d + Z.to_nat v2))
            with (u_offset (s_cur (q_st qM))) by (rewrite HoffMv; lia).
          rewrite <- HObQ. exact Hoffle. }
        split.
        { rewrite HSlf, HObQ, HlenN, HoffN. reflexivity. }
        exact HMf. }
      split. { rewrite HBrf. exact HwfM. }
      split. { rewrite HPutf, HObQ, HlenMv. lia. }
      split.
      { rewrite HObQ in Hlenle, HSumf, HPutf.
        rewrite HlenMv in Hlenle, HPutf. lia. }
      split. { rewrite HSumf, HObQ. reflexivity. }
      split. { rewrite HTabf. exact HTabQ. }
      split. { rewrite HWinf. exact HWinQ. }
      split. { rewrite HLastf. exact HLastQ. }
      split. { rewrite HWrapf. exact HWrapQ. }
      split. { rewrite HRetf. exact HRetQ. }
      split. { rewrite HInf. exact HInQ. }
      split. { rewrite HOutf. exact HOutQ. }
      split. { intro Hal. rewrite HBrf. exact (HhaM (HhaX (HhaD (HhaE Hal)))). }
      split. { rewrite HFlagf. exact HFlagQ. }
      split. { rewrite HCheckf. exact HCheckQ. }
      rewrite HTotalf. exact HTotalQ.
    + (* PARTIAL copy: output exhausted, next trip starves *)
      right; right. exists 2%nat, (InfLeave q4).
      assert (HI1 : inf_iter 1 c q = Some q4)
        by (apply inf_iter_one; rewrite HSTEP, EC, ECD, ECX, ECM;
            exact ECp).
      split.
      { apply (inf_loop_after_iter 1 c q q4 1 (InfLeave q4) HI1).
        apply inf_loop_one_exit;
          [ rewrite (zr_step_at_match c q4
                       ltac:(rewrite HMode4; exact HmM));
            apply zr_match_left0; exact HLeft4
          | exact I ]. }
      rewrite HRet4, HRetQ. reflexivity.
Qed.

