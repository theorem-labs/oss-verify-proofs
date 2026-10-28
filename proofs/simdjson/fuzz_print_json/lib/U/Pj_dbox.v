(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes FP StoreFast SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjPjNum SjPjDig.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Sj_num_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Pj_num_defs Pj_sf_c Pj_tochars_defs Pj_tochars_b Pj_tochars.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Ltac arr_load UA k :=
  lazymatch type of UA with
  | u8arr ?segs ?m ?A ?bs =>
      let b := fresh "b" in let RD := fresh "RD" in
      destruct (u8arr_read1 segs m A bs k UA ltac:(lia)) as [b RD];
      zstep; clear RD
  end.

Lemma bytes_at_read1 : forall segs (m : word -> option byte) A bs k,
  bytes_at segs m A bs -> (0 <= k < Z.of_nat (length bs))%Z ->
  exists b, ov_read_bytes segs m (wa (A + k)) 1 = Some [b].
Proof.
  intros segs m A bs k H Hk.
  destruct (nth_error bs (Z.to_nat k)) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  exists b. rewrite (bytes_at_read segs m A bs k 1 H) by lia.
  f_equal. apply nth_error_split in E. destruct E as (l1 & l2 & -> & L).
  rewrite <- L. rewrite skipn_app, Nat.sub_diag, skipn_all. reflexivity.
Qed.

Section DB.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (p lo NB sg : Z) (m0 : word -> option byte).
  Hypothesis ROOM : (lo <= p - DBOX_STACK)%Z.
  Hypothesis GTOP : (GLOBALS_TOP <= lo)%Z.
  Hypothesis PNB : (p + 32 <= NB)%Z.
  Hypothesis NBHI : (NB + 40 < 2^63)%Z.
  Hypothesis HSG : (0 <= sg <= 1)%Z.

  Notation POST := (dbox_post ra p gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo NB m0).
  Notation DBS pc xra xt0 xt1 xt2 xs3 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xt3 xt4 xt5 xt6 m :=
    (MS (mkR xra (Z_to_bv 64 (p + -96)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (p + 8)) (Z_to_bv 64 (p + 12)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
             (Z_to_bv 64 (NB + sg)) xs3 xs4 (Z_to_bv 64 (p + -72)) s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).

  Definition DBINV (m : word -> option byte) : Prop :=
    rw_cells usegs m (p + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    (exists tmp, u8arr usegs m (p + -96) tmp /\ length tmp = 40%nat) /\
    (exists c0 c1, rw_cells usegs m (p + 8) [C4 c0; C4 c1]) /\
    (exists nb, u8arr usegs m NB nb /\ length nb = 40%nat) /\
    mem_inv usegs m /\ munch [(p + -96, p); (p + 8, p + 16); (NB, NB + 40)]%Z m0 m /\ wmono usegs m0 m /\ stk usegs m lo (p + -96).

  Lemma db_fin : forall n d e xra xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 m,
    DBINV m -> (1 <= n <= 20)%Z -> (1 <= d <= 2)%Z -> (d <= n)%Z -> (SF_EMIN <= e <= SF_EMAX)%Z ->
    evt usegs POST (DBS 0x40790 xra xt0 xt1 xt2 (Z_to_bv 64 (e mod 4294967296)) xa0 xa1 xa2 (Z_to_bv 64 (p + -72 - n + d)) xa4 xa5 xa6 xa7
                        (Z_to_bv 64 (p + -72 - n)) xt3 xt4 xt5 xt6 m).
  Proof using ROOM GTOP PNB NBHI HSG.
    intros until m. intros I HN HD HDN HE.
    destruct I as (FRS & (tmp & TA & TL) & (c0 & c1 & CEL) & (nb & NA & NL) & MI & MU & WM & ST).
    unfold DBOX_STACK, GLOBALS_TOP, SF_EMIN, SF_EMAX in *.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.

    arr_store TA TL (24 - n + d - 1)%Z 1%nat.
    zstep. zstep. zstep. zstep.
    pose proof (bytes_at_sub usegs _ (p + -96) _ (Z.to_nat (24 - n)) 16 (proj1 TA) ltac:(rewrite TL; lia)) as SRC.
    lazymatch type of SRC with bytes_at _ _ _ ?l =>
      assert (LS : length l = 16%nat) by (rewrite length_firstn, length_skipn; lia); set (src16 := l) in *; clearbody src16 end.
    replace (p + -96 + Z.of_nat (Z.to_nat (24 - n)))%Z with (p + -72 - n)%Z in SRC by lia.
    call arr_memcpy; [ exact NA | first [eassumption | rewrite ?NL; lia] .. | ].
    clear SRC.
    match goal with H : u8arr _ _ NB ?bs, L : length ?bs = length nb |- _ => rename H into NA1; rename L into NL1; rewrite NL in NL1 end.

    zstep.
    zstep. if_cases G1; zify_cond G1; [exfalso; rewrite ?unsigned_lit in G1 by lia; lia|].
    zstep. if_cases G2; zify_cond G2; [exfalso; rewrite ?unsigned_lit in G2 by lia; lia|].

    arr_load TA (40 - n)%Z.
    zstep. zstep.
    arr_store NA1 NL1 (sg + 16)%Z 1%nat.
    zstep. if_cases G3; zify_cond G3; [exfalso; rewrite ?unsigned_lit in G3 by lia; lia|].

    zstep.
    replace (bv_swrap 32 (p + -72 - (p + -72 - n))) with n
      by (replace (p + -72 - (p + -72 - n))%Z with n by lia; symmetry; apply swrap32_id; lia).
    zstep. zstep.

    do 7 zstep. zstep. zstep.
    lazymatch type of TA with u8arr _ ?mm _ ?tb =>
      pose proof (rw_cells_of_u8arr usegs _ _ _ TA) as TMP; rewrite TL in TMP;
      pose proof (proj2 (num_rw_cells_app usegs mm (p + -96)%Z [CB 40 tb] [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])) as J;
      cbn [cells_size csize Nat.add] in J; change (Z.of_nat 40) with 40%Z in J;
      replace (p + -96 + 40)%Z with (p + -56)%Z in J by lia;
      specialize (J (conj TMP FRS)); cbn [app] in J
    end.
    release_frame J ST p.
    replace (p + -96)%Z with (p - 96)%Z in MU by lia.
    apply evt_done. unfold dbox_post.
    do 15 eexists. eexists. exists n, e. eexists.
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact HN|]. split; [unfold SF_EMIN, SF_EMAX; exact HE|].
    split; [exact CEL|]. split; [exact NA1| exact NL1].
  Qed.

  Lemma db_tail1 : forall (j w e : Z) xra xt0 xt1 xt2 xa0 xa1 xa4 xa5 xa6 xa7 xs4 xt3 xt4 xt5 xt6 m,
    DBINV m -> (0 <= w < 10)%Z -> (1 <= j <= 10)%Z -> (SF_EMIN <= e <= SF_EMAX)%Z ->
    evt usegs POST (DBS 0x40728 xra xt0 xt1 xt2 (Z_to_bv 64 (e mod 4294967296)) xa0 xa1 (Z_to_bv 64 w) (Z_to_bv 64 (p + -92 + 2 * j)) xa4 xa5 xa6 xa7
                        xs4 xt3 xt4 xt5 xt6 m).
  Proof using ROOM GTOP PNB NBHI HSG.
    intros until m. intros I HW HJ HE. pose proof I as I0.
    destruct I as (FRS & (tmp & TA & TL) & (c0 & c1 & CEL) & (nb & NA & NL) & MI & MU & WM & ST).
    unfold DBOX_STACK, GLOBALS_TOP in *.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    zstep.
    zstep. if_cases G; zify_cond G; [exfalso; rewrite ?unsigned_lit in G by lia; lia|].
    zstep. zstep. zstep.
    eapply evt_eq; [| eapply (db_fin (21 - 2 * j)%Z 1%Z e); [exact I0 | lia | lia | lia | exact HE]].
    num_st_eq.
  Qed.

  Lemma db_tail2 : forall (j w e : Z) xra xt0 xt1 xt2 xa0 xa1 xa4 xa5 xa6 xa7 xs4 xt3 xt4 xt5 xt6 m,
    DBINV m -> (10 <= w < 100)%Z -> (1 <= j <= 10)%Z -> (SF_EMIN <= e <= SF_EMAX)%Z ->
    evt usegs POST (DBS 0x4074c xra xt0 xt1 xt2 (Z_to_bv 64 (e mod 4294967296)) xa0 xa1 (Z_to_bv 64 w) (Z_to_bv 64 (p + -92 + 2 * j)) xa4 xa5 xa6 xa7
                        xs4 xt3 xt4 xt5 xt6 m).
  Proof using ROOM GTOP PNB NBHI HSG.
    intros until m. intros I HW HJ HE.
    destruct I as (FRS & (tmp & TA & TL) & (c0 & c1 & CEL) & (nb & NA & NL) & MI & MU & WM & ST).
    unfold DBOX_STACK, GLOBALS_TOP in *.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.

    zstep.
    zstep. if_cases G1; zify_cond G1; [exfalso; rewrite ?unsigned_lit in G1 by lia; lia|].

    zstep. rewrite shl1. rewrite (swrap32_id (2 * w)) by lia.
    zstep. zstep. zstep.
    zstep. if_cases G2; zify_cond G2; [exfalso; rewrite ?unsigned_lit in G2 by lia; lia|].
    destruct (image_readable_b usegs m 200 0x175f1 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (tb & TBL & TB).
    destruct (bytes_at_read1 usegs m 0x175f1 tb (2 * w) TB ltac:(lia)) as [b0 RD0].

    zstep. zstep. clear RD0 TB TBL tb.
    zstep. zstep.
    assert (LO1 : Z.lor (2 * w) 1 = (2 * w + 1)%Z).
    { assert (L : Z.land (2 * w) 1 = 0%Z) by (change 1%Z with (Z.ones 1); rewrite Z.land_ones by lia; change (2 ^ 1)%Z with 2%Z; Z.div_mod_to_equations; lia).
      rewrite <- (Z.lxor_lor _ _ L), <- (Z.add_nocarry_lxor _ _ L). reflexivity. }
    rewrite LO1.

    arr_store TA TL (2 * j + 2)%Z 1%nat.
    zstep. if_cases G3; zify_cond G3; [exfalso; rewrite ?unsigned_lit in G3 by lia; lia|].
    zstep.
    zstep. if_cases G4; zify_cond G4; [exfalso; rewrite ?unsigned_lit in G4 by lia; lia|].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (image_readable_b usegs mm 200 0x175f1 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (tb & TBL & TB);
      destruct (bytes_at_read1 usegs mm 0x175f1 tb (2 * w + 1) TB ltac:(lia)) as [b1 RD1]
    end.
    zstep. zstep. clear RD1 TB TBL tb.
    eapply evt_eq; [| eapply (db_fin (22 - 2 * j)%Z 2%Z e); [ | lia | lia | lia | exact HE]].
    - num_st_eq.
    - split; [eassumption|]. split; [eexists; split; eassumption|]. split; [do 2 eexists; eassumption|].
      split; [eexists; split; eassumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
  Qed.

  Lemma db_loop : forall (f : nat) (j w e : Z) xra xt2 xa2 xs4 xt3 xt4 xt5 xt6 m,
    DBINV m -> (100 <= w < 100 ^ j)%Z -> (w < 18446744073709551616)%Z -> (j <= 10)%Z -> (j <= Z.of_nat f)%Z -> (SF_EMIN <= e <= SF_EMAX)%Z ->
    evt usegs POST (DBS 0x406c4 xra (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 624) xt2 (Z_to_bv 64 (e mod 4294967296))
                        (Z_to_bv 64 w) (Z_to_bv 64 100) xa2 (Z_to_bv 64 (p + -94 + 2 * j)) (Z_to_bv 64 3) (Z_to_bv 64 DIV100_MAGIC)
                        (Z_to_bv 64 0x175f1) (Z_to_bv 64 18446744073709455886) xs4 xt3 xt4 xt5 xt6 m).
  Proof using ROOM GTOP PNB NBHI HSG.
    induction f as [|f IH]; intros j w e xra xt2 xa2 xs4 xt3 xt4 xt5 xt6 m I HW W64 HJ HF HE.
    { exfalso. pose proof (pow100_ge2 w j HW). lia. }
    pose proof (pow100_ge2 w j HW) as J2.
    pose proof (pow100_step w j ltac:(lia) ltac:(lia)) as HQ.
    destruct I as (FRS & (tmp & TA & TL) & (c0 & c1 & CEL) & (nb & NA & NL) & MI & MU & WM & ST).
    unfold DBOX_STACK, GLOBALS_TOP, DIV100_MAGIC in *.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.

    zstep.
    zstep. if_cases G1; zify_cond G1; [exfalso; rewrite ?unsigned_lit in G1 by lia; lia|].

    zstep. zstep. zstep.
    rewrite SFModel.land_W64. change (2 ^ 64)%Z with 18446744073709551616%Z.
    change 2951479051793528259%Z with DIV100_MAGIC. rewrite (div100_machine w) by lia.

    zstep. zstep. zstep.
    replace (w - w / 100 * 100)%Z with (w mod 100)%Z by (Z.div_mod_to_equations; lia).
    assert (R100 : (0 <= w mod 100 < 100)%Z) by (apply Z.mod_pos_bound; lia).
    set (r := (w mod 100)%Z) in *.
    rewrite (swrap32_id r) by lia. rewrite SFModel.land_W64. change (2 ^ 64)%Z with 18446744073709551616%Z.
    rewrite (Z.mod_small r) by lia. rewrite shl1. rewrite (swrap32_id (2 * r)) by lia.
    assert (LO1 : Z.lor (2 * r) 1 = (2 * r + 1)%Z).
    { assert (L : Z.land (2 * r) 1 = 0%Z) by (change 1%Z with (Z.ones 1); rewrite Z.land_ones by lia; change (2 ^ 1)%Z with 2%Z; Z.div_mod_to_equations; lia).
      rewrite <- (Z.lxor_lor _ _ L), <- (Z.add_nocarry_lxor _ _ L). reflexivity. }

    zstep. if_cases G2; zify_cond G2; [exfalso; rewrite ?unsigned_lit in G2 by lia; lia|].
    destruct (image_readable_b usegs m 200 0x175f1 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (tb & TBL & TB).
    destruct (bytes_at_read1 usegs m 0x175f1 tb (2 * r) TB ltac:(lia)) as [b0 RD0].
    zstep. zstep. clear RD0 TB TBL tb.
    zstep. rewrite LO1.
    arr_store TA TL (2 * j + 2)%Z 1%nat.

    zstep. if_cases G3; zify_cond G3; [exfalso; rewrite ?unsigned_lit in G3 by lia; lia|].
    zstep. if_cases G4; zify_cond G4; [exfalso; rewrite ?unsigned_lit in G4 by lia; lia|].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (image_readable_b usegs mm 200 0x175f1 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (tb & TBL & TB);
      destruct (bytes_at_read1 usegs mm 0x175f1 tb (2 * r + 1) TB ltac:(lia)) as [b1 RD1]
    end.
    zstep. zstep. clear RD1 TB TBL tb.
    zstep.
    arr_store TA TL (2 * j + 3)%Z 1%nat.

    zstep. zstep.
    zstep. if_cases K; zify_cond K.
    - assert (W4 : (10000 <= w)%Z).
      { rewrite ?unsigned_lit in K by (rewrite ?Z.shiftr_div_pow2 by lia; change (2 ^ 4)%Z with 16%Z; Z.div_mod_to_equations; lia).
        rewrite Z.shiftr_div_pow2 in K by lia. change (2 ^ 4)%Z with 16%Z in K. Z.div_mod_to_equations. lia. }
      eapply evt_eq; [| eapply (IH (j - 1)%Z (w / 100)%Z e); [ | | | lia | lia | exact HE]].
      + num_st_eq.
      + split; [eassumption|]. split; [eexists; split; eassumption|]. split; [do 2 eexists; eassumption|].
        split; [eexists; split; eassumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
      + split; [Z.div_mod_to_equations; lia| lia].
      + Z.div_mod_to_equations; lia.
    - assert (W4 : (w < 10000)%Z).
      { rewrite ?unsigned_lit in K by (rewrite ?Z.shiftr_div_pow2 by lia; change (2 ^ 4)%Z with 16%Z; Z.div_mod_to_equations; lia).
        rewrite Z.shiftr_div_pow2 in K by lia. change (2 ^ 4)%Z with 16%Z in K. Z.div_mod_to_equations. lia. }
      assert (Q100 : (0 <= w / 100 < 100)%Z) by (Z.div_mod_to_equations; lia).

      zstep. zstep.
      zstep. if_cases K2; zify_cond K2.
      + eapply evt_eq; [| eapply (db_tail2 (j - 1)%Z (w / 100)%Z e); [ | rewrite ?unsigned_lit in K2 by lia; lia | lia | exact HE]].
        * num_st_eq.
        * split; [eassumption|]. split; [eexists; split; eassumption|]. split; [do 2 eexists; eassumption|].
          split; [eexists; split; eassumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
      + eapply evt_eq; [| eapply (db_tail1 (j - 1)%Z (w / 100)%Z e); [ | rewrite ?unsigned_lit in K2 by lia; lia | lia | exact HE]].
        * num_st_eq.
        * split; [eassumption|]. split; [eexists; split; eassumption|]. split; [do 2 eexists; eassumption|].
          split; [eexists; split; eassumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
  Qed.

  Lemma dbox_body : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (nb : list byte) (c0 c1 : word),
    stk usegs m0 lo p -> mem_inv usegs m0 ->
    rw_cells usegs m0 (p + 8) [C4 c0; C4 c1] -> u8arr usegs m0 NB nb -> length nb = 40%nat ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (NB + sg)) (Z_to_bv 64 (p + 12)) (Z_to_bv 64 (p + 8)) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x40640) fc None m0 (seg_rom usegs)).
  Proof using ROOM GTOP PNB NBHI HSG.
    intros until c1. intros ST MI CEL NA NL.
    pose proof db_loop as KLOOP. pose proof db_tail1 as KT1. pose proof db_tail2 as KT2.
    pose proof ROOM as ROOM'. pose proof GTOP as GTOP'. unfold DBOX_STACK, GLOBALS_TOP in ROOM', GTOP'.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    pose proof (munch_refl [(p + -96, p); (p + 8, p + 16); (NB, NB + 40)]%Z m0) as MU. pose proof (wmono_refl usegs m0) as WM.
    zstep. carve_frame 96%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 96 junk [] [40;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    do 7 zstep.
    do 3 zstep. do 5 zstep. zstep.
    apply (proj1 (num_rw_cells_app usegs _ _ [CB 40 (firstn 40 junk)] _)) in FR. destruct FR as [TMP FRS].
    cbn [cells_size csize Nat.add] in FRS. change (Z.of_nat 40) with 40%Z in FRS.
    replace (p + -96 + 40)%Z with (p + -56)%Z in FRS by lia.
    pose proof (u8arr_of_rw_cells usegs _ _ _ _ TMP) as TA.
    assert (TL : length (firstn 40 junk) = 40%nat) by (destruct TMP as [[Hwf _] _]; cbn in Hwf; tauto).
    clear TMP. set (tmp := firstn 40 junk) in *. clearbody tmp.
    lazymatch goal with |- context [Z.shiftr ?x 53] => set (E := Z.shiftr x 53) end.
    assert (HE : (0 <= E <= 2047)%Z).
    { unfold E. rewrite ?SFModel.land_W64. change (2 ^ 64)%Z with 18446744073709551616%Z.
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 53)%Z with 9007199254740992%Z.
      generalize (bv_unsigned (reg_get F 10) ≪ 1)%Z. intros z. Z.div_mod_to_equations. lia. }
    clearbody E.
    eapply evt_cut; [eapply sf_proof; [eassumption | exact HE] |].
    cbv beta. intros ms' PO. unfold sf_post in PO.
    destruct PO as (y0 & y1 & y2 & w & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & e & -> & HR).
    replace (ret_pc (Z_to_bv 64 263812)) with (Z_to_bv 64 263812) by (apply bv_eq; vm_compute; reflexivity).
    pose proof (bv_unsigned_in_range 64 w) as WR. unfold bv_modulus in WR. cbn in WR.
    rewrite <- (Z_to_bv_bv_unsigned w). set (wv := bv_unsigned w) in *. clearbody wv.
    assert (I0 : DBINV m).
    { split; [exact FRS|]. split; [eexists; split; eassumption|]. split; [do 2 eexists; eassumption|].
      split; [eexists; split; eassumption|]. split; [assumption|]. split; [assumption|]. split; assumption. }

    zstep. zstep.
    zstep. if_cases G; zify_cond G; [exfalso; rewrite ?unsigned_lit in G by lia; lia|].
    zstep. zstep. zstep.
    zstep. if_cases K; zify_cond K.
    -
      rewrite ?unsigned_lit in K by lia.
      do 3 zstep.
      zstep. if_cases K2; zify_cond K2.
      + eapply evt_eq; [| eapply (KT1 10%Z wv e); [exact I0 | rewrite ?unsigned_lit in K2 by lia; lia | lia | exact HR]]. num_st_eq.
      + eapply evt_eq; [| eapply (KT2 10%Z wv e); [exact I0 | rewrite ?unsigned_lit in K2 by lia; lia | lia | exact HR]]. num_st_eq.
    - rewrite ?unsigned_lit in K by lia.
      do 9 zstep.
      replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity).
      eapply evt_eq; [| eapply (KLOOP 10%nat 10%Z wv e); [exact I0 | | lia | lia | lia | exact HR]].
      + unfold DIV100_MAGIC. num_st_eq.
      + change (100 ^ 10)%Z with 100000000000000000000%Z. lia.
  Qed.
End DB.

Theorem dbox_proof : dbox_stmt.
Proof.
  unfold dbox_stmt. intros until c1. intros ST ROOM GTOP MI PNB NBHI HSG CEL NA NL. unfold DBOX_ENTRY.
  eapply dbox_body; eassumption.
Qed.
