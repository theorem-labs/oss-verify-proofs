(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_frame_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import frame_kit.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma fcs_mask_form : forall ty fcs, (ty = 0 \/ ty = 1) -> 0 <= fcs < 18446744073709551616 ->
  Z.land ((Z.b2z ((ty + -1) mod 18446744073709551616 <? 1) + -1) mod 18446744073709551616) fcs = (if ty =? 1 then 0 else fcs).
Proof.
  intros ty fcs [-> | ->] Hf.
  - change ((0 + -1) mod 18446744073709551616 <? 1) with false. cbn [Z.b2z].
    change ((0 + -1) mod 18446744073709551616) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
    change (2^64) with 18446744073709551616. rewrite Z.mod_small by lia. reflexivity.
  - change ((1 + -1) mod 18446744073709551616 <? 1) with true. cbn [Z.b2z]. change ((1 + -1) mod 18446744073709551616) with 0.
    apply Z.land_0_l.
Qed.

(* [comment removed for export] *)
Lemma cblock_ret_range' : forall src ip rem, all_bytes src ->
  0 <= cblock_ret (get_cblock_size src ip rem) < 18446744073709551616.
Proof.
  intros src ip rem OK. unfold get_cblock_size.
  destruct (rem <? ZD_blockHeaderSize); cbn [cblock_ret].
  - unfold ZERR, ZE_srcSize_wrong. change (2^64) with 18446744073709551616. lia.
  - pose proof (cblock_props_range (le24 src ip) (le24_range src OK ip)) as (_ & _ & RO2). change (2^21) with 2097152 in RO2.
    unfold bt_rle, bt_reserved, ZERR, ZE_corruption_detected. change (2^64) with 18446744073709551616.
    destruct (_ =? 1); [lia|]. destruct (_ =? 3); lia.
Qed.

Lemma fsi_blocks_fuel_err_range : forall src, all_bytes src -> forall f ip rem nb v,
  fsi_blocks_fuel f src ip rem nb = FL_err v -> 0 <= v < 18446744073709551616.
Proof.
  intros src OK. induction f as [|f IH]; intros ip rem nb v E; cbn [fsi_blocks_fuel] in E.
  - injection E as <-. unfold ZERR, ZE_srcSize_wrong. change (2^64) with 18446744073709551616. lia.
  - pose proof (cblock_ret_range' src ip rem OK) as RC.
    destruct (get_cblock_size src ip rem) as [[cbs bp]|]; cbn [cblock_ret] in RC.
    + destruct (zd_is_error cbs); [injection E as <-; exact RC|].
      destruct (rem <? ZD_blockHeaderSize + cbs); [injection E as <-; unfold ZERR, ZE_srcSize_wrong; change (2^64) with 18446744073709551616; lia|].
      destruct (bp_last bp =? 0); [eapply IH; exact E| discriminate E].
    + injection E as <-. exact RC.
Qed.

Lemma fsi_csize_range : forall src off sz, all_bytes src -> 0 <= off -> 5 <= sz < 18446744073709551616 ->
  0 <= find_frame_compressed_size src off sz < 18446744073709551616.
Proof.
  intros src off sz OK OFF RSZ. unfold find_frame_compressed_size, find_frame_size_info.
  destruct ((ZD_SKIPPABLEHEADERSIZE <=? sz) && is_skippable_magic (le32 src off)); cbn [fsi_csize].
  - unfold read_skippable_frame_size. pose proof (le32_range src OK (off + 4)) as R4. change (2^32) with 4294967296 in R4.
    unfold ZERR, ZE_srcSize_wrong, ZE_frameParameter_unsupported, ZD_SKIPPABLEHEADERSIZE. change (2^64) with 18446744073709551616.
    destruct (sz <? 8); [lia|]. cbv zeta. destruct (_ <? le32 src (off + 4)); [lia|]. destruct (sz <? _); lia.
  - destruct (get_frame_header src off sz) as [h|v] eqn:G.
    + pose proof (get_frame_header_ok src OK off sz h G) as (TY & _ & RHS & _ & _ & _ & _ & _ & HT0 & HT1).
      assert (RHS0 : 5 <= fh_hsize h).
      { destruct TY as [T|T].
        - destruct (HT0 T) as (_ & _ & RR & _). unfold ZD_FRAMEHEADERSIZE_MIN, ZD_FRAMEHEADERSIZE_MAX in RR. lia.
        - destruct (HT1 T) as (_ & RR & _). unfold ZD_SKIPPABLEHEADERSIZE in RR. lia. }
      destruct (fsi_blocks src (off + fh_hsize h) (sz - fh_hsize h) 0) as [v|ip rem nb] eqn:B.
      * cbn [fsi_csize]. eapply fsi_blocks_fuel_err_range; [exact OK| exact B].
      * apply (fsi_blocks_done src OK) in B. destruct B as (B1 & B2 & B3 & _). unfold ZD_blockHeaderSize in B1.
        destruct (negb (fh_checksum h =? 0) && (rem <? 4)) eqn:C; cbv zeta; cbn [fsi_csize].
        -- unfold ZERR, ZE_srcSize_wrong. change (2^64) with 18446744073709551616. lia.
        -- destruct (fh_checksum h =? 0); cbn [negb andb] in C; [lia|]. apply Z.ltb_ge in C. lia.
    + pose proof (gfh_ret_pos src off sz v ltac:(lia) G) as RV.
      destruct (zd_is_error v); cbn [fsi_csize]; [lia|]. unfold ZERR, ZE_srcSize_wrong. change (2^64) with 18446744073709551616. lia.
Qed.

Section FINDDSIZE.
  Hypothesis GETFH : zd_getfh_stmt.
  Hypothesis FINDFSI : zd_findfsi_stmt.
  Variables (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SP SRC : Z) (src : list Z) (size0 : Z) (lo : Z).
  Hypothesis SB : bytes_at usegs m SRC (map (Z_to_bv 8) src).
  Hypothesis OK : all_bytes src.
  Hypothesis N0 : 0 <= size0.
  Hypothesis N40 : size0 < 1099511627776.
  Hypothesis NLEN : size0 <= zlen src.
  Hypothesis SRC0 : 0 < SRC.
  Hypothesis SRCE : SRC + zlen src < 2^64.
  Hypothesis ST : stk usegs m lo SP.
  Hypothesis LO : lo <= SP - 320.
  Hypothesis RSP : 0 <= SP < 2^64.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SS : SRC + zlen src <= lo \/ SP <= SRC.
  Hypothesis MI : mem_inv usegs m.

  Notation W := [(SP - 320, SP)].
  Notation POST := (zd_finddsize_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc SP src size0 lo m).
  Notation RES := (find_decompressed_size src size0).

  (* [comment removed for export] *)
  Notation STpc pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  (* [comment removed for export] *)
  Notation K8 := (Z_to_bv 64 8).  Notation K4 := (Z_to_bv 64 4).  Notation KM3 := (Z_to_bv 64 (-3)).
  Notation KSK := (Z_to_bv 64 25481893).  Notation KW := (Z_to_bv 64 4294967287).  Notation KM120 := (Z_to_bv 64 (-120)).

  Definition XINV (m1 : fmem) : Prop :=
    bytes_at usegs m1 SRC (map (Z_to_bv 8) src)
    /\ (exists csz, rw_cells usegs m1 (SP + -144) csz /\ cells_size csz = 48%nat)
    /\ rw_cells usegs m1 (SP + -96) [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk usegs m1 lo (SP + -144)
    /\ munch W m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1.

  (* [comment removed for export] *)
  Lemma p_ret : forall m1 r (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 : word),
    XINV m1 -> Z_to_bv 64 r = Z_to_bv 64 RES ->
    evt usegs POST (STpc 0x150f8 m1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 r) x19 x20 x21 x22 x23 x24 x25 x26).
  Proof.
    intros m1 r x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26
           (SB1 & (csz & ZFC & ZSZ) & SAVED & ST1 & MU1 & WM1 & MI1) ER.
    do 13 zs.
    assert (FR : rw_cells usegs m1 (SP + -144) (csz ++ [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact ZFC|].
      rewrite ZSZ. replace (SP + -144 + Z.of_nat 48) with (SP + -96) by lia. exact SAVED. }
    eapply stk_release in FR; [| exact ST1 | lia].
    rewrite !cells_size_app, ZSZ in FR. cbn [cells_size csize Nat.add] in FR.
    replace (SP + -144 + Z.of_nat 144) with SP in FR by lia.
    zs. zs. rewrite ER.
    apply evt_done. unfold zd_finddsize_post.
    do 10 eexists. exists m1. split; [reflexivity|].
    split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1| exact FR].
  Qed.

  (* [comment removed for export] *)
  Lemma p_chk : forall m1 off sz total (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 : word),
    XINV m1 -> RES = find_dsize src off sz total -> 0 <= sz < 5 -> 0 <= total < 18446744073709551616 ->
    evt usegs POST (STpc 0x150ec m1 x1 x5 x6 x7 (Z_to_bv 64 sz) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 total) x22 x23 x24 x25 x26).
  Proof.
    intros m1 off sz total x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 XI ER RSZ RT.
    rewrite (find_dsize_eq src OK) in ER by (change (2^64) with 18446744073709551616; lia).
    unfold ZD_FRAMEHEADERSIZE_PREFIX in ER. replace (sz <? 5) with true in ER by (symmetry; apply Z.ltb_lt; lia).
    zs. if_cases K; zify_cond K.
    - zs. eapply p_ret; [exact XI|]. rewrite ER. replace (sz =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
    - zs. zs. eapply p_ret; [exact XI|]. rewrite ER. replace (sz =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      apply Z_to_bv_eqm. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma p_loop : forall (n : nat) m1 off sz total (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x26 : word),
    sz <= Z.of_nat n -> XINV m1 -> RES = find_dsize src off sz total ->
    5 <= sz -> 0 <= off -> off + sz <= size0 -> 0 <= total < 18446744073709551616 ->
    evt usegs POST (STpc 0x15170 m1 x1 x5 x6 x7 (Z_to_bv 64 sz) (Z_to_bv 64 (SRC + off)) x10 x11 x12 x13 x14 x15 x16 x17 x18
                         K8 K4 (Z_to_bv 64 total) KM120 KSK KW KM3 x26).
  Proof.
    induction n as [|n IH]; intros m1 off sz total x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x26 RN XI ER R5 ROFF RSZ RT; [exfalso; lia|].
    pose proof XI as (SB1 & (csz & ZFC & ZSZ) & SAVED & ST1 & MU1 & WM1 & MI1).
    pose proof (bytes_at_bound _ _ _ _ SB1) as DB. rewrite length_map in DB.
    assert (LENP : zlen (map (Z_to_bv 8) src) = zlen src) by (rewrite length_map; reflexivity).
    pose proof ST1 as (LO0 & _ & _).
    rewrite (find_dsize_eq src OK) in ER by (change (2^64) with 18446744073709551616; lia).
    unfold ZD_FRAMEHEADERSIZE_PREFIX in ER. replace (sz <? 5) with false in ER by (symmetry; apply Z.ltb_ge; lia).
    (* [comment removed for export] *)
    assert (ADV : forall mm step total' (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y26 : word),
      XINV mm -> 8 <= step <= sz -> RES = find_dsize src (off + step) (sz - step) total' -> 0 <= total' < 18446744073709551616 ->
      evt usegs POST (STpc 0x15164 mm y1 y5 y6 y7 (Z_to_bv 64 sz) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 step) y11 y12 y13 y14 y15 y16 y17 y18
                           K8 K4 (Z_to_bv 64 total') KM120 KSK KW KM3 y26)).
    { intros mm step total' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y26 XIm RST ERm RTm.
      zs. zs. replace (SRC + off + step) with (SRC + (off + step)) by lia.
      zs. if_cases KX; zify_cond KX.
      - eapply p_chk; [exact XIm | exact ERm | lia | exact RTm].
      - eapply (IH mm (off + step) (sz - step) total'); try eassumption; lia. }
    zs. fck.
    zlb SB1 OK (off + 1). zlb SB1 OK off. zlb SB1 OK (off + 2). zlb SB1 OK (off + 3).
    do 7 zs.
    match goal with |- context [Z.shiftr ?e 4] => replace e with (le32 src off) by (rewrite le32_bytes; lia) end.
    pose proof (le32_range src OK off) as RM. change (2^32) with 4294967296 in RM.
    rewrite Z.shiftr_div_pow2 by lia. change (2^4) with 16.
    zs. if_cases KS; zify_cond KS.
    - (* [comment removed for export] *)
      unfold is_skippable_magic in ER. replace (le32 src off / 16 =? 25481893) with false in ER by (symmetry; apply Z.eqb_neq; lia).
      cbv zeta in ER.
      zs. zs. zs. zs. zs.
      unfold PZD_GETFH in GETFH.
      call (GETFH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SP + -144) (SP + -144) SRC src off sz _ lo);
        [ exact SB1 | exact OK | exact ROFF | exact R5 | lia | exact SRC0 | exact ZFC | exact ZSZ
        | clear - SP16; Z.div_mod_to_equations; lia | exact ST1
        | lia | lia | lia | lia | lia | exact MI1 | reflexivity | reflexivity | reflexivity | reflexivity | ].
      rename PC into ST2. rename PC0 into ZFC'. rename PC1 into ZSZ'. rename POST into ZFP. rename MI0 into MI2.
      assert (XI2 : forall mm cs, bytes_at usegs mm SRC (map (Z_to_bv 8) src) ->
                rw_cells usegs mm (SP + -144) cs -> cells_size cs = 48%nat ->
                rw_cells usegs mm (SP + -96) [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
                stk usegs mm lo (SP + -144) -> munch W m mm -> wmono usegs m mm -> mem_inv usegs mm -> XINV mm).
      { intros mm cs A0 A2 A3 A4 A5 A6 A7 A8. split; [exact A0|]. split; [eexists; split; [exact A2| exact A3]|].
        split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7| exact A8]. }
      set (gfh := get_frame_header src off sz) in *.
      assert (RRET : 0 <= fh_retval gfh < 18446744073709551616).
      { destruct gfh as [hh|v] eqn:G; cbn [fh_retval]; [lia|]. pose proof (gfh_ret_pos src off sz v R5 G). lia. }
      zs. if_cases K0; zify_cond K0.
      + (* [comment removed for export] *)
        destruct gfh as [h|v] eqn:G; cbn [fh_retval] in *; [| exfalso; pose proof (gfh_ret_pos src off sz v R5 G); lia].
        rewrite (ZFP h eq_refl) in ZFC'. clear ZFP.
        pose proof (get_frame_header_ok src OK off sz h G) as (TY & _ & _ & RFCS & _).
        change (2^64) with 18446744073709551616 in RFCS.
        unfold get_frame_content_size in ER. fold gfh in ER. rewrite G in ER.
        set (fcs := if fh_type h =? 1 then 0 else fh_fcs h) in *.
        assert (RFCS2 : 0 <= fcs < 18446744073709551616) by (unfold fcs; destruct (fh_type h =? 1); lia).
        unfold zfh_cells in ZFC'.
        zs. rewrite sx32w_small by lia.
        zs. zs. zs. zs. zs.
        rewrite (fcs_mask_form (fh_type h) (fh_fcs h) TY RFCS). fold fcs.
        zs. if_cases KF; zify_cond KF.
        * (* [comment removed for export] *)
          zs. zs. eapply p_ret; [eapply XI2; eassumption || reflexivity|].
          rewrite ER. unfold ZD_CONTENTSIZE_ERROR. change (2^64 - 2) with 18446744073709551614.
          replace (18446744073709551614 <=? fcs) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
        * unfold ZD_CONTENTSIZE_ERROR in ER. change (2^64 - 2) with 18446744073709551614 in ER.
          replace (18446744073709551614 <=? fcs) with false in ER by (symmetry; apply Z.leb_gt; lia).
          zs. zs.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            let r1 := getreg 1 in let r5 := getreg 5 in let r6 := getreg 6 in let r7 := getreg 7 in
            let r8 := getreg 8 in let r9 := getreg 9 in let r10 := getreg 10 in let r11 := getreg 11 in
            let r12 := getreg 12 in let r13 := getreg 13 in let r14 := getreg 14 in let r15 := getreg 15 in
            let r16 := getreg 16 in let r17 := getreg 17 in let r18 := getreg 18 in let r19 := getreg 19 in
            let r20 := getreg 20 in let r21 := getreg 21 in let r22 := getreg 22 in let r23 := getreg 23 in
            let r24 := getreg 24 in let r25 := getreg 25 in
            assert (CONT : forall y26, (total + fcs < 18446744073709551616 -> y26 = Z_to_bv 64 (fcs + total)) ->
              evt usegs POST (STpc 0x15250 mm r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 y26)) end.
          { intros y26 HY.
          zs. zs. if_cases KO; zify_cond KO.
          -- (* [comment removed for export] *)
             eapply p_ret; [eapply XI2; eassumption || reflexivity|].
             rewrite ER. change (2^64) with 18446744073709551616.
             replace (18446744073709551616 <=? total + fcs) with true
               by (symmetry; apply Z.leb_le; destruct (Z.lt_ge_cases (total + fcs) 18446744073709551616) as [L|L]; [rewrite Z.mod_small in KO by lia; lia| exact L]).
             apply Z_to_bv_eqm. reflexivity.
          -- assert (NOV : total + fcs < 18446744073709551616).
             { destruct (Z.lt_ge_cases (total + fcs) 18446744073709551616) as [L|L]; [exact L| exfalso].
               assert ((fcs + total) mod 18446744073709551616 = fcs + total - 18446744073709551616)
                 by (symmetry; apply Z.mod_unique with 1; lia). lia. }
             rewrite (HY NOV). change (2^64) with 18446744073709551616 in ER.
             replace (18446744073709551616 <=? total + fcs) with false in ER by (symmetry; apply Z.leb_gt; lia).
             replace (Z_to_bv 64 (fcs + total)) with (Z_to_bv 64 (total + fcs)) by (f_equal; lia).
             (* [comment removed for export] *)
             destruct (rw_cells_forget _ _ _ _ ZFC') as [jz ZJ]. cbn [cells_size csize Nat.add] in ZJ.
             apply (rw_cells_split_CB usegs _ _ [] _ _ _ [24; 24]%nat) in ZJ; [| reflexivity]. cbn [mk_CB_cells app] in ZJ.
             apply (proj1 (rw_cells_app _ _ _ [CB 24 _] _)) in ZJ. destruct ZJ as [FSIC RESTC]. cbn [cells_size csize Nat.add] in RESTC.
             replace (SP + -144 + Z.of_nat 24) with (SP + -120) in RESTC by lia.
             clear ZFC'.
             zs. zs. zs. zs. zs.
             unfold PZD_FINDFSI in FINDFSI.
             call (FINDFSI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SP + -144) (SP + -144) SRC src off sz _ lo);
               [ exact SB1 | exact OK | exact ROFF | exact R5 | lia | lia | exact SRC0 | exact SRCE | exact FSIC | reflexivity | exact ST2
               | lia | lia | clear - SP16; Z.div_mod_to_equations; lia
               | lia | lia | lia | exact MI2 | reflexivity | reflexivity | reflexivity | reflexivity | ].
             rename PC into ST3. rename POST into FSIC'. rename MI0 into MI3.
             change (fsi_csize (find_frame_size_info src off sz)) with (find_frame_compressed_size src off sz) in FSIC'.
             set (fsz := find_frame_compressed_size src off sz) in *.
             lazymatch type of FSIC' with rw_cells _ ?mm _ ?c1 =>
               lazymatch type of RESTC with rw_cells _ _ _ ?c2 =>
                 assert (ZM : rw_cells usegs mm (SP + -144) (c1 ++ c2))
                   by (apply (proj2 (rw_cells_app _ _ _ _ _)); split; [exact FSIC'|]; cbn [cells_size csize Nat.add];
                       replace (SP + -144 + Z.of_nat 24) with (SP + -120) by lia; exact RESTC) end end.
             pose proof (fsi_csize_range src off sz OK ROFF ltac:(lia)) as RFSZ. fold fsz in RFSZ.
             zs. zs. if_cases KE; zify_cond KE.
             ++ eapply p_ret; [eapply XI2; eassumption || reflexivity|].
                rewrite ER. replace (zd_is_error fsz) with true by (symmetry; apply zd_is_error_true_iff; change (2^64) with 18446744073709551616; lia).
                apply Z_to_bv_eqm. reflexivity.
             ++ (* [comment removed for export] *)
                assert (NE : zd_is_error fsz = false) by (apply zd_is_error_false_iff; change (2^64) with 18446744073709551616; lia).
                rewrite NE in ER.
                pose proof (find_frame_compressed_size_ok src OK off sz ltac:(change (2^64) with 18446744073709551616; lia) NE) as RF.
                unfold ZD_SKIPPABLEHEADERSIZE in RF. fold fsz in RF.
                zs. rewrite zb_lxor_ones by lia. zs. zs. fck.
                eapply (ADV _ fsz (total + fcs)); [eapply XI2; eassumption || reflexivity | lia | exact ER | lia]. }
          zs. if_cases KM; zify_cond KM.
          -- apply CONT. intros _. reflexivity.
          -- zs. apply CONT. intros NV. f_equal. lia.
      + (* [comment removed for export] *)
        zs. zs. if_cases KN; zify_cond KN; [exfalso; lia|].
        zs. zs. zs. eapply p_ret; [eapply XI2; eassumption|].
        destruct gfh as [h|v] eqn:G; cbn [fh_retval] in *; [exfalso; lia|].
        rewrite ER. unfold get_frame_content_size. fold gfh. rewrite G.
        unfold ZD_CONTENTSIZE_ERROR. change (2^64 - 2) with 18446744073709551614. cbn [Z.leb Z.compare Pos.compare Pos.compare_cont].
        apply Z_to_bv_eqm. reflexivity.
    - (* [comment removed for export] *)
      unfold is_skippable_magic in ER. rewrite KS, Z.eqb_refl in ER. cbv zeta in ER.
      assert (ERRV : Z_to_bv 64 (-2) = Z_to_bv 64 ZD_CONTENTSIZE_ERROR) by (apply Z_to_bv_eqm; reflexivity).
      zs. zs. if_cases KSZ8; zify_cond KSZ8.
      + (* [comment removed for export] *)
        eapply p_ret; [exact XI|]. rewrite ER. unfold read_skippable_frame_size, ZD_SKIPPABLEHEADERSIZE.
        replace (sz <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
        rewrite zd_is_error_ZERR by (unfold ZE_srcSize_wrong, ZE_maxCode; lia). exact ERRV.
      + zs. zs. fck.
        zlb SB1 OK (off + 5). zlb SB1 OK (off + 4). zlb SB1 OK (off + 6). zlb SB1 OK (off + 7).
        do 6 zs.
        let w := getreg 10 in replace w with (Z_to_bv 64 (le32 src (off + 4)))
          by (f_equal; rewrite le32_bytes; replace (off + 4 + 1) with (off + 5) by lia; replace (off + 4 + 2) with (off + 6) by lia;
              replace (off + 4 + 3) with (off + 7) by lia; lia).
        pose proof (le32_range src OK (off + 4)) as RS. change (2^32) with 4294967296 in RS.
        set (s32 := le32 src (off + 4)) in *.
        assert (RSK : read_skippable_frame_size src off sz =
                      if 4294967287 <? s32 then ZERR ZE_frameParameter_unsupported else if sz <? 8 + s32 then ZERR ZE_srcSize_wrong else 8 + s32).
        { unfold read_skippable_frame_size, ZD_SKIPPABLEHEADERSIZE. replace (sz <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
          cbv zeta. fold s32. pose proof (skippable_wrap_iff s32 ltac:(change (2^32) with 4294967296; lia)) as WI.
          unfold ZD_SKIPPABLEHEADERSIZE in WI. rewrite WI. reflexivity. }
        rewrite RSK in ER.
        zs. if_cases KWR; zify_cond KWR.
        * (* [comment removed for export] *)
          eapply p_ret; [exact XI|]. rewrite ER. replace (4294967287 <? s32) with true by (symmetry; apply Z.ltb_lt; lia).
          rewrite zd_is_error_ZERR by (unfold ZE_frameParameter_unsupported, ZE_maxCode; lia). exact ERRV.
        * replace (4294967287 <? s32) with false in ER by (symmetry; apply Z.ltb_ge; lia).
          zs. zs. zs. if_cases KFIT; zify_cond KFIT.
          -- replace (sz <? 8 + s32) with false in ER by (symmetry; apply Z.ltb_ge; lia).
             replace (zd_is_error (8 + s32)) with false in ER
               by (symmetry; apply zd_is_error_false_iff; change (2^64) with 18446744073709551616; lia).
             replace (Z_to_bv 64 (s32 + 8)) with (Z_to_bv 64 (8 + s32)) by (f_equal; lia).
             zs. if_cases KE; zify_cond KE; [exfalso; lia|].
             zs. rewrite zb_lxor_ones by lia. zs. fck.
             eapply (ADV _ (8 + s32) total); [exact XI | lia | exact ER | exact RT].
          -- zs. zs. if_true. eapply p_ret; [exact XI|]. rewrite ER. replace (sz <? 8 + s32) with true by (symmetry; apply Z.ltb_lt; lia).
             rewrite zd_is_error_ZERR by (unfold ZE_srcSize_wrong, ZE_maxCode; lia). exact ERRV.
  Qed.

  Lemma finddsize_body : evt usegs POST
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 SRC) (Z_to_bv 64 size0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_FINDDSIZE) fc None m (seg_rom usegs)).
  Proof.
    unfold PZD_FINDDSIZE.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ SB) as DB. rewrite length_map in DB.
    pose proof ST as (LO0 & _ & _).
    carve_frame 144%nat ST.
    do 13 zs.
    apply (rw_cells_split_CB usegs _ _ [] _ _ _ [48]%nat) in FR; [| reflexivity].
    cbn [mk_CB_cells app] in FR.
    apply (proj1 (rw_cells_app _ _ _ [CB 48 _] _)) in FR. destruct FR as [ZFC SAVED]. cbn [cells_size csize Nat.add] in SAVED.
    replace (SP + -144 + Z.of_nat 48) with (SP + -96) in * by lia.
    assert (XI : XINV m1).
    { split; [exact SB|]. split; [eexists; split; [exact ZFC| reflexivity]|].
      split; [exact SAVED|]. split; [exact ST|]. split; [exact MU|]. split; [exact WM| exact MI]. }
    assert (ER0 : RES = find_dsize src 0 size0 0) by reflexivity.
    zs. zs. zs. if_cases K5; zify_cond K5.
    - (* [comment removed for export] *)
      do 12 zs.
      replace (Z_to_bv 64 SRC) with (Z_to_bv 64 (SRC + 0)) by (f_equal; lia).
      replace (Z_to_bv 64 (4294967296 + -9)) with KW by reflexivity || idtac.
      eapply (p_loop (Z.to_nat size0) _ 0 size0 0); try eassumption; lia.
    - zs. replace (Z_to_bv 64 SRC) with (Z_to_bv 64 (SRC + 0)) by (f_equal; lia).
      eapply (p_chk _ 0 size0 0); try eassumption; lia.
  Qed.
End FINDDSIZE.

Theorem zd_finddsize_proof : zd_getfh_stmt -> zd_findfsi_stmt -> zd_finddsize_stmt.
Proof.
  intros GETFH FINDFSI. intros until lo. intros SB OK N0 N40 NLEN SRC0 SRCE ST LO RSP SP16 SS MI -> ->.
  change (2^40) with 1099511627776 in N40.
  eapply finddsize_body; eassumption.
Qed.
Print Assumptions zd_finddsize_proof.
