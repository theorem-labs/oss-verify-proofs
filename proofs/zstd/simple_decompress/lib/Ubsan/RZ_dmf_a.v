(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdFrameW ZdWalkKit ZdCellKit ZdDctxRep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_libc_iface RZ_frame_iface RZ_block_iface RZ_dframe_iface.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DMF.
  Variable TBL : tbl_pred.
  Hypothesis TBLL : tbl_laws TBL.
  Hypothesis DBLOCK : zd_dblock_stmt TBL.
  Hypothesis DBEGIN : zd_dbegin_stmt.
  Hypothesis CHECKCONT : zd_checkcont_stmt.
  Hypothesis GETFH : zd_getfh_stmt.
  Hypothesis XXHRESET : zd_xxh_reset_stmt.
  Hypothesis GETCB : zd_getcblock_stmt.
  Hypothesis ERRCODE : zd_errcode_stmt.
  Hypothesis XXHUPD : zd_xxh_update_stmt.
  Hypothesis XXHDIG : zd_xxh_digest_stmt.
  Hypothesis MEMMOVE : zd_memmoveZ_stmt.
  Hypothesis MEMSET : zd_memsetZ_stmt.

  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SP lo DCTX DST CAP SRC : Z) (src : list Z) (size : Z).
  Hypothesis RD0 : 4096 <= DCTX.  Hypothesis RD1 : DCTX + 95992 < 2^47.  Hypothesis RD8 : DCTX mod 8 = 0.
  Hypothesis OK : all_bytes src.
  Hypothesis N0 : 0 <= size.  Hypothesis NLEN : size <= zlen src.  Hypothesis N40 : size < 1099511627776.
  Hypothesis RS0 : 4096 <= SRC.  Hypothesis RS1 : SRC + zlen src < 2^47.
  Hypothesis RC0 : 0 <= CAP.  Hypothesis RC40 : CAP < 1099511627776.
  Hypothesis DNULL : DST = 0 -> CAP = 0.  Hypothesis DNN : DST <> 0 -> 4096 <= DST.  Hypothesis RDST : DST + CAP < 2^47.
  Hypothesis RLO : 4096 <= lo.  Hypothesis LO : lo <= SP - 2368.  Hypothesis RSP : SP < 2^47.
  Hypothesis S_DC : DCTX + 95992 <= lo \/ SP <= DCTX.
  Hypothesis S_DS : DST + CAP <= lo \/ SP <= DST.
  Hypothesis S_SR : SRC + zlen src <= lo \/ SP <= SRC.
  Hypothesis S_GT : 0x36e40 + 16 <= lo \/ SP <= 0x36e40.
  Hypothesis D_DC : DST + CAP <= DCTX \/ DCTX + 95992 <= DST.
  Hypothesis D_SR : DST + CAP <= SRC \/ SRC + zlen src <= DST.
  Hypothesis SR_DC : SRC + zlen src <= DCTX \/ DCTX + 95992 <= SRC.
  Hypothesis GT_DC : 0x36e40 + 16 <= DCTX \/ DCTX + 95992 <= 0x36e40.
  Hypothesis GT_DS : 0x36e40 + 16 <= DST \/ DST + CAP <= 0x36e40.

  Notation W := [(DCTX, DCTX + 95992); (DST, DST + CAP); (SP - 2368, SP)].
  Notation POST := (zd_dmf_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP DCTX DST CAP src size lo m).

  (* [comment removed for export] *)
  Notation STpc pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -272)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition frl_cells (sl0 sl1 sl2 sl3 : word) : list cell :=
    [C8 sl0; C8 sl1; C8 sl2; C8 (Z_to_bv 64 10600); C8 (Z_to_bv 64 (DCTX + 95984)); C8 (Z_to_bv 64 DST);
     C8 (Z_to_bv 64 (DCTX + 30008)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 25481893);
     C8 (Z_to_bv 64 4294967287); C8 (Z_to_bv 64 0); C8 sl3].
  Definition frh_cells (jt : list byte) : list cell :=
    [CB 52 jt; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition ENV (m1 : fmem) : Prop :=
    rw_cells usegs m1 0x36e40 [C8 wz0; C8 wz0]
    /\ bytes_at usegs m1 SRC (map (Z_to_bv 8) src)
    /\ stk usegs m1 DST (DST + CAP)
    /\ (exists csb, rw_cells usegs m1 (SP + -168) csb /\ cells_size csb = 12%nat)
    /\ (exists jt, rw_cells usegs m1 (SP + -156) (frh_cells jt))
    /\ stk usegs m1 lo (SP + -272)
    /\ munch W m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1.

  (* [comment removed for export] *)
  Lemma L_ret : forall m1 r sl0 sl1 sl2 sl3
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    ENV m1 -> rw_cells usegs m1 (SP + -272) (frl_cells sl0 sl1 sl2 sl3) -> dctx_any m1 DCTX ->
    0 <= r < 2^64 -> (zd_is_error r = false -> decompress_ok src size CAP r) ->
    evt usegs POST (STpc 0x15b20 m1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 r) x28 x29 x30 x31).
  Proof.
    intros m1 r sl0 sl1 sl2 sl3 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
           (GOT & SB1 & DSK & (csb & BPC & BSZ) & (jt & FRH) & ST1 & MU1 & WM1 & MI1) FRL DA RR RM.
    unfold frh_cells in FRH. unfold frl_cells in FRL.
    do 14 zs.
    assert (FR : rw_cells usegs m1 (SP + -272) ([C8 sl0; C8 sl1; C8 sl2; C8 (Z_to_bv 64 10600); C8 (Z_to_bv 64 (DCTX + 95984)); C8 (Z_to_bv 64 DST);
         C8 (Z_to_bv 64 (DCTX + 30008)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 25481893);
         C8 (Z_to_bv 64 4294967287); C8 (Z_to_bv 64 0); C8 sl3] ++ csb ++ [CB 52 jt; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact FRL|]. cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app _ _ _ _ _)). split; [replace (SP + -272 + Z.of_nat 104) with (SP + -168) by lia; exact BPC|].
      rewrite BSZ. replace (SP + -272 + Z.of_nat 104 + Z.of_nat 12) with (SP + -156) by lia. exact FRH. }
    eapply stk_release in FR; [| exact ST1 | lia].
    rewrite !cells_size_app, BSZ in FR. cbn [cells_size csize Nat.add] in FR.
    replace (SP + -272 + Z.of_nat 272) with SP in FR by lia.
    zs. zs.
    apply evt_done. unfold zd_dmf_post.
    do 14 eexists. exists m1, r. split; [reflexivity|].
    split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact FR|]. split; [exact DA|]. split; [exact DSK|]. split; [exact RR| exact RM].
  Qed.

  (* [comment removed for export] *)
  Lemma L_exit : forall m1 sz tot sl0 sl1 sl2 sl3
      (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    ENV m1 -> rw_cells usegs m1 (SP + -272) (frl_cells sl0 sl1 sl2 sl3) -> dctx_any m1 DCTX ->
    0 <= sz < 2^64 -> 0 <= tot <= CAP -> (sz = 0 -> decompress_ok src size CAP tot) ->
    evt usegs POST (STpc 0x15af4 m1 x1 x5 x6 x7 x8 (Z_to_bv 64 (DST + tot)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sz)
                         x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros m1 sz tot sl0 sl1 sl2 sl3 x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
           EN FRL DA RSZ RT ACC.
    pose proof FRL as FRL'. unfold frl_cells in FRL'.
    zs. if_cases K; zify_cond K.
    - zs. zs. replace (DST + tot - DST) with tot by lia. zs.
      eapply (L_ret m1 tot); try eassumption; [lia | intros _; apply ACC; lia].
    - zs. zs. replace (Z_to_bv 64 (-72)) with (Z_to_bv 64 (ZERR ZE_srcSize_wrong)) by (apply Z_to_bv_eqm; reflexivity).
      eapply (L_ret m1 (ZERR ZE_srcSize_wrong)); try eassumption.
      + unfold ZERR, ZE_srcSize_wrong. lia.
      + intros E. rewrite zd_is_error_ZERR in E by (unfold ZE_srcSize_wrong, ZE_maxCode; lia). discriminate E.
  Qed.

  (* [comment removed for export] *)
  Definition A_INV (m1 : fmem) (off sz tot mt1 : Z) : Prop :=
    ENV m1 /\ (exists sl0 sl1 sl2 sl3, rw_cells usegs m1 (SP + -272) (frl_cells sl0 sl1 sl2 sl3)) /\ dctx_any m1 DCTX /\
    0 <= off /\ off + sz <= size /\ 0 <= sz /\ 0 <= tot <= CAP /\ (mt1 = 0 \/ mt1 = 1) /\
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r).
  Notation ASt mm off sz tot mt1 x1 x5 x8 x11 x12 x13 x14 x26 x27 x28 x29 x30 x31 :=
    (STpc 0x155a8 mm x1 x5 (Z_to_bv 64 (-120)) (Z_to_bv 64 25481893) x8 (Z_to_bv 64 (DST + tot)) (Z_to_bv 64 5) x11 x12 x13 x14
          (Z_to_bv 64 5) (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 sz) (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) (Z_to_bv 64 0)
          (Z_to_bv 64 mt1) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 4294967287) (Z_to_bv 64 (DCTX + 29928)) x26 x27 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma L_result : forall m1 off sz tot mt1 res sl0 sl1 sl2
      (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x26 x28 x29 x30 x31 : word),
    ENV m1 -> rw_cells usegs m1 (SP + -272) (frl_cells sl0 sl1 sl2 (Z_to_bv 64 mt1)) -> dctx_any m1 DCTX ->
    0 <= off -> off + sz <= size -> 0 <= tot <= CAP -> (mt1 = 0 \/ mt1 = 1) -> 0 <= res < 2^64 ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    (zd_is_error res = false -> exists off' sz',
        x18 = Z_to_bv 64 sz' /\ x23 = Z_to_bv 64 (SRC + off') /\ res <= CAP - tot /\ off <= off' /\ off' + sz' <= size /\ 0 <= sz' < sz /\
        (forall r, dmulti src off' sz' (CAP - tot - res) (tot + res) r -> dmulti src off sz (CAP - tot) tot r)) ->
    (forall m' off' sz' tot' (y1 y5 y8 y11 y12 y13 y14 y26 y27 y28 y29 y30 y31 : word), sz' < sz -> A_INV m' off' sz' tot' 1 ->
        evt usegs POST (ASt m' off' sz' tot' 1 y1 y5 y8 y11 y12 y13 y14 y26 y27 y28 y29 y30 y31)) ->
    evt usegs POST (STpc 0x15764 m1 x1 x5 x6 x7 x8 (Z_to_bv 64 (DST + tot)) x10 x11 x12 x13 x14 x15 x16 x17
                         x18 (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) x21 x22 x23 (Z_to_bv 64 res) (Z_to_bv 64 (DCTX + 29928))
                         x26 (Z_to_bv 64 (-72)) x28 x29 x30 x31).
  Proof.
    intros m1 off sz tot mt1 res sl0 sl1 sl2 x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x26 x28 x29 x30 x31
           EN FRL DA ROFF RSZ RT RMT RRES ACC SUCC KA.
    pose proof EN as (GOT & SB1 & DSK & (csb & BPC & BSZ) & (jt & FRH) & ST1 & MU1 & WM1 & MI1).
    pose proof DA as (llt & mlt & oft & huf & pde & pfx & vst & dend & expd & fp & pcs & dsz & bt & stg & le & fe & xs & ws & jhb & ovd & dcb & dce & trace &
                      PT & H1 & FP & H3 & XS & [H5C H5L] & H5OK & TX & OWN).
    pose proof H5OK as (K_FMT & _).
    lazymatch goal with |- evt _ ?Q _ => set (Q0 := Q) end.
    pose proof FRL as FRL'. unfold frl_cells in FRL'.
    zs. zs.
    unfold PZD_ERRCODE in ERRCODE.
    change (2^64) with 18446744073709551616 in RRES.
    call_pure (ERRCODE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res).
    1: lia. 1: reflexivity.
    assert (RCODE : 0 <= zd_error_code res < 120).
    { unfold zd_error_code. destruct (zd_is_error res) eqn:E; [| lia]. apply zd_is_error_true_iff in E. change (2^64) with 18446744073709551616 in *. lia. }
    zs. zs. zs. zs. zs. if_cases KP; zify_cond KP.
    - replace (Z_to_bv 64 (-72)) with (Z_to_bv 64 (ZERR ZE_srcSize_wrong)) by (apply Z_to_bv_eqm; reflexivity).
      eapply (L_ret m1 (ZERR ZE_srcSize_wrong) sl0 sl1 sl2 (Z_to_bv 64 mt1)); try eassumption.
      + unfold ZERR, ZE_srcSize_wrong. lia.
      + intros E. rewrite zd_is_error_ZERR in E by (unfold ZE_srcSize_wrong, ZE_maxCode; lia). discriminate E.
    - zs. zs. if_cases KE; zify_cond KE.
      + (* [comment removed for export] *)
        zs. zs. eapply (L_ret m1 res sl0 sl1 sl2 (Z_to_bv 64 mt1)); try eassumption; try lia.
        intros E. apply zd_is_error_false_iff in E. change (2^64) with 18446744073709551616 in E. lia.
      + (* [comment removed for export] *)
        assert (NE : zd_is_error res = false) by (apply zd_is_error_false_iff; change (2^64) with 18446744073709551616; lia).
        destruct (SUCC NE) as (off' & sz' & -> & -> & RRC & RO1 & RO2 & RSZ' & STEP).
        h5_open ws H5L. unfold wz0 in *. subst b0.
        do 9 zs. zs. rewrite sx32w_small by lia. zs. zs. if_false. zs. zs. if_true.
        assert (DA2 : dctx_any m1 DCTX).
        { match type of H5OK with h5_frame_ok ?l => exists llt, mlt, oft, huf, pde, pfx, vst, dend, expd, fp, pcs, dsz, bt, stg, le, fe, xs, l, jhb, ovd, dcb, dce, trace end.
          split; [exact PT|]. split; [exact H1|]. split; [exact FP|]. split; [exact H3|]. split; [exact XS|].
          split; [split; [exact H5C| reflexivity]|]. split; [exact H5OK|]. split; [exact TX| exact OWN]. }
        assert (ACC2 : forall r, dmulti src off' sz' (CAP - (tot + res)) (tot + res) r -> decompress_ok src size CAP r).
        { intros r D. apply ACC. apply STEP. replace (CAP - tot - res) with (CAP - (tot + res)) by lia. exact D. }
        replace (DST + tot + res) with (DST + (tot + res)) by lia. replace (CAP - tot - res) with (CAP - (tot + res)) by lia.
        eapply (KA m1 off' sz' (tot + res)); [lia|].
        split; [exact EN|]. split; [do 4 eexists; exact FRL|]. split; [exact DA2|].
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [right; reflexivity| exact ACC2].
  Qed.
End DMF.
