(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdFrameW ZdWalkKit ZdCellKit ZdDctxRep ZdSepKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_libc_iface RZ_frame_iface RZ_block_iface RZ_dframe_iface RZ_dmf_a RZ_dmf_b.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import frame_kit.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac transport_chunks segs m a bs ::= zd_transport_chunks segs m a bs.

(* [comment removed for export] *)
Lemma dmf_tbl_did_rd : forall m k, mem_inv usegs m -> 0 <= k < 4 ->
  ov_read_bytes usegs m (Z_to_bv 64 (67392 + k * 8)) 8 = Some (le8 (Z_to_bv 64 (did_fieldSize k))).
Proof.
  intros m k MI Hk. assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
  destruct C as [-> | [-> | [-> | ->]]]; (apply img_rd8; [exact MI | vm_compute; reflexivity | lia | lia]).
Qed.
Lemma dmf_tbl_fcs_rd : forall m k, mem_inv usegs m -> 0 <= k < 4 ->
  ov_read_bytes usegs m (Z_to_bv 64 (67424 + k * 8)) 8 = Some (le8 (Z_to_bv 64 (fcs_fieldSize k))).
Proof.
  intros m k MI Hk. assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
  destruct C as [-> | [-> | [-> | ->]]]; (apply img_rd8; [exact MI | vm_compute; reflexivity | lia | lia]).
Qed.

Section DMFD.
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
  Hypothesis DNULL : zimp (DST = 0) (CAP = 0).  Hypothesis DNN : zimp (DST <> 0) (4096 <= DST).  Hypothesis RDST : DST + CAP < 2^47.
  Hypothesis RLO : 4096 <= lo.  Hypothesis LO : lo <= SP - 2368.  Hypothesis RSP : SP < 2^47.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis S_DC : zsep DCTX (DCTX + 95992) lo SP.
  Hypothesis S_DS : zsep DST (DST + CAP) lo SP.
  Hypothesis S_SR : zsep SRC (SRC + zlen src) lo SP.
  Hypothesis S_GT : zsep 0x36e40 (0x36e40 + 16) lo SP.
  Hypothesis D_DC : zsep DST (DST + CAP) DCTX (DCTX + 95992).
  Hypothesis D_SR : zsep DST (DST + CAP) SRC (SRC + zlen src).
  Hypothesis SR_DC : zsep SRC (SRC + zlen src) DCTX (DCTX + 95992).
  Hypothesis GT_DC : zsep 0x36e40 (0x36e40 + 16) DCTX (DCTX + 95992).
  Hypothesis GT_DS : zsep 0x36e40 (0x36e40 + 16) DST (DST + CAP).

  Notation W := [(DCTX, DCTX + 95992); (DST, DST + CAP); (SP - 2368, SP)].
  Notation POST := (zd_dmf_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP DCTX DST CAP src size lo m).

  (* [comment removed for export] *)
  Notation STpc pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -272)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Notation frl_cells := (RZ_dmf_a.frl_cells DCTX DST).
  Notation frh_cells := (RZ_dmf_a.frh_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation ENV := (RZ_dmf_a.ENV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SP lo DCTX DST CAP SRC src).
  Notation A_INV := (RZ_dmf_a.A_INV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SP lo DCTX DST CAP SRC src size).
  Notation ASt mm off sz tot mt1 x1 x5 x8 x11 x12 x13 x14 x26 x27 x28 x29 x30 x31 :=
    (STpc 87464 mm x1 x5 (Z_to_bv 64 (-120)) (Z_to_bv 64 25481893) x8 (Z_to_bv 64 (DST + tot)) (Z_to_bv 64 5) x11 x12 x13 x14
          (Z_to_bv 64 5) (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 sz) (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) (Z_to_bv 64 0)
          (Z_to_bv 64 mt1) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 4294967287) (Z_to_bv 64 (DCTX + 29928)) x26 x27 x28 x29 x30 x31).


  Notation B_DCTX := (RZ_dmf_b.B_DCTX TBL DCTX).
  Notation FRAME_OK := (RZ_dmf_b.FRAME_OK CAP src size).
  Notation KA_T := (RZ_dmf_b.KA_T ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SP lo DCTX DST CAP SRC src size).
  Notation FRLB mm mt1 sl0 sl1 sl2 := (rw_cells usegs mm (SP + -272) (frl_cells sl0 sl1 sl2 (Z_to_bv 64 mt1))).

  Notation B_HEAD := (RZ_dmf_b.B_HEAD TBL ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SP lo DCTX DST CAP SRC src size).

  (* [comment removed for export] *)
  Hypothesis L_ret : forall m1 r sl0 sl1 sl2 sl3
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    ENV m1 -> rw_cells usegs m1 (SP + -272) (frl_cells sl0 sl1 sl2 sl3) -> dctx_any m1 DCTX ->
    0 <= r < 2^64 -> (zd_is_error r = false -> decompress_ok src size CAP r) ->
    evt usegs POST (STpc 88864 m1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 r) x28 x29 x30 x31).

  Hypothesis L_exit : forall m1 sz tot sl0 sl1 sl2 sl3
      (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    ENV m1 -> rw_cells usegs m1 (SP + -272) (frl_cells sl0 sl1 sl2 sl3) -> dctx_any m1 DCTX ->
    0 <= sz < 2^64 -> 0 <= tot <= CAP -> (sz = 0 -> decompress_ok src size CAP tot) ->
    evt usegs POST (STpc 88820 m1 x1 x5 x6 x7 x8 (Z_to_bv 64 (DST + tot)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sz)
                         x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).

  Hypothesis HRES : forall m1 off sz tot mt1 res sl0 sl1 sl2
      (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x26 x28 x29 x30 x31 : word),
    ENV m1 -> rw_cells usegs m1 (SP + -272) (frl_cells sl0 sl1 sl2 (Z_to_bv 64 mt1)) -> dctx_any m1 DCTX ->
    0 <= off -> off + sz <= size -> 0 <= tot <= CAP -> (mt1 = 0 \/ mt1 = 1) -> 0 <= res < 2^64 ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    (zd_is_error res = false -> exists off' sz',
        x18 = Z_to_bv 64 sz' /\ x23 = Z_to_bv 64 (SRC + off') /\ res <= CAP - tot /\ off <= off' /\ off' + sz' <= size /\ 0 <= sz' < sz /\
        (forall r, dmulti src off' sz' (CAP - tot - res) (tot + res) r -> dmulti src off sz (CAP - tot) tot r)) ->
    (forall m' off' sz' tot' (y1 y5 y8 y11 y12 y13 y14 y26 y27 y28 y29 y30 y31 : word), sz' < sz -> A_INV m' off' sz' tot' 1 ->
        evt usegs POST (ASt m' off' sz' tot' 1 y1 y5 y8 y11 y12 y13 y14 y26 y27 y28 y29 y30 y31)) ->
    evt usegs POST (STpc 87908 m1 x1 x5 x6 x7 x8 (Z_to_bv 64 (DST + tot)) x10 x11 x12 x13 x14 x15 x16 x17
                         x18 (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) x21 x22 x23 (Z_to_bv 64 res) (Z_to_bv 64 (DCTX + 29928))
                         x26 (Z_to_bv 64 (-72)) x28 x29 x30 x31).

  Hypothesis L_errx : forall mm off sz tot mt1 res sl0 sl1 sl2
      (y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y18 y21 y22 y23 y26 y28 y29 y30 y31 : word),
    ENV mm -> FRLB mm mt1 sl0 sl1 sl2 -> dctx_any mm DCTX ->
    0 <= off -> off + sz <= size -> 0 <= tot <= CAP -> (mt1 = 0 \/ mt1 = 1) ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    zd_is_error res = true -> 0 <= res < 2^64 -> KA_T sz ->
    evt usegs POST (STpc 87908 mm y1 y5 y6 y7 y8 (Z_to_bv 64 (DST + tot)) y10 y11 y12 y13 y14 y15 y16 y17 y18
                       (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) y21 y22 y23 (Z_to_bv 64 res) (Z_to_bv 64 (DCTX + 29928))
                       y26 (Z_to_bv 64 (-72)) y28 y29 y30 y31).

  Hypothesis L_errx2 : forall mm off sz tot mt1 sl0 sl1 sl2
      (y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y18 y21 y22 y23 y24 y26 y28 y29 y30 y31 : word),
    ENV mm -> FRLB mm mt1 sl0 sl1 sl2 -> dctx_any mm DCTX ->
    0 <= off -> off + sz <= size -> 0 <= tot <= CAP -> (mt1 = 0 \/ mt1 = 1) ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    KA_T sz ->
    evt usegs POST (STpc 87904 mm y1 y5 y6 y7 y8 (Z_to_bv 64 (DST + tot)) y10 y11 y12 y13 y14 y15 y16 y17 y18
                       (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) y21 y22 y23 y24 (Z_to_bv 64 (DCTX + 29928))
                       y26 (Z_to_bv 64 (-72)) y28 y29 y30 y31).

  Hypothesis L_blocks : forall (n : nat) off sz tot mt1 hsz h PFX ipb rem o,
    rem <= Z.of_nat n ->
    FRAME_OK off sz tot mt1 hsz h ->
    ((PFX = 0 /\ CAP - tot = 0) \/ PFX = DST + tot) ->
    off + hsz <= ipb -> ipb + rem <= off + sz -> 0 <= o <= CAP - tot ->
    (forall ip' rem' o', dblocks src (CAP - tot) ipb rem o ip' rem' o' -> dblocks src (CAP - tot) (off + hsz) (sz - hsz) 0 ip' rem' o') ->
    KA_T sz ->
    B_HEAD off sz tot mt1 h PFX ipb rem o.

  Lemma L_pcs : forall mm off sz tot mt1 hsz h PFX (llt mlt oft huf pde expd pcs dsz bt stg le fe : word) xs ws sl0 sl1 sl2
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y26 y28 y29 y30 y31 : word),
    ENV mm -> FRLB mm mt1 sl0 sl1 sl2 -> B_DCTX mm h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
    FRAME_OK off sz tot mt1 hsz h -> 5 <= hsz -> ((PFX = 0 /\ CAP - tot = 0) \/ PFX = DST + tot) -> KA_T sz ->
    evt usegs POST (STpc 88076 mm y1 y5 y6 y7 (Z_to_bv 64 (DST + CAP)) (Z_to_bv 64 (DST + tot)) y10 y11 y12 y13 y14 y15 y16 y17
                       (Z_to_bv 64 sz) (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) y21 y22 (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 hsz)
                       (Z_to_bv 64 (DCTX + 29928)) y26 (Z_to_bv 64 (-72)) y28 y29 y30 y31).
  Proof.
    intros mm off sz tot mt1 hsz h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws sl0 sl1 sl2
           y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y26 y28 y29 y30 y31 EN FRL BD FOK H5Z WIN KA.
    pose proof FOK as (ROFF & RSZ & RT & RMT & ACC & K9 & EHSZ & KS & NSK & GFH).
    pose proof EN as (GOT & SB1 & DSK & (csb & BPC & BSZ) & (jt & FRH) & ST1 & MU1 & WM1 & MI1).
    pose proof DSK as (DST0 & _ & _).
    assert (LENP : zlen (map (Z_to_bv 8) src) = zlen src) by (rewrite length_map; reflexivity).
    pose proof (bytes_at_bound _ _ _ _ SB1) as DB. rewrite length_map in DB.
    destruct BD as (PT & H1 & FPC & H3 & [XSC XSSZ] & XSI & [H5C H5L] & H5OK & KV & KI & TXe & [OWE OWX] & TB).
    pose proof H5OK as (_ & _ & _ & K_MBS & _).
    h5_open ws H5L. unfold wz0 in K_MBS. subst b22.
    assert (MU2 : munch [(DCTX + 29976, DCTX + 29984); (SP + -272, SP)] mm mm) by apply munch_refl.
    assert (WM2 : wmono usegs mm mm) by apply wmono_refl.
    assert (MI0 : id (mem_inv usegs mm)) by exact MI1.
    destruct TXe as (jhb & ovd & dcb & dce & trace & TX). unfold dctx_ptrs in PT. unfold dctx_h1 in H1. unfold dctx_tx in TX.
    unfold dctx_h3 in H3. unfold zfh_cells in FPC. unfold RZ_dmf_a.frl_cells in FRL. unfold RZ_dmf_a.frh_cells in FRH. clear EN.
    pose proof S_DC as S_DC'. pose proof S_SR as S_SR'. pose proof SR_DC as SR_DC'. unfold zsep in S_DC', S_SR', SR_DC'.
    zs. zs. zs. zs.
    zs. if_cases UK; zify_cond UK; rewrite ?zb_lxor_ones in UK by lia; [exfalso; lia | clear UK].

    zs. rewrite sx32w_small by lia. zs. if_true.
    zs. replace (SRC + off + hsz) with (SRC + (off + hsz)) by lia.
    zs. zs. zs. zs. zs.
    assert (BPC' : id (rw_cells usegs _ (SP + -168) csb)) by exact BPC. clear BPC.
    unfold PZD_GETCBLOCK in GETCB.
    callk (GETCB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SRC (SP + -168) src (off + hsz) (sz - hsz) csb);
      [ exact SB1 | exact OK | lia | lia | lia | lia | exact BPC' | exact BSZ | lia | lia | assumption | reflexivity | reflexivity | reflexivity | ].

    clear BPC'.
    rename PC into BPC2. rename PC0 into BSZ2. rename POST into BPP.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m3 _) =>
      eassert (BD3 : B_DCTX m3 h PFX llt mlt oft huf pde expd _ dsz bt stg le fe xs [b; b0; b1; b2; b3; b4; b5; b6; b7; b8; b9; b10; b11; b12; b13; b14; b15; b16; b17; b18; b19; b20; b21; Z_to_bv 64 0; b23; b24; b25; b26; b27; b28; b29; b30; b31; b32; b33; b34; b35; b36; b37; b38; b39; b40; b41; b42])
    end.
    { split; [exact PT|]. split; [exact H1|]. split; [exact FPC|]. split; [exact H3|]. split; [split; [exact XSC| exact XSSZ]|].
      split; [exact XSI|]. split; [split; [exact H5C| reflexivity]|]. split; [exact H5OK|]. split; [exact KV|]. split; [exact KI|].
      split; [exists jhb, ovd, dcb, dce, trace; exact TX|]. split; [split; [exact OWE| exact OWX]|].
      eapply (tbl_frame TBL TBLL); [exact TB | exact MU2 | exact MI0 | assumption | intros q Hq; cbn [outside]; repeat split; try lia; exact I]. }
    clear PT H1 FPC H3 XSC XSI H5C KV KI TX OWE OWX TB MU2 WM2 MI0.
    pose proof (RZ_dmf_b.B_DCTX_any TBL DCTX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BD3) as DA3.
    assert (RRET : 0 <= cblock_ret (get_cblock_size src (off + hsz) (sz - hsz)) < 18446744073709551616).
    { clear - OK. unfold get_cblock_size.
      destruct (sz - hsz <? ZD_blockHeaderSize); cbn [cblock_ret].
      - unfold ZERR, ZE_srcSize_wrong. change (2^64) with 18446744073709551616. lia.
      - pose proof (cblock_props_range (le24 src (off + hsz)) (le24_range src OK (off + hsz))) as (_ & _ & RO2). change (2^21) with 2097152 in RO2.
        unfold bt_rle, bt_reserved, ZERR, ZE_corruption_detected. change (2^64) with 18446744073709551616.
        destruct (_ =? 1); [lia|]. destruct (_ =? 3); lia. }
    zs. zs. zs. if_cases KE; zify_cond KE.
    - (* [comment removed for export] *)
      zs. zs.
      eapply (L_errx _ off sz tot mt1 (cblock_ret (get_cblock_size src (off + hsz) (sz - hsz))) sl0 sl1 sl2); try eassumption.
      + split; [exact GOT|]; split; [exact SB1|]; split; [exact DSK|]; split; [eexists; split; [exact BPC2| exact BSZ2]|]; split; [eexists; exact FRH|]; split; [exact ST1|]; split; [exact MU1|]; split; [exact WM1| assumption].
      + apply zd_is_error_true_iff. change (2^64) with 18446744073709551616. lia.
    - (* [comment removed for export] *)
      destruct (get_cblock_size src (off + hsz) (sz - hsz)) as [[cbs bp]|] eqn:GCB; cbn [cblock_ret] in *;
        [| exfalso; unfold ZERR, ZE_srcSize_wrong in KE; change (2^64) with 18446744073709551616 in KE; lia].
      rewrite (BPP cbs bp eq_refl) in BPC2.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m3 _) =>
        assert (MU3 : munch [(SP + -272, SP)] m3 m3) by apply munch_refl;
        assert (WM3 : wmono usegs m3 m3) by apply wmono_refl;
        assert (MI3 : id (mem_inv usegs m3)) by assumption
      end.
      zs.
      lazymatch type of MU3 with munch _ ?m0 ?m4 =>
        assert (BD4 : B_DCTX m4 h PFX llt mlt oft huf pde expd _ dsz bt stg le fe xs _)
          by (eapply (RZ_dmf_b.B_DCTX_transport TBL TBLL SP lo DCTX DST CAP SRC src size RD0 N0 NLEN RS0 RC0 DNULL DNN RLO LO S_DC S_DS S_SR S_GT D_DC D_SR SR_DC GT_DC GT_DS [(SP + -272, SP)] m0 m4); [exact BD3 | exact MU3 | exact WM3 | exact MI3 | assumption | dj_solve])
      end.
      assert (EN4 : ENV _) by (split; [exact GOT|]; split; [exact SB1|]; split; [exact DSK|]; split; [eexists; split; [exact BPC2| reflexivity]|]; split; [eexists; exact FRH|]; split; [exact ST1|]; split; [exact MU1|]; split; [exact WM1| assumption]).
      assert (NEC : zd_is_error cbs = false) by (apply zd_is_error_false_iff; change (2^64) with 18446744073709551616; lia).
      pose proof (L_blocks (Z.to_nat (sz - hsz)) off sz tot mt1 hsz h PFX (off + hsz) (sz - hsz) 0) as HB.
      unfold RZ_dmf_b.B_HEAD in HB. replace (DST + tot + 0) with (DST + tot) in HB by lia.
      eapply HB; try eassumption; try lia.
      intros ip' rem' o' D. exact D.
  Qed.

  (* [comment removed for export] *)
  Lemma L_frame : forall m1 off sz tot mt1
      (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x24 x26 x27 x28 x29 x30 x31 : word),
    A_INV m1 off sz tot mt1 ->
    (4 <= sz -> is_skippable_magic (le32 src off) = false) ->
    KA_T sz ->
    evt usegs POST (STpc 87440 m1 x1 x5 x6 x7 x8 (Z_to_bv 64 (DST + tot)) x10 x11 x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 sz) (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) (Z_to_bv 64 0) (Z_to_bv 64 mt1)
                         (Z_to_bv 64 (SRC + off)) x24 (Z_to_bv 64 (DCTX + 29928)) x26 x27 x28 x29 x30 x31).
  Proof.
    intros m1 off sz tot mt1 x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x24 x26 x27 x28 x29 x30 x31
           (EN & (sl0 & sl1 & sl2 & sl3 & FRL) & DA & ROFF & RSZ & RSZ0 & RT & RMT & ACC) NSK KA.
    pose proof EN as (GOT & SB1 & DSK & (csb & BPC & BSZ) & (jt & FRH) & ST1 & MU1 & WM1 & MI1).
    pose proof DSK as (DST0 & _ & _).
    destruct DA as (llt & mlt & oft & huf & pde & pfx & vst & dend & expd & fp & pcs & dsz & bt & stg & le & fe & xs & ws & jhb & ovd & dcb & dce & trace &
                    PT & H1 & [FPC FPSZ] & H3 & [XSC XSSZ] & H5 & H5OK & TX & OWN).
    unfold RZ_dmf_a.frl_cells in FRL. unfold RZ_dmf_a.frh_cells in FRH.
    pose proof H5 as [_ WSL]. pose proof H5OK as (K_FMT & K_FIC & K_RMD & K_MBS & _).
    h5_open ws WSL. unfold wz0 in K_FMT, K_FIC, K_RMD, K_MBS. subst b0 b1 b20 b22.
    assert (LENP : zlen (map (Z_to_bv 8) src) = zlen src) by (rewrite length_map; reflexivity).
    pose proof (bytes_at_bound _ _ _ _ SB1) as DB. rewrite length_map in DB.
    zs. zs. zs. if_true. zs. zs. zs.
    assert (PT' : id (dctx_ptrs usegs m1 DCTX llt mlt oft huf)) by exact PT. clear PT.
    assert (H1' : id (dctx_h1 usegs m1 DCTX pde pfx vst dend expd)) by exact H1. clear H1.
    assert (H3' : id (dctx_h3 usegs m1 DCTX pcs dsz bt stg le fe)) by exact H3. clear H3.
    assert (H5' : id (dctx_h5 usegs m1 DCTX _)) by exact H5. clear H5.
    assert (TX' : id (dctx_tx usegs m1 DCTX jhb ovd dcb dce trace)) by exact TX. clear TX.
    assert (OWN' : id (dctx_owned usegs m1 DCTX)) by exact OWN. clear OWN.
    assert (ST1' : id (stk usegs m1 lo (SP + -272))) by exact ST1. clear ST1.
    assert (SUBFP : sub_fp [(DCTX, DCTX + 32); (DCTX + 10296, DCTX + 10300); (DCTX + 26684, DCTX + 26696); (DCTX + 29888, DCTX + 29928);
                            (DCTX + 29976, DCTX + 30008); (DCTX + 30096, DCTX + 30372); (DCTX + 95940, DCTX + 95992); (SP + -272 - 64, SP + -272)] W).
    { clear. unfold sub_fp. cbn [outside]. intros x Hx. repeat split; try lia; exact I. }
    clear EN.
    unfold PZD_DBEGIN in DBEGIN.
    callk (DBEGIN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SP + -272) DCTX llt mlt oft huf pde pfx vst dend expd pcs dsz bt stg le fe _ jhb ovd dcb dce trace wz0 lo);
      [ exact PT' | exact H1' | exact H3' | exact H5' | exact H5OK | exact TX' | exact OWN' | exact GOT | exact RD0 | exact RD1 | exact RD8
      | exact ST1' | lia | lia
      | generalize S_DC; unfold zsep; lia | generalize S_GT; unfold zsep; lia | exact GT_DC
      | exact MI1 | reflexivity | reflexivity | reflexivity | ].
    clear SUBFP PT' H1' H3' H5' TX' OWN' ST1'.
    rename PC into ST2. rename PC0 into PT2. rename PC2 into H32. rename PC3 into H52. rename PC4 into TX2. rename PC5 into OWN2.
    rename PC6 into BHUF. rename POST into BREP. rename MI into MI2.
    unfold dctx_ptrs in PT2. unfold dctx_h3 in H32. unfold dctx_tx in TX2. destruct OWN2 as [OWE OWX]. destruct H52 as [H5C H5L].
    cbv beta iota delta [h5_cells h5_sizes mk_wcells wupd H5_isFrameDecompression H5_dictID] in H5C. clear H5L.
    unfold wz0 in H5C, H32, TX2, PC1.
    unfold dctx_h1 in PC1.
    zs. if_false.
    zs. zs. zs. zs. zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m2 end.
    assert (H1' : id (dctx_h1 usegs m2 DCTX wz0 wz0 wz0 wz0 (Z_to_bv 64 5))) by exact PC1. clear PC1.
    assert (SUBFP : sub_fp [(DCTX + 29888, DCTX + 29920)] W).
    { clear. unfold sub_fp. cbn [outside]. intros x Hx. repeat split; try lia; exact I. }
    unfold PZD_CHECKCONT in CHECKCONT.
    callk (CHECKCONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DCTX (DST + tot) (CAP - tot) (Z_to_bv 64 5));
      [ exact H1' | lia | exact RD8 | lia | lia | lia | exact MI2 | reflexivity | reflexivity | reflexivity | ].
    clear SUBFP H1'.
    rename MI into MI3.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
    set (PFX := if (DST + tot =? 0) || (CAP - tot =? 0) then 0 else DST + tot).
    assert (H1x : rw_cells usegs m3 (DCTX + 29888) [C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 5)]).
    { unfold PFX. unfold dctx_h1, wz0 in POST. destruct ((DST + tot =? 0) || (CAP - tot =? 0)); exact POST. }
    assert (WIN : (PFX = 0 /\ CAP - tot = 0) \/ PFX = DST + tot).
    { unfold PFX. destruct (Z.eqb_spec (DST + tot) 0); destruct (Z.eqb_spec (CAP - tot) 0); cbn [orb]; lia. }
    clearbody PFX. clear POST.
    assert (ENx : ENV m3).
    { split; [exact GOT|]. split; [exact SB1|]. split; [exact DSK|]. split; [exists csb; split; [exact BPC| exact BSZ]|].
      split; [exists jt; exact FRH|]. split; [exact ST2|]. split; [exact MU1|]. split; [exact WM1| exact MI3]. }
    pose (WS1 := [b; Z_to_bv 64 0; Z_to_bv 64 0; b2; b3; b4; b5; b6; b7; b8; b9; b10; Z_to_bv 64 1; b12; b13; b14; Z_to_bv 64 0; b16; b17; b18; b19; Z_to_bv 64 0; b21; Z_to_bv 64 0; b23; b24; b25; b26; b27; b28; b29; b30; b31; b32; b33; b34; b35; b36; b37; b38; b39; b40; b41; b42]).
    assert (H5OKx : h5_frame_ok WS1).
    { clear - H5OK. unfold WS1, h5_frame_ok in *. cbv beta iota delta [wnth nth H5_format H5_forceIgnoreChecksum H5_refMultipleDDicts H5_maxBlockSizeParam H5_customAlloc
        H5_customFree H5_customOpaque H5_staticSize H5_ddictLocal H5_ddict H5_dictUses H5_ddictSet H5_inBuff] in *. exact H5OK. }
    assert (DAx : dctx_any m3 DCTX).
    { eexists _, _, _, _, _, _, _, _, _, fp, _, _, _, _, _, _, xs, WS1, _, _, _, _, _.
      split; [exact PT2|]. split; [exact H1x|]. split; [split; [exact FPC| exact FPSZ]|]. split; [exact H32|]. split; [split; [exact XSC| exact XSSZ]|].
      split; [split; [exact H5C| reflexivity]|]. split; [exact H5OKx|]. split; [exact TX2|]. split; [exact OWE| exact OWX]. }
    assert (DNZ : CAP - tot <> 0 -> 4096 <= DST).
    { intros NZ. destruct (Z.eq_dec DST 0) as [E|E]; [pose proof (DNULL E); lia | pose proof (DNN E); lia]. }
    assert (G496 : forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y24 y26 y27 y28 y29 y30 y31 : word), evt usegs POST (STpc 87672 m3 y1 y5 y6 y7 (Z_to_bv 64 (DST + CAP)) (Z_to_bv 64 (DST + tot)) y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 sz) (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) (Z_to_bv 64 0) (Z_to_bv 64 mt1) (Z_to_bv 64 (SRC + off)) y24 (Z_to_bv 64 (DCTX + 29928)) y26 y27 y28 y29 y30 y31));
      [| zs; zs; if_cases K3; zify_cond K3;
         [ replace (DST + CAP) with (DST + tot) in G496 by lia; apply G496
         | specialize (DNZ K3); zs; zs; fck; zs; fck; zs; fck; try replace (DST + tot + (CAP - tot)) with (DST + CAP) by lia; apply G496 ] ].
    intros y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y24 y26 y27 y28 y29 y30 y31.
    zs. rewrite sx32w_small by lia. zs. if_true.
    zs. zs. zs. if_cases K9; zify_cond K9.
    - (* [comment removed for export] *)
      eapply (L_errx2 _ off sz tot mt1 sl0 sl1 sl2); try eassumption.
    - (* [comment removed for export] *)
      zs. zs. if_true.
      zs. zs. zs.
      zs. fck.
      zs. zs. zs. zs.
      rewrite (proj2 (Z.ltb_lt 0 (SRC + off))) by lia. rewrite (proj2 (Z.ltb_ge (5 + (SRC + off) + -1) 1)) by lia.
      change (Z.lxor (Z.b2z true) (Z.b2z false)) with 1. if_false.
      zs. fck.
      try replace (5 + (SRC + off) + -1) with (SRC + (off + 4)) by lia.
      zlb SB1 OK (off + 4).
      set (fhd := Znth (off + 4) src) in *.
      zs. zs. zs. zs. zs. zs. if_cases UK; zify_cond UK; rewrite ?zb_lxor_ones in UK by lia; fck_norm UK; [exfalso; lia | clear UK].
      zs. replace (fhd ≫ 6) with (fhd_fcsID fhd) by (unfold fhd_fcsID; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      zs. zs. zs. zs. zs. if_cases UK; zify_cond UK; rewrite ?zb_lxor_ones in UK by lia; unfold fhd_fcsID in UK; [exfalso; lia | clear UK].
      zs. zs. zs. zs. zs.
      assert (RDD := dmf_tbl_did_rd _ (Z.land fhd 3) MI3 ltac:(change 3 with (Z.ones 2); rewrite Z.land_ones by lia; Z.div_mod_to_equations; lia)).
      zs. clear RDD.
      assert (RDF := dmf_tbl_fcs_rd _ (fhd_fcsID fhd) MI3 ltac:(unfold fhd_fcsID; Z.div_mod_to_equations; lia)).
      zs. clear RDF.
      do 6 zs.
      match goal with |- context [Z_to_bv 64 (?e + fcs_fieldSize (fhd_fcsID fhd))] =>
        replace (e + fcs_fieldSize (fhd_fcsID fhd)) with (fhd_header_size fhd)
          by (unfold fhd_header_size, ZD_FRAMEHEADERSIZE_PREFIX, fhd_singleSegment, fhd_dictIDSizeCode, fhd_fcsID, did_fieldSize, fcs_fieldSize; byte_brute fhd)
      end.
      pose proof (fhd_header_size_range fhd) as RFS. unfold ZD_FRAMEHEADERSIZE_MIN, ZD_FRAMEHEADERSIZE_MAX in RFS.
      assert (EHSZ : fhd_header_size fhd = frame_header_size src off ZD_FRAMEHEADERSIZE_PREFIX).
      { unfold fhd. rewrite frame_header_size_ge5 by (unfold ZD_FRAMEHEADERSIZE_PREFIX; lia). reflexivity. }
      set (hsz := fhd_header_size fhd) in *. clearbody hsz. clear RB. clearbody fhd.
      zs. if_cases KH; zify_cond KH; [exfalso; lia|].
      zs. zs. if_cases KS; zify_cond KS.
      + (* [comment removed for export] *)
        eapply (L_errx2 _ off sz tot mt1 sl0 sl1 sl2); try eassumption.
      + (* [comment removed for export] *)
        zs. zs. zs. zs.
        unfold PZD_GETFH in GETFH.
        callk (GETFH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SP + -272) (DCTX + 29928) SRC src off hsz fp lo);
          [ exact SB1 | exact OK | exact ROFF | lia | lia | lia | exact FPC | exact FPSZ | lia | exact ST2 | lia | lia
          | generalize S_DC; unfold zsep; lia | generalize S_SR; unfold zsep; lia | generalize SR_DC; unfold zsep; lia
          | exact MI3 | reflexivity | reflexivity | reflexivity | reflexivity | ].
        rename MI into MI4. rename PC into ST4. rename PC0 into FPC4. rename PC1 into FPSZ4. rename POST into ZFP.
        assert (ENy : ENV _) by (split; [exact GOT|]; split; [exact SB1|]; split; [exact DSK|]; split; [exists csb; split; [exact BPC| exact BSZ]|]; split; [exists jt; exact FRH|]; split; [exact ST4|]; split; [exact MU1|]; split; [exact WM1| assumption]).
        destruct (get_frame_header src off hsz) as [h|v] eqn:GFH; cbn [fh_retval] in *.
        * (* [comment removed for export] *)
          rewrite (ZFP h eq_refl) in FPC4. clear ZFP.
          pose proof (get_frame_header_ok src OK off hsz h GFH) as (_ & _ & _ & RFCS & _ & _ & _ & RCK & _).
          unfold zfh_cells in FPC4.
          (* [comment removed for export] *)
          assert (FOK : FRAME_OK off sz tot mt1 hsz h).
          { split; [exact ROFF|]. split; [exact RSZ|]. split; [exact RT|]. split; [exact RMT|]. split; [exact ACC|].
            split; [lia|]. split; [exact EHSZ|]. split; [lia|]. split; [apply NSK; lia| exact GFH]. }
          zs. zs. if_false. zs. if_true.
          zs. rewrite sx32w_small by lia. zs. zs. if_true.
          zs. rewrite sx32w_small by lia.
          zs. if_cases KC; zify_cond KC.
          -- assert (KCB : (fh_checksum h =? 0) = true) by (apply Z.eqb_eq; lia).
             zs.
             assert (ENz : ENV _) by (split; [exact GOT|]; split; [exact SB1|]; split; [exact DSK|]; split; [exists csb; split; [exact BPC| exact BSZ]|]; split; [exists jt; exact FRH|]; split; [assumption|]; split; [assumption|]; split; [assumption| assumption]).
             eassert (BD : B_DCTX _ h PFX _ _ _ _ _ _ _ _ _ _ _ _ xs [b; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; b3; b4; b5; b6; b7; b8; b9; b10; Z_to_bv 64 1; b12; b13; b14; Z_to_bv 64 0; b16; b17; b18; b19; Z_to_bv 64 0; b21; Z_to_bv 64 0; b23; b24; b25; b26; b27; b28; b29; b30; b31; b32; b33; b34; b35; b36; b37; b38; b39; b40; b41; b42]).
          { split; [exact PT2|]. split; [exact H1x|]. split; [exact FPC4|]. split; [exact H32|]. split; [split; [exact XSC| exact XSSZ]|].
            split; [intros NZ; exfalso; lia|]. split; [split; [exact H5C| reflexivity]|].
            split; [clear - H5OK; unfold h5_frame_ok in *; cbv beta iota delta [wnth nth H5_format H5_forceIgnoreChecksum H5_refMultipleDDicts H5_maxBlockSizeParam H5_customAlloc H5_customFree H5_customOpaque H5_staticSize H5_ddictLocal H5_ddict H5_dictUses H5_ddictSet H5_inBuff] in *; exact H5OK|].
            split; [cbv beta iota delta [wnth nth H5_validateChecksum]; rewrite ?KCB; reflexivity|]. split; [reflexivity|].
            split; [exists jhb, ovd, dcb, dce, (Z_to_bv 64 0); exact TX2|]. split; [split; [exact OWE| exact OWX]|].
            exact (tbl_init TBL TBLL _ DCTX BHUF BREP). }

             eapply (L_pcs _ off sz tot mt1 hsz h PFX); try eassumption; try lia.
          -- assert (KCB : (fh_checksum h =? 0) = false) by (apply Z.eqb_neq; lia).
             zs. rewrite sx32w_small by lia. zs. zs. zs. if_false.
             zs. zs. zs.
             unfold PZD_XXH_RESET in XXHRESET.
             callk (XXHRESET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SP + -272) (DCTX + 30008) xs lo);
               [ exact XSC | exact XSSZ | lia | lia | assumption | lia | lia | generalize S_DC; unfold zsep; lia | assumption | reflexivity | ].
             destruct POST as (j1 & j2 & XS2).
             zs.
             eassert (BD : B_DCTX _ h PFX _ _ _ _ _ _ _ _ _ _ _ _ (xxh_cells j1 0 j2) [b; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 1; b3; b4; b5; b6; b7; b8; b9; b10; Z_to_bv 64 1; b12; b13; b14; Z_to_bv 64 0; b16; b17; b18; b19; Z_to_bv 64 0; b21; Z_to_bv 64 0; b23; b24; b25; b26; b27; b28; b29; b30; b31; b32; b33; b34; b35; b36; b37; b38; b39; b40; b41; b42]).
          { split; [exact PT2|]. split; [exact H1x|]. split; [exact FPC4|]. split; [exact H32|]. split; [split; [exact XS2| reflexivity]|].
            split; [intros _; exists j1, 0, j2; split; [reflexivity| lia]|]. split; [split; [exact H5C| reflexivity]|].
            split; [clear - H5OK; unfold h5_frame_ok in *; cbv beta iota delta [wnth nth H5_format H5_forceIgnoreChecksum H5_refMultipleDDicts H5_maxBlockSizeParam H5_customAlloc H5_customFree H5_customOpaque H5_staticSize H5_ddictLocal H5_ddict H5_dictUses H5_ddictSet H5_inBuff] in *; exact H5OK|].
            split; [cbv beta iota delta [wnth nth H5_validateChecksum]; rewrite ?KCB; reflexivity|]. split; [reflexivity|].
            split; [exists jhb, ovd, dcb, dce, (Z_to_bv 64 0); exact TX2|]. split; [split; [exact OWE| exact OWX]|].
            exact (tbl_init TBL TBLL _ DCTX BHUF BREP). }

             assert (ENz : ENV _) by (split; [exact GOT|]; split; [exact SB1|]; split; [exact DSK|]; split; [exists csb; split; [exact BPC| exact BSZ]|]; split; [exists jt; exact FRH|]; split; [assumption|]; split; [assumption|]; split; [assumption| assumption]).
             eapply (L_pcs _ off sz tot mt1 hsz h PFX); try eassumption; try lia.
        * (* [comment removed for export] *)
          pose proof (gfh_ret_pos src off hsz v ltac:(lia) GFH) as RV.
          eassert (DAy : dctx_any _ DCTX).
          { eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, xs, WS1, _, _, _, _, _.
            split; [exact PT2|]. split; [exact H1x|]. split; [split; [exact FPC4| exact FPSZ4]|]. split; [exact H32|]. split; [split; [exact XSC| exact XSSZ]|].
            split; [split; [exact H5C| reflexivity]|]. split; [exact H5OKx|]. split; [exact TX2|]. split; [exact OWE| exact OWX]. }
          zs. zs. if_cases KE; zify_cond KE.
          -- zs. zs.
             eapply (L_errx _ off sz tot mt1 v sl0 sl1 sl2); try eassumption.
             ++ apply zd_is_error_true_iff. change (2^64) with 18446744073709551616. lia.
             ++ lia.
          -- zs. if_cases K0; zify_cond K0; [exfalso; lia|].
             eapply (L_errx2 _ off sz tot mt1 sl0 sl1 sl2); try eassumption.
  Qed.

  (* [comment removed for export] *)
  Notation A2St mm off sz tot mt1 x1 x5 x8 x11 x12 x13 x14 x26 x27 x28 x29 x30 x31 :=
    (STpc 87468 mm x1 x5 (Z_to_bv 64 (-120)) (Z_to_bv 64 25481893) x8 (Z_to_bv 64 (DST + tot)) (Z_to_bv 64 5) x11 x12 x13 x14
          (Z_to_bv 64 5) (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 sz) (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) (Z_to_bv 64 0)
          (Z_to_bv 64 mt1) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 4294967287) (Z_to_bv 64 (DCTX + 29928)) x26 x27 x28 x29 x30 x31).

  Lemma L_A2_body : forall m1 off sz tot mt1 (x1 x5 x8 x11 x12 x13 x14 x26 x27 x28 x29 x30 x31 : word),
    A_INV m1 off sz tot mt1 -> KA_T sz ->
    (forall off' sz' (y1 y5 y8 y11 y12 y13 y14 y26 y27 y28 y29 y30 y31 : word), sz' < sz -> A_INV m1 off' sz' tot mt1 ->
        evt usegs POST (A2St m1 off' sz' tot mt1 y1 y5 y8 y11 y12 y13 y14 y26 y27 y28 y29 y30 y31)) ->
    evt usegs POST (A2St m1 off sz tot mt1 x1 x5 x8 x11 x12 x13 x14 x26 x27 x28 x29 x30 x31).
  Proof.
    intros m1 off sz tot mt1 x1 x5 x8 x11 x12 x13 x14 x26 x27 x28 x29 x30 x31 AI KA KS.
    pose proof AI as (EN & (sl0 & sl1 & sl2 & sl3 & FRL) & DA & ROFF & RSZ & RSZ0 & RT & RMT & ACC).
    pose proof EN as (_ & SB1 & _).
    pose proof (bytes_at_bound _ _ _ _ SB1) as DB. rewrite length_map in DB.
    zs. if_cases K4; zify_cond K4.
    - (* [comment removed for export] *)
      eapply (L_frame m1 off sz tot mt1); try eassumption. intros C. exfalso. lia.
    - zs. fck.
      zlb SB1 OK (off + 1). zlb SB1 OK off. zlb SB1 OK (off + 2). zlb SB1 OK (off + 3).
      do 7 zs.
      match goal with |- context [Z.shiftr ?e 4] => replace e with (le32 src off) by (rewrite le32_bytes; lia) end.
      pose proof (le32_range src OK off) as RM. change (2^32) with 4294967296 in RM.
      rewrite Z.shiftr_div_pow2 by lia. change (2^4) with 16.
      zs. if_cases KSK; zify_cond KSK.
      + (* [comment removed for export] *)
        eapply (L_frame m1 off sz tot mt1); try eassumption. intros _.
        unfold is_skippable_magic. apply Z.eqb_neq. exact KSK.
      + (* [comment removed for export] *)
        assert (SKM : is_skippable_magic (le32 src off) = true) by (unfold is_skippable_magic; apply Z.eqb_eq; exact KSK).
        zs. if_cases K8; zify_cond K8.
        * (* [comment removed for export] *)
          zs. zs.
          replace (Z_to_bv 64 (-72)) with (Z_to_bv 64 (ZERR ZE_srcSize_wrong)) by (apply Z_to_bv_eqm; reflexivity).
          eapply (L_ret m1 (ZERR ZE_srcSize_wrong) sl0 sl1 sl2 sl3); try eassumption.
          -- unfold ZERR, ZE_srcSize_wrong. lia.
          -- intros E. rewrite zd_is_error_ZERR in E by (unfold ZE_srcSize_wrong, ZE_maxCode; lia). discriminate E.
        * zs. zs. fck.
          zlb SB1 OK (off + 5). zlb SB1 OK (off + 4). zlb SB1 OK (off + 6). zlb SB1 OK (off + 7).
          do 6 zs.
          replace (Znth (off + 7) src * 16777216 + Znth (off + 6) src * 65536 + (Znth (off + 5) src * 256 + Znth (off + 4) src)) with (le32 src (off + 4))
            by (rewrite le32_bytes; replace (off + 4 + 1) with (off + 5) by lia; replace (off + 4 + 2) with (off + 6) by lia;
                replace (off + 4 + 3) with (off + 7) by lia; lia).
          pose proof (le32_range src OK (off + 4)) as RS. change (2^32) with 4294967296 in RS.
          set (s32 := le32 src (off + 4)) in *.
          assert (RSK : read_skippable_frame_size src off sz =
                        if 4294967287 <? s32 then ZERR ZE_frameParameter_unsupported else if sz <? 8 + s32 then ZERR ZE_srcSize_wrong else 8 + s32).
          { unfold read_skippable_frame_size, ZD_SKIPPABLEHEADERSIZE. replace (sz <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
            cbv zeta. fold s32. pose proof (skippable_wrap_iff s32 ltac:(change (2^32) with 4294967296; lia)) as WI.
            unfold ZD_SKIPPABLEHEADERSIZE in WI. rewrite WI. reflexivity. }
          clearbody s32. clear RB RB0 RB1 RB2 RB3 RB4 RB5 RB6.
          zs. if_cases KU; zify_cond KU.
          -- (* [comment removed for export] *)
             zs. zs.
             replace (Z_to_bv 64 (-14)) with (Z_to_bv 64 (ZERR ZE_frameParameter_unsupported)) by (apply Z_to_bv_eqm; reflexivity).
             eapply (L_ret m1 (ZERR ZE_frameParameter_unsupported) sl0 sl1 sl2 sl3); try eassumption.
             ++ unfold ZERR, ZE_frameParameter_unsupported. lia.
             ++ intros E. rewrite zd_is_error_ZERR in E by (unfold ZE_frameParameter_unsupported, ZE_maxCode; lia). discriminate E.
          -- zs. zs. if_cases KF; zify_cond KF.
             ++ (* [comment removed for export] *)
                assert (RSV : read_skippable_frame_size src off sz = 8 + s32).
                { rewrite RSK. replace (4294967287 <? s32) with false by (symmetry; apply Z.ltb_ge; lia).
                  replace (sz <? 8 + s32) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
                assert (ACC2 : forall r, dmulti src (off + (s32 + 8)) (sz - (s32 + 8)) (CAP - tot) tot r -> decompress_ok src size CAP r).
                { intros r D. apply ACC. eapply (DM_skip src off sz (CAP - tot) tot r); [unfold ZD_FRAMEHEADERSIZE_PREFIX; lia | exact SKM | |].
                  - rewrite RSV. apply zd_is_error_false_iff. change (2^64) with 18446744073709551616. lia.
                  - rewrite RSV. replace (off + (8 + s32)) with (off + (s32 + 8)) by lia. replace (sz - (8 + s32)) with (sz - (s32 + 8)) by lia. exact D. }
                assert (AI2 : A_INV m1 (off + (s32 + 8)) (sz - (s32 + 8)) tot mt1).
                { split; [exact EN|]. split; [exists sl0, sl1, sl2, sl3; exact FRL|]. split; [exact DA|].
                  split; [lia|]. split; [lia|]. split; [lia|]. split; [exact RT|]. split; [exact RMT| exact ACC2]. }
                zs. if_cases KE; zify_cond KE; [exfalso; lia|].
                zs. zs. replace (SRC + off + (s32 + 8)) with (SRC + (off + (s32 + 8))) by lia.
                zs. if_cases K5; zify_cond K5.
                ** eapply (KS (off + (s32 + 8)) (sz - (s32 + 8))); [lia | exact AI2].
                ** zs.
                   eapply (L_exit m1 (sz - (s32 + 8)) tot sl0 sl1 sl2 sl3); try eassumption; try lia.
                   intros E0. apply ACC2. rewrite E0. apply DM_end.
             ++ (* [comment removed for export] *)
                zs. zs. if_cases KE; zify_cond KE; [| exfalso; lia].
                replace (Z_to_bv 64 (-72)) with (Z_to_bv 64 (ZERR ZE_srcSize_wrong)) by (apply Z_to_bv_eqm; reflexivity).
                eapply (L_ret m1 (ZERR ZE_srcSize_wrong) sl0 sl1 sl2 sl3); try eassumption.
                ** unfold ZERR, ZE_srcSize_wrong. lia.
                ** intros E. rewrite zd_is_error_ZERR in E by (unfold ZE_srcSize_wrong, ZE_maxCode; lia). discriminate E.
  Qed.

  Lemma L_A_of : forall m1 off sz tot mt1 (x1 x5 x8 x11 x12 x13 x14 x26 x27 x28 x29 x30 x31 : word),
    A_INV m1 off sz tot mt1 ->
    (forall (y1 y5 y8 y11 y12 y13 y14 y26 y27 y28 y29 y30 y31 : word),
        evt usegs POST (A2St m1 off sz tot mt1 y1 y5 y8 y11 y12 y13 y14 y26 y27 y28 y29 y30 y31)) ->
    evt usegs POST (ASt m1 off sz tot mt1 x1 x5 x8 x11 x12 x13 x14 x26 x27 x28 x29 x30 x31).
  Proof.
    intros m1 off sz tot mt1 x1 x5 x8 x11 x12 x13 x14 x26 x27 x28 x29 x30 x31 AI K2.
    pose proof AI as (EN & (sl0 & sl1 & sl2 & sl3 & FRL) & DA & ROFF & RSZ & RSZ0 & RT & RMT & ACC).
    zs. if_cases K5; zify_cond K5.
    - eapply (L_exit m1 sz tot sl0 sl1 sl2 sl3); try eassumption; try lia.
      intros E0. apply ACC. rewrite E0. apply DM_end.
    - apply K2.
  Qed.

  (* [comment removed for export] *)
  Lemma L_A2 : forall (n : nat) m1 off sz tot mt1 (x1 x5 x8 x11 x12 x13 x14 x26 x27 x28 x29 x30 x31 : word),
    sz <= Z.of_nat n -> A_INV m1 off sz tot mt1 ->
    evt usegs POST (A2St m1 off sz tot mt1 x1 x5 x8 x11 x12 x13 x14 x26 x27 x28 x29 x30 x31).
  Proof.
    induction n as [|n IH]; intros m1 off sz tot mt1 x1 x5 x8 x11 x12 x13 x14 x26 x27 x28 x29 x30 x31 RN AI.
    - apply L_A2_body; [exact AI | |].
      + intros m' off' sz' tot' y1 y5 y8 y11 y12 y13 y14 y26 y27 y28 y29 y30 y31 LT (_ & _ & _ & _ & _ & S0 & _). exfalso. lia.
      + intros off' sz' y1 y5 y8 y11 y12 y13 y14 y26 y27 y28 y29 y30 y31 LT (_ & _ & _ & _ & _ & S0 & _). exfalso. lia.
    - apply L_A2_body; [exact AI | |].
      + intros m' off' sz' tot' y1 y5 y8 y11 y12 y13 y14 y26 y27 y28 y29 y30 y31 LT AI'.
        apply L_A_of; [exact AI' |]. intros. apply IH; [lia | exact AI'].
      + intros off' sz' y1 y5 y8 y11 y12 y13 y14 y26 y27 y28 y29 y30 y31 LT AI'. apply IH; [lia | exact AI'].
  Qed.

  (* [comment removed for export] *)
  Lemma L_A : forall m1 off sz tot mt1 (x1 x5 x8 x11 x12 x13 x14 x26 x27 x28 x29 x30 x31 : word),
    A_INV m1 off sz tot mt1 ->
    evt usegs POST (ASt m1 off sz tot mt1 x1 x5 x8 x11 x12 x13 x14 x26 x27 x28 x29 x30 x31).
  Proof.
    intros m1 off sz tot mt1 x1 x5 x8 x11 x12 x13 x14 x26 x27 x28 x29 x30 x31 AI.
    pose proof AI as (_ & _ & _ & _ & _ & S0 & _).
    apply L_A_of; [exact AI |]. intros. apply (L_A2 (Z.to_nat sz)); [lia | exact AI].
  Qed.

  (* [comment removed for export] *)
  Lemma dctx_any_transport : forall W' m1 m2, dctx_any m1 DCTX -> munch W' m1 m2 -> wmono usegs m1 m2 ->
    disjoint_from W' DCTX 95992 -> dctx_any m2 DCTX.
  Proof.
    intros W' m1 m2 (llt & mlt & oft & huf & pde & pfx & vst & dend & expd & fp & pcs & dsz & bt & stg & le & fe & xs & ws & jhb & ovd & dcb & dce & trace &
                     PT & H1 & [FPC FPSZ] & H3 & [XSC XSSZ] & [H5C H5L] & H5OK & TX & [OWE OWX]) MU WM DJ.
    assert (TR : forall A cs, rw_cells usegs m1 A cs -> DCTX <= A -> A + Z.of_nat (cells_size cs) <= DCTX + 95992 -> rw_cells usegs m2 A cs).
    { intros A cs RC L1 L2. eapply rw_cells_transport; [exact RC | exact MU | exact WM |]. eapply ZdSepKit.disjoint_from_sub; [exact DJ | lia | lia]. }
    assert (TS : forall a b, stk usegs m1 a b -> DCTX <= a -> a <= b -> b <= DCTX + 95992 -> stk usegs m2 a b).
    { intros a b SK L1 L2 L3. eapply stk_transport_disjoint; [exact SK | exact MU | exact WM |]. eapply ZdSepKit.disjoint_from_sub; [exact DJ | lia | lia]. }
    unfold dctx_ptrs, dctx_h1, dctx_h3, dctx_tx in *.
    exists llt, mlt, oft, huf, pde, pfx, vst, dend, expd, fp, pcs, dsz, bt, stg, le, fe, xs, ws, jhb, ovd, dcb, dce, trace.
    split; [apply TR; [exact PT | lia | cbn; lia]|].
    split; [apply TR; [exact H1 | lia | cbn; lia]|].
    split; [split; [apply TR; [exact FPC | lia | rewrite FPSZ; lia]| exact FPSZ]|].
    split; [apply TR; [exact H3 | lia | cbn; lia]|].
    split; [split; [apply TR; [exact XSC | lia | rewrite XSSZ; lia]| exact XSSZ]|].
    split; [split; [apply TR; [exact H5C | lia | rewrite (h5_cells_size _ H5L); lia]| exact H5L]|].
    split; [exact H5OK|].
    split; [apply TR; [exact TX | lia | cbn; lia]|].
    split; apply TS; try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma L_ret_gen : forall m1 r (cl : list cell)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    ENV m1 -> rw_cells usegs m1 (SP + -272) cl -> cells_size cl = 104%nat -> dctx_any m1 DCTX ->
    0 <= r < 2^64 -> (zd_is_error r = false -> decompress_ok src size CAP r) ->
    evt usegs POST (STpc 88864 m1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 r) x28 x29 x30 x31).
  Proof.
    intros m1 r cl x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
           (GOT & SB1 & DSK & (csb & BPC & BSZ) & (jt & FRH) & ST1 & MU1 & WM1 & MI1) FRL CSZ DA RR RM.
    unfold RZ_dmf_a.frh_cells in FRH.
    do 14 zs.
    assert (FR : rw_cells usegs m1 (SP + -272) (cl ++ csb ++ [CB 52 jt; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact FRL|]. rewrite CSZ.
      apply (proj2 (rw_cells_app _ _ _ _ _)). split; [replace (SP + -272 + Z.of_nat 104) with (SP + -168) by lia; exact BPC|].
      rewrite BSZ. replace (SP + -272 + Z.of_nat 104 + Z.of_nat 12) with (SP + -156) by lia. exact FRH. }
    eapply stk_release in FR; [| exact ST1 | lia].
    rewrite !cells_size_app, BSZ, CSZ in FR. cbn [cells_size csize Nat.add] in FR.
    replace (SP + -272 + Z.of_nat 272) with SP in FR by lia.
    zs. zs.
    apply evt_done. unfold zd_dmf_post.
    do 14 eexists. exists m1, r. split; [reflexivity|].
    split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact FR|]. split; [exact DA|]. split; [exact DSK|]. split; [exact RR| exact RM].
  Qed.

  (* [comment removed for export] *)
  Lemma dmf_body : forall (t0 t1 t2 t3 t4 t5 t6 : word),
    dctx_any m DCTX -> rw_cells usegs m 0x36e40 [C8 wz0; C8 wz0] -> bytes_at usegs m SRC (map (Z_to_bv 8) src) ->
    stk usegs m DST (DST + CAP) -> stk usegs m lo SP -> mem_inv usegs m ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DCTX) (Z_to_bv 64 DST) (Z_to_bv 64 CAP) (Z_to_bv 64 SRC) (Z_to_bv 64 size)
               wz0 wz0 wz0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_DMF) fc None m (seg_rom usegs)).
  Proof.
    intros t0 t1 t2 t3 t4 t5 t6 DA GOT SB DSK ST MI.
    unfold PZD_DMF, wz0.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (MU2 : munch [(SP + -272, SP)] m m) by apply munch_refl.
    assert (WM2 : wmono usegs m m) by apply wmono_refl.
    pose proof (bytes_at_bound _ _ _ _ SB) as DB. rewrite length_map in DB.
    assert (LENP : zlen (map (Z_to_bv 8) src) = zlen src) by (rewrite length_map; reflexivity).
    pose proof DSK as (DST0 & _ & _).
    carve_frame 272%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] _ _ _ [8;8;8;8;8;8;8;8;8;8;8;8;8; 12; 52; 8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity].
    cbn [mk_CB_cells app] in FR.
    do 23 zs. if_true.
    zs. fck. zs. zs. fck.
    do 28 zs.
    lazymatch type of MU2 with munch _ _ ?mm =>
      assert (DA1 : dctx_any mm DCTX) by (eapply (dctx_any_transport [(SP + -272, SP)] m mm); [exact DA | exact MU2 | exact WM2 | dj_solve])
    end.
    clear DA MU2 WM2.
    pose proof DA1 as (llt & mlt & oft & huf & pde & pfx & vst & dend & expd & fp & pcs & dsz & bt & stg & le & fe & xs & ws & jhb & ovd & dcb & dce & trace &
                       _ & _ & _ & _ & _ & [H5C H5L] & H5OK & _).
    pose proof H5OK as (K_FMT & _). clear H5OK.
    h5_open ws H5L. unfold wz0 in K_FMT. subst b0.
    zs. rewrite sx32w_small by lia. clear H5C.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    zs. zs. if_true. zs. if_true.
    destruct (cb8_as_c8 usegs _ _ [] _ _ FR) as [w0 FR0]. cbn [app] in FR0. clear FR.
    destruct (cb8_as_c8 usegs _ _ [C8 w0] _ _ FR0) as [w1 FR1]. cbn [app] in FR1. clear FR0.
    destruct (cb8_as_c8 usegs _ _ [C8 w0; C8 w1] _ _ FR1) as [w2 FR2]. cbn [app] in FR2. clear FR1.
    lazymatch type of FR2 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: CB 8 _ :: _) =>
      destruct (cb8_as_c8 usegs _ _ [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11] _ _ FR2) as [w3 FR3]
    end.
    cbn [app] in FR3. clear FR2.
    apply (proj1 (rw_cells_app _ _ _ [C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _] _)) in FR3.
    destruct FR3 as [FRL FRX]. cbn [cells_size csize Nat.add] in FRX.
    apply (proj1 (rw_cells_app _ _ _ [CB 12 _] _)) in FRX. destruct FRX as [BPC FRH]. cbn [cells_size csize Nat.add] in FRH.
    replace (SP + -272 + Z.of_nat 104) with (SP + -168) in * by lia.
    replace (SP + -168 + Z.of_nat 12) with (SP + -156) in * by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AI : A_INV mm 0 size 0 0);
      [| pose proof (L_A mm 0 size 0 0) as HA ]
    end.
    { split. { split; [exact GOT|]. split; [exact SB|]. split; [exact DSK|]. split; [eexists; split; [exact BPC| reflexivity]|].
               split; [eexists; exact FRH|]. split; [exact ST|]. split; [exact MU|]. split; [exact WM| exact MI]. }
      split; [exists w0, w1, w2, w3; exact FRL|]. split; [exact DA1|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|].
      intros r D. unfold decompress_ok. replace (CAP - 0) with CAP in D by lia. exact D. }
    replace (DST + 0) with DST in HA by lia. replace (CAP - 0) with CAP in HA by lia. replace (SRC + 0) with SRC in HA by lia.
    eapply HA. exact AI.
  Qed.
End DMFD.
