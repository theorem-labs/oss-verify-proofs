(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdSeqTable ZdSeqBuild ZdSeqBuildThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdSeqBuildW2 ZdSeqBuildW3 ZdSeqBuildW4 ZdSeqBuildW5 ZdSeqBuildW6.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_blk_iface RZ_bfse_defs RZ_bfse_a RZ_bfse_p1 RZ_bfse_b RZ_bfse_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.


Section G.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo DT NC BASE BITS W maxSV tl : Z) (k : seq_kind) (wlen : nat) (norm : list Z).
  Hypothesis HY : bf_hyps SPV lo DT NC BASE BITS W maxSV tl k wlen norm.
  Notation POST t := (bf_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT W tl wlen lo m t).
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -128)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  Notation BFm := (BF ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DT NC BASE BITS W tl k wlen norm).

  (* [comment removed for export] *)
  Notation STP pc mm xra x6e x7e xs0 xs1 xa0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (ST pc mm xra (Z_to_bv 64 (2^tl + -1)) x6e x7e xs0 xs1 xa0 (Z_to_bv 64 NC) (Z_to_bv 64 (2^tl)) (Z_to_bv 64 BASE) (Z_to_bv 64 BITS)
        (Z_to_bv 64 tl) (Z_to_bv 64 W) (Z_to_bv 64 (DT + 8)) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31).
  Notation ST1 pc mm xra xa0 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 :=
    (STP pc mm xra (Z_to_bv 64 (W + 106)) (Z_to_bv 64 (maxSV + 1)) (Z_to_bv 64 (W + 2 * (maxSV + 1))) (Z_to_bv 64 65535) xa0
         xs2 xs3 xs4 xs5 (Z_to_bv 64 DT) xs7 xs8 xs9 xs10 xs11 x28 x29 x30 (Z_to_bv 64 (2^(tl + -1)))).



  (* [comment removed for export] *)
  Lemma bf_p3 : forall m1 fast w8 w16 cells symNext spread cellsF snF xra x5 x6 xs0 xs1 xa0 xa1 xa7 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    BFm (Z_to_bv 64 fast) (Z_to_bv 64 tl) w8 w16 cells symNext spread m1 -> 0 <= fast <= 1 ->
    (forall v, 0 <= v < 2^tl -> good norm maxSV (ss_base (cell_nth cells v))) ->
    (forall s, 0 <= s <= maxSV -> Znth s symNext = snext0 norm s) ->
    build_cells (Z.to_nat (2^tl)) tl (kind_base k) (kind_bits k) 0 cells symNext = (cellsF, snF) ->
    evt psegs (POST (mkST fast tl cellsF))
      (ST 0x16aa4 m1 xra x5 x6 (Z_to_bv 64 (2^tl)) xs0 xs1 xa0 xa1 (Z_to_bv 64 (2^tl)) (Z_to_bv 64 BASE) (Z_to_bv 64 BITS) (Z_to_bv 64 tl) (Z_to_bv 64 W) xa7
          xs2 xs3 xs4 xs5 (Z_to_bv 64 DT) xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I HF GOODC SN0 BC.
    destruct (bf_size_rng _ _ _ _ _ _ _ _ _ _ _ _ HY) as (TL9 & SZ & MSV52).
    zstep. zstep. rewrite (Z.shiftl_mul_pow2 (2^tl) 3) by lia. change (2^3) with 8.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    replace (DT + 12 + 2^tl * 8) with (DT + 12 + 8 * 2^tl) by lia.
    replace (Z.to_nat (2^tl)) with (S (Z.to_nat (2^tl - 1))) in BC by lia.
    eapply (bf_p3_loop ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DT NC BASE BITS W maxSV tl k wlen norm HY
              (Z.to_nat (2^tl - 1)) m1 fast w8 w16 0 cells symNext spread cellsF snF);
      [exact I | exact HF | lia | lia | | | exact BC | f_equal; lia].
    - intros v Hv. apply GOODC. lia.
    - intros s GS. rewrite SN0 by (destruct GS; lia). lia.
  Qed.

  (* [comment removed for export] *)
  Definition bf_table (cells0 : list seqsym) (symNext0 spread0 : list Z) : seq_table :=
    fst (fst (build_fse_table (kind_base k) (kind_bits k) norm maxSV tl cells0 symNext0 spread0)).

  (* [comment removed for export] *)
  Lemma bf_after1 : forall m1 h0 h1 w8 w16 cells0 symNext0 spread0 cells1 symNext1 high fast xra xa0 ys3 ys4 ys5 xs7 xs8 xs9 xs10 xs11,
    zlenF cells0 = 2^tl -> zlenF symNext0 = 53 -> 2^tl + 8 <= zlenF spread0 -> Forall (fun v => 0 <= v < 256) spread0 ->
    lowprob (Z.to_nat (maxSV + 1)) norm (2^(tl - 1)) 0 cells0 symNext0 (2^tl - 1) 1 = (cells1, symNext1, high, fast) ->
    BFm h0 h1 w8 w16 cells1 symNext1 spread0 m1 -> 0 <= fast <= 1 ->
    evt psegs (POST (bf_table cells0 symNext0 spread0))
      (ST1 0x168d8 m1 xra xa0 (Z_to_bv 64 (NC + 2 * (maxSV + 1))) ys3 ys4 ys5 xs7 xs8 xs9 xs10 xs11
           (Z_to_bv 64 high) (Z_to_bv 64 fast) (Z_to_bv 64 (maxSV + 1))).
  Proof.
    intros until xs11; intros HC0 HN0 HSP0 SB0 LP I HF. open_bh HY.
    destruct (bf_size_rng _ _ _ _ _ _ _ _ _ _ _ _ HY) as (TL9 & SZ & MSV52).
    pose proof (p12_after1 norm maxSV tl TL9 ltac:(lia) NLEN NGE NSUM cells0 symNext0 cells1 symNext1 high fast HC0 ltac:(lia) LP)
      as (HHN & HHR & C1 & N1 & S1 & AG1).
    pose proof I as I'. open_bf I'.
    assert (LBASE : Z.of_nat (length (kind_base k)) <= 53) by (destruct k; vm_compute; discriminate).
    assert (LBITS : Z.of_nat (length (kind_bits k)) <= 53) by (destruct k; vm_compute; discriminate).
    unfold FseNCount.Zlength in CLEN, SNLEN, SPLEN, NLEN, NCH, OFFNC, DTNC, WNC.
    hide_not_mentioning DT. zstep. zstep. unhide. zstep.
    rewrite (srliw_val (2^tl) 3) by lia. rewrite (Z.mod_small (2^tl) 4294967296) by lia. change (2^3) with 8.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (I1 : BFm (Z_to_bv 64 fast) (Z_to_bv 64 tl) w8 w16 cells1 symNext1 spread0 mx) by close_bf end.
    clear HDR CEL CLEN SNX SNLEN SPRD SPLEN NCB BASEB BITSB STK FR MI MU WM.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      assert (NH : high <> 2^tl - 1) by (intros E; apply K; rewrite E; rewrite Z.mod_small by lia; lia).
      eapply (bf_slow ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DT NC BASE BITS W maxSV tl k wlen norm HY
                (bf_table cells0 symNext0 spread0) _ _ _ w8 w16 cells1 symNext1 spread0 high); [exact I1 | exact HHN |].
      intros mm2 cells2 p2 yi ya0 yn SS I2.
      destruct (p12_slow norm maxSV tl TL9 ltac:(lia) NLEN NGE NSUM cells0 symNext0 cells1 symNext1 high fast HC0 ltac:(lia) LP NH cells2 p2 SS) as (C2 & G2).
      destruct (build_cells (Z.to_nat (2^tl)) tl (kind_base k) (kind_bits k) 0 cells2 symNext1) as [cellsF snF] eqn:BC.
      assert (ET : bf_table cells0 symNext0 spread0 = mkST fast tl cellsF).
      { unfold bf_table, build_fse_table. rewrite LP. destruct (Z.eqb_spec high (2^tl - 1)) as [E|_]; [exfalso; exact (NH E)|].
        rewrite SS. cbn [fst]. rewrite BC. reflexivity. }
      rewrite ET.
      zstep. zstep. rewrite (Z.mod_small (2^tl) 4294967296) by lia.
      eapply bf_p3; [exact I2 | exact HF | exact G2 | exact S1 | exact BC].
    - (* [comment removed for export] *)
      assert (EH : high = 2^tl - 1) by (destruct (Z_lt_le_dec high 0); [rewrite <- (Z.mod_small (2^tl + -1) 18446744073709551616) in K by lia; exfalso; Z.div_mod_to_equations; lia | rewrite Z.mod_small in K by lia; lia]).
      replace (Z_to_bv 64 high) with (Z_to_bv 64 (2^tl + -1)) by (f_equal; lia).
      eapply (bf_fast ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DT NC BASE BITS W maxSV tl k wlen norm HY
                (bf_table cells0 symNext0 spread0) _ _ _ w8 w16 cells1 symNext1 spread0); [exact I1 | exact SB0 | lia |].
      intros mm2 w8' w16' spread1 pos1 cells2 p2 yra ys0 ys1 ya0 ys2 ys3' ys4' ys5' ys7 ys8 ys9 ys10 ys11 ys ypos LSY PF I2.
      destruct (p12_fast norm maxSV tl TL9 ltac:(lia) NLEN NGE NSUM cells0 symNext0 spread0 cells1 symNext1 high fast HC0 ltac:(lia) HSP0 LP EH spread1 pos1 cells2 p2 LSY PF) as (C2 & G2).
      destruct (build_cells (Z.to_nat (2^tl)) tl (kind_base k) (kind_bits k) 0 cells2 symNext1) as [cellsF snF] eqn:BC.
      assert (ET : bf_table cells0 symNext0 spread0 = mkST fast tl cellsF).
      { unfold bf_table, build_fse_table. rewrite LP. destruct (Z.eqb_spec high (2^tl - 1)) as [_|NE]; [|exfalso; exact (NE EH)].
        rewrite LSY, PF. cbn [fst]. rewrite BC. reflexivity. }
      rewrite ET.
      eapply bf_p3; [exact I2 | exact HF | exact G2 | exact S1 | exact BC].
  Qed.

  (* [comment removed for export] *)
  Lemma bf_p1_0 : forall (t : seq_table) (f : nat) m1 h0 h1 w8 w16 cells symNext spread high fast xra xa0 xs4 xs5 xs7 xs8 xs9 xs10 xs11,
    BFm h0 h1 w8 w16 cells symNext spread m1 ->
    Z.of_nat (S f) = maxSV + 1 -> 0 <= fast <= 1 -> high = 2^tl - 1 ->
    (forall m2 cells' symNext' high' fast' ys3 ys4 ys5,
       lowprob (S f) norm (2^(tl + -1)) 0 cells symNext high fast = (cells', symNext', high', fast') ->
       BFm h0 h1 w8 w16 cells' symNext' spread m2 -> 0 <= fast' <= 1 ->
       evt psegs (POST t) (ST1 0x168d8 m2 xra xa0 (Z_to_bv 64 (NC + 2 * (maxSV + 1))) ys3 ys4 ys5 xs7 xs8 xs9 xs10 xs11
                               (Z_to_bv 64 high') (Z_to_bv 64 fast') (Z_to_bv 64 (maxSV + 1)))) ->
    evt psegs (POST t) (ST1 0x168a4 m1 xra xa0 (Z_to_bv 64 NC) (Z_to_bv 64 W) xs4 xs5 xs7 xs8 xs9 xs10 xs11
                            (Z_to_bv 64 high) (Z_to_bv 64 fast) (Z_to_bv 64 0)).
  Proof.
    intros until xs11; intros I HF HFA HH KONT.
    pose proof (bf_p1_loop ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DT NC BASE BITS W maxSV tl k wlen norm HY
                  t f m1 h0 h1 w8 w16 0 cells symNext spread high fast xra xa0 xs4 xs5 xs7 xs8 xs9 xs10 xs11) as L.
    replace (NC + 2 * 0) with NC in L by lia. replace (W + 2 * 0) with W in L by lia.
    apply L; [exact I | lia | lia | exact HFA | change (FseReadSound.pws norm 0) with 0; change (nsum norm 0) with 0; lia | exact KONT].
  Qed.

  (* [comment removed for export] *)
  Lemma bf_main : forall (t0 t1 t2 a7 t3 t4 t5 t6 : word) ha hb cells0 symNext0 spread0,
    rw_cells psegs m DT [C4 ha; C4 hb] ->
    u8arr psegs m (DT + 8) (cellsB cells0) -> zlenF cells0 = 2^tl ->
    u8arr psegs m W (u16s (map (Z_to_bv 64) symNext0)) -> zlenF symNext0 = 53 ->
    u8arr psegs m (W + 106) (map (Z_to_bv 8) spread0) -> zlenF spread0 = Z.of_nat wlen - 106 -> Forall (fun v => 0 <= v < 256) spread0 ->
    bytes_at psegs m NC (u16s (map (Z_to_bv 64) norm)) ->
    bytes_at psegs m BASE (u32s (map (Z_to_bv 64) (kind_base k))) ->
    bytes_at psegs m BITS (map (Z_to_bv 8) (kind_bits k)) ->
    stk psegs m lo SPV -> mem_inv psegs m ->
    evt psegs (POST (bf_table cells0 symNext0 spread0))
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DT) (Z_to_bv 64 NC) (Z_to_bv 64 maxSV) (Z_to_bv 64 BASE) (Z_to_bv 64 BITS)
               (Z_to_bv 64 tl) (Z_to_bv 64 W) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x167cc) fc None m (seg_rom psegs)).
  Proof.
    intros until spread0. intros HDR CEL CLEN SNX SNLEN SPRD SPLEN SB0 NCB BASEB BITSB STK MI. open_bh HY.
    destruct (bf_size_rng _ _ _ _ _ _ _ _ _ _ _ _ HY) as (TL9 & SZ & MSV52).
    assert (LBASE : Z.of_nat (length (kind_base k)) <= 53) by (destruct k; vm_compute; discriminate).
    assert (LBITS : Z.of_nat (length (kind_bits k)) <= 53) by (destruct k; vm_compute; discriminate).
    assert (MU : munch [(DT, DT + 8 + 8 * 2^tl); (W, W + Z.of_nat wlen); (SPV - 128, SPV)] m m) by apply munch_refl.
    assert (WM : wmono psegs m m) by apply wmono_refl.
    unfold FseNCount.Zlength in *.
    hide_not_mentioning SPV.
    zstep. carve_frame 128%nat STK.
    do 13 zstep.
    unhide.
    lazymatch type of FR with rw_cells _ _ _ (CB 24 ?j :: ?post) =>
      apply (rw_cells_split_CB psegs _ _ [] 24 j post [8; 8; 8]%nat) in FR; [| reflexivity] end.
    cbn [mk_CB_cells app] in FR.
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: CB 8 ?j :: ?post) =>
      destruct (cb8_as_c8 psegs _ _ [c0] j post FR) as [w8 FR1] end. cbn [app] in FR1. clear FR.
    lazymatch type of FR1 with rw_cells _ _ _ (?c0 :: ?c1 :: CB 8 ?j :: ?post) =>
      destruct (cb8_as_c8 psegs _ _ [c0; c1] j post FR1) as [w16 FR] end. cbn [app] in FR. clear FR1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. rewrite (swrap32_small (maxSV + 1)) by lia.
    zstep. zstep. rewrite (sllw_pow2 tl) by lia.
    zstep. zstep. rewrite ?(Z.mod_small (2^tl) 18446744073709551616) by lia. rewrite (swrap32_small (2^tl + -1)) by lia.
    zstep. if_cases K0; zify_cond K0; [|exfalso; lia]. clear K0.
    zstep. zstep. zstep. zstep. zstep.
    rewrite (shiftl_mod32 65536 (tl + -1)) by lia.
    assert (P1 : 16 <= 2^(tl + -1) <= 256).
    { assert (2^4 <= 2^(tl + -1)) by (apply Z.pow_le_mono_r; lia). assert (2^(tl + -1) <= 2^8) by (apply Z.pow_le_mono_r; lia).
      change (2^4) with 16 in *. change (2^8) with 256 in *. lia. }
    rewrite (swrap32_small (65536 * 2^(tl + -1))) by lia.
    zstep. zstep. zstep.
    rewrite (signed_lit (65536 * 2^(tl + -1))) by lia.
    rewrite (Z.shiftr_div_pow2 (65536 * 2^(tl + -1)) 16) by lia. change (2^16) with 65536.
    rewrite (Z.mul_comm 65536), Z.div_mul by lia.
    rewrite (Z.mod_small (maxSV + 1) 4294967296) by lia.
    rewrite (zext32_sh31 (maxSV + 1)) by lia.
    zstep. zstep. zstep. zstep. zstep. zstep.
    assert (CLEN' : zlenF cells0 = 2^tl) by exact CLEN. assert (SNLEN' : zlenF symNext0 = 53) by exact SNLEN.
    assert (SPLEN' : zlenF spread0 = Z.of_nat wlen - 106) by exact SPLEN.
    eapply (bf_p1_0 (bf_table cells0 symNext0 spread0) (Z.to_nat maxSV) _ ha hb w8 w16 cells0 symNext0 spread0 (2^tl + -1) 1);
      [close_bf | lia | lia | lia |].
    intros mm2 cells1 symNext1 high fast ys3 ys4 ys5 LP I2 HF.
    replace (S (Z.to_nat maxSV)) with (Z.to_nat (maxSV + 1)) in LP by lia.
    replace (tl + -1) with (tl - 1) in LP by lia. replace (2^tl + -1) with (2^tl - 1) in LP by lia.
    replace (tl + -1) with (tl - 1) by lia.
    eapply (bf_after1 mm2 ha hb w8 w16 cells0 symNext0 spread0 cells1 symNext1 high fast);
      [exact CLEN | exact SNLEN | unfold FseNCount.Zlength; lia | exact SB0 | exact LP | exact I2 | exact HF].
  Qed.
End G.

Theorem zd_buildfse_proof : zd_buildfse_stmt.
Proof.
  unfold zd_buildfse_stmt, PZD_BUILDFSE, off_stack, apart. intros until norm.
  intros DTA DTLEN WA WLEN NCB TLR MSVR NLEN NGE NSUM BASEB BITSB DTL DTH WL WH NCL NCH BASER BITSR STK LOS LO0 SPR
         OFFDT OFFW OFFNC OFFBASE OFFBITS DTW DTNC WNC DTBASE DTBITS WBASE WBITS MI -> -> -> -> -> -> ->.
  assert (HY : bf_hyps SPV lo DT NC BASE BITS W maxSV tl k (length wb0) norm).
  { unfold bf_hyps. repeat split; try eassumption; try lia. }
  destruct (bf_size_rng _ _ _ _ _ _ _ _ _ _ _ _ HY) as (TL9 & SZ & MSV52).
  (* [comment removed for export] *)
  rewrite <- (firstn_skipn 8 dt0) in DTA. apply u8arr_app in DTA. destruct DTA as [HDRU CELU].
  assert (LH : length (firstn 8 dt0) = 8%nat) by (rewrite firstn_length; lia).
  rewrite LH in CELU. change (Z.of_nat 8) with 8 in CELU.
  apply rw_cells_of_u8arr in HDRU. rewrite LH in HDRU. destruct (cb8_as_c4s _ _ _ _ HDRU) as (ha & hb & HDR).
  destruct (cells_of_bytes (Z.to_nat (2^tl)) (skipn 8 dt0) ltac:(rewrite skipn_length; lia)) as (cells0 & LC0 & EC0).
  rewrite <- EC0 in CELU.
  (* [comment removed for export] *)
  rewrite <- (firstn_skipn 106 wb0) in WA. apply u8arr_app in WA. destruct WA as [SNU SPU].
  assert (LS : length (firstn 106 wb0) = 106%nat) by (rewrite firstn_length; lia).
  rewrite LS in SPU. change (Z.of_nat 106) with 106 in SPU.
  destruct (u16s_of_bytes 53 (firstn 106 wb0) LS) as (symNext0 & LN0 & _ & EN0). rewrite EN0 in SNU.
  rewrite <- (bytes_of_unsigned (skipn 106 wb0)) in SPU.
  eapply evt_mono.
  - eapply (bf_main ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DT NC BASE BITS W maxSV tl k (length wb0) norm HY
              t0 t1 t2 a7 t3 t4 t5 t6 ha hb cells0 symNext0 (map bv_unsigned (skipn 106 wb0)));
      [exact HDR | exact CELU | unfold FseNCount.Zlength; lia | exact SNU | unfold FseNCount.Zlength; lia | exact SPU
      | unfold FseNCount.Zlength; rewrite length_map, skipn_length; lia | apply bytes_unsigned_range
      | exact NCB | exact BASEB | exact BITSB | exact STK | exact MI].
  - intros ms' (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & wb' & -> & MU & WM & MI' & STK' & TB & WB' & LWB).
    unfold zd_buildfse_post. do 15 eexists. exists m'. eexists. exists wb'.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact STK'|].
    split; [exact TB|].
    assert (OK : seq_table_ok k (bf_table maxSV tl k norm cells0 symNext0 (map bv_unsigned (skipn 106 wb0)))).
    { unfold bf_table. apply (build_fse_table_ok_wsum k norm maxSV tl); try assumption; unfold FseNCount.Zlength; try lia.
      rewrite length_map, skipn_length. lia. }
    split; [| split; [exact OK | split; [exact WB' | exact LWB]]].
    unfold bf_table, build_fse_table.
    destruct (lowprob _ _ _ _ _ _ _ _) as [[[c1 n1] h1] f1].
    destruct (if h1 =? 2 ^ tl - 1 then _ else _) as [c2 sp2].
    destruct (build_cells _ _ _ _ _ _ _) as [c3 n3]. reflexivity.
Qed.
