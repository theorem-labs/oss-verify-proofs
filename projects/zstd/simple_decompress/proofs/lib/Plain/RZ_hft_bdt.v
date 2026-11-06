(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound ZdFrame ZdSeqBuild ZdSeqBuildThm ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdSeqBuildW2 ZdSeqBuildW4 ZdHufW ZdHufWM.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_hft_iface RZ_hft_bdt_defs RZ_hft_bdt_p1 RZ_hft_bdt_p3 RZ_hft_bdt_p2 RZ_hft_bdt_p2a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section G.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo DT NC W wlen maxSV tl : Z) (norm : list Z).
  Hypothesis HY : bd_hyps SPV lo DT NC W wlen maxSV tl norm.
  Notation POST := (fse_bdt_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT W wlen tl lo m).
  Notation ST pc mm x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR ra (Z_to_bv 64 (SPV + -96)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  Notation BDm := (BD s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DT NC W wlen maxSV tl norm).
  Notation HIGH := (hhigh norm maxSV tl).

  (* [comment removed for export] *)
  Lemma bd_p3_entry : forall m1 tb1 tb2 sn sp high fast y5 y6 y7 ys0 ys1 ya1 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y28 y29 y30 y31,
    BDm (Z_to_bv 64 tl) (Z_to_bv 64 fast) tb2 sn sp m1 -> p1_inv norm maxSV tl (maxSV + 1) tb1 sn high fast ->
    symtab_ok norm maxSV tl tb2 -> zlenF tb2 = 4 * 2^tl ->
    evt psegs POST (ST 0x252f4 m1 y5 y6 y7 ys0 ys1 (Z_to_bv 64 DT) ya1 (Z_to_bv 64 (2^tl)) (Z_to_bv 64 tl) (Z_to_bv 64 W) ya5 ya6 ya7
                       ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y28 y29 y30 y31).
  Proof.
    intros until y31; intros I P1 OK L2. open_bh HY.
    destruct (bd_size_rng _ _ _ _ _ _ _ _ _ HY) as (SZ & _).
    destruct (p3_init norm maxSV tl TLR MSVR NLEN NGE NSUM tb1 sn high fast P1 tb2 OK L2) as (TGOOD & TCNT & FASTH & P3).
    assert (FASTR : 0 <= fast <= 1) by (destruct P1 as (_ & _ & _ & _ & _ & FR1 & _); exact FR1).
    do 11 zstep.
    replace (DT + 7 + 2 ^ tl ≪ 2) with (DT + 7 + 4 * 2^tl) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    replace (Z_to_bv 64 (DT + 7)) with (Z_to_bv 64 (DT + 7 + 4 * 0)) by (f_equal; lia).
    eapply (bd_p3_loop ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DT NC W wlen maxSV tl norm HY (hsym tb2) fast
              TGOOD TCNT FASTH FASTR (Z.to_nat (2^tl - 1)) m1 0 tb2 sn sp); [exact I | exact P3 | lia | lia].
  Qed.

  Notation ST1 pc mm high s xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 fast :=
    (ST pc mm (Z_to_bv 64 (maxSV + 1)) (Z_to_bv 64 high) (Z_to_bv 64 s) (Z_to_bv 64 65535) xs1
        (Z_to_bv 64 DT) (Z_to_bv 64 NC) (Z_to_bv 64 (2^tl)) (Z_to_bv 64 tl) (Z_to_bv 64 W) (Z_to_bv 64 (DT + 4))
        (Z_to_bv 64 (2^tl + -1)) (Z_to_bv 64 (W + 2 * maxSV + 2)) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
        (Z_to_bv 64 (maxSV + 1)) (Z_to_bv 64 maxSV) (Z_to_bv 64 fast) (Z_to_bv 64 (2^(tl - 1)))).

  (* [comment removed for export] *)
  Lemma bd_after1 : forall m1 h0 h1 tb sn sp high fast ys1 ys2 ys3 ys4 xs5 xs6 xs7 xs8 xs9 xs10 xs11,
    BDm h0 h1 tb sn sp m1 -> p1_inv norm maxSV tl (maxSV + 1) tb sn high fast ->
    evt psegs POST (ST1 0x2512c m1 high (maxSV + 1) ys1 ys2 ys3 ys4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 fast).
  Proof.
    intros until xs11; intros I P1. open_bh HY.
    destruct (bd_size_rng _ _ _ _ _ _ _ _ _ HY) as (SZ & LLR & LL2).
    destruct (p2_init norm maxSV tl TLR MSVR NLEN NGE NSUM tb sn high fast P1) as (EH & P2).
    pose proof (hhigh_range norm maxSV tl TLR ltac:(lia) NLEN NGE NSUM) as HR.
    assert (FASTR : 0 <= fast <= 1) by (destruct P1 as (_ & _ & _ & _ & _ & FR1 & _); exact FR1).
    pose proof I as I'. open_bd I'.
    unfold FseNCount.Zlength in *.
    hide_not_mentioning DT. zstep. zstep. unhide. zstep.
    rewrite (srliw_val (2^tl) 1) by lia. rewrite (Z.mod_small (2^tl) 4294967296) by lia. change (2^1) with 2.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (I1 : BDm (Z_to_bv 64 tl) (Z_to_bv 64 fast) tb sn sp mx) by (unfold FseNCount.Zlength; close_bd) end.
    clear HDR CEL CLEN CBY SNX SNLEN SPRD SPLEN SPBY NCB STK FR MI MU WM.
    assert (KP3 : forall m2 tb' sp' y5 y6 y7 ys0 ys1' ya1 ya5 ya6 ya7 ys2' ys3' ys4' ys5 ys6 ys7 ys8 ys9 ys10 ys11 y28 y29 y30 y31,
       BDm (Z_to_bv 64 tl) (Z_to_bv 64 fast) tb' sn sp' m2 -> symtab_ok norm maxSV tl tb' -> zlenF tb' = 4 * 2^tl ->
       evt psegs POST (ST 0x252f4 m2 y5 y6 y7 ys0 ys1' (Z_to_bv 64 DT) ya1 (Z_to_bv 64 (2^tl)) (Z_to_bv 64 tl) (Z_to_bv 64 W) ya5 ya6 ya7
                          ys2' ys3' ys4' ys5 ys6 ys7 ys8 ys9 ys10 ys11 y28 y29 y30 y31)).
    { intros. eapply (bd_p3_entry _ tb); eassumption. }
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      subst high.
      eapply (bd_slow ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DT NC W wlen maxSV tl norm HY _ _ _ tb sn sp); [exact I1 | exact P2 |].
      intros. eapply KP3; eassumption.
    - (* [comment removed for export] *)
      assert (NOLOW : HIGH = 2^tl - 1).
      { subst high. destruct (Z_lt_le_dec HIGH 0) as [NEG|POS].
        - exfalso. assert (EE : HIGH = -1) by lia. rewrite EE in K. change ((-1) mod 18446744073709551616) with 18446744073709551615 in K. lia.
        - rewrite Z.mod_small in K by lia. lia. }
      eapply (bd_fast ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DT NC W wlen maxSV tl norm HY NOLOW _ _ _ tb sn sp); [exact I1 | exact P2 |].
      intros. eapply KP3; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma bd_p1_0 : forall (f : nat) m1 h0 h1 tb sn sp high fast xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11,
    BDm h0 h1 tb sn sp m1 -> p1_inv norm maxSV tl 0 tb sn high fast -> Z.of_nat (S f) = maxSV + 1 ->
    (forall m2 tb' sn' high' fast' ys1 ys2 ys3 ys4, BDm h0 h1 tb' sn' sp m2 -> p1_inv norm maxSV tl (maxSV + 1) tb' sn' high' fast' ->
       evt psegs POST (ST1 0x2512c m2 high' (maxSV + 1) ys1 ys2 ys3 ys4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 fast')) ->
    evt psegs POST (ST1 0x250f8 m1 high 0 (Z_to_bv 64 NC) (Z_to_bv 64 W) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 fast).
  Proof.
    intros until xs11; intros I P1 HF KONT.
    pose proof (bd_p1_loop ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DT NC W wlen maxSV tl norm HY
                  f m1 h0 h1 0 tb sn sp high fast xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11) as L.
    replace (NC + 2 * 0) with NC in L by lia. replace (W + 2 * 0) with W in L by lia.
    apply L; [exact I | exact P1 | lia | lia | exact KONT].
  Qed.

  (* [comment removed for export] *)
  Lemma bd_main : forall (t2 a6 t3 t4 t5 t6 xa5 : word),
    stk psegs m lo SPV -> stk psegs m DT (DT + 4 + 4 * 2^tl) -> stk psegs m W (W + wlen) ->
    bytes_at psegs m NC (u16s (map (Z_to_bv 64) norm)) -> mem_inv psegs m ->
    evt psegs POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp (Z_to_bv 64 (maxSV + 1)) (Z_to_bv 64 1) t2 s0 s1 (Z_to_bv 64 DT) (Z_to_bv 64 NC) (Z_to_bv 64 maxSV) (Z_to_bv 64 tl)
               (Z_to_bv 64 W) xa5 a6 (Z_to_bv 64 ((maxSV + 1) * 4294967296)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x25038) fc None m (seg_rom psegs)).
  Proof.
    intros t2 a6 t3 t4 t5 t6 xa5 STK DTS WS NCB MI. open_bh HY.
    destruct (bd_size_rng _ _ _ _ _ _ _ _ _ HY) as (SZ & LLR & LL2).
    assert (MU : munch [(DT, DT + 4 + 4 * 2^tl); (W, W + wlen); (SPV - 96, SPV)] m m) by apply munch_refl.
    assert (WM : wmono psegs m m) by apply wmono_refl.
    unfold FseNCount.Zlength in *.
    zstep. zstep. if_cases K0; zify_cond K0; [|exfalso; lia]. clear K0.
    hide_not_mentioning SPV.
    zstep. carve_frame 96%nat STK.
    do 12 zstep.
    unhide.
    zstep. zstep. zstep. zstep.
    rewrite (sllw_pow2 tl) by lia.
    zstep.
    replace (((maxSV + 1) * 4294967296) ≫ 32) with (maxSV + 1) by (rewrite Z.shiftr_div_pow2 by lia; change (2^32) with 4294967296; rewrite Z.div_mul by lia; reflexivity).
    zstep. zstep. zstep. zstep. zstep.
    rewrite (Z.mod_small maxSV 4294967296) by lia.
    rewrite (zext32_sh31' maxSV) by lia.
    zstep.
    rewrite (swrap32_small (2^tl + -1)) by lia.
    zstep.
    rewrite (shiftl_mod32 32768 tl) by lia.
    assert (P15 : 32768 * 2^tl = 65536 * 2^(tl - 1)) by lia.
    rewrite (swrap32_small (32768 * 2^tl)) by lia.
    zstep. zstep.
    rewrite (srliw_val (32768 * 2^tl) 16) by lia. rewrite (Z.mod_small (32768 * 2^tl) 4294967296) by lia.
    replace (32768 * 2 ^ tl / 2 ^ 16) with (2^(tl - 1)) by (rewrite P15; change (2^16) with 65536; rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
    zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    destruct (stk_open psegs _ DT (DT + 4 + 4 * 2^tl) DT (Z.to_nat (4 + 4 * 2^tl)) DTS ltac:(lia) ltac:(lia)) as (jd & DTC & _ & _).
    assert (LJD : length jd = Z.to_nat (4 + 4 * 2^tl)) by (destruct DTC as [[WF _] _]; cbn in WF; destruct WF as [LJ _]; exact LJ).
    apply u8arr_of_rw_cells in DTC.
    rewrite <- (firstn_skipn 4 jd) in DTC. apply u8arr_app in DTC. destruct DTC as [HDRU CELU].
    assert (LH : length (firstn 4 jd) = 4%nat) by (rewrite firstn_length; lia).
    rewrite LH in CELU. change (Z.of_nat 4) with 4 in CELU.
    apply rw_cells_of_u8arr in HDRU. rewrite LH in HDRU.
    apply (rw_cells_split_CB psegs _ _ [] 4 _ [] [2; 2]%nat) in HDRU; [| reflexivity]. cbn [mk_CB_cells app] in HDRU.
    lazymatch type of HDRU with rw_cells _ _ _ (CB 2 ?j :: ?post) => destruct (cb2_as_c2 psegs _ _ [] j post HDRU) as [h0 HDR1] end. cbn [app] in HDR1. clear HDRU.
    lazymatch type of HDR1 with rw_cells _ _ _ (?c0 :: CB 2 ?j :: ?post) => destruct (cb2_as_c2 psegs _ _ [c0] j post HDR1) as [h1 HDR] end. cbn [app] in HDR. clear HDR1.
    rewrite <- (bytes_of_unsigned (skipn 4 jd)) in CELU.
    set (tb0 := map bv_unsigned (skipn 4 jd)) in *.
    assert (CLEN : Z.of_nat (length tb0) = 4 * 2^tl) by (unfold tb0; rewrite length_map, skipn_length; lia).
    assert (CBY : Forall isbyte tb0) by (apply bytes_unsigned_range).
    (* [comment removed for export] *)
    destruct (stk_open psegs _ W (W + wlen) W (Z.to_nat wlen) WS ltac:(lia) ltac:(lia)) as (jw & WC & _ & _).
    assert (LJW : length jw = Z.to_nat wlen) by (destruct WC as [[WF _] _]; cbn in WF; destruct WF as [LJ _]; exact LJ).
    apply u8arr_of_rw_cells in WC.
    rewrite <- (firstn_skipn (2 * Z.to_nat (maxSV + 1)) jw) in WC. apply u8arr_app in WC. destruct WC as [SNU SPU].
    assert (LS : length (firstn (2 * Z.to_nat (maxSV + 1)) jw) = (2 * Z.to_nat (maxSV + 1))%nat) by (rewrite firstn_length; lia).
    rewrite LS in SPU. replace (W + Z.of_nat (2 * Z.to_nat (maxSV + 1))) with (W + 2 * (maxSV + 1)) in SPU by lia.
    destruct (u16s_of_bytes (Z.to_nat (maxSV + 1)) _ LS) as (sn0 & LN0 & _ & EN0). rewrite EN0 in SNU.
    rewrite <- (bytes_of_unsigned (skipn (2 * Z.to_nat (maxSV + 1)) jw)) in SPU.
    set (sp0 := map bv_unsigned (skipn (2 * Z.to_nat (maxSV + 1)) jw)) in *.
    assert (SPLEN : Z.of_nat (length sp0) = wlen - 2 * (maxSV + 1)) by (unfold sp0; rewrite length_map, skipn_length; lia).
    assert (SPBY : Forall isbyte sp0) by (apply bytes_unsigned_range).
    assert (SNLEN : Z.of_nat (length sn0) = maxSV + 1) by lia.
    clear DTS WS EN0 LS LJW LJD LH.
    assert (I : BDm h0 h1 tb0 sn0 sp0 m1) by (unfold BD, FseNCount.Zlength; close_bd).
    eapply (bd_p1_0 (Z.to_nat maxSV) m1 h0 h1 tb0 sn0 sp0 (2^tl + -1) 1); [exact I | | lia |].
    - replace (2^tl + -1) with (2^tl - 1) by lia.
      apply (p1_init norm maxSV tl TLR MSVR NLEN NGE NSUM); unfold FseNCount.Zlength; assumption.
    - intros m2 tb' sn' high' fast' ys1 ys2 ys3 ys4 I2 P1'.
      eapply bd_after1; [exact I2 | exact P1'].
  Qed.
End G.

Theorem fse_bdt_proof : fse_bdt_stmt.
Proof.
  unfold fse_bdt_stmt, PFSE_BDT. intros until norm.
  intros MI STK LO0 LOS SPR DTS DTL DTH WS WL WLEN WH NCB NCL NCH TLR MSVR NLEN NGE NSUM OFFDT OFFW OFFNC DTW DTNC WNC.
  assert (SZ : 32 <= 2^tl <= 512).
  { assert (2^5 <= 2^tl) by (apply Z.pow_le_mono_r; lia). assert (2^tl <= 2^9) by (apply Z.pow_le_mono_r; lia).
    change (2^5) with 32 in *. change (2^9) with 512 in *. lia. }
  zstep. zstep. zstep. if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
  zstep. rewrite (swrap32_small (maxSV + 1)) by lia.
  zstep. zstep.
  replace ((maxSV + 1) ≪ 32) with ((maxSV + 1) * 4294967296) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  zstep.
  replace (((maxSV + 1) * 4294967296) ≫ 31) with (2 * (maxSV + 1))
    by (rewrite Z.shiftr_div_pow2 by lia; change 4294967296 with (2 * 2^31); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
  zstep.
  replace (1 ≪ (tl mod 64)) with (2^tl) by (rewrite Z.mod_small by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep. zstep. zstep. if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    zstep. replace (Z_to_bv 64 (-46)) with (Z_to_bv 64 18446744073709551570) by (apply bv_eq; reflexivity).
    zstep. apply evt_done. unfold fse_bdt_post.
    do 14 eexists. exists m, 18446744073709551570.
    split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|].
    split; [exact STK|]. split; [exact WS|]. split; [lia|]. right. split; [reflexivity| exact DTS].
  - assert (HY : bd_hyps SPV lo DT NC W wlen maxSV tl norm).
    { unfold bd_hyps, FseNCount.Zlength, pws. repeat split; try eassumption; try lia. }
    eapply (bd_main ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DT NC W wlen maxSV tl norm HY); assumption.
Qed.

(* [comment removed for export] *)
