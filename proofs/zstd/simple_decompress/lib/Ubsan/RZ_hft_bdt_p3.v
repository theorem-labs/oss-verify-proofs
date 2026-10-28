(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound ZdFrame ZdSeqBuild ZdSeqBuildThm ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdSeqBuildW2 ZdSeqBuildW4 ZdHufW ZdHufWM.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_hft_iface RZ_hft_bdt_defs RZ_fse_bdt_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section EPI.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo DT NC W wlen maxSV tl : Z) (norm : list Z).
  Hypothesis HY : bd_hyps SPV lo DT NC W wlen maxSV tl norm.
  Hypothesis HUB : lo <= SPV - 128 /\ DT mod 4 = 0 /\ W mod 2 = 0 /\ NC mod 2 = 0.
  Notation POST := (fse_bdt_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT W wlen tl lo m).
  Notation ST pc mm x1 x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -128)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation BDm := (BDU ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DT NC W wlen maxSV tl norm).

  (* [comment removed for export] *)
  Lemma bd_wk_stk : forall m1 h0 h1 tb sn sp, BDm h0 h1 tb sn sp m1 ->
    stk usegs m1 W (W + wlen) /\ stk usegs m1 DT (DT + 4 + 4 * 2^tl).
  Proof.
    intros m1 h0 h1 tb sn sp I. open_bh HY. open_bd I. unfold FseNCount.Zlength in *. split.
    - apply rw_cells_of_u8arr in SNX. apply stk_of_rw_cells in SNX. apply rw_cells_of_u8arr in SPRD. apply stk_of_rw_cells in SPRD.
      cbn [cells_size csize] in SNX, SPRD. rewrite u16s_length, length_map in SNX. rewrite length_map in SPRD.
      apply (stk_merge usegs m1 W (W + 2 * (maxSV + 1)) (W + wlen)); [| |lia].
      + replace (W + 2 * (maxSV + 1)) with (W + Z.of_nat (2 * length sn + 0)) by lia. exact SNX.
      + replace (W + wlen) with (W + 2 * (maxSV + 1) + Z.of_nat (length sp + 0)) by lia. exact SPRD.
    - apply stk_of_rw_cells in HDR. apply rw_cells_of_u8arr in CEL. apply stk_of_rw_cells in CEL.
      cbn [cells_size csize] in HDR, CEL. rewrite length_map in CEL.
      apply (stk_merge usegs m1 DT (DT + 4) (DT + 4 + 4 * 2^tl)); [| |lia].
      + replace (DT + 4) with (DT + Z.of_nat (2 + (2 + 0))) at 2 by lia. exact HDR.
      + replace (DT + 4 + 4 * 2^tl) with (DT + 4 + Z.of_nat (length tb + 0)) by lia. exact CEL.
  Qed.

  (* [comment removed for export] *)
  Lemma bd_epi : forall m1 h0 h1 tb sn sp r x1 x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    BDm h0 h1 tb sn sp m1 ->
    0 <= r < 2^64 ->
    ((r = 0 /\ exists fast, h0 = Z_to_bv 64 tl /\ h1 = Z_to_bv 64 fast /\ 0 <= fast <= 1 /\ forall u, 0 <= u < 2^tl -> fse_cell_ok tl fast tb u)
     \/ zd_is_error r = true) ->
    evt usegs POST
      (ST 0x2ab08 m1 x1 x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 r) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I RR RES. open_bh HY. pose proof HUB as (LOU & _ & _ & _).
    pose proof (bd_wk_stk _ _ _ _ _ _ I) as (WKS & DTS). open_bd I.
    zstep. do 13 zstep.
    zstep.
    release_frame FR STK SPV.
    zstep. apply evt_done. unfold fse_bdt_post.
    do 14 eexists. exists m1, r.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|]. split; [exact WKS|]. split; [exact RR|].
    destruct RES as [(R0 & fast & E0 & E1 & FR01 & OK)|ERR].
    - left. split; [exact R0|]. exists fast, tb. subst h0 h1. unfold fse_dtable, FseNCount.Zlength in *.
      split; [exact HDR|]. split; [exact CEL|]. split; [exact CLEN|]. split; [exact FR01|]. split; [exact CBY| exact OK].
    - right. split; [exact ERR| exact DTS].
  Qed.
End EPI.

Section P3.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo DT NC W wlen maxSV tl : Z) (norm : list Z).
  Hypothesis HY : bd_hyps SPV lo DT NC W wlen maxSV tl norm.
  Hypothesis HUB : lo <= SPV - 128 /\ DT mod 4 = 0 /\ W mod 2 = 0 /\ NC mod 2 = 0.
  Variables (T : Z -> Z) (fast : Z).
  Hypothesis TGOOD : forall v, 0 <= v < 2^tl -> good norm maxSV (T v).
  Hypothesis TCNT : forall s, 0 <= s <= maxSV -> hocc T s (2^tl) = weight (Znth s norm).
  Hypothesis FASTH : fast = 1 -> forall i, 0 <= i <= maxSV -> Znth i norm < 2^(tl - 1).
  Hypothesis FASTR : 0 <= fast <= 1.

  Notation POST := (fse_bdt_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT W wlen tl lo m).
  Notation ST pc mm x1 x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -128)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation BDm := (BDU ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DT NC W wlen maxSV tl norm).

  (* [comment removed for export] *)
  Notation ST3 pc mm x1 xs0 xs1 xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 u :=
    (ST pc mm x1 (Z_to_bv 64 252645135) (Z_to_bv 64 16843009) (Z_to_bv 64 31) xs0 xs1 (Z_to_bv 64 (DT + 7 + 4 * u))
        (Z_to_bv 64 1431655765) (Z_to_bv 64 858993459) xa3 (Z_to_bv 64 W) (Z_to_bv 64 (2^tl)) (Z_to_bv 64 (znot W)) (Z_to_bv 64 (DT + 4))
        xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma bd_p3_body : forall m1 u tb sn sp x1 xs0 xs1 xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    BDm (Z_to_bv 64 tl) (Z_to_bv 64 fast) tb sn sp m1 -> p3_inv norm maxSV tl T fast u tb sn -> 0 <= u < 2^tl ->
    x28 = Z_to_bv 64 (2^tl - u) -> x29 = Z_to_bv 64 (DT + 4 + 4 * u) ->
    (forall m2 tb' sn' y28 y29 ya3 y30 y31, BDm (Z_to_bv 64 tl) (Z_to_bv 64 fast) tb' sn' sp m2 -> p3_inv norm maxSV tl T fast (u + 1) tb' sn' ->
       y28 = Z_to_bv 64 (2^tl - (u + 1)) -> y29 = Z_to_bv 64 (DT + 4 + 4 * (u + 1)) ->
       evt usegs POST (ST3 0x2ab00 m2 x1 xs0 xs1 ya3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 y28 y29 y30 y31 (u + 1))) ->
    evt usegs POST (ST3 0x2aa50 m1 x1 xs0 xs1 xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 u).
  Proof.
    intros until x31; intros I P3 HU E28 E29 KONT; open_bh HY; open_bd I. subst x28 x29.
    pose proof HUB as (LOU & _ & _ & _).
    destruct (bd_size_rng _ _ _ _ _ _ _ _ _ HY) as (SZ & LLR & LL2).
    unfold FseNCount.Zlength in *.
    pose proof (p3_step norm maxSV tl TLR MSVR NLEN NGE NSUM T fast TGOOD TCNT FASTH u tb sn P3 HU) as STEP. cbv zeta in STEP.
    set (sym := hsym tb u) in *. set (ns := Znth sym sn) in *.
    destruct STEP as (SYR & NSR & LGR & NXR & P3').
    assert (SYB : Znth (4 * u + 2) tb = sym) by reflexivity.
    zstep. bd_chk.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u8_znth usegs m1 (DT + 4) tb (4 * u + 2) a CEL ltac:(lia) ltac:(addr_tac)) as RD end.
    rewrite SYB in RD.
    zstep.
    cbv beta. rewrite (byte_lit sym) by lia.
    zstep. rewrite ?(Z.mod_small (sym ≪ 1) 18446744073709551616) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    replace (sym ≪ 1) with (2 * sym) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep. bd_chk.
    zstep.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u16_znth usegs m1 W sn sym a (proj1 SNX) ltac:(lia) ltac:(addr_tac)) as RD2 end.
    fold ns in RD2.
    zstep.
    rewrite (zx16_u ns) by lia.
    zstep.
    snst SNX sym (ns + 1) (ns + 1).
    assert (SNLEN' : Z.of_nat (length (upd_nat (Z.to_nat sym) (ns + 1) sn)) = maxSV + 1)
      by (rewrite FseLemmas.upd_nat_length; exact SNLEN).
    zstep. bd_chk.
    zstep. bd_chk.
    (* [comment removed for export] *)
    zstep. zstep. set (sa := Z.lor ns (ns ≫ 1)). zstep. zstep. set (sb := Z.lor sa (sa ≫ 2)). zstep. zstep. set (sc := Z.lor sb (sb ≫ 4)).
    zstep. zstep. zstep.
    lazymatch goal with |- _ => let v := reg_val 13 in lazymatch v with Z_to_bv 64 ?e => change e with (smear16 ns) end end.
    rewrite (smear16_ok ns) by lia.
    set (L := Z.log2 ns) in *.
    assert (HL : 0 <= L <= 10).
    { subst L. split; [apply Z.log2_nonneg|]. assert (Z.log2 ns < 11); [|lia]. apply Z.log2_lt_pow2; [lia|]. change (2^11) with 2048. lia. }
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- _ => let v := reg_val 13 in lazymatch v with Z_to_bv 64 ?e =>
      replace e with L by (clear - HL; clearbody L;
        assert (C : L = 0 \/ L = 1 \/ L = 2 \/ L = 3 \/ L = 4 \/ L = 5 \/ L = 6 \/ L = 7 \/ L = 8 \/ L = 9 \/ L = 10) by lia;
        destruct C as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]; rewrite E; vm_compute; reflexivity) end end.
    zstep.
    zstep.
    rewrite (swrap32_small (tl - L)) by lia.
    zstep. rewrite land255, (Z.mod_small (tl - L) 256) by lia.
    tbst CEL (4 * u + 3) (tl - L); [reflexivity|].
    zstep. bd_chk.
    zstep.
    rewrite (shiftl_mod32 ns (tl - L)) by lia.
    pose proof (shl_hb_range ns tl ltac:(lia) ltac:(lia) ltac:(lia)) as NSB. fold L in NSB.
    rewrite (swrap32_small (ns * 2^(tl - L))) by lia.
    zstep.
    zstep.
    rewrite (swrap32_small (ns * 2^(tl - L) - 2^tl)) by lia.
    set (nxt := ns * 2^(tl - L) - 2^tl) in *.
    u8_sok2 CEL (4 * u). zstep. hide_not_mentioning DT. u8_store2 CEL (4 * u) nxt; [reflexivity|]. unhide.
    zstep. zstep.
    rewrite (Z.mod_small (nxt / 256) 256) in CEL by (clear - NXR SZ; Z.div_mod_to_equations; lia).
    rewrite (Zupd_comm tb (4 * u) (4 * u + 3)) in CEL by lia.
    rewrite (Zupd_comm _ (4 * u + 1) (4 * u + 3)) in CEL by lia.
    replace (DT + 7 + 4 * u + 4) with (DT + 7 + 4 * (u + 1)) by lia.
    eapply KONT; [| exact P3' | f_equal; lia | f_equal; lia].
    assert (CLEN' : Z.of_nat (length (Zupd (4 * u + 3) (tl - L) (Zupd (4 * u + 1) (nxt / 256) (Zupd (4 * u) (nxt mod 256) tb)))) = 4 * 2^tl)
      by (rewrite !FseLemmas.Zupd_length; exact CLEN).
    assert (CBY' : Forall isbyte (Zupd (4 * u + 3) (tl - L) (Zupd (4 * u + 1) (nxt / 256) (Zupd (4 * u) (nxt mod 256) tb)))).
    { repeat apply Forall_Zupd; [exact CBY | | | ]; clear - NXR SZ HL TLR LGR; Z.div_mod_to_equations; lia. }
    unfold Zupd in *. unfold FseNCount.Zlength. close_bd.
  Qed.

  (* [comment removed for export] *)
  Lemma bd_p3_loop : forall (f : nat) m1 u tb sn sp x1 xs0 xs1 xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    BDm (Z_to_bv 64 tl) (Z_to_bv 64 fast) tb sn sp m1 -> p3_inv norm maxSV tl T fast u tb sn -> 0 <= u -> u + Z.of_nat (S f) = 2^tl ->
    x28 = Z_to_bv 64 (2^tl - u) -> x29 = Z_to_bv 64 (DT + 4 + 4 * u) ->
    evt usegs POST (ST3 0x2aa50 m1 x1 xs0 xs1 xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 u).
  Proof.
    induction f as [|f IH]; intros until x31; intros I P3 HU HUF E28 E29; open_bh HY.
    all: destruct (bd_size_rng _ _ _ _ _ _ _ _ _ HY) as (SZ & _).
    - eapply bd_p3_body; [exact I | exact P3 | lia | exact E28 | exact E29 |].
      intros m2 tb' sn' y28 y29 ya3 y30 y31 I2 P3' F28 F29. subst y28 y29.
      zstep. if_cases K; zify_cond K; [exfalso; clear - K HUF HU SZ; Z.div_mod_to_equations; lia|].
      zstep.
      eapply (bd_epi ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DT NC W wlen maxSV tl norm HY HUB m2 _ _ tb' sn' sp 0); [exact I2| lia |].
      left. split; [reflexivity|]. exists fast. split; [reflexivity|]. split; [reflexivity|]. split; [exact FASTR|].
      replace (u + 1) with (2^tl) in P3' by lia.
      exact (p3_done norm maxSV tl TLR MSVR NLEN NGE NSUM T fast TGOOD TCNT FASTH tb' sn' P3').
    - eapply bd_p3_body; [exact I | exact P3 | lia | exact E28 | exact E29 |].
      intros m2 tb' sn' y28 y29 ya3 y30 y31 I2 P3' F28 F29. subst y28 y29.
      zstep. if_cases K; zify_cond K; [|exfalso; clear - K HUF HU SZ; Z.div_mod_to_equations; lia].
      eapply (IH m2 (u + 1)); [exact I2 | exact P3' | lia | lia | reflexivity | reflexivity].
  Qed.
End P3.
