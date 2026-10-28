(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require FseNCountRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memset RZ_huf_iface RZ_hft_iface RZ_hft_rs_iface RZ_hft_kit RZ_hft_bdt_defs.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import huf411_kit_rs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac u32st RK s x v :=
  lazymatch type of RK with u32arr ?segs ?mx ?Wb (map (Z_to_bv 64) ?l) =>
    let SOK := fresh "SOK" in
    pose proof (u32arr_store_ok segs mx Wb _ s (wa (Wb + 4 * s)) RK ltac:(rewrite length_map; lia) eq_refl) as SOK;
    zstep;
    let S2 := fresh "RK" in
    pose proof (u32arr_write segs mx Wb _ s (Z_to_bv 64 x) RK ltac:(rewrite length_map; lia)) as S2;
    clear RK; store_done;
    apply (u32arr_upd_Z segs _ Wb l (Z.to_nat s) x v) in S2; [| first [ reflexivity | rewrite Z.mod_mod by lia; reflexivity ]];
    rename S2 into RK
  end.

Section RSTATS.
  Hypothesis FDEC : fse_dec_stmt.

  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV HW RS NSP SRC n WK wksz lo B bsz : Z) (src : list byte).
  Hypothesis LO0 : 4096 <= lo.  Hypothesis LOS : lo <= SPV - 512.
  Hypothesis SPV16 : rsk_al SPV 16.  Hypothesis RS4 : rsk_al RS 4.  Hypothesis NSP4 : rsk_al NSP 4.  Hypothesis WK4 : rsk_al WK 4.
  Hypothesis SRCLEN : Z.of_nat (length src) = n.  Hypothesis SRCL : 4096 <= SRC.  Hypothesis NR : n < 2^32.  Hypothesis SRCH : SRC + n < 2^47.
  Hypothesis WKSZ : 0 <= wksz < 2^32.
  Hypothesis BL : 4096 <= B.  Hypothesis BH : B + bsz < 2^47.  Hypothesis BRS : B <= RS.  Hypothesis RSHW : RS + 52 <= HW.
  Hypothesis RSWK : RS + 52 <= WK.  Hypothesis HWB : HW + 256 <= B + bsz.  Hypothesis WKB : WK + wksz <= B + bsz.
  Hypothesis HWWK : WK + wksz <= HW \/ HW + 256 <= WK.
  Hypothesis NSLO : SPV + 8 <= NSP.  Hypothesis NSH : NSP + 8 < 2^47.
  Hypothesis OFFB : B + bsz <= lo \/ SPV + 8 <= B.  Hypothesis BNS : B + bsz <= NSP \/ NSP + 8 <= B.
  Hypothesis BSRC : B + bsz <= SRC \/ SRC + n <= B.  Hypothesis NSSRC : NSP + 8 <= SRC \/ SRC + n <= NSP.
  Hypothesis OFFSRC : SRC + n <= lo \/ SPV <= SRC.

  Notation POST := (huf_rstats_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV HW RS NSP n WK wksz lo m).
  Notation MUNCH := [(HW, HW + 256); (RS, RS + 52); (NSP, NSP + 8); (WK, WK + wksz); (SPV - 512, SPV)].
  Notation STF pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -64)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FRAME j := [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Lemma rs_exit_err : forall m1 j r x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    stk usegs m1 HW (HW + 256) -> stk usegs m1 RS (RS + 52) -> stk usegs m1 NSP (NSP + 8) -> stk usegs m1 WK (WK + wksz) ->
    stk usegs m1 lo (SPV + -64) -> rw_cells usegs m1 (SPV + -64) (FRAME j) ->
    mem_inv usegs m1 -> munch MUNCH m m1 -> wmono usegs m m1 ->
    0 <= r < 2^64 -> zd_is_error r = true ->
    evt usegs POST (STF 0x2a638 m1 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros until x31; intros HWS RSS NSS WKS STK FR MI MU WM RR RE.
    do 7 zstep. zstep.
    apply stk_of_rw_cells in FR. cbn [cells_size csize Nat.add] in FR.
    assert (STK' : stk usegs m1 lo SPV).
    { apply (stk_merge usegs m1 lo (SPV + -64) SPV STK); [|lia]. replace SPV with (SPV + -64 + Z.of_nat 64) at 2 by lia. exact FR. }
    zstep. apply evt_done. unfold huf_rstats_post.
    do 14 eexists. exists m1, r.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK'|].
    split; [exact WKS|]. split; [exact RR|]. right. split; [exact RE|]. split; [exact HWS|]. split; [exact RSS| exact NSS].
  Qed.

  (* [comment removed for export] *)
  Definition RSM (fj : list byte) (hw rank : list Z) (m1 : fmem) : Prop :=
    u8arr usegs m1 HW (map (Z_to_bv 8) hw) /\ Z.of_nat (length hw) = 256 /\ Forall (fun c => 0 <= c < 256) hw
    /\ u32arr usegs m1 RS (map (Z_to_bv 64) rank) /\ Z.of_nat (length rank) = 13
    /\ (exists wn wt, rw_cells usegs m1 NSP [C4 wn; C4 wt])
    /\ stk usegs m1 WK (WK + wksz)
    /\ stk usegs m1 lo (SPV + -64) /\ rw_cells usegs m1 (SPV + -64) (FRAME fj)
    /\ mem_inv usegs m1 /\ munch MUNCH m m1 /\ wmono usegs m m1.
  Ltac open_rsm I := destruct I as (HWC & HWLEN & HWBY & RK & RKLEN & (wn & wt & NSC) & WKS & STK & FR & MI & MU & WM).

  Lemma rs_exit_arr : forall m1 fj hw rank r x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    RSM fj hw rank m1 -> 0 <= r < 2^64 -> zd_is_error r = true ->
    evt usegs POST (STF 0x2a638 m1 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I RR RE. open_rsm I.
    eapply (rs_exit_err _ _ r); try eassumption.
    - apply rw_cells_of_u8arr in HWC. apply stk_of_rw_cells in HWC. cbn [cells_size csize] in HWC. rewrite length_map in HWC.
      replace (HW + 256) with (HW + Z.of_nat (length hw + 0)) by lia. exact HWC.
    - apply u8arr_of_u32arr in RK. apply rw_cells_of_u8arr in RK. apply stk_of_rw_cells in RK. cbn [cells_size csize] in RK.
      rewrite u32s_length, length_map in RK. replace (RS + 52) with (RS + Z.of_nat (4 * length rank + 0)) by lia. exact RK.
    - apply stk_of_rw_cells in NSC. cbn [cells_size csize Nat.add] in NSC. exact NSC.
  Qed.

  (* [comment removed for export] *)
  Lemma rs_final : forall m1 fj hw rank isz osz x1 x5 x6 x7 x15 x16 x17 x20 x21 x28 x29 x30 x31,
    RSM fj hw rank m1 -> rank_inv (firstn (Z.to_nat osz) hw) rank -> Forall (fun w => 0 <= w <= 12) (firstn (Z.to_nat osz) hw) ->
    1 <= osz <= 255 -> 0 <= isz -> isz + 1 <= n ->
    evt usegs POST
      (STF 0x2a46c m1 x1 x5 x6 x7 (Z_to_bv 64 RS) (Z_to_bv 64 HW) (Z_to_bv 64 (-20)) (Z_to_bv 64 NSP) (Z_to_bv 64 (Z.lxor HW 18446744073709551615)) (Z_to_bv 64 (NSP + 4))
           (Z_to_bv 64 (hw_total (firstn (Z.to_nat osz) hw))) x15 x16 x17 (Z_to_bv 64 osz) (Z_to_bv 64 isz) x20 x21 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I RI FA OSR ISZ0 ISZN. open_rsm I.
    set (ws0 := firstn (Z.to_nat osz) hw) in *.
    assert (WS0L : FseNCount.Zlength ws0 = osz) by (unfold FseNCount.Zlength, ws0; rewrite length_firstn; lia).
    pose proof (hw_total_bound ws0 FA) as WTB. pose proof (hw_total_nonneg ws0) as WT0.
    set (wt0 := hw_total ws0) in *.
    assert (WTR : 0 <= wt0 < 524288) by lia.
    zstep. if_cases K0; zify_cond K0.
    { replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 18446744073709551596) by (apply bv_eq; reflexivity).
      eapply (rs_exit_arr _ fj hw rank 18446744073709551596); [ | lia | reflexivity].
      unfold RSM. split; [exact HWC|]. split; [exact HWLEN|]. split; [exact HWBY|]. split; [exact RK|]. split; [exact RKLEN|].
      split; [exists wn, wt; exact NSC|]. split; [exact WKS|]. split; [exact STK|]. split; [exact FR|]. split; [exact MI|]. split; [exact MU| exact WM]. }
    zstep.
    assert (srliw_small : forall x k, 0 <= x < 2^19 -> 0 <= k -> bv_swrap 32 (bv_wrap 32 x ≫ k) = x ≫ k).
    { clear. intros x k Hx Hk. change (2^19) with 524288 in Hx. rewrite wrap32_small by lia. apply swrap32_small.
      assert (0 <= x ≫ k) by (apply Z.shiftr_nonneg; lia).
      assert (x ≫ k <= x) by (rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk); Z.div_mod_to_equations; nia). lia. }
    assert (RW : 0 <= wt0 < 2^19) by (change (2^19) with 524288; lia).
    rewrite (srliw_small wt0 1 RW) by lia.
    zstep. zstep.
    pose proof (lor_shr_lt wt0 1 19 RW ltac:(lia) ltac:(lia)) as RA.
    zstep. zstep. rewrite (srliw_small _ 2 RA) by lia. zstep.
    pose proof (lor_shr_lt _ 2 19 RA ltac:(lia) ltac:(lia)) as RB.
    zstep. rewrite (srliw_small _ 4 RB) by lia. zstep.
    pose proof (lor_shr_lt _ 4 19 RB ltac:(lia) ltac:(lia)) as RC.
    zstep. rewrite (srliw_small _ 8 RC) by lia. zstep.
    pose proof (lor_shr_lt _ 8 19 RC ltac:(lia) ltac:(lia)) as RD.
    zstep. rewrite (srliw_small _ 16 RD) by lia. zstep.
    lazymatch goal with |- _ => let v := reg_val 15 in lazymatch v with Z_to_bv 64 ?e => change e with (smear32 wt0) end end.
    rewrite (smear32_ok wt0) by lia.
    clear RA RB RC RD.
    set (L := Z.log2 wt0) in *.
    assert (HL : 0 <= L <= 18).
    { subst L. split; [apply Z.log2_nonneg|]. assert (Z.log2 wt0 < 19); [|lia]. apply Z.log2_lt_pow2; lia. }
    assert (LSPEC : 2^L <= wt0 < 2^(L + 1)) by (subst L; pose proof (Z.log2_spec wt0 ltac:(lia)) as X; replace (Z.succ (Z.log2 wt0)) with (Z.log2 wt0 + 1) in X by lia; exact X).
    clearbody L.
    do 18 zstep.
    zstep.
    lazymatch goal with |- _ => let v := reg_val 16 in lazymatch v with Z_to_bv 64 ?e =>
      replace e with (31 - L) by (clear - HL;
        assert (C : L = 0 \/ L = 1 \/ L = 2 \/ L = 3 \/ L = 4 \/ L = 5 \/ L = 6 \/ L = 7 \/ L = 8 \/ L = 9 \/ L = 10 \/ L = 11 \/ L = 12
                    \/ L = 13 \/ L = 14 \/ L = 15 \/ L = 16 \/ L = 17 \/ L = 18) by lia;
        repeat (destruct C as [E|C]; [rewrite E; vm_compute; reflexivity|]); rewrite C; vm_compute; reflexivity) end end.
    zstep.
    replace (Z.lxor (31 - L) 31) with L by (clear - HL;
        assert (C : L = 0 \/ L = 1 \/ L = 2 \/ L = 3 \/ L = 4 \/ L = 5 \/ L = 6 \/ L = 7 \/ L = 8 \/ L = 9 \/ L = 10 \/ L = 11 \/ L = 12
                    \/ L = 13 \/ L = 14 \/ L = 15 \/ L = 16 \/ L = 17 \/ L = 18) by lia;
        repeat (destruct C as [E|C]; [rewrite E; vm_compute; reflexivity|]); rewrite C; vm_compute; reflexivity).
    zstep. zstep. if_cases K1; zify_cond K1.
    { replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 18446744073709551596) by (apply bv_eq; reflexivity).
      eapply (rs_exit_arr _ fj hw rank 18446744073709551596); [ | lia | reflexivity].
      unfold RSM. split; [exact HWC|]. split; [exact HWLEN|]. split; [exact HWBY|]. split; [exact RK|]. split; [exact RKLEN|].
      split; [exists wn, wt; exact NSC|]. split; [exact WKS|]. split; [exact STK|]. split; [exact FR|]. split; [exact MI|]. split; [exact MU| exact WM]. }
    zstep. rsk_chk. zstep. zstep. rsk_chk.
    zstep. zstep. replace (32 - (31 - L)) with (L + 1) by lia.
    zstep. zstep.
    rewrite (shiftl_mod32 2 L) by lia.
    assert (PL : 1 <= 2^L <= 2048) by (split; [pose proof (Z.pow_pos_nonneg 2 L ltac:(lia) ltac:(lia)); lia | change 2048 with (2^11); apply Z.pow_le_mono_r; lia]).
    assert (PE : 2^(L + 1) = 2 * 2^L) by (rewrite Z.pow_add_r by lia; lia).
    rewrite PE in LSPEC.
    remember (2^L) as P eqn:EP.
    rewrite (swrap32_small (2 * P)) by lia.
    zstep. zstep. rsk_chk.
    zstep. rewrite (swrap32_small (2 * P - wt0)) by lia.
    remember (2 * P - wt0) as rest eqn:EREST.
    assert (RR : 0 <= rest < 2^19) by (change (2^19) with 524288; lia).
    zstep. zstep. rewrite (srliw_small rest 1 RR) by lia. zstep. zstep.
    pose proof (lor_shr_lt rest 1 19 RR ltac:(lia) ltac:(lia)) as RA.
    zstep. rewrite (srliw_small _ 2 RA) by lia. zstep.
    pose proof (lor_shr_lt _ 2 19 RA ltac:(lia) ltac:(lia)) as RB.
    zstep. rewrite (srliw_small _ 4 RB) by lia. zstep.
    pose proof (lor_shr_lt _ 4 19 RB ltac:(lia) ltac:(lia)) as RC.
    zstep. rewrite (srliw_small _ 8 RC) by lia. zstep.
    pose proof (lor_shr_lt _ 8 19 RC ltac:(lia) ltac:(lia)) as RD.
    zstep. rewrite (srliw_small _ 16 RD) by lia. zstep.
    lazymatch goal with |- _ => let v := reg_val 15 in lazymatch v with Z_to_bv 64 ?e => change e with (smear32 rest) end end.
    rewrite (smear32_ok rest) by lia.
    clear RA RB RC RD.
    set (M := Z.log2 rest) in *.
    assert (HM : 0 <= M <= 11).
    { subst M. split; [apply Z.log2_nonneg|]. assert (Z.log2 rest < 12); [|lia]. apply Z.log2_lt_pow2; [lia|]. change (2^12) with 4096. lia. }
    assert (MSPEC : 2^M <= rest < 2^(M + 1)) by (subst M; pose proof (Z.log2_spec rest ltac:(lia)) as X; replace (Z.succ (Z.log2 rest)) with (Z.log2 rest + 1) in X by lia; exact X).
    clearbody M.
    do 18 zstep. zstep.
    lazymatch goal with |- _ => let v := reg_val 14 in lazymatch v with Z_to_bv 64 ?e =>
      replace e with (31 - M) by (clear - HM;
        assert (C : M = 0 \/ M = 1 \/ M = 2 \/ M = 3 \/ M = 4 \/ M = 5 \/ M = 6 \/ M = 7 \/ M = 8 \/ M = 9 \/ M = 10 \/ M = 11) by lia;
        repeat (destruct C as [E|C]; [rewrite E; vm_compute; reflexivity|]); rewrite C; vm_compute; reflexivity) end end.
    zstep. rsk_chk.
    zstep. zstep. zstep.
    lazymatch goal with |- _ => let v := reg_val 15 in lazymatch v with Z_to_bv 64 ?e =>
      replace e with (2^M) by (clear - HM;
        assert (C : M = 0 \/ M = 1 \/ M = 2 \/ M = 3 \/ M = 4 \/ M = 5 \/ M = 6 \/ M = 7 \/ M = 8 \/ M = 9 \/ M = 10 \/ M = 11) by lia;
        repeat (destruct C as [E|C]; [rewrite E; vm_compute; reflexivity|]); rewrite C; vm_compute; reflexivity) end end.
    zstep. if_cases K2; zify_cond K2.
    { replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 18446744073709551596) by (apply bv_eq; reflexivity).
      eapply (rs_exit_arr _ fj hw rank 18446744073709551596); [ | lia | reflexivity].
      unfold RSM. split; [exact HWC|]. split; [exact HWLEN|]. split; [exact HWBY|]. split; [exact RK|]. split; [exact RKLEN|].
      split; [do 2 eexists; exact NSC|]. split; [exact WKS|]. split; [exact STK|]. split; [exact FR|]. split; [exact MI|]. split; [exact MU| exact WM]. }
    zstep. rsk_chk.
    zstep. zstep. replace (32 - (31 - M)) with (M + 1) by lia.
    zstep. zstep. replace ((M + 1) ≪ 2) with (4 * (M + 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia). zstep.
    u8_sok HWC osz. zstep. u8_store HWC osz (M + 1).
    1: reflexivity.
    zstep. rsk_chk. zstep. rsk_chk.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u32_znth usegs m1 RS rank (M + 1) a RK ltac:(lia) ltac:(addr_tac)) as RD end.
    zstep.
    assert (RKB : forall w, 0 <= w <= 12 -> 0 <= Znth w rank <= 255).
    { intros w Hw. rewrite (proj2 RI w Hw). unfold hcount. pose proof (count_occ_bound Z.eq_dec w ws0). unfold FseNCount.Zlength in WS0L. lia. }
    pose proof (RKB (M + 1) ltac:(lia)) as RKM.
    rewrite (sx32w_small (Znth (M + 1) rank)) by lia.
    zstep. zstep. zstep.
    u32st RK (M + 1) (Znth (M + 1) rank + 1) (Znth (M + 1) rank + 1).
    change (upd_nat (Z.to_nat (M + 1)) (Znth (M + 1) rank + 1) rank) with (Zupd (M + 1) (Znth (M + 1) rank + 1) rank) in RK.
    pose proof (huf_stats_final ws0 rank wt0 (L + 1) (M + 1) FA ltac:(lia) RI eq_refl ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(replace (M + 1 - 1) with M by lia; lia)) as FIN.
    remember (Zupd (M + 1) (Znth (M + 1) rank + 1) rank) as rank' eqn:ERK'.
    assert (RKLEN' : Z.of_nat (length rank') = 13) by (subst rank'; rewrite Zupd_length; exact RKLEN).
    zstep. rsk_chk. zstep. zstep. rsk_chk.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u32_znth usegs m0 RS rank' 1 a RK ltac:(lia) ltac:(addr_tac)) as RD1 end.
    zstep.
    assert (R1 : 0 <= Znth 1 rank' <= 256).
    { destruct FIN as (_ & (_ & LEN') & _ & _ & CNT & _). rewrite (CNT 1 ltac:(lia)). unfold hcount.
      pose proof (count_occ_bound Z.eq_dec 1 (ws0 ++ [M + 1])). unfold FseNCount.Zlength in LEN'. lia. }
    rewrite (sx32w_small (Znth 1 rank')) by lia.
    zstep. zstep. if_cases K3; zify_cond K3.
    { replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 18446744073709551596) by (apply bv_eq; reflexivity).
      eapply (rs_exit_arr _ fj (Zupd osz (M + 1) hw) rank' 18446744073709551596); [ | lia | reflexivity].
      unfold RSM. split; [exact HWC|]. split; [rewrite Zupd_length; exact HWLEN|]. split; [apply Forall_Zupd; [exact HWBY | lia]|]. split; [exact RK|]. split; [exact RKLEN'|].
      split; [do 2 eexists; exact NSC|]. split; [exact WKS|]. split; [exact STK|]. split; [exact FR|]. split; [exact MI|]. split; [exact MU| exact WM]. }
    zstep.
    assert (LB : 0 <= Z.land (Znth 1 rank') 1 <= 1).
    { pose proof (Z.land_ones (Znth 1 rank') 1 ltac:(lia)) as E1. change (Z.ones 1) with 1 in E1. change (2^1) with 2 in E1. rewrite E1. Z.div_mod_to_equations; lia. }
    zstep. if_cases K4; zify_cond K4.
    { replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 18446744073709551596) by (apply bv_eq; reflexivity).
      eapply (rs_exit_arr _ fj (Zupd osz (M + 1) hw) rank' 18446744073709551596); [ | lia | reflexivity].
      unfold RSM. split; [exact HWC|]. split; [rewrite Zupd_length; exact HWLEN|]. split; [apply Forall_Zupd; [exact HWBY | lia]|]. split; [exact RK|]. split; [exact RKLEN'|].
      split; [do 2 eexists; exact NSC|]. split; [exact WKS|]. split; [exact STK|]. split; [exact FR|]. split; [exact MI|]. split; [exact MU| exact WM]. }
    zstep. rsk_chk. zstep. zstep. rsk_chk.
    zstep. zstep. zstep. zstep.
    assert (firstn_upd_nat_snoc : forall k v (l : list Z), (k < length l)%nat -> firstn (S k) (upd_nat k v l) = firstn k l ++ [v]).
    { clear. induction k as [|k IH]; intros v [|a l] H; cbn [length] in H; try lia; cbn [upd_nat firstn app]; [reflexivity|]. rewrite IH by lia. reflexivity. }
    do 7 zstep. zstep.
    apply stk_of_rw_cells in FR. cbn [cells_size csize Nat.add] in FR.
    assert (STK' : stk usegs m1 lo SPV).
    { apply (stk_merge usegs m1 lo (SPV + -64) SPV STK); [|lia]. replace SPV with (SPV + -64 + Z.of_nat 64) at 2 by lia. exact FR. }
    zstep. apply evt_done. unfold huf_rstats_post.
    do 14 eexists. exists m1, (isz + 1).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK'|].
    split; [exact WKS|]. split; [lia|]. left. split; [unfold zd_is_error, ZE_maxCode; apply Z.ltb_ge; lia|]. split; [lia|].
    exists (Zupd osz (M + 1) hw), rank', (L + 1), (osz + 1).
    split; [exact HWC|]. split; [rewrite Zupd_length; exact HWLEN|]. split; [apply Forall_Zupd; [exact HWBY | lia]|]. split; [exact RK|].
    split; [exact NSC|]. split; [|lia].
    replace (firstn (Z.to_nat (osz + 1)) (Zupd osz (M + 1) hw)) with (ws0 ++ [M + 1]); [exact FIN|].
    unfold Zupd, ws0. replace (Z.to_nat (osz + 1)) with (S (Z.to_nat osz)) by lia. rewrite firstn_upd_nat_snoc by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Notation STL pc mm x1 x5 x6 x7 isz x14 x17 osz x28 x29 x30 x31 :=
    (STF pc mm x1 x5 x6 x7 (Z_to_bv 64 RS) (Z_to_bv 64 HW) (Z_to_bv 64 (-20)) (Z_to_bv 64 NSP) (Z_to_bv 64 (Z.lxor HW 18446744073709551615)) (Z_to_bv 64 (NSP + 4))
         x14 (Z_to_bv 64 1) (Z_to_bv 64 12) x17 (Z_to_bv 64 osz) (Z_to_bv 64 isz) (Z_to_bv 64 (NSP + 4)) (Z_to_bv 64 NSP) x28 x29 x30 x31).
  Lemma rs_loop : forall k m1 fj hw rank isz osz i x1 x7 x28 x29 x30 x31,
    Z.to_nat (osz - i) = k ->
    RSM fj hw rank m1 -> rank_inv (firstn (Z.to_nat i) hw) rank -> Forall (fun w => 0 <= w <= 12) (firstn (Z.to_nat i) hw) ->
    0 <= i < osz -> osz <= 255 -> 0 <= isz -> isz + 1 <= n ->
    evt usegs POST (STL 0x2a41c m1 x1 (Z_to_bv 64 (i + 1)) (Z_to_bv 64 i) x7 isz (Z_to_bv 64 (hw_total (firstn (Z.to_nat i) hw))) (Z_to_bv 64 30) osz x28 x29 x30 x31).
  Proof.
  induction k as [|k IH]; intros until x31; intros EK I RI FA IR OSR ISZ0 ISZN; [exfalso; lia|].
  open_rsm I.
  set (ws0 := firstn (Z.to_nat i) hw) in *.
  assert (WS0L : FseNCount.Zlength ws0 = i) by (unfold FseNCount.Zlength, ws0; rewrite length_firstn; lia).
  pose proof (hw_total_bound ws0 FA) as WTB. pose proof (hw_total_nonneg ws0) as WT0.
  remember (hw_total ws0) as wt0 eqn:EWT.
  assert (WSN : firstn (Z.to_nat (i + 1)) hw = ws0 ++ [Znth i hw]).
  { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. unfold ws0, Znth. apply FseNCountRT.firstn_S_nth. lia. }
  pose proof (Forall_Znth _ hw i HWBY ltac:(lia)) as WB. cbv beta in WB.
  remember (Znth i hw) as w eqn:EW.
  zstep. rsk_chk. zstep.
  lazymatch goal with |- _ => let a := cur_mem_addr in
    pose proof (u8_znth usegs m1 HW hw i a HWC ltac:(lia) ltac:(addr_tac)) as RD end.
  rewrite <- EW in RD.
  zstep. cbv beta. rewrite (byte_lit w) by lia.
  zstep. if_cases K0; zify_cond K0.
  { replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 18446744073709551596) by (apply bv_eq; reflexivity).
    eapply (rs_exit_arr _ fj hw rank 18446744073709551596); [ | lia | reflexivity].
    unfold RSM. split; [exact HWC|]. split; [exact HWLEN|]. split; [exact HWBY|]. split; [exact RK|]. split; [exact RKLEN|].
    split; [do 2 eexists; exact NSC|]. split; [exact WKS|]. split; [exact STK|]. split; [exact FR|]. split; [exact MI|]. split; [exact MU| exact WM]. }
  zstep. replace (w ≪ 2) with (4 * w) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep. zstep. rsk_chk. zstep. rsk_chk.
  lazymatch goal with |- _ => let a := cur_mem_addr in
    pose proof (u32_znth usegs m1 RS rank w a RK ltac:(lia) ltac:(addr_tac)) as RD2 end.
  zstep.
  assert (RKW : 0 <= Znth w rank <= 255).
  { rewrite (proj2 RI w ltac:(lia)). unfold hcount. pose proof (count_occ_bound Z.eq_dec w ws0). unfold FseNCount.Zlength in WS0L. lia. }
  rewrite (sx32w_small (Znth w rank)) by lia.
  zstep.
  u32st RK w (Znth w rank + 1) (Znth w rank + 1).
  change (upd_nat (Z.to_nat w) (Znth w rank + 1) rank) with (Zupd w (Znth w rank + 1) rank) in RK.
  pose proof (rank_inv_step ws0 rank w RI ltac:(lia)) as RI'.
  remember (Zupd w (Znth w rank + 1) rank) as rank' eqn:ERK'.
  assert (RKLEN' : Z.of_nat (length rank') = 13) by (subst rank'; rewrite Zupd_length; exact RKLEN).
  lazymatch goal with |- _ => let a := cur_mem_addr in
    pose proof (u8_znth usegs m0 HW hw i a HWC ltac:(lia) ltac:(addr_tac)) as RD end.
  rewrite <- EW in RD.
  zstep. cbv beta. rewrite (byte_lit w) by lia.
  zstep. rsk_chk.
  zstep. rewrite (sllw_pow2 w) by lia.
  assert (HC : 2^w ≫ 1 = hw_cells w).
  { clear - K0 WB. assert (C : w = 0 \/ w = 1 \/ w = 2 \/ w = 3 \/ w = 4 \/ w = 5 \/ w = 6 \/ w = 7 \/ w = 8 \/ w = 9 \/ w = 10 \/ w = 11 \/ w = 12) by lia.
    repeat (destruct C as [E|C]; [rewrite E; vm_compute; reflexivity|]). rewrite C. vm_compute. reflexivity. }
  pose proof (hw_cells_bound w ltac:(lia)) as HCB. pose proof (hw_cells_nonneg w) as HC0.
  assert (PW : 1 <= 2^w <= 4096) by (split; [pose proof (Z.pow_pos_nonneg 2 w ltac:(lia) ltac:(lia)); lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
  zstep. try rewrite (Z.mod_small (2^w)) by lia. rewrite (rsk_srliw (2^w) 1) by lia. rewrite HC.
  zstep. rewrite (swrap32_small (hw_cells w + wt0)) by lia.
  zstep. zstep. rewrite (Z.mod_small (i + 1) 4294967296) by lia.
  zstep.
  assert (WT' : hw_total (firstn (Z.to_nat (i + 1)) hw) = hw_cells w + wt0) by (rewrite WSN, hw_total_app; cbn [hw_total]; lia).
  assert (FA' : Forall (fun w => 0 <= w <= 12) (firstn (Z.to_nat (i + 1)) hw)) by (rewrite WSN; apply Forall_app; split; [exact FA | constructor; [lia | constructor]]).
  rewrite <- WSN in RI'.
  assert (I' : RSM fj hw rank' m0).
  { unfold RSM. split; [exact HWC|]. split; [exact HWLEN|]. split; [exact HWBY|]. split; [exact RK|]. split; [exact RKLEN'|].
    split; [do 2 eexists; exact NSC|]. split; [exact WKS|]. split; [exact STK|]. split; [exact FR|]. split; [exact MI|]. split; [exact MU| exact WM]. }
  zstep. if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    rewrite <- WT'.
    replace (Z_to_bv 64 (i + 2)) with (Z_to_bv 64 (i + 1 + 1)) by (f_equal; lia).
    eapply (IH m0 fj hw rank' isz osz (i + 1)); try eassumption; lia.
  - (* [comment removed for export] *)
    assert (EO : osz = i + 1) by lia. rewrite <- WT'. rewrite <- EO in *.
    eapply (rs_final m0 fj hw rank' isz osz); try eassumption; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rs_count : forall m1 fj isz osz x1 x5 x6 x7 x10 x11 x12 x15 x16 x17 x20 x21 x28 x29 x30 x31,
    stk usegs m1 HW (HW + 256) -> stk usegs m1 RS (RS + 52) -> stk usegs m1 NSP (NSP + 8) -> stk usegs m1 WK (WK + wksz) ->
    stk usegs m1 lo (SPV + -64) -> rw_cells usegs m1 (SPV + -64) (FRAME fj) ->
    mem_inv usegs m1 -> munch MUNCH m m1 -> wmono usegs m m1 ->
    0 <= osz <= 255 -> 0 <= isz -> isz + 1 <= n ->
    evt usegs POST (STF 0x2a3d4 m1 x1 x5 x6 x7 (Z_to_bv 64 RS) (Z_to_bv 64 HW) x10 x11 x12 (Z_to_bv 64 NSP) (Z_to_bv 64 (NSP + 4))
                        x15 x16 x17 (Z_to_bv 64 osz) (Z_to_bv 64 isz) x20 x21 x28 x29 x30 x31).
  Proof.
  intros until x31; intros HWS RSS NSS WKS STK FR MI MU WM OSR ISZ0 ISZN.
  do 5 zstep. zstep.
  destruct (stk_open usegs _ RS (RS + 52) RS 52%nat RSS ltac:(lia) ltac:(lia)) as (jr & RSC & _ & _).
  eapply evt_cut.
  { eapply (memset_spec _ _ gp tp _ _ _ _ _ (Z_to_bv 64 RS) (Z_to_bv 64 0) (Z_to_bv 64 52) _ _ _ _ _ _ _ _ _ _ _ s8 s9 s10 s11 _ _ _ _ F fc m1 jr); [|eassumption].
    rewrite !unsigned_lit by lia. exact RSC. }
  unfold memset_post. rewrite !unsigned_lit by lia. post_call usegs m1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RK : u32arr usegs mm RS (map (Z_to_bv 64) (repeat 0 13))) end.
  { apply u8arr_of_rw_cells in POST. destruct POST as [Hb Hw]. split.
    - replace (u32s (map (Z_to_bv 64) (repeat 0 13))) with (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 52)) by (vm_compute; reflexivity). exact Hb.
    - rewrite repeat_length in Hw. rewrite length_map, repeat_length. exact Hw. }
  clear POST.
  (* [comment removed for export] *)
  destruct (stk_open usegs _ HW (HW + 256) HW 256%nat HWS ltac:(lia) ltac:(lia)) as (hwb & HWC & _ & _).
  assert (HWBL : length hwb = 256%nat) by (destruct HWC as [[WF _] _]; cbn in WF; destruct WF as [LJ _]; exact LJ).
  apply u8arr_of_rw_cells in HWC. rewrite <- (bytes_of_unsigned hwb) in HWC.
  remember (map bv_unsigned hwb) as hw eqn:EHW.
  assert (HWL : Z.of_nat (length hw) = 256) by (subst hw; rewrite length_map; lia).
  assert (HWBY : Forall (fun c => 0 <= c < 256) hw) by (subst hw; apply bytes_unsigned_range).
  clear EHW HWBL.
  (* [comment removed for export] *)
  destruct (stk_open usegs _ NSP (NSP + 8) NSP 8%nat NSS ltac:(lia) ltac:(lia)) as (jn & NSC & _ & _).
  apply (rw_cells_split_CB usegs _ _ [] 8 jn [] [4; 4]%nat) in NSC; [| reflexivity]. cbn [mk_CB_cells app] in NSC.
  lazymatch type of NSC with rw_cells _ _ _ (CB 4 ?j :: ?post) => destruct (hcb4_as_c4 usegs _ _ [] j post NSC) as [wn NSC1] end. cbn [app] in NSC1. clear NSC.
  lazymatch type of NSC1 with rw_cells _ _ _ (?c0 :: CB 4 ?j :: ?post) => destruct (hcb4_as_c4 usegs _ _ [c0] j post NSC1) as [wt NSC] end. cbn [app] in NSC. clear NSC1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (I : RSM fj hw (repeat 0 13) mm) end.
  { unfold RSM. split; [exact HWC|]. split; [exact HWL|]. split; [exact HWBY|]. split; [exact RK|]. split; [reflexivity|].
    split; [do 2 eexists; exact NSC|]. split; [exact WKS|]. split; [exact STK|]. split; [exact FR|]. split; [assumption|]. split; [exact MU| exact WM]. }
  zstep. zstep. if_cases K4; zify_cond K4.
  { replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 18446744073709551596) by (apply bv_eq; reflexivity).
    eapply (rs_exit_arr _ fj hw (repeat 0 13) 18446744073709551596); [exact I | lia | reflexivity]. }
  zstep. rsk_chk.
  do 9 zstep.
  eapply (rs_loop (Z.to_nat osz) _ fj hw (repeat 0 13) isz osz 0); try eassumption; try lia.
  - exact rank_inv_nil.
  - constructor.
  Qed.

  (* [comment removed for export] *)
  Lemma rs_direct : forall j m1 fj out isz osz K k x1 x5 x6 x7 x17 x19 x20 x21 x28 x29 x30 x31,
    (Z.to_nat (K - k) < j)%nat ->
    u8arr usegs m1 HW out -> Z.of_nat (length out) = 256 -> bytes_at usegs m1 SRC src ->
    stk usegs m1 RS (RS + 52) -> stk usegs m1 NSP (NSP + 8) -> stk usegs m1 WK (WK + wksz) ->
    stk usegs m1 lo (SPV + -64) -> rw_cells usegs m1 (SPV + -64) (FRAME fj) ->
    mem_inv usegs m1 -> munch MUNCH m m1 -> wmono usegs m m1 ->
    0 <= k <= K -> 2 * K + 1 <= osz <= 2 * K + 2 -> osz <= 255 -> 1 + K < n -> 0 <= isz -> isz + 1 <= n ->
    evt usegs POST (STF 0x2a37c m1 x1 x5 x6 x7 (Z_to_bv 64 RS) (Z_to_bv 64 HW) (Z_to_bv 64 (2 * k)) (Z_to_bv 64 (Z.lxor HW 18446744073709551615))
                        (Z_to_bv 64 isz) (Z_to_bv 64 NSP) (Z_to_bv 64 (NSP + 4)) (Z_to_bv 64 (SRC + 1)) (Z_to_bv 64 (2 * k)) x17 (Z_to_bv 64 osz) x19 x20 x21 x28 x29 x30 x31).
  Proof.
  induction j as [|j IH]; intros until x31; intros EJ OUT OLEN SRCB RSS NSS WKS STK FR MI MU WM KR KO K255 KN ISZ0 ISZN; [exfalso; lia|].
  all: zstep; rewrite (rsk_srliw_dbl k) by lia; zstep; zstep; rsk_chk; zstep; rsk_chk;
       lbyte SRCB; zstep; zstep; outst OUT OLEN; zstep; rsk_chk; zstep; zstep; zstep;
       rewrite (Z.mod_small (2 * k + 1)) by lia; zstep; rsk_chk; lbyte SRCB; zstep; zstep;
       rewrite (swrap32_small (2 * k + 2)) by lia; zstep; outst OUT OLEN; zstep; zstep;
       rewrite (Z.mod_small (2 * k + 2)) by lia; zstep; if_cases KB; zify_cond KB.
  - replace (Z_to_bv 64 (2 * k + 2)) with (Z_to_bv 64 (2 * (k + 1))) by (f_equal; lia).
    eapply (IH _ fj out1 isz osz K (k + 1)); try eassumption; lia.
  - zstep. apply rw_cells_of_u8arr in OUT. apply stk_of_rw_cells in OUT. cbn [cells_size csize] in OUT.
    replace (HW + Z.of_nat (length out1 + 0)) with (HW + 256) in OUT by lia.
    eapply (rs_count _ fj isz osz); try eassumption; lia.
  Qed.

  Theorem huf_rstats_body : forall (t0 t1 t2 t3 t4 t5 t6 : word),
    mem_inv usegs m -> stk usegs m lo SPV -> bytes_at usegs m SPV (le8 (Z_to_bv 64 wksz)) ->
    stk usegs m HW (HW + 256) -> stk usegs m RS (RS + 52) -> stk usegs m NSP (NSP + 8) ->
    bytes_at usegs m SRC src -> stk usegs m WK (WK + wksz) ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 HW) (Z_to_bv 64 256) (Z_to_bv 64 RS) (Z_to_bv 64 NSP)
               (Z_to_bv 64 (NSP + 4)) (Z_to_bv 64 SRC) (Z_to_bv 64 n) (Z_to_bv 64 WK) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PHUF_RSTATS) fc None m (seg_rom usegs)).
  Proof.
    intros t0 t1 t2 t3 t4 t5 t6 MI STK WSZB HWS RSS NSS SRCB WKS. unfold PHUF_RSTATS.
    assert (MU : munch MUNCH m m) by apply munch_refl.
    assert (WM : wmono usegs m m) by apply wmono_refl.
    zstep. carve_frame 64%nat STK.
    do 7 zstep. do 2 zstep.
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j :: _) => generalize dependent j; intros fj FR end.
    assert (NN : 0 <= n) by (clear - SRCLEN; lia).
    (* [comment removed for export] *)
    pose proof SRCB as SRCZ. rewrite <- (bytes_of_unsigned src) in SRCZ.
    remember (map bv_unsigned src) as buf eqn:EBUF.
    assert (BUFL : Z.of_nat (length buf) = n) by (subst buf; rewrite length_map; exact SRCLEN).
    assert (BUFB : Forall (fun c => 0 <= c < 256) buf) by (subst buf; apply bytes_unsigned_range).
    clear EBUF.
    zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      replace (Z_to_bv 64 (-72)) with (Z_to_bv 64 18446744073709551544) by (apply bv_eq; reflexivity).
      eapply (rs_exit_err _ _ 18446744073709551544); try eassumption; [lia | reflexivity]. }
    zstep. rsk_chk. zstep.
    assert (RB0 : 0 <= Znth 0 buf < 256) by (apply (Forall_Znth _ buf 0 BUFB); lia).
    replace (Z_to_bv 64 SRC) with (Z_to_bv 64 (SRC + 0)) by (f_equal; lia).
    zlbs SRCZ BUFB 0.
    clear H. set (c0 := Znth 0 buf) in *. unfold sx8.
    destruct (Z.ltb_spec c0 128) as [C128|C128].
    { (* [comment removed for export] *)
      zstep.
      replace (Z.land c0 255) with c0 by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; rewrite Z.mod_small; lia).
      clearbody c0.
      zstep. if_cases K1; zify_lts K1; [exfalso; lia|].
      zstep. if_cases K2; zify_cond K2.
      { replace (Z_to_bv 64 (-72)) with (Z_to_bv 64 18446744073709551544) by (apply bv_eq; reflexivity).
        eapply (rs_exit_err _ _ 18446744073709551544); try eassumption; [lia | reflexivity]. }
      zstep. zstep. rsk_chk.
      assert (RDW : ov_read_bytes usegs m0 (Z_to_bv 64 (SPV + -64 + 64)) 8 = Some (le8 (Z_to_bv 64 wksz))).
      { pose proof (bytes_at_read usegs m0 SPV (le8 (Z_to_bv 64 wksz)) 0 8 WSZB ltac:(lia) ltac:(rewrite length_le8; cbn; lia)) as RD.
        rewrite skipn_O in RD. rewrite firstn_all2 in RD by (rewrite length_le8; lia).
        unfold wa in RD. replace (SPV + -64 + 64) with (SPV + 0) by lia. exact RD. }
      zstep.
      clear RDW. do 9 zstep. zstep.
      destruct (stk_split usegs _ HW (HW + 255) (HW + 256) HWS ltac:(lia)) as [HWA HWZ].
      assert (SUBB : bytes_at usegs m0 (SRC + 1) (firstn (Z.to_nat c0) (skipn 1 src))).
      { pose proof SRCB as SB. rewrite <- (firstn_skipn 1 src) in SB. apply bytes_at_app in SB. destruct SB as [_ SB].
        rewrite length_firstn in SB. replace (SRC + Z.of_nat (Nat.min 1 (length src))) with (SRC + 1) in SB by lia.
        rewrite <- (firstn_skipn (Z.to_nat c0) (skipn 1 src)) in SB. apply bytes_at_app in SB. exact (proj1 SB). }
      assert (SUBL : Z.of_nat (length (firstn (Z.to_nat c0) (skipn 1 src))) = c0) by (rewrite length_firstn, length_skipn; lia).
      remember (firstn (Z.to_nat c0) (skipn 1 src)) as sub eqn:ESUB. clear ESUB.
      eapply evt_cut.
      { eapply (FDEC _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ s8 s9 s10 s11 _ _ _ _ F fc m0 (SPV + -64) HW 255 (SRC + 1) c0 6 WK wksz lo sub);
          try eassumption; try exact (rsk_al_e _ _ WK4); try exact (rsk_al_add SPV 16 (-64) eq_refl SPV16 eq_refl);
          try lia; try (Z.div_mod_to_equations; lia). }
      unfold fse_dec_post. post_call usegs m0.
      rename x14 into rd. rename PC into STK'. rename PC0 into HWA'. rename PC1 into WKS'. rename PC2 into RDR.
      assert (HWS' : stk usegs x13 HW (HW + 256)) by (apply (stk_merge usegs _ HW (HW + 255) (HW + 256) HWA' HWZ); lia).
      do 4 zstep. zstep. if_cases K3; zify_cond K3.
      2:{ (* [comment removed for export] *)
          zstep. eapply (rs_exit_err _ _ rd); try eassumption.
          unfold zd_is_error, ZE_maxCode. apply Z.ltb_lt. lia. }
      destruct POST as [RE|RLE]; [exfalso; unfold zd_is_error, ZE_maxCode in RE; apply Z.ltb_lt in RE; lia|].
      eapply (rs_count _ fj c0 rd); try eassumption; lia. }
    (* [comment removed for export] *)
    zstep.
    replace (Z.land ((c0 - 256) mod 18446744073709551616) 255) with c0
      by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; change (2^8) with 256; clear - RB0 C128; Z.div_mod_to_equations; lia).
    clearbody c0.
    zstep. if_cases K1; zify_lts K1; [|exfalso; lia].
    zstep. zstep.
    replace ((c0 + -126) ≫ 1) with ((c0 - 126) / 2) by (rewrite Z.shiftr_div_pow2 by lia; change (2^1) with 2; f_equal; lia).
    assert (IQ : 1 <= (c0 - 126) / 2 <= 64 /\ 2 * ((c0 - 126) / 2) <= c0 - 126 <= 2 * ((c0 - 126) / 2) + 1) by (clear - RB0 C128; Z.div_mod_to_equations; lia).
    remember ((c0 - 126) / 2) as isz eqn:EISZ. clear EISZ.
    zstep. if_cases K2; zify_cond K2.
    { replace (Z_to_bv 64 (-72)) with (Z_to_bv 64 18446744073709551544) by (apply bv_eq; reflexivity).
      eapply (rs_exit_err _ _ 18446744073709551544); try eassumption; [lia | reflexivity]. }
    zstep. zstep. zstep. if_cases K3; zify_cond K3; [exfalso; lia|].
    zstep. zstep. rsk_chk.
    zstep. if_cases K4; zify_cond K4; [exfalso; lia|].
    zstep. rsk_chk.
    do 4 zstep.
    destruct (stk_open usegs _ HW (HW + 256) HW 256%nat HWS ltac:(lia) ltac:(lia)) as (out & OUTC & _ & _).
    assert (OLEN : Z.of_nat (length out) = 256) by (destruct OUTC as [[WF _] _]; cbn in WF; destruct WF as [LJ _]; lia).
    apply u8arr_of_rw_cells in OUTC.
    eapply (rs_direct (S (Z.to_nat (isz - 1))) _ fj out isz (c0 + -127) (isz - 1) 0); try eassumption; lia.
  Qed.
End RSTATS.

(* [comment removed for export] *)
Theorem huf_rstats_proof : fse_dec_stmt -> huf_rstats_stmt.
Proof.
  intros FDEC. unfold huf_rstats_stmt. intros.
  eapply (huf_rstats_body FDEC); try eassumption; apply rsk_al_i; assumption.
Qed.
