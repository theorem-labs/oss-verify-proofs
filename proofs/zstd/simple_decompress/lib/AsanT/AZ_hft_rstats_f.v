(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require FseNCountRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree StrFun WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AFake_iface AFakeK_iface
     AZ_kit AZ_fkit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface AZ_hft_rs_iface AZ_libc_iface AZ_libc AZ_kx AZ_hft_rs_defs AZ_hft_rstats_a.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.
(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_hide segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_hide segs m a bs.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_hide segs m m' MU WM.

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

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Lemma shspan_4 : forall A, A mod 4 = 0 -> shspan A 4 = 1.
Proof. intros A H. unfold shspan. Z.div_mod_to_equations. lia. Qed.

Section RS.
  Variables (AI : AMallocIface) (fflag : alayout -> Z -> Z -> Z) (rng_fs : alayout -> footprint -> Prop).
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem).
  Variables (SPV lo HW RS NBP TLP SRC n WK wksz B bsz : Z).
  Hypothesis HY : rsA_hyps RNG SPV lo HW RS NBP TLP SRC n WK wksz B bsz.
  Hypothesis LBH : ablkLB LB.
  Hypothesis INB : ainblk LB B bsz.
  Hypothesis INNB : ainblk LB NBP 4.
  Hypothesis INTL : ainblk LB TLP 4.
  Hypothesis HULLB : ahull RNG m B bsz.
  Notation POST := (huf_rstats_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV HW RS NBP TLP n WK wksz lo m).
  Notation MUNCH := ([(HW, HW + 256); (RS, RS + 52); (NBP, NBP + 4); (TLP, TLP + 4); (WK, WK + wksz); (SPV - 5056, SPV)] ++ fake_area L).
  Notation WL := [(HW, HW + 256); (RS, RS + 52); (NBP, NBP + 4); (TLP, TLP + 4); (WK, WK + wksz)].
  Notation STF pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -64)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation FRAME := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation KZB := [KZRange SPV (0x10007fff8000 + 5056) (2^47 - 16); KZRange HW 4096 (2^47 - 256); KZRange RS 4096 (2^47 - 52);
     KZRange NBP 4096 (2^47 - 12); KZRange TLP 4096 (2^47 - 12); KZRange B 4096 (2^47); KZRange (B + bsz) 4096 (2^47);
     KZAlign NBP 4; KZAlign TLP 4; KZAlign RS 4; KZAlign WK 4] (only parsing).
  (* [comment removed for export] *)
  Local Ltac rs_seps BNB BTL BSRC OFFB OFFNB OFFTL BRS RSHW RSWK HWB WKB LOS WKSZ0 :=
    assert (SHNB : HW + 256 <= NBP \/ NBP + 4 <= HW) by (clear - BNB BRS RSHW HWB; lia);
    assert (SRNB : RS + 52 <= NBP \/ NBP + 4 <= RS) by (clear - BNB BRS RSHW HWB; lia);
    assert (SHTL : HW + 256 <= TLP \/ TLP + 4 <= HW) by (clear - BTL BRS RSHW HWB; lia);
    assert (SRTL : RS + 52 <= TLP \/ TLP + 4 <= RS) by (clear - BTL BRS RSHW HWB; lia);
    assert (SHF : HW + 256 <= SPV + -64 \/ SPV <= HW) by (clear - OFFB BRS RSHW HWB LOS; lia);
    assert (SRF : RS + 52 <= SPV + -64 \/ SPV <= RS) by (clear - OFFB BRS RSHW HWB LOS; lia);
    assert (SHL : HW + 256 <= lo \/ SPV <= HW) by (clear - OFFB BRS RSHW HWB LOS; lia);
    assert (SRL : RS + 52 <= lo \/ SPV <= RS) by (clear - OFFB BRS RSHW HWB LOS; lia);
    assert (SWF : WK + wksz <= SPV + -64 \/ SPV <= WK) by (clear - OFFB BRS RSWK WKB LOS WKSZ0; lia);
    assert (SWL : WK + wksz <= lo \/ SPV <= WK) by (clear - OFFB BRS RSWK WKB LOS WKSZ0; lia);
    assert (SWNB : WK + wksz <= NBP \/ NBP + 4 <= WK) by (clear - BNB BRS RSWK WKB WKSZ0; lia);
    assert (SWTL : WK + wksz <= TLP \/ TLP + 4 <= WK) by (clear - BTL BRS RSWK WKB WKSZ0; lia);
    assert (SHS : HW + 256 <= SRC \/ SRC + n <= HW) by (clear - BSRC BRS RSHW HWB; lia);
    assert (SRS : RS + 52 <= SRC \/ SRC + n <= RS) by (clear - BSRC BRS RSHW HWB; lia);
    assert (SHR : HW + 256 <= RS \/ RS + 52 <= HW) by (clear - RSHW; lia);
    assert (SNBF : NBP + 4 <= SPV + -64 \/ SPV <= NBP) by (clear - OFFNB LOS; lia);
    assert (STLF : TLP + 4 <= SPV + -64 \/ SPV <= TLP) by (clear - OFFTL LOS; lia).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section PostJoin.
  Variable mj : amem.
  Hypothesis UBj : unpoisoned mj B (B + bsz).
  Hypothesis UNBj : unpoisoned mj NBP (NBP + 4).
  Hypothesis UTLj : unpoisoned mj TLP (TLP + 4).
  Hypothesis ARTj : art mj.
  Hypothesis AHj : AHEAP AI L RNG st LB mj.
  Hypothesis MU0j : munch MUNCH m mj.
  Hypothesis WM0j : wmono bsegs m mj.
  Hypothesis FFR0j : ffr_pres WL LB m mj.
  Notation RSMj := (RSM ra s0 s1 s2 s3 s4 s5 s6 mj SPV lo HW RS NBP TLP WK wksz).
  Notation WJ := [(HW, HW + 256); (RS, RS + 52); (NBP, NBP + 4); (TLP, TLP + 4); (SPV - 2272, SPV)].
  Notation CB := (rs_cellbands LB NBP TLP LBH INNB INTL).
  Local Ltac rs_reunp :=
    repeat match goal with H : unpoisoned ?mx _ _ |- _ => lazymatch mx with mj => fail | _ => clear H end end;
    repeat match goal with H : art ?mx |- _ => lazymatch mx with mj => fail | _ => clear H end end;
    repeat match goal with H : rt_got _ |- _ => clear H | H : rt_got_ric _ |- _ => clear H | H : rt_shbase _ |- _ => clear H
                         | H : rt_inited _ |- _ => clear H | H : rt_layout _ |- _ => clear H | H : rt_real_mem _ |- _ => clear H end;
    lazymatch goal with
    | MU : munch _ mj ?m2, WM : wmono bsegs mj ?m2 |- _ =>
        pose proof (rs_unp_bM _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UBj CB m2 MU) as UB1;
        pose proof (rs_unp_nbM _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UNBj CB m2 MU) as UNB1;
        pose proof (rs_unp_tlM _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UTLj CB m2 MU) as UTL1;
        pose proof (rs_artM _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY ARTj CB m2 MU WM) as ART1;
        destruct ART1 as (GOT1 & RIC1 & SHB1 & INI1 & LAY1 & REAL1)
    end.
  Local Ltac kx_chk AKS STOP KX REGS :=
    kx_autoFLAc tt AKS [STOP] 24%nat (KZB ++ KX) (@nil (Z * Z)) (@nil (Z * Z));
    [ .. | kx_mem; kx_gen_regsF REGS; kx_tidy_run ]; try kx_z.
  (* [comment removed for export] *)
  Local Ltac rs_rd H :=
    kx_side_pre;
    lazymatch goal with
    | KXA : atoms_ok ?zs ?E |- rd_ok ?segs ?mm _ ?a ?nn =>
        let nz := kx_len zs in
        let P := kx_rd_fact segs mm H in
        eapply (kx_rd_ok segs mm E a nn _ _ P); kx_estarts E zs nz KXA; rewrite ?length_map, ?u32s_length; kx_lia
    end.
  (* [comment removed for export] *)
  Notation RS_EXIT_ARR := (rs_exit_arr AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo HW RS NBP TLP SRC n WK wksz B bsz
                             HY LBH INB INNB INTL mj AHj MU0j WM0j FFR0j).
  Notation RS_EXIT_OK := (rs_exit_ok AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo HW RS NBP TLP SRC n WK wksz B bsz
                             HY LBH INB INNB INTL mj AHj MU0j WM0j FFR0j).

  (* [comment removed for export] *)
  Lemma rs_final : forall m1 hw rank (wn wt : word) isz osz x1 x5 x6 x7 x13 x14 x15 x17 x28 x29 x30 x31,
    RSMj hw rank wn wt m1 -> rank_inv (firstn (Z.to_nat osz) hw) rank -> Forall (fun w => 0 <= w <= 12) (firstn (Z.to_nat osz) hw) ->
    1 <= osz <= 255 -> 0 <= isz -> isz + 1 <= n ->
    evtF bsegs RNG POST
      (STF 0xab4d0 m1 x1 x5 x6 x7 (Z_to_bv 64 RS) (Z_to_bv 64 osz) (Z_to_bv 64 (-20)) (Z_to_bv 64 NBP) (Z_to_bv 64 TLP) x13 x14 x15
           (Z_to_bv 64 (hw_total (firstn (Z.to_nat osz) hw))) x17 (Z_to_bv 64 isz) (Z_to_bv 64 HW) (Z_to_bv 64 2147450880)
           (Z_to_bv 64 TLP) (Z_to_bv 64 NBP) x28 x29 x30 x31).
  Proof.
    intros until x31; intros I RINV FA OSR ISZ0 ISZN. open_rsm I. open_hy HY.
    pose proof CB as (CB1 & CB2 & CB3 & CB4 & CB5 & CB6). rs_reunp.
    rs_seps BNB BTL BSRC OFFB OFFNB OFFTL BRS RSHW RSWK HWB WKB LOS WKSZ0. hide_all_disj.
    set (ws0 := firstn (Z.to_nat osz) hw) in *.
    assert (WS0L : FseNCount.Zlength ws0 = osz) by (unfold FseNCount.Zlength, ws0; rewrite length_firstn; clear - OSR HWLEN; lia).
    pose proof (hw_total_bound ws0 FA) as WTB. pose proof (hw_total_nonneg ws0) as WT0.
    set (wt0 := hw_total ws0) in *.
    assert (WTR : 0 <= wt0 < 524288) by (clear - WTB WT0 WS0L OSR; lia).
    zstep. if_cases K0; zify_cond K0.                                          (* [comment removed for export] *)
    { replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 18446744073709551596) by (apply bv_eq; reflexivity).
      eapply (RS_EXIT_ARR _ hw rank wn wt 18446744073709551596); [ close_rsm | clear; lia | reflexivity]. }
    zstep.                                                                     (* [comment removed for export] *)
    assert (srliw_small : forall x k, 0 <= x < 2^19 -> 0 <= k -> bv_swrap 32 (bv_wrap 32 x ≫ k) = x ≫ k).
    { clear. intros x k Hx Hk. change (2^19) with 524288 in Hx. rewrite wrap32_small by lia. apply swrap32_small.
      assert (0 <= x ≫ k) by (apply Z.shiftr_nonneg; lia).
      assert (x ≫ k <= x) by (rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk); Z.div_mod_to_equations; nia). lia. }
    assert (RW : 0 <= wt0 < 2^19) by (change (2^19) with 524288; exact WTR).
    rewrite (srliw_small wt0 1 RW) by lia.
    zstep. zstep. zstep.                                                       (* [comment removed for export] *)
    pose proof (lor_shr_lt wt0 1 19 RW ltac:(lia) ltac:(lia)) as RA.
    zstep. rewrite (srliw_small _ 2 RA) by lia. zstep.
    pose proof (lor_shr_lt _ 2 19 RA ltac:(lia) ltac:(lia)) as RB'.
    zstep. rewrite (srliw_small _ 4 RB') by lia. zstep.
    pose proof (lor_shr_lt _ 4 19 RB' ltac:(lia) ltac:(lia)) as RC.
    zstep. rewrite (srliw_small _ 8 RC) by lia. zstep.
    pose proof (lor_shr_lt _ 8 19 RC ltac:(lia) ltac:(lia)) as RD.
    zstep. rewrite (srliw_small _ 16 RD) by lia. zstep.
    lazymatch goal with |- _ => let v := reg_val 13 in lazymatch v with Z_to_bv 64 ?e => change e with (smear32 wt0) end end.
    rewrite (smear32_ok wt0) by lia.
    clear RA RB' RC RD.
    set (HB := Z.log2 wt0) in *.
    assert (HL : 0 <= HB <= 18).
    { subst HB. split; [apply Z.log2_nonneg|]. assert (Z.log2 wt0 < 19); [|lia]. apply Z.log2_lt_pow2; lia. }
    assert (LSPEC : 2^HB <= wt0 < 2^(HB + 1)) by (subst HB; pose proof (Z.log2_spec wt0 ltac:(lia)) as X; replace (Z.succ (Z.log2 wt0)) with (Z.log2 wt0 + 1) in X by lia; exact X).
    clearbody HB.
    do 19 zstep.                                                               (* [comment removed for export] *)
    lazymatch goal with |- _ => let v := reg_val 13 in lazymatch v with Z_to_bv 64 ?e =>
      replace e with (31 - HB) by (clear - HL;
        assert (C : HB = 0 \/ HB = 1 \/ HB = 2 \/ HB = 3 \/ HB = 4 \/ HB = 5 \/ HB = 6 \/ HB = 7 \/ HB = 8 \/ HB = 9 \/ HB = 10 \/ HB = 11 \/ HB = 12
                    \/ HB = 13 \/ HB = 14 \/ HB = 15 \/ HB = 16 \/ HB = 17 \/ HB = 18) by lia;
        repeat (destruct C as [E|C]; [rewrite E; vm_compute; reflexivity|]); rewrite C; vm_compute; reflexivity) end end.
    zstep.                                                                     (* [comment removed for export] *)
    replace (Z.lxor (31 - HB) 31) with HB by (clear - HL;
        assert (C : HB = 0 \/ HB = 1 \/ HB = 2 \/ HB = 3 \/ HB = 4 \/ HB = 5 \/ HB = 6 \/ HB = 7 \/ HB = 8 \/ HB = 9 \/ HB = 10 \/ HB = 11 \/ HB = 12
                    \/ HB = 13 \/ HB = 14 \/ HB = 15 \/ HB = 16 \/ HB = 17 \/ HB = 18) by lia;
        repeat (destruct C as [E|C]; [rewrite E; vm_compute; reflexivity|]); rewrite C; vm_compute; reflexivity).
    zstep. zstep. if_cases K1; zify_cond K1.                                   (* [comment removed for export] *)
    { replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 18446744073709551596) by (apply bv_eq; reflexivity).
      eapply (RS_EXIT_ARR _ hw rank wn wt 18446744073709551596); [ close_rsm | clear; lia | reflexivity]. }
    (* [comment removed for export] *)
    kx_chk [KAUnp TLP 4] 0xab56c (@nil kz) [17%nat].
    zstep. zstep. zstep. replace (32 - (31 - HB)) with (HB + 1) by (clear; lia).       (* [comment removed for export] *)
    zstep. zstep. rewrite (shiftl_mod32 2 HB) by lia.                          (* [comment removed for export] *)
    assert (PL : 1 <= 2^HB <= 2048) by (split; [pose proof (Z.pow_pos_nonneg 2 HB ltac:(lia) ltac:(lia)); lia | change 2048 with (2^11); apply Z.pow_le_mono_r; lia]).
    assert (PE : 2^(HB + 1) = 2 * 2^HB) by (rewrite Z.pow_add_r by lia; lia).
    rewrite PE in LSPEC.
    remember (2^HB) as P eqn:EP.
    rewrite (swrap32_small (2 * P)) by lia.
    zstep.                                                                     (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep. rewrite (swrap32_small (2 * P - wt0)) by lia.                       (* [comment removed for export] *)
    remember (2 * P - wt0) as rest eqn:EREST.
    assert (RR : 0 <= rest < 2^19) by (change (2^19) with 524288; lia).
    zstep. rewrite (srliw_small rest 1 RR) by lia. zstep.        (* [comment removed for export] *)
    pose proof (lor_shr_lt rest 1 19 RR ltac:(lia) ltac:(lia)) as RA.
    zstep. rewrite (srliw_small _ 2 RA) by lia. zstep.
    pose proof (lor_shr_lt _ 2 19 RA ltac:(lia) ltac:(lia)) as RB'.
    zstep. rewrite (srliw_small _ 4 RB') by lia. zstep.
    pose proof (lor_shr_lt _ 4 19 RB' ltac:(lia) ltac:(lia)) as RC.
    zstep. rewrite (srliw_small _ 8 RC) by lia. zstep.
    pose proof (lor_shr_lt _ 8 19 RC ltac:(lia) ltac:(lia)) as RD.
    zstep. rewrite (srliw_small _ 16 RD) by lia. zstep.
    lazymatch goal with |- _ => let v := reg_val 14 in lazymatch v with Z_to_bv 64 ?e => change e with (smear32 rest) end end.
    rewrite (smear32_ok rest) by lia.
    clear RA RB' RC RD.
    set (M := Z.log2 rest) in *.
    assert (HM : 0 <= M <= 11).
    { subst M. split; [apply Z.log2_nonneg|]. assert (Z.log2 rest < 12); [|lia]. apply Z.log2_lt_pow2; [lia|]. change (2^12) with 4096. lia. }
    assert (MSPEC : 2^M <= rest < 2^(M + 1)) by (subst M; pose proof (Z.log2_spec rest ltac:(lia)) as X; replace (Z.succ (Z.log2 rest)) with (Z.log2 rest + 1) in X by lia; exact X).
    clearbody M.
    do 19 zstep.                                                               (* [comment removed for export] *)
    lazymatch goal with |- _ => let v := reg_val 14 in lazymatch v with Z_to_bv 64 ?e =>
      replace e with (31 - M) by (clear - HM;
        assert (C : M = 0 \/ M = 1 \/ M = 2 \/ M = 3 \/ M = 4 \/ M = 5 \/ M = 6 \/ M = 7 \/ M = 8 \/ M = 9 \/ M = 10 \/ M = 11) by lia;
        repeat (destruct C as [E|C]; [rewrite E; vm_compute; reflexivity|]); rewrite C; vm_compute; reflexivity) end end.
    (* [comment removed for export] *)
    zstep. zstep. zstep.                                                       (* [comment removed for export] *)
    lazymatch goal with |- _ => let v := reg_val 17 in lazymatch v with Z_to_bv 64 ?e =>
      replace e with (2^M) by (clear - HM;
        assert (C : M = 0 \/ M = 1 \/ M = 2 \/ M = 3 \/ M = 4 \/ M = 5 \/ M = 6 \/ M = 7 \/ M = 8 \/ M = 9 \/ M = 10 \/ M = 11) by lia;
        repeat (destruct C as [E|C]; [rewrite E; vm_compute; reflexivity|]); rewrite C; vm_compute; reflexivity) end end.
    zstep. zstep. if_cases K2; zify_cond K2.                                          (* [comment removed for export] *)
    { replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 18446744073709551596) by (apply bv_eq; reflexivity).
      eapply (RS_EXIT_ARR _ hw rank wn (Z_to_bv 64 (HB + 1)) 18446744073709551596); [ close_rsm | clear; lia | reflexivity]. }
    (* [comment removed for export] *)
    zstep.                                                                     (* [comment removed for export] *)
    (* [comment removed for export] *)
    rs_reunp. kx_chk [KAUnp (HW + osz) 1] 0xab624 [KZRange osz 1 255] [13%nat; 15%nat].
    zstep. zstep. replace (32 - (31 - M)) with (M + 1) by (clear; lia).        (* [comment removed for export] *)
    u8_sok HWC osz. zstep. u8_store HWC osz (M + 1).                           (* [comment removed for export] *)
    1: reflexivity.
    zstep. zstep. replace ((M + 1) ≪ 2) with (4 * (M + 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    rs_reunp. kx_chk [KAUnp (RS + 4 * (M + 1)) 4] 0xab648 [KZRange M 0 11] [13%nat; 14%nat].
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u32_znth bsegs _ RS rank (M + 1) a RK ltac:(lia) ltac:(addr_tac)) as RD end.
    zstep.                                                                     (* [comment removed for export] *)
    assert (RKB : forall w, 0 <= w <= 12 -> 0 <= Znth w rank <= 255).
    { intros w Hw. rewrite (proj2 RINV w Hw). unfold hcount. pose proof (count_occ_bound Z.eq_dec w ws0). unfold FseNCount.Zlength in WS0L. clear - H WS0L OSR. lia. }
    pose proof (RKB (M + 1) ltac:(lia)) as RKM.
    rewrite (sx32w_small (Znth (M + 1) rank)) by lia.
    zstep. zstep.                                                       (* [comment removed for export] *)
    try replace (4 * (M + 1) + RS) with (RS + 4 * (M + 1)) by lia.
    u32st RK (M + 1) (Znth (M + 1) rank + 1) (Znth (M + 1) rank + 1).          (* [comment removed for export] *)
    change (upd_nat (Z.to_nat (M + 1)) (Znth (M + 1) rank + 1) rank) with (Zupd (M + 1) (Znth (M + 1) rank + 1) rank) in RK.
    assert (FZupd : forall (P : Z -> Prop) i v (l : list Z), Forall P l -> P v -> Forall P (Zupd i v l)).
    { clear. intros P i v l Fl Hv. unfold Zupd. generalize (Z.to_nat i). intros k. revert k.
      induction Fl as [|x t Hx Ht IH]; intros [|k]; cbn [upd_nat]; constructor; auto. }
    pose proof (huf_stats_final ws0 rank wt0 (HB + 1) (M + 1) FA ltac:(lia) RINV eq_refl ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(replace (M + 1 - 1) with M by lia; lia)) as FIN.
    remember (Zupd (M + 1) (Znth (M + 1) rank + 1) rank) as rank' eqn:ERK'.
    assert (RKLEN' : Z.of_nat (length rank') = 13) by (subst rank'; rewrite Zupd_length; exact RKLEN).
    (* [comment removed for export] *)
    rs_reunp. kx_chk [KAUnp (RS + 4) 4] 0xab668 (@nil kz) [12%nat; 13%nat].
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u32_znth bsegs _ RS rank' 1 a RK ltac:(lia) ltac:(addr_tac)) as RD1 end.
    zstep.                                                                     (* [comment removed for export] *)
    assert (R1 : 0 <= Znth 1 rank' <= 256).
    { destruct FIN as (_ & (_ & LEN') & _ & _ & CNT & _). rewrite (CNT 1 ltac:(lia)). unfold hcount.
      pose proof (count_occ_bound Z.eq_dec 1 (ws0 ++ [M + 1])). unfold FseNCount.Zlength in LEN'. clear - H LEN' OSR WS0L. lia. }
    rewrite (sx32w_small (Znth 1 rank')) by lia.
    zstep. zstep. if_cases K3; zify_cond K3.                                   (* [comment removed for export] *)
    { replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 18446744073709551596) by (apply bv_eq; reflexivity).
      eapply (RS_EXIT_ARR _ (Zupd osz (M + 1) hw) rank' wn (Z_to_bv 64 (HB + 1)) 18446744073709551596); [ | clear; lia | reflexivity].
      eapply RSM_close; try eassumption; [rewrite Zupd_length; exact HWLEN| apply FZupd; [exact HWBY | clear - HM; lia]]. }
    zstep.                                                                     (* [comment removed for export] *)
    assert (LB1 : 0 <= Z.land (Znth 1 rank') 1 <= 1).
    { pose proof (Z.land_ones (Znth 1 rank') 1 ltac:(lia)) as E1. change (Z.ones 1) with 1 in E1. change (2^1) with 2 in E1. rewrite E1. clear - R1. Z.div_mod_to_equations; lia. }
    zstep. if_cases K4; zify_cond K4.                                          (* [comment removed for export] *)
    { replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 18446744073709551596) by (apply bv_eq; reflexivity).
      eapply (RS_EXIT_ARR _ (Zupd osz (M + 1) hw) rank' wn (Z_to_bv 64 (HB + 1)) 18446744073709551596); [ | clear; lia | reflexivity].
      eapply RSM_close; try eassumption; [rewrite Zupd_length; exact HWLEN| apply FZupd; [exact HWBY | clear - HM; lia]]. }
    (* [comment removed for export] *)
    rs_reunp. kx_chk [KAUnp NBP 4] 0xab68c (@nil kz) [10%nat; 12%nat].
    assert (HWLEN' : Z.of_nat (length (Zupd osz (M + 1) hw)) = 256) by (rewrite Zupd_length; exact HWLEN).
    remember (Zupd osz (M + 1) hw) as hw' eqn:EHW'.
    zstep. zstep. zstep. zstep.                                                (* [comment removed for export] *)
    assert (firstn_upd_nat_snoc : forall k v (l : list Z), (k < length l)%nat -> firstn (S k) (upd_nat k v l) = firstn k l ++ [v]).
    { clear. induction k as [|k IH]; intros v [|a l] H; cbn [length] in H; try lia; cbn [upd_nat firstn app]; [reflexivity|]. rewrite IH by lia. reflexivity. }
    eapply (RS_EXIT_OK _ hw' rank' (HB + 1) (osz + 1) (isz + 1)).
    - eapply RSM_close; try eassumption. subst hw'. apply FZupd; [exact HWBY | clear - HM; lia].
    - clear - ISZ0 ISZN. lia.
    - replace (firstn (Z.to_nat (osz + 1)) hw') with (ws0 ++ [M + 1]); [exact FIN|].
      subst hw'. unfold Zupd, ws0. replace (Z.to_nat (osz + 1)) with (S (Z.to_nat osz)) by lia. rewrite firstn_upd_nat_snoc by lia. reflexivity.
    - clear - OSR. lia.
  Qed.
  End PostJoin.
End RS.
End CANSEC1.
