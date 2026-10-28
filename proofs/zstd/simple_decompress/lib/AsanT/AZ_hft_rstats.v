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
     AZ_kit AZ_fkit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface AZ_hft_rs_iface AZ_libc_iface AZ_libc AZ_kx AZ_hft_rs_defs AZ_hft_rstats_a AZ_hft_rstats_f.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.
Ltac nrm_not := repeat match goal with |- context [Z.lxor ?x 18446744073709551615] => rewrite (zb_lxor_ones x) by lia end.
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
  Variable src : list byte.
  Hypothesis SRCLEN : zlen src = n.
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
  Notation RS_FINAL := (rs_final AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo HW RS NBP TLP SRC n WK wksz B bsz
                          HY LBH INB INNB INTL mj UBj UNBj UTLj ARTj AHj MU0j WM0j FFR0j).

  (* [comment removed for export] *)
  Notation STL pc mm x1 x7 i tot osz isz x14 x15 x28 x29 x30 x31 :=
    (STF pc mm x1 (Z_to_bv 64 12) (Z_to_bv 64 (i + 1)) x7 (Z_to_bv 64 RS) (Z_to_bv 64 osz) (Z_to_bv 64 (-20)) (Z_to_bv 64 NBP) (Z_to_bv 64 TLP)
         (Z_to_bv 64 i) x14 x15 (Z_to_bv 64 tot) (Z_to_bv 64 1) (Z_to_bv 64 isz) (Z_to_bv 64 HW) (Z_to_bv 64 2147450880)
         (Z_to_bv 64 TLP) (Z_to_bv 64 NBP) x28 x29 x30 x31).
  Lemma rs_loop : forall k m1 hw rank (wn wt : word) isz osz i x1 x7 x14 x15 x28 x29 x30 x31,
    Z.to_nat (osz - i) = k ->
    RSMj hw rank wn wt m1 -> rank_inv (firstn (Z.to_nat i) hw) rank -> Forall (fun w => 0 <= w <= 12) (firstn (Z.to_nat i) hw) ->
    0 <= i < osz -> osz <= 255 -> 0 <= isz -> isz + 1 <= n ->
    evtF bsegs RNG POST (STL 0xab438 m1 x1 x7 i (hw_total (firstn (Z.to_nat i) hw)) osz isz x14 x15 x28 x29 x30 x31).
  Proof.
  induction k as [|k IH]; intros until x31; intros EK I RINV FA IR OSR ISZ0 ISZN; [exfalso; lia|].
  pose proof I as I0. open_rsm I. open_hy HY. pose proof CB as (CB1 & CB2 & CB3 & CB4 & CB5 & CB6). rs_reunp.
  rs_seps BNB BTL BSRC OFFB OFFNB OFFTL BRS RSHW RSWK HWB WKB LOS WKSZ0. hide_all_disj.
  set (ws0 := firstn (Z.to_nat i) hw) in *.
  assert (WS0L : FseNCount.Zlength ws0 = i) by (unfold FseNCount.Zlength, ws0; rewrite length_firstn; clear - IR OSR HWLEN; lia).
  pose proof (hw_total_bound ws0 FA) as WTB. pose proof (hw_total_nonneg ws0) as WT0.
  remember (hw_total ws0) as wt0 eqn:EWT.
  assert (WSN : firstn (Z.to_nat (i + 1)) hw = ws0 ++ [Znth i hw]).
  { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. unfold ws0, Znth. apply FseNCountRT.firstn_S_nth. clear - IR OSR HWLEN. lia. }
  pose proof (Forall_Znth _ hw i HWBY ltac:(clear - IR OSR HWLEN; lia)) as WB. cbv beta in WB.
  remember (Znth i hw) as w eqn:EW.
  (* [comment removed for export] *)
  kx_autoFLAc tt [KAUnp HW 256; KAUnp RS 52] [0xab46c; 0xab6b0] 30%nat (KZB ++ [KZRange i 0 254]) (@nil (Z * Z)) (@nil (Z * Z)).
  all: try (rs_rd HWC). all: try kx_acc RB.
  (* [comment removed for export] *)
  1: { lazymatch goal with |- context [ev ?E ?j] => kx_read_eq j RD end.
       rewrite (rdval_u8Zb bsegs m1 HW hw i _ HWC) in RD by first [clear - IR; lia | clear - IR OSR HWLEN; lia | exact HWBY].
       rewrite RD in *. rewrite <- EW in *. rewrite (unsigned_lit w) in * by (clear - WB; lia).
       kx_mem. kx_gen_regsF [7%nat; 30%nat]. kx_tidy_run.
       replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 18446744073709551596) by (apply bv_eq; reflexivity).
       eapply (RS_EXIT_ARR _ hw rank wn wt 18446744073709551596); [ exact I0 | clear; lia | reflexivity]. }
  lazymatch goal with |- context [Z_to_bv 64 (RS + 4 * bv_unsigned (ev ?E ?j))] => kx_read_eq j RD end.
  rewrite (rdval_u8Zb bsegs m1 HW hw i _ HWC) in RD by first [clear - IR; lia | clear - IR OSR HWLEN; lia | exact HWBY].
  rewrite RD in *. rewrite <- EW in *. rewrite (unsigned_lit w) in * by (clear - WB; lia).
  kx_mem. kx_gen_regsF [28%nat; 31%nat]. kx_tidy_run.
  (* [comment removed for export] *)
  pose proof (u32_znth bsegs _ RS rank w (wa (RS + 4 * w)) RK ltac:(clear - KXBR WB RKLEN; lia) eq_refl) as RD2.
  zstep.                                                                       (* [comment removed for export] *)
  assert (RKW : 0 <= Znth w rank <= 255).
  { rewrite (proj2 RINV w ltac:(clear - KXBR WB; lia)). unfold hcount. pose proof (count_occ_bound Z.eq_dec w ws0). unfold FseNCount.Zlength in WS0L. clear - H WS0L IR OSR. lia. }
  rewrite (sx32w_small (Znth w rank)) by (clear - RKW; lia).
  zstep.                                                                       (* [comment removed for export] *)
  u32st RK w (Znth w rank + 1) (Znth w rank + 1).                              (* [comment removed for export] *)
  change (upd_nat (Z.to_nat w) (Znth w rank + 1) rank) with (Zupd w (Znth w rank + 1) rank) in RK.
  pose proof (rank_inv_step ws0 rank w RINV ltac:(clear - KXBR WB; lia)) as RI'.
  remember (Zupd w (Znth w rank + 1) rank) as rank' eqn:ERK'.
  assert (RKLEN' : Z.of_nat (length rank') = 13) by (subst rank'; rewrite Zupd_length; exact RKLEN).
  (* [comment removed for export] *)
  kx_setreg 7%Z (2147450880 + (HW + i) / 8). kx_setreg 13%Z (HW + i). rs_reunp.
  kx_autoFLAc tt [KAUnp HW 256; KAShp (2147450880 + (HW + i) / 8) (HW + i)] [0xab480] 10%nat (KZB ++ [KZRange i 0 254]) (@nil (Z * Z)) (@nil (Z * Z)).
  kx_mem. kx_gen_regsF [7%nat; 14%nat]. kx_tidy_run.
  (* [comment removed for export] *)
  pose proof (u8_znth bsegs _ HW hw i (wa (HW + i)) HWC ltac:(clear - IR OSR HWLEN; lia) eq_refl) as RD3.
  rewrite <- EW in RD3.
  zstep. cbv beta. rewrite (byte_lit w) by (clear - WB; lia).                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. rewrite (sllw_pow2 w) by (clear - KXBR WB; lia).                      (* [comment removed for export] *)
  zstep.                                                                       (* [comment removed for export] *)
  lazymatch goal with |- _ => let v := reg_val 13 in lazymatch v with Z_to_bv 64 ?e => assert (HC : e = hw_cells w) end end.
  { clear - KXBR WB. assert (C : w = 0 \/ w = 1 \/ w = 2 \/ w = 3 \/ w = 4 \/ w = 5 \/ w = 6 \/ w = 7 \/ w = 8 \/ w = 9 \/ w = 10 \/ w = 11 \/ w = 12) by lia.
    repeat (destruct C as [E|C]; [rewrite E; vm_compute; reflexivity|]). rewrite C. vm_compute. reflexivity. }
  rewrite HC.
  pose proof (hw_cells_bound w ltac:(clear - KXBR WB; lia)) as HCB. pose proof (hw_cells_nonneg w) as HC0.
  zstep. rewrite (swrap32_small (hw_cells w + wt0)) by (clear - HCB HC0 WTB WT0 WS0L IR OSR; lia).   (* [comment removed for export] *)
  zstep. zstep. rewrite (Z.mod_small (i + 1) 4294967296) by (clear - IR OSR; lia).                   (* [comment removed for export] *)
  zstep.                                                                       (* [comment removed for export] *)
  assert (WT' : hw_total (firstn (Z.to_nat (i + 1)) hw) = hw_cells w + wt0) by (rewrite WSN, hw_total_app; cbn [hw_total]; clear - EWT; lia).
  assert (FA' : Forall (fun w => 0 <= w <= 12) (firstn (Z.to_nat (i + 1)) hw)) by (rewrite WSN; apply Forall_app; split; [exact FA | constructor; [clear - KXBR WB; lia | constructor]]).
  rewrite <- WSN in RI'.
  assert (I' : RSMj hw rank' wn wt m0) by close_rsm.
  zstep. if_cases K1; zify_cond K1.                                            (* [comment removed for export] *)
  - (* [comment removed for export] *)
    rewrite <- WT'.
    replace (Z_to_bv 64 (i + 2)) with (Z_to_bv 64 (i + 1 + 1)) by (f_equal; clear; lia).
    eapply (IH m0 hw rank' wn wt isz osz (i + 1)); try eassumption; clear - EK IR OSR ISZ0 ISZN K1; lia.
  - (* [comment removed for export] *)
    assert (EO : osz = i + 1) by (clear - K1 IR; lia). rewrite <- WT'. rewrite <- EO in *.
    zstep.                                                                     (* [comment removed for export] *)
    eapply (RS_FINAL _ hw rank' wn wt isz osz); try eassumption; clear - IR OSR ISZ0 ISZN EO; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma rs_count : forall m1 isz osz x1 x5 x6 x7 x10 x11 x12 x15 x16 x17 x21 x22 x28 x29 x30 x31,
    stk bsegs m1 HW (HW + 256) -> stk bsegs m1 RS (RS + 52) -> stk bsegs m1 NBP (NBP + 4) -> stk bsegs m1 TLP (TLP + 4) -> stk bsegs m1 WK (WK + wksz) ->
    stk bsegs m1 lo (SPV + -64) -> rw_cells bsegs m1 (SPV + -64) FRAME ->
    mem_inv bsegs m1 -> munch WJ mj m1 -> wmono bsegs mj m1 ->
    0 <= osz <= 255 -> 0 <= isz -> isz + 1 <= n ->
    evtF bsegs RNG POST (STF 0xab3fc m1 x1 x5 x6 x7 (Z_to_bv 64 RS) (Z_to_bv 64 osz) x10 x11 x12 (Z_to_bv 64 NBP) (Z_to_bv 64 TLP)
                             x15 x16 x17 (Z_to_bv 64 isz) (Z_to_bv 64 HW) (Z_to_bv 64 2147450880) x21 x22 x28 x29 x30 x31).
  Proof.
  intros until x31; intros HWS RSS NBS TLS WKS STK FR MI MU WM OSR ISZ0 ISZN.
  open_hy HY. pose proof CB as (CB1 & CB2 & CB3 & CB4 & CB5 & CB6). rs_reunp.
  pose proof (ablk_lin _ _ ABB) as (Ba & Bb & Bc & Bd). pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  assert (SRLO : RS + 52 <= lo \/ SPV + -64 <= RS) by (clear - OFFB BRS RSHW HWB LOS; lia).
  assert (APPR : app_blk RS (RS + 52)) by (apply ablk_app_blk; [eapply ablk_sub; [exact ABB| clear - BRS; lia| clear - RSHW HWB; lia]| clear; lia]).
  assert (AROR : aro RNG m1 RS 52).
  { split; [eapply unpoisoned_sub; [exact UB1| clear - BRS; lia| clear - RSHW HWB; lia]|].
    split; [eapply rng_sub'; [exact RB| clear - BRS RSHW HWB; lia]|].
    destruct (shspan_sub B bsz RS 52 ltac:(clear - BRS; lia) ltac:(clear; lia) ltac:(clear - RSHW HWB; lia)) as [S1 S2].
    eapply rng_sub'; [exact RSB| clear - S1 S2; unfold shspan in *; lia]. }
  assert (HULLR : ahull RNG m1 RS 52).
  { destruct (fk_ahull_pres RNG m m1 B bsz ltac:(eapply wmono_trans; [exact WM0j| exact WM]) HULLB) as (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & W6 & R6).
    exists RLO, RHI. split; [clear - H1 BRS; lia|]. split; [clear - H2 RSHW HWB; lia|]. repeat (split; [assumption|]). exact R6. }
  assert (ASTK : astk RNG lo (SPV + -64)) by (split; [exact KLO|]; split; [eapply rng_sub'; [exact RSTK| clear - LOS; lia]| exact RI]).
  pose proof (conj GOT1 (conj RIC1 (conj SHB1 (conj INI1 (conj LAY1 REAL1))))) as ART1'. change (art m1) in ART1'.
  rs_seps BNB BTL BSRC OFFB OFFNB OFFTL BRS RSHW RSWK HWB WKB LOS WKSZ0. hide_all_disj.
  do 5 zstep. zstep.                                                           (* [comment removed for export] *)
  destruct (stk_open bsegs _ RS (RS + 52) RS 52%nat RSS ltac:(clear; lia) ltac:(clear; lia)) as (jr & RSC & _ & _).
  eapply evtF_cut.
  { eapply (zd_memsetZ_proofA RNG RS 52 0 (SPV + -64)); first [exact RSC| exact STK| exact APPR| exact AROR| exact HULLR| exact ART1'| exact ASTK| exact MI| reflexivity| idtac];
      unhide; clear - LOS SPR SRLO; lia. }
  unfold zd_memsetZ_postA. post_call bsegs m1.
  lazymatch goal with H : rw_cells bsegs ?mx RS [Cells.CB _ (repeat _ _)] |- _ => rename H into RSZ; rename mx into m2 end.
  lazymatch goal with H : stk bsegs m2 lo (SPV + -64) |- _ => rename H into STK2 end.
  assert (RK : u32arr bsegs m2 RS (map (Z_to_bv 64) (repeat 0 13))).
  { apply u8arr_of_rw_cells in RSZ. destruct RSZ as [Hb Hw]. split.
    - replace (u32s (map (Z_to_bv 64) (repeat 0 13))) with (repeat (Z_to_bv 8 0) (Z.to_nat 52)) by (vm_compute; reflexivity). exact Hb.
    - rewrite repeat_length in Hw. rewrite length_map, repeat_length. exact Hw. }
  clear RSZ.
  destruct (stk_open bsegs _ HW (HW + 256) HW 256%nat HWS ltac:(clear; lia) ltac:(clear; lia)) as (hwb & HWC & _ & _).
  assert (HWBL : length hwb = 256%nat) by (destruct HWC as [[WF _] _]; cbn in WF; destruct WF as [LJ _]; exact LJ).
  apply u8arr_of_rw_cells in HWC. rewrite <- (bytes_of_unsigned hwb) in HWC.
  remember (map bv_unsigned hwb) as hw eqn:EHW.
  assert (HWLEN : zlen hw = 256) by (subst hw; rewrite length_map; clear - HWBL; lia).
  assert (HWBY : Forall (fun c => 0 <= c < 256) hw) by (subst hw; apply bytes_unsigned_range).
  clear EHW HWBL.
  destruct (stk_open bsegs _ NBP (NBP + 4) NBP 4%nat NBS ltac:(clear; lia) ltac:(clear; lia)) as (jn & NBC0 & _ & _).
  destruct (hcb4_as_c4 bsegs _ _ [] jn [] NBC0) as [wn NBC]. cbn [app] in NBC. clear NBC0.
  destruct (stk_open bsegs _ TLP (TLP + 4) TLP 4%nat TLS ltac:(clear; lia) ltac:(clear; lia)) as (jt & TLC0 & _ & _).
  destruct (hcb4_as_c4 bsegs _ _ [] jt [] TLC0) as [wt TLC]. cbn [app] in TLC. clear TLC0.
  assert (I : RSMj hw (repeat 0 13) wn wt m2) by (eapply RSM_close; try eassumption; reflexivity).
  zstep. zstep. if_cases K4; zify_cond K4.                                     (* [comment removed for export] *)
  { replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 18446744073709551596) by (apply bv_eq; reflexivity).
    eapply (RS_EXIT_ARR _ hw (repeat 0 13) wn wt 18446744073709551596); [exact I | clear; lia | reflexivity]. }
  (* [comment removed for export] *)
  do 7 zstep.                                                                 (* [comment removed for export] *)
  nrm_not.
  eapply (rs_loop (Z.to_nat osz) _ hw (repeat 0 13) wn wt isz osz 0); try eassumption; try (clear - OSR K4 ISZ0 ISZN; lia).
  - exact rank_inv_nil.
  - constructor.
  Qed.
  (* [comment removed for export] *)
  Hypothesis N0 : 0 < n.
  Hypothesis ABS : ablk SRC (SRC + n).
  Hypothesis RSR : rng RNG SRC n.
  Hypothesis RSSR : rng RNG (shad SRC) (shspan SRC n).
  Hypothesis NBSRC : NBP + 4 <= SRC \/ SRC + n <= NBP.
  Hypothesis TLSRC : TLP + 4 <= SRC \/ SRC + n <= TLP.
  Hypothesis USj : unpoisoned mj SRC (SRC + n).
  Lemma rs_unp_srcM : forall m1, munch WJ mj m1 -> unpoisoned m1 SRC (SRC + n).
  Proof.
    intros m1 MU. open_hy HY. pose proof CB as (C1 & C2 & C3 & C4 & C5 & C6).
    pose proof (ablk_lin _ _ ABS) as (Sa & Sb & Sc & Sd). pose proof (ablk_disj_band _ _ ABS) as SD. unfold AIMG_HI, KLS in Sa, SD.
    pose proof (ablk_disj_band _ _ ABB) as BD. unfold KLS in BD.
    eapply unpoisoned_munch; [exact USj | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF, KHIGH in *. clear - Sa Sb Sc Sd SD BD C1 C2 C3 C4 C5 C6 BRS RSHW HWB BSRC NBSRC TLSRC OFFSRC LOS N0 SRCH SRCL KLO.
    repeat split; Z.div_mod_to_equations; lia.
  Qed.


  (* [comment removed for export] *)
  Lemma rs_direct : forall f m1 (out : list byte) isz osz k x1 x5 x11 x15 x18 x21 x22 x28 x29 x30 x31,
    osz - 2 * k <= 2 * Z.of_nat f ->
    u8arr bsegs m1 HW out -> zlen out = 256 -> bytes_at bsegs m1 SRC src ->
    stk bsegs m1 RS (RS + 52) -> stk bsegs m1 NBP (NBP + 4) -> stk bsegs m1 TLP (TLP + 4) -> stk bsegs m1 WK (WK + wksz) ->
    stk bsegs m1 lo (SPV + -64) -> rw_cells bsegs m1 (SPV + -64) FRAME ->
    mem_inv bsegs m1 -> munch WJ mj m1 -> wmono bsegs mj m1 ->
    0 <= k -> 2 * k < osz -> osz <= 128 -> osz <= 2 * isz <= osz + 1 -> isz < n ->
    evtF bsegs RNG POST
      (STF 0xab368 m1 x1 x5 (Z_to_bv 64 (SRC + 1 + k)) (Z_to_bv 64 (HW + 1 + 2 * k)) (Z_to_bv 64 RS) (Z_to_bv 64 osz) (Z_to_bv 64 (SRC + 1 + k)) x11
           (Z_to_bv 64 (HW + 2 * k)) (Z_to_bv 64 NBP) (Z_to_bv 64 TLP) x15 (Z_to_bv 64 (2 * k)) (Z_to_bv 64 isz) x18 (Z_to_bv 64 HW)
           (Z_to_bv 64 2147450880) x21 x22 x28 x29 x30 x31).
  Proof.
  induction f as [|f IH]; intros until x31; intros HF OUT OLEN SRCB RSS NBS TLS WKS STK FR MI MU WM K0 KO OSR ISR ISN; [exfalso; clear - HF K0 KO; lia|].
  open_hy HY. pose proof CB as (CB1 & CB2 & CB3 & CB4 & CB5 & CB6). rs_reunp. pose proof (rs_unp_srcM m1 MU) as US1.
  pose proof (ablk_disj_band _ _ ABB) as BD. pose proof (ablk_disj_band _ _ ABS) as SD. pose proof (ablk_lin _ _ ABS) as (Sa & _ & _ & _). unfold AIMG_HI, KLS in BD, SD, Sa.
  assert (BHW : HW + 256 <= 0x7fff7000 \/ 0x10007fff8000 <= HW) by (clear - BD BRS RSHW HWB; lia).
  rs_seps BNB BTL BSRC OFFB OFFNB OFFTL BRS RSHW RSWK HWB WKB LOS WKSZ0. hide_all_disj. unfold hidden in BHW, SHS, SHF.
  kx_autoFLAc FR [KAUnp SRC n; KAUnp HW 256; KAApp HW 256] [0xab368; 0xab3f8] 48%nat
    (KZB ++ [KZRange k 0 127; KZRange osz 1 128; KZRange isz 0 65535; KZRange n 1 (2^32); KZRange (n - k) 2 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4097 (2^47);
             KZWr HW 256; KZDisj HW 256 SRC n; KZDisj HW 256 (SPV - 64) 64])
    (@nil (Z * Z)) (@nil (Z * Z)).
  all: try (rs_rd SRCB). all: try kx_acc RSR. all: try kx_acc RB.
  all: try kx_z.                                                               (* [comment removed for export] *)
  all: kx_mem.
  all: kx_gen_regsF [11%nat; 15%nat; 28%nat]; kx_tidy_run.
  - (* [comment removed for export] *)
    lazymatch goal with H : length ?kb = length out |- _ => assert (OLEN' : zlen kb = 256) by (rewrite H; exact OLEN); clear H end.
    kx_setreg 6%Z (SRC + 1 + (k + 1)). kx_setreg 7%Z (HW + 1 + 2 * (k + 1)). kx_setreg 10%Z (SRC + 1 + (k + 1)). kx_setreg 12%Z (HW + 2 * (k + 1)). kx_setreg 16%Z (2 * (k + 1)).
    eapply (IH _ _ isz osz (k + 1)); try eassumption; clear - HF K0 KO OSR ISR ISN KXBR; lia.
  - (* [comment removed for export] *)
    lazymatch goal with H : length ?kb = length out |- _ => assert (OLEN' : zlen kb = 256) by (rewrite H; exact OLEN); clear H end.
    zstep.
    apply rw_cells_of_u8arr in OUT. apply stk_of_rw_cells in OUT. cbn [cells_size csize] in OUT.
    lazymatch type of OUT with stk _ _ _ (HW + Z.of_nat (length ?o + 0)) => replace (HW + Z.of_nat (length o + 0)) with (HW + 256) in OUT by (clear - OLEN'; lia) end.
    eapply (rs_count _ isz osz); try eassumption; clear - OSR ISR ISN K0 KO KXBR; lia.
  Qed.
  End PostJoin.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis FHL : fake_heap_law AI.
  Hypothesis FDEC : fse_dec_stmtA AI rng_fs.

  Lemma dj_sub : forall W a k a' k', disjoint_from W a k -> a <= a' -> a' + k' <= a + k -> disjoint_from W a' k'.
  Proof.
    induction W as [|[l hh] W IHW]; cbn; intros a k a' k' D L1 L2; [exact I|].
    destruct D as [D1 D2]. split; [clear - D1 L1 L2; lia|]. eapply IHW; eauto.
  Qed.
  Lemma ffr_pres_mono_nil : forall W (mA mB : amem), ffr_pres [] LB mA mB -> ffr_pres W LB mA mB.
  Proof.
    intros W mA mB H a Ha HP. apply (H a Ha). destruct HP as [[HF _]|HS]; [left; split; [exact HF| exact I]| right; exact HS].
  Qed.

  Lemma ffr_pres_monoC : forall W W' (mA mB : amem), ffr_pres W LB mA mB ->
    (forall x y, In (x, y) W -> exists x' y', In (x', y') W' /\ x' <= x /\ y <= y') -> ffr_pres W' LB mA mB.
  Proof.
    intros W W' mA mB H HC a Ha HP. apply (H a Ha). destruct HP as [[HF HO]|HS]; [left; split; [exact HF|]| right; exact HS].
    clear - HO HC. induction W as [|[x y] W IH]; cbn [outside]; [exact I|]. split.
    - destruct (HC x y (or_introl eq_refl)) as (x' & y' & HI & L1 & L2). pose proof (outside_In W' a x' y' HO HI). clear - H L1 L2. lia.
    - apply IH. intros u v Huv. apply (HC u v). right. exact Huv.
  Qed.

  (* [comment removed for export] *)
  Lemma inblk_magree : forall (mA mB : amem) Wd Ws X k,
    AHEAP AI L RNG st LB mB -> ainblk LB X k -> 0 <= k ->
    munch (Wd ++ Ws ++ fake_area L) mA mB -> wmono bsegs mA mB -> ffr_pres Wd LB mA mB ->
    disjoint_from Wd X k -> disjoint_from Ws X k -> magree bsegs (fun a => X <= a < X + k) mA mB.
  Proof.
    intros mA mB Wd Ws X k AH (b & Hb & H1 & H2) Hk MU WM FP DD DS.
    destruct b as [[p|c] A nb]; cbn [ab_addr ab_size] in H1, H2.
    - destruct (fake_area_block AI L RNG st LB mB p A nb FHL AH Hb) as [DF _].
      eapply magree_mono; [eapply magree_of_munch; [exact MU| exact WM]|].
      intros a Ha. cbv beta in Ha.
      apply (disjoint_outside _ X k a); [| exact Ha].
      apply disjoint_from_app2; [exact DD|]. apply disjoint_from_app2; [exact DS|].
      eapply dj_sub; [exact DF| exact H1| exact H2].
    - eapply magree_mono; [exact FP|]. intros a Ha. cbv beta in Ha. left. split.
      + exists c, A, nb. split; [exact Hb| clear - Ha H1 H2; lia].
      + exact (disjoint_outside _ X k a DD Ha).
  Qed.

  (* [comment removed for export] *)
  Theorem rs_body : forall (t0 t1 t2 t3 t4 t5 t6 : word),
    AHEAP AI L RNG st LB m -> ashort LB 3 -> art m -> rng_fs L RNG -> SPV + 16 < al_top L -> rng RNG lo (al_top L - lo) -> tp = Z_to_bv 64 ATP ->
    azstk RNG m lo SPV -> aro_client RNG m ->
    unpoisoned m B (B + bsz) -> unpoisoned m NBP (NBP + 4) -> unpoisoned m TLP (TLP + 4) ->
    (0 < n -> ablk SRC (SRC + n) /\ unpoisoned m SRC (SRC + n) /\ rng RNG SRC n /\ rng RNG (shad SRC) (shspan SRC n)) ->
    (0 < n -> ainimg LB SRC n) -> (0 < n -> ahull RNG m SRC n) ->
    (0 < n -> NBP + 4 <= SRC \/ SRC + n <= NBP) -> (0 < n -> TLP + 4 <= SRC \/ SRC + n <= TLP) ->
    mem_inv bsegs m -> stk bsegs m lo SPV -> bytes_at bsegs m SPV (le8 (Z_to_bv 64 wksz)) ->
    stk bsegs m HW (HW + 256) -> stk bsegs m RS (RS + 52) -> stk bsegs m NBP (NBP + 4) -> stk bsegs m TLP (TLP + 4) ->
    bytes_at bsegs m SRC src -> stk bsegs m WK (WK + wksz) ->
    evtF bsegs RNG POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 HW) (Z_to_bv 64 256) (Z_to_bv 64 RS) (Z_to_bv 64 NBP)
               (Z_to_bv 64 TLP) (Z_to_bv 64 SRC) (Z_to_bv 64 n) (Z_to_bv 64 WK) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xab294) fc None m (seg_rom bsegs)).
  Proof.
    intros t0 t1 t2 t3 t4 t5 t6 AH ASH ART RFS SPT RSTK2 TP AZS AROC UB UNB UTL HSRC INSRC HULLS NBSRC' TLSRC' MI STK WSZ HWS RSS NBS TLS SRCB WKS.
    open_hy HY. pose proof (rs_cellbands LB NBP TLP LBH INNB INTL) as (CB1 & CB2 & CB3 & CB4 & CB5 & CB6).
    pose proof (ablk_lin _ _ ABB) as (Ba & Bb & Bc & Bd). pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof ART as ART0. destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
    assert (MU : munch [(SPV - 64, SPV)] m m) by apply munch_refl.
    assert (WM : wmono bsegs m m) by apply wmono_refl.
    rs_seps BNB BTL BSRC OFFB OFFNB OFFTL BRS RSHW RSWK HWB WKB LOS WKSZ0. hide_all_disj.
    carve_frame 64%nat STK.
    apply (rw_cells_split_CB bsegs _ _ [] 64 _ [] [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    (* [comment removed for export] *)
    assert (PRO : forall mq, munch [(SPV + -64, SPV)] m mq -> wmono bsegs m mq ->
              munch MUNCH m mq /\ ffr_pres WL LB m mq /\ AHEAP AI L RNG st LB mq /\
              stk bsegs mq WK (WK + wksz) /\ stk bsegs mq HW (HW + 256) /\ stk bsegs mq RS (RS + 52) /\ stk bsegs mq NBP (NBP + 4) /\ stk bsegs mq TLP (TLP + 4) /\
              unpoisoned mq B (B + bsz) /\ unpoisoned mq NBP (NBP + 4) /\ unpoisoned mq TLP (TLP + 4) /\ art mq /\ aro_client RNG mq /\
              bytes_at bsegs mq SRC src /\ bytes_at bsegs mq SPV (le8 (Z_to_bv 64 wksz)) /\ azstk RNG mq lo (SPV + -64)).
    { intros mq MUq WMq.
      split; [eapply munch_weaken; [| exact MUq]; intros x Hx; cbn [outside app fake_area] in *; clear - Hx; lia|].
      split; [apply ffr_pres_mono_nil; eapply (fk_ffr_stack AI); [exact AH| exact MUq| exact WMq| constructor; [cbn [fst]; clear - BOT LOS; lia| constructor]]|].
      split; [eapply (AI_frame AI); [exact AH| exact MUq| exact WMq| constructor; [cbn [fst snd]; apply (fk_acr_stack AI) with (lo := lo); clear - BOT LOS SPR; lia| constructor]]|].
      unhide. split; [eapply stk_transport_disjoint; [exact WKS| exact MUq| exact WMq| cbn [disjoint_from]; clear - SWF WKSZ0; lia]|].
      split; [eapply stk_transport_disjoint; [exact HWS| exact MUq| exact WMq| cbn [disjoint_from]; clear - SHF; lia]|].
      split; [eapply stk_transport_disjoint; [exact RSS| exact MUq| exact WMq| cbn [disjoint_from]; clear - SRF; lia]|].
      split; [eapply stk_transport_disjoint; [exact NBS| exact MUq| exact WMq| cbn [disjoint_from]; clear - SNBF; lia]|].
      split; [eapply stk_transport_disjoint; [exact TLS| exact MUq| exact WMq| cbn [disjoint_from]; clear - STLF; lia]|].
      pose proof (ablk_disj_band _ _ ABB) as BD. unfold KLS in BD.
      split; [eapply unpoisoned_munch; [exact UB| exact MUq| cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF, KHIGH in *; clear - BD Bb Bd KLO LOS; split; [Z.div_mod_to_equations; lia| exact I]]|].
      split; [eapply unpoisoned_munch; [exact UNB| exact MUq| cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF, KHIGH in *; clear - CB1 CB3 CB5 KLO LOS; split; [Z.div_mod_to_equations; lia| exact I]]|].
      split; [eapply unpoisoned_munch; [exact UTL| exact MUq| cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF, KHIGH in *; clear - CB2 CB4 CB6 KLO LOS; split; [Z.div_mod_to_equations; lia| exact I]]|].
      split; [eapply rs_art_transport; [exact ART0| exact MUq| exact WMq| constructor; [cbn [fst]; unfold KHIGH in KLO; clear - KLO LOS; lia| constructor]]|].
      split; [eapply aro_client_transport; [exact AROC| exact MUq| exact WMq| constructor; [cbn [fst snd]; right; clear - KLO LOS; lia| constructor]]|].
      split; [eapply bytes_at_transport; [exact SRCB| exact MUq| cbn [disjoint_from]; rewrite SRCLEN; clear - OFFSRC LOS NN; lia]|].
      split; [eapply bytes_at_transport; [exact WSZ| exact MUq| cbn [disjoint_from]; rewrite length_le8; clear; lia]|].
      eapply azstk_sub; [eapply azstk_transport; [exact AZS| exact MUq| exact WMq| constructor; [cbn [fst snd]; right; clear - KLO LOS; lia| constructor]| clear - LOS; lia]
                       | clear; lia| clear - LOS; lia| clear; lia]. }
    destruct (Z.eq_dec n 0) as [EN|NPOS].
    { (* [comment removed for export] *)
      replace (Z_to_bv 64 n) with (Z_to_bv 64 0) by (rewrite EN; reflexivity).
      kx_autoFLAc FR [KAApp (SPV - 64) 64] [0xab6b0] 24%nat (KZB ++ [KZWr (SPV - 64) 64]) (@nil (Z * Z)) (@nil (Z * Z)).
      all: try kx_acc RSTK2. all: kx_mem. all: kx_tidy_run.
      destruct (PRO _ MU WM) as (MU' & FFR' & AH' & WKS' & HWS' & RSS' & NBS' & TLS' & _).
      eapply (rs_exit_gen AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo HW RS NBP TLP SRC n WK wksz B bsz HY _ 18446744073709551544);
        try eassumption; [clear; lia|].
      right. split; [reflexivity|]. repeat (split; [assumption|]). assumption. }
    (* [comment removed for export] *)
    assert (N0 : 0 < n) by (clear - NN NPOS; lia).
    destruct (HSRC N0) as (ABS & USRC & RSR & RSSR). specialize (INSRC N0). specialize (HULLS N0). specialize (NBSRC' N0). specialize (TLSRC' N0).
    pose proof (ablk_disj_band _ _ ABS) as SD. pose proof (ablk_lin _ _ ABS) as (Sa & Sb & Sc & Sd). unfold AIMG_HI, KLS in SD, Sa.
    kx_autoFLAc (FR, GOT, SHB) [KAApp (SPV - 64) 64; KAUnp SRC n] [0xab2e4] 36%nat
      (KZB ++ [KZWr (SPV - 64) 64; KZRange n 1 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4097 (2^47)]) (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_cell_lit. all: try kx_z. all: try kx_acc RSTK2. all: try kx_acc RI.
    all: kx_mem. all: kx_gen_regsF [12%nat]; kx_tidy_run.
    destruct (PRO _ MU WM) as (MU1 & FFR1 & AH1 & WKS1 & HWS1 & RSS1 & NBS1 & TLS1 & UB1 & UNB1 & UTL1 & ART1 & AROC1 & SRCB1 & WSZ1 & AZS1).
    assert (USRC1 : unpoisoned m0 SRC (SRC + n)).
    { eapply unpoisoned_munch; [exact USRC| exact MU|]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF, KHIGH in *.
      clear - SD Sb Sd KLO LOS N0. split; [Z.div_mod_to_equations; lia| exact I]. }
    pose proof SRCB1 as SRCZ. rewrite <- (bytes_of_unsigned src) in SRCZ.
    remember (map bv_unsigned src) as buf eqn:EBUF.
    assert (BUFL : zlen buf = n) by (subst buf; rewrite length_map; exact SRCLEN).
    assert (BUFB : Forall (fun c => 0 <= c < 256) buf) by (subst buf; apply bytes_unsigned_range).
    clear EBUF.
    assert (RB0 : 0 <= Znth 0 buf < 256) by (apply (Forall_Znth _ buf 0 BUFB); clear - BUFL N0; lia).
    replace (Z_to_bv 64 SRC) with (Z_to_bv 64 (SRC + 0)) by (f_equal; clear; lia).
    assert (RD : ov_read_bytes bsegs m0 (Z_to_bv 64 (SRC + 0)) 1 = Some [Z_to_bv 8 (Znth 0 buf)]) by (eapply zd_src_rd; [exact SRCZ | clear - BUFL N0; lia | reflexivity]).
    step. unfold sxb. rewrite (byte_sig8 (Znth 0 buf)) by assumption. clear RD. set (c0 := Znth 0 buf) in *.
    zstep. unfold ZdWalkKit.sx8.
    destruct (Z.ltb_spec c0 128) as [C128|C128].
    { (* [comment removed for export] *)
      replace (Z.land (c0 mod 18446744073709551616) 255) with c0 by (rewrite Z.mod_small by lia; change 255 with (Z.ones 8); rewrite Z.land_ones by lia; rewrite Z.mod_small; lia).
      clearbody c0.
      zstep. if_cases K1; zify_lts K1; [exfalso; clear - K1 RB0 C128; lia|].
      zstep. if_cases K2; zify_cond K2.
      { eapply (rs_exit_gen AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo HW RS NBP TLP SRC n WK wksz B bsz HY _ 18446744073709551544);
          try eassumption; [clear; lia|].
        right. split; [reflexivity|]. repeat (split; [assumption|]). assumption. }
      assert (RDW : ov_read_bytes bsegs m0 (Z_to_bv 64 (SPV + -64 + 64)) 8 = Some (le8 (Z_to_bv 64 wksz))).
      { pose proof (bytes_at_read bsegs m0 SPV (le8 (Z_to_bv 64 wksz)) 0 8 WSZ1 ltac:(clear; lia) ltac:(rewrite length_le8; cbn; clear; lia)) as RD.
        rewrite skipn_O in RD. rewrite firstn_all2 in RD by (rewrite length_le8; clear; lia).
        unfold wa in RD. replace (SPV + -64 + 64) with (SPV + 0) by (clear; lia). exact RD. }
      (* [comment removed for export] *)
      zstep. clear RDW.                                                        (* [comment removed for export] *)
      do 9 zstep. zstep.                                                      (* [comment removed for export] *)
      (* [comment removed for export] *)
      assert (SUBB : bytes_at bsegs m0 (SRC + 1) (firstn (Z.to_nat c0) (skipn 1 src))).
      { pose proof SRCB1 as SB. rewrite <- (firstn_skipn 1 src) in SB. apply bytes_at_app in SB. destruct SB as [_ SB].
        rewrite length_firstn in SB. replace (SRC + Z.of_nat (Nat.min 1 (length src))) with (SRC + 1) in SB by (clear - SRCLEN N0; lia).
        rewrite <- (firstn_skipn (Z.to_nat c0) (skipn 1 src)) in SB. apply bytes_at_app in SB. exact (proj1 SB). }
      assert (SUBL : zlen (firstn (Z.to_nat c0) (skipn 1 src)) = c0) by (rewrite length_firstn, length_skipn; clear - SRCLEN K2 RB0; lia).
      remember (firstn (Z.to_nat c0) (skipn 1 src)) as sub eqn:ESUB. clear ESUB.
      destruct (stk_split bsegs _ HW (HW + 255) (HW + 256) HWS1 ltac:(clear; lia)) as [HWA HWZ].
      eapply evtF_cut.
      { eapply (FDEC L RNG st LB) with (lo := lo) (src := sub); unfold afpre, astk.
        all: lazymatch goal with
             | |- _ /\ _ => idtac
             | |- tp = _ => exact TP
             | |- aro_client _ _ => exact AROC1
             | |- azstk _ _ _ _ => exact AZS1
             | |- mem_inv _ _ => exact KXMI
             | |- stk bsegs _ lo _ => exact STK
             | |- stk bsegs _ HW _ => exact HWA
             | |- stk bsegs _ WK _ => exact WKS1
             | |- bytes_at _ _ _ _ => exact SUBB
             | |- Z.of_nat (length _) = _ => exact SUBL
             | |- WK mod 4 = 0 => exact WKA
             | |- ainblk LB HW _ => eapply ainblk_sub; [exact INB| clear - BRS RSHW; lia| clear - HWB; lia]
             | |- ainblk LB WK _ => eapply ainblk_sub; [exact INB| clear - BRS RSWK; lia| clear - WKB; lia]
             | |- ainimg LB _ _ => eapply ainimg_sub; [exact INSRC| clear; lia| clear - K2; lia]
             | |- _ => idtac
             end.
        - (* [comment removed for export] *)
          split; [exact AH1|]. split; [exact ASH|]. split; [exact ART1|]. split; [split; [exact KLO|]; split; [eapply rng_sub'; [exact RSTK| clear - LOS; lia]| exact RI]|].
          split; [exact RFS|]. split; [exact BOT|]. split; [clear - SPT; lia|]. split; [clear - SPA; Z.div_mod_to_equations; lia|]. split; [exact RSTK2| exact LBH].
        - intros _. split; [eapply ablk_sub; [exact ABB| clear - BRS RSHW; lia| clear - HWB; lia]|].
          split; [eapply unpoisoned_sub; [exact UB1| clear - BRS RSHW; lia| clear - HWB; lia]|].
          split; [eapply rng_sub'; [exact RB| clear - BRS RSHW HWB; lia]|].
          destruct (shspan_sub B bsz HW 255 ltac:(clear - BRS RSHW; lia) ltac:(clear; lia) ltac:(clear - HWB; lia)) as [S1 S2].
          eapply rng_sub'; [exact RSB| clear - S1 S2; unfold shspan in *; lia].
        - split; [eapply ablk_sub; [exact ABS| clear; lia| clear - K2; lia]|].
          split; [eapply unpoisoned_sub; [exact USRC1| clear; lia| clear - K2; lia]|].
          split; [eapply rng_sub'; [exact RSR| clear - K2 RB0; lia]|].
          destruct (shspan_sub SRC n (SRC + 1) c0 ltac:(clear; lia) ltac:(clear - RB0; lia) ltac:(clear - K2; lia)) as [S1 S2].
          eapply rng_sub'; [exact RSSR| clear - S1 S2; unfold shspan in *; lia].
        - destruct (fk_ahull_pres RNG m m0 SRC n WM HULLS) as (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & W6 & R6).
          exists RLO, RHI. split; [clear - H1; lia|]. split; [clear - H2 K2; lia|]. repeat (split; [assumption|]). exact R6.
        - intros WP. split; [eapply ablk_sub; [exact ABB| clear - BRS RSWK; lia| clear - WKB; lia]|].
          split; [eapply unpoisoned_sub; [exact UB1| clear - BRS RSWK; lia| clear - WKB; lia]|].
          split; [eapply rng_sub'; [exact RB| clear - BRS RSWK WKB WP; lia]|].
          destruct (shspan_sub B bsz WK wksz ltac:(clear - BRS RSWK; lia) ltac:(clear - WP; lia) ltac:(clear - WKB; lia)) as [S1 S2].
          eapply rng_sub'; [exact RSB| clear - S1 S2; unfold shspan in *; lia].
        - destruct (fk_ahull_pres RNG m m0 B bsz WM HULLB) as (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & W6 & R6).
          exists RLO, RHI. split; [clear - H1 BRS RSWK; lia|]. split; [clear - H2 WKB; lia|]. repeat (split; [assumption|]). exact R6.
        - exact LO0.
        - clear - LOS; lia.
        - clear - SPR; lia.
        - clear - BL BRS RSHW; lia.
        - clear; lia.
        - clear - HWB BH; lia.
        - clear - SRCL; lia.
        - clear - C128; lia.
        - clear - K2 SRCH; lia.
        - clear - BL BRS RSWK; lia.
        - clear - WKSZ0 WKSZ; lia.
        - clear - WKB BH; lia.
        - clear; lia.
        - unhide. clear - SHL LOS; lia.
        - unhide. clear - SWL LOS; lia.
        - unhide. clear - OFFSRC LOS K2; lia.
        - unhide. clear - HWWK; lia.
        - unhide. clear - SHS K2; lia.
        - unhide. clear - BSRC BRS RSWK WKB K2; lia. }
      intros ms' PO. unfold fse_dec_postA in PO.
      destruct PO as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & m7 & rd & -> & MU7 & WM7 & MI7 & ST7 & FFR7 & AH7 & HWA7 & WKS7 & RDR & RDP).
      lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?nn)] => replace (ret_pc (Z_to_bv 64 nn)) with (Z_to_bv 64 nn) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
      (* [comment removed for export] *)
      assert (MU07 : munch MUNCH m m7).
      { eapply munch_trans; [exact MU1|]. eapply munch_weaken; [| exact MU7]. intros x Hx. cbn [outside app fake_area] in *. clear - Hx. lia. }
      assert (WM07 : wmono bsegs m m7) by (eapply wmono_trans; [exact WM| exact WM7]).
      assert (FFR07 : ffr_pres WL LB m m7).
      { eapply ffr_pres_trans; [exact FFR1|]. eapply ffr_pres_monoC; [exact FFR7|].
        intros x y [E|[E|[]]]; injection E as <- <-.
        - exists HW, (HW + 256). split; [left; reflexivity| clear; lia].
        - exists WK, (WK + wksz). split; [do 4 right; left; reflexivity| clear; lia]. }
      pose proof (ffr_unp_pres AI L RNG st LB _ m0 m7 B bsz AH7 FFR7 INB ltac:(clear - BRS RSHW HWB; lia) UB1) as UB7.
      pose proof (ffr_unp_pres AI L RNG st LB _ m0 m7 NBP 4 AH7 FFR7 INNB ltac:(clear; lia) UNB1) as UNB7.
      pose proof (ffr_unp_pres AI L RNG st LB _ m0 m7 TLP 4 AH7 FFR7 INTL ltac:(clear; lia) UTL1) as UTL7.
      pose proof (art_of_aheap AI L RNG st LB m7 AH7) as ART7.
      assert (MU7' : munch ([(HW, HW + 255); (WK, WK + wksz)] ++ [(SPV + -64 - 4992, SPV + -64)] ++ fake_area L) m0 m7) by exact MU7.
      unhide.
      assert (RSS7 : stk bsegs m7 RS (RS + 52)).
      { eapply stk_magree; [eapply (inblk_magree m0 m7 _ _ RS 52 AH7); [eapply ainblk_sub; [exact INB| clear - BRS; lia| clear - RSHW HWB; lia]| clear; lia| exact MU7'| exact WM7| exact FFR7| |]| exact RSS1| intros a Ha; exact Ha].
        - cbn [disjoint_from]. clear - RSHW RSWK. lia.
        - cbn [disjoint_from]. clear - SRL LOS. lia. }
      assert (NBS7 : stk bsegs m7 NBP (NBP + 4)).
      { eapply stk_magree; [eapply (inblk_magree m0 m7 _ _ NBP 4 AH7); [exact INNB| clear; lia| exact MU7'| exact WM7| exact FFR7| |]| exact NBS1| intros a Ha; exact Ha].
        - cbn [disjoint_from]. clear - SHNB SWNB WKSZ0. lia.
        - cbn [disjoint_from]. clear - OFFNB LOS. lia. }
      assert (TLS7 : stk bsegs m7 TLP (TLP + 4)).
      { eapply stk_magree; [eapply (inblk_magree m0 m7 _ _ TLP 4 AH7); [exact INTL| clear; lia| exact MU7'| exact WM7| exact FFR7| |]| exact TLS1| intros a Ha; exact Ha].
        - cbn [disjoint_from]. clear - SHTL SWTL WKSZ0. lia.
        - cbn [disjoint_from]. clear - OFFTL LOS. lia. }
      assert (HWZ7 : stk bsegs m7 (HW + 255) (HW + 256)).
      { eapply stk_magree; [eapply (inblk_magree m0 m7 _ _ (HW + 255) 1 AH7); [eapply ainblk_sub; [exact INB| clear - BRS RSHW; lia| clear - HWB; lia]| clear; lia| exact MU7'| exact WM7| exact FFR7| |]| exact HWZ| intros a Ha; cbv beta; clear - Ha; lia].
        - cbn [disjoint_from]. clear - HWWK. lia.
        - cbn [disjoint_from]. clear - SHL LOS. lia. }
      assert (HWS7 : stk bsegs m7 HW (HW + 256)) by (apply (stk_merge bsegs _ HW (HW + 255) (HW + 256) HWA7 HWZ7); clear; lia).
      destruct (FHL _ _ _ _ _ AH7) as [FAB _]. pose proof (ablk_lin _ _ FAB) as (FAa & FAb & FAc & FAd).
      assert (FR7 : rw_cells bsegs m7 (SPV + -64) FRAME).
      { eapply rw_cells_transport; [exact FR| exact MU7| exact WM7|]. cbn [disjoint_from fake_area app cells_size csize Nat.add]. rewrite shad_div. unfold ASHOFF, FAKESZ in *.
        clear - SHF SWF WKSZ0 FAc FAb BOT LOS ATR. repeat split; Z.div_mod_to_equations; lia. }
      hide_all_disj.
      do 4 zstep. zstep. if_cases K3; zify_cond K3.                           (* [comment removed for export] *)
      2:{ (* [comment removed for export] *)
          zstep. eapply (rs_exit_gen AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo HW RS NBP TLP SRC n WK wksz B bsz HY _ rd); try eassumption.
          right. split; [unfold zd_is_error, ZE_maxCode; apply Z.ltb_lt; clear - K3 RDR; lia|]. repeat (split; [assumption|]). assumption. }
      destruct RDP as [RE|RLE]; [exfalso; unfold zd_is_error, ZE_maxCode in RE; apply Z.ltb_lt in RE; clear - RE K3 RDR; lia|].
      eapply (rs_count m7 UB7 UNB7 UTL7 ART7 AH7 MU07 WM07 FFR07 _ c0 rd); try eassumption; try apply munch_refl; try apply wmono_refl; clear - RDR RLE K2 RB0; lia. }
    (* [comment removed for export] *)
    replace (Z.land ((c0 - 256) mod 18446744073709551616) 255) with c0
      by (change 255 with (Z.ones 8); rewrite Z.land_ones by (clear; lia); change (2^8) with 256; clear - RB0 C128; Z.div_mod_to_equations; lia).
    clearbody c0.
    zstep. if_cases K1; zify_lts K1; [|exfalso; clear - K1 RB0 C128; lia].     (* [comment removed for export] *)
    zstep. zstep.                                                              (* [comment removed for export] *)
    replace ((c0 + -126) ≫ 1) with ((c0 - 126) / 2) by (rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^1) with 2; f_equal; clear; lia).
    assert (IQ : 1 <= (c0 - 126) / 2 <= 64 /\ 2 * ((c0 - 126) / 2) <= c0 - 126 <= 2 * ((c0 - 126) / 2) + 1) by (clear - RB0 C128; Z.div_mod_to_equations; lia).
    remember ((c0 - 126) / 2) as isz eqn:EISZ. clear EISZ.
    zstep. if_cases K2; zify_cond K2.
    { eapply (rs_exit_gen AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo HW RS NBP TLP SRC n WK wksz B bsz HY _ 18446744073709551544);
        try eassumption; [clear; lia|].
      right. split; [reflexivity|]. repeat (split; [assumption|]). assumption. }
    zstep. zstep. zstep. if_cases K3; zify_cond K3; [exfalso; clear - K3 RB0 C128; lia|].   (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep. if_cases K4; zify_cond K4; [exfalso; clear - K4 C128 RB0; lia|].    (* [comment removed for export] *)
    (* [comment removed for export] *)
    do 5 zstep. nrm_not.                                                       (* [comment removed for export] *)
    destruct (stk_open bsegs _ HW (HW + 256) HW 256%nat HWS1 ltac:(clear; lia) ltac:(clear; lia)) as (out & OUTC & _ & _).
    assert (OLEN : zlen out = 256) by (destruct OUTC as [[WF _] _]; cbn in WF; destruct WF as [LJ _]; clear - LJ; lia).
    apply u8arr_of_rw_cells in OUTC.
    pose proof (rs_direct m0 UB1 UNB1 UTL1 ART1 AH1 MU1 WM FFR1 N0 ABS RSR RSSR NBSRC' TLSRC' USRC1 (Z.to_nat (c0 - 127)) m0 out isz (c0 + -127) 0) as RD0.
    rewrite !Z.mul_0_r, ?Z.add_0_r in RD0.
    eapply RD0; try eassumption; try apply munch_refl; try apply wmono_refl; clear - IQ K2 RB0 C128; lia.
  Qed.
End RS.

(* [comment removed for export] *)
Theorem huf_rstats_proofA : forall (AI : AMallocIface) (fflag : alayout -> Z -> Z -> Z) (rng_fs : alayout -> footprint -> Prop),
  fake_heap_law AI -> fse_dec_stmtA AI rng_fs -> huf_rstats_stmtA AI rng_fs.
Proof.
  intros AI fflag rng_fs FHL FDEC. unfold huf_rstats_stmtA. intros until src.
  intros AFP AZS TP AROC AB HULLB INB ANB INNB ATL INTL ASRC INSRC HULLS MI STK LO0 LOS WSZ HWS RSS NBS TLS SRCB SRCLEN SRCL NR SRCH WKS WKSZ WKA RSA
         BL BH BRS RSHW RSWK HWB WKB HWWK NBL NBH NBA OFFNB TLL TLH TLA OFFTL NBTL OFFB BNB BTL BSRC NBSRC TLSRC OFFSRC.
  destruct AFP as (AH & ASH & ART & (KLO & RSTK & RI) & RFS & BOT & SPT & SP16 & RSTK2 & LBH).
  pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
  destruct (AB ltac:(clear - BRS RSHW HWB; lia)) as (ABB & UB & RB & RSB).
  destruct ANB as (UNB & RNB & RSNB). destruct ATL as (UTL & RTL & RSTL).
  rewrite (shspan_4 NBP NBA) in RSNB. rewrite (shspan_4 TLP TLA) in RSTL.
  assert (HY : rsA_hyps RNG SPV lo HW RS NBP TLP SRC n WK wksz B bsz).
  { unfold rsA_hyps. repeat (simple apply conj).
    all: first [assumption | clear - SRCLEN; lia | clear - WKSZ; lia | clear - SPT LY3; unfold KEND in *; lia
               | eapply rng_sub'; [exact RSTK2| clear - SPT; lia] ]. }
  unfold APHUF_RSTATS.
  eapply (rs_body AI rng_fs L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo HW RS NBP TLP SRC n WK wksz B bsz
            HY LBH INB INNB INTL HULLB src SRCLEN FHL FDEC); try eassumption.   (* [comment removed for export] *)
Qed.
End CANSEC1.
