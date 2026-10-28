From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_tbl_iface RF_huf_tbl_iface2 RF_huf_fdw_cut RF_huf_fdw_tk
  RF_huf_bdt_model.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Mem Cells.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma fdw_ret : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m m1 : fmem) (DST dcap W wks maxLog lo : Z) (src : list Z) (R : res (list Z)) (a4v : Z)
    (y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
  fse_decompress_wksp (repeat 0 256) dcap src maxLog wks = R ->
  rw_cells usegs m1 (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2;
                                            C8 s1; C8 s0; C8 ra] ->
  stk usegs m1 lo (bv_unsigned sp + -104) ->
  448 <= bv_unsigned sp <= 2^47 -> bv_unsigned sp mod 16 = 0 -> lo <= bv_unsigned sp - 448 -> 0 <= dcap <= 255 ->
  munch [(bv_unsigned sp - FSE_DECOMP_STACK, bv_unsigned sp); (DST, DST + dcap); (W, W + wks)] m m1 ->
  wmono usegs m m1 -> mem_inv usegs m1 ->
  dres DST dcap R m1 a4v ->
  evt usegs (fse_decomp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap W wks maxLog src lo m)
      (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 a4v) y11 y12 y13 y14 y15 y16
               y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
          F (Z_to_bv 64 PFDW_EXIT) fc None m1 (seg_rom usegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 DST dcap W wks maxLog lo src R a4v
    y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31
    FW SAV STK SPB SPA LOS DC MU WM MI DR.
  unfold PFDW_EXIT.
  repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?z) _ _ _ _) => zstep end).
  pose proof (stk_of_rw_cells usegs _ _ _ SAV) as SS. cbn [cells_size csize Nat.add] in SS.
  pose proof (stk_merge usegs _ _ _ _ STK SS ltac:(lia)) as STK'.
  replace (bv_unsigned sp + -104 + Z.of_nat 104) with (bv_unsigned sp) in STK' by lia.
  apply evt_done. unfold fse_decomp_post.
  assert (RNG : 0 <= a4v mod 2^64 < 2^64) by (apply Z.mod_pos_bound; lia).
  do 14 eexists. exists (a4v mod 2^64), m1.
  split; [ f_equal; rewrite (Z_to_bv_eqm (a4v mod 2^64) a4v) by (rewrite Z.mod_mod by lia; reflexivity); reflexivity |].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK'|]. split; [exact RNG|].
  rewrite FW. unfold dres in DR. destruct R as [l|e| |]; try contradiction.
  - destruct DR as (A4 & junk & U & LJ). subst a4v. split.
    + rewrite Z.mod_small; [reflexivity|]. pose proof (Nat2Z.is_nonneg (length junk)). pose proof (Nat2Z.is_nonneg (length l)). lia.
    + exists junk. split; [exact U | exact LJ].
  - destruct DR as (A4 & E). subst a4v. split; [| exact E].
    symmetry. apply Z.mod_unique with (-1); lia.
Qed.

(* [comment removed for export] *)
Lemma fdw_K_ok : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m m1 : fmem) (DST dcap W wks maxLog lo : Z) (src : list Z) (R : res (list Z)),
  fse_decompress_wksp (repeat 0 256) dcap src maxLog wks = R ->
  rw_cells usegs m1 (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2;
                                            C8 s1; C8 s0; C8 ra] ->
  wr_at usegs m1 (bv_unsigned sp + -192) 88 ->
  stk usegs m1 lo (bv_unsigned sp + -192) ->
  448 <= bv_unsigned sp <= 2^47 -> bv_unsigned sp mod 16 = 0 -> lo <= bv_unsigned sp - 448 -> 0 <= dcap <= 255 ->
  0 <= DST -> DST + dcap <= lo ->
  munch [(bv_unsigned sp - FSE_DECOMP_STACK, bv_unsigned sp); (DST, DST + dcap); (W, W + wks)] m m1 ->
  wmono usegs m m1 ->
  fdw_K (bv_unsigned sp + -192) gp tp F fc m1 DST dcap lo
        (fse_decomp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap W wks maxLog src lo m) R.
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 DST dcap W wks maxLog lo src R
    FW SAV WR STK SPB SPA LOS DC DST0 DSTL MU WM.
  unfold fdw_K. intros m2 a4v y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28
    y29 y30 y31 MU2 WM2 MI2 STK2 DR.
  assert (SA : bv_unsigned sp + -192 + 88 = bv_unsigned sp + -104) by lia.
  apply (wr_at_transport usegs m1 m2) in WR; [| exact WM2].
  pose proof (stk_of_wr_at _ _ _ WR) as S88. rewrite SA in S88.
  pose proof (stk_merge usegs _ _ _ _ STK2 S88 ltac:(lia)) as STK3.
  apply (rw_cells_transport usegs [(bv_unsigned sp + -192 + 16, bv_unsigned sp + -192 + 88); (DST, DST + dcap)] m1 m2) in SAV;
    [| exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; repeat split; lia].
  assert (MU3 : munch [(bv_unsigned sp - FSE_DECOMP_STACK, bv_unsigned sp); (DST, DST + dcap); (W, W + wks)] m m2).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2].
    unfold sub_fp, FSE_DECOMP_STACK; intros x Hx; cbn [outside] in *. repeat split; lia. }
  eapply fdw_ret; [exact FW | exact SAV | exact STK3 | lia | lia | lia | lia | exact MU3 | | exact MI2 | exact DR].
  exact (wmono_trans usegs _ _ _ WM WM2).
Qed.

(* [comment removed for export] *)
Lemma fdw_m_ok : forall dcap src maxLog wks nc msv tl hn dt,
  512 <= wks -> read_ncount (repeat 0 256) 255 src = Ok (nc, msv, tl, hn) -> tl <= maxLog ->
  FSE_DECOMPRESS_WKSP_SIZE tl msv <= wks -> 0 <= hn <= zlen src ->
  build_dtable nc msv tl (wks - 512 - FSE_DTABLE_SIZE tl) = Ok dt ->
  fse_decompress_wksp (repeat 0 256) dcap src maxLog wks
  = decompress_usingDTable (skipn (Z.to_nat hn) src) dt dcap (negb (dt_fastMode dt =? 0)).
Proof.
  intros dcap src maxLog wks nc msv tl hn dt W RN TM WS HN BD.
  unfold fse_decompress_wksp. change FSE_MAX_SYMBOL_VALUE with 255.
  rewrite (proj2 (Z.ltb_ge wks 512) W), RN. cbn [bind].
  rewrite (proj2 (Z.ltb_ge maxLog tl) TM), (proj2 (Z.ltb_ge wks (FSE_DECOMPRESS_WKSP_SIZE tl msv)) WS).
  assert (ZE : FseNCount.Zlength src = zlen src) by reflexivity.
  rewrite ZE, (proj2 (Z.leb_le 0 hn) (proj1 HN)), (proj2 (Z.leb_le hn (zlen src)) (proj2 HN)).
  cbn [andb assert bind]. rewrite BD. cbn [bind]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fdw_bdt_ok : forall nc msv tl wks', ncount_ok nc msv tl -> tl <= 12 -> msv <= 255 ->
  FSE_BUILD_DTABLE_WKSP_SIZE tl msv <= wks' ->
  exists dt, build_dtable nc msv tl wks' = Ok dt /\ dt_tableLog dt = tl /\ zlen (dt_cells dt) = 2^tl
             /\ cells_ok tl (dt_cells dt) /\ (dt_fastMode dt = 0 \/ dt_fastMode dt = 1)
             /\ (dt_fastMode dt = 1 -> Forall (fun c => 1 <= dc_nbBits c) (dt_cells dt)).
Proof.
  intros nc msv tl wks' HOK T12 M255 W.
  destruct (build_dtable_ok nc msv tl HOK wks' ltac:(unfold FSE_MAX_TABLELOG; lia) W) as (dt & BD & TL & ZL & FM & FC).
  exists dt. split; [exact BD|]. split; [exact TL|]. split; [exact ZL|]. split; [|split; [exact FM|]].
  unfold cells_ok. eapply Forall_impl; [|exact FC].
  intros c CK. unfold cell_ok in CK. cbv zeta in CK. destruct CK as (CS & CN & CW & CE & _). lia.
  intros F1. eapply Forall_impl; [|exact FC].
  intros c CK. unfold cell_ok in CK. cbv zeta in CK. destruct CK as (_ & _ & _ & _ & CF). exact (CF F1).
Qed.

(* [comment removed for export] *)
Lemma fdw_dt_split : forall m DT d, u8arr usegs m DT (fse_dt_bytes d) ->
  rw_cells usegs m DT [C2 (Z_to_bv 64 (dt_tableLog d)); C2 (Z_to_bv 64 (dt_fastMode d))]
  /\ bytes_at usegs m (DT + 4) (concat (map fse_cell_bytes (dt_cells d))).
Proof.
  intros m DT d U. unfold fse_dt_bytes in U. rewrite app_assoc in U.
  apply u8arr_app in U. destruct U as ((BA & WR) & (BB & _)).
  rewrite length_app, !Mem.length_le2 in WR, BB. change (Z.of_nat (2 + 2)) with 4 in WR, BB.
  split; [|exact BB].
  unfold rw_cells, Cells.cells_at. cbn [Cells.cells_wf Cells.cell_wf Cells.cells_bytes Cells.cbytes Cells.cells_size Cells.csize].
  rewrite app_nil_r. split; [split; [tauto | exact BA] | exact WR].
Qed.
