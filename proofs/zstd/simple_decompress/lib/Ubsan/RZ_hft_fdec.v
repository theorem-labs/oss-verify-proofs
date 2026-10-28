(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound ZdFrame ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RF_fse_iface RF_fse_rd_err RZ_huf_iface RZ_hft_iface RZ_hft_kit RZ_hft_fdec_defs RZ_hft_fdec_epi
     RZ_hft_fdec_l1 RZ_hft_fdec_t1 RZ_hft_fdec_l3 RZ_hft_fdec_t2 RZ_hft_fdec_ini RZ_hft_fdec_inif RZ_fse_decf_kit fse_kit_dsym fse_kit_dsymf fse_kit_reload.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma land_m4 : forall x, 0 <= x < 4096 -> Z.land x 9223372036854775804 = 4 * (x / 4).
Proof.
  assert (B : forallb (fun x => Z.land x 9223372036854775804 =? 4 * (x / 4)) (map Z.of_nat (seq 0 4096)) = true) by (vm_compute; reflexivity).
  intros x Hx. rewrite forallb_forall in B. apply Z.eqb_eq. apply B. apply in_map_iff. exists (Z.to_nat x). split; [lia|]. apply in_seq. lia.
Qed.

(* [comment removed for export] *)
Lemma read_ncount_err_code : forall nc0 maxSV buf e, all_bytes buf -> 0 <= maxSV -> maxSV + 1 <= FseNCount.Zlength nc0 ->
  read_ncount nc0 maxSV buf = Err e -> e = 20 \/ e = 44.
Proof.
  intros nc0 maxSV buf e HB HM HL E. unfold read_ncount in E. cbv zeta in E.
  destruct (Z.ltb_spec (FseNCount.Zlength buf) 8) as [S|S].
  - set (buf8 := buf ++ repeat 0 (Z.to_nat (8 - FseNCount.Zlength buf))) in *.
    assert (HB8 : all_bytes buf8).
    { subst buf8. apply Forall_all_bytes. apply Forall_app. split; [apply all_bytes_Forall; exact HB|].
      apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia. }
    assert (HL8 : Z.of_nat (length buf8) = 8) by (subst buf8; unfold FseNCount.Zlength in *; rewrite length_app, repeat_length; lia).
    destruct (read_ncount_body8 buf8 (maxSV + 1) nc0) as [[[[nc msv] tl] cs]|e'| |] eqn:B8; cbn [bind] in E; try discriminate E.
    + destruct (FseNCount.Zlength buf <? cs); [injection E as <-; left; reflexivity | discriminate E].
    + injection E as <-. destruct (read_body8_err_inv buf8 (maxSV + 1) nc0 e' ltac:(lia) HB8 ltac:(unfold FseNCount.Zlength in *; lia) B8) as [(_ & ->)|(_ & -> & _)]; [right|left]; reflexivity.
  - destruct (read_body8_err_inv buf (maxSV + 1) nc0 e ltac:(unfold FseNCount.Zlength in *; lia) HB ltac:(unfold FseNCount.Zlength in *; lia) E) as [(_ & ->)|(_ & -> & _)]; [right|left]; reflexivity.
Qed.

Section ENTRY.
  Hypothesis READ : fse_read_body_any_stmt.
  Hypothesis BDT : fse_bdt_stmt.
  Hypothesis BINIT : bit_init_stmt_at 0x2bd40.
  Hypothesis INITDS : fse_initds_stmt.

  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo DST cap SRC n ml WK wksz : Z) (src : list byte).
  Hypothesis LO0 : 4096 <= lo.  Hypothesis LOS : lo <= SPV - 448.  Hypothesis SPR : SPV < 2^47.  Hypothesis SPA : SPV mod 16 = 0.
  Hypothesis DSTL : 4096 <= DST.  Hypothesis CAPR : 0 <= cap <= 65536.  Hypothesis DSTH : DST + cap < 2^47.
  Hypothesis SRCLEN : Z.of_nat (length src) = n.  Hypothesis SRCL : 4096 <= SRC.  Hypothesis NR : n <= 65536.  Hypothesis SRCH : SRC + n < 2^47.
  Hypothesis WKL : 4096 <= WK.  Hypothesis WKSZ : 0 <= wksz < 2^32.  Hypothesis WKH : WK + wksz < 2^47.  Hypothesis WKA : WK mod 4 = 0.
  Hypothesis MLR : 0 <= ml <= 9.
  Hypothesis OFFDST : DST + cap <= lo \/ SPV <= DST.  Hypothesis OFFWK : WK + wksz <= lo \/ SPV <= WK.  Hypothesis OFFSRC : SRC + n <= lo \/ SPV <= SRC.
  Hypothesis DSTWK : DST + cap <= WK \/ WK + wksz <= DST.  Hypothesis DSTSRC : DST + cap <= SRC \/ SRC + n <= DST.
  Hypothesis WKSRC : WK + wksz <= SRC \/ SRC + n <= WK.

  Notation POST := (fse_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST cap WK wksz lo m).
  Notation STF pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -192)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Lemma fd_exit1 : forall m1 out j0 wa wb (ws : list Z) f2 f1 fb r x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    u8arr usegs m1 DST out -> Z.of_nat (length out) = cap ->
    u8arr usegs m1 WK (u16s (map (Z_to_bv 64) ws)) -> length ws = 256%nat -> stk usegs m1 (WK + 512) (WK + wksz) -> 512 <= wksz ->
    stk usegs m1 lo (SPV + -192) ->
    rw_cells usegs m1 (SPV + -192) [CB 8 j0] -> rw_cells usegs m1 (SPV + -184) [C4 wa] -> rw_cells usegs m1 (SPV + -180) [C4 wb] ->
    rw_cells usegs m1 (SPV + -176) f2 -> cells_size f2 = 16%nat ->
    rw_cells usegs m1 (SPV + -160) f1 -> cells_size f1 = 16%nat -> rw_cells usegs m1 (SPV + -144) fb -> cells_size fb = 40%nat ->
    rw_cells usegs m1 (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    mem_inv usegs m1 -> munch [(DST, DST + cap); (WK, WK + wksz); (SPV - 448, SPV)] m m1 -> wmono usegs m m1 ->
    0 <= r < 2^64 -> (zd_is_error r = true \/ r <= cap) ->
    evt usegs POST (STF 0x2b964 m1 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros OUT OLEN NCC LWS WKR K0 STK F0a FM FT FS2 SZ2 FS1 SZ1 FBD SZB FSAV MI MU WM RR RES.
    assert (WKS : stk usegs m1 WK (WK + wksz)).
    { apply rw_cells_of_u8arr in NCC. apply stk_of_rw_cells in NCC. cbn [cells_size csize] in NCC. rewrite u16s_length, length_map, LWS in NCC.
      apply (stk_merge usegs m1 WK (WK + 512) (WK + wksz)); [exact NCC | exact WKR | lia]. }
    assert (F0 : rw_cells usegs m1 (SPV + -192) ([CB 8 j0] ++ [C4 wa] ++ [C4 wb])).
    { apply (proj2 (rw_cells_app usegs m1 (SPV + -192) [CB 8 j0] ([C4 wa] ++ [C4 wb]))). split; [exact F0a|].
      cbn [cells_size csize Nat.add]. replace (SPV + -192 + Z.of_nat 8) with (SPV + -184) by lia.
      apply (proj2 (rw_cells_app usegs m1 (SPV + -184) [C4 wa] [C4 wb])). split; [exact FM|].
      cbn [cells_size csize Nat.add]. replace (SPV + -184 + Z.of_nat 4) with (SPV + -180) by lia. exact FT. }
    eapply fd_epi0; try eassumption; try reflexivity; try lia.
  Qed.

  Theorem fse_dec_body : forall (t0 t1 t2 bmi2 t3 t4 t5 t6 : word),
    mem_inv usegs m -> stk usegs m lo SPV -> stk usegs m DST (DST + cap) -> bytes_at usegs m SRC src -> stk usegs m WK (WK + wksz) ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 cap) (Z_to_bv 64 SRC) (Z_to_bv 64 n)
               (Z_to_bv 64 ml) (Z_to_bv 64 WK) (Z_to_bv 64 wksz) bmi2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PFSE_DEC) fc None m (seg_rom usegs)).
  Proof.
    intros t0 t1 t2 bmi2 t3 t4 t5 t6 MI STK DSTS SRCB WKS. unfold PFSE_DEC.
    assert (MU : munch [(DST, DST + cap); (WK, WK + wksz); (SPV - 448, SPV)] m m) by apply munch_refl.
    assert (WM : wmono usegs m m) by apply wmono_refl.
    (* [comment removed for export] *)
    destruct (stk_open usegs _ DST (DST + cap) DST (Z.to_nat cap) DSTS ltac:(lia) ltac:(lia)) as (out & OUTC & _ & _).
    assert (OLEN : Z.of_nat (length out) = cap) by (destruct OUTC as [[WF _] _]; cbn in WF; destruct WF as [LJ _]; lia).
    apply u8arr_of_rw_cells in OUTC. rename OUTC into OUT. clear DSTS.
    zstep. carve_frame 192%nat STK.
    do 13 zstep.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ (CB 88 ?j :: ?post) =>
      apply (rw_cells_split_CB usegs _ _ [] 88 j post [8; 4; 4; 16; 16; 40]%nat) in FR; [| reflexivity] end.
    cbn [mk_CB_cells app] in FR.
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: CB 4 ?j :: ?post) => destruct (hcb4_as_c4 usegs _ _ [c0] j post FR) as [wm FR1] end. cbn [app] in FR1. clear FR.
    lazymatch type of FR1 with rw_cells _ _ _ (?c0 :: ?c1 :: CB 4 ?j :: ?post) => destruct (hcb4_as_c4 usegs _ _ [c0; c1] j post FR1) as [wt FR] end. cbn [app] in FR. clear FR1.
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?rest) =>
      apply (proj1 (rw_cells_app usegs _ _ [c0; c1; c2] rest)) in FR; destruct FR as [F0 FR] end.
    cbn [cells_size csize Nat.add] in FR. replace (SPV + -192 + Z.of_nat 16) with (SPV + -176) in FR by lia.
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?rest) =>
      apply (proj1 (rw_cells_app usegs _ _ [c0] rest)) in FR; destruct FR as [FS2 FR] end.
    cbn [cells_size csize Nat.add] in FR. replace (SPV + -176 + Z.of_nat 16) with (SPV + -160) in FR by lia.
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?rest) =>
      apply (proj1 (rw_cells_app usegs _ _ [c0] rest)) in FR; destruct FR as [FS1 FR] end.
    cbn [cells_size csize Nat.add] in FR. replace (SPV + -160 + Z.of_nat 16) with (SPV + -144) in FR by lia.
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?rest) =>
      apply (proj1 (rw_cells_app usegs _ _ [c0] rest)) in FR; destruct FR as [FBD FSAV] end.
    cbn [cells_size csize Nat.add] in FSAV. replace (SPV + -144 + Z.of_nat 40) with (SPV + -104) in FSAV by lia.
    do 5 zstep.
    zstep. if_cases K; zify_cond K; [| exfalso; lia]. clear K.
    do 4 zstep. zstep. try (if_cases Ka; zify_cond Ka; [| zb_refute Ka]).
    zstep. zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      zstep. if_cases Kb; zify_cond Kb; [| exfalso; lia].
      assert (WK1 : Z.land WK 1 = WK mod 2) by (apply (Z.land_ones WK 1); lia).
      assert (WK2 : WK mod 2 = 0) by (clear - WKA; Z.div_mod_to_equations; lia).
      zstep. zstep. if_cases Kc; zify_cond Kc; [| exfalso; rewrite ?WK1, ?WK2 in Kc; lia].
      (* [comment removed for export] *)
      destruct (stk_split usegs _ WK (WK + 512) (WK + wksz) WKS ltac:(lia)) as [WKN WKR].
      destruct (stk_open usegs _ WK (WK + 512) WK 512%nat WKN ltac:(lia) ltac:(lia)) as (jn & NCC & _ & _).
      assert (LJN : length jn = 512%nat) by (destruct NCC as [[WF _] _]; cbn in WF; destruct WF as [LJ _]; exact LJ).
      apply u8arr_of_rw_cells in NCC.
      destruct (u16s_of_bytes 256 jn LJN) as (rt0 & LRT0 & _ & ERT0). rewrite ERT0 in NCC. clear WKN ERT0 LJN.
      (* [comment removed for export] *)
      pose proof SRCB as SRCZ. rewrite <- (bytes_of_unsigned src) in SRCZ.
      remember (map bv_unsigned src) as buf eqn:EBUF.
      assert (BUFL : Z.of_nat (length buf) = n) by (subst buf; rewrite length_map; exact SRCLEN).
      assert (BUFB : Forall (fun c => 0 <= c < 256) buf) by (subst buf; apply bytes_unsigned_range).
      clear EBUF.
      (* [comment removed for export] *)
      lazymatch type of F0 with rw_cells _ _ _ (?c0 :: ?rest) =>
        apply (proj1 (rw_cells_app usegs _ _ [c0] rest)) in F0; destruct F0 as [F0a F0] end.
      cbn [cells_size csize Nat.add] in F0. replace (SPV + -192 + Z.of_nat 8) with (SPV + -184) in F0 by lia.
      lazymatch type of F0 with rw_cells _ _ _ (?c0 :: ?rest) =>
        apply (proj1 (rw_cells_app usegs _ _ [c0] rest)) in F0; destruct F0 as [FM FT] end.
      cbn [cells_size csize Nat.add] in FT. replace (SPV + -184 + Z.of_nat 4) with (SPV + -180) in FT by lia.
      do 11 zstep.
      zstep.
      assert (ZR : zlen rt0 = 256) by (unfold zlen; rewrite LRT0; reflexivity).
      assert (ZB : zlen buf = n) by (unfold zlen; exact BUFL).
      eapply evt_cut.
      { eapply (READ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (SPV + -192) WK (SPV + -184) (SPV + -180) SRC rt0 buf 255 lo wt);
          rewrite ?ZR, ?ZB; try eassumption; try reflexivity; unfold FSE_READ_STACK; try lia; try (clear - SPA WKA; Z.div_mod_to_equations; lia). }
      pose proof (read_ncount_total rt0 255 buf (Forall_all_bytes _ BUFB) ltac:(lia) ltac:(unfold FseNCount.Zlength; lia)) as TOT.
      intros ms' [(rt & msv & tl & hn & RN & PO) | (e & RN & PO)]; revert ms' PO; unfold fse_read_post, fse_read_err_post, FSE_READ_STACK; post_call usegs m1.
      + (* [comment removed for export] *)
        destruct TOT as [(rt' & msv' & tl' & n' & RN' & LRT & MSVR & TLR & HNR & _ & _ & WS) | (e' & RN')]; [|rewrite RN in RN'; discriminate RN'].
        rewrite RN in RN'. injection RN' as <- <- <- <-.
        unfold FseNCount.Zlength in *.
        zstep. zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
        zstep. zstep. rewrite (sx32w_small tl) by lia.
        zstep. zstep. if_cases K2; zify_cond K2.
        * (* [comment removed for export] *)
          replace (Z_to_bv 64 (-44)) with (Z_to_bv 64 18446744073709551572) by (apply bv_eq; reflexivity).
          eapply (fd_exit1 _ out _ _ _ rt _ _ _ 18446744073709551572); try eassumption; try reflexivity; try lia.
          left; reflexivity.
        * zstep. zstep. if_cases K3; zify_cond K3; [| exfalso; lia].
          do 3 zstep. zstep. try (if_cases K4; zify_cond K4; [| zb_refute K4]).
          zstep. zstep. if_cases K5; zify_cond K5; [| exfalso; lia].
          zstep. zstep. zstep. rewrite (sx32w_small msv) by lia.
          assert (P2 : 32 <= 2^tl <= 512) by (split; [change 32 with (2^5); apply Z.pow_le_mono_r; lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
          zstep. rewrite (sllw_pow2 tl) by lia.
          zstep. replace (1 ≪ (tl mod 64)) with (2^tl) by (rewrite Z.mod_small by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
          zstep. replace (2^tl ≪ 2) with (4 * 2^tl) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
          zstep. zstep. zstep.
          replace ((msv + 1) ≪ 32) with ((msv + 1) * 4294967296) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
          zstep.
          replace (((msv + 1) * 4294967296) ≫ 31) with (2 * (msv + 1))
            by (rewrite Z.shiftr_div_pow2 by lia; change 4294967296 with (2 * 2^31); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
          zstep. zstep. zstep. zstep. zstep. zstep.
          rewrite (land_m4 (4 * 2 ^ tl + 2 ^ tl + 2 * (msv + 1) + 19)) by lia.
          set (need0 := 4 * ((4 * 2 ^ tl + 2 ^ tl + 2 * (msv + 1) + 19) / 4)).
          assert (NEED : 5 * 2^tl + 2 * (msv + 1) + 16 <= need0 <= 5 * 2^tl + 2 * (msv + 1) + 19) by (unfold need0; Z.div_mod_to_equations; lia).
          clearbody need0.
          zstep. if_cases K6; zify_cond K6.
          -- replace (Z_to_bv 64 (-44)) with (Z_to_bv 64 18446744073709551572) by (apply bv_eq; reflexivity).
             eapply (fd_exit1 _ out _ _ _ rt _ _ _ 18446744073709551572); try eassumption; try reflexivity; try lia.
             left; reflexivity.
          -- zstep. zstep. zstep. if_cases K7; zify_cond K7; [| exfalso; rewrite zb_lxor_ones in K7 by lia; lia].
             do 5 zstep.
             set (W := WK + 512 + (4 * 2 ^ tl + 4)) in *. set (wlen := wksz - (4 * 2 ^ tl + 4) + -512) in *.
             destruct (stk_split usegs _ (WK + 512) W (WK + wksz) WKR ltac:(unfold W; lia)) as [DTS WS2].
             replace W with (WK + 512 + 4 + 4 * 2^tl) in DTS by (unfold W; lia).
             replace (WK + wksz) with (W + wlen) in WS2 by (unfold W, wlen; lia).
             specialize (WS ltac:(lia)). destruct WS as (NGE & NSUM).
             zstep.
             eapply evt_cut.
             { eapply (BDT _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (SPV + -192) (WK + 512) WK W wlen msv tl lo rt);
                 try eassumption; try reflexivity; try (unfold W, wlen; lia); try (clear - WKA; unfold W; Z.div_mod_to_equations; lia).
               all: try (match goal with H : u8arr _ _ WK _ |- _ => exact (proj1 H) end). }
             unfold fse_bdt_post. lazymatch goal with |- forall ms', _ -> evt _ _ _ => idtac end.
             lazymatch goal with MIx : mem_inv usegs ?mm |- _ => post_call usegs mm end.
             rename x29 into rb. rename PC3 into RBR. rename PC into STK'. rename PC2 into WS2'.
             zstep. zstep. if_cases K8; zify_cond K8.
             { (* [comment removed for export] *)
               destruct POST0 as [(RB0 & _) | (RBE & DTS')]; [exfalso; lia|].
               clear K8.
               eapply (fd_exit1 _ out _ _ _ rt _ _ _ rb); try eassumption; try reflexivity; try lia.
               { apply (stk_merge usegs _ (WK + 512) (WK + 512 + 4 + 4 * 2^tl) (WK + wksz) DTS'); [|lia].
                 replace (WK + 512 + 4 + 4 * 2^tl) with W by (unfold W; lia). replace (WK + wksz) with (W + wlen) by (unfold W, wlen; lia). exact WS2'. }
               left; exact RBE. }
             destruct POST0 as [(RB0 & fast & tb & HDR & CELU & TBLEN & FASTR & TBBY & TBOK) | (RBE & _)]; [| exfalso; unfold zd_is_error, ZE_maxCode in RBE; apply Z.ltb_lt in RBE; lia].
             zstep. zstep. rewrite (zx16_u fast) by lia.
             do 7 zstep.
             assert (WKS' : stk usegs x28 WK (WK + wksz)).
             { pose proof PC0 as NCS. apply rw_cells_of_u8arr in NCS. apply stk_of_rw_cells in NCS. cbn [cells_size csize] in NCS. rewrite u16s_length, length_map, LRT, LRT0 in NCS.
               pose proof HDR as HS. apply stk_of_rw_cells in HS. cbn [cells_size csize Nat.add] in HS.
               pose proof CELU as CS. apply rw_cells_of_u8arr in CS. apply stk_of_rw_cells in CS. cbn [cells_size csize] in CS. rewrite length_map in CS.
               apply (stk_merge usegs _ WK (WK + 512) (WK + wksz)); [replace (WK + 512) with (WK + Z.of_nat (2 * 256 + 0)) by lia; exact NCS | | lia].
               apply (stk_merge usegs _ (WK + 512) (WK + 512 + 4) (WK + wksz)); [exact HS | | lia].
               apply (stk_merge usegs _ (WK + 512 + 4) W (WK + wksz)); [ | replace (WK + wksz) with (W + wlen) by (unfold W, wlen; lia); exact WS2' | unfold W; lia].
               replace W with (WK + 512 + 4 + Z.of_nat (length tb + 0)) by (unfold W; pose proof (TBLEN : Z.of_nat (length tb) = 4 * 2^tl); lia). exact CS. }
             assert (HNN : 1 <= hn <= n) by (rewrite <- ZB; lia).
             assert (TBLD : fd_tbl tl fast tb) by (split; [exact TBLEN | split; [exact TBBY | exact TBOK]]).
             assert (SRCIB : bytes_at usegs x28 (hn + SRC) (skipn (Z.to_nat hn) src)).
             { pose proof SRCB as SB. rewrite <- (firstn_skipn (Z.to_nat hn) src) in SB. apply bytes_at_app in SB. destruct SB as [_ SB].
               rewrite length_firstn in SB. replace (SRC + Z.of_nat (Nat.min (Z.to_nat hn) (length src))) with (hn + SRC) in SB by lia. exact SB. }
             assert (SRCIL : Z.of_nat (length (skipn (Z.to_nat hn) src)) = n - hn) by (rewrite length_skipn; lia).
             assert (FDIx : FDI ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DST cap WK wksz (hn + SRC) (WK + 512) tl (skipn (Z.to_nat hn) src) tb out x28).
             { unfold FDI.
               split; [exact OUT|]. split; [exact OLEN|]. split; [exact WKS'|]. split; [exact SRCIB|].
               split. { pose proof (SysStep.rw_cells_bytes_at _ _ _ _ HDR) as HB. cbn [cells_bytes cbytes] in HB. apply bytes_at_app in HB. exact (proj1 HB). }
               split. { pose proof CELU as CB0. apply rw_cells_of_u8arr in CB0. pose proof (SysStep.rw_cells_bytes_at _ _ _ _ CB0) as HB. cbn [cells_bytes cbytes] in HB.
                        rewrite app_nil_r in HB. exact HB. }
               split; [exact STK'|].
               split. { do 3 eexists. apply (proj2 (rw_cells_app usegs _ (SPV + -192) [CB 8 _] ([C4 _] ++ [C4 _]))). split; [exact F0a|].
                        cbn [cells_size csize Nat.add]. replace (SPV + -192 + Z.of_nat 8) with (SPV + -184) by lia.
                        apply (proj2 (rw_cells_app usegs _ (SPV + -184) [C4 _] [C4 _])). split; [exact PC1|].
                        cbn [cells_size csize Nat.add]. replace (SPV + -184 + Z.of_nat 4) with (SPV + -180) by lia. exact POST. }
               split; [eexists; exact FS2|]. split; [eexists; exact FS1|]. split; [eexists; exact FBD|].
               split; [exact FSAV|]. split; [exact MI|]. split; [exact MU | exact WM]. }
             assert (HYD : fd_hyps SPV lo DST cap (hn + SRC) (n - hn) (WK + 512) tl) by (unfold fd_hyps; repeat split; lia).
             assert (LOSU : lo <= SPV - 192) by lia.
             assert (DTA2 : (WK + 512) mod 2 = 0) by (clear - WKA; Z.div_mod_to_equations; lia).
             assert (DTA4 : (WK + 512) mod 4 = 0) by (clear - WKA; Z.div_mod_to_equations; lia).
             assert (WKR0 : 0 <= wksz) by lia.
             pose proof fse_reload_proof as RELOAD. pose proof fse_dsym_proof as DSYM. pose proof fse_dsymf_proof as DSYMF.
             rewrite (proj2 (Z.ltb_lt 0 DST)) by lia.
             rewrite (proj2 (Z.ltb_ge (DST + cap) DST)) by lia.
             rewrite (proj2 (Z.ltb_ge (DST + cap) 1)) by lia.
             cbn [Z.b2z].
             repeat match goal with
             | |- context [Z.lxor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v
             | |- context [Z.land ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v
             end.
             zstep. if_cases K9; zify_cond K9.
             { (* [comment removed for export] *)
               eapply fd_nf_init; eassumption. }
             assert (FAST1 : fast = 1) by lia.
             eapply fd_f_init; eassumption.
      + (* [comment removed for export] *)
        destruct (read_ncount_err_code rt0 255 buf e (Forall_all_bytes _ BUFB) ltac:(lia) ltac:(unfold FseNCount.Zlength; lia) RN) as [-> | ->].
        all: zstep; zstep; (if_cases K1; zify_cond K1; [| exfalso; lia]).
        1: eapply (fd_exit1 _ out _ _ _ _ _ _ _ 18446744073709551596); try eassumption; try reflexivity; try lia; [left; reflexivity].
        1: eapply (fd_exit1 _ out _ _ _ _ _ _ _ 18446744073709551572); try eassumption; try reflexivity; try lia; [left; reflexivity].
    - (* [comment removed for export] *)
      zstep. zstep.
      replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; reflexivity).
      eapply fd_epi0; try eassumption; try reflexivity; try lia; [left; reflexivity].
  Qed.
End ENTRY.

(* [comment removed for export] *)
Theorem fse_dec_proof : fse_read_body_any_stmt -> fse_bdt_stmt -> bit_init_stmt_at 0x2bd40 -> fse_initds_stmt -> fse_dec_stmt.
Proof.
  intros READ BDT BINIT INITDS. unfold fse_dec_stmt. intros.
  eapply (fse_dec_body READ BDT BINIT INITDS); eassumption.
Qed.
