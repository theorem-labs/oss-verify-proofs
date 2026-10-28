(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount HufPure_FseDecomp.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseRdKit FseRdKit2 HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

Ltac rd_refresh S bs :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mg _) =>
  tryif (match goal with _ : ov_read_bytes usegs mg (Z_to_bv 64 (S + _)) 1 = Some _ |- _ => idtac end) then idtac
  else (
  repeat match goal with H : ov_read_bytes usegs _ (Z_to_bv 64 (S + _)) 1 = Some _ |- _ => clear H end;
  lazymatch goal with
  | EL : zlen bs = ?N, H : bytes_at usegs mg S (map (Z_to_bv 8) bs) |- _ =>
    let t k := let b := eval vm_compute in (k <? N) in
               lazymatch b with
               | true => pose proof (src_rd usegs mg S bs k H ltac:(rewrite EL; split; [discriminate| reflexivity]))
               | false => idtac
               end in
    t 0; t 1; t 2; t 3; t 4; t 5; t 6
  end) end.

(* [comment removed for export] *)
Ltac dec_if := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  let b := eval vm_compute in c in change c with b; cbv iota end.

Ltac step_to S bs pc := repeat (lazymatch goal with
   | |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail
   | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => dec_if
   | |- evt _ _ (MS _ _ _ _ _ _ _) => rd_refresh S bs; zstep end).

(* [comment removed for export] *)
Ltac hb_byte r :=
  zstep; zstep; zstep; brute_reg 11%Z r 1 255 sm1;
  zstep; zstep; zstep; brute_reg 11%Z r 1 255 sm2;
  zstep; zstep; brute_reg 11%Z r 1 255 sm3;
  zstep; brute_reg 11%Z r 1 255 nsm;
  zstep; zstep; zstep; zstep; zstep; brute_reg 11%Z r 1 255 (fun r0 => pc_a (nsm r0));
  zstep; zstep; zstep; zstep; zstep; brute_reg 11%Z r 1 255 (fun r0 => pc_b (pc_a (nsm r0)));
  zstep; zstep; brute_reg 11%Z r 1 255 (fun r0 => pc_c (pc_b (pc_a (nsm r0))));
  zstep; zstep; zstep; zstep; zstep; brute_reg 11%Z r 1 255 (fun r0 => pc_d (pc_c (pc_b (pc_a (nsm r0)))));
  zstep; brute_reg 11%Z r 1 255 (fun r0 => 31 - Z.log2 r0).

Ltac hb_byte_s r :=
  zstep; zstep; zstep; brute_reg 11%Z r 1 255 sm1;
  zstep; zstep; zstep; brute_reg 11%Z r 1 255 sm2;
  zstep; zstep; brute_reg 11%Z r 1 255 sm3;
  zstep; brute_reg 11%Z r 1 255 nsm;
  zstep; zstep; zstep; zstep; zstep; brute_reg 11%Z r 1 255 (fun r0 => pc_a (nsm r0));
  zstep; zstep; zstep; zstep; zstep; brute_reg 11%Z r 1 255 (fun r0 => pc_b (pc_a (nsm r0)));
  zstep; zstep; brute_reg 11%Z r 1 255 (fun r0 => pc_c (pc_b (pc_a (nsm r0))));
  zstep; zstep; zstep; zstep; zstep; zstep; brute_reg 11%Z r 1 255 (fun r0 => pc_d (pc_c (pc_b (pc_a (nsm r0))))).

(* [comment removed for export] *)
Ltac lit_sub := repeat match goal with |- context [Znth (?a - ?b) _] =>
  let c := eval vm_compute in (a - b) in change (a - b) with c end.

Ltac small_cont ELn ER RB BYn :=
  unfold lesmall; rewrite ELn; cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont];
  lazymatch type of ELn with _ = ?N =>
    let t k := let b := eval vm_compute in (k <? N) in
               lazymatch b with true => pose proof (BYn k ltac:(lia)) | false => idtac end in
    t 0; t 1; t 2; t 3; t 4; t 5; t 6 end;
  repeat (rewrite byte_lit by lia);
  rewrite ?Z.shiftl_mul_pow2 by lia;
  rewrite ?(Z.mod_small (_ * 2^48) 18446744073709551616) by lia;
  rewrite ?lor_shift_add by lia;
  subst; lia.

Lemma bit_init_proof : bit_init_stmt PHUF_BIT_INIT.
Proof.
  unfold PHUF_BIT_INIT.
  intros until lo. intros RJ D8 D0 SRC BY S0 DT ST DJ STK SPD MI -> -> ->. 
  set (n := zlen bs) in *. assert (ELn : zlen bs = n) by reflexivity.
  pose proof (munch_refl [(D, D + 40)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  idtac.
  assert (N0 : 0 <= n) by (unfold n; lia).
  zstep. if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    do 7 zstep.
    assert (BS0 : bs = []) by (apply length_zero_iff_nil; unfold n in K; lia).
    apply evt_done. unfold bit_init_post.
    do 7 eexists. exists (-72). eexists.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|]. split; [exact SRC|].
    rewrite BS0. cbn. split; [reflexivity|].
    destruct (rw_cells_forget _ _ _ _ RJ) as (j' & RJ'). exists j'. exact RJ'.
  - (* [comment removed for export] *)
    zstep. zstep. if_cases U1; zify_cond U1; [exfalso; apply U1; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; exact D8|].
    zstep. zstep. zstep. zstep. if_cases U2; zify_cond U2; [exfalso; lia|].
    zstep. zstep. if_cases K2; zify_cond K2.
    + (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep. zstep. if_cases U3; zify_cond U3; [exfalso; lia|].
      pose proof (src_rd usegs _ S bs 0 SRC ltac:(lia)) as R0. replace (S + 0) with S in R0 by lia.
      zstep. clear R0. zstep. zstep. zstep. zstep. if_cases K4; zify_cond K4;
      [ assert (EN : n = 1) by (rewrite ?unsigned_lit in K4 by lia; clear - K4 K K2; Z.div_mod_to_equations; lia);
        rewrite EN in *
      | assert (NC : n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7) by (rewrite ?unsigned_lit in K4 by lia; clear - K4 K K2; Z.div_mod_to_equations; lia);
        destruct NC as [EN|[EN|[EN|[EN|[EN|EN]]]]]; rewrite EN in * ].
      all: step_to S bs 108264.
      all: assert (BYn : forall i, 0 <= i < n -> 0 <= Znth i bs < 256) by (intros i Hi; apply byte_Znth; [exact BY| unfold n in Hi; lia]).
      all: lazymatch type of ELn with _ = ?N => let k := eval vm_compute in (N - 1) in remember (Znth k bs) as r eqn:ER end.
      all: assert (RB : 0 <= r < 256) by (subst r; apply BYn; lia).
      all: zstep; if_cases K3; zify_cond K3.
      all: rewrite byte_lit in K3 by exact RB.
      all: lazymatch goal with RJ' : rw_cells usegs _ _ (C8 (Z_to_bv 64 ?e) :: CB 8 _ :: _) |- _ =>
             assert (EC : e = lesmall bs) by (small_cont ELn ER RB BYn) end.
      (* [comment removed for export] *)
      1,3,5,7,9,11,13: (zstep; zstep; zstep;
        apply evt_done; unfold bit_init_post; do 7 eexists; exists (-20); eexists;
        split; [reflexivity|];
        split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
        rewrite (init_dstream_small bs) by lia; replace (Znth (zlen bs - 1) bs =? 0) with true by (symmetry; apply Z.eqb_eq; rewrite ELn; lit_sub; lia);
        split; [reflexivity|];
        lazymatch goal with RJ' : rw_cells usegs _ _ (C8 _ :: _) |- _ =>
          destruct (rw_cells_forget _ _ _ _ RJ') as (j' & RJ''); exists j'; exact RJ'' end).
      (* [comment removed for export] *)
      all: hb_byte_s r.
      all: zstep; brute_reg 11%Z r 1 255 (fun r0 => 31 - Z.log2 r0).
      all: zstep; zstep; zstep; zstep.
      all: lazymatch type of ELn with _ = ?N => brute_reg 13%Z r 1 255 (fun r0 => 72 - Z.log2 r0 - 8 * N) end.
      all: zstep; zstep; zstep.
      all: apply evt_done; unfold bit_init_post; do 7 eexists; exists n; eexists.
      all: split; [rewrite EN; reflexivity|].
      all: split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|].
      all: rewrite (init_dstream_small bs) by lia.
      all: replace (Znth (zlen bs - 1) bs =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite ELn; lit_sub; lia).
      all: rewrite highbit32_ok by (rewrite ELn; lit_sub; lia); cbn [bind].
      all: split; [reflexivity|]; split; [reflexivity|].
      all: eexists; unfold bitd_cells; cbn [bd_cont bd_bits bd_ptr].
      all: rewrite <- EC; rewrite ELn; lit_sub; rewrite <- ER; replace (S + 0) with S by lia.
      all: lazymatch goal with RJ' : rw_cells usegs _ _ (_ :: C4 (Z_to_bv 64 ?v) :: _) |- _ =>
             lazymatch goal with |- rw_cells _ _ _ (_ :: C4 (Z_to_bv 64 ?w) :: _) => replace w with v by lia end; exact RJ' end.
    + (* [comment removed for export] *)
      zstep. if_cases U3; zify_cond U3; [exfalso; lia|].
      zstep. zstep. if_cases U4; zify_cond U4; [exfalso; rewrite zb_lxor_ones in U4 by lia; lia|].
      zstep. zstep. zstep. if_cases U5; zify_cond U5; [exfalso; lia|].
      assert (BYn : forall i, 0 <= i < n -> 0 <= Znth i bs < 256) by (intros i Hi; apply byte_Znth; [exact BY| unfold n in Hi; lia]).
      pose proof (src_rd _ _ S bs (n - 8) SRC ltac:(unfold n in *; lia)) as R8. pose proof (src_rd _ _ S bs (n - 7) SRC ltac:(unfold n in *; lia)) as R7.
      pose proof (src_rd _ _ S bs (n - 6) SRC ltac:(unfold n in *; lia)) as R6. pose proof (src_rd _ _ S bs (n - 5) SRC ltac:(unfold n in *; lia)) as R5.
      pose proof (src_rd _ _ S bs (n - 4) SRC ltac:(unfold n in *; lia)) as R4. pose proof (src_rd _ _ S bs (n - 3) SRC ltac:(unfold n in *; lia)) as R3.
      pose proof (src_rd _ _ S bs (n - 2) SRC ltac:(unfold n in *; lia)) as R2. pose proof (src_rd _ _ S bs (n - 1) SRC ltac:(unfold n in *; lia)) as R1.
      do 24 zstep. clear R8 R7 R6 R5 R4 R3 R2 R1.
      rewrite le64_lbu_raw in RJ by (apply BYn; lia).
      zstep.
      lazymatch goal with H : bytes_at usegs ?mm S _ |- _ => pose proof (src_rd _ mm S bs (n - 1) H ltac:(unfold n in *; lia)) as R1 end.
      remember (Znth (n - 1) bs) as r eqn:ER. assert (RB : 0 <= r < 256) by (subst r; apply BYn; lia).
      zstep. clear R1. zstep. if_cases K3; zify_cond K3.
      * (* [comment removed for export] *)
        rewrite byte_lit in K3 by exact RB.
        zstep. zstep. zstep.
        apply evt_done. unfold bit_init_post. do 7 eexists. exists (-1). eexists.
        split; [reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|]. split; [exact SRC|].
        rewrite (init_dstream_big_err bs) by (unfold n in *; lia). split; [reflexivity|].
        destruct (rw_cells_forget _ _ _ _ RJ) as (j' & RJ'). exists j'. exact RJ'.
      * rewrite byte_lit in K3 by exact RB.
        hb_byte r.
        zstep. brute_reg 11%Z r 1 255 (fun r0 => Z.log2 r0).
        zstep. zstep. brute_reg 13%Z r 1 255 (fun r0 => 8 - Z.log2 r0).
        zstep. zstep. zstep.
        apply evt_done. unfold bit_init_post. do 7 eexists. exists n. eexists.
        split; [reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|]. split; [exact SRC|].
        rewrite (init_dstream_big_ok bs) by (unfold n in *; lia). split; [reflexivity|]. split; [reflexivity|].
        eexists. unfold bitd_cells. cbn [bd_cont bd_bits bd_ptr]. fold n. rewrite <- ER.
        replace (S + (n - 8)) with (S + n + -8) by lia. exact RJ.
Qed.
