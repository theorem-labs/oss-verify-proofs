(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptScan.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require Import O9LeptBase O9_code_edB.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

(* [comment removed for export] *)
Lemma jt1_val : rdn SEGS (fun _ => None) (Z_to_bv 64 0x1c64c) 4 = Some (Z_to_le_bytes 4 0x46fe0).
Proof. vm_refl_bv. Qed.

Section ScanSegs.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

  (* [comment removed for export] *)
  Definition PGF (m : word -> option byte) (s pv : Z) (ret : word) (regs : bvmap 5 word) (w h d : Z) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
      (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
      (Z_to_bv 64 pv) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (s - 52)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (s - 56)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (s - 60)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (s - 52)) (word_to_le_bytes 4 (Z_to_bv 64 w)))
      (Z_to_bv 64 (s - 56)) (word_to_le_bytes 4 (Z_to_bv 64 h)))
      (Z_to_bv 64 (s - 60)) (word_to_le_bytes 4 (Z_to_bv 64 d)).

  Lemma PGF_out : forall m s pv ret regs w h d (x : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pv)%Z -> (pv + 4 <= 2 ^ 64)%Z ->
    ~ (s - 64 <= u x < s)%Z -> ~ (pv <= u x < pv + 4)%Z -> PGF m s pv ret regs w h d x = m x.
  Proof.
    intros m s pv ret regs w h d x Hs Hs64 Hpv Hpv4 N1 N2. unfold PGF.
    rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma pgp1_run : forall regs m (s pv pix x y Wv : Z) (v : pixv) (ret : word),
    (0x20000 <= s)%Z -> (s + 64 < 2 ^ 64)%Z -> (s <= pv)%Z -> (pv + 4 <= s + 64)%Z ->
    PIXat m pix v -> p_d v = 1%Z -> (1 <= p_w v)%Z -> (p_w v <= 32 * p_wpl v)%Z -> (4 * (p_wpl v * p_h v) <= 2 ^ 26)%Z ->
    (0 <= x < p_w v)%Z -> (0 <= y < p_h v)%Z -> (p_data v mod 4 = 0)%Z -> (1 <= p_data v)%Z ->
    (4096 <= pix)%Z -> (pix + 64 <= s - 64)%Z -> (p_data v + 4 * (p_wpl v * p_h v) <= s - 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true -> store_ok SEGS m (Z_to_bv 64 pv) 4 = true ->
    rdn SEGS m (Z_to_bv 64 (p_data v + 4 * (p_wpl v * y) + 4 * (x / 32))) 4 = Some (Z_to_le_bytes 4 Wv) -> (0 <= Wv < 2 ^ 32)%Z ->
    rdn SEGS m (Z_to_bv 64 0x1c64c) 4 = Some (Z_to_le_bytes 4 0x46fe0) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> ret_ok ret ->
    getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 x -> getr regs 12 = Z_to_bv 64 y -> getr regs 13 = Z_to_bv 64 pv ->
    exists regs',
      msteps SEGS (mkst regs (0x6357c : word) m rom)
                  (mkst regs' ret (wbytes (PGF m s pv ret regs (p_w v) (p_h v) 1) (Z_to_bv 64 pv) (word_to_le_bytes 4 (Z_to_bv 64 (pbit Wv x)))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 18; 19; 20]%list) regs regs'.
  Proof.
    intros regs m s pv pix x y Wv v ret Hs Hs64 Hpv Hpv4 PX Hd1 Hw1 Hw4 Hsz Hx Hy ALd Hdp Gp Hpix Hdat SOK SOKv HWd HWr JT H2 H1 Hret H10 H11 H12 H13.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_w _ WF). pose proof (wf_h _ WF). pose proof (wf_wpl _ WF). pose proof (wf_data _ WF).
    pose proof (pbit_range Wv x) as Hbit.
    assert (Hrow : (4 * (p_wpl v * y) + 4 * p_wpl v <= 4 * (p_wpl v * p_h v))%Z).
    { assert (p_wpl v * (y + 1) <= p_wpl v * p_h v)%Z by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
    assert (Hwy : (0 <= p_wpl v * y)%Z) by (apply Z.mul_nonneg_nonneg; lia).
    assert (Hx32 : (0 <= x / 32 < p_wpl v)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    set (L := (p_data v + 4 * (p_wpl v * y))%Z) in *. assert (EL : L = (p_data v + 4 * (p_wpl v * y))%Z) by reflexivity.
    clearbody L.
    eexists. split.
    - zv F_63524 D_63524 (Z_to_bv 64 (s - 64)).
      stepST F_63528 D_63528 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_6352c D_6352c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_63530 D_63530 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_63534 D_63534 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_63538 D_63538 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_6353c D_6353c (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepb_ft F_63540 D_63540 ltac:(condZ).                                          (* [comment removed for export] *)
      stepST F_63544 D_63544 (Z_to_bv 64 pv) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOKv).
      stepb_ft F_63548 D_63548 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_6354c D_6354c. sn F_63550 D_63550. sn F_63554 D_63554.
      zv F_63558 D_63558 (Z_to_bv 64 (s - 52)). zv F_6355c D_6355c (Z_to_bv 64 (s - 56)). zv F_63560 D_63560 (Z_to_bv 64 (s - 60)).
      sn F_63564 D_63564. sn F_63568 D_63568.
      (* [comment removed for export] *)
      stepb_ft F_628b8 D_628b8 ltac:(condZ).
      stepST F_628bc D_628bc (Z_to_bv 64 (s - 52)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_628c0 D_628c0 ltac:(condZ).
      stepST F_628c4 D_628c4 (Z_to_bv 64 (s - 56)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_628c8 D_628c8 ltac:(condZ).
      stepST F_628cc D_628cc (Z_to_bv 64 (s - 60)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_628d0 D_628d0 ltac:(condZ).
      stepb_ft F_628d4 D_628d4 ltac:(condZ).
      stepLD F_628d8 D_628d8 (Z_to_le_bytes 4 (p_w v)) (Z_to_bv 64 (p_w v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_w SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_w v)) by lia.
      stepST F_628dc D_628dc (Z_to_bv 64 (s - 52)) (Z_to_bv 64 (p_w v)) ltac:(sok_in SOK).
      stepb_ft F_628e0 D_628e0 ltac:(condZ).
      stepLD F_628e4 D_628e4 (Z_to_le_bytes 4 (p_h v)) (Z_to_bv 64 (p_h v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_h SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_h v)) by lia.
      stepST F_628e8 D_628e8 (Z_to_bv 64 (s - 56)) (Z_to_bv 64 (p_h v)) ltac:(sok_in SOK).
      sn F_628ec D_628ec.
      stepb_ft F_628f0 D_628f0 ltac:(condZ).
      stepLD F_628f4 D_628f4 (Z_to_le_bytes 4 (p_d v)) (Z_to_bv 64 (p_d v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_d SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d v)) by lia. rewrite Hd1.
      stepST F_628f8 D_628f8 (Z_to_bv 64 (s - 60)) (Z_to_bv 64 1) ltac:(sok_in SOK).
      sn F_628fc D_628fc.
      stepret F_62900 D_62900 (0x635c4 : word) ltac:(bveq).
      (* [comment removed for export] *)
      sn F_6356c D_6356c.
      stepb_ft F_63570 D_63570 ltac:(condZ).                                          (* [comment removed for export] *)
      stepb_ft F_63574 D_63574 ltac:(condZ).                                          (* [comment removed for export] *)
      stepLD F_63578 D_63578 (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))) (Z_to_bv 64 (p_w v)) ltac:(addr_norm; rdn_chain) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small (p_w v)) by lia.
      stepb_ft F_6357c D_6357c ltac:(condZ).                                          (* [comment removed for export] *)
      stepLD F_63580 D_63580 (word_to_le_bytes 4 (Z_to_bv 64 (p_h v))) (Z_to_bv 64 (p_h v)) ltac:(addr_norm; rdn_chain) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small (p_h v)) by lia.
      stepb_ft F_63584 D_63584 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_63588 D_63588. sn F_6358c D_6358c.
      (* [comment removed for export] *)
      stepb_ft F_625bc D_625bc ltac:(condZ).
      stepLD F_625c0 D_625c0 (Z_to_le_bytes 4 (p_wpl v)) (Z_to_bv 64 (p_wpl v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_wpl SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_wpl v)) by lia.
      stepret F_625c4 D_625c4 (0x635e8 : word) ltac:(bveq).
      sn F_63590 D_63590. sn F_63594 D_63594. sn F_63598 D_63598.
      (* [comment removed for export] *)
      stepb_ft F_63324 D_63324 ltac:(condZ).
      stepLD F_63328 D_63328 (Z_to_le_bytes 8 (p_data v)) (Z_to_bv 64 (p_data v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_data SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepret F_6332c D_6332c (0x635f4 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLD F_6359c D_6359c (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(addr_norm; rdn_chain) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      try rewrite (v_lw_small 1) by lia.
      zv F_635a0 D_635a0 (Z_to_bv 64 0).
      sn F_635a4 D_635a4.
      stepb_ft F_635a8 D_635a8 ltac:(condZ).                                          (* [comment removed for export] *)
      stepiv F_635ac D_635ac (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; reflexivity).
      sn F_635b0 D_635b0. zv F_635b4 D_635b4 (Z_to_bv 64 0x1c64c).
      zv F_635b8 D_635b8 (Z_to_bv 64 0x1c64c).
      stepLD F_635bc D_635bc (Z_to_le_bytes 4 0x46fe0) (Z_to_bv 64 0x46fe0) ltac:(addr_norm; repeat rdn_peel1; exact JT) ltac:(apply lez4; lia).
      try rewrite (v_lw_small 0x46fe0) by lia.
      sn F_635c0 D_635c0. fixv (Z_to_bv 64 (p_wpl v * y)) ltac:(rewrite zbv_mulw_small by nia; reflexivity).   (* [comment removed for export] *)
      stepiv F_635c4 D_635c4 (Z_to_bv 64 (4 * (p_wpl v * y))) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      zv F_635c8 D_635c8 (Z_to_bv 64 0x6362c).
      zv F_635cc D_635cc (Z_to_bv 64 L).
      stepret F_635d0 D_635d0 (0x6362c : word) ltac:(bveq).
      (* [comment removed for export] *)
      sn F_635d4 D_635d4. fixv (Z_to_bv 64 (x / 32)) ltac:(rewrite zbv_srliw_small by lia; reflexivity).                 (* [comment removed for export] *)
      stepiv F_635d8 D_635d8 (Z_to_bv 64 (4 * (x / 32))) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      zv F_635dc D_635dc (Z_to_bv 64 (L + 4 * (x / 32))).
      stepLD F_635e0 D_635e0 (Z_to_le_bytes 4 Wv) (Z_to_bv 64 Wv) ltac:(addr_norm; repeat rdn_peel1; exact HWd) ltac:(apply lez4; lia).
      sn F_635e4 D_635e4.                                                               (* [comment removed for export] *)
      sn F_635e8 D_635e8.                                                               (* [comment removed for export] *)
      stepiv F_635ec D_635ec (Z_to_bv 64 (pbit Wv x)) ltac:(gres; pin; imm_norm; apply pbit_val; lia).
      sn F_635f0 D_635f0.
      sn F_63714 D_63714.
      stepST F_63718 D_63718 (Z_to_bv 64 pv) (Z_to_bv 64 (pbit Wv x)) ltac:(sok_in SOKv).
      stepLD8 F_6371c D_6371c ret. stepLD8 F_63720 D_63720 (getr regs 8). stepLD8 F_63724 D_63724 (getr regs 9).
      stepLD8 F_63728 D_63728 (getr regs 18). stepLD8 F_6372c D_6372c (getr regs 19). stepLD8 F_63730 D_63730 (getr regs 20).
      zv F_63734 D_63734 (Z_to_bv 64 s).
      stepret F_63738 D_63738 ret ltac:(bveq).
      unfold PGF. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

End ScanSegs.
