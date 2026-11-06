(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.kernel_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure AllocCredit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require Import O17LeptStderr O17LeptBase O17_code_132e8_14000 O17_code_14000_15000 O17_code_15000_16000.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Lemma w2b4_Z : forall z, (0 <= z < 2 ^ 64)%Z -> word_to_le_bytes 4 (Z_to_bv 64 z) = Z_to_le_bytes 4 z.
Proof. intros z Hz. unfold word_to_le_bytes. rewrite u_Z2bv by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma jt8_val : rdn SEGS (fun _ => None) (Z_to_bv 64 0x10bdc) 4 = Some (Z_to_le_bytes 4 0x3948).
Proof. vm_refl_bv. Qed.

Section KernPix.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ACR : AllocCredit}.
Context {PINS : @LeptPins AL LL17} {P16 : O17Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma W_jt8 : forall C A m md, W C A m md -> rdn SEGS m (Z_to_bv 64 0x10bdc) 4 = Some (Z_to_le_bytes 4 0x3948).
Proof.
  intros C A m md HW. rewrite <- p16_segs. rewrite (W_rdn_ro C A m md 0x10bdc 4 HW); [rewrite p16_segs; exact jt8_val | |];
  cbn [fst snd ll_ro LL17]; lia.
Qed.

Section Segs.
Variable rom : word -> option byte.

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
  Lemma pgp_run : forall regs m (s pv pix x y : Z) (v : pixv) (ret : word) (b : byte),
    (0x20560 <= s)%Z -> (s + 64 < 2 ^ 64)%Z -> (s <= pv)%Z -> (pv + 4 <= s + 64)%Z ->
    PIXat m pix v -> p_d v = 8%Z -> (1 <= p_w v)%Z -> (p_w v <= 4 * p_wpl v)%Z -> (4 * (p_wpl v * p_h v) <= 2 ^ 26)%Z ->
    (0 <= x < p_w v)%Z -> (0 <= y < p_h v)%Z -> (p_data v mod 4 = 0)%Z -> (1 <= p_data v)%Z ->
    (4096 <= pix)%Z -> (pix + 64 <= s - 64)%Z -> (p_data v + 4 * (p_wpl v * p_h v) <= s - 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true -> store_ok SEGS m (Z_to_bv 64 pv) 4 = true ->
    m (Z_to_bv 64 (p_data v + 4 * (p_wpl v * y) + x - (p_data v + 4 * (p_wpl v * y) + x) mod 4 + (3 - (p_data v + 4 * (p_wpl v * y) + x) mod 4))) = Some b ->
    rdn SEGS m (Z_to_bv 64 0x10bdc) 4 = Some (Z_to_le_bytes 4 0x3948) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> ret_ok ret ->
    getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 x -> getr regs 12 = Z_to_bv 64 y -> getr regs 13 = Z_to_bv 64 pv ->
    exists regs',
      msteps SEGS (mkst regs (0x14338 : word) m rom)
                  (mkst regs' ret (wbytes (PGF m s pv ret regs (p_w v) (p_h v) 8) (Z_to_bv 64 pv) (word_to_le_bytes 4 (Z_to_bv 64 (u b)))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 18; 19; 20]%list) regs regs'.
  Proof.
    intros regs m s pv pix x y v ret b Hs Hs64 Hpv Hpv4 PX Hd8 Hw1 Hw4 Hsz Hx Hy ALd Hd1 Gp Hpix Hdat SOK SOKv Hb JT H2 H1 Hret H10 H11 H12 H13.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_w _ WF). pose proof (wf_h _ WF). pose proof (wf_wpl _ WF). pose proof (wf_data _ WF).
    pose proof (u8_range b) as Hb8.
    assert (Hrow : (4 * (p_wpl v * y) + 4 * p_wpl v <= 4 * (p_wpl v * p_h v))%Z).
    { assert (p_wpl v * (y + 1) <= p_wpl v * p_h v)%Z by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
    assert (Hwy : (0 <= p_wpl v * y)%Z) by (apply Z.mul_nonneg_nonneg; lia).
    set (L := (p_data v + 4 * (p_wpl v * y))%Z) in *. assert (EL : L = (p_data v + 4 * (p_wpl v * y))%Z) by reflexivity.
    assert (ALL : (L mod 4 = 0)%Z) by (rewrite EL, Z.mul_comm, Z_mod_plus_full; exact ALd).
    pose proof (flip3_bounds L (p_wpl v) (L + x) ALL ltac:(lia)) as Hf.
    set (f := (L + x - (L + x) mod 4 + (3 - (L + x) mod 4))%Z) in *. assert (Ef : f = (L + x - (L + x) mod 4 + (3 - (L + x) mod 4))%Z) by reflexivity.
    clearbody f L.
    eexists. split.
    - zv F_1423c D_1423c (Z_to_bv 64 (s - 64)).
      stepST F_14240 D_14240 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_14244 D_14244 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_14248 D_14248 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_1424c D_1424c (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_14250 D_14250 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_14254 D_14254 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepb_ft F_14258 D_14258 ltac:(condZ).                                          (* [comment removed for export] *)
      stepST F_1425c D_1425c (Z_to_bv 64 pv) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOKv).
      stepb_ft F_14260 D_14260 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_14264 D_14264. sn F_14268 D_14268. sn F_1426c D_1426c.
      zv F_14270 D_14270 (Z_to_bv 64 (s - 52)). zv F_14274 D_14274 (Z_to_bv 64 (s - 56)). zv F_14278 D_14278 (Z_to_bv 64 (s - 60)).
      sn F_1427c D_1427c. sn F_14280 D_14280.
      (* [comment removed for export] *)
      stepb_ft F_13fd8 D_13fd8 ltac:(condZ).
      stepST F_13fdc D_13fdc (Z_to_bv 64 (s - 52)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_13fe0 D_13fe0 ltac:(condZ).
      stepST F_13fe4 D_13fe4 (Z_to_bv 64 (s - 56)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_13fe8 D_13fe8 ltac:(condZ).
      stepST F_13fec D_13fec (Z_to_bv 64 (s - 60)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_13ff0 D_13ff0 ltac:(condZ).
      stepb_ft F_13ff4 D_13ff4 ltac:(condZ).
      stepLD F_13ff8 D_13ff8 (Z_to_le_bytes 4 (p_w v)) (Z_to_bv 64 (p_w v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_w SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_w v)) by lia.
      stepST F_13ffc D_13ffc (Z_to_bv 64 (s - 52)) (Z_to_bv 64 (p_w v)) ltac:(sok_in SOK).
      stepb_ft F_14000 D_14000 ltac:(condZ).
      stepLD F_14004 D_14004 (Z_to_le_bytes 4 (p_h v)) (Z_to_bv 64 (p_h v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_h SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_h v)) by lia.
      stepST F_14008 D_14008 (Z_to_bv 64 (s - 56)) (Z_to_bv 64 (p_h v)) ltac:(sok_in SOK).
      sn F_1400c D_1400c.
      stepb_ft F_14010 D_14010 ltac:(condZ).
      stepLD F_14014 D_14014 (Z_to_le_bytes 4 (p_d v)) (Z_to_bv 64 (p_d v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_d SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d v)) by lia. rewrite Hd8.
      stepST F_14018 D_14018 (Z_to_bv 64 (s - 60)) (Z_to_bv 64 8) ltac:(sok_in SOK).
      sn F_1401c D_1401c.
      stepret F_14020 D_14020 (0x14380 : word) ltac:(bveq).
      (* [comment removed for export] *)
      sn F_14284 D_14284.
      stepb_ft F_14288 D_14288 ltac:(condZ).                                          (* [comment removed for export] *)
      stepb_ft F_1428c D_1428c ltac:(condZ).                                          (* [comment removed for export] *)
      stepLD F_14290 D_14290 (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))) (Z_to_bv 64 (p_w v)) ltac:(addr_norm; rdn_chain) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small (p_w v)) by lia.
      stepb_ft F_14294 D_14294 ltac:(condZ).                                          (* [comment removed for export] *)
      stepLD F_14298 D_14298 (word_to_le_bytes 4 (Z_to_bv 64 (p_h v))) (Z_to_bv 64 (p_h v)) ltac:(addr_norm; rdn_chain) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small (p_h v)) by lia.
      stepb_ft F_1429c D_1429c ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_142a0 D_142a0. sn F_142a4 D_142a4.
      (* [comment removed for export] *)
      stepb_ft F_13ecc D_13ecc ltac:(condZ).
      stepLD F_13ed0 D_13ed0 (Z_to_le_bytes 4 (p_wpl v)) (Z_to_bv 64 (p_wpl v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_wpl SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_wpl v)) by lia.
      stepret F_13ed4 D_13ed4 (0x143a4 : word) ltac:(bveq).
      sn F_142a8 D_142a8. sn F_142ac D_142ac. sn F_142b0 D_142b0.
      (* [comment removed for export] *)
      stepb_ft F_141bc D_141bc ltac:(condZ).
      stepLD F_141c0 D_141c0 (Z_to_le_bytes 8 (p_data v)) (Z_to_bv 64 (p_data v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_data SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepret F_141c4 D_141c4 (0x143b0 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLD F_142b4 D_142b4 (word_to_le_bytes 4 (Z_to_bv 64 8)) (Z_to_bv 64 8) ltac:(addr_norm; rdn_chain) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      try rewrite (v_lw_small 8) by lia.
      zv F_142b8 D_142b8 (Z_to_bv 64 7).
      sn F_142bc D_142bc.
      stepb_ft F_142c0 D_142c0 ltac:(condZ).                                          (* [comment removed for export] *)
      stepiv F_142c4 D_142c4 (Z_to_bv 64 28) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; reflexivity).
      sn F_142c8 D_142c8. zv F_142cc D_142cc (Z_to_bv 64 0x10bc0).
      zv F_142d0 D_142d0 (Z_to_bv 64 0x10bdc).
      stepLD F_142d4 D_142d4 (Z_to_le_bytes 4 0x3948) (Z_to_bv 64 0x3948) ltac:(addr_norm; repeat rdn_peel1; exact JT) ltac:(apply lez4; lia).
      try rewrite (v_lw_small 0x3948) by lia.
      sn F_142d8 D_142d8. fixv (Z_to_bv 64 (p_wpl v * y)) ltac:(rewrite zbv_mulw_small by nia; reflexivity).   (* [comment removed for export] *)
      stepiv F_142dc D_142dc (Z_to_bv 64 (4 * (p_wpl v * y))) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      zv F_142e0 D_142e0 (Z_to_bv 64 0x14508).
      zv F_142e4 D_142e4 (Z_to_bv 64 L).
      stepret F_142e8 D_142e8 (0x14508 : word) ltac:(bveq).
      (* [comment removed for export] *)
      zv F_1440c D_1440c (Z_to_bv 64 (L + x)).
      stepiv F_14410 D_14410 (Z_to_bv 64 f) ltac:(gres; pin; imm_norm; rewrite Ef; apply zbv_xori3; lia).
      stepLBU F_14414 D_14414 b ltac:(addr_norm; repeat rdn_peel1; cbn [rdn]; rewrite Hb; reflexivity).
      sn F_14418 D_14418.
      sn F_1442c D_1442c.
      stepST F_14430 D_14430 (Z_to_bv 64 pv) (Z_to_bv 64 (u b)) ltac:(sok_in SOKv).
      stepLD8 F_14434 D_14434 ret. stepLD8 F_14438 D_14438 (getr regs 8). stepLD8 F_1443c D_1443c (getr regs 9).
      stepLD8 F_14440 D_14440 (getr regs 18). stepLD8 F_14444 D_14444 (getr regs 19). stepLD8 F_14448 D_14448 (getr regs 20).
      zv F_1444c D_1444c (Z_to_bv 64 s).
      stepret F_14450 D_14450 ret ltac:(bveq).
      unfold PGF. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kse_ok : forall regs m (kel sy sx arr rp row col : Z) (ret : word),
    (1 <= kel)%Z -> (kel + 24 < 2 ^ 64)%Z -> (1 <= arr)%Z -> (arr + 8 * sy < 2 ^ 64)%Z -> (1 <= rp)%Z -> (rp + 4 * sx < 2 ^ 64)%Z ->
    (0 <= row < sy)%Z -> (0 <= col < sx)%Z -> (sy < 2 ^ 31)%Z -> (sx < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 kel) 4 = Some (Z_to_le_bytes 4 sy) -> rdn SEGS m (Z_to_bv 64 (kel + 4)) 4 = Some (Z_to_le_bytes 4 sx) ->
    rdn SEGS m (Z_to_bv 64 (kel + 16)) 8 = Some (Z_to_le_bytes 8 arr) -> rdn SEGS m (Z_to_bv 64 (arr + 8 * row)) 8 = Some (Z_to_le_bytes 8 rp) ->
    store_ok SEGS m (Z_to_bv 64 (rp + 4 * col)) 4 = true ->
    getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 kel -> getr regs 11 = Z_to_bv 64 row -> getr regs 12 = Z_to_bv 64 col ->
    exists regs',
      msteps SEGS (mkst regs (0x15818 : word) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 (rp + 4 * col)) (Z_to_le_bytes 4 (u (low32 (reg_get (@fp_regs fx) 10))))) rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 10 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m kel sy sx arr rp row col ret Hk Hk64 Ha Ha64 Hr Hr64 Hrow Hcol Hsy Hsx Rsy Rsx Rarr Rrp SOK H1 Hret H10 H11 H12.
    eexists. split.
    - stepb_ft F_1571c D_1571c ltac:(condZ).                                          (* [comment removed for export] *)
      stepb_ft F_15720 D_15720 ltac:(condZ).   (* [comment removed for export] *)
      stepLD F_15724 D_15724 (Z_to_le_bytes 4 sy) (Z_to_bv 64 sy) ltac:(addr_norm; exact Rsy) ltac:(apply lez4; lia).
      rewrite (v_lw_small sy) by lia.
      stepb_ft F_15728 D_15728 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_1572c D_1572c ltac:(condZ).   (* [comment removed for export] *)
      stepLD F_15730 D_15730 (Z_to_le_bytes 4 sx) (Z_to_bv 64 sx) ltac:(addr_norm; exact Rsx) ltac:(apply lez4; lia).
      rewrite (v_lw_small sx) by lia.
      stepb_ft F_15734 D_15734 ltac:(condZ).   (* [comment removed for export] *)
      sn F_15738 D_15738. sn F_1573c D_1573c.
      stepLD F_15740 D_15740 (Z_to_le_bytes 8 arr) (Z_to_bv 64 arr) ltac:(addr_norm; exact Rarr) ltac:(apply lez8; lia).
      stepiv F_15744 D_15744 (Z_to_bv 64 (8 * row)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 3)%Z with 8%Z; lia).
      zv F_15748 D_15748 (Z_to_bv 64 (arr + 8 * row)).
      stepLD F_1574c D_1574c (Z_to_le_bytes 8 rp) (Z_to_bv 64 rp) ltac:(addr_norm; exact Rrp) ltac:(apply lez8; lia).
      stepiv F_15750 D_15750 (Z_to_bv 64 (4 * col)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      zv F_15754 D_15754 (Z_to_bv 64 (rp + 4 * col)).
      (* [comment removed for export] *)
      chain_step; [ reflexivity
                  | eapply fp_step_fsw with (a := Z_to_bv 64 (rp + 4 * col)); [exact F_15758 | reflexivity | exact D_15758 | gres; imm_norm; addr_tac | exact SOK]
                  | step_simpl ].
      stepret F_1575c D_1575c ret ltac:(exact H1).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kse_null : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x1f150) 8 = Some (Z_to_le_bytes 8 0x201c0) ->
    rdn SEGS m (Z_to_bv 64 0x201c0) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x15818 : word) m rom) (mkst regs' (0x139d0 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = getr regs 1
      /\ getr regs' 10 = Z_to_bv 64 0x103e8 /\ getr regs' 11 = Z_to_bv 64 0x1054c /\ getr regs' 12 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m Rg Rs H10. eexists. split.
    - stepb_tk F_1571c D_1571c ltac:(condZ).
      sn F_1578c D_1578c.
      stepLD F_15790 D_15790 (Z_to_le_bytes 8 0x201c0) (Z_to_bv 64 0x201c0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_15794 D_15794 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_15798 D_15798.
      stepb_ft F_1579c D_1579c ltac:(condZ).
      sn F_157a0 D_157a0. sn F_157a4 D_157a4. sn F_157a8 D_157a8. sn F_157ac D_157ac. sn F_157b0 D_157b0. sn F_157b4 D_157b4.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_fcvt : forall (fx' : FPState) regs m, frm_zero (@fp_csr fx') ->
    exists fr cs, frm_zero cs /\ msteps SEGS (@mkst fx' regs (0x15a88 : word) m rom) (@mkst (mkFP fr cs) regs (0x15a8c : word) m rom).
  Proof.
    intros fx' regs m Hz.
    destruct (fp_step_fcvt_to_f fx' SEGS regs (0x15a88 : word) m rom W_1598c FC_S FC_WU 10 10 7 F_1598c eq_refl D_1598c
                (or_introl eq_refl) Hz ltac:(right; reflexivity)) as (fr & cs & Hz' & ST).
    exists fr, cs. split; [exact Hz'|].
    eapply mst_step; [reflexivity | exact ST |]. step_simpl. apply mst_refl.
  Qed.

End Segs.
End KernPix.
