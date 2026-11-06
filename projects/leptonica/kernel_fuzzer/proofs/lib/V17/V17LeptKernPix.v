(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.kernel_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure AllocCredit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17 Require Import V17LeptStderr V17LeptBase V17_code_133ec_14000 V17_code_14000_15000 V17_code_15000_16000 V17_code_16000_17000.
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
Lemma jt8_val : rdn SEGS (fun _ => None) (Z_to_bv 64 0x10c34) 4 = Some (Z_to_le_bytes 4 0x3d10).
Proof. vm_refl_bv. Qed.

Section KernPix.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ACR : AllocCredit}.
Context {PINS : @LeptPins AL LLU17} {P16 : V17Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma W_jt8 : forall C A m md, W C A m md -> rdn SEGS m (Z_to_bv 64 0x10c34) 4 = Some (Z_to_le_bytes 4 0x3d10).
Proof.
  intros C A m md HW. rewrite <- p16_segs. rewrite (W_rdn_ro C A m md 0x10c34 4 HW); [rewrite p16_segs; exact jt8_val | |];
  cbn [fst snd ll_ro LLU17]; lia.
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

  Ltac zand F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM; unorm; rewrite EQ; reflexivity).
  Ltac condE := pin; rewrite c_eq_Z by lia; first [ apply Z.eqb_eq | apply Z.eqb_neq ]; lia.
  Ltac zlit F D v := stepat F D v ltac:(gres; pin; imm_norm; apply bv_eq; vm_compute; reflexivity).

  (* [comment removed for export] *)
  Lemma pgp_run : forall regs m (s pv pix x y : Z) (v : pixv) (ret : word) (b : byte),
    (0x20000 <= s)%Z -> (s + 64 < 2 ^ 64)%Z -> (s <= pv)%Z -> (pv + 4 <= s + 64)%Z ->
    PIXat m pix v -> p_d v = 8%Z -> (1 <= p_w v)%Z -> (p_w v <= 4 * p_wpl v)%Z -> (4 * (p_wpl v * p_h v) <= 2 ^ 26)%Z ->
    (0 <= x < p_w v)%Z -> (0 <= y < p_h v)%Z -> (p_data v mod 4 = 0)%Z -> (4 <= p_data v)%Z ->
    (4096 <= pix)%Z -> (pix + 64 <= s - 64)%Z -> (p_data v + 4 * (p_wpl v * p_h v) <= s - 64)%Z ->
    (s mod 16 = 0)%Z -> (pv mod 4 = 0)%Z -> (pix mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true -> store_ok SEGS m (Z_to_bv 64 pv) 4 = true ->
    m (Z_to_bv 64 (p_data v + 4 * (p_wpl v * y) + x - (p_data v + 4 * (p_wpl v * y) + x) mod 4 + (3 - (p_data v + 4 * (p_wpl v * y) + x) mod 4))) = Some b ->
    rdn SEGS m (Z_to_bv 64 0x10c34) 4 = Some (Z_to_le_bytes 4 0x3d10) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> ret_ok ret ->
    getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 x -> getr regs 12 = Z_to_bv 64 y -> getr regs 13 = Z_to_bv 64 pv ->
    exists regs',
      msteps SEGS (mkst regs (0x146b0 : word) m rom)
                  (mkst regs' ret (wbytes (PGF m s pv ret regs (p_w v) (p_h v) 8) (Z_to_bv 64 pv) (word_to_le_bytes 4 (Z_to_bv 64 (u b)))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20]%list) regs regs'.
  Proof.
    intros regs m s pv pix x y v ret b Hs Hs64 Hpv Hpv4 PX Hd8 Hw1 Hw4 Hsz Hx Hy ALd Hd1 Gp Hpix Hdat Hs16 ALpv ALp SOK SOKv Hb JT H2 H1 Hret H10 H11 H12 H13.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_w _ WF). pose proof (wf_h _ WF). pose proof (wf_wpl _ WF). pose proof (wf_data _ WF).
    pose proof (u8_range b) as Hb8.
    assert (Hrow : (4 * (p_wpl v * y) + 4 * p_wpl v <= 4 * (p_wpl v * p_h v))%Z).
    { assert (p_wpl v * (y + 1) <= p_wpl v * p_h v)%Z by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
    assert (Hwy : (0 <= p_wpl v * y)%Z) by (apply Z.mul_nonneg_nonneg; lia).
    assert (AL52 : ((s - 52) mod 4 = 0)%Z) by (replace (s - 52)%Z with (s + (-52))%Z by lia; apply mod16_plus_mod4; [exact Hs16 | reflexivity]).
    assert (AL56 : ((s - 56) mod 4 = 0)%Z) by (replace (s - 56)%Z with (s + (-56))%Z by lia; apply mod16_plus_mod4; [exact Hs16 | reflexivity]).
    assert (AL60 : ((s - 60) mod 4 = 0)%Z) by (replace (s - 60)%Z with (s + (-60))%Z by lia; apply mod16_plus_mod4; [exact Hs16 | reflexivity]).
    set (L := (p_data v + 4 * (p_wpl v * y))%Z) in *. assert (EL : L = (p_data v + 4 * (p_wpl v * y))%Z) by reflexivity.
    assert (ALL : (L mod 4 = 0)%Z) by (rewrite EL, Z.mul_comm, Z_mod_plus_full; exact ALd).
    pose proof (flip3_bounds L (p_wpl v) (L + x) ALL ltac:(lia)) as Hf.
    set (f := (L + x - (L + x) mod 4 + (3 - (L + x) mod 4))%Z) in *. assert (Ef : f = (L + x - (L + x) mod 4 + (3 - (L + x) mod 4))%Z) by reflexivity.
    clearbody f L.
    eexists. split.
    - zv F_145b4 D_145b4 (Z_to_bv 64 (s - 64)).
      stepST F_145b8 D_145b8 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_145bc D_145bc (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_145c0 D_145c0 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_145c4 D_145c4 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_145c8 D_145c8 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_145cc D_145cc (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepb_ft F_145d0 D_145d0 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_145d4 D_145d4.
      zand F_145d8 D_145d8 andi_3 ALpv.                                               (* [comment removed for export] *)
      stepb_ft F_145dc D_145dc ltac:(condZ).
      stepST F_145e0 D_145e0 (Z_to_bv 64 pv) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOKv).
      stepb_ft F_145e4 D_145e4 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_145e8 D_145e8. sn F_145ec D_145ec.
      zv F_145f0 D_145f0 (Z_to_bv 64 (s - 52)). zv F_145f4 D_145f4 (Z_to_bv 64 (s - 56)). zv F_145f8 D_145f8 (Z_to_bv 64 (s - 60)).
      sn F_145fc D_145fc. sn F_14600 D_14600.
      (* [comment removed for export] *)
      zand F_14148 D_14148 andi_3 AL52.
      stepb_ft F_1414c D_1414c ltac:(condZ).
      stepb_ft F_14150 D_14150 ltac:(condZ).
      stepST F_14154 D_14154 (Z_to_bv 64 (s - 52)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      zand F_14158 D_14158 andi_3 AL56.
      stepb_ft F_1415c D_1415c ltac:(condZ).
      stepb_ft F_14160 D_14160 ltac:(condZ).
      stepST F_14164 D_14164 (Z_to_bv 64 (s - 56)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      zand F_14168 D_14168 andi_3 AL60.
      stepb_ft F_1416c D_1416c ltac:(condZ).
      stepb_ft F_14170 D_14170 ltac:(condZ).
      stepST F_14174 D_14174 (Z_to_bv 64 (s - 60)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_14178 D_14178 ltac:(condZ).
      zand F_1417c D_1417c andi_7 ALp.                                                (* [comment removed for export] *)
      stepb_ft F_14180 D_14180 ltac:(condZ).
      zlit F_14184 D_14184 (Z_to_bv 64 0).                                            (* [comment removed for export] *)
      stepb_ft F_14188 D_14188 ltac:(condZ).
      stepLD F_1418c D_1418c (Z_to_le_bytes 4 (p_w v)) (Z_to_bv 64 (p_w v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_w SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_w v)) by lia.
      stepST F_14190 D_14190 (Z_to_bv 64 (s - 52)) (Z_to_bv 64 (p_w v)) ltac:(sok_in SOK).
      stepb_ft F_14194 D_14194 ltac:(condZ).
      zlit F_14198 D_14198 (Z_to_bv 64 0).                                            (* [comment removed for export] *)
      stepb_ft F_1419c D_1419c ltac:(condZ).
      stepLD F_141a0 D_141a0 (Z_to_le_bytes 4 (p_h v)) (Z_to_bv 64 (p_h v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_h SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_h v)) by lia.
      stepST F_141a4 D_141a4 (Z_to_bv 64 (s - 56)) (Z_to_bv 64 (p_h v)) ltac:(sok_in SOK).
      stepb_ft F_141a8 D_141a8 ltac:(condZ).
      zlit F_141ac D_141ac (Z_to_bv 64 0).                                            (* [comment removed for export] *)
      stepb_ft F_141b0 D_141b0 ltac:(condZ).
      stepLD F_141b4 D_141b4 (Z_to_le_bytes 4 (p_d v)) (Z_to_bv 64 (p_d v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_d SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d v)) by lia. rewrite Hd8.
      stepST F_141b8 D_141b8 (Z_to_bv 64 (s - 60)) (Z_to_bv 64 8) ltac:(sok_in SOK).
      sn F_141bc D_141bc.
      stepret F_141c0 D_141c0 (0x14700 : word) ltac:(bveq).
      (* [comment removed for export] *)
      sn F_14604 D_14604.
      stepb_ft F_14608 D_14608 ltac:(condZ).                                          (* [comment removed for export] *)
      stepb_ft F_1460c D_1460c ltac:(condZ).                                          (* [comment removed for export] *)
      stepLD F_14610 D_14610 (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))) (Z_to_bv 64 (p_w v)) ltac:(addr_norm; rdn_chain) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small (p_w v)) by lia.
      stepb_ft F_14614 D_14614 ltac:(condZ).                                          (* [comment removed for export] *)
      stepLD F_14618 D_14618 (word_to_le_bytes 4 (Z_to_bv 64 (p_h v))) (Z_to_bv 64 (p_h v)) ltac:(addr_norm; rdn_chain) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small (p_h v)) by lia.
      stepb_ft F_1461c D_1461c ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_14620 D_14620. sn F_14624 D_14624.
      (* [comment removed for export] *)
      stepb_ft F_1401c D_1401c ltac:(condZ).
      zand F_14020 D_14020 andi_7 ALp.
      stepb_ft F_14024 D_14024 ltac:(condZ).
      stepLD F_14028 D_14028 (Z_to_le_bytes 4 (p_wpl v)) (Z_to_bv 64 (p_wpl v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_wpl SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_wpl v)) by lia.
      stepret F_1402c D_1402c (0x14724 : word) ltac:(bveq).
      sn F_14628 D_14628. sn F_1462c D_1462c. sn F_14630 D_14630.
      (* [comment removed for export] *)
      stepb_ft F_1451c D_1451c ltac:(condZ).
      zand F_14520 D_14520 andi_7 ALp.
      stepb_ft F_14524 D_14524 ltac:(condZ).
      stepLD F_14528 D_14528 (Z_to_le_bytes 8 (p_data v)) (Z_to_bv 64 (p_data v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_data SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepret F_1452c D_1452c (0x14730 : word) ltac:(bveq).
      (* [comment removed for export] *)
      zv F_14634 D_14634 (Z_to_bv 64 (y * p_wpl v)).                                 (* [comment removed for export] *)
      sn F_14638 D_14638. fixv (Z_to_bv 64 (y * p_wpl v)) ltac:(rewrite zbv_mulw_small by nia; reflexivity).   (* [comment removed for export] *)
      stepb_ft F_1463c D_1463c ltac:(condZ).                                          (* [comment removed for export] *)
      stepiv F_14640 D_14640 (Z_to_bv 64 (y * p_wpl v)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by nia; f_equal; lia).   (* [comment removed for export] *)
      stepiv F_14644 D_14644 (Z_to_bv 64 (4 * (p_wpl v * y))) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; nia).
      zv F_14648 D_14648 (Z_to_bv 64 L).                                             (* [comment removed for export] *)
      sn F_1464c D_1464c. fixv (Z_to_bv 64 1) ltac:(apply zbv_snez; lia).             (* [comment removed for export] *)
      stepiv F_14650 D_14650 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).   (* [comment removed for export] *)
      stepb_ft F_14654 D_14654 ltac:(condZ).                                          (* [comment removed for export] *)
      stepat F_14658 D_14658 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_sltu_ge; lia).     (* [comment removed for export] *)
      stepat F_1465c D_1465c (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_slti0; nia).      (* [comment removed for export] *)
      zlit F_14660 D_14660 (Z_to_bv 64 0).                                            (* [comment removed for export] *)
      zlit F_14664 D_14664 (Z_to_bv 64 1).                                            (* [comment removed for export] *)
      stepb_ft F_14668 D_14668 ltac:(condZ).                                          (* [comment removed for export] *)
      (* [comment removed for export] *)
      stepLD F_1466c D_1466c (word_to_le_bytes 4 (Z_to_bv 64 8)) (Z_to_bv 64 8) ltac:(addr_norm; rdn_chain) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      try rewrite (v_lw_small 8) by lia.
      zv F_14670 D_14670 (Z_to_bv 64 7).
      sn F_14674 D_14674.
      stepb_ft F_14678 D_14678 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_1467c D_1467c.
      stepiv F_14680 D_14680 (Z_to_bv 64 28) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; reflexivity).
      sn F_14684 D_14684. zv F_14688 D_14688 (Z_to_bv 64 0x10c18).
      zv F_1468c D_1468c (Z_to_bv 64 0x10c34).
      stepLD F_14690 D_14690 (Z_to_le_bytes 4 0x3d10) (Z_to_bv 64 0x3d10) ltac:(addr_norm; repeat rdn_peel1; exact JT) ltac:(apply lez4; lia).
      try rewrite (v_lw_small 0x3d10) by lia.
      zv F_14694 D_14694 (Z_to_bv 64 0x14928).
      stepret F_14698 D_14698 (0x14928 : word) ltac:(bveq).
      (* [comment removed for export] *)
      zv F_1482c D_1482c (Z_to_bv 64 (L + x)).
      stepb_ft F_14830 D_14830 ltac:(condZ).                                          (* [comment removed for export] *)
      stepiv F_14834 D_14834 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).   (* [comment removed for export] *)
      zlit F_14838 D_14838 (Z_to_bv 64 1).                                            (* [comment removed for export] *)
      stepb_ft F_1483c D_1483c ltac:(condZ).                                          (* [comment removed for export] *)
      zv F_14840 D_14840 (Z_to_bv 64 (L + x)).
      sn F_14844 D_14844.
      stepb_ft F_14848 D_14848 ltac:(condZ).                                          (* [comment removed for export] *)
      stepiv F_1484c D_1484c (Z_to_bv 64 f) ltac:(gres; pin; imm_norm; rewrite Ef; apply zbv_xori3; lia).
      stepLBU F_14850 D_14850 b ltac:(addr_norm; repeat rdn_peel1; cbn [rdn]; rewrite Hb; reflexivity).
      sn F_14854 D_14854.
      sn F_14890 D_14890.
      stepST F_14894 D_14894 (Z_to_bv 64 pv) (Z_to_bv 64 (u b)) ltac:(sok_in SOKv).
      stepLD8 F_14898 D_14898 ret. stepLD8 F_1489c D_1489c (getr regs 8). stepLD8 F_148a0 D_148a0 (getr regs 9).
      stepLD8 F_148a4 D_148a4 (getr regs 18). stepLD8 F_148a8 D_148a8 (getr regs 19). stepLD8 F_148ac D_148ac (getr regs 20).
      zv F_148b0 D_148b0 (Z_to_bv 64 s).
      stepret F_148b4 D_148b4 ret ltac:(bveq).
      unfold PGF. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kse_ok : forall regs m (kel sy sx arr rp row col : Z) (ret : word),
    (1 <= kel)%Z -> (kel + 24 < 2 ^ 64)%Z -> (1 <= arr)%Z -> (arr + 8 * sy < 2 ^ 64)%Z -> (1 <= rp)%Z -> (rp + 4 * sx < 2 ^ 64)%Z ->
    (0 <= row < sy)%Z -> (0 <= col < sx)%Z -> (sy < 2 ^ 31)%Z -> (sx < 2 ^ 31)%Z ->
    (kel mod 8 = 0)%Z -> (arr mod 8 = 0)%Z -> (rp mod 4 = 0)%Z ->
    rdn SEGS m (Z_to_bv 64 kel) 4 = Some (Z_to_le_bytes 4 sy) -> rdn SEGS m (Z_to_bv 64 (kel + 4)) 4 = Some (Z_to_le_bytes 4 sx) ->
    rdn SEGS m (Z_to_bv 64 (kel + 16)) 8 = Some (Z_to_le_bytes 8 arr) -> rdn SEGS m (Z_to_bv 64 (arr + 8 * row)) 8 = Some (Z_to_le_bytes 8 rp) ->
    store_ok SEGS m (Z_to_bv 64 (rp + 4 * col)) 4 = true ->
    getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 kel -> getr regs 11 = Z_to_bv 64 row -> getr regs 12 = Z_to_bv 64 col ->
    exists regs',
      msteps SEGS (mkst regs (0x16044 : word) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 (rp + 4 * col)) (Z_to_le_bytes 4 (u (low32 (reg_get (@fp_regs fx) 10))))) rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 10 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m kel sy sx arr rp row col ret Hk Hk64 Ha Ha64 Hr Hr64 Hrow Hcol Hsy Hsx ALk ALa ALr Rsy Rsx Rarr Rrp SOK H1 Hret H10 H11 H12.
    assert (AL8r : ((arr + 8 * row) mod 8 = 0)%Z) by (rewrite Z.mul_comm, Z_mod_plus_full; exact ALa).
    assert (AL4c : ((rp + 4 * col) mod 4 = 0)%Z) by (rewrite Z.mul_comm, Z_mod_plus_full; exact ALr).
    eexists. split.
    - stepb_ft F_15f48 D_15f48 ltac:(condZ).                                          (* [comment removed for export] *)
      stepb_ft F_15f4c D_15f4c ltac:(condZ).                                          (* [comment removed for export] *)
      zand F_15f50 D_15f50 andi_7 ALk.
      stepb_ft F_15f54 D_15f54 ltac:(condZ).
      stepLD F_15f58 D_15f58 (Z_to_le_bytes 4 sy) (Z_to_bv 64 sy) ltac:(addr_norm; exact Rsy) ltac:(apply lez4; lia).
      rewrite (v_lw_small sy) by lia.
      stepb_ft F_15f5c D_15f5c ltac:(condZ).                                          (* [comment removed for export] *)
      stepb_ft F_15f60 D_15f60 ltac:(condZ).                                          (* [comment removed for export] *)
      stepLD F_15f64 D_15f64 (Z_to_le_bytes 4 sx) (Z_to_bv 64 sx) ltac:(addr_norm; exact Rsx) ltac:(apply lez4; lia).
      rewrite (v_lw_small sx) by lia.
      stepb_ft F_15f68 D_15f68 ltac:(condZ).                                          (* [comment removed for export] *)
      stepLD F_15f6c D_15f6c (Z_to_le_bytes 8 arr) (Z_to_bv 64 arr) ltac:(addr_norm; exact Rarr) ltac:(apply lez8; lia).
      stepiv F_15f70 D_15f70 (Z_to_bv 64 (8 * row)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 3)%Z with 8%Z; lia).
      zv F_15f74 D_15f74 (Z_to_bv 64 (arr + 8 * row)).
      stepb_ft F_15f78 D_15f78 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_15f7c D_15f7c. fixv (Z_to_bv 64 1) ltac:(apply zbv_snez; lia).             (* [comment removed for export] *)
      stepiv F_15f80 D_15f80 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).   (* [comment removed for export] *)
      zlit F_15f84 D_15f84 (Z_to_bv 64 1).                                            (* [comment removed for export] *)
      stepb_ft F_15f88 D_15f88 ltac:(condZ).                                          (* [comment removed for export] *)
      stepb_ft F_15f8c D_15f8c ltac:(condZ).                                          (* [comment removed for export] *)
      zand F_15f90 D_15f90 andi_7 AL8r.
      stepb_ft F_15f94 D_15f94 ltac:(condZ).
      stepLD F_15f98 D_15f98 (Z_to_le_bytes 8 rp) (Z_to_bv 64 rp) ltac:(addr_norm; exact Rrp) ltac:(apply lez8; lia).
      stepiv F_15f9c D_15f9c (Z_to_bv 64 (4 * col)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      zv F_15fa0 D_15fa0 (Z_to_bv 64 (rp + 4 * col)).
      stepb_ft F_15fa4 D_15fa4 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_15fa8 D_15fa8. fixv (Z_to_bv 64 1) ltac:(apply zbv_snez; lia).             (* [comment removed for export] *)
      stepiv F_15fac D_15fac (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).   (* [comment removed for export] *)
      zlit F_15fb0 D_15fb0 (Z_to_bv 64 1).                                            (* [comment removed for export] *)
      stepb_ft F_15fb4 D_15fb4 ltac:(condZ).                                          (* [comment removed for export] *)
      stepb_ft F_15fb8 D_15fb8 ltac:(condZ).                                          (* [comment removed for export] *)
      zand F_15fbc D_15fbc andi_3 AL4c.
      stepb_ft F_15fc0 D_15fc0 ltac:(condZ).
      (* [comment removed for export] *)
      chain_step; [ reflexivity
                  | eapply fp_step_fsw with (a := Z_to_bv 64 (rp + 4 * col)); [exact F_15fc4 | reflexivity | exact D_15fc4 | gres; imm_norm; addr_tac | exact SOK]
                  | step_simpl ].
      stepret F_15fc8 D_15fc8 ret ltac:(exact H1).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kse_null : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x1f9d0) 8 = Some (Z_to_le_bytes 8 0x20a40) ->
    rdn SEGS m (Z_to_bv 64 0x20a40) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x16044 : word) m rom) (mkst regs' (0x13ad4 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = getr regs 1
      /\ getr regs' 10 = Z_to_bv 64 0x103f4 /\ getr regs' 11 = Z_to_bv 64 0x10558 /\ getr regs' 12 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m Rg Rs H10. eexists. split.
    - stepb_tk F_15f48 D_15f48 ltac:(condZ).
      sn F_15ff8 D_15ff8.
      stepLD F_15ffc D_15ffc (Z_to_le_bytes 8 0x20a40) (Z_to_bv 64 0x20a40) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_16000 D_16000 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_16004 D_16004.
      stepb_ft F_16008 D_16008 ltac:(condZ).
      sn F_1600c D_1600c. sn F_16010 D_16010. sn F_16014 D_16014. sn F_16018 D_16018. sn F_1601c D_1601c. sn F_16020 D_16020.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kfp_fcvt : forall (fx' : FPState) regs m, frm_zero (@fp_csr fx') ->
    exists fr cs, frm_zero cs /\ msteps SEGS (@mkst fx' regs (0x16304 : word) m rom) (@mkst (mkFP fr cs) regs (0x16308 : word) m rom).
  Proof.
    intros fx' regs m Hz.
    destruct (fp_step_fcvt_to_f fx' SEGS regs (0x16304 : word) m rom W_16208 FC_S FC_WU 10 10 7 F_16208 eq_refl D_16208
                (or_introl eq_refl) Hz ltac:(right; reflexivity)) as (fr & cs & Hz' & ST).
    exists fr, cs. split; [exact Hz'|].
    eapply mst_step; [reflexivity | exact ST |]. step_simpl. apply mst_refl.
  Qed.

End Segs.
End KernPix.
