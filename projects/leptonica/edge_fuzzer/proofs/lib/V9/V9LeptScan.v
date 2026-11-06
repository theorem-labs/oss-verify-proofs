(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptScan.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.V9 Require Import V9LeptBase V9_code_edB.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

(* [comment removed for export] *)
Lemma jt1_val : rdn SEGS (fun _ => None) (Z_to_bv 64 0x1c70c) 4 = Some (Z_to_le_bytes 4 0x48348).
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

  Ltac zand F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM; unorm; rewrite EQ; reflexivity).
  Ltac condE := pin; rewrite c_eq_Z by lia; first [ apply Z.eqb_eq | apply Z.eqb_neq ]; lia.
  Ltac zlit F D v := stepat F D v ltac:(gres; pin; imm_norm; apply bv_eq; vm_compute; reflexivity).

  (* [comment removed for export] *)
  Lemma pgp1_run : forall regs m (s pv pix x y Wv : Z) (v : pixv) (ret : word),
    (0x20000 <= s)%Z -> (s + 64 < 2 ^ 64)%Z -> (s <= pv)%Z -> (pv + 4 <= s + 64)%Z ->
    PIXat m pix v -> p_d v = 1%Z -> (1 <= p_w v)%Z -> (p_w v <= 32 * p_wpl v)%Z -> (4 * (p_wpl v * p_h v) <= 2 ^ 26)%Z ->
    (0 <= x < p_w v)%Z -> (0 <= y < p_h v)%Z -> (p_data v mod 4 = 0)%Z -> (4 <= p_data v)%Z ->
    (4096 <= pix)%Z -> (pix + 64 <= s - 64)%Z -> (p_data v + 4 * (p_wpl v * p_h v) <= s - 64)%Z ->
    (s mod 16 = 0)%Z -> (pv mod 4 = 0)%Z -> (pix mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true -> store_ok SEGS m (Z_to_bv 64 pv) 4 = true ->
    rdn SEGS m (Z_to_bv 64 (p_data v + 4 * (p_wpl v * y) + 4 * (x / 32))) 4 = Some (Z_to_le_bytes 4 Wv) -> (0 <= Wv < 2 ^ 32)%Z ->
    rdn SEGS m (Z_to_bv 64 0x1c70c) 4 = Some (Z_to_le_bytes 4 0x48348) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> ret_ok ret ->
    getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 x -> getr regs 12 = Z_to_bv 64 y -> getr regs 13 = Z_to_bv 64 pv ->
    exists regs',
      msteps SEGS (mkst regs (0x6496c : word) m rom)
                  (mkst regs' ret (wbytes (PGF m s pv ret regs (p_w v) (p_h v) 1) (Z_to_bv 64 pv) (word_to_le_bytes 4 (Z_to_bv 64 (pbit Wv x)))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20]%list) regs regs'.
  Proof.
    intros regs m s pv pix x y Wv v ret Hs Hs64 Hpv Hpv4 PX Hd1 Hw1 Hw4 Hsz Hx Hy ALd Hdp Gp Hpix Hdat Hs16 ALpv ALp SOK SOKv HWd HWr JT H2 H1 Hret H10 H11 H12 H13.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_w _ WF). pose proof (wf_h _ WF). pose proof (wf_wpl _ WF). pose proof (wf_data _ WF).
    pose proof (pbit_range Wv x) as Hbit.
    assert (Hrow : (4 * (p_wpl v * y) + 4 * p_wpl v <= 4 * (p_wpl v * p_h v))%Z).
    { assert (p_wpl v * (y + 1) <= p_wpl v * p_h v)%Z by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
    assert (Hwy : (0 <= p_wpl v * y)%Z) by (apply Z.mul_nonneg_nonneg; lia).
    assert (Hx32 : (0 <= x / 32 < p_wpl v)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (AL52 : ((s - 52) mod 4 = 0)%Z) by (replace (s - 52)%Z with (s + (-52))%Z by lia; apply mod16_plus_mod4; [exact Hs16 | reflexivity]).
    assert (AL56 : ((s - 56) mod 4 = 0)%Z) by (replace (s - 56)%Z with (s + (-56))%Z by lia; apply mod16_plus_mod4; [exact Hs16 | reflexivity]).
    assert (AL60 : ((s - 60) mod 4 = 0)%Z) by (replace (s - 60)%Z with (s + (-60))%Z by lia; apply mod16_plus_mod4; [exact Hs16 | reflexivity]).
    set (L := (p_data v + 4 * (p_wpl v * y))%Z) in *. assert (EL : L = (p_data v + 4 * (p_wpl v * y))%Z) by reflexivity.
    assert (ALL : (L mod 4 = 0)%Z) by (rewrite EL, Z.mul_comm, Z_mod_plus_full; exact ALd).
    assert (ALw : ((L + 4 * (x / 32)) mod 4 = 0)%Z) by (rewrite Z.mul_comm, Z_mod_plus_full; exact ALL).
    clearbody L.
    eexists. split.
    - zv F_64914 D_64914 (Z_to_bv 64 (s - 64)).
      stepST F_64918 D_64918 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_6491c D_6491c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_64920 D_64920 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_64924 D_64924 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_64928 D_64928 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_6492c D_6492c (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepb_ft F_64930 D_64930 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_64934 D_64934.
      zand F_64938 D_64938 andi_3 ALpv.                                               (* [comment removed for export] *)
      stepb_ft F_6493c D_6493c ltac:(condZ).
      stepST F_64940 D_64940 (Z_to_bv 64 pv) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOKv).
      stepb_ft F_64944 D_64944 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_64948 D_64948. sn F_6494c D_6494c.
      zv F_64950 D_64950 (Z_to_bv 64 (s - 52)). zv F_64954 D_64954 (Z_to_bv 64 (s - 56)). zv F_64958 D_64958 (Z_to_bv 64 (s - 60)).
      sn F_6495c D_6495c. sn F_64960 D_64960.
      (* [comment removed for export] *)
      zand F_6397c D_6397c andi_3 AL52.
      stepb_ft F_63980 D_63980 ltac:(condZ).
      stepb_ft F_63984 D_63984 ltac:(condZ).
      stepST F_63988 D_63988 (Z_to_bv 64 (s - 52)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      zand F_6398c D_6398c andi_3 AL56.
      stepb_ft F_63990 D_63990 ltac:(condZ).
      stepb_ft F_63994 D_63994 ltac:(condZ).
      stepST F_63998 D_63998 (Z_to_bv 64 (s - 56)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      zand F_6399c D_6399c andi_3 AL60.
      stepb_ft F_639a0 D_639a0 ltac:(condZ).
      stepb_ft F_639a4 D_639a4 ltac:(condZ).
      stepST F_639a8 D_639a8 (Z_to_bv 64 (s - 60)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_639ac D_639ac ltac:(condZ).
      zand F_639b0 D_639b0 andi_7 ALp.                                                (* [comment removed for export] *)
      stepb_ft F_639b4 D_639b4 ltac:(condZ).
      zlit F_639b8 D_639b8 (Z_to_bv 64 0).                                            (* [comment removed for export] *)
      stepb_ft F_639bc D_639bc ltac:(condZ).
      stepLD F_639c0 D_639c0 (Z_to_le_bytes 4 (p_w v)) (Z_to_bv 64 (p_w v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_w SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_w v)) by lia.
      stepST F_639c4 D_639c4 (Z_to_bv 64 (s - 52)) (Z_to_bv 64 (p_w v)) ltac:(sok_in SOK).
      stepb_ft F_639c8 D_639c8 ltac:(condZ).
      zlit F_639cc D_639cc (Z_to_bv 64 0).                                            (* [comment removed for export] *)
      stepb_ft F_639d0 D_639d0 ltac:(condZ).
      stepLD F_639d4 D_639d4 (Z_to_le_bytes 4 (p_h v)) (Z_to_bv 64 (p_h v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_h SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_h v)) by lia.
      stepST F_639d8 D_639d8 (Z_to_bv 64 (s - 56)) (Z_to_bv 64 (p_h v)) ltac:(sok_in SOK).
      stepb_ft F_639dc D_639dc ltac:(condZ).
      zlit F_639e0 D_639e0 (Z_to_bv 64 0).                                            (* [comment removed for export] *)
      stepb_ft F_639e4 D_639e4 ltac:(condZ).
      stepLD F_639e8 D_639e8 (Z_to_le_bytes 4 (p_d v)) (Z_to_bv 64 (p_d v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_d SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d v)) by lia. rewrite Hd1.
      stepST F_639ec D_639ec (Z_to_bv 64 (s - 60)) (Z_to_bv 64 1) ltac:(sok_in SOK).
      sn F_639f0 D_639f0.
      stepret F_639f4 D_639f4 (0x649bc : word) ltac:(bveq).
      (* [comment removed for export] *)
      sn F_64964 D_64964.
      stepb_ft F_64968 D_64968 ltac:(condZ).                                          (* [comment removed for export] *)
      stepb_ft F_6496c D_6496c ltac:(condZ).                                          (* [comment removed for export] *)
      stepLD F_64970 D_64970 (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))) (Z_to_bv 64 (p_w v)) ltac:(addr_norm; rdn_chain) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small (p_w v)) by lia.
      stepb_ft F_64974 D_64974 ltac:(condZ).                                          (* [comment removed for export] *)
      stepLD F_64978 D_64978 (word_to_le_bytes 4 (Z_to_bv 64 (p_h v))) (Z_to_bv 64 (p_h v)) ltac:(addr_norm; rdn_chain) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small (p_h v)) by lia.
      stepb_ft F_6497c D_6497c ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_64980 D_64980. sn F_64984 D_64984.
      (* [comment removed for export] *)
      stepb_ft F_63624 D_63624 ltac:(condZ).
      zand F_63628 D_63628 andi_7 ALp.
      stepb_ft F_6362c D_6362c ltac:(condZ).
      stepLD F_63630 D_63630 (Z_to_le_bytes 4 (p_wpl v)) (Z_to_bv 64 (p_wpl v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_wpl SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_wpl v)) by lia.
      stepret F_63634 D_63634 (0x649e0 : word) ltac:(bveq).
      sn F_64988 D_64988. sn F_6498c D_6498c. sn F_64990 D_64990.
      (* [comment removed for export] *)
      stepb_ft F_646b4 D_646b4 ltac:(condZ).
      zand F_646b8 D_646b8 andi_7 ALp.
      stepb_ft F_646bc D_646bc ltac:(condZ).
      stepLD F_646c0 D_646c0 (Z_to_le_bytes 8 (p_data v)) (Z_to_bv 64 (p_data v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_data SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepret F_646c4 D_646c4 (0x649ec : word) ltac:(bveq).
      (* [comment removed for export] *)
      zv F_64994 D_64994 (Z_to_bv 64 (y * p_wpl v)).                                 (* [comment removed for export] *)
      sn F_64998 D_64998. fixv (Z_to_bv 64 (y * p_wpl v)) ltac:(rewrite zbv_mulw_small by nia; reflexivity).   (* [comment removed for export] *)
      stepb_ft F_6499c D_6499c ltac:(condZ).                                          (* [comment removed for export] *)
      stepiv F_649a0 D_649a0 (Z_to_bv 64 (y * p_wpl v)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by nia; f_equal; lia).   (* [comment removed for export] *)
      stepiv F_649a4 D_649a4 (Z_to_bv 64 (4 * (p_wpl v * y))) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; nia).
      zv F_649a8 D_649a8 (Z_to_bv 64 L).                                             (* [comment removed for export] *)
      sn F_649ac D_649ac. fixv (Z_to_bv 64 1) ltac:(apply zbv_snez; lia).             (* [comment removed for export] *)
      stepiv F_649b0 D_649b0 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).   (* [comment removed for export] *)
      stepb_ft F_649b4 D_649b4 ltac:(condZ).                                          (* [comment removed for export] *)
      stepat F_649b8 D_649b8 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_sltu_ge; lia).     (* [comment removed for export] *)
      stepat F_649bc D_649bc (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_slti0; nia).      (* [comment removed for export] *)
      zlit F_649c0 D_649c0 (Z_to_bv 64 0).                                            (* [comment removed for export] *)
      zlit F_649c4 D_649c4 (Z_to_bv 64 1).                                            (* [comment removed for export] *)
      stepb_ft F_649c8 D_649c8 ltac:(condZ).                                          (* [comment removed for export] *)
      (* [comment removed for export] *)
      stepLD F_649cc D_649cc (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(addr_norm; rdn_chain) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      try rewrite (v_lw_small 1) by lia.
      zv F_649d0 D_649d0 (Z_to_bv 64 0).
      sn F_649d4 D_649d4.
      stepb_ft F_649d8 D_649d8 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_649dc D_649dc.
      stepiv F_649e0 D_649e0 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; reflexivity).
      sn F_649e4 D_649e4. zv F_649e8 D_649e8 (Z_to_bv 64 0x1c70c).
      zv F_649ec D_649ec (Z_to_bv 64 0x1c70c).
      stepLD F_649f0 D_649f0 (Z_to_le_bytes 4 0x48348) (Z_to_bv 64 0x48348) ltac:(addr_norm; repeat rdn_peel1; exact JT) ltac:(apply lez4; lia).
      try rewrite (v_lw_small 0x48348) by lia.
      zv F_649f4 D_649f4 (Z_to_bv 64 0x64a54).
      stepret F_649f8 D_649f8 (0x64a54 : word) ltac:(bveq).
      (* [comment removed for export] *)
      sn F_649fc D_649fc. fixv (Z_to_bv 64 (x / 32)) ltac:(rewrite zbv_srliw_small by lia; reflexivity).                 (* [comment removed for export] *)
      stepiv F_64a00 D_64a00 (Z_to_bv 64 (4 * (x / 32))) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      zv F_64a04 D_64a04 (Z_to_bv 64 (L + 4 * (x / 32))).
      stepb_ft F_64a08 D_64a08 ltac:(condZ).                                          (* [comment removed for export] *)
      stepiv F_64a0c D_64a0c (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).   (* [comment removed for export] *)
      zlit F_64a10 D_64a10 (Z_to_bv 64 1).                                            (* [comment removed for export] *)
      stepb_ft F_64a14 D_64a14 ltac:(condZ).
      stepb_ft F_64a18 D_64a18 ltac:(condZ).                                          (* [comment removed for export] *)
      zand F_64a1c D_64a1c andi_3 ALw.
      stepb_ft F_64a20 D_64a20 ltac:(condZ).
      stepLD F_64a24 D_64a24 (Z_to_le_bytes 4 Wv) (Z_to_bv 64 Wv) ltac:(addr_norm; repeat rdn_peel1; exact HWd) ltac:(apply lez4; lia).
      sn F_64a28 D_64a28.                                                               (* [comment removed for export] *)
      sn F_64a2c D_64a2c.                                                               (* [comment removed for export] *)
      stepiv F_64a30 D_64a30 (Z_to_bv 64 (pbit Wv x)) ltac:(gres; pin; imm_norm; apply pbit_val; lia).
      sn F_64a34 D_64a34.
      sn F_64bf0 D_64bf0.
      stepST F_64bf4 D_64bf4 (Z_to_bv 64 pv) (Z_to_bv 64 (pbit Wv x)) ltac:(sok_in SOKv).
      stepLD8 F_64bf8 D_64bf8 ret. stepLD8 F_64bfc D_64bfc (getr regs 8). stepLD8 F_64c00 D_64c00 (getr regs 9).
      stepLD8 F_64c04 D_64c04 (getr regs 18). stepLD8 F_64c08 D_64c08 (getr regs 19). stepLD8 F_64c0c D_64c0c (getr regs 20).
      zv F_64c10 D_64c10 (Z_to_bv 64 s).
      stepret F_64c14 D_64c14 ret ltac:(bveq).
      unfold PGF. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

End ScanSegs.
