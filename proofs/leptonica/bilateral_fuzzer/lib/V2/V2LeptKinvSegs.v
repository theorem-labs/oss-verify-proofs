(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptArithB GrayACELib LeptRop.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptStderr V2LeptBase V2LeptErr V2KernUb V2_code_kernelInvert.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRop2Arith LeptRgbLib.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

(* [comment removed for export] *)
Ltac condS :=
  idtac; pin; rewrite ?c_lts_Zs by lia;
  first [ apply Z.ltb_lt | apply Z.ltb_ge | reflexivity ]; lia.

(* [comment removed for export] *)
Ltac ldhyp F D a z R :=
  stepLD F D (word_to_le_bytes 4 (Z_to_bv 64 z)) (Z_to_bv 64 z) ltac:(rdn_addr a; exact R) ltac:(apply bytes_le_to_Z_4; unorm; lia);
  rewrite ?(v_lw_small z) by lia.
Ltac ldhyp8 F D a z R :=
  stepLD F D (word_to_le_bytes 8 (Z_to_bv 64 z)) (Z_to_bv 64 z) ltac:(rdn_addr a; exact R) ltac:(apply bytes_le_to_Z_8).

Ltac fpn := cbn [fp_regs fp_csr];
  repeat first [ rewrite fpv_get_same | rewrite fpv_get_other by reg_neq_tac ].

Ltac ldz4 F D z R := stepLD F D (word_to_le_bytes 4 (Z_to_bv 64 z)) (Z_to_bv 64 z) ltac:(addr_norm; repeat rdn_peel1; exact R) ltac:(apply bytes_le_to_Z_4; unorm; lia);
  rewrite ?(v_lw_small z) by lia.
Ltac ldz8 F D z R := stepLD F D (word_to_le_bytes 8 (Z_to_bv 64 z)) (Z_to_bv 64 z) ltac:(addr_norm; repeat rdn_peel1; exact R) ltac:(apply bytes_le_to_Z_8).
Ltac ldw8 F D a w R := stepLD F D (word_to_le_bytes 8 w) w ltac:(rdn_addr a; exact R) ltac:(apply bytes_le_to_Z_8).
Ltac sxw F D v := stepiwv F D v ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; f_equal; lia).
Ltac subw F D v := sn F D; fixv v ltac:(gres; pin; rewrite zbv_subw_signed by lia; f_equal; lia).

Lemma and_m1 : forall a, (0 <= a < 2 ^ 64)%Z -> v_and (Z_to_bv 64 (0 - 1)) (Z_to_bv 64 a) = Z_to_bv 64 a.
Proof. intros a Ha. change (0 - 1)%Z with (-1)%Z. apply and_m1_l. Qed.

Section KinvSegs.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
#[local] Notation w4 x := (word_to_le_bytes 4 x) (only parsing).

(* [comment removed for export] *)
Definition FRK7 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
    (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
    (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
    (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
    (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)).
Definition framek7 (s : Z) (ret : word) (r0 : bvmap 5 word) : list (Z * word) :=
  [((s - 8)%Z, ret); ((s - 16)%Z, getr r0 8); ((s - 24)%Z, getr r0 9); ((s - 32)%Z, getr r0 18); ((s - 40)%Z, getr r0 19); ((s - 48)%Z, getr r0 20);
   ((s - 56)%Z, getr r0 21)].
Lemma FRK7_out : forall m s ret regs (x : word), (64 <= s)%Z -> (s < 2 ^ 64)%Z -> ~ (s - 56 <= u x < s)%Z -> FRK7 m s ret regs x = m x.
Proof.
  intros m s ret regs x Hs Hs64 Hx. pose proof (u64_range x). unfold FRK7.
  rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity.
Qed.
Lemma framek7_bounds : forall s ret r0, (64 <= s)%Z -> (s < 2 ^ 64)%Z ->
  Forall (fun av => s - 56 <= fst av /\ fst av + 8 <= s)%Z (framek7 s ret r0).
Proof. intros s ret r0 Hs Hs64. unfold framek7. repeat constructor; cbn; lia. Qed.
Lemma framek7_init : forall m s ret regs, (64 <= s)%Z -> (s < 2 ^ 64)%Z -> cellsZ (FRK7 m s ret regs) (framek7 s ret regs).
Proof. intros m s ret regs Hs Hs64. unfold cellsZ, framek7, FRK7. repeat split; rdn_solve. Qed.

(* [comment removed for export] *)
Definition khdr (m : word -> option byte) (kel sy sx cy cx : Z) : Prop :=
  rdn SEGS m (Z_to_bv 64 kel) 4 = Some (w4 (Z_to_bv 64 sy)) /\ rdn SEGS m (Z_to_bv 64 (kel + 4)) 4 = Some (w4 (Z_to_bv 64 sx)) /\
  rdn SEGS m (Z_to_bv 64 (kel + 8)) 4 = Some (w4 (Z_to_bv 64 cy)) /\ rdn SEGS m (Z_to_bv 64 (kel + 12)) 4 = Some (w4 (Z_to_bv 64 cx)).

Section Segs.
Variable rom : word -> option byte.
  Ltac zand F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM; unorm; rewrite EQ; reflexivity).
  Ltac zlit F D v := stepat F D v ltac:(gres; pin; imm_norm; apply bv_eq; vm_compute; reflexivity).

  (* [comment removed for export] *)
  Lemma ki_A : forall (fx : FPState) regs m (s kels sy sx cy cx : Z) (ret : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= kels)%Z -> (kels + 24 <= s - 64)%Z -> (kels mod 8 = 0)%Z ->
    (0 <= sy < 2 ^ 31)%Z -> (0 <= sx < 2 ^ 31)%Z -> (0 <= cy < 2 ^ 31)%Z -> (0 <= cx < 2 ^ 31)%Z -> khdr m kels sy sx cy cx ->
    store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 kels ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x38e54 : word) m rom) (@mkst fx regs' (0x382d0 : word) (FRK7 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 1 = Z_to_bv 64 0x38ea4 /\ getr regs' 10 = Z_to_bv 64 sy /\ getr regs' 11 = Z_to_bv 64 sx
      /\ getr regs' 8 = Z_to_bv 64 kels /\ getr regs' 18 = Z_to_bv 64 sy /\ getr regs' 19 = Z_to_bv 64 sx /\ getr regs' 9 = Z_to_bv 64 sx
      /\ getr regs' 20 = Z_to_bv 64 cx /\ getr regs' 21 = Z_to_bv 64 cy
      /\ regs_agree (fun x => In x [1; 2; 8; 9; 10; 11; 18; 19; 20; 21]%list) regs regs'.
  Proof.
    intros fx regs m s kels sy sx cy cx ret Hs Hs64 Hk Hks ALk Hsy Hsx Hcy Hcx (Rsy & Rsx & Rcy & Rcx) SOK H2 H1 H10.
    eexists. split.
    - zv F_38e54 D_38e54 (Z_to_bv 64 (s - 64)).
      stepST F_38e58 D_38e58 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_38e5c D_38e5c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_38e60 D_38e60 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_38e64 D_38e64 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_38e68 D_38e68 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_38e6c D_38e6c (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_38e70 D_38e70 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepb_ft F_38e74 D_38e74 ltac:(condZ).
      sn F_38e78 D_38e78.
      zand F_38e7c D_38e7c andi_7 ALk.
      stepb_ft F_38e80 D_38e80 ltac:(condZ).
      ldz4 F_38e84 D_38e84 sy Rsy.
      ldz4 F_38e88 D_38e88 sx Rsx.
      ldz4 F_38e8c D_38e8c cy Rcy.
      ldz4 F_38e90 D_38e90 cx Rcx.
      sxw F_38e94 D_38e94 (Z_to_bv 64 sx).
      sn F_38e98 D_38e98. sn F_38e9c D_38e9c.
      sn F_38ea0 D_38ea0.
      unfold FRK7. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ki_B : forall (fx : FPState) regs m (keld sy sx cy cx : Z),
    (1 <= keld)%Z -> (keld + 24 < 2 ^ 64)%Z -> (keld mod 8 = 0)%Z -> (1 <= sy < 2 ^ 31)%Z -> (1 <= sx < 2 ^ 31)%Z -> (0 <= cy < 2 ^ 31)%Z -> (0 <= cx < 2 ^ 31)%Z ->
    store_ok SEGS m (Z_to_bv 64 (keld + 8)) 8 = true ->
    getr regs 10 = Z_to_bv 64 keld -> getr regs 18 = Z_to_bv 64 sy -> getr regs 9 = Z_to_bv 64 sx -> getr regs 19 = Z_to_bv 64 sx ->
    getr regs 20 = Z_to_bv 64 cx -> getr regs 21 = Z_to_bv 64 cy ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x38ea4 : word) m rom)
                  (@mkst fx regs' (0x38f00 : word) (wbytes (wbytes m (Z_to_bv 64 (keld + 8)) (w4 (Z_to_bv 64 (sy - 1 - cy)))) (Z_to_bv 64 (keld + 12)) (w4 (Z_to_bv 64 (sx - 1 - cx)))) rom)
      /\ getr regs' 10 = Z_to_bv 64 keld /\ getr regs' 11 = Z_to_bv 64 (sy - 1) /\ getr regs' 12 = Z_to_bv 64 (sx - 1) /\ getr regs' 13 = Z_to_bv 64 0
      /\ getr regs' 14 = Z_to_bv 64 (4 * sx) /\ getr regs' 15 = Z_to_bv 64 sy /\ getr regs' 16 = Z_to_bv 64 2147483647
      /\ getr regs' 9 = Z_to_bv 64 sx /\ getr regs' 18 = Z_to_bv 64 sy
      /\ regs_agree (fun x => In x [11; 12; 13; 14; 15; 16]%list) regs regs'.
  Proof.
    intros fx regs m keld sy sx cy cx Hk Hk64 ALd Hsy Hsx Hcy Hcx SOK H10 H18 H9 H19 H20 H21.
    eexists. split.
    - stepb_ft F_38ea4 D_38ea4 ltac:(condZ).
      sxw F_38ea8 D_38ea8 (Z_to_bv 64 (sy - 1)).
      stepb_ft F_38eac D_38eac ltac:(condZ).
      zv F_38eb0 D_38eb0 (Z_to_bv 64 (sy - 1 - cy)).
      subw F_38eb4 D_38eb4 (Z_to_bv 64 (sy - 1 - cy)).
      stepb_ft F_38eb8 D_38eb8 ltac:(condR).
      zand F_38ebc D_38ebc andi_7 ALd.
      stepb_ft F_38ec0 D_38ec0 ltac:(condZ).
      sxw F_38ec4 D_38ec4 (Z_to_bv 64 (sx - 1)).
      stepST F_38ec8 D_38ec8 (Z_to_bv 64 (keld + 8)) (Z_to_bv 64 (sy - 1 - cy)) ltac:(sok_in SOK).
      stepb_ft F_38ecc D_38ecc ltac:(condZ).
      zv F_38ed0 D_38ed0 (Z_to_bv 64 (sx - 1 - cx)).
      subw F_38ed4 D_38ed4 (Z_to_bv 64 (sx - 1 - cx)).
      stepb_ft F_38ed8 D_38ed8 ltac:(condR).
      stepST F_38edc D_38edc (Z_to_bv 64 (keld + 12)) (Z_to_bv 64 (sx - 1 - cx)) ltac:(sok_in SOK).
      stepb_ft F_38ee0 D_38ee0 ltac:(condZ).
      zlit F_38ee4 D_38ee4 (Z_to_bv 64 0).
      stepat F_38ee8 D_38ee8 (Z_to_bv 64 1) ltac:(gres; pin; imm_norm; apply slt0_pos; lia).
      stepiv F_38eec D_38eec (Z_to_bv 64 (4 * sx)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      zv F_38ef0 D_38ef0 (Z_to_bv 64 (0 - 1)).
      stepat F_38ef4 D_38ef4 (Z_to_bv 64 sy) ltac:(gres; pin; imm_norm; apply and_m1; lia).
      zlit F_38ef8 D_38ef8 (Z_to_bv 64 18446744071562067968).
      zlit F_38efc D_38efc (Z_to_bv 64 2147483647).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ki_OH : forall (fx : FPState) regs m (kels sy sx i arrs : Z),
    (1 <= sx < 2 ^ 31)%Z -> (0 <= i < sy)%Z -> (sy < 2 ^ 31)%Z -> (1 <= kels)%Z -> (kels + 24 < 2 ^ 64)%Z ->
    (1 <= arrs)%Z -> (arrs + 8 * sy < 2 ^ 64)%Z -> (arrs mod 8 = 0)%Z ->
    rdn SEGS m (Z_to_bv 64 (kels + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 arrs)) ->
    getr regs 9 = Z_to_bv 64 sx -> getr regs 8 = Z_to_bv 64 kels -> getr regs 11 = Z_to_bv 64 (sy - 1) -> getr regs 13 = Z_to_bv 64 i ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x38f00 : word) m rom) (@mkst fx regs' (0x38f58 : word) m rom)
      /\ getr regs' 17 = Z_to_bv 64 (arrs + 8 * (sy - 1 - i)) /\ getr regs' 6 = Z_to_bv 64 0 /\ getr regs' 5 = Z_to_bv 64 0
      /\ getr regs' 7 = Z_to_bv 64 (8 * i)
      /\ regs_agree (fun x => In x [5; 6; 7; 17; 28]%list) regs regs'.
  Proof.
    intros fx regs m kels sy sx i arrs Hsx Hi Hsy Hk Hk64 Ha Ha64 ALa Ra H9 H8 H11 H13.
    assert (ALr : ((arrs + 8 * (sy - 1 - i)) mod 8 = 0)%Z) by (rewrite Z.mul_comm, Z_mod_plus_full; exact ALa).
    eexists. split.
    - stepb_ft F_38f00 D_38f00 ltac:(condZ).
      sxw F_38f04 D_38f04 (Z_to_bv 64 i).
      zv F_38f08 D_38f08 (Z_to_bv 64 (sy - 1 - i)).
      subw F_38f0c D_38f0c (Z_to_bv 64 (sy - 1 - i)).
      stepb_ft F_38f10 D_38f10 ltac:(condR).
      ldz8 F_38f14 D_38f14 arrs Ra.
      sxw F_38f18 D_38f18 (Z_to_bv 64 (sy - 1 - i)).
      stepiv F_38f1c D_38f1c (Z_to_bv 64 (8 * (sy - 1 - i))) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 3)%Z with 8%Z; lia).
      zv F_38f20 D_38f20 (Z_to_bv 64 (arrs + 8 * (sy - 1 - i))).
      snez1 F_38f24 D_38f24.
      seqz0 F_38f28 D_38f28.
      stepb_ft F_38f2c D_38f2c ltac:(condZ).
      slti0 F_38f30 D_38f30.
      sltu0 F_38f34 D_38f34.
      zlit F_38f38 D_38f38 (Z_to_bv 64 0).
      zlit F_38f3c D_38f3c (Z_to_bv 64 1).
      stepb_ft F_38f40 D_38f40 ltac:(condZ).
      stepb_ft F_38f44 D_38f44 ltac:(condZ).
      zand F_38f48 D_38f48 andi_7 ALr.
      stepb_ft F_38f4c D_38f4c ltac:(condZ).
      zlit F_38f50 D_38f50 (Z_to_bv 64 0).
      stepiv F_38f54 D_38f54 (Z_to_bv 64 (8 * i)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 3)%Z with 8%Z; lia).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ki_I : forall (last : bool) fr cs regs m (sx j a7 rs keld arrd i rd : Z) (bs : list byte),
    (1 <= sx < 2 ^ 31)%Z -> (0 <= j < sx)%Z -> (if last then j + 1 = sx else j + 1 < sx)%Z ->
    (0 <= a7)%Z -> (a7 + 8 < 2 ^ 64)%Z -> (1 <= rs)%Z -> (rs + 4 * sx < 2 ^ 64)%Z -> (rs mod 4 = 0)%Z ->
    (0 <= keld)%Z -> (keld + 24 < 2 ^ 64)%Z -> (1 <= arrd)%Z -> (0 <= i < 2 ^ 31)%Z -> (arrd + 8 * i + 8 < 2 ^ 64)%Z -> (arrd mod 8 = 0)%Z ->
    (1 <= rd)%Z -> (rd + 4 * sx < 2 ^ 64)%Z -> (rd mod 4 = 0)%Z ->
    rdn SEGS m (Z_to_bv 64 a7) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 rs)) ->
    rdn SEGS m (Z_to_bv 64 (keld + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 arrd)) ->
    rdn SEGS m (Z_to_bv 64 (arrd + 8 * i)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 rd)) ->
    rdn SEGS m (Z_to_bv 64 (rs + 4 * (sx - 1 - j))) 4 = Some bs -> store_ok SEGS m (Z_to_bv 64 (rd + 4 * j)) 4 = true ->
    getr regs 10 = Z_to_bv 64 keld -> getr regs 12 = Z_to_bv 64 (sx - 1) -> getr regs 14 = Z_to_bv 64 (4 * sx) -> getr regs 17 = Z_to_bv 64 a7 ->
    getr regs 6 = Z_to_bv 64 j -> getr regs 5 = Z_to_bv 64 (4 * j) -> getr regs 7 = Z_to_bv 64 (8 * i) ->
    exists regs',
      msteps SEGS (@mkst (mkFP fr cs) regs (0x38f58 : word) m rom)
                  (@mkst (mkFP (bvmap_set 15 (nan_box (bv_extract 0 32 (le_bytes_to_word bs))) fr) cs) regs' (if last then (0x39004 : word) else (0x38f58 : word))
                         (wbytes m (Z_to_bv 64 (rd + 4 * j)) (Z_to_le_bytes 4 (u (low32 (nan_box (bv_extract 0 32 (le_bytes_to_word bs))))))) rom)
      /\ getr regs' 6 = Z_to_bv 64 (j + 1) /\ getr regs' 5 = Z_to_bv 64 (4 * (j + 1))
      /\ regs_agree (fun x => In x [5; 6; 18; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros last fr cs regs m sx j a7 rs keld arrd i rd bs Hsx Hj Hlast Ha7 Ha7b Hr Hrb ALs0 Hk Hkb Had Hi Hadb ALd0 Hrd Hrdb ALq0
      Rrs Rad Rrd Rbs SOK H10 H12 H14 H17 H6 H5 H7.
    assert (ALs : ((rs + 4 * (sx - 1 - j)) mod 4 = 0)%Z) by (rewrite Z.mul_comm, Z_mod_plus_full; exact ALs0).
    assert (ALd : ((arrd + 8 * i) mod 8 = 0)%Z) by (rewrite Z.mul_comm, Z_mod_plus_full; exact ALd0).
    assert (ALq : ((4 * j + rd) mod 4 = 0)%Z) by (rewrite Z.add_comm, Z.mul_comm, Z_mod_plus_full; exact ALq0).
    destruct last; (eexists; split;
    [ zv F_38f58 D_38f58 (Z_to_bv 64 (sx - 1 - j));
      subw F_38f5c D_38f5c (Z_to_bv 64 (sx - 1 - j));
      stepb_ft F_38f60 D_38f60 ltac:(condR);
      ldz8 F_38f64 D_38f64 rs Rrs;
      sxw F_38f68 D_38f68 (Z_to_bv 64 (sx - 1 - j));
      stepiv F_38f6c D_38f6c (Z_to_bv 64 (4 * (sx - 1 - j))) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia);
      zv F_38f70 D_38f70 (Z_to_bv 64 (rs + 4 * (sx - 1 - j)));
      snez1 F_38f74 D_38f74;
      seqz0 F_38f78 D_38f78;
      stepb_ft F_38f7c D_38f7c ltac:(condZ);
      sltu0 F_38f80 D_38f80;
      slti0 F_38f84 D_38f84;
      zlit F_38f88 D_38f88 (Z_to_bv 64 0);
      zlit F_38f8c D_38f8c (Z_to_bv 64 1);
      stepb_ft F_38f90 D_38f90 ltac:(condZ);
      stepb_ft F_38f94 D_38f94 ltac:(condZ);
      zand F_38f98 D_38f98 andi_3 ALs;
      stepb_ft F_38f9c D_38f9c ltac:(condZ);
      ldz8 F_38fa0 D_38fa0 arrd Rad;
      zv F_38fa4 D_38fa4 (Z_to_bv 64 (arrd + 8 * i));
      snez1 F_38fa8 D_38fa8;
      seqz0 F_38fac D_38fac;
      stepb_ft F_38fb0 D_38fb0 ltac:(condZ);
      stepb_ft F_38fb4 D_38fb4 ltac:(condZ);
      stepb_ft F_38fb8 D_38fb8 ltac:(condZ);
      zand F_38fbc D_38fbc andi_7 ALd;
      stepb_ft F_38fc0 D_38fc0 ltac:(condZ);
      ldz8 F_38fc4 D_38fc4 rd Rrd;
      zv F_38fc8 D_38fc8 (Z_to_bv 64 (rd + 4 * j));
      stepb_ft F_38fcc D_38fcc ltac:(condZ);
      snez1 F_38fd0 D_38fd0;
      seqz0 F_38fd4 D_38fd4;
      zlit F_38fd8 D_38fd8 (Z_to_bv 64 1);
      stepb_ft F_38fdc D_38fdc ltac:(condZ);
      stepb_ft F_38fe0 D_38fe0 ltac:(condZ);
      zv F_38fe4 D_38fe4 (Z_to_bv 64 (4 * j + rd));
      zand F_38fe8 D_38fe8 andi_3 ALq;
      stepb_ft F_38fec D_38fec ltac:(condZ);
      chain_step; [ reflexivity
                  | eapply fp_step_flw with (a := Z_to_bv 64 (rs + 4 * (sx - 1 - j))) (bs := bs); [exact F_38ff0 | reflexivity | exact D_38ff0 | gres; imm_norm; addr_tac | exact Rbs]
                  | step_simpl ]; fpn;
      zv F_38ff4 D_38ff4 (Z_to_bv 64 (4 * j + 4));
      chain_step; [ reflexivity
                  | eapply fp_step_fsw with (a := Z_to_bv 64 (rd + 4 * j)); [exact F_38ff8 | reflexivity | exact D_38ff8 | gres; imm_norm; addr_tac | exact SOK]
                  | step_simpl ]; fpn;
      sxw F_38ffc D_38ffc (Z_to_bv 64 (j + 1));
      first [ stepb_ft F_39000 D_39000 ltac:(condZ) | stepb_tk F_39000 D_39000 ltac:(condZ) ];
      apply mst_refl
    | repeat split; gres; pin; first [reflexivity | f_equal; lia | solve_regs_agree] ]).
  Qed.

  (* [comment removed for export] *)
  Lemma ki_ON : forall (fx : FPState) (last : bool) regs m (i sy : Z),
    (0 <= i < sy)%Z -> (sy < 2 ^ 31)%Z -> (if last then i + 1 = sy else i + 1 < sy)%Z ->
    getr regs 13 = Z_to_bv 64 i -> getr regs 15 = Z_to_bv 64 sy -> getr regs 16 = Z_to_bv 64 2147483647 ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x39004 : word) m rom) (@mkst fx regs' (if last then (0x39084 : word) else (0x38f00 : word)) m rom)
      /\ getr regs' 13 = Z_to_bv 64 (i + 1)
      /\ regs_agree (fun x => In x [13]%list) regs regs'.
  Proof.
    intros fx last regs m i sy Hi Hsy Hlast H13 H15 H16.
    destruct last; (eexists; split;
    [ stepb_ft F_39004 D_39004 ltac:(condZ);
      zv F_39008 D_39008 (Z_to_bv 64 (i + 1));
      first [ stepb_ft F_3900c D_3900c ltac:(condZ); stepj F_39010 D_39010 | stepb_tk F_3900c D_3900c ltac:(condZ) ];
      apply mst_refl
    | repeat split; gres; pin; first [reflexivity | solve_regs_agree] ]).
  Qed.

  (* [comment removed for export] *)
  Lemma ki_E : forall (fx : FPState) regs r0 m (s : Z) (ret : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cellsZ m (framek7 s ret r0) ->
    getr regs 2 = Z_to_bv 64 (s - 64) ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x39084 : word) m rom) (@mkst fx regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ (forall x, In x [8; 9; 18; 19; 20; 21]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun x => In x [1; 2; 8; 9; 18; 19; 20; 21]%list) regs regs'.
  Proof.
    intros fx regs r0 m s ret Hs Hs64 Hret CE H2. unfold framek7 in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & _).
    eexists. split.
    - ldw8 F_39084 D_39084 (s - 8)%Z ret C1. ldw8 F_39088 D_39088 (s - 16)%Z (getr r0 8) C2. ldw8 F_3908c D_3908c (s - 24)%Z (getr r0 9) C3.
      ldw8 F_39090 D_39090 (s - 32)%Z (getr r0 18) C4. ldw8 F_39094 D_39094 (s - 40)%Z (getr r0 19) C5. ldw8 F_39098 D_39098 (s - 48)%Z (getr r0 20) C6.
      ldw8 F_3909c D_3909c (s - 56)%Z (getr r0 21) C7.
      zv F_390a0 D_390a0 (Z_to_bv 64 s). stepret F_390a4 D_390a4 ret ltac:(bveq). apply mst_refl.
    - split; [gres; pin; reflexivity|]. split; [gres; pin; reflexivity|]. split.
      + intros x Hx. cbn [In] in Hx. destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; gres; pin; reflexivity.
      + solve_regs_agree.
  Qed.

End Segs.
End KinvSegs.
