(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure AllocCredit.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptStderr V2LeptBase V2LeptBaseK V2KernUb V2_code_kernelCreate V2_code_kernelDestroy V2_code_kern.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
Ltac ldz8 F D z R := stepLD F D (word_to_le_bytes 8 (Z_to_bv 64 z)) (Z_to_bv 64 z) ltac:(addr_norm; repeat rdn_peel1; exact R) ltac:(apply bytes_le_to_Z_8).
Ltac ldz4 F D z R := stepLD F D (word_to_le_bytes 4 (Z_to_bv 64 z)) (Z_to_bv 64 z) ltac:(addr_norm; repeat rdn_peel1; exact R) ltac:(apply bytes_le_to_Z_4; unorm; lia);
  rewrite ?(v_lw_small z) by lia.
Ltac rdn_cell C :=
  lazymatch goal with |- rdn _ _ ?a _ = Some ?v =>
    lazymatch type of C with rdn _ _ ?a _ = Some ?v =>
      rewrite <- C; apply rdn_ext; [ rewrite u_Z2bv by lia; cbn; lia | intros ? ?; rewrite ?u_Z2bv in * by lia ] end end.

(* [comment removed for export] *)
Lemma lui_m100001 : v_addiw (Z_to_bv 64 4294868992) (-1697) = Z_to_bv 64 (2 ^ 64 - 100001).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma addw_m100001 : forall n, (1 <= n <= 100000)%Z ->
  v_addw (Z_to_bv 64 n) (Z_to_bv 64 (2 ^ 64 - 100001)) = Z_to_bv 64 (2 ^ 64 + (n - 100001)).
Proof.
  intros n Hn. rewrite v_addw_Z. apply bv_eq. rewrite !u_Z2bv_mod. unfold sw32.
  replace ((n + (2 ^ 64 - 100001) + 2 ^ 31) mod 2 ^ 32)%Z with (n - 100001 + 2 ^ 31)%Z.
  2:{ replace (n + (2 ^ 64 - 100001) + 2 ^ 31)%Z with ((n - 100001 + 2 ^ 31) + 2 ^ 32 * 2 ^ 32)%Z by lia.
      rewrite Z_mod_plus_full. rewrite Z.mod_small; lia. }
  replace (n - 100001 + 2 ^ 31 - 2 ^ 31)%Z with ((2 ^ 64 + (n - 100001)) + (-1) * 2 ^ 64)%Z by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma srli29_small : forall z, (0 <= z < 2 ^ 29)%Z -> v_srli (Z_to_bv 64 z) 29 = Z_to_bv 64 0.
Proof. intros z Hz. rewrite zbv_srli by lia. f_equal. apply Z.div_small. lia. Qed.

Section KernSegs2.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ACR : AllocCredit}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.

  Ltac zand F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM; unorm; rewrite EQ; reflexivity).
  Ltac zlit F D v := stepat F D v ltac:(gres; pin; imm_norm; apply bv_eq; vm_compute; reflexivity).

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition KCF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
           (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)).

  (* [comment removed for export] *)
  Lemma kc_A : forall regs m (s w h : Z) (ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= w < 2 ^ 31)%Z -> (1 <= h < 2 ^ 31)%Z -> (w * h < 2 ^ 29)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 h -> getr regs 11 = Z_to_bv 64 w ->
    exists regs',
      msteps SEGS (mkst regs (0x382d0 : word) m rom) (mkst regs' (0x3c0f8 : word) (KCF m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x38398 /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 11 = Z_to_bv 64 24
      /\ getr regs' 8 = Z_to_bv 64 w /\ getr regs' 9 = Z_to_bv 64 h
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s w h ret Hs Hs64 Hw Hh Hwh SOK H2 H1 H10 H11.
    assert (Hwh0 : (0 <= w * h)%Z) by (apply Z.mul_nonneg_nonneg; lia).
    eexists. split.
    - zv F_382d0 D_382d0 (Z_to_bv 64 (s - 32)).
      stepST F_382d4 D_382d4 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_382d8 D_382d8 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_382dc D_382dc (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepb_ft F_382e0 D_382e0 ltac:(condZ).                                          (* [comment removed for export] *)
      stepb_ft F_382e4 D_382e4 ltac:(condZ).                                          (* [comment removed for export] *)
      zv F_382e8 D_382e8 (Z_to_bv 64 (w * h)).
      stepiv F_382ec D_382ec (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply srli29_small; lia).
      stepb_tk F_382f0 D_382f0 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_38384 D_38384. sn F_38388 D_38388. sn F_3838c D_3838c. sn F_38390 D_38390. sn F_38394 D_38394.
      unfold KCF. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kc_B1 : forall regs m (s w h kel : Z),
    (1 <= kel)%Z -> (kel + 24 < 2 ^ 64)%Z -> (0 <= w < 2 ^ 31)%Z -> (0 <= h < 2 ^ 31)%Z -> (kel mod 8 = 0)%Z -> store_ok SEGS m (Z_to_bv 64 kel) 8 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 kel -> getr regs 8 = Z_to_bv 64 w -> getr regs 9 = Z_to_bv 64 h ->
    exists regs',
      msteps SEGS (mkst regs (0x38398 : word) m rom)
                  (mkst regs' (0x38428 : word) (wbytes (wbytes m (Z_to_bv 64 kel) (word_to_le_bytes 4 (Z_to_bv 64 h)))
                                                      (Z_to_bv 64 (kel + 4)) (word_to_le_bytes 4 (Z_to_bv 64 w))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = Z_to_bv 64 0x383bc /\ getr regs' 10 = Z_to_bv 64 h /\ getr regs' 11 = Z_to_bv 64 w
      /\ getr regs' 8 = Z_to_bv 64 kel /\ getr regs' 9 = Z_to_bv 64 h
      /\ regs_agree (fun r => In r [1; 8; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s w h kel Hk Hk64 Hw Hh ALk SOK H2 H10 H8 H9. eexists. split.
    - stepb_ft F_38398 D_38398 ltac:(condZ).
      zand F_3839c D_3839c andi_7 ALk.
      stepb_ft F_383a0 D_383a0 ltac:(condZ).
      stepST F_383a4 D_383a4 (Z_to_bv 64 kel) (Z_to_bv 64 h) ltac:(sok_in SOK).
      sn F_383a8 D_383a8.
      stepST F_383ac D_383ac (Z_to_bv 64 (kel + 4)) (Z_to_bv 64 w) ltac:(sok_in SOK).
      sn F_383b0 D_383b0. sn F_383b4 D_383b4. sn F_383b8 D_383b8.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kc_C1 : forall regs m (s kel arr : Z) (ret s0v s1v : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= kel)%Z -> (kel + 24 < 2 ^ 64)%Z -> (1 <= arr < 2 ^ 64)%Z -> ret_ok ret ->
    store_ok SEGS m (Z_to_bv 64 (kel + 16)) 8 = true -> (kel + 24 <= s - 32 \/ s <= kel)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 arr -> getr regs 8 = Z_to_bv 64 kel ->
    exists regs',
      msteps SEGS (mkst regs (0x383bc : word) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 (kel + 16)) (word_to_le_bytes 8 (Z_to_bv 64 arr))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 kel /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s kel arr ret s0v s1v Hs Hs64 Hk Hk64 Ha Hret SOK DJ R1 R2 R3 H2 H10 H8. eexists. split.
    - sn F_383bc D_383bc. sn F_383c0 D_383c0.
      stepST F_383c4 D_383c4 (Z_to_bv 64 (kel + 16)) (Z_to_bv 64 arr) ltac:(sok_in SOK).
      stepb_tk F_383c8 D_383c8 ltac:(condZ).                                          (* [comment removed for export] *)
      stepLD8 F_38410 D_38410 ret. stepLD8 F_38414 D_38414 s0v. stepLD8 F_38418 D_38418 s1v.
      zv F_3841c D_3841c (Z_to_bv 64 s).
      stepret F_38420 D_38420 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition C2F (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
      (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
      (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)))
      (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr regs 22)).

  Definition c2cells (M : word -> option byte) (s : Z) (ret s0v s1v s2v s3v s4v s5v s6v : word) : Prop :=
    rdn SEGS M (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
    rdn SEGS M (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
    rdn SEGS M (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) /\
    rdn SEGS M (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) /\
    rdn SEGS M (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v) /\
    rdn SEGS M (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 s4v) /\
    rdn SEGS M (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 s5v) /\
    rdn SEGS M (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 s6v).

  Lemma c2cells_C2F : forall m s ret regs, (64 <= s)%Z -> (s < 2 ^ 64)%Z ->
    c2cells (C2F m s ret regs) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22).
  Proof. intros m s ret regs Hs Hs64. unfold c2cells, C2F. repeat split; rdn_chain. Qed.

  Lemma c2cells_frame : forall M M' s ret s0v s1v s2v s3v s4v s5v s6v, (64 <= s)%Z -> (s < 2 ^ 64)%Z ->
    c2cells M s ret s0v s1v s2v s3v s4v s5v s6v -> (forall x : word, (s - 64 <= u x < s)%Z -> M' x = M x) -> c2cells M' s ret s0v s1v s2v s3v s4v s5v s6v.
  Proof.
    intros M M' s ret s0v s1v s2v s3v s4v s5v s6v Hs Hs64 (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8) E.
    unfold c2cells. repeat split;
      [rewrite <- C1 | rewrite <- C2 | rewrite <- C3 | rewrite <- C4 | rewrite <- C5 | rewrite <- C6 | rewrite <- C7 | rewrite <- C8];
      (apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]; intros x Hx; cbn in Hx; apply E; lia).
  Qed.

  Local Ltac c2_epi CE :=
    let C1 := fresh in let C2 := fresh in let C3 := fresh in let C4 := fresh in let C5 := fresh in let C6 := fresh in let C7 := fresh in let C8 := fresh in
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).

  (* [comment removed for export] *)
  Lemma c2d_A : forall regs m (s sx sy : Z) (ret : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= sx <= 100000)%Z -> (1 <= sy <= 100000)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 sy -> getr regs 11 = Z_to_bv 64 sx ->
    exists regs',
      msteps SEGS (mkst regs (0x38428 : word) m rom) (mkst regs' (0x3c0f8 : word) (C2F m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 1 = Z_to_bv 64 0x384f0 /\ getr regs' 10 = Z_to_bv 64 sy /\ getr regs' 11 = Z_to_bv 64 8
      /\ getr regs' 8 = Z_to_bv 64 sx /\ getr regs' 9 = Z_to_bv 64 sy
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s sx sy ret Hs Hs64 Hsx Hsy SOK H2 H1 H10 H11. eexists. split.
    - zv F_38428 D_38428 (Z_to_bv 64 (s - 64)).
      stepST F_3842c D_3842c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_38430 D_38430 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_38434 D_38434 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_38438 D_38438 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_3843c D_3843c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_38440 D_38440 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_38444 D_38444 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_38448 D_38448 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      sn F_3844c D_3844c.
      sn F_38450 D_38450.
      stepiv F_38454 D_38454 (Z_to_bv 64 (2 ^ 64 - 100001)) ltac:(gres; pin; imm_norm; exact lui_m100001).
      sn F_38458 D_38458. fixv (Z_to_bv 64 (2 ^ 64 + (sx - 100001))) ltac:(rewrite addw_m100001 by lia; reflexivity).
      stepb_tk F_3845c D_3845c ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_38480 D_38480.
      sn F_38484 D_38484. fixv (Z_to_bv 64 (2 ^ 64 + (sy - 100001))) ltac:(rewrite addw_m100001 by lia; reflexivity).
      stepb_tk F_38488 D_38488 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_384e4 D_384e4. sn F_384e8 D_384e8. sn F_384ec D_384ec.
      unfold C2F. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma c2d_B : forall regs m (arr : Z),
    (1 <= arr < 2 ^ 64)%Z -> (arr mod 8 = 0)%Z -> getr regs 10 = Z_to_bv 64 arr ->
    exists regs',
      msteps SEGS (mkst regs (0x384f0 : word) m rom) (mkst regs' (0x3850c : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 18 = Z_to_bv 64 arr /\ getr regs' 19 = Z_to_bv 64 1 /\ getr regs' 20 = Z_to_bv 64 1
      /\ getr regs' 21 = Z_to_bv 64 arr /\ getr regs' 22 = Z_to_bv 64 arr
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [10; 18; 19; 20; 21; 22]%list) regs regs'.
  Proof.
    intros regs m arr Ha ALa H10. eexists. split.
    - sn F_384f0 D_384f0.
      sn F_384f4 D_384f4. fixv (Z_to_bv 64 1) ltac:(apply zbv_snez; lia).             (* [comment removed for export] *)
      zand F_384f8 D_384f8 andi_7 ALa.                                                (* [comment removed for export] *)
      stepiv F_384fc D_384fc (Z_to_bv 64 1) ltac:(gres; pin; imm_norm; rewrite zbv_seqz by lia; reflexivity).   (* [comment removed for export] *)
      zlit F_38500 D_38500 (Z_to_bv 64 1).                                            (* [comment removed for export] *)
      sn F_38504 D_38504. sn F_38508 D_38508.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma c2d_H : forall regs m (sx : Z),
    getr regs 8 = Z_to_bv 64 sx ->
    exists regs',
      msteps SEGS (mkst regs (0x3850c : word) m rom) (mkst regs' (0x3c0f8 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x38518 /\ getr regs' 10 = Z_to_bv 64 sx /\ getr regs' 11 = Z_to_bv 64 4
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
      /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\ getr regs' 22 = getr regs 22
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m sx H8. eexists. split.
    - sn F_3850c D_3850c. sn F_38510 D_38510. sn F_38514 D_38514. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma c2d_I1 : forall regs m (arr sy i row : Z),
    (1 <= arr)%Z -> (arr + 8 * sy < 2 ^ 64)%Z -> (0 <= i)%Z -> (i + 1 < sy)%Z -> (sy < 2 ^ 31)%Z -> (1 <= row < 2 ^ 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 (arr + 8 * i)) 8 = true ->
    getr regs 10 = Z_to_bv 64 row -> getr regs 9 = Z_to_bv 64 (sy - i) -> getr regs 18 = Z_to_bv 64 arr -> getr regs 19 = Z_to_bv 64 1 ->
    getr regs 20 = Z_to_bv 64 1 -> getr regs 21 = Z_to_bv 64 (arr + 8 * i) -> getr regs 22 = Z_to_bv 64 (arr + 8 * i) ->
    exists regs',
      msteps SEGS (mkst regs (0x38518 : word) m rom)
                  (mkst regs' (0x3850c : word) (wbytes m (Z_to_bv 64 (arr + 8 * i)) (word_to_le_bytes 8 (Z_to_bv 64 row))) rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 9 = Z_to_bv 64 (sy - (i + 1)) /\ getr regs' 21 = Z_to_bv 64 (arr + 8 * (i + 1))
      /\ getr regs' 22 = Z_to_bv 64 (arr + 8 * (i + 1))
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
      /\ regs_agree (fun r => In r [9; 11; 21; 22]%list) regs regs'.
  Proof.
    intros regs m arr sy i row Ha Ha64 Hi Hi1 Hsy Hrow SOK H10 H9 H18 H19 H20 H21 H22. eexists. split.
    - stepb_ft F_38518 D_38518 ltac:(condZ).                                          (* [comment removed for export] *)
      stepiv F_3851c D_3851c (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).   (* [comment removed for export] *)
      zlit F_38520 D_38520 (Z_to_bv 64 1).                                            (* [comment removed for export] *)
      stepb_ft F_38524 D_38524 ltac:(condZ).                                          (* [comment removed for export] *)
      stepb_ft F_38528 D_38528 ltac:(condZ).                                          (* [comment removed for export] *)
      stepST F_3852c D_3852c (Z_to_bv 64 (arr + 8 * i)) (Z_to_bv 64 row) ltac:(store_ok_peel; exact SOK).
      zv F_38530 D_38530 (Z_to_bv 64 (arr + 8 * (i + 1))).
      zv F_38534 D_38534 (Z_to_bv 64 (sy - (i + 1))).
      zv F_38538 D_38538 (Z_to_bv 64 (arr + 8 * (i + 1))).
      stepb_tk F_3853c D_3853c ltac:(condZ).                                          (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma c2d_I2 : forall regs m (s arr sy i row : Z) (ret s0v s1v s2v s3v s4v s5v s6v : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= arr)%Z -> (arr + 8 * sy < 2 ^ 64)%Z -> (0 <= i)%Z -> (i + 1 = sy)%Z -> (sy < 2 ^ 31)%Z -> (1 <= row < 2 ^ 64)%Z ->
    ret_ok ret -> store_ok SEGS m (Z_to_bv 64 (arr + 8 * i)) 8 = true -> (arr + 8 * sy <= s - 64 \/ s <= arr)%Z ->
    c2cells m s ret s0v s1v s2v s3v s4v s5v s6v ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 10 = Z_to_bv 64 row -> getr regs 9 = Z_to_bv 64 (sy - i) -> getr regs 18 = Z_to_bv 64 arr ->
    getr regs 19 = Z_to_bv 64 1 -> getr regs 20 = Z_to_bv 64 1 -> getr regs 21 = Z_to_bv 64 (arr + 8 * i) -> getr regs 22 = Z_to_bv 64 (arr + 8 * i) ->
    exists regs',
      msteps SEGS (mkst regs (0x38518 : word) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 (arr + 8 * i)) (word_to_le_bytes 8 (Z_to_bv 64 row))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 arr
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18; 19; 20; 21; 22]%list) regs regs'.
  Proof.
    intros regs m s arr sy i row ret s0v s1v s2v s3v s4v s5v s6v Hs Hs64 Ha Ha64 Hi Hi1 Hsy Hrow Hret SOK DJ CE H2 H10 H9 H18 H19 H20 H21 H22. c2_epi CE.
    eexists. split.
    - stepb_ft F_38518 D_38518 ltac:(condZ).
      stepiv F_3851c D_3851c (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).
      zlit F_38520 D_38520 (Z_to_bv 64 1).
      stepb_ft F_38524 D_38524 ltac:(condZ).
      stepb_ft F_38528 D_38528 ltac:(condZ).
      stepST F_3852c D_3852c (Z_to_bv 64 (arr + 8 * i)) (Z_to_bv 64 row) ltac:(store_ok_peel; exact SOK).
      zv F_38530 D_38530 (Z_to_bv 64 (arr + 8 * (i + 1))).
      zv F_38534 D_38534 (Z_to_bv 64 0).
      zv F_38538 D_38538 (Z_to_bv 64 (arr + 8 * (i + 1))).
      stepb_ft F_3853c D_3853c ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_38540 D_38540.
      stepLD8 F_38544 D_38544 ret. stepLD8 F_38548 D_38548 s0v. stepLD8 F_3854c D_3854c s1v.
      stepLD8 F_38550 D_38550 s2v. stepLD8 F_38554 D_38554 s3v. stepLD8 F_38558 D_38558 s4v. stepLD8 F_3855c D_3855c s5v. stepLD8 F_38560 D_38560 s6v.
      zv F_38564 D_38564 (Z_to_bv 64 s).
      stepret F_38568 D_38568 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition KDF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)).

  Definition kdcells (M : word -> option byte) (s : Z) (ret s0v s1v s2v s3v : word) : Prop :=
    rdn SEGS M (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
    rdn SEGS M (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
    rdn SEGS M (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) /\
    rdn SEGS M (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) /\
    rdn SEGS M (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v).

  Lemma kdcells_KDF : forall m s ret regs, (48 <= s)%Z -> (s < 2 ^ 64)%Z ->
    kdcells (KDF m s ret regs) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19).
  Proof. intros m s ret regs Hs Hs64. unfold kdcells, KDF. repeat split; rdn_solve. Qed.

  Lemma kdcells_frame : forall M M' s ret s0v s1v s2v s3v, (48 <= s)%Z -> (s < 2 ^ 64)%Z ->
    kdcells M s ret s0v s1v s2v s3v -> (forall x : word, (s - 40 <= u x < s)%Z -> M' x = M x) -> kdcells M' s ret s0v s1v s2v s3v.
  Proof.
    intros M M' s ret s0v s1v s2v s3v Hs Hs64 (C1 & C2 & C3 & C4 & C5) HF. unfold kdcells.
    repeat split; [rdn_cell C1 | rdn_cell C2 | rdn_cell C3 | rdn_cell C4 | rdn_cell C5]; apply HF; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma kd_A0 : forall regs m (s pp : Z) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (s <= pp \/ pp + 8 <= s - 48)%Z -> (pp mod 8 = 0)%Z -> ret_ok ret ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x38570 : word) m rom) (mkst regs' ret (KDF m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s pp ret Hs Hs64 Hpp Hpp8 DJ ALp Hret SOK Rpp H2 H1 H10.
    pose proof (u64_range ret) as Hrr.
    unfold KDF. eexists. split.
    - zv F_38570 D_38570 (Z_to_bv 64 (s - 48)).
      stepST F_38574 D_38574 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_38578 D_38578 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_3857c D_3857c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_38580 D_38580 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_38584 D_38584 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepb_ft F_38588 D_38588 ltac:(condZ).
      sn F_3858c D_3858c.
      guard8 F_38590 D_38590 ALp.
      stepb_ft F_38594 D_38594 ltac:(condZ).
      ldz8 F_38598 D_38598 0%Z Rpp.
      stepb_tk F_3859c D_3859c ltac:(condZ).
      stepLD8 F_38654 D_38654 ret. stepLD8 F_38658 D_38658 (getr regs 8). stepLD8 F_3865c D_3865c (getr regs 9).
      stepLD8 F_38660 D_38660 (getr regs 18). stepLD8 F_38664 D_38664 (getr regs 19).
      zv F_38668 D_38668 (Z_to_bv 64 s).
      stepret F_3866c D_3866c ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kd_A1 : forall regs m (s pp kel sy : Z) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (s <= pp \/ pp + 8 <= s - 48)%Z -> (pp mod 8 = 0)%Z ->
    (1 <= kel)%Z -> (kel + 24 <= s - 48)%Z -> (kel mod 8 = 0)%Z -> (1 <= sy < 2 ^ 31)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 kel)) ->
    rdn SEGS m (Z_to_bv 64 kel) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 sy)) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x38570 : word) m rom) (mkst regs' (0x385b8 : word) (KDF m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 8 = Z_to_bv 64 pp /\ getr regs' 9 = Z_to_bv 64 kel
      /\ getr regs' 18 = Z_to_bv 64 0 /\ getr regs' 19 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [2; 8; 9; 10; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s pp kel sy ret Hs Hs64 Hpp Hpp8 DJ ALp Hk Hk24 ALk Hsy SOK Rpp Rsy H2 H1 H10.
    unfold KDF. eexists. split.
    - zv F_38570 D_38570 (Z_to_bv 64 (s - 48)).
      stepST F_38574 D_38574 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_38578 D_38578 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_3857c D_3857c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_38580 D_38580 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_38584 D_38584 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepb_ft F_38588 D_38588 ltac:(condZ).
      sn F_3858c D_3858c.
      guard8 F_38590 D_38590 ALp.
      stepb_ft F_38594 D_38594 ltac:(condZ).
      ldz8 F_38598 D_38598 kel Rpp.
      stepb_ft F_3859c D_3859c ltac:(condZ).
      guard8 F_385a0 D_385a0 ALk.
      stepb_ft F_385a4 D_385a4 ltac:(condZ).
      ldz4 F_385a8 D_385a8 sy Rsy.
      stepb_ft F_385ac D_385ac ltac:(condZ).
      zv F_385b0 D_385b0 (Z_to_bv 64 0). zv F_385b4 D_385b4 (Z_to_bv 64 0).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kd_H : forall regs m (kel arr sy i r : Z),
    (1 <= kel)%Z -> (kel + 24 < 2 ^ 64)%Z -> (1 <= arr)%Z -> (arr + 8 * sy < 2 ^ 64)%Z -> (arr mod 8 = 0)%Z -> (0 <= i < sy)%Z -> (0 <= r < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (kel + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 arr)) ->
    rdn SEGS m (Z_to_bv 64 (arr + 8 * i)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 r)) ->
    getr regs 9 = Z_to_bv 64 kel -> getr regs 18 = Z_to_bv 64 (8 * i) -> getr regs 19 = Z_to_bv 64 i ->
    exists regs',
      msteps SEGS (mkst regs (0x385b8 : word) m rom) (mkst regs' (0x3c230 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x385ec /\ getr regs' 10 = Z_to_bv 64 r
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m kel arr sy i r Hk Hk24 Ha Ha8 ALa Hi Hr Rarr Rrow H9 H18 H19.
    assert (ALi : ((8 * i + arr) mod 8 = 0)%Z) by (rewrite Z.add_comm; apply kal8_mul; exact ALa).
    eexists. split.
    - ldz8 F_385b8 D_385b8 arr Rarr.
      zv F_385bc D_385bc (Z_to_bv 64 (arr + 8 * i)).
      stepb_ft F_385c0 D_385c0 ltac:(condZ).
      snez1 F_385c4 D_385c4.
      seqz0 F_385c8 D_385c8.
      zlitv F_385cc D_385cc (Z_to_bv 64 1).
      stepb_ft F_385d0 D_385d0 ltac:(condZ).
      stepb_ft F_385d4 D_385d4 ltac:(condZ).
      zv F_385d8 D_385d8 (Z_to_bv 64 (8 * i + arr)).
      guard8 F_385dc D_385dc ALi.
      stepb_ft F_385e0 D_385e0 ltac:(condZ).
      ldz8 F_385e4 D_385e4 r Rrow.
      stepj F_385e8 D_385e8.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kd_Nn : forall regs m (kel sy i : Z),
    (1 <= kel)%Z -> (kel + 24 < 2 ^ 64)%Z -> (0 <= i)%Z -> (i + 1 < sy)%Z -> (sy < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 kel) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 sy)) ->
    getr regs 9 = Z_to_bv 64 kel -> getr regs 18 = Z_to_bv 64 (8 * i) -> getr regs 19 = Z_to_bv 64 i ->
    exists regs',
      msteps SEGS (mkst regs (0x385ec : word) m rom) (mkst regs' (0x385b8 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 18 = Z_to_bv 64 (8 * (i + 1)) /\ getr regs' 19 = Z_to_bv 64 (i + 1)
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [10; 18; 19]%list) regs regs'.
  Proof.
    intros regs m kel sy i Hk Hk24 Hi Hi1 Hsy Rsy H9 H18 H19.
    eexists. split.
    - ldz4 F_385ec D_385ec sy Rsy.
      zv F_385f0 D_385f0 (Z_to_bv 64 (i + 1)).
      zv F_385f4 D_385f4 (Z_to_bv 64 (8 * (i + 1))).
      stepb_tk F_385f8 D_385f8 ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kd_Nl : forall regs m (kel arr sy i : Z),
    (1 <= kel)%Z -> (kel + 24 < 2 ^ 64)%Z -> (0 <= i)%Z -> (i + 1 = sy)%Z -> (sy < 2 ^ 31)%Z -> (0 <= arr < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 kel) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 sy)) ->
    rdn SEGS m (Z_to_bv 64 (kel + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 arr)) ->
    getr regs 9 = Z_to_bv 64 kel -> getr regs 18 = Z_to_bv 64 (8 * i) -> getr regs 19 = Z_to_bv 64 i ->
    exists regs',
      msteps SEGS (mkst regs (0x385ec : word) m rom) (mkst regs' (0x3c230 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x38604 /\ getr regs' 10 = Z_to_bv 64 arr
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [1; 10; 18; 19]%list) regs regs'.
  Proof.
    intros regs m kel arr sy i Hk Hk24 Hi Hi1 Hsy Harr Rsy Rarr H9 H18 H19.
    eexists. split.
    - ldz4 F_385ec D_385ec sy Rsy.
      zv F_385f0 D_385f0 (Z_to_bv 64 (i + 1)).
      zv F_385f4 D_385f4 (Z_to_bv 64 (8 * (i + 1))).
      stepb_ft F_385f8 D_385f8 ltac:(condZ).
      ldz8 F_385fc D_385fc arr Rarr.
      stepj F_38600 D_38600.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kd_P : forall regs m (kel : word),
    getr regs 9 = kel ->
    exists regs',
      msteps SEGS (mkst regs (0x38604 : word) m rom) (mkst regs' (0x3c230 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x3860c /\ getr regs' 10 = kel
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m kel H9. eexists. split.
    - sn F_38604 D_38604.
      stepj F_38608 D_38608.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kd_Q : forall regs m (s pp : Z) (ret s0v s1v s2v s3v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (s <= pp \/ pp + 8 <= s - 48)%Z -> ret_ok ret ->
    store_ok SEGS m (Z_to_bv 64 pp) 8 = true -> kdcells m s ret s0v s1v s2v s3v ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 8 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x3860c : word) m rom) (mkst regs' ret (wbytes m (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s pp ret s0v s1v s2v s3v Hs Hs64 Hpp Hpp8 DJ Hret SOK (C1 & C2 & C3 & C4 & C5) H2 H8.
    pose proof (u64_range ret) as Hrr.
    eexists. split.
    - stepST F_3860c D_3860c (Z_to_bv 64 pp) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepj F_38610 D_38610.
      stepLD F_38654 D_38654 (word_to_le_bytes 8 ret) ret ltac:(addr_norm; repeat rdn_peel1; exact C1) ltac:(apply bytes_le_to_Z_8).
      stepLD F_38658 D_38658 (word_to_le_bytes 8 s0v) s0v ltac:(addr_norm; repeat rdn_peel1; exact C2) ltac:(apply bytes_le_to_Z_8).
      stepLD F_3865c D_3865c (word_to_le_bytes 8 s1v) s1v ltac:(addr_norm; repeat rdn_peel1; exact C3) ltac:(apply bytes_le_to_Z_8).
      stepLD F_38660 D_38660 (word_to_le_bytes 8 s2v) s2v ltac:(addr_norm; repeat rdn_peel1; exact C4) ltac:(apply bytes_le_to_Z_8).
      stepLD F_38664 D_38664 (word_to_le_bytes 8 s3v) s3v ltac:(addr_norm; repeat rdn_peel1; exact C5) ltac:(apply bytes_le_to_Z_8).
      zv F_38668 D_38668 (Z_to_bv 64 s).
      stepret F_3866c D_3866c ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

End Segs.
End KernSegs2.
