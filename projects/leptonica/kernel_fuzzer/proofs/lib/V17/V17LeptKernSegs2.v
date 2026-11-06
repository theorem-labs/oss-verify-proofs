(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.kernel_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure AllocCredit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17 Require Import V17LeptStderr V17LeptBase.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17 Require Import V17CL8a.
Import V17CL8a.V17LeptDeserB.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17 Require Import V17_code_133ec_14000 V17_code_15000_16000 V17_code_16000_17000.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

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
Context {PINS : @LeptPins AL LLU17} {P16 : V17Pins}.
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
      msteps SEGS (mkst regs (0x15ca0 : word) m rom) (mkst regs' (0x16d48 : word) (KCF m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x15d68 /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 11 = Z_to_bv 64 24
      /\ getr regs' 8 = Z_to_bv 64 w /\ getr regs' 9 = Z_to_bv 64 h
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s w h ret Hs Hs64 Hw Hh Hwh SOK H2 H1 H10 H11.
    assert (Hwh0 : (0 <= w * h)%Z) by (apply Z.mul_nonneg_nonneg; lia).
    eexists. split.
    - zv F_15ba4 D_15ba4 (Z_to_bv 64 (s - 32)).
      stepST F_15ba8 D_15ba8 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_15bac D_15bac (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_15bb0 D_15bb0 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepb_ft F_15bb4 D_15bb4 ltac:(condZ).                                          (* [comment removed for export] *)
      stepb_ft F_15bb8 D_15bb8 ltac:(condZ).                                          (* [comment removed for export] *)
      zv F_15bbc D_15bbc (Z_to_bv 64 (w * h)).
      stepiv F_15bc0 D_15bc0 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply srli29_small; lia).
      stepb_tk F_15bc4 D_15bc4 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_15c58 D_15c58. sn F_15c5c D_15c5c. sn F_15c60 D_15c60. sn F_15c64 D_15c64. sn F_15c68 D_15c68.
      unfold KCF. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kc_B1 : forall regs m (s w h kel : Z),
    (1 <= kel)%Z -> (kel + 24 < 2 ^ 64)%Z -> (0 <= w < 2 ^ 31)%Z -> (0 <= h < 2 ^ 31)%Z -> (kel mod 8 = 0)%Z -> store_ok SEGS m (Z_to_bv 64 kel) 8 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 kel -> getr regs 8 = Z_to_bv 64 w -> getr regs 9 = Z_to_bv 64 h ->
    exists regs',
      msteps SEGS (mkst regs (0x15d68 : word) m rom)
                  (mkst regs' (0x15df8 : word) (wbytes (wbytes m (Z_to_bv 64 kel) (word_to_le_bytes 4 (Z_to_bv 64 h)))
                                                      (Z_to_bv 64 (kel + 4)) (word_to_le_bytes 4 (Z_to_bv 64 w))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = Z_to_bv 64 0x15d8c /\ getr regs' 10 = Z_to_bv 64 h /\ getr regs' 11 = Z_to_bv 64 w
      /\ getr regs' 8 = Z_to_bv 64 kel /\ getr regs' 9 = Z_to_bv 64 h
      /\ regs_agree (fun r => In r [1; 8; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s w h kel Hk Hk64 Hw Hh ALk SOK H2 H10 H8 H9. eexists. split.
    - stepb_ft F_15c6c D_15c6c ltac:(condZ).
      zand F_15c70 D_15c70 andi_7 ALk.
      stepb_ft F_15c74 D_15c74 ltac:(condZ).
      stepST F_15c78 D_15c78 (Z_to_bv 64 kel) (Z_to_bv 64 h) ltac:(sok_in SOK).
      sn F_15c7c D_15c7c.
      stepST F_15c80 D_15c80 (Z_to_bv 64 (kel + 4)) (Z_to_bv 64 w) ltac:(sok_in SOK).
      sn F_15c84 D_15c84. sn F_15c88 D_15c88. sn F_15c8c D_15c8c.
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
      msteps SEGS (mkst regs (0x15d8c : word) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 (kel + 16)) (word_to_le_bytes 8 (Z_to_bv 64 arr))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 kel /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s kel arr ret s0v s1v Hs Hs64 Hk Hk64 Ha Hret SOK DJ R1 R2 R3 H2 H10 H8. eexists. split.
    - sn F_15c90 D_15c90. sn F_15c94 D_15c94.
      stepST F_15c98 D_15c98 (Z_to_bv 64 (kel + 16)) (Z_to_bv 64 arr) ltac:(sok_in SOK).
      stepb_tk F_15c9c D_15c9c ltac:(condZ).                                          (* [comment removed for export] *)
      stepLD8 F_15ce4 D_15ce4 ret. stepLD8 F_15ce8 D_15ce8 s0v. stepLD8 F_15cec D_15cec s1v.
      zv F_15cf0 D_15cf0 (Z_to_bv 64 s).
      stepret F_15cf4 D_15cf4 ret ltac:(bveq).
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
      msteps SEGS (mkst regs (0x15df8 : word) m rom) (mkst regs' (0x16d48 : word) (C2F m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 1 = Z_to_bv 64 0x15ec0 /\ getr regs' 10 = Z_to_bv 64 sy /\ getr regs' 11 = Z_to_bv 64 8
      /\ getr regs' 8 = Z_to_bv 64 sx /\ getr regs' 9 = Z_to_bv 64 sy
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s sx sy ret Hs Hs64 Hsx Hsy SOK H2 H1 H10 H11. eexists. split.
    - zv F_15cfc D_15cfc (Z_to_bv 64 (s - 64)).
      stepST F_15d00 D_15d00 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_15d04 D_15d04 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_15d08 D_15d08 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_15d0c D_15d0c (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_15d10 D_15d10 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_15d14 D_15d14 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_15d18 D_15d18 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_15d1c D_15d1c (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      sn F_15d20 D_15d20.
      sn F_15d24 D_15d24.
      stepiv F_15d28 D_15d28 (Z_to_bv 64 (2 ^ 64 - 100001)) ltac:(gres; pin; imm_norm; exact lui_m100001).
      sn F_15d2c D_15d2c. fixv (Z_to_bv 64 (2 ^ 64 + (sx - 100001))) ltac:(rewrite addw_m100001 by lia; reflexivity).
      stepb_tk F_15d30 D_15d30 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_15d54 D_15d54.
      sn F_15d58 D_15d58. fixv (Z_to_bv 64 (2 ^ 64 + (sy - 100001))) ltac:(rewrite addw_m100001 by lia; reflexivity).
      stepb_tk F_15d5c D_15d5c ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_15db8 D_15db8. sn F_15dbc D_15dbc. sn F_15dc0 D_15dc0.
      unfold C2F. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma c2d_B : forall regs m (arr : Z),
    (1 <= arr < 2 ^ 64)%Z -> (arr mod 8 = 0)%Z -> getr regs 10 = Z_to_bv 64 arr ->
    exists regs',
      msteps SEGS (mkst regs (0x15ec0 : word) m rom) (mkst regs' (0x15edc : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 18 = Z_to_bv 64 arr /\ getr regs' 19 = Z_to_bv 64 1 /\ getr regs' 20 = Z_to_bv 64 1
      /\ getr regs' 21 = Z_to_bv 64 arr /\ getr regs' 22 = Z_to_bv 64 arr
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [10; 18; 19; 20; 21; 22]%list) regs regs'.
  Proof.
    intros regs m arr Ha ALa H10. eexists. split.
    - sn F_15dc4 D_15dc4.
      sn F_15dc8 D_15dc8. fixv (Z_to_bv 64 1) ltac:(apply zbv_snez; lia).             (* [comment removed for export] *)
      zand F_15dcc D_15dcc andi_7 ALa.                                                (* [comment removed for export] *)
      stepiv F_15dd0 D_15dd0 (Z_to_bv 64 1) ltac:(gres; pin; imm_norm; rewrite zbv_seqz by lia; reflexivity).   (* [comment removed for export] *)
      zlit F_15dd4 D_15dd4 (Z_to_bv 64 1).                                            (* [comment removed for export] *)
      sn F_15dd8 D_15dd8. sn F_15ddc D_15ddc.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma c2d_H : forall regs m (sx : Z),
    getr regs 8 = Z_to_bv 64 sx ->
    exists regs',
      msteps SEGS (mkst regs (0x15edc : word) m rom) (mkst regs' (0x16d48 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x15ee8 /\ getr regs' 10 = Z_to_bv 64 sx /\ getr regs' 11 = Z_to_bv 64 4
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
      /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\ getr regs' 22 = getr regs 22
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m sx H8. eexists. split.
    - sn F_15de0 D_15de0. sn F_15de4 D_15de4. sn F_15de8 D_15de8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma c2d_I1 : forall regs m (arr sy i row : Z),
    (1 <= arr)%Z -> (arr + 8 * sy < 2 ^ 64)%Z -> (0 <= i)%Z -> (i + 1 < sy)%Z -> (sy < 2 ^ 31)%Z -> (1 <= row < 2 ^ 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 (arr + 8 * i)) 8 = true ->
    getr regs 10 = Z_to_bv 64 row -> getr regs 9 = Z_to_bv 64 (sy - i) -> getr regs 18 = Z_to_bv 64 arr -> getr regs 19 = Z_to_bv 64 1 ->
    getr regs 20 = Z_to_bv 64 1 -> getr regs 21 = Z_to_bv 64 (arr + 8 * i) -> getr regs 22 = Z_to_bv 64 (arr + 8 * i) ->
    exists regs',
      msteps SEGS (mkst regs (0x15ee8 : word) m rom)
                  (mkst regs' (0x15edc : word) (wbytes m (Z_to_bv 64 (arr + 8 * i)) (word_to_le_bytes 8 (Z_to_bv 64 row))) rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 9 = Z_to_bv 64 (sy - (i + 1)) /\ getr regs' 21 = Z_to_bv 64 (arr + 8 * (i + 1))
      /\ getr regs' 22 = Z_to_bv 64 (arr + 8 * (i + 1))
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
      /\ regs_agree (fun r => In r [9; 11; 21; 22]%list) regs regs'.
  Proof.
    intros regs m arr sy i row Ha Ha64 Hi Hi1 Hsy Hrow SOK H10 H9 H18 H19 H20 H21 H22. eexists. split.
    - stepb_ft F_15dec D_15dec ltac:(condZ).                                          (* [comment removed for export] *)
      stepiv F_15df0 D_15df0 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).   (* [comment removed for export] *)
      zlit F_15df4 D_15df4 (Z_to_bv 64 1).                                            (* [comment removed for export] *)
      stepb_ft F_15df8 D_15df8 ltac:(condZ).                                          (* [comment removed for export] *)
      stepb_ft F_15dfc D_15dfc ltac:(condZ).                                          (* [comment removed for export] *)
      stepST F_15e00 D_15e00 (Z_to_bv 64 (arr + 8 * i)) (Z_to_bv 64 row) ltac:(store_ok_peel; exact SOK).
      zv F_15e04 D_15e04 (Z_to_bv 64 (arr + 8 * (i + 1))).
      zv F_15e08 D_15e08 (Z_to_bv 64 (sy - (i + 1))).
      zv F_15e0c D_15e0c (Z_to_bv 64 (arr + 8 * (i + 1))).
      stepb_tk F_15e10 D_15e10 ltac:(condZ).                                          (* [comment removed for export] *)
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
      msteps SEGS (mkst regs (0x15ee8 : word) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 (arr + 8 * i)) (word_to_le_bytes 8 (Z_to_bv 64 row))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 arr
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18; 19; 20; 21; 22]%list) regs regs'.
  Proof.
    intros regs m s arr sy i row ret s0v s1v s2v s3v s4v s5v s6v Hs Hs64 Ha Ha64 Hi Hi1 Hsy Hrow Hret SOK DJ CE H2 H10 H9 H18 H19 H20 H21 H22. c2_epi CE.
    eexists. split.
    - stepb_ft F_15dec D_15dec ltac:(condZ).
      stepiv F_15df0 D_15df0 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).
      zlit F_15df4 D_15df4 (Z_to_bv 64 1).
      stepb_ft F_15df8 D_15df8 ltac:(condZ).
      stepb_ft F_15dfc D_15dfc ltac:(condZ).
      stepST F_15e00 D_15e00 (Z_to_bv 64 (arr + 8 * i)) (Z_to_bv 64 row) ltac:(store_ok_peel; exact SOK).
      zv F_15e04 D_15e04 (Z_to_bv 64 (arr + 8 * (i + 1))).
      zv F_15e08 D_15e08 (Z_to_bv 64 0).
      zv F_15e0c D_15e0c (Z_to_bv 64 (arr + 8 * (i + 1))).
      stepb_ft F_15e10 D_15e10 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_15e14 D_15e14.
      stepLD8 F_15e18 D_15e18 ret. stepLD8 F_15e1c D_15e1c s0v. stepLD8 F_15e20 D_15e20 s1v.
      stepLD8 F_15e24 D_15e24 s2v. stepLD8 F_15e28 D_15e28 s3v. stepLD8 F_15e2c D_15e2c s4v. stepLD8 F_15e30 D_15e30 s5v. stepLD8 F_15e34 D_15e34 s6v.
      zv F_15e38 D_15e38 (Z_to_bv 64 s).
      stepret F_15e3c D_15e3c ret ltac:(bveq).
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
  Proof. intros m s ret regs Hs Hs64. unfold kdcells, KDF. repeat split; rdn_chain. Qed.

  Lemma kdcells_frame : forall M M' s ret s0v s1v s2v s3v, (48 <= s)%Z -> (s < 2 ^ 64)%Z ->
    kdcells M s ret s0v s1v s2v s3v -> (forall x : word, (s - 40 <= u x < s)%Z -> M' x = M x) -> kdcells M' s ret s0v s1v s2v s3v.
  Proof.
    intros M M' s ret s0v s1v s2v s3v Hs Hs64 (C1 & C2 & C3 & C4 & C5) E.
    unfold kdcells. repeat split;
      [rewrite <- C1 | rewrite <- C2 | rewrite <- C3 | rewrite <- C4 | rewrite <- C5];
      (apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]; intros x Hx; cbn in Hx; apply E; lia).
  Qed.

  (* [comment removed for export] *)
  Lemma kd_A0 : forall regs m (s pp : Z) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (s <= pp \/ pp + 8 <= s - 48)%Z -> ret_ok ret -> (pp mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x15f40 : word) m rom) (mkst regs' ret (KDF m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s pp ret Hs Hs64 Hpp Hpp8 DJ Hret ALpp SOK Rpp H2 H1 H10. eexists. split.
    - zv F_15e44 D_15e44 (Z_to_bv 64 (s - 48)).
      stepST F_15e48 D_15e48 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_15e4c D_15e4c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_15e50 D_15e50 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_15e54 D_15e54 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_15e58 D_15e58 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepb_ft F_15e5c D_15e5c ltac:(condZ).
      sn F_15e60 D_15e60.
      zand F_15e64 D_15e64 andi_7 ALpp.
      stepb_ft F_15e68 D_15e68 ltac:(condZ).
      stepLD F_15e6c D_15e6c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; repeat rdn_peel1; exact Rpp) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_15e70 D_15e70 ltac:(condZ).
      stepLD8 F_15f28 D_15f28 ret. stepLD8 F_15f2c D_15f2c (getr regs 8). stepLD8 F_15f30 D_15f30 (getr regs 9).
      stepLD8 F_15f34 D_15f34 (getr regs 18). stepLD8 F_15f38 D_15f38 (getr regs 19).
      zv F_15f3c D_15f3c (Z_to_bv 64 s).
      stepret F_15f40 D_15f40 ret ltac:(bveq).
      unfold KDF. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kd_A1 : forall regs m (s pp kel sy : Z) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (s <= pp \/ pp + 8 <= s - 48)%Z ->
    (1 <= kel)%Z -> (kel + 24 <= s - 48)%Z -> (1 <= sy < 2 ^ 31)%Z -> (pp mod 8 = 0)%Z -> (kel mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 kel)) ->
    rdn SEGS m (Z_to_bv 64 kel) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 sy)) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x15f40 : word) m rom) (mkst regs' (0x15f88 : word) (KDF m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 8 = Z_to_bv 64 pp /\ getr regs' 9 = Z_to_bv 64 kel
      /\ getr regs' 18 = Z_to_bv 64 0 /\ getr regs' 19 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [2; 8; 9; 10; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s pp kel sy ret Hs Hs64 Hpp Hpp8 DJ Hk Hk24 Hsy ALpp ALk SOK Rpp Rsy H2 H1 H10. eexists. split.
    - zv F_15e44 D_15e44 (Z_to_bv 64 (s - 48)).
      stepST F_15e48 D_15e48 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_15e4c D_15e4c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_15e50 D_15e50 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_15e54 D_15e54 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_15e58 D_15e58 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepb_ft F_15e5c D_15e5c ltac:(condZ).
      sn F_15e60 D_15e60.
      zand F_15e64 D_15e64 andi_7 ALpp.
      stepb_ft F_15e68 D_15e68 ltac:(condZ).
      stepLD F_15e6c D_15e6c (word_to_le_bytes 8 (Z_to_bv 64 kel)) (Z_to_bv 64 kel) ltac:(addr_norm; repeat rdn_peel1; exact Rpp) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_15e70 D_15e70 ltac:(condZ).
      zand F_15e74 D_15e74 andi_7 ALk.
      stepb_ft F_15e78 D_15e78 ltac:(condZ).
      stepLD F_15e7c D_15e7c (word_to_le_bytes 4 (Z_to_bv 64 sy)) (Z_to_bv 64 sy) ltac:(addr_norm; repeat rdn_peel1; exact Rsy) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small sy) by lia.
      stepb_ft F_15e80 D_15e80 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_15e84 D_15e84. sn F_15e88 D_15e88.
      unfold KDF. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kd_H : forall regs m (kel arr sy i r : Z),
    (1 <= kel)%Z -> (kel + 24 < 2 ^ 64)%Z -> (1 <= arr)%Z -> (arr + 8 * sy < 2 ^ 64)%Z -> (0 <= i < sy)%Z -> (0 <= r < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (kel + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 arr)) ->
    rdn SEGS m (Z_to_bv 64 (arr + 8 * i)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 r)) -> (arr mod 8 = 0)%Z ->
    getr regs 9 = Z_to_bv 64 kel -> getr regs 18 = Z_to_bv 64 (8 * i) -> getr regs 19 = Z_to_bv 64 i ->
    exists regs',
      msteps SEGS (mkst regs (0x15f88 : word) m rom) (mkst regs' (0x16e80 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x15fbc /\ getr regs' 10 = Z_to_bv 64 r
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m kel arr sy i r Hk Hk64 Ha Ha64 Hi Hr Rarr Rr ALa H9 H18 H19.
    assert (AL8i : ((arr + 8 * i) mod 8 = 0)%Z) by (rewrite Z.mul_comm, Z_mod_plus_full; exact ALa).
    eexists. split.
    - stepLD F_15e8c D_15e8c (word_to_le_bytes 8 (Z_to_bv 64 arr)) (Z_to_bv 64 arr) ltac:(addr_norm; exact Rarr) ltac:(apply bytes_le_to_Z_8).
      zv F_15e90 D_15e90 (Z_to_bv 64 (arr + 8 * i)).
      stepb_ft F_15e94 D_15e94 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_15e98 D_15e98. fixv (Z_to_bv 64 1) ltac:(apply zbv_snez; lia).             (* [comment removed for export] *)
      stepiv F_15e9c D_15e9c (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).   (* [comment removed for export] *)
      zlit F_15ea0 D_15ea0 (Z_to_bv 64 1).                                            (* [comment removed for export] *)
      stepb_ft F_15ea4 D_15ea4 ltac:(condZ).                                          (* [comment removed for export] *)
      stepb_ft F_15ea8 D_15ea8 ltac:(condZ).                                          (* [comment removed for export] *)
      zv F_15eac D_15eac (Z_to_bv 64 (arr + 8 * i)).                                  (* [comment removed for export] *)
      zand F_15eb0 D_15eb0 andi_7 AL8i.
      stepb_ft F_15eb4 D_15eb4 ltac:(condZ).
      stepLD F_15eb8 D_15eb8 (word_to_le_bytes 8 (Z_to_bv 64 r)) (Z_to_bv 64 r) ltac:(addr_norm; exact Rr) ltac:(apply bytes_le_to_Z_8).
      sn F_15ebc D_15ebc.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kd_Nn : forall regs m (kel sy i : Z),
    (1 <= kel)%Z -> (kel + 24 < 2 ^ 64)%Z -> (0 <= i)%Z -> (i + 1 < sy)%Z -> (sy < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 kel) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 sy)) ->
    getr regs 9 = Z_to_bv 64 kel -> getr regs 18 = Z_to_bv 64 (8 * i) -> getr regs 19 = Z_to_bv 64 i ->
    exists regs',
      msteps SEGS (mkst regs (0x15fbc : word) m rom) (mkst regs' (0x15f88 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 18 = Z_to_bv 64 (8 * (i + 1)) /\ getr regs' 19 = Z_to_bv 64 (i + 1)
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [10; 18; 19]%list) regs regs'.
  Proof.
    intros regs m kel sy i Hk Hk64 Hi Hi1 Hsy Rsy H9 H18 H19. eexists. split.
    - stepLD F_15ec0 D_15ec0 (word_to_le_bytes 4 (Z_to_bv 64 sy)) (Z_to_bv 64 sy) ltac:(addr_norm; exact Rsy) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small sy) by lia.
      zv F_15ec4 D_15ec4 (Z_to_bv 64 (i + 1)).
      zv F_15ec8 D_15ec8 (Z_to_bv 64 (8 * (i + 1))).
      stepb_tk F_15ecc D_15ecc ltac:(condZ).                                          (* [comment removed for export] *)
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
      msteps SEGS (mkst regs (0x15fbc : word) m rom) (mkst regs' (0x16e80 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x15fd4 /\ getr regs' 10 = Z_to_bv 64 arr
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [1; 10; 18; 19]%list) regs regs'.
  Proof.
    intros regs m kel arr sy i Hk Hk64 Hi Hi1 Hsy Ha Rsy Rarr H9 H18 H19. eexists. split.
    - stepLD F_15ec0 D_15ec0 (word_to_le_bytes 4 (Z_to_bv 64 sy)) (Z_to_bv 64 sy) ltac:(addr_norm; exact Rsy) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite (v_lw_small sy) by lia.
      zv F_15ec4 D_15ec4 (Z_to_bv 64 (i + 1)).
      zv F_15ec8 D_15ec8 (Z_to_bv 64 (8 * (i + 1))).
      stepb_ft F_15ecc D_15ecc ltac:(condZ).                                          (* [comment removed for export] *)
      stepLD F_15ed0 D_15ed0 (word_to_le_bytes 8 (Z_to_bv 64 arr)) (Z_to_bv 64 arr) ltac:(addr_norm; exact Rarr) ltac:(apply bytes_le_to_Z_8).
      sn F_15ed4 D_15ed4.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kd_P : forall regs m (kel : word),
    getr regs 9 = kel ->
    exists regs',
      msteps SEGS (mkst regs (0x15fd4 : word) m rom) (mkst regs' (0x16e80 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x15fdc /\ getr regs' 10 = kel
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m kel H9. eexists. split.
    - sn F_15ed8 D_15ed8. sn F_15edc D_15edc. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma kd_Q : forall regs m (s pp : Z) (ret s0v s1v s2v s3v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (s <= pp \/ pp + 8 <= s - 48)%Z -> ret_ok ret ->
    store_ok SEGS m (Z_to_bv 64 pp) 8 = true -> kdcells m s ret s0v s1v s2v s3v ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 8 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x15fdc : word) m rom) (mkst regs' ret (wbytes m (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s pp ret s0v s1v s2v s3v Hs Hs64 Hpp Hpp8 DJ Hret SOK (C1 & C2 & C3 & C4 & C5) H2 H8. eexists. split.
    - stepST F_15ee0 D_15ee0 (Z_to_bv 64 pp) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOK).
      sn F_15ee4 D_15ee4.
      stepLD8 F_15f28 D_15f28 ret. stepLD8 F_15f2c D_15f2c s0v. stepLD8 F_15f30 D_15f30 s1v.
      stepLD8 F_15f34 D_15f34 s2v. stepLD8 F_15f38 D_15f38 s3v.
      zv F_15f3c D_15f3c (Z_to_bv 64 s).
      stepret F_15f40 D_15f40 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

End Segs.
End KernSegs2.
