(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptExec LeptExecX.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptUb V23_code_red_casc V23_code_red_rb2 V23_code_red_acc.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
Ltac fixv' v tac := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?x) _ _ _) _ => first [ constr_eq x v | replace x with v by (symmetry; tac) ] end.
Ltac snez1 F D := sn F D; fixv' (Z_to_bv 64 1) ltac:(apply zbv_snez; lia).

Definition PC_pixReduceRankBinaryCascade : Z := 0xa6c38.

(* [comment removed for export] *)
Definition FRBn (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
    (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
    (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
    (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
    (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)))
    (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr regs 22)))
    (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (getr regs 23)))
    (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (getr regs 24)))
    (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (getr regs 25)))
    (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (getr regs 26)))
    (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 (getr regs 27)).
(* [comment removed for export] *)
Definition FCS (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
    (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
    (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
    (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
    (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)))
    (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr regs 22)).

Section Casc.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Section Segs.
  Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma rb_N : forall regs m (s : Z) (ret : word),
    (256 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 208)) 208 = true ->
    rdn SEGS (FRBn m s ret regs) (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) ->
    rdn SEGS (FRBn m s ret regs) (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0xa6f20 : word) m rom) (mkst regs' (0x63740 : word) (FRBn m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 10 = Z_to_bv 64 0x10355 /\ getr regs' 11 = Z_to_bv 64 0x16386 /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
      /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\ getr regs' 22 = getr regs 22 /\ getr regs' 23 = getr regs 23
      /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25 /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m s ret Hs Hs64 SOK Rg Rs H2 H1 H10.
    eexists. split.
    - zv F_a6f20 D_a6f20 (Z_to_bv 64 (s - 208)).
      stepST F_a6f24 D_a6f24 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_a6f28 D_a6f28 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_a6f2c D_a6f2c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_a6f30 D_a6f30 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_a6f34 D_a6f34 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_a6f38 D_a6f38 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_a6f3c D_a6f3c (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_a6f40 D_a6f40 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      stepST F_a6f44 D_a6f44 (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
      stepST F_a6f48 D_a6f48 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
      stepST F_a6f4c D_a6f4c (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).
      stepST F_a6f50 D_a6f50 (Z_to_bv 64 (s - 96)) (getr regs 26) ltac:(sok_in SOK).
      stepST F_a6f54 D_a6f54 (Z_to_bv 64 (s - 104)) (getr regs 27) ltac:(sok_in SOK).
      fold (FRBn m s ret regs).
      stepb_tk F_a6f58 D_a6f58 ltac:(condZ).
      sn F_a6fa8 D_a6fa8.
      stepLD F_a6fac D_a6fac (Z_to_le_bytes 8 0x127c60) (Z_to_bv 64 0x127c60) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_a6fb0 D_a6fb0 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rs) ltac:(apply lez4; lia).
      sn F_a6fb4 D_a6fb4. stepb_ft F_a6fb8 D_a6fb8 ltac:(condZ).
      sn F_a6fbc D_a6fbc. sn F_a6fc0 D_a6fc0. sn F_a6fc4 D_a6fc4. sn F_a6fc8 D_a6fc8.
      stepj F_a6fcc D_a6fcc.
      sn F_a6ff4 D_a6ff4. unfold FRBn.
      stepLD8 F_a6ff8 D_a6ff8 ret. stepLD8 F_a6ffc D_a6ffc (getr regs 8). stepLD8 F_a7000 D_a7000 (getr regs 9).
      stepLD8 F_a7004 D_a7004 (getr regs 18). stepLD8 F_a7008 D_a7008 (getr regs 19). stepLD8 F_a700c D_a700c (getr regs 20).
      stepLD8 F_a7010 D_a7010 (getr regs 21). stepLD8 F_a7014 D_a7014 (getr regs 22). stepLD8 F_a7018 D_a7018 (getr regs 23).
      stepLD8 F_a701c D_a701c (getr regs 24). stepLD8 F_a7020 D_a7020 (getr regs 25). stepLD8 F_a7024 D_a7024 (getr regs 26).
      stepLD8 F_a7028 D_a7028 (getr regs 27).
      zv F_a702c D_a702c (Z_to_bv 64 s).
      stepj F_a7030 D_a7030.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma cs_N : forall regs m (s : Z) (ret : word),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    rdn SEGS (FCS m s ret regs) (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) ->
    rdn SEGS (FCS m s ret regs) (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0xa6c38 : word) m rom) (mkst regs' (0x63740 : word) (FCS m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 10 = Z_to_bv 64 0x10355 /\ getr regs' 11 = Z_to_bv 64 0x15c90 /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
      /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\ getr regs' 22 = getr regs 22
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 20; 21; 22]%list) regs regs'.
  Proof.
    intros regs m s ret Hs Hs64 SOK Rg Rs H2 H1 H10.
    eexists. split.
    - zv F_a6c38 D_a6c38 (Z_to_bv 64 (s - 96)).
      stepST F_a6c3c D_a6c3c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_a6c40 D_a6c40 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_a6c44 D_a6c44 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_a6c48 D_a6c48 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_a6c4c D_a6c4c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_a6c50 D_a6c50 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_a6c54 D_a6c54 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_a6c58 D_a6c58 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      fold (FCS m s ret regs).
      stepb_tk F_a6c5c D_a6c5c ltac:(condZ).
      sn F_a6dc4 D_a6dc4.
      stepLD F_a6dc8 D_a6dc8 (Z_to_le_bytes 8 0x127c60) (Z_to_bv 64 0x127c60) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_a6dcc D_a6dcc (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rs) ltac:(apply lez4; lia).
      sn F_a6dd0 D_a6dd0. stepb_ft F_a6dd4 D_a6dd4 ltac:(condZ).
      sn F_a6dd8 D_a6dd8. sn F_a6ddc D_a6ddc. sn F_a6de0 D_a6de0. sn F_a6de4 D_a6de4.
      stepj F_a6de8 D_a6de8.
      sn F_a6e38 D_a6e38. unfold FCS.
      stepLD8 F_a6e3c D_a6e3c ret. stepLD8 F_a6e40 D_a6e40 (getr regs 8). stepLD8 F_a6e44 D_a6e44 (getr regs 9).
      stepLD8 F_a6e48 D_a6e48 (getr regs 18). stepLD8 F_a6e4c D_a6e4c (getr regs 19). stepLD8 F_a6e50 D_a6e50 (getr regs 20).
      stepLD8 F_a6e54 D_a6e54 (getr regs 21). stepLD8 F_a6e58 D_a6e58 (getr regs 22).
      zv F_a6e5c D_a6e5c (Z_to_bv 64 s).
      stepj F_a6e60 D_a6e60.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma cs_A : forall regs m (s pixs : Z) (v : pixv) (ret : word),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> PIXat m pixs v -> (pixs + 64 <= s - 96 \/ s <= pixs)%Z -> p_d v = 1%Z ->
    (pixs mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixs ->
    getr regs 11 = Z_to_bv 64 1 -> getr regs 12 = Z_to_bv 64 1 -> getr regs 13 = Z_to_bv 64 0 -> getr regs 14 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0xa6c38 : word) m rom) (mkst regs' (0x10e6e0 : word) (FCS m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 1 = Z_to_bv 64 0xa6cb0
      /\ getr regs' 10 = Z_to_bv 64 256 /\ getr regs' 11 = Z_to_bv 64 1
      /\ getr regs' 21 = Z_to_bv 64 pixs /\ getr regs' 20 = Z_to_bv 64 1 /\ getr regs' 19 = Z_to_bv 64 1
      /\ getr regs' 9 = Z_to_bv 64 0 /\ getr regs' 8 = Z_to_bv 64 0 /\ getr regs' 22 = Z_to_bv 64 256
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 19; 20; 21; 22]%list) regs regs'.
  Proof.
    intros regs m s pixs v ret Hs Hs64 Hp1 PX DJ Hd ALp SOK H2 H1 H10 H11 H12 H13 H14.
    pose proof PX as (Hp0 & Hp64 & WF & _).
    eexists. split.
    - zv F_a6c38 D_a6c38 (Z_to_bv 64 (s - 96)).
      stepST F_a6c3c D_a6c3c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_a6c40 D_a6c40 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_a6c44 D_a6c44 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_a6c48 D_a6c48 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_a6c4c D_a6c4c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_a6c50 D_a6c50 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_a6c54 D_a6c54 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_a6c58 D_a6c58 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      stepb_ft F_a6c5c D_a6c5c ltac:(condZ).
      sn F_a6c60 D_a6c60. sn F_a6c64 D_a6c64. sn F_a6c68 D_a6c68. sn F_a6c6c D_a6c6c. sn F_a6c70 D_a6c70.
      stepj F_a6c74 D_a6c74.
      stepb_ft F_6f114 D_6f114 ltac:(condZ).
      guard8 F_6f118 D_6f118 ALp.
      stepb_ft F_6f11c D_6f11c ltac:(condZ).
      stepLD F_6f120 D_6f120 (Z_to_le_bytes 4 (p_d v)) (Z_to_bv 64 (p_d v))
        ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_d SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite Hd. change (v_lw (Z_to_bv 64 1)) with (Z_to_bv 64 1).
      stepret F_6f124 D_6f124 (0xa6c78 : word) ltac:(bveq).
      sn F_a6c78 D_a6c78. stepb_ft F_a6c7c D_a6c7c ltac:(condZ).
      sn F_a6c80 D_a6c80. stepb_ft F_a6c84 D_a6c84 ltac:(condZ). stepb_ft F_a6c88 D_a6c88 ltac:(condZ).
      sn F_a6c8c D_a6c8c. stepb_ft F_a6c90 D_a6c90 ltac:(condZ).
      sn F_a6c94 D_a6c94. stepb_ft F_a6c98 D_a6c98 ltac:(condZ).
      stepb_ft F_a6c9c D_a6c9c ltac:(condZ).
      sn F_a6ca0 D_a6ca0. sn F_a6ca4 D_a6ca4. sn F_a6ca8 D_a6ca8.
      stepj F_a6cac D_a6cac.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma cs_T0 : forall regs m (tab : Z), (4096 <= tab)%Z -> (tab + 256 < 2 ^ 64)%Z -> getr regs 10 = Z_to_bv 64 tab ->
    exists regs',
      msteps SEGS (mkst regs (0xa6cb0 : word) m rom) (mkst regs' (0xa6cd0 : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 tab /\ getr regs' 15 = Z_to_bv 64 1
      /\ getr regs' 16 = Z_to_bv 64 tab /\ getr regs' 17 = Z_to_bv 64 tab
      /\ regs_agree (fun r => In r [11; 12; 13; 14; 15; 16; 17; 18]%list) regs regs'.
  Proof.
    intros regs m tab Ht Ht2 H10.
    eexists. split.
    - sn F_a6cb0 D_a6cb0. sn F_a6cb4 D_a6cb4. sn F_a6cb8 D_a6cb8. sn F_a6cbc D_a6cbc. sn F_a6cc0 D_a6cc0.
      snez1 F_a6cc4 D_a6cc4.
      sn F_a6cc8 D_a6cc8. sn F_a6ccc D_a6ccc.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma cs_Tn : forall regs m (tab k : Z),
    (0 <= k)%Z -> (k + 1 < 256)%Z -> (4096 <= tab)%Z -> (tab + 256 < 2 ^ 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 (tab + k)) 1 = true ->
    getr regs 18 = Z_to_bv 64 tab -> getr regs 15 = Z_to_bv 64 1 ->
    getr regs 16 = Z_to_bv 64 (tab + k) -> getr regs 17 = Z_to_bv 64 (tab + k) -> getr regs 22 = Z_to_bv 64 (256 - k) ->
    exists regs' (x : word),
      msteps SEGS (mkst regs (0xa6cd0 : word) m rom) (mkst regs' (0xa6cd0 : word) (wbytes m (Z_to_bv 64 (tab + k)) (word_to_le_bytes 1 x)) rom)
      /\ getr regs' 18 = Z_to_bv 64 tab /\ getr regs' 15 = Z_to_bv 64 1
      /\ getr regs' 16 = Z_to_bv 64 (tab + (k + 1)) /\ getr regs' 17 = Z_to_bv 64 (tab + (k + 1)) /\ getr regs' 22 = Z_to_bv 64 (256 - (k + 1))
      /\ regs_agree (fun r => In r [5; 6; 7; 11; 12; 13; 14; 16; 17; 22; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs m tab k Hk Hk1 Ht Ht2 SOK H18 H15 H16 H17 H22.
    replace (0xa6cd0 : word) with (Z_to_bv 64 0xa6cd0) by (apply bv_eq; reflexivity).
    ex_entry regs (@nil Z) HR.
    assert (HK : know_ok SEGS (ex_env regs []) m
                   [KRange (EVar 18) 4096 (2 ^ 64 - 257); KRange (EVar 15) 1 1; KRange (EVar 16) 4096 (2 ^ 64 - 3);
                    KRange (EVar 17) 4096 (2 ^ 64 - 3); KRange (EVar 22) 2 256]%Z).
    { unfold know_ok. repeat (apply Forall_cons; [eapply ex_krange; [ex_eden regs | lia | lia] |]). apply Forall_nil. }
    ex_run 300%nat [0xa6cd0; 0xa6f20]%Z (SCR [false] [] []) HR HK R' HR' Hms.
    all: cycle 1.
    { exists R'. eexists. split.
      - ex_mem regs Hms.
      - repeat split; try (ex_reg regs HR'). ex_agree HR HR'. }
    all: try (rewrite ?Z.add_0_r; exact SOK).
  Qed.

  (* [comment removed for export] *)
  Lemma cs_Tx : forall regs m (tab k pixs lv : Z),
    (k = 255)%Z -> (4096 <= tab)%Z -> (tab + 256 < 2 ^ 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 (tab + k)) 1 = true ->
    getr regs 18 = Z_to_bv 64 tab -> getr regs 15 = Z_to_bv 64 1 ->
    getr regs 16 = Z_to_bv 64 (tab + k) -> getr regs 17 = Z_to_bv 64 (tab + k) -> getr regs 22 = Z_to_bv 64 (256 - k) ->
    getr regs 21 = Z_to_bv 64 pixs -> getr regs 20 = Z_to_bv 64 lv ->
    exists regs' (x : word),
      msteps SEGS (mkst regs (0xa6cd0 : word) m rom) (mkst regs' (0xa6f20 : word) (wbytes m (Z_to_bv 64 (tab + k)) (word_to_le_bytes 1 x)) rom)
      /\ getr regs' 1 = Z_to_bv 64 0xa6d58 /\ getr regs' 10 = Z_to_bv 64 pixs /\ getr regs' 11 = Z_to_bv 64 lv /\ getr regs' 12 = Z_to_bv 64 tab
      /\ regs_agree (fun r => In r [1; 5; 6; 7; 10; 11; 12; 13; 14; 16; 17; 22; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs m tab k pixs lv Hk Ht Ht2 SOK H18 H15 H16 H17 H22 H21 H20. subst k.
    replace (0xa6cd0 : word) with (Z_to_bv 64 0xa6cd0) by (apply bv_eq; reflexivity).
    replace (0xa6f20 : word) with (Z_to_bv 64 0xa6f20) by (apply bv_eq; reflexivity).
    ex_entry regs (@nil Z) HR.
    assert (HK : know_ok SEGS (ex_env regs []) m
                   [KRange (EVar 18) 4096 (2 ^ 64 - 257); KRange (EVar 15) 1 1; KRange (EVar 16) 4096 (2 ^ 64 - 2);
                    KRange (EVar 17) 4096 (2 ^ 64 - 2); KRange (EVar 22) 1 1]%Z).
    { unfold know_ok. repeat (apply Forall_cons; [eapply ex_krange; [ex_eden regs | lia | lia] |]). apply Forall_nil. }
    ex_run 300%nat [0xa6cd0; 0xa6f20]%Z (SCR [false] [] []) HR HK R' HR' Hms.
    all: cycle 1.
    { exists R'. eexists. split.
      - ex_mem regs Hms.
      - repeat split; try (ex_reg regs HR'). ex_agree HR HR'. }
    all: try (rewrite ?Z.add_0_r; exact SOK).
  Qed.

  (* [comment removed for export] *)
  Lemma cs_C : forall regs m (s : Z),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 72)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 19 = Z_to_bv 64 1 ->
    exists regs',
      msteps SEGS (mkst regs (0xa6d58 : word) m rom) (mkst regs' (0xa6f20 : word) (wbytes m (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (getr regs 10))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0xa6d6c /\ getr regs' 10 = getr regs 10 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = getr regs 18
      /\ regs_agree (fun r => In r [1; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s Hs Hs64 SOK H2 H19.
    eexists. split.
    - stepST F_a6d58 D_a6d58 (Z_to_bv 64 (s - 72)) (getr regs 10) ltac:(store_ok_peel; exact SOK).
      stepb_ft F_a6d5c D_a6d5c ltac:(condZ).
      sn F_a6d60 D_a6d60. sn F_a6d64 D_a6d64.
      stepj F_a6d68 D_a6d68.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma cs_D : forall regs m (s : Z),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 80)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs',
      msteps SEGS (mkst regs (0xa6d6c : word) m rom) (mkst regs' (0x6df98 : word) (wbytes m (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (getr regs 10))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0xa6d7c /\ getr regs' 10 = Z_to_bv 64 (s - 72) /\ getr regs' 19 = getr regs 10
      /\ regs_agree (fun r => In r [1; 10; 19]%list) regs regs'.
  Proof.
    intros regs m s Hs Hs64 SOK H2.
    eexists. split.
    - sn F_a6d6c D_a6d6c.
      stepST F_a6d70 D_a6d70 (Z_to_bv 64 (s - 80)) (getr regs 10) ltac:(store_ok_peel; exact SOK).
      zv F_a6d74 D_a6d74 (Z_to_bv 64 (s - 72)).
      stepj F_a6d78 D_a6d78.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma cs_E : forall regs m, getr regs 9 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0xa6d7c : word) m rom) (mkst regs' (0x10e818 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0xa6f04 /\ getr regs' 10 = getr regs 18
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m H9.
    eexists. split.
    - stepb_tk F_a6d7c D_a6d7c ltac:(condZ).
      sn F_a6efc D_a6efc.
      stepj F_a6f00 D_a6f00.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma cs_F : forall regs m (s : Z) (ret s0v s1v s2v s3v s4v s5v s6v : word),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    cellsZ m [(s - 8, ret); (s - 16, s0v); (s - 24, s1v); (s - 32, s2v); (s - 40, s3v); (s - 48, s4v); (s - 56, s5v); (s - 64, s6v)]%Z ->
    getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs',
      msteps SEGS (mkst regs (0xa6f04 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = getr regs 19
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v s2v s3v s4v s5v s6v Hs Hs64 Hret (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & _) H2.
    eexists. split.
    - sn F_a6f04 D_a6f04.
      stepj F_a6f08 D_a6f08.
      stepLD F_a6e68 D_a6e68 (word_to_le_bytes 8 ret) ret ltac:(addr_norm; exact C1) ltac:(apply bytes_le_to_Z_8).
      stepLD F_a6e6c D_a6e6c (word_to_le_bytes 8 s0v) s0v ltac:(addr_norm; exact C2) ltac:(apply bytes_le_to_Z_8).
      stepLD F_a6e70 D_a6e70 (word_to_le_bytes 8 s1v) s1v ltac:(addr_norm; exact C3) ltac:(apply bytes_le_to_Z_8).
      stepLD F_a6e74 D_a6e74 (word_to_le_bytes 8 s2v) s2v ltac:(addr_norm; exact C4) ltac:(apply bytes_le_to_Z_8).
      stepLD F_a6e78 D_a6e78 (word_to_le_bytes 8 s3v) s3v ltac:(addr_norm; exact C5) ltac:(apply bytes_le_to_Z_8).
      stepLD F_a6e7c D_a6e7c (word_to_le_bytes 8 s4v) s4v ltac:(addr_norm; exact C6) ltac:(apply bytes_le_to_Z_8).
      stepLD F_a6e80 D_a6e80 (word_to_le_bytes 8 s5v) s5v ltac:(addr_norm; exact C7) ltac:(apply bytes_le_to_Z_8).
      stepLD F_a6e84 D_a6e84 (word_to_le_bytes 8 s6v) s6v ltac:(addr_norm; exact C8) ltac:(apply bytes_le_to_Z_8).
      zv F_a6e88 D_a6e88 (Z_to_bv 64 s).
      stepret F_a6e8c D_a6e8c ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.
End Casc.
