(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.paintcmap_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac MmapSim SeqExec.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require Import V21LeptStderr V21LeptBase V21LeptUb V21LeptBox V21LeptPixCopy V21LeptSelLoop V21_code_136d4_14000 V21_code_14000_15000 V21_code_15000_16000 V21_code_16000_17000.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

(* [comment removed for export] *)
Definition svr13 (regs : bvmap 5 word) (i : nat) : word :=
  match i with 8 => getr regs 8 | 9 => getr regs 9 | 18 => getr regs 18 | 19 => getr regs 19 | 20 => getr regs 20
  | 21 => getr regs 21 | 22 => getr regs 22 | 23 => getr regs 23 | 24 => getr regs 24 | 25 => getr regs 25 | 26 => getr regs 26 | _ => getr regs 27 end%nat.
Definition frame13 (s : Z) (ret : word) (sv : nat -> word) : list (Z * word) :=
  [((s - 8)%Z, ret); ((s - 16)%Z, sv 8%nat); ((s - 24)%Z, sv 9%nat); ((s - 32)%Z, sv 18%nat); ((s - 40)%Z, sv 19%nat); ((s - 48)%Z, sv 20%nat);
   ((s - 56)%Z, sv 21%nat); ((s - 64)%Z, sv 22%nat); ((s - 72)%Z, sv 23%nat); ((s - 80)%Z, sv 24%nat); ((s - 88)%Z, sv 25%nat);
   ((s - 96)%Z, sv 26%nat); ((s - 104)%Z, sv 27%nat)].

Ltac zva F D v := stepiv F D v ltac:(gres; pin; imm_norm; rewrite ?zbv_addi, ?zbv_add, ?zbv_sub, ?zbv_mul; first [reflexivity | f_equal; lia]).
Ltac zvs F D v := stepiv F D v ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
Ltac seqz_nz F D := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).
Ltac litv F D v := sn F D; fixv v ltac:(apply bv_eq; vm_compute; reflexivity).

Section SelSegs.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU21} {P16 : V21Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

  Definition FR13 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
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

  Lemma cells_FR13 : forall m s ret regs, (144 <= s)%Z -> (s < 2 ^ 64)%Z -> cellsZ (FR13 m s ret regs) (frame13 s ret (svr13 regs)).
  Proof. intros m s ret regs Hs Hs64. unfold frame13, FR13, svr13. cbn [cellsZ]. repeat split; rdn_solve. Qed.

  Lemma frame13_bounds : forall s ret sv, (144 <= s)%Z -> (s < 2 ^ 64)%Z ->
    Forall (fun av => s - 104 <= fst av /\ fst av + 8 <= 2 ^ 64)%Z (frame13 s ret sv).
  Proof. intros s ret sv Hs Hs64. unfold frame13. repeat (apply Forall_cons; [cbn [fst snd]; lia |]). apply Forall_nil. Qed.

  Lemma cells13_frm : forall C s' m m' s ret sv, Cok C -> FRM C s' m m' -> (c_top C - LSTK <= s')%Z -> (s' <= s - 104)%Z -> (144 <= s)%Z -> (s < 2 ^ 64)%Z ->
    cellsZ m (frame13 s ret sv) -> cellsZ m' (frame13 s ret sv).
  Proof.
    intros C s' m m' s ret sv CK F Hlo Hs' Hs Hs64 CE. apply (cellsZ_frm C s' m m' _ CK F Hlo); [| exact CE].
    eapply Forall_impl; [| apply (frame13_bounds s ret sv Hs Hs64)]. intros av [A B]. lia.
  Qed.

  Lemma cells13_out : forall m m' (lo hi : Z) s ret sv, (forall x : word, ~ (lo <= u x < hi)%Z -> m' x = m x) -> (hi <= s - 104 \/ s <= lo)%Z -> (144 <= s)%Z -> (s < 2 ^ 64)%Z ->
    cellsZ m (frame13 s ret sv) -> cellsZ m' (frame13 s ret sv).
  Proof.
    intros m m' lo hi s ret sv OUT Hd Hs Hs64 CE. apply (cellsZ_out m m' lo hi _ OUT); [| exact CE].
    unfold frame13. repeat (apply Forall_cons; [cbn [fst snd]; lia |]). apply Forall_nil.
  Qed.

Section Segs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma ss_P : forall regs m (s : Z) (ret : word),
    (144 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 144)) 144 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret ->
    exists regs',
      msteps SEGS (mkst regs (0x168ac : word) m rom) (mkst regs' (0x168e4 : word) (FR13 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 144) /\ getr regs' 1 = ret
      /\ regs_agree (fun r => In r [2]%list) regs regs'.
  Proof.
    intros regs m s ret Hs Hs64 SOK H2 H1. unfold FR13. eexists. split.
    - zv F_167a8 D_167a8 (Z_to_bv 64 (s - 144)).
      stepST F_167ac D_167ac (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_167b0 D_167b0 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_167b4 D_167b4 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_167b8 D_167b8 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_167bc D_167bc (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_167c0 D_167c0 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_167c4 D_167c4 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_167c8 D_167c8 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      stepST F_167cc D_167cc (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
      stepST F_167d0 D_167d0 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
      stepST F_167d4 D_167d4 (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).
      stepST F_167d8 D_167d8 (Z_to_bv 64 (s - 96)) (getr regs 26) ltac:(sok_in SOK).
      stepST F_167dc D_167dc (Z_to_bv 64 (s - 104)) (getr regs 27) ltac:(sok_in SOK).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_etail : forall regs m (s : Z) (ret : word) (sv : nat -> word) (msg : Z),
    (144 <= s)%Z -> (s < 2 ^ 64)%Z -> cellsZ m (frame13 s ret sv) ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 10 = Z_to_bv 64 msg -> getr regs 11 = Z_to_bv 64 0x10d41 ->
    exists regs',
      msteps SEGS (mkst regs (0x16a38 : word) m rom) (mkst regs' (0x13e3c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 msg /\ getr regs' 11 = Z_to_bv 64 0x10d41 /\ getr regs' 12 = Z_to_bv 64 1
      /\ getr regs' 8 = sv 8%nat /\ getr regs' 9 = sv 9%nat /\ getr regs' 18 = sv 18%nat /\ getr regs' 19 = sv 19%nat /\ getr regs' 20 = sv 20%nat
      /\ getr regs' 21 = sv 21%nat /\ getr regs' 22 = sv 22%nat /\ getr regs' 23 = sv 23%nat /\ getr regs' 24 = sv 24%nat /\ getr regs' 25 = sv 25%nat
      /\ getr regs' 26 = sv 26%nat /\ getr regs' 27 = sv 27%nat
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 12; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m s ret sv msg Hs Hs64 CE H2 H10 H11. unfold frame13 in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & _).
    eexists. split.
    - sn F_16934 D_16934.
      stepLD8 F_16938 D_16938 ret. stepLD8 F_1693c D_1693c (sv 8%nat). stepLD8 F_16940 D_16940 (sv 9%nat).
      stepLD8 F_16944 D_16944 (sv 18%nat). stepLD8 F_16948 D_16948 (sv 19%nat). stepLD8 F_1694c D_1694c (sv 20%nat).
      stepLD8 F_16950 D_16950 (sv 21%nat). stepLD8 F_16954 D_16954 (sv 22%nat). stepLD8 F_16958 D_16958 (sv 23%nat).
      stepLD8 F_1695c D_1695c (sv 24%nat). stepLD8 F_16960 D_16960 (sv 25%nat). stepLD8 F_16964 D_16964 (sv 26%nat).
      stepLD8 F_16968 D_16968 (sv 27%nat).
      zv F_1696c D_1696c (Z_to_bv 64 s). sn F_16970 D_16970.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_RET : forall regs m (s : Z) (ret : word) (sv : nat -> word) (a0v : word),
    (144 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cellsZ m (frame13 s ret sv) ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 10 = a0v ->
    exists regs',
      msteps SEGS (mkst regs (0x16d64 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = a0v
      /\ getr regs' 8 = sv 8%nat /\ getr regs' 9 = sv 9%nat /\ getr regs' 18 = sv 18%nat /\ getr regs' 19 = sv 19%nat /\ getr regs' 20 = sv 20%nat
      /\ getr regs' 21 = sv 21%nat /\ getr regs' 22 = sv 22%nat /\ getr regs' 23 = sv 23%nat /\ getr regs' 24 = sv 24%nat /\ getr regs' 25 = sv 25%nat
      /\ getr regs' 26 = sv 26%nat /\ getr regs' 27 = sv 27%nat
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m s ret sv a0v Hs Hs64 Hret CE H2 H10. unfold frame13 in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & _).
    eexists. split.
    - stepLD8 F_16c60 D_16c60 ret. stepLD8 F_16c64 D_16c64 (sv 8%nat). stepLD8 F_16c68 D_16c68 (sv 9%nat).
      stepLD8 F_16c6c D_16c6c (sv 18%nat). stepLD8 F_16c70 D_16c70 (sv 19%nat). stepLD8 F_16c74 D_16c74 (sv 20%nat).
      stepLD8 F_16c78 D_16c78 (sv 21%nat). stepLD8 F_16c7c D_16c7c (sv 22%nat). stepLD8 F_16c80 D_16c80 (sv 23%nat).
      stepLD8 F_16c84 D_16c84 (sv 24%nat). stepLD8 F_16c88 D_16c88 (sv 25%nat). stepLD8 F_16c8c D_16c8c (sv 26%nat).
      stepLD8 F_16c90 D_16c90 (sv 27%nat).
      zv F_16c94 D_16c94 (Z_to_bv 64 s). stepret F_16c98 D_16c98 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_ehead : forall (pc msg : Z) regs m (s : Z),
    In (pc, msg) [(0x1699c, 0x10298); (0x169c4, 0x108f0); (0x169ec, 0x10368); (0x16a14, 0x10891)]%Z ->
    rdn SEGS m (Z_to_bv 64 0x20e58) 8 = Some (Z_to_le_bytes 8 0x21ec8) -> rdn SEGS m (Z_to_bv 64 0x21ec8) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 (s - 144) ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 pc) m rom) (mkst regs' (0x16a38 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 144) /\ getr regs' 10 = Z_to_bv 64 msg /\ getr regs' 11 = Z_to_bv 64 0x10d41
      /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
  Proof.
    intros pc msg regs m s Hin Rg Rs H2. cbn [In] in Hin.
    destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as Epc Emsg; subst pc msg.
    - eexists. split.
      + replace (Z_to_bv 64 0x1699c) with (0x1699c : word) by (apply bv_eq; reflexivity).
        sn F_16898 D_16898.
        stepLD F_1689c D_1689c (Z_to_le_bytes 8 0x21ec8) (Z_to_bv 64 0x21ec8) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_168a0 D_168a0 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_168a4 D_168a4. stepb_ft F_168a8 D_168a8 ltac:(condZ).
        sn F_168ac D_168ac. sn F_168b0 D_168b0. sn F_168b4 D_168b4. sn F_168b8 D_168b8. sn F_168bc D_168bc.
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      + replace (Z_to_bv 64 0x169c4) with (0x169c4 : word) by (apply bv_eq; reflexivity).
        sn F_168c0 D_168c0.
        stepLD F_168c4 D_168c4 (Z_to_le_bytes 8 0x21ec8) (Z_to_bv 64 0x21ec8) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_168c8 D_168c8 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_168cc D_168cc. stepb_ft F_168d0 D_168d0 ltac:(condZ).
        sn F_168d4 D_168d4. sn F_168d8 D_168d8. sn F_168dc D_168dc. sn F_168e0 D_168e0. sn F_168e4 D_168e4.
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      + replace (Z_to_bv 64 0x169ec) with (0x169ec : word) by (apply bv_eq; reflexivity).
        sn F_168e8 D_168e8.
        stepLD F_168ec D_168ec (Z_to_le_bytes 8 0x21ec8) (Z_to_bv 64 0x21ec8) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_168f0 D_168f0 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_168f4 D_168f4. stepb_ft F_168f8 D_168f8 ltac:(condZ).
        sn F_168fc D_168fc. sn F_16900 D_16900. sn F_16904 D_16904. sn F_16908 D_16908. sn F_1690c D_1690c.
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      + replace (Z_to_bv 64 0x16a14) with (0x16a14 : word) by (apply bv_eq; reflexivity).
        sn F_16910 D_16910.
        stepLD F_16914 D_16914 (Z_to_le_bytes 8 0x21ec8) (Z_to_bv 64 0x21ec8) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_16918 D_16918 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_1691c D_1691c. stepb_ft F_16920 D_16920 ltac:(condZ).
        sn F_16924 D_16924. sn F_16928 D_16928. sn F_1692c D_1692c. sn F_16930 D_16930.
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_A0 : forall regs m,
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x168e4 : word) m rom) (mkst regs' (Z_to_bv 64 0x1699c) m rom)
      /\ regs_agree (fun r => In r []%list) regs regs'.
  Proof.
    intros regs m H10. eexists. split.
    - stepb_tk F_167e0 D_167e0 ltac:(condZ).
      replace (0x1699c : word) with (Z_to_bv 64 0x1699c) by (apply bv_eq; reflexivity). apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_A : forall regs m (pixd bx : Z) (vd : pixv),
    (1 <= pixd)%Z -> (pixd mod 16 = 0)%Z -> PIXat m pixd vd -> (0 <= bx < 2 ^ 64)%Z ->
    getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 bx -> getr regs 12 = Z_to_bv 64 2 ->
    getr regs 13 = Z_to_bv 64 255 -> getr regs 14 = Z_to_bv 64 255 -> getr regs 15 = Z_to_bv 64 100 ->
    exists regs',
      msteps SEGS (mkst regs (0x168e4 : word) m rom) (mkst regs' (0x16904 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (p_cmap vd) /\ getr regs' 20 = Z_to_bv 64 100 /\ getr regs' 21 = Z_to_bv 64 255 /\ getr regs' 22 = Z_to_bv 64 255
      /\ getr regs' 8 = Z_to_bv 64 2 /\ getr regs' 18 = Z_to_bv 64 bx /\ getr regs' 19 = Z_to_bv 64 pixd /\ getr regs' 2 = getr regs 2
      /\ regs_agree (fun r => In r [1; 8; 10; 11; 18; 19; 20; 21; 22]%list) regs regs'.
  Proof.
    intros regs m pixd bx vd Hp ALp PX Hbx H10 H11 H12 H13 H14 H15. pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_cmap _ WF) as Rc.
    assert (ALp8 : (pixd mod 8 = 0)%Z) by (apply al16_mod8; exact ALp).
    pose proof (PIX_rd_cmap SEGS _ _ _ PX) as Cc.
    eexists. split.
    - stepb_ft F_167e0 D_167e0 ltac:(condZ).
      sn F_167e4 D_167e4. sn F_167e8 D_167e8. sn F_167ec D_167ec. sn F_167f0 D_167f0. sn F_167f4 D_167f4. sn F_167f8 D_167f8.
      sn F_167fc D_167fc.
      stepb_ft F_155e8 D_155e8 ltac:(condZ).
      guard8 F_155ec D_155ec ALp8. stepb_ft F_155f0 D_155f0 ltac:(condZ). (* [comment removed for export] *)
      stepLD F_155f4 D_155f4 (Z_to_le_bytes 8 (p_cmap vd)) (Z_to_bv 64 (p_cmap vd)) ltac:(addr_norm; exact Cc) ltac:(apply lez8; lia).
      stepret F_155f8 D_155f8 (0x16904 : word) ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_B0 : forall regs m,
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x16904 : word) m rom) (mkst regs' (Z_to_bv 64 0x169c4) m rom)
      /\ regs_agree (fun r => In r []%list) regs regs'.
  Proof.
    intros regs m H10. eexists. split.
    - stepb_tk F_16800 D_16800 ltac:(condZ).
      replace (0x169c4 : word) with (Z_to_bv 64 0x169c4) by (apply bv_eq; reflexivity). apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_Bd : forall regs m (pixd cd : Z) (vd : pixv),
    (1 <= pixd)%Z -> (pixd mod 16 = 0)%Z -> PIXat m pixd vd -> (1 <= cd)%Z -> (cd < 2 ^ 64)%Z -> (8 < p_d vd)%Z ->
    getr regs 10 = Z_to_bv 64 cd -> getr regs 19 = Z_to_bv 64 pixd ->
    exists regs', msteps SEGS (mkst regs (0x16904 : word) m rom) (mkst regs' (Z_to_bv 64 0x16a14) m rom)
      /\ regs_agree (fun r => In r [1; 10; 11; 23]%list) regs regs'.
  Proof.
    intros regs m pixd cd vd Hp ALp PX Hcd Hcd64 Hd H10 H19. pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_d _ WF) as Rd.
    assert (ALp8 : (pixd mod 8 = 0)%Z) by (apply al16_mod8; exact ALp).
    pose proof (PIX_rd_d SEGS _ _ _ PX) as Cd.
    eexists. split.
    - stepb_ft F_16800 D_16800 ltac:(condZ).
      sn F_16804 D_16804. sn F_16808 D_16808. sn F_1680c D_1680c.
      stepb_ft F_15550 D_15550 ltac:(condZ).
      guard8 F_15554 D_15554 ALp8. stepb_ft F_15558 D_15558 ltac:(condZ). (* [comment removed for export] *)
      stepLD F_1555c D_1555c (Z_to_le_bytes 4 (p_d vd)) (Z_to_bv 64 (p_d vd)) ltac:(addr_norm; exact Cd) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d vd)) by lia.
      stepret F_15560 D_15560 (0x16914 : word) ltac:(bveq).
      sn F_16810 D_16810. stepb_tk F_16814 D_16814 ltac:(condZ).
      replace (0x16a14 : word) with (Z_to_bv 64 0x16a14) by (apply bv_eq; reflexivity). apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_Bn : forall regs m (pixd cd : Z) (vd : pixv) (cv : cmapv),
    (1 <= pixd)%Z -> (pixd mod 16 = 0)%Z -> PIXat m pixd vd -> (1 <= cd)%Z -> (cd mod 16 = 0)%Z -> CMAPat m cd cv -> (p_d vd = 1 \/ p_d vd = 2 \/ p_d vd = 4 \/ p_d vd = 8)%Z -> (c_n cv <= 2)%Z ->
    getr regs 10 = Z_to_bv 64 cd -> getr regs 19 = Z_to_bv 64 pixd -> getr regs 8 = Z_to_bv 64 2 ->
    exists regs', msteps SEGS (mkst regs (0x16904 : word) m rom) (mkst regs' (Z_to_bv 64 0x169ec) m rom)
      /\ regs_agree (fun r => In r [1; 9; 10; 11; 23]%list) regs regs'.
  Proof.
    intros regs m pixd cd vd cv Hp ALp PX Hcd ALc CM Hd Hn H10 H19 H8. pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_d _ WF) as Rd.
    assert (ALp8 : (pixd mod 8 = 0)%Z) by (apply al16_mod8; exact ALp). assert (ALc8 : (cd mod 8 = 0)%Z) by (apply al16_mod8; exact ALc).
    pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_n _ CWF) as Rn.
    pose proof (PIX_rd_d SEGS _ _ _ PX) as Cd. pose proof (CMAP_rd_n SEGS _ _ _ CM) as Cn.
    eexists. split.
    - stepb_ft F_16800 D_16800 ltac:(condZ).
      sn F_16804 D_16804. sn F_16808 D_16808. sn F_1680c D_1680c.
      stepb_ft F_15550 D_15550 ltac:(condZ).
      guard8 F_15554 D_15554 ALp8. stepb_ft F_15558 D_15558 ltac:(condZ). (* [comment removed for export] *)
      stepLD F_1555c D_1555c (Z_to_le_bytes 4 (p_d vd)) (Z_to_bv 64 (p_d vd)) ltac:(addr_norm; exact Cd) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d vd)) by lia.
      stepret F_15560 D_15560 (0x16914 : word) ltac:(bveq).
      sn F_16810 D_16810. stepb_ft F_16814 D_16814 ltac:(condZ).
      sn F_16818 D_16818. sn F_1681c D_1681c. sn F_16820 D_16820. sn F_16824 D_16824.
      stepb_ft F_16828 D_16828 ltac:(pin; rewrite (depth_mask_278 (p_d vd) Hd); reflexivity).
      sn F_1682c D_1682c. sn F_16830 D_16830.
      stepb_ft F_15f04 D_15f04 ltac:(condZ).
      guard8 F_15f08 D_15f08 ALc8. stepb_ft F_15f0c D_15f0c ltac:(condZ). (* [comment removed for export] *)
      stepLD F_15f10 D_15f10 (Z_to_le_bytes 4 (c_n cv)) (Z_to_bv 64 (c_n cv)) ltac:(addr_norm; exact Cn) ltac:(apply lez4; lia).
      rewrite (v_lw_small (c_n cv)) by lia.
      stepret F_15f14 D_15f14 (0x16938 : word) ltac:(bveq).
      stepb_tk F_16834 D_16834 ltac:(condZ).
      replace (0x169ec : word) with (Z_to_bv 64 0x169ec) by (apply bv_eq; reflexivity). apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_B : forall regs m (s pixd cd : Z) (vd : pixv) (cv : cmapv),
    (1 <= pixd)%Z -> (pixd mod 16 = 0)%Z -> PIXat m pixd vd -> (1 <= cd)%Z -> (cd mod 16 = 0)%Z -> CMAPat m cd cv -> (p_d vd = 1 \/ p_d vd = 2 \/ p_d vd = 4 \/ p_d vd = 8)%Z -> (2 < c_n cv)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 10 = Z_to_bv 64 cd -> getr regs 19 = Z_to_bv 64 pixd -> getr regs 8 = Z_to_bv 64 2 ->
    getr regs 20 = Z_to_bv 64 100 -> getr regs 21 = Z_to_bv 64 255 -> getr regs 22 = Z_to_bv 64 255 ->
    exists regs', msteps SEGS (mkst regs (0x16904 : word) m rom) (mkst regs' (0x15f10 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 144) /\ getr regs' 1 = Z_to_bv 64 0x16958
      /\ getr regs' 10 = Z_to_bv 64 cd /\ getr regs' 11 = Z_to_bv 64 255 /\ getr regs' 12 = Z_to_bv 64 255 /\ getr regs' 13 = Z_to_bv 64 100 /\ getr regs' 14 = Z_to_bv 64 (s - 132)
      /\ getr regs' 9 = Z_to_bv 64 (p_d vd) /\ getr regs' 23 = Z_to_bv 64 cd /\ getr regs' 24 = Z_to_bv 64 (c_n cv)
      /\ regs_agree (fun r => In r [1; 9; 10; 11; 12; 13; 14; 23; 24]%list) regs regs'.
  Proof.
    intros regs m s pixd cd vd cv Hp ALp PX Hcd ALc CM Hd Hn H2 H10 H19 H8 H20 H21 H22. pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_d _ WF) as Rd.
    assert (ALp8 : (pixd mod 8 = 0)%Z) by (apply al16_mod8; exact ALp). assert (ALc8 : (cd mod 8 = 0)%Z) by (apply al16_mod8; exact ALc).
    pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_n _ CWF) as Rn.
    pose proof (PIX_rd_d SEGS _ _ _ PX) as Cd. pose proof (CMAP_rd_n SEGS _ _ _ CM) as Cn.
    eexists. split.
    - stepb_ft F_16800 D_16800 ltac:(condZ).
      sn F_16804 D_16804. sn F_16808 D_16808. sn F_1680c D_1680c.
      stepb_ft F_15550 D_15550 ltac:(condZ).
      guard8 F_15554 D_15554 ALp8. stepb_ft F_15558 D_15558 ltac:(condZ). (* [comment removed for export] *)
      stepLD F_1555c D_1555c (Z_to_le_bytes 4 (p_d vd)) (Z_to_bv 64 (p_d vd)) ltac:(addr_norm; exact Cd) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d vd)) by lia.
      stepret F_15560 D_15560 (0x16914 : word) ltac:(bveq).
      sn F_16810 D_16810. stepb_ft F_16814 D_16814 ltac:(condZ).
      sn F_16818 D_16818. sn F_1681c D_1681c. sn F_16820 D_16820. sn F_16824 D_16824.
      stepb_ft F_16828 D_16828 ltac:(pin; rewrite (depth_mask_278 (p_d vd) Hd); reflexivity).
      sn F_1682c D_1682c. sn F_16830 D_16830.
      stepb_ft F_15f04 D_15f04 ltac:(condZ).
      guard8 F_15f08 D_15f08 ALc8. stepb_ft F_15f0c D_15f0c ltac:(condZ). (* [comment removed for export] *)
      stepLD F_15f10 D_15f10 (Z_to_le_bytes 4 (c_n cv)) (Z_to_bv 64 (c_n cv)) ltac:(addr_norm; exact Cn) ltac:(apply lez4; lia).
      rewrite (v_lw_small (c_n cv)) by lia.
      stepret F_15f14 D_15f14 (0x16938 : word) ltac:(bveq).
      stepb_ft F_16834 D_16834 ltac:(condZ).
      sn F_16838 D_16838. zv F_1683c D_1683c (Z_to_bv 64 (s - 132)). sn F_16840 D_16840. sn F_16844 D_16844. sn F_16848 D_16848. sn F_1684c D_1684c.
      sn F_16850 D_16850.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rdn1_of : forall m (a : word) b, m a = Some b -> rdn SEGS m a 1 = Some [b].
  Proof. intros m a b E. cbn [rdn]. rewrite E. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma gi_loop : forall c regs m (arr p n i : Z) (ret : word),
    (1 <= arr)%Z -> (arr + 4 * n < 2 ^ 64)%Z -> (0 <= i)%Z -> (Z.of_nat (S c) = n - i)%Z -> (1 <= p)%Z -> (p + 4 <= 2 ^ 64)%Z ->
    (forall a : word, (arr <= u a < arr + 4 * n)%Z -> m a <> None) ->
    store_ok SEGS m (Z_to_bv 64 p) 4 = true -> getr regs 1 = ret -> ret_ok ret ->
    getr regs 17 = Z_to_bv 64 arr -> getr regs 5 = Z_to_bv 64 (arr + 1 + 4 * i) -> getr regs 6 = Z_to_bv 64 1 -> getr regs 7 = Z_to_bv 64 (arr + 4 * i) ->
    getr regs 16 = Z_to_bv 64 i -> getr regs 15 = Z_to_bv 64 (n - i) ->
    getr regs 10 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 p ->
    getr regs 11 = Z_to_bv 64 255 -> getr regs 12 = Z_to_bv 64 255 -> getr regs 13 = Z_to_bv 64 100 ->
    exists regs' m',
      msteps SEGS (mkst regs (0x15f68 : word) m rom) (mkst regs' ret m' rom)
      /\ ( (getr regs' 10 = Z_to_bv 64 1 /\ m' = m)
           \/ (getr regs' 10 = Z_to_bv 64 0 /\ exists i', (0 <= i' < n)%Z /\ m' = wbytes m (Z_to_bv 64 p) (word_to_le_bytes 4 (Z_to_bv 64 i'))) )
      /\ regs_agree (fun r => In r [5; 7; 10; 15; 16; 28]%list) regs regs'.
  Proof.
    induction c as [|c IH]; intros regs m arr p n i ret Harr Harr64 Hi Hc Hp Hp64 DEF SOK H1 Hret H17 H5 H6 H7 H16 H15 H10 H14 H11 H12 H13.
    all: destruct (m (Z_to_bv 64 (arr + 1 + 4 * i + 1))) as [b2|] eqn:E2; [| exfalso; exact (DEF (Z_to_bv 64 (arr + 1 + 4 * i + 1)) ltac:(rewrite u_Z2bv by lia; lia) E2)].
    all: destruct (m (Z_to_bv 64 (arr + 1 + 4 * i))) as [b1|] eqn:E1; [| exfalso; exact (DEF (Z_to_bv 64 (arr + 1 + 4 * i)) ltac:(rewrite u_Z2bv by lia; lia) E1)].
    all: destruct (m (Z_to_bv 64 (arr + 1 + 4 * i - 1))) as [b0|] eqn:E0; [| exfalso; exact (DEF (Z_to_bv 64 (arr + 1 + 4 * i - 1)) ltac:(rewrite u_Z2bv by lia; lia) E0)].
    all: pose proof (rdn1_of m _ _ E2) as R2; pose proof (rdn1_of m _ _ E1) as R1; pose proof (rdn1_of m _ _ E0) as R0.
    all: pose proof (u_byte64 b2) as U2; pose proof (u_byte64 b1) as U1; pose proof (u_byte64 b0) as U0.
    (* [comment removed for export] *)
    all: assert (HD : exists rh, msteps SEGS (mkst regs (0x15f68 : word) m rom) (mkst rh (0x15f80 : word) m rom)
                             /\ getr rh 28 = Z_to_bv 64 (bv_unsigned b2) /\ regs_agree (fun r => In r [28]%list) regs rh)
      by (eexists; split;
          [ stepb_ft F_15e64 D_15e64 ltac:(condZ);
            seqz_nz F_15e68 D_15e68;
            litv F_15e6c D_15e6c (Z_to_bv 64 1);
            stepb_ft F_15e70 D_15e70 ltac:(condZ);
            stepb_ft F_15e74 D_15e74 ltac:(condZ);
            stepLBU F_15e78 D_15e78 b2 ltac:(rdn_addr (arr + 1 + 4 * i + 1)%Z; exact R2);
            apply mst_refl
          | split; [gres; pin; reflexivity | solve_regs_agree] ]).
    all: destruct HD as (rh & SH & Q28 & AGh).
    all: pose proof (AGh 11 ltac:(notin_list)) as P11; rewrite H11 in P11; pose proof (AGh 12 ltac:(notin_list)) as P12; rewrite H12 in P12;
         pose proof (AGh 13 ltac:(notin_list)) as P13; rewrite H13 in P13; pose proof (AGh 5 ltac:(notin_list)) as P5; rewrite H5 in P5;
         pose proof (AGh 7 ltac:(notin_list)) as P7; rewrite H7 in P7; pose proof (AGh 16 ltac:(notin_list)) as Pi16; rewrite H16 in Pi16;
         pose proof (AGh 15 ltac:(notin_list)) as P15; rewrite H15 in P15; pose proof (AGh 14 ltac:(notin_list)) as P14; rewrite H14 in P14;
         pose proof (AGh 1 ltac:(notin_list)) as P1; rewrite H1 in P1; pose proof (AGh 10 ltac:(notin_list)) as P10; rewrite H10 in P10;
         pose proof (AGh 17 ltac:(notin_list)) as P17; rewrite H17 in P17; pose proof (AGh 6 ltac:(notin_list)) as P6; rewrite H6 in P6.
    - (* [comment removed for export] *)
      destruct (c_eq (Z_to_bv 64 255) (Z_to_bv 64 (bv_unsigned b2))) eqn:Hc2;
        [destruct (c_eq (Z_to_bv 64 255) (Z_to_bv 64 (bv_unsigned b1))) eqn:Hc1;
           [destruct (c_eq (Z_to_bv 64 100) (Z_to_bv 64 (bv_unsigned b0))) eqn:Hc0 |] |].
      + (* [comment removed for export] *)
        eexists. eexists. split; [| split; [right; split; [| exists i; split; [lia | reflexivity]] |]].
        * eapply msteps_trans; [exact SH|].
          stepb_ft F_15e7c D_15e7c ltac:(pin; exact Hc2).
          stepLBU F_15e80 D_15e80 b1 ltac:(rdn_addr (arr + 1 + 4 * i)%Z; exact R1).
          stepb_ft F_15e84 D_15e84 ltac:(pin; exact Hc1).
          stepLBU F_15e88 D_15e88 b0 ltac:(rdn_addr (arr + 1 + 4 * i - 1)%Z; exact R0).
          stepb_ft F_15e8c D_15e8c ltac:(pin; exact Hc0).
          sn F_15e90 D_15e90.
          stepST F_15e94 D_15e94 (Z_to_bv 64 p) (Z_to_bv 64 i) ltac:(store_ok_peel; exact SOK).
          stepret F_15e98 D_15e98 ret ltac:(pin; reflexivity).
          apply mst_refl.
        * gres. reflexivity.
        * eapply regs_agree_trans; [regs_agree_weaken AGh|]. solve_regs_agree.
      + eexists. exists m. split; [| split; [left; split; [| reflexivity] |]].
        * eapply msteps_trans; [exact SH|].
          stepb_ft F_15e7c D_15e7c ltac:(pin; exact Hc2).
          stepLBU F_15e80 D_15e80 b1 ltac:(rdn_addr (arr + 1 + 4 * i)%Z; exact R1).
          stepb_ft F_15e84 D_15e84 ltac:(pin; exact Hc1).
          stepLBU F_15e88 D_15e88 b0 ltac:(rdn_addr (arr + 1 + 4 * i - 1)%Z; exact R0).
          stepb_tk F_15e8c D_15e8c ltac:(pin; exact Hc0).
          zva F_15e50 D_15e50 (Z_to_bv 64 (i + 1)). zva F_15e54 D_15e54 (Z_to_bv 64 (arr + 4 * (i + 1))). zva F_15e58 D_15e58 (Z_to_bv 64 (n - i - 1)). zva F_15e5c D_15e5c (Z_to_bv 64 (arr + 1 + 4 * (i + 1))).
          stepb_tk F_15e60 D_15e60 ltac:(condZ).
          stepret F_15ec8 D_15ec8 ret ltac:(pin; reflexivity).
          apply mst_refl.
        * gres. pin. reflexivity.
        * eapply regs_agree_trans; [regs_agree_weaken AGh|]. solve_regs_agree.
      + eexists. exists m. split; [| split; [left; split; [| reflexivity] |]].
        * eapply msteps_trans; [exact SH|].
          stepb_ft F_15e7c D_15e7c ltac:(pin; exact Hc2).
          stepLBU F_15e80 D_15e80 b1 ltac:(rdn_addr (arr + 1 + 4 * i)%Z; exact R1).
          stepb_tk F_15e84 D_15e84 ltac:(pin; exact Hc1).
          zva F_15e50 D_15e50 (Z_to_bv 64 (i + 1)). zva F_15e54 D_15e54 (Z_to_bv 64 (arr + 4 * (i + 1))). zva F_15e58 D_15e58 (Z_to_bv 64 (n - i - 1)). zva F_15e5c D_15e5c (Z_to_bv 64 (arr + 1 + 4 * (i + 1))).
          stepb_tk F_15e60 D_15e60 ltac:(condZ).
          stepret F_15ec8 D_15ec8 ret ltac:(pin; reflexivity).
          apply mst_refl.
        * gres. pin. reflexivity.
        * eapply regs_agree_trans; [regs_agree_weaken AGh|]. solve_regs_agree.
      + eexists. exists m. split; [| split; [left; split; [| reflexivity] |]].
        * eapply msteps_trans; [exact SH|].
          stepb_tk F_15e7c D_15e7c ltac:(pin; exact Hc2).
          zva F_15e50 D_15e50 (Z_to_bv 64 (i + 1)). zva F_15e54 D_15e54 (Z_to_bv 64 (arr + 4 * (i + 1))). zva F_15e58 D_15e58 (Z_to_bv 64 (n - i - 1)). zva F_15e5c D_15e5c (Z_to_bv 64 (arr + 1 + 4 * (i + 1))).
          stepb_tk F_15e60 D_15e60 ltac:(condZ).
          stepret F_15ec8 D_15ec8 ret ltac:(pin; reflexivity).
          apply mst_refl.
        * gres. pin. reflexivity.
        * eapply regs_agree_trans; [regs_agree_weaken AGh|]. solve_regs_agree.
    - (* [comment removed for export] *)
      assert (STEP : forall r1, getr r1 5 = Z_to_bv 64 (arr + 1 + 4 * (i + 1)) -> getr r1 7 = Z_to_bv 64 (arr + 4 * (i + 1)) ->
                getr r1 16 = Z_to_bv 64 (i + 1) -> getr r1 15 = Z_to_bv 64 (n - i - 1) ->
                getr r1 1 = ret -> regs_agree (fun r => In r [5; 7; 15; 16; 28]%list) regs r1 ->
                msteps SEGS (mkst regs (0x15f68 : word) m rom) (mkst r1 (0x15f68 : word) m rom) ->
                exists regs' m',
                  msteps SEGS (mkst regs (0x15f68 : word) m rom) (mkst regs' ret m' rom)
                  /\ ( (getr regs' 10 = Z_to_bv 64 1 /\ m' = m)
                       \/ (getr regs' 10 = Z_to_bv 64 0 /\ exists i', (0 <= i' < n)%Z /\ m' = wbytes m (Z_to_bv 64 p) (word_to_le_bytes 4 (Z_to_bv 64 i'))) )
                  /\ regs_agree (fun r => In r [5; 7; 10; 15; 16; 28]%list) regs regs').
      { intros r1 Q5 Q7 Q16 Q15 Q1 AG1 S1.
        destruct (IH r1 m arr p n (i + 1)%Z ret Harr Harr64 ltac:(lia) ltac:(lia) Hp Hp64 DEF SOK Q1 Hret
                    ltac:(rewrite (AG1 17) by notin_list; exact H17) Q5 ltac:(rewrite (AG1 6) by notin_list; exact H6) Q7 Q16 ltac:(rewrite Q15; f_equal; lia)
                    ltac:(rewrite (AG1 10) by notin_list; exact H10) ltac:(rewrite (AG1 14) by notin_list; exact H14)
                    ltac:(rewrite (AG1 11) by notin_list; exact H11) ltac:(rewrite (AG1 12) by notin_list; exact H12) ltac:(rewrite (AG1 13) by notin_list; exact H13))
          as (r2 & m2 & S2 & RES & AG2).
        exists r2, m2. split; [| split; [exact RES|]].
        - eapply msteps_trans; [exact S1|]. exact S2.
        - eapply regs_agree_trans; [regs_agree_weaken AG1 | exact AG2]. }
      destruct (c_eq (Z_to_bv 64 255) (Z_to_bv 64 (bv_unsigned b2))) eqn:Hc2;
        [destruct (c_eq (Z_to_bv 64 255) (Z_to_bv 64 (bv_unsigned b1))) eqn:Hc1;
           [destruct (c_eq (Z_to_bv 64 100) (Z_to_bv 64 (bv_unsigned b0))) eqn:Hc0 |] |].
      + (* [comment removed for export] *)
        eexists. eexists. split; [| split; [right; split; [| exists i; split; [lia | reflexivity]] |]].
        * eapply msteps_trans; [exact SH|].
          stepb_ft F_15e7c D_15e7c ltac:(pin; exact Hc2).
          stepLBU F_15e80 D_15e80 b1 ltac:(rdn_addr (arr + 1 + 4 * i)%Z; exact R1).
          stepb_ft F_15e84 D_15e84 ltac:(pin; exact Hc1).
          stepLBU F_15e88 D_15e88 b0 ltac:(rdn_addr (arr + 1 + 4 * i - 1)%Z; exact R0).
          stepb_ft F_15e8c D_15e8c ltac:(pin; exact Hc0).
          sn F_15e90 D_15e90.
          stepST F_15e94 D_15e94 (Z_to_bv 64 p) (Z_to_bv 64 i) ltac:(store_ok_peel; exact SOK).
          stepret F_15e98 D_15e98 ret ltac:(pin; reflexivity).
          apply mst_refl.
        * gres. reflexivity.
        * eapply regs_agree_trans; [regs_agree_weaken AGh|]. solve_regs_agree.
      + unshelve (eapply STEP; [ | | | | | | ]).
        8:{ eapply msteps_trans; [exact SH|].
            stepb_ft F_15e7c D_15e7c ltac:(pin; exact Hc2).
            stepLBU F_15e80 D_15e80 b1 ltac:(rdn_addr (arr + 1 + 4 * i)%Z; exact R1).
            stepb_ft F_15e84 D_15e84 ltac:(pin; exact Hc1).
            stepLBU F_15e88 D_15e88 b0 ltac:(rdn_addr (arr + 1 + 4 * i - 1)%Z; exact R0).
            stepb_tk F_15e8c D_15e8c ltac:(pin; exact Hc0).
            zva F_15e50 D_15e50 (Z_to_bv 64 (i + 1)). zva F_15e54 D_15e54 (Z_to_bv 64 (arr + 4 * (i + 1))). zva F_15e58 D_15e58 (Z_to_bv 64 (n - i - 1)). zva F_15e5c D_15e5c (Z_to_bv 64 (arr + 1 + 4 * (i + 1))).
            stepb_ft F_15e60 D_15e60 ltac:(condZ).
            apply mst_refl. }
        all: gres; pin; try reflexivity. eapply regs_agree_trans; [regs_agree_weaken AGh|]. solve_regs_agree.
      + unshelve (eapply STEP; [ | | | | | | ]).
        8:{ eapply msteps_trans; [exact SH|].
            stepb_ft F_15e7c D_15e7c ltac:(pin; exact Hc2).
            stepLBU F_15e80 D_15e80 b1 ltac:(rdn_addr (arr + 1 + 4 * i)%Z; exact R1).
            stepb_tk F_15e84 D_15e84 ltac:(pin; exact Hc1).
            zva F_15e50 D_15e50 (Z_to_bv 64 (i + 1)). zva F_15e54 D_15e54 (Z_to_bv 64 (arr + 4 * (i + 1))). zva F_15e58 D_15e58 (Z_to_bv 64 (n - i - 1)). zva F_15e5c D_15e5c (Z_to_bv 64 (arr + 1 + 4 * (i + 1))).
            stepb_ft F_15e60 D_15e60 ltac:(condZ).
            apply mst_refl. }
        all: gres; pin; try reflexivity. eapply regs_agree_trans; [regs_agree_weaken AGh|]. solve_regs_agree.
      + unshelve (eapply STEP; [ | | | | | | ]).
        8:{ eapply msteps_trans; [exact SH|].
            stepb_tk F_15e7c D_15e7c ltac:(pin; exact Hc2).
            zva F_15e50 D_15e50 (Z_to_bv 64 (i + 1)). zva F_15e54 D_15e54 (Z_to_bv 64 (arr + 4 * (i + 1))). zva F_15e58 D_15e58 (Z_to_bv 64 (n - i - 1)). zva F_15e5c D_15e5c (Z_to_bv 64 (arr + 1 + 4 * (i + 1))).
            stepb_ft F_15e60 D_15e60 ltac:(condZ).
            apply mst_refl. }
        all: gres; pin; try reflexivity. eapply regs_agree_trans; [regs_agree_weaken AGh|]. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma gi_W : forall regs m (cd p : Z) (cv : cmapv) (ret : word),
    (1 <= cd)%Z -> (cd mod 8 = 0)%Z -> CMAPat m cd cv -> (1 <= c_n cv)%Z -> (1 <= c_arr cv)%Z -> (c_arr cv + 4 * c_n cv < 2 ^ 64)%Z ->
    (1 <= p)%Z -> (p + 4 <= 2 ^ 64)%Z -> (p mod 4 = 0)%Z -> (cd + 24 <= p \/ p + 4 <= cd)%Z -> (c_arr cv + 4 * c_n cv <= p \/ p + 4 <= c_arr cv)%Z ->
    (forall a : word, (c_arr cv <= u a < c_arr cv + 4 * c_n cv)%Z -> m a <> None) ->
    store_ok SEGS m (Z_to_bv 64 p) 4 = true -> getr regs 1 = ret -> ret_ok ret ->
    getr regs 10 = Z_to_bv 64 cd -> getr regs 14 = Z_to_bv 64 p ->
    getr regs 11 = Z_to_bv 64 255 -> getr regs 12 = Z_to_bv 64 255 -> getr regs 13 = Z_to_bv 64 100 ->
    exists regs' m',
      msteps SEGS (mkst regs (0x15f10 : word) m rom) (mkst regs' ret m' rom)
      /\ ( (getr regs' 10 = Z_to_bv 64 1 /\ m' = wbytes m (Z_to_bv 64 p) (word_to_le_bytes 4 (Z_to_bv 64 0)))
           \/ (getr regs' 10 = Z_to_bv 64 0 /\ exists i', (0 <= i' < c_n cv)%Z /\
                 m' = wbytes (wbytes m (Z_to_bv 64 p) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 p) (word_to_le_bytes 4 (Z_to_bv 64 i'))) )
      /\ regs_agree (fun r => In r [5; 6; 7; 10; 15; 16; 17; 28]%list) regs regs'.
  Proof.
    intros regs m cd p cv ret Hcd ALc CM Hn Harr Harr64 Hp Hp64 ALp DJc DJa DEF SOK H1 Hret H10 H14 H11 H12 H13.
    pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_n _ CWF) as Rn. pose proof (cf_arr _ CWF) as Ra.
    set (m1 := wbytes m (Z_to_bv 64 p) (word_to_le_bytes 4 (Z_to_bv 64 0))).
    assert (CM1 : CMAPat m1 cd cv) by (subst m1; apply CMAPat_out; [exact CM | rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]).
    pose proof (CMAP_rd_n SEGS _ _ _ CM1) as Cn. pose proof (CMAP_rd_arr SEGS _ _ _ CM1) as Ca.
    assert (S1 : exists r1, msteps SEGS (mkst regs (0x15f10 : word) m rom) (mkst r1 (0x15f68 : word) m1 rom)
                            /\ getr r1 17 = Z_to_bv 64 (c_arr cv) /\ getr r1 5 = Z_to_bv 64 (c_arr cv + 1 + 4 * 0) /\ getr r1 6 = Z_to_bv 64 1
                            /\ getr r1 7 = Z_to_bv 64 (c_arr cv + 4 * 0) /\ getr r1 16 = Z_to_bv 64 0 /\ getr r1 15 = Z_to_bv 64 (c_n cv - 0)
                            /\ getr r1 10 = Z_to_bv 64 1 /\ getr r1 1 = ret
                            /\ regs_agree (fun r => In r [5; 6; 7; 10; 15; 16; 17]%list) regs r1).
    { eexists. split.
      - stepb_ft F_15e0c D_15e0c ltac:(condZ).
        guard4 F_15e10 D_15e10 ALp. stepb_ft F_15e14 D_15e14 ltac:(condZ).
        subst m1. stepST F_15e18 D_15e18 (Z_to_bv 64 p) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOK).
        stepb_ft F_15e1c D_15e1c ltac:(condZ).
        guard8 F_15e20 D_15e20 ALc. stepb_ft F_15e24 D_15e24 ltac:(condZ).
        sn F_15e28 D_15e28.
        stepLD F_15e2c D_15e2c (Z_to_le_bytes 4 (c_n cv)) (Z_to_bv 64 (c_n cv)) ltac:(addr_norm; exact Cn) ltac:(apply lez4; lia).
        rewrite (v_lw_small (c_n cv)) by lia.
        sn F_15e30 D_15e30.
        stepb_ft F_15e34 D_15e34 ltac:(condZ).
        sn F_15e38 D_15e38.
        stepLD F_15e3c D_15e3c (Z_to_le_bytes 8 (c_arr cv)) (Z_to_bv 64 (c_arr cv)) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Ca) ltac:(apply lez8; lia).
        zva F_15e40 D_15e40 (Z_to_bv 64 (c_arr cv + 1 + 4 * 0)).
        sn F_15e44 D_15e44. fixv (Z_to_bv 64 1) ltac:(apply zbv_snez; lia).
        zva F_15e48 D_15e48 (Z_to_bv 64 (c_arr cv + 4 * 0)).
        sn F_15e4c D_15e4c.
        apply mst_refl.
      - repeat split; gres; pin; try reflexivity; try (f_equal; lia). solve_regs_agree. }
    destruct S1 as (r1 & S1 & Q17 & Q5 & Q6 & Q7 & Q16 & Q15 & Q10 & Q1 & AG1).
    assert (DEF1 : forall a : word, (c_arr cv <= u a < c_arr cv + 4 * c_n cv)%Z -> m1 a <> None) by (intros a Ha; subst m1; apply wbytes_grows; exact (DEF a Ha)).
    assert (SOK1 : store_ok SEGS m1 (Z_to_bv 64 p) 4 = true).
    { subst m1. eapply store_ok_mono; [apply wbytes_grows | exact SOK]. }
    destruct (gi_loop (Z.to_nat (c_n cv - 1)) r1 m1 (c_arr cv) p (c_n cv) 0 ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hp Hp64 DEF1 SOK1 Q1 Hret Q17 Q5 Q6 Q7 Q16 Q15 Q10
                ltac:(rewrite (AG1 14) by notin_list; exact H14) ltac:(rewrite (AG1 11) by notin_list; exact H11)
                ltac:(rewrite (AG1 12) by notin_list; exact H12) ltac:(rewrite (AG1 13) by notin_list; exact H13))
      as (r2 & m2 & S2 & RES & AG2).
    exists r2, m2. split; [| split; [exact RES|]].
    - eapply msteps_trans; [exact S1|]. exact S2.
    - eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
  Qed.

  (* [comment removed for export] *)
  Lemma ac_ok : forall regs m (cd : Z) (cv : cmapv) (ret : word),
    (1 <= cd)%Z -> (cd mod 8 = 0)%Z -> CMAPat m cd cv -> (c_n cv < c_nalloc cv)%Z -> (1 <= c_arr cv)%Z -> (c_arr cv + 4 * c_nalloc cv < 2 ^ 64)%Z ->
    (cd + 24 <= c_arr cv \/ c_arr cv + 4 * c_nalloc cv <= cd)%Z ->
    store_ok SEGS m (Z_to_bv 64 (c_arr cv + 4 * c_n cv)) 4 = true -> store_ok SEGS m (Z_to_bv 64 cd) 24 = true ->
    getr regs 1 = ret -> ret_ok ret ->
    getr regs 10 = Z_to_bv 64 cd -> getr regs 11 = Z_to_bv 64 255 -> getr regs 12 = Z_to_bv 64 255 -> getr regs 13 = Z_to_bv 64 100 ->
    exists regs',
      msteps SEGS (mkst regs (0x15974 : word) m rom)
                  (mkst regs' ret
                     (wbytes (wbytes (wbytes (wbytes (wbytes m
                        (Z_to_bv 64 (c_arr cv + 4 * c_n cv + 2)) [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 255))])
                        (Z_to_bv 64 (c_arr cv + 4 * c_n cv)) [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 100))])
                        (Z_to_bv 64 (c_arr cv + 4 * c_n cv + 1)) [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 255))])
                        (Z_to_bv 64 (c_arr cv + 4 * c_n cv + 3)) [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 18446744073709551615))])
                        (Z_to_bv 64 (cd + 16)) (word_to_le_bytes 4 (Z_to_bv 64 (c_n cv + 1)))) rom)
      /\ getr regs' 10 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [5; 10; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m cd cv ret Hcd ALc CM Hn Harr Harr64 DJ SOKa SOKc H1 Hret H10 H11 H12 H13.
    pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_n _ CWF) as Rn. pose proof (cf_nalloc _ CWF) as Rna. pose proof (cf_arr _ CWF) as Ra.
    pose proof (CMAP_rd_n SEGS _ _ _ CM) as Cn. pose proof (CMAP_rd_nalloc SEGS _ _ _ CM) as Cna. pose proof (CMAP_rd_arr SEGS _ _ _ CM) as Ca.
    eexists. split.
    - stepb_ft F_15870 D_15870 ltac:(condZ).
      guard8 F_15874 D_15874 ALc. stepb_ft F_15878 D_15878 ltac:(condZ).
      stepLD F_1587c D_1587c (Z_to_le_bytes 4 (c_nalloc cv)) (Z_to_bv 64 (c_nalloc cv)) ltac:(addr_norm; exact Cna) ltac:(apply lez4; lia).
      rewrite (v_lw_small (c_nalloc cv)) by lia.
      stepLD F_15880 D_15880 (Z_to_le_bytes 4 (c_n cv)) (Z_to_bv 64 (c_n cv)) ltac:(addr_norm; exact Cn) ltac:(apply lez4; lia).
      rewrite (v_lw_small (c_n cv)) by lia.
      stepb_ft F_15884 D_15884 ltac:(condZ).
      stepLD F_15888 D_15888 (Z_to_le_bytes 8 (c_arr cv)) (Z_to_bv 64 (c_arr cv)) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Ca) ltac:(apply lez8; lia).
      zvs F_1588c D_1588c (Z_to_bv 64 (4 * c_n cv)).
      zva F_15890 D_15890 (Z_to_bv 64 (c_arr cv + 4 * c_n cv)).
      sn F_15894 D_15894. fixv (Z_to_bv 64 1) ltac:(apply zbv_snez; lia).
      seqz_nz F_15898 D_15898.
      stepb_ft F_1589c D_1589c ltac:(condZ).
      sn F_158a0 D_158a0. fixv (Z_to_bv 64 0) ltac:(apply zbv_sltu_ge; lia).
      sn F_158a4 D_158a4. fixv (Z_to_bv 64 0) ltac:(apply zbv_slti0; lia).
      litv F_158a8 D_158a8 (Z_to_bv 64 0).
      litv F_158ac D_158ac (Z_to_bv 64 1).
      stepb_ft F_158b0 D_158b0 ltac:(condZ).
      stepb_ft F_158b4 D_158b4 ltac:(condZ).
      stepST F_158b8 D_158b8 (Z_to_bv 64 (c_arr cv + 4 * c_n cv + 2)) (Z_to_bv 64 255) ltac:(sok_in SOKa).
      stepb_ft F_158bc D_158bc ltac:(condZ).
      sn F_158c0 D_158c0.
      zva F_158c4 D_158c4 (Z_to_bv 64 (c_n cv + 1)).
      stepST F_158c8 D_158c8 (Z_to_bv 64 (c_arr cv + 4 * c_n cv)) (Z_to_bv 64 100) ltac:(sok_in SOKa).
      stepST F_158cc D_158cc (Z_to_bv 64 (c_arr cv + 4 * c_n cv + 1)) (Z_to_bv 64 255) ltac:(sok_in SOKa).
      stepST F_158d0 D_158d0 (Z_to_bv 64 (c_arr cv + 4 * c_n cv + 3)) (Z_to_bv 64 18446744073709551615) ltac:(sok_in SOKa).
      stepST F_158d4 D_158d4 (Z_to_bv 64 (cd + 16)) (Z_to_bv 64 (c_n cv + 1)) ltac:(sok_in SOKc).
      sn F_158d8 D_158d8.
      stepret F_158dc D_158dc ret ltac:(pin; reflexivity).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ac_full : forall regs m (cd : Z) (cv : cmapv),
    (1 <= cd)%Z -> (cd mod 8 = 0)%Z -> CMAPat m cd cv -> (c_nalloc cv <= c_n cv)%Z ->
    rdn SEGS m (Z_to_bv 64 0x20e58) 8 = Some (Z_to_le_bytes 8 0x21ec8) -> rdn SEGS m (Z_to_bv 64 0x21ec8) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 cd ->
    exists regs',
      msteps SEGS (mkst regs (0x15974 : word) m rom) (mkst regs' (0x13e3c : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x10b69 /\ getr regs' 11 = Z_to_bv 64 0x10abb /\ getr regs' 12 = Z_to_bv 64 1
      /\ getr regs' 1 = getr regs 1 /\ getr regs' 2 = getr regs 2
      /\ regs_agree (fun r => In r [10; 11; 12; 14; 15]%list) regs regs'.
  Proof.
    intros regs m cd cv Hcd ALc CM Hn Rg Rs H10.
    pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_n _ CWF) as Rn. pose proof (cf_nalloc _ CWF) as Rna.
    pose proof (CMAP_rd_n SEGS _ _ _ CM) as Cn. pose proof (CMAP_rd_nalloc SEGS _ _ _ CM) as Cna.
    eexists. split.
    - stepb_ft F_15870 D_15870 ltac:(condZ).
      guard8 F_15874 D_15874 ALc. stepb_ft F_15878 D_15878 ltac:(condZ).
      stepLD F_1587c D_1587c (Z_to_le_bytes 4 (c_nalloc cv)) (Z_to_bv 64 (c_nalloc cv)) ltac:(addr_norm; exact Cna) ltac:(apply lez4; lia).
      rewrite (v_lw_small (c_nalloc cv)) by lia.
      stepLD F_15880 D_15880 (Z_to_le_bytes 4 (c_n cv)) (Z_to_bv 64 (c_n cv)) ltac:(addr_norm; exact Cn) ltac:(apply lez4; lia).
      rewrite (v_lw_small (c_n cv)) by lia.
      stepb_tk F_15884 D_15884 ltac:(condZ).
      sn F_1590c D_1590c.
      stepLD F_15910 D_15910 (Z_to_le_bytes 8 0x21ec8) (Z_to_bv 64 0x21ec8) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_15914 D_15914 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rs) ltac:(apply lez4; lia).
      sn F_15918 D_15918. stepb_ft F_1591c D_1591c ltac:(condZ).
      sn F_15920 D_15920. sn F_15924 D_15924. sn F_15928 D_15928. sn F_1592c D_1592c. sn F_15930 D_15930. sn F_15934 D_15934.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_C0 : forall regs m,
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x16958 : word) m rom) (mkst regs' (0x16a7c : word) m rom)
      /\ regs_agree (fun r => In r []%list) regs regs'.
  Proof.
    intros regs m H10. eexists. split.
    - stepb_tk F_16854 D_16854 ltac:(condZ). apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_C1 : forall regs m (cd : Z),
    getr regs 10 = Z_to_bv 64 1 -> getr regs 23 = Z_to_bv 64 cd ->
    getr regs 20 = Z_to_bv 64 100 -> getr regs 21 = Z_to_bv 64 255 -> getr regs 22 = Z_to_bv 64 255 ->
    exists regs', msteps SEGS (mkst regs (0x16958 : word) m rom) (mkst regs' (0x15974 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x16970 /\ getr regs' 10 = Z_to_bv 64 cd /\ getr regs' 11 = Z_to_bv 64 255 /\ getr regs' 12 = Z_to_bv 64 255 /\ getr regs' 13 = Z_to_bv 64 100
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m cd H10 H23 H20 H21 H22. eexists. split.
    - stepb_ft F_16854 D_16854 ltac:(condZ).
      sn F_16858 D_16858. sn F_1685c D_1685c. sn F_16860 D_16860. sn F_16864 D_16864. sn F_16868 D_16868.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_D0 : forall regs m (s n : Z),
    (144 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= n < 2 ^ 31)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 144)) 144 = true ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 10 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 n ->
    exists regs', msteps SEGS (mkst regs (0x16970 : word) m rom) (mkst regs' (0x16a7c : word) (wbytes m (Z_to_bv 64 (s - 132)) (word_to_le_bytes 4 (Z_to_bv 64 n))) rom)
      /\ regs_agree (fun r => In r []%list) regs regs'.
  Proof.
    intros regs m s n Hs Hs64 Hn SOK H2 H10 H24. eexists. split.
    - stepb_tk F_1686c D_1686c ltac:(condZ).
      stepST F_16974 D_16974 (Z_to_bv 64 (s - 132)) (Z_to_bv 64 n) ltac:(sok_in SOK).
      apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_D1 : forall regs m (s : Z),
    rdn SEGS m (Z_to_bv 64 0x20e58) 8 = Some (Z_to_le_bytes 8 0x21ec8) -> rdn SEGS m (Z_to_bv 64 0x21ec8) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 10 = Z_to_bv 64 1 ->
    exists regs', msteps SEGS (mkst regs (0x16970 : word) m rom) (mkst regs' (0x13e3c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 144) /\ getr regs' 1 = Z_to_bv 64 0x16d5c
      /\ getr regs' 10 = Z_to_bv 64 0x10c63 /\ getr regs' 11 = Z_to_bv 64 0x10d41 /\ getr regs' 12 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s Rg Rs H2 H10. eexists. split.
    - stepb_ft F_1686c D_1686c ltac:(condZ).
      sn F_16870 D_16870.
      stepLD F_16874 D_16874 (Z_to_le_bytes 8 0x21ec8) (Z_to_bv 64 0x21ec8) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_16878 D_16878 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_1687c D_1687c. stepb_ft F_16880 D_16880 ltac:(condZ).
      sn F_16884 D_16884. sn F_16888 D_16888. sn F_1688c D_1688c. sn F_16890 D_16890. sn F_16894 D_16894.
      sn F_16c50 D_16c50. sn F_16c54 D_16c54.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_J : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x16d5c : word) m rom) (mkst regs' (0x16d64 : word) m rom)
      /\ regs_agree (fun r => In r []%list) regs regs'.
  Proof. intros regs m. eexists. split; [sn F_16c58 D_16c58; apply mst_refl | solve_regs_agree]. Qed.

  (* [comment removed for export] *)
  Lemma ss_dims : forall regs m (s pixd : Z) (vd : pixv),
    (144 <= s)%Z -> (s < 2 ^ 64)%Z -> (s mod 16 = 0)%Z -> (1 <= pixd)%Z -> (pixd mod 16 = 0)%Z -> PIXat m pixd vd -> (pixd + 64 <= s - 144)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 144)) 144 = true ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 19 = Z_to_bv 64 pixd ->
    exists regs', msteps SEGS (mkst regs (0x16a7c : word) m rom)
      (mkst regs' (0x16a90 : word)
         (wbytes (wbytes (wbytes (wbytes m
            (Z_to_bv 64 (s - 108)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
            (Z_to_bv 64 (s - 112)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
            (Z_to_bv 64 (s - 108)) (word_to_le_bytes 4 (Z_to_bv 64 (p_w vd))))
            (Z_to_bv 64 (s - 112)) (word_to_le_bytes 4 (Z_to_bv 64 (p_h vd)))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 144) /\ getr regs' 19 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd vd Hs Hs64 Hs16 Hp ALp PX DJ SOK H2 H19. pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_w _ WF) as Rw. pose proof (wf_h _ WF) as Rh.
    pose proof (PIX_rd_w SEGS _ _ _ PX) as Cw. pose proof (PIX_rd_h SEGS _ _ _ PX) as Ch.
    assert (ALw : ((s - 108) mod 4 = 0)%Z) by (apply sp_slot_al4'; [exact Hs16 | reflexivity]).
    assert (ALh : ((s - 112) mod 4 = 0)%Z) by (apply sp_slot_al4'; [exact Hs16 | reflexivity]).
    assert (AL0 : (0 mod 4 = 0)%Z) by reflexivity.
    assert (ALp8 : (pixd mod 8 = 0)%Z) by (apply al16_mod8; exact ALp).
    eexists. split.
    - zv F_16978 D_16978 (Z_to_bv 64 (s - 108)). zv F_1697c D_1697c (Z_to_bv 64 (s - 112)). sn F_16980 D_16980. sn F_16984 D_16984.
      sn F_16988 D_16988.
      guard4 F_14ae4 D_14ae4 ALw.                                                  (* [comment removed for export] *)
      stepb_ft F_14ae8 D_14ae8 ltac:(condZ). stepb_ft F_14aec D_14aec ltac:(condZ).
      stepST F_14af0 D_14af0 (Z_to_bv 64 (s - 108)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      guard4 F_14af4 D_14af4 ALh.                                                  (* [comment removed for export] *)
      stepb_ft F_14af8 D_14af8 ltac:(condZ). stepb_ft F_14afc D_14afc ltac:(condZ).
      stepST F_14b00 D_14b00 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      guard4 F_14b04 D_14b04 AL0.                                                  (* [comment removed for export] *)
      stepb_tk F_14b08 D_14b08 ltac:(condZ).                                      (* [comment removed for export] *)
      stepb_ft F_14b14 D_14b14 ltac:(condZ).
      guard8 F_14b18 D_14b18 ALp8.                                                 (* [comment removed for export] *)
      stepb_ft F_14b1c D_14b1c ltac:(condZ).
      litv F_14b20 D_14b20 (Z_to_bv 64 0).                                        (* [comment removed for export] *)
      stepb_ft F_14b24 D_14b24 ltac:(condZ).
      stepLD F_14b28 D_14b28 (Z_to_le_bytes 4 (p_w vd)) (Z_to_bv 64 (p_w vd)) ltac:(addr_norm; rewrite ?Z.add_0_r; repeat rdn_peel1; exact Cw) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_w vd)) by lia.
      stepST F_14b2c D_14b2c (Z_to_bv 64 (s - 108)) (Z_to_bv 64 (p_w vd)) ltac:(sok_in SOK).
      stepb_ft F_14b30 D_14b30 ltac:(condZ).
      litv F_14b34 D_14b34 (Z_to_bv 64 0).                                        (* [comment removed for export] *)
      stepb_ft F_14b38 D_14b38 ltac:(condZ).
      stepLD F_14b3c D_14b3c (Z_to_le_bytes 4 (p_h vd)) (Z_to_bv 64 (p_h vd)) ltac:(addr_norm; repeat rdn_peel1; exact Ch) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_h vd)) by lia.
      stepST F_14b40 D_14b40 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 (p_h vd)) ltac:(sok_in SOK).
      stepb_tk F_14b44 D_14b44 ltac:(condZ).
      sn F_14b8c D_14b8c.
      stepret F_14b90 D_14b90 (0x16a90 : word) ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_F : forall regs m (s bx : Z),
    (144 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= bx)%Z -> (bx < 2 ^ 64)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 18 = Z_to_bv 64 bx ->
    exists regs', msteps SEGS (mkst regs (0x16a90 : word) m rom) (mkst regs' (0x14364 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x16aac /\ getr regs' 10 = Z_to_bv 64 bx
      /\ getr regs' 11 = Z_to_bv 64 (s - 116) /\ getr regs' 12 = Z_to_bv 64 (s - 120) /\ getr regs' 13 = Z_to_bv 64 (s - 124) /\ getr regs' 14 = Z_to_bv 64 (s - 128)
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m s bx Hs Hs64 Hbx Hbx64 H2 H18. eexists. split.
    - stepb_ft F_1698c D_1698c ltac:(condZ).
      zv F_16990 D_16990 (Z_to_bv 64 (s - 116)). zv F_16994 D_16994 (Z_to_bv 64 (s - 120)). zv F_16998 D_16998 (Z_to_bv 64 (s - 124)). zv F_1699c D_1699c (Z_to_bv 64 (s - 128)).
      sn F_169a0 D_169a0. sn F_169a4 D_169a4.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_G : forall regs m (s pixd x1 y1 bw bh : Z) (vd : pixv),
    (144 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixd)%Z -> (pixd mod 16 = 0)%Z -> PIXat m pixd vd ->
    (0 <= x1)%Z -> (0 <= y1)%Z -> (1 <= bw)%Z -> (1 <= bh)%Z -> (x1 + bw < 2 ^ 31)%Z -> (y1 + bh < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 116)) 4 = Some (Z_to_le_bytes 4 x1) -> rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some (Z_to_le_bytes 4 y1) ->
    rdn SEGS m (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 bw) -> rdn SEGS m (Z_to_bv 64 (s - 128)) 4 = Some (Z_to_le_bytes 4 bh) ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 19 = Z_to_bv 64 pixd ->
    exists regs', msteps SEGS (mkst regs (0x16aac : word) m rom) (mkst regs' (0x16b14 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 144) /\ getr regs' 10 = Z_to_bv 64 (p_wpl vd) /\ getr regs' 18 = Z_to_bv 64 (p_data vd)
      /\ getr regs' 20 = Z_to_bv 64 (x1 + bw - 1) /\ getr regs' 21 = Z_to_bv 64 (y1 + bh - 1) /\ getr regs' 19 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 18; 20; 21]%list) regs regs'.
  Proof.
    intros regs m s pixd x1 y1 bw bh vd Hs Hs64 Hp ALp PX Hx1 Hy1 Hbw Hbh Hx Hy Rx1 Ry1 Rbw Rbh H2 H19.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_wpl _ WF) as Rw. pose proof (wf_data _ WF) as Rd.
    assert (ALp8 : (pixd mod 8 = 0)%Z) by (apply al16_mod8; exact ALp).
    pose proof (PIX_rd_wpl SEGS _ _ _ PX) as Cwpl. pose proof (PIX_rd_data SEGS _ _ _ PX) as Cdata.
    eexists. split.
    - stepLD F_169a8 D_169a8 (Z_to_le_bytes 4 x1) (Z_to_bv 64 x1) ltac:(addr_norm; exact Rx1) ltac:(apply lez4; lia). rewrite (v_lw_small x1) by lia.
      stepLD F_169ac D_169ac (Z_to_le_bytes 4 bw) (Z_to_bv 64 bw) ltac:(addr_norm; exact Rbw) ltac:(apply lez4; lia). rewrite (v_lw_small bw) by lia.
      zva F_169b0 D_169b0 (Z_to_bv 64 (x1 + bw)).                                                     (* [comment removed for export] *)
      sn F_169b4 D_169b4. fixv (Z_to_bv 64 (x1 + bw)) ltac:(rewrite v_addw_Z, sw32_small by lia; reflexivity).   (* [comment removed for export] *)
      stepb_ft F_169b8 D_169b8 ltac:(condZ).                                                          (* [comment removed for export] *)
      sn F_169bc D_169bc. fixv (Z_to_bv 64 (x1 + bw - 1)) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia).   (* [comment removed for export] *)
      sn F_169c0 D_169c0. fixv (Z_to_bv 64 (x1 + bw)) ltac:(rewrite v_addiw_Z, Z.add_0_r, sw32_small by lia; reflexivity).   (* [comment removed for export] *)
      stepb_ft F_169c4 D_169c4 ltac:(condZ).                                                          (* [comment removed for export] *)
      stepLD F_169c8 D_169c8 (Z_to_le_bytes 4 y1) (Z_to_bv 64 y1) ltac:(addr_norm; exact Ry1) ltac:(apply lez4; lia). rewrite (v_lw_small y1) by lia.
      stepLD F_169cc D_169cc (Z_to_le_bytes 4 bh) (Z_to_bv 64 bh) ltac:(addr_norm; exact Rbh) ltac:(apply lez4; lia). rewrite (v_lw_small bh) by lia.
      zva F_169d0 D_169d0 (Z_to_bv 64 (y1 + bh)).                                                     (* [comment removed for export] *)
      sn F_169d4 D_169d4. fixv (Z_to_bv 64 (y1 + bh)) ltac:(rewrite v_addw_Z, sw32_small by lia; reflexivity).   (* [comment removed for export] *)
      stepb_ft F_169d8 D_169d8 ltac:(condZ).                                                          (* [comment removed for export] *)
      sn F_169dc D_169dc. fixv (Z_to_bv 64 (y1 + bh)) ltac:(rewrite v_addiw_Z, Z.add_0_r, sw32_small by lia; reflexivity).   (* [comment removed for export] *)
      sn F_169e0 D_169e0. fixv (Z_to_bv 64 (y1 + bh - 1)) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia).   (* [comment removed for export] *)
      stepb_tk F_169e4 D_169e4 ltac:(condZ).                                                          (* [comment removed for export] *)
      sn F_169fc D_169fc. sn F_16a00 D_16a00.
      stepb_ft F_1559c D_1559c ltac:(condZ).
      guard8 F_155a0 D_155a0 ALp8. stepb_ft F_155a4 D_155a4 ltac:(condZ).
      stepLD F_155a8 D_155a8 (Z_to_le_bytes 8 (p_data vd)) (Z_to_bv 64 (p_data vd)) ltac:(addr_norm; exact Cdata) ltac:(apply lez8; lia).
      stepret F_155ac D_155ac (0x16b08 : word) ltac:(bveq).
      sn F_16a04 D_16a04. sn F_16a08 D_16a08. sn F_16a0c D_16a0c.
      stepb_ft F_1485c D_1485c ltac:(condZ).
      guard8 F_14860 D_14860 ALp8. stepb_ft F_14864 D_14864 ltac:(condZ).
      stepLD F_14868 D_14868 (Z_to_le_bytes 4 (p_wpl vd)) (Z_to_bv 64 (p_wpl vd)) ltac:(addr_norm; exact Cwpl) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_wpl vd)) by lia.
      stepret F_1486c D_1486c (0x16b14 : word) ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_F0 : forall regs m (s pixd w h : Z) (vd : pixv),
    (144 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixd)%Z -> (pixd mod 16 = 0)%Z -> PIXat m pixd vd -> (pixd + 64 <= s - 144)%Z -> (0 <= w < 2 ^ 31)%Z -> (0 <= h < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) -> rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h) ->
    store_ok SEGS m (Z_to_bv 64 (s - 144)) 144 = true ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 18 = Z_to_bv 64 0 -> getr regs 19 = Z_to_bv 64 pixd ->
    exists regs', msteps SEGS (mkst regs (0x16a90 : word) m rom)
      (mkst regs' (0x16b14 : word)
         (wbytes (wbytes m (Z_to_bv 64 (s - 120)) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 (s - 116)) (word_to_le_bytes 4 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 144) /\ getr regs' 10 = Z_to_bv 64 (p_wpl vd) /\ getr regs' 18 = Z_to_bv 64 (p_data vd)
      /\ getr regs' 20 = Z_to_bv 64 w /\ getr regs' 21 = Z_to_bv 64 h /\ getr regs' 19 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 10; 11; 18; 20; 21]%list) regs regs'.
  Proof.
    intros regs m s pixd w h vd Hs Hs64 Hp ALp PX DJ Hw Hh Rw Rh SOK H2 H18 H19.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_wpl _ WF) as Rwpl. pose proof (wf_data _ WF) as Rd.
    assert (ALp8 : (pixd mod 8 = 0)%Z) by (apply al16_mod8; exact ALp).
    pose proof (PIX_rd_wpl SEGS _ _ _ PX) as Cwpl. pose proof (PIX_rd_data SEGS _ _ _ PX) as Cdata.
    eexists. split.
    - stepb_tk F_1698c D_1698c ltac:(condZ).
      stepLD F_169ec D_169ec (Z_to_le_bytes 4 w) (Z_to_bv 64 w) ltac:(addr_norm; exact Rw) ltac:(apply lez4; lia). rewrite (v_lw_small w) by lia.
      stepLD F_169f0 D_169f0 (Z_to_le_bytes 4 h) (Z_to_bv 64 h) ltac:(addr_norm; exact Rh) ltac:(apply lez4; lia). rewrite (v_lw_small h) by lia.
      stepST F_169f4 D_169f4 (Z_to_bv 64 (s - 120)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepST F_169f8 D_169f8 (Z_to_bv 64 (s - 116)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_169fc D_169fc. sn F_16a00 D_16a00.
      stepb_ft F_1559c D_1559c ltac:(condZ).
      guard8 F_155a0 D_155a0 ALp8. stepb_ft F_155a4 D_155a4 ltac:(condZ).
      stepLD F_155a8 D_155a8 (Z_to_le_bytes 8 (p_data vd)) (Z_to_bv 64 (p_data vd)) ltac:(addr_norm; repeat rdn_peel1; exact Cdata) ltac:(apply lez8; lia).
      stepret F_155ac D_155ac (0x16b08 : word) ltac:(bveq).
      sn F_16a04 D_16a04. sn F_16a08 D_16a08. sn F_16a0c D_16a0c.
      stepb_ft F_1485c D_1485c ltac:(condZ).
      guard8 F_14860 D_14860 ALp8. stepb_ft F_14864 D_14864 ltac:(condZ).
      stepLD F_14868 D_14868 (Z_to_le_bytes 4 (p_wpl vd)) (Z_to_bv 64 (p_wpl vd)) ltac:(addr_norm; repeat rdn_peel1; exact Cwpl) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_wpl vd)) by lia.
      stepret F_1486c D_1486c (0x16b14 : word) ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.
End SelSegs.
