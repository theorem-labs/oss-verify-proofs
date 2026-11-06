(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.paintcmap_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.O21 Require Import O21LeptStderr O21LeptBase.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.O21 Require Import O21CL7a.
Import O21CL7a.O21LeptErr.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.O21 Require Import O21LeptPixCopy O21LeptSelSegs O21_code_1364c_14000 O21_code_15000_16000 O21_code_16000_17000.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Lemma str_pixSetSelectMaskedCmap : str16 0x10a26 22. Proof. str16_tac. Qed.
Lemma str_no_mask : str16 0x10388 38. Proof. str16_tac. Qed.
Lemma str_pixs_not_defined' : str16 0x10298 16. Proof. str16_tac. Qed.
Lemma str_no_colormap' : str16 0x108f0 11. Proof. str16_tac. Qed.

Section SelMasked.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL21} {P16 : O21Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

  (* [comment removed for export] *)
  Definition FR13m (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
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

  Lemma cells_FR13m : forall m s ret regs, (144 <= s)%Z -> (s < 2 ^ 64)%Z -> cellsZ (FR13m m s ret regs) (frame13 s ret (svr13 regs)).
  Proof. intros m s ret regs Hs Hs64. unfold frame13, FR13m, svr13. cbn [cellsZ]. repeat split; rdn_solve. Qed.

Section Segs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma sm_P : forall regs m (s : Z) (ret : word),
    (144 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 144)) 144 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret ->
    exists regs',
      msteps SEGS (mkst regs (0x165a4 : word) m rom) (mkst regs' (0x165dc : word) (FR13m m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 144) /\ getr regs' 1 = ret
      /\ regs_agree (fun r => In r [2]%list) regs regs'.
  Proof.
    intros regs m s ret Hs Hs64 SOK H2 H1. unfold FR13m. eexists. split.
    - zv F_164a0 D_164a0 (Z_to_bv 64 (s - 144)).
      stepST F_164a4 D_164a4 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_164a8 D_164a8 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_164ac D_164ac (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_164b0 D_164b0 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_164b4 D_164b4 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_164b8 D_164b8 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_164bc D_164bc (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_164c0 D_164c0 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      stepST F_164c4 D_164c4 (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
      stepST F_164c8 D_164c8 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
      stepST F_164cc D_164cc (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).
      stepST F_164d0 D_164d0 (Z_to_bv 64 (s - 96)) (getr regs 26) ltac:(sok_in SOK).
      stepST F_164d4 D_164d4 (Z_to_bv 64 (s - 104)) (getr regs 27) ltac:(sok_in SOK).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sm_etail : forall regs m (s : Z) (ret : word) (sv : nat -> word) (msg : Z),
    (144 <= s)%Z -> (s < 2 ^ 64)%Z -> cellsZ m (frame13 s ret sv) ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 10 = Z_to_bv 64 msg -> getr regs 11 = Z_to_bv 64 0x10a26 ->
    exists regs',
      msteps SEGS (mkst regs (0x1676c : word) m rom) (mkst regs' (0x13db4 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 msg /\ getr regs' 11 = Z_to_bv 64 0x10a26 /\ getr regs' 12 = Z_to_bv 64 1
      /\ getr regs' 8 = sv 8%nat /\ getr regs' 9 = sv 9%nat /\ getr regs' 18 = sv 18%nat /\ getr regs' 19 = sv 19%nat /\ getr regs' 20 = sv 20%nat
      /\ getr regs' 21 = sv 21%nat /\ getr regs' 22 = sv 22%nat /\ getr regs' 23 = sv 23%nat /\ getr regs' 24 = sv 24%nat /\ getr regs' 25 = sv 25%nat
      /\ getr regs' 26 = sv 26%nat /\ getr regs' 27 = sv 27%nat
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 12; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m s ret sv msg Hs Hs64 CE H2 H10 H11. unfold frame13 in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & _).
    eexists. split.
    - sn F_16668 D_16668.
      stepLD8 F_1666c D_1666c ret. stepLD8 F_16670 D_16670 (sv 8%nat). stepLD8 F_16674 D_16674 (sv 9%nat).
      stepLD8 F_16678 D_16678 (sv 18%nat). stepLD8 F_1667c D_1667c (sv 19%nat). stepLD8 F_16680 D_16680 (sv 20%nat).
      stepLD8 F_16684 D_16684 (sv 21%nat). stepLD8 F_16688 D_16688 (sv 22%nat). stepLD8 F_1668c D_1668c (sv 23%nat).
      stepLD8 F_16690 D_16690 (sv 24%nat). stepLD8 F_16694 D_16694 (sv 25%nat). stepLD8 F_16698 D_16698 (sv 26%nat).
      stepLD8 F_1669c D_1669c (sv 27%nat).
      zv F_166a0 D_166a0 (Z_to_bv 64 s). sn F_166a4 D_166a4.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sm_A0 : forall regs m (s : Z),
    rdn SEGS m (Z_to_bv 64 0x20520) 8 = Some (Z_to_le_bytes 8 0x21590) -> rdn SEGS m (Z_to_bv 64 0x21590) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x165dc : word) m rom) (mkst regs' (0x1676c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 144) /\ getr regs' 10 = Z_to_bv 64 0x10298 /\ getr regs' 11 = Z_to_bv 64 0x10a26
      /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
  Proof.
    intros regs m s Rg Rs H2 H10. eexists. split.
    - stepb_tk F_164d8 D_164d8 ltac:(condZ).
      sn F_1659c D_1659c.
      stepLD F_165a0 D_165a0 (Z_to_le_bytes 8 0x21590) (Z_to_bv 64 0x21590) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_165a4 D_165a4 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_165a8 D_165a8. stepb_ft F_165ac D_165ac ltac:(condZ).
      sn F_165b0 D_165b0. sn F_165b4 D_165b4. sn F_165b8 D_165b8. sn F_165bc D_165bc. sn F_165c0 D_165c0.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sm_A : forall regs m (pixd : Z) (vd : pixv),
    (1 <= pixd)%Z -> PIXat m pixd vd ->
    getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x165dc : word) m rom) (mkst regs' (0x16604 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (p_cmap vd) /\ getr regs' 23 = Z_to_bv 64 0 /\ getr regs' 2 = getr regs 2
      /\ regs_agree (fun r => In r [1; 8; 10; 18; 19; 20; 21; 23; 24; 25]%list) regs regs'.
  Proof.
    intros regs m pixd vd Hp PX H10 H11. pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_cmap _ WF) as Rc.
    pose proof (PIX_rd_cmap SEGS _ _ _ PX) as Cc.
    eexists. split.
    - stepb_ft F_164d8 D_164d8 ltac:(condZ).
      sn F_164dc D_164dc. sn F_164e0 D_164e0. sn F_164e4 D_164e4. sn F_164e8 D_164e8. sn F_164ec D_164ec. sn F_164f0 D_164f0. sn F_164f4 D_164f4. sn F_164f8 D_164f8.
      sn F_164fc D_164fc.
      stepb_ft F_151ac D_151ac ltac:(condZ).
      stepLD F_151b0 D_151b0 (Z_to_le_bytes 8 (p_cmap vd)) (Z_to_bv 64 (p_cmap vd)) ltac:(addr_norm; exact Cc) ltac:(apply lez8; lia).
      stepret F_151b4 D_151b4 (0x16604 : word) ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sm_B0 : forall regs m (s : Z),
    rdn SEGS m (Z_to_bv 64 0x20520) 8 = Some (Z_to_le_bytes 8 0x21590) -> rdn SEGS m (Z_to_bv 64 0x21590) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x16604 : word) m rom) (mkst regs' (0x1676c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 144) /\ getr regs' 10 = Z_to_bv 64 0x108f0 /\ getr regs' 11 = Z_to_bv 64 0x10a26
      /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
  Proof.
    intros regs m s Rg Rs H2 H10. eexists. split.
    - stepb_tk F_16500 D_16500 ltac:(condZ).
      sn F_165c4 D_165c4.
      stepLD F_165c8 D_165c8 (Z_to_le_bytes 8 0x21590) (Z_to_bv 64 0x21590) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_165cc D_165cc (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_165d0 D_165d0. stepb_ft F_165d4 D_165d4 ltac:(condZ).
      sn F_165d8 D_165d8. sn F_165dc D_165dc. sn F_165e0 D_165e0. sn F_165e4 D_165e4. sn F_165e8 D_165e8.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sm_B : forall regs m (s cd : Z),
    (1 <= cd)%Z -> (cd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 0x20520) 8 = Some (Z_to_le_bytes 8 0x21590) -> rdn SEGS m (Z_to_bv 64 0x21590) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 10 = Z_to_bv 64 cd -> getr regs 23 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x16604 : word) m rom) (mkst regs' (0x13de8 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 144) /\ getr regs' 1 = Z_to_bv 64 0x16718 /\ getr regs' 10 = Z_to_bv 64 0x10388 /\ getr regs' 11 = Z_to_bv 64 0x10a26
      /\ regs_agree (fun r => In r [1; 10; 11; 22]%list) regs regs'.
  Proof.
    intros regs m s cd Hcd Hcd64 Rg Rs H2 H10 H23. eexists. split.
    - stepb_ft F_16500 D_16500 ltac:(condZ).
      stepb_tk F_16504 D_16504 ltac:(condZ).
      sn F_165ec D_165ec.
      stepLD F_165f0 D_165f0 (Z_to_le_bytes 8 0x21590) (Z_to_bv 64 0x21590) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_165f4 D_165f4 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_165f8 D_165f8. stepb_ft F_165fc D_165fc ltac:(condZ).
      sn F_16600 D_16600. sn F_16604 D_16604. sn F_16608 D_16608. sn F_1660c D_1660c. sn F_16610 D_16610.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sm_C : forall regs m (s : Z) (ret : word) (sv : nat -> word),
    (144 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cellsZ m (frame13 s ret sv) ->
    getr regs 2 = Z_to_bv 64 (s - 144) ->
    exists regs',
      msteps SEGS (mkst regs (0x16718 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 8 = sv 8%nat /\ getr regs' 9 = sv 9%nat /\ getr regs' 18 = sv 18%nat /\ getr regs' 19 = sv 19%nat /\ getr regs' 20 = sv 20%nat
      /\ getr regs' 21 = sv 21%nat /\ getr regs' 22 = sv 22%nat /\ getr regs' 23 = sv 23%nat /\ getr regs' 24 = sv 24%nat /\ getr regs' 25 = sv 25%nat
      /\ getr regs' 26 = sv 26%nat /\ getr regs' 27 = sv 27%nat
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m s ret sv Hs Hs64 Hret CE H2. unfold frame13 in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & _).
    eexists. split.
    - sn F_16614 D_16614. sn F_16618 D_16618. sn F_168e8 D_168e8.
      stepLD8 F_168ec D_168ec ret. stepLD8 F_168f0 D_168f0 (sv 8%nat). stepLD8 F_168f4 D_168f4 (sv 9%nat).
      stepLD8 F_168f8 D_168f8 (sv 18%nat). stepLD8 F_168fc D_168fc (sv 19%nat). stepLD8 F_16900 D_16900 (sv 20%nat).
      stepLD8 F_16904 D_16904 (sv 21%nat). stepLD8 F_16908 D_16908 (sv 22%nat). stepLD8 F_1690c D_1690c (sv 23%nat).
      stepLD8 F_16910 D_16910 (sv 24%nat). stepLD8 F_16914 D_16914 (sv 25%nat). stepLD8 F_16918 D_16918 (sv 26%nat).
      stepLD8 F_1691c D_1691c (sv 27%nat).
      zv F_16920 D_16920 (Z_to_bv 64 s). stepret F_16924 D_16924 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.

(* [comment removed for export] *)
Theorem pixSetSelectMaskedCmap_W : forall C A m md regs (s pixd : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 144 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 0 ->
  (pixd = 0%Z \/ (exists vd, PIXat m pixd vd /\ live A (Z_to_bv 64 pixd) = Some 64%Z)) ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x165a4 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pixd ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 H11 HP HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL21] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  destruct (sm_P al_rom regs m s ret ltac:(lia) ltac:(lia) (W_sok_win C A m md (s - 144) 144 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1) as (r0 & RUN0 & P2 & P1 & AG0).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN0 |].
  assert (WP0 : W C A (FR13m m s ret regs) md /\ POSTM C A s m (FR13m m s ret regs)) by (unfold FR13m; wp_win CK).
  destruct WP0 as [HW0 PM0]. set (M0 := FR13m m s ret regs) in *.
  pose proof (cells_FR13m m s ret regs ltac:(lia) ltac:(lia)) as CE0. fold M0 in CE0.
  assert (OUT0 : forall x : word, ~ (s - 144 <= u x < s)%Z -> M0 x = m x).
  { intros x Hx. subst M0. unfold FR13m. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (Q10 : getr r0 10 = Z_to_bv 64 pixd) by (rewrite (AG0 10) by notin_list; exact H10).
  assert (Q11 : getr r0 11 = Z_to_bv 64 0) by (rewrite (AG0 11) by notin_list; exact H11).
  (* [comment removed for export] *)
  assert (ERR : forall r2 (msg k : Z), str16 msg k -> W C A M0 md ->
            getr r2 2 = Z_to_bv 64 (s - 144) -> getr r2 10 = Z_to_bv 64 msg -> getr r2 11 = Z_to_bv 64 0x10a26 ->
            (forall x, In x [3; 4]%bv -> getr r2 x = getr regs x) ->
            realizes SEGS (mkCfg (mkst r2 (0x1676c : word) M0 al_rom) md) S).
  { intros r2 msg k Sk HWx X2 X10 X11 RR.
    destruct (sm_etail al_rom r2 M0 s ret (svr13 regs) msg ltac:(lia) ltac:(lia) CE0 X2 X10 X11)
      as (r3 & RUN3 & V2 & V1 & V10 & V11 & V12 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26 & V27 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWx)) | exact (mp_lazy _ (w_pure _ _ _ _ HWx)) | exact RUN3 |].
    unfold svr13 in *.
    apply (returnErrorInt_W C A M0 md r3 s msg 0x10a26 k 22 ret (Z_to_bv 64 1) S CK HWx V2 Hs16 ltac:(unfold LSF; lia) Hhi V1 Hret V10 V11 V12 Sk str_pixSetSelectMaskedCmap).
    intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
    apply (HK m4 r5 HW4).
    - apply cs_kept_intro; csr; try reflexivity. all: rewrite ?V8, ?V9, ?V18, ?V19, ?V20, ?V21, ?V22, ?V23, ?V24, ?V25, ?V26, ?V27; try reflexivity.
      all: rewrite RR by (cbn; tauto); reflexivity.
    - eapply POSTM_trans; [exact PM0|]. eapply (POSTM_range C A M0 md m4); [exact CK | exact HW0 | exact OUT4 | lia | lia | lia]. }
  destruct HP as [P0 | (vd & PX & Lp)].
  - (* [comment removed for export] *)
    subst pixd.
    destruct (sm_A0 al_rom r0 M0 s (W_sev_got C A M0 md HW0) (W_sev C A M0 md HW0) P2 Q10) as (r1 & RUN1 & X2 & X10 & X11 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN1 |].
    apply (ERR r1 0x10298%Z 16%Z str_pixs_not_defined' HW0 X2 X10 X11). intros x Hx. rewrite (AG1 x), (AG0 x) by (cbn in Hx; destruct Hx as [<-|[<-|[]]]; notin_list). reflexivity.
  - pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_cmap _ WF) as Rc.
    destruct (blk_range C A m md (Z_to_bv 64 pixd) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
    assert (PX0 : PIXat M0 pixd vd) by (apply (PIXat_frame m); [exact PX | intros x Hx; apply OUT0; lia]).
    destruct (sm_A al_rom r0 M0 pixd vd ltac:(lia) PX0 Q10 Q11) as (r1 & RUN1 & X10 & X23 & X2 & AG1). rewrite P2 in X2.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN1 |].
    destruct (Z.eq_dec (p_cmap vd) 0) as [CD0|CDnz].
    + rewrite CD0 in X10.
      destruct (sm_B0 al_rom r1 M0 s (W_sev_got C A M0 md HW0) (W_sev C A M0 md HW0) X2 X10) as (r2 & RUN2 & Y2 & Y10 & Y11 & AG2).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN2 |].
      apply (ERR r2 0x108f0%Z 11%Z str_no_colormap' HW0 Y2 Y10 Y11). intros x Hx. rewrite (AG2 x), (AG1 x), (AG0 x) by (cbn in Hx; destruct Hx as [<-|[<-|[]]]; notin_list). reflexivity.
    + destruct (sm_B al_rom r1 M0 s (p_cmap vd) ltac:(lia) ltac:(lia) (W_sev_got C A M0 md HW0) (W_sev C A M0 md HW0) X2 X10 X23) as (r2 & RUN2 & Y2 & Y1 & Y10 & Y11 & AG2).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN2 |].
      apply (lept_stderr1_W C A M0 md r2 (s - 144) 0x10388 0x10a26 38 22 (Z_to_bv 64 0x16718) S CK HW0 Y2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
               ltac:(unfold LSF; lia) ltac:(lia) Y1 ltac:(red; apply bv_eq; reflexivity) Y10 Y11 ltac:(apply fmts1_16; cbn; tauto) str_no_mask str_pixSetSelectMaskedCmap).
      intros m3 r3 HW3 OUT3 GR3 CS3. unfold LSF in OUT3.
      replace (Z_to_bv 64 0x16718) with (0x16718 : word) by (apply bv_eq; reflexivity).
      assert (CE3 : cellsZ m3 (frame13 s ret (svr13 regs))) by (eapply (cells13_out M0 m3 _ _); [exact OUT3 | lia | lia | lia | exact CE0]).
      destruct (sm_C al_rom r3 m3 s ret (svr13 regs) ltac:(lia) ltac:(lia) Hret CE3 ltac:(csr; reflexivity))
        as (r4 & RUN4 & V2 & V1 & V10 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26 & V27 & AG4).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN4 |].
      unfold svr13 in *.
      apply (HK m3 r4 HW3).
      * apply cs_kept_intro; csr; try reflexivity. all: rewrite ?V8, ?V9, ?V18, ?V19, ?V20, ?V21, ?V22, ?V23, ?V24, ?V25, ?V26, ?V27; try reflexivity.
        all: rewrite (AG2 _), (AG1 _), (AG0 _) by notin_list; reflexivity.
      * eapply POSTM_trans; [exact PM0|]. eapply (POSTM_range C A M0 md m3); [exact CK | exact HW0 | exact OUT3 | lia | lia | lia].
Qed.

End SelMasked.
