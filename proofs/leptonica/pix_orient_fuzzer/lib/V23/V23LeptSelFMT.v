(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptRop GrayLib LeptRecs LeptSel.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptSelFMT.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptUb V23_code_morphA_selfmt.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition FRS (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) (a3 a4 : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
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
    (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 (getr regs 27)))
    (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 a3)))
    (Z_to_bv 64 (s - 120)) (word_to_le_bytes 8 (Z_to_bv 64 a4)).

Lemma xor_self : forall x : word, v_xor x x = Z_to_bv 64 0.
Proof. intros x. unfold v_xor. rewrite Z.lxor_nilpotent. reflexivity. Qed.

Lemma and_m1 : forall x : word, v_and (Z_to_bv 64 (-1)) x = x.
Proof.
  intros x. unfold v_and. rewrite u_Z2bv_mod. change ((-1) mod 2 ^ 64)%Z with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. pose proof (u64_range x). rewrite Z.mod_small by lia. apply zbv_self.
Qed.

Lemma slt_0_pos : forall z, (0 < z < 2 ^ 63)%Z -> v_slt (Z_to_bv 64 0) (Z_to_bv 64 z) = Z_to_bv 64 1.
Proof.
  intros z Hz. unfold v_slt. rewrite c_lts_Z by lia.
  replace (0 <? z)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma ble4_range : forall bs : list byte, length bs = 4%nat -> (0 <= bytes_le_to_Z bs < 2 ^ 32)%Z.
Proof.
  intros bs L. pose proof (bytes_le_to_Z_nonneg bs). pose proof (bytes_le_to_Z_bound bs) as B.
  rewrite L in B. change (8 * Z.of_nat 4)%Z with 32%Z in B. lia.
Qed.

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
Ltac condR := pin; first [ apply c_eq_refl | vm_compute; reflexivity ].
Ltac condS := pin; rewrite ?c_lts_Zs by lia; first [ apply Z.ltb_lt | apply Z.ltb_ge ]; lia.
Ltac condE := pin; rewrite ?c_eq_Zs by lia; first [ apply Z.eqb_eq | apply Z.eqb_neq ]; lia.
Ltac zlit F D v := stepat F D v ltac:(gres; pin; imm_norm; apply bv_eq; vm_compute; reflexivity).
Ltac seqz0 F D := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).
Ltac snez1 F D := stepat F D (Z_to_bv 64 1) ltac:(gres; pin; apply zbv_snez; lia).
Ltac sltu00 F D := stepat F D (Z_to_bv 64 0) ltac:(gres; pin; apply zbv_sltu_ge; lia).
Ltac sxw F D v := stepiv F D v ltac:(gres; pin; imm_norm; rewrite LeptArith2.v_addiw_Z, sw32_small by lia; first [reflexivity | f_equal; lia]).
Ltac subwv F D v := sn F D; fixv v ltac:(rewrite v_subw_Z, sw32_small by lia; first [reflexivity | f_equal; lia]).
Ltac xor0 F D := stepat F D (Z_to_bv 64 0) ltac:(gres; pin; apply xor_self).
Ltac byag := repeat match goal with
  | H : getr ?B ?r = ?v |- getr ?B ?r = ?v => exact H
  | AG : regs_agree _ ?A ?B |- getr ?B ?r = _ => rewrite (AG r) by notin_list
  end.

Section Segs.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation K := 10000%Z (only parsing).
#[local] Notation inm x := (0 <= x <= K)%Z (only parsing).

Lemma sf_entry : forall regs m (s sel a1 a2 a3 a4 sy sx cy cx data name : Z) (ret : word),
  (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= sel)%Z -> (sel mod 8 = 0)%Z ->
  RECat (O23LeptSelFMT.SFZ (FRS m s ret regs a3 a4) a1 a2 a3 a4) sel (sel_flds sy sx cy cx data name) ->
  (1 <= sy <= K)%Z -> (1 <= sx <= K)%Z -> (0 <= cx < sx)%Z -> (0 <= cy < sy)%Z ->
  (s <= a1)%Z -> (a1 + 4 < 2 ^ 64)%Z -> (s <= a2)%Z -> (a2 + 4 < 2 ^ 64)%Z ->
  (s <= a3)%Z -> (a3 + 4 < 2 ^ 64)%Z -> (s <= a4)%Z -> (a4 + 4 < 2 ^ 64)%Z ->
  (a1 mod 4 = 0)%Z -> (a2 mod 4 = 0)%Z -> (a3 mod 4 = 0)%Z -> (a4 mod 4 = 0)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 128)) 128 = true ->
  store_ok SEGS m (Z_to_bv 64 a1) 4 = true -> store_ok SEGS m (Z_to_bv 64 a2) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 a3) 4 = true -> store_ok SEGS m (Z_to_bv 64 a4) 4 = true ->
  getr regs 1 = ret -> getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 sel ->
  getr regs 11 = Z_to_bv 64 a1 -> getr regs 12 = Z_to_bv 64 a2 -> getr regs 13 = Z_to_bv 64 a3 -> getr regs 14 = Z_to_bv 64 a4 ->
  exists regs',
    msteps SEGS (mkst regs (0xa5590 : word) m rom) (mkst regs' (0xa566c : word) (O23LeptSelFMT.SFZ (FRS m s ret regs a3 a4) a1 a2 a3 a4) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 128) /\ getr regs' 10 = Z_to_bv 64 sel /\ getr regs' 11 = Z_to_bv 64 a1 /\ getr regs' 12 = Z_to_bv 64 a2
    /\ getr regs' 13 = Z_to_bv 64 sx /\ getr regs' 8 = Z_to_bv 64 sx /\ getr regs' 9 = Z_to_bv 64 2147483647 /\ getr regs' 6 = Z_to_bv 64 0
    /\ getr regs' 5 = Z_to_bv 64 0 /\ getr regs' 14 = Z_to_bv 64 0 /\ getr regs' 15 = Z_to_bv 64 0 /\ getr regs' 16 = Z_to_bv 64 0
    /\ getr regs' 28 = Z_to_bv 64 cy /\ getr regs' 29 = Z_to_bv 64 cx /\ getr regs' 30 = Z_to_bv 64 1 /\ getr regs' 31 = Z_to_bv 64 sy
    /\ regs_agree (fun r => In r [2; 5; 6; 8; 9; 13; 14; 15; 16; 17; 28; 29; 30; 31]%list) regs regs'.
Proof.
  intros regs m s sel a1 a2 a3 a4 sy sx cy cx data name ret Hs Hs64 Hsel ALs RC Hsy Hsx Hcx Hcy
    Ha1 Ha1' Ha2 Ha2' Ha3 Ha3' Ha4 Ha4' AL1 AL2 AL3 AL4 SOK S1 S2 S3 S4 H1 H2 H10 H11 H12 H13 H14.
  pose proof (RECat_range _ _ _ RC) as [Hs0 Hs32].
  change (Z.of_nat (flds_len (sel_flds sy sx cy cx data name))) with 32%Z in Hs32.
  pose proof (REC_rd' SEGS _ sel _ 0 4 (Z_to_bv 64 sel) sy RC ltac:(cbn; lia) eq_refl ltac:(f_equal; cbn; lia) eq_refl) as R0.
  pose proof (REC_rd' SEGS _ sel _ 1 4 (Z_to_bv 64 (sel + 4)) sx RC ltac:(cbn; lia) eq_refl ltac:(f_equal; cbn; lia) eq_refl) as R1.
  pose proof (REC_rd' SEGS _ sel _ 2 4 (Z_to_bv 64 (sel + 8)) cy RC ltac:(cbn; lia) eq_refl ltac:(f_equal; cbn; lia) eq_refl) as R2.
  pose proof (REC_rd' SEGS _ sel _ 3 4 (Z_to_bv 64 (sel + 12)) cx RC ltac:(cbn; lia) eq_refl ltac:(f_equal; cbn; lia) eq_refl) as R3.
  eexists. split.
  - unfold O23LeptSelFMT.SFZ, O23LeptSelFMT.wr4, FRS.
    zv F_a5590 D_a5590 (Z_to_bv 64 (s - 128)).
    stepST F_a5594 D_a5594 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_a5598 D_a5598 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_a559c D_a559c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_a55a0 D_a55a0 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_a55a4 D_a55a4 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepST F_a55a8 D_a55a8 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
    stepST F_a55ac D_a55ac (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
    stepST F_a55b0 D_a55b0 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
    stepST F_a55b4 D_a55b4 (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
    stepST F_a55b8 D_a55b8 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
    stepST F_a55bc D_a55bc (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).
    stepST F_a55c0 D_a55c0 (Z_to_bv 64 (s - 96)) (getr regs 26) ltac:(sok_in SOK).
    stepST F_a55c4 D_a55c4 (Z_to_bv 64 (s - 104)) (getr regs 27) ltac:(sok_in SOK).
    stepb_ft F_a55c8 D_a55c8 ltac:(condZ).
    stepb_ft F_a55cc D_a55cc ltac:(condZ).
    stepb_ft F_a55d0 D_a55d0 ltac:(condZ).
    stepb_ft F_a55d4 D_a55d4 ltac:(condZ).
    stepST F_a55d8 D_a55d8 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 a3) ltac:(sok_in SOK).
    stepST F_a55dc D_a55dc (Z_to_bv 64 (s - 120)) (Z_to_bv 64 a4) ltac:(sok_in SOK).
    guard4 F_a55e0 D_a55e0 AL4.
    stepb_ft F_a55e4 D_a55e4 ltac:(condR).
    stepLD8 F_a55e8 D_a55e8 (Z_to_bv 64 a3).
    guard4 F_a55ec D_a55ec AL3.
    stepLD8 F_a55f0 D_a55f0 (Z_to_bv 64 a4).
    stepST F_a55f4 D_a55f4 (Z_to_bv 64 a4) (Z_to_bv 64 0) ltac:(sok_in S4).
    stepb_ft F_a55f8 D_a55f8 ltac:(condR).
    guard4 F_a55fc D_a55fc AL2.
    stepLD8 F_a5600 D_a5600 (Z_to_bv 64 a3).
    stepST F_a5604 D_a5604 (Z_to_bv 64 a3) (Z_to_bv 64 0) ltac:(sok_in S3).
    stepb_ft F_a5608 D_a5608 ltac:(condR).
    guard4 F_a560c D_a560c AL1.
    stepST F_a5610 D_a5610 (Z_to_bv 64 a2) (Z_to_bv 64 0) ltac:(sok_in S2).
    stepb_ft F_a5614 D_a5614 ltac:(condR).
    stepST F_a5618 D_a5618 (Z_to_bv 64 a1) (Z_to_bv 64 0) ltac:(sok_in S1).
    stepb_ft F_a561c D_a561c ltac:(condZ).
    guard8 F_a5620 D_a5620 ALs.
    stepb_ft F_a5624 D_a5624 ltac:(condR).
    stepLD F_a5628 D_a5628 (Z_to_le_bytes 4 sy) (Z_to_bv 64 sy) ltac:(addr_norm; exact R0) ltac:(apply lez4; lia).
    rewrite ?(v_lw_small sy) by lia.
    stepb_ft F_a562c D_a562c ltac:(condZ).
    zv F_a5630 D_a5630 (Z_to_bv 64 0).
    zv F_a5634 D_a5634 (Z_to_bv 64 0).
    zv F_a5638 D_a5638 (Z_to_bv 64 0).
    zv F_a563c D_a563c (Z_to_bv 64 0).
    zv F_a5640 D_a5640 (Z_to_bv 64 0).
    stepLD F_a5644 D_a5644 (Z_to_le_bytes 4 sx) (Z_to_bv 64 sx) ltac:(addr_norm; exact R1) ltac:(apply lez4; lia).
    stepLD F_a5648 D_a5648 (Z_to_le_bytes 4 cy) (Z_to_bv 64 cy) ltac:(addr_norm; exact R2) ltac:(apply lez4; lia).
    rewrite ?(v_lw_small cy) by lia.
    stepLD F_a564c D_a564c (Z_to_le_bytes 4 cx) (Z_to_bv 64 cx) ltac:(addr_norm; exact R3) ltac:(apply lez4; lia).
    rewrite ?(v_lw_small cx) by lia.
    stepat F_a5650 D_a5650 (Z_to_bv 64 1) ltac:(gres; pin; apply slt_0_pos; lia).
    zv F_a5654 D_a5654 (Z_to_bv 64 1).
    zlit F_a5658 D_a5658 (Z_to_bv 64 (-2147483648)).
    zlit F_a565c D_a565c (Z_to_bv 64 (-1)).
    stepat F_a5660 D_a5660 (Z_to_bv 64 sy) ltac:(gres; pin; apply and_m1).
    sxw F_a5664 D_a5664 (Z_to_bv 64 sx).
    zlit F_a5668 D_a5668 (Z_to_bv 64 2147483647).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

Lemma sfi_y3a : forall regs m (icy y3 : Z), (- K <= icy <= K)%Z -> inm y3 ->
  getr regs 21 = Z_to_bv 64 icy -> getr regs 15 = Z_to_bv 64 y3 ->
  exists regs', msteps SEGS (mkst regs (0xa575c : word) m rom) (mkst regs' (0xa56e4 : word) m rom)
    /\ getr regs' 15 = Z_to_bv 64 (Z.max y3 icy) /\ regs_agree (fun r => In r [15; 17]%list) regs regs'.
Proof.
  intros regs m icy y3 Hi Hy H21 H15.
  destruct (Z.ltb_spec icy y3) as [Lt|Ge]; eexists; split; [| split | | split].
  - sxw F_a575c D_a575c (Z_to_bv 64 icy). stepb_tk F_a5760 D_a5760 ltac:(condS). apply mst_refl.
  - gres; pin. f_equal; lia.
  - solve_regs_agree.
  - sxw F_a575c D_a575c (Z_to_bv 64 icy). stepb_ft F_a5760 D_a5760 ltac:(condS).
    sn F_a5764 D_a5764. zv F_a577c D_a577c (Z_to_bv 64 icy). sn F_a5780 D_a5780. apply mst_refl.
  - gres; pin. f_equal; lia.
  - solve_regs_agree.
Qed.

Lemma sfi_y3b : forall regs m (icy y3 : Z), (- K <= icy <= K)%Z -> inm y3 ->
  getr regs 21 = Z_to_bv 64 icy -> getr regs 15 = Z_to_bv 64 y3 ->
  exists regs', msteps SEGS (mkst regs (0xa5774 : word) m rom) (mkst regs' (0xa56e4 : word) m rom)
    /\ getr regs' 15 = Z_to_bv 64 (Z.max y3 icy) /\ regs_agree (fun r => In r [15; 17]%list) regs regs'.
Proof.
  intros regs m icy y3 Hi Hy H21 H15.
  destruct (Z.ltb_spec icy y3) as [Lt|Ge]; eexists; split; [| split | | split].
  - sxw F_a5774 D_a5774 (Z_to_bv 64 icy). stepb_tk F_a5778 D_a5778 ltac:(condS). apply mst_refl.
  - gres; pin. f_equal; lia.
  - solve_regs_agree.
  - sxw F_a5774 D_a5774 (Z_to_bv 64 icy). stepb_ft F_a5778 D_a5778 ltac:(condS).
    zv F_a577c D_a577c (Z_to_bv 64 icy). sn F_a5780 D_a5780. apply mst_refl.
  - gres; pin. f_equal; lia.
  - solve_regs_agree.
Qed.

Lemma sfi_y2a : forall regs m (jcx icy y2 y3 : Z), (- K <= jcx <= K)%Z -> (- K <= icy <= K)%Z -> inm y2 -> inm y3 ->
  getr regs 7 = Z_to_bv 64 jcx -> getr regs 21 = Z_to_bv 64 icy -> getr regs 16 = Z_to_bv 64 y2 -> getr regs 15 = Z_to_bv 64 y3 ->
  exists regs', msteps SEGS (mkst regs (0xa5754 : word) m rom) (mkst regs' (0xa56e4 : word) m rom)
    /\ getr regs' 16 = Z_to_bv 64 (Z.max y2 jcx) /\ getr regs' 15 = Z_to_bv 64 (Z.max y3 icy)
    /\ regs_agree (fun r => In r [7; 15; 16; 17]%list) regs regs'.
Proof.
  intros regs m jcx icy y2 y3 Hj Hi Hy2 Hy3 H7 H21 H16 H15.
  destruct (Z.ltb_spec jcx y2) as [Lt|Ge].
  - assert (P : exists r1, msteps SEGS (mkst regs (0xa5754 : word) m rom) (mkst r1 (0xa575c : word) m rom)
              /\ regs_agree (fun r => In r [7]%list) regs r1).
    { eexists. split.
      - sxw F_a5754 D_a5754 (Z_to_bv 64 jcx). stepb_ft F_a5758 D_a5758 ltac:(condS). apply mst_refl.
      - solve_regs_agree. }
    destruct P as (r1 & S1 & AG1).
    destruct (sfi_y3a r1 m icy y3 Hi Hy3 ltac:(byag) ltac:(byag)) as (r2 & S2 & E15 & AG2).
    exists r2. split; [eapply msteps_trans; [exact S1 | exact S2] |]. split; [| split].
    + rewrite (AG2 16) by notin_list. rewrite (AG1 16) by notin_list. rewrite H16. f_equal; lia.
    + exact E15.
    + eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
  - assert (P : exists r1, msteps SEGS (mkst regs (0xa5754 : word) m rom) (mkst r1 (0xa5774 : word) m rom)
              /\ getr r1 16 = Z_to_bv 64 jcx /\ regs_agree (fun r => In r [7; 16]%list) regs r1).
    { eexists. split; [| split].
      - sxw F_a5754 D_a5754 (Z_to_bv 64 jcx). stepb_tk F_a5758 D_a5758 ltac:(condS).
        zv F_a5770 D_a5770 (Z_to_bv 64 jcx). apply mst_refl.
      - gres; pin; reflexivity.
      - solve_regs_agree. }
    destruct P as (r1 & S1 & E16 & AG1).
    destruct (sfi_y3b r1 m icy y3 Hi Hy3 ltac:(byag) ltac:(byag)) as (r2 & S2 & E15 & AG2).
    exists r2. split; [eapply msteps_trans; [exact S1 | exact S2] |]. split; [| split].
    + rewrite (AG2 16) by notin_list. rewrite E16. f_equal; lia.
    + exact E15.
    + eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
Qed.

Lemma sfi_y2b : forall regs m (jcx icy y2 y3 : Z), (- K <= jcx <= K)%Z -> (- K <= icy <= K)%Z -> inm y2 -> inm y3 ->
  getr regs 7 = Z_to_bv 64 jcx -> getr regs 21 = Z_to_bv 64 icy -> getr regs 16 = Z_to_bv 64 y2 -> getr regs 15 = Z_to_bv 64 y3 ->
  exists regs', msteps SEGS (mkst regs (0xa5768 : word) m rom) (mkst regs' (0xa56e4 : word) m rom)
    /\ getr regs' 16 = Z_to_bv 64 (Z.max y2 jcx) /\ getr regs' 15 = Z_to_bv 64 (Z.max y3 icy)
    /\ regs_agree (fun r => In r [7; 15; 16; 17]%list) regs regs'.
Proof.
  intros regs m jcx icy y2 y3 Hj Hi Hy2 Hy3 H7 H21 H16 H15.
  destruct (Z.ltb_spec jcx y2) as [Lt|Ge].
  - assert (P : exists r1, msteps SEGS (mkst regs (0xa5768 : word) m rom) (mkst r1 (0xa575c : word) m rom)
              /\ regs_agree (fun r => In r [7]%list) regs r1).
    { eexists. split.
      - sxw F_a5768 D_a5768 (Z_to_bv 64 jcx). stepb_tk F_a576c D_a576c ltac:(condS). apply mst_refl.
      - solve_regs_agree. }
    destruct P as (r1 & S1 & AG1).
    destruct (sfi_y3a r1 m icy y3 Hi Hy3 ltac:(byag) ltac:(byag)) as (r2 & S2 & E15 & AG2).
    exists r2. split; [eapply msteps_trans; [exact S1 | exact S2] |]. split; [| split].
    + rewrite (AG2 16) by notin_list. rewrite (AG1 16) by notin_list. rewrite H16. f_equal; lia.
    + exact E15.
    + eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
  - assert (P : exists r1, msteps SEGS (mkst regs (0xa5768 : word) m rom) (mkst r1 (0xa5774 : word) m rom)
              /\ getr r1 16 = Z_to_bv 64 jcx /\ regs_agree (fun r => In r [7; 16]%list) regs r1).
    { eexists. split; [| split].
      - sxw F_a5768 D_a5768 (Z_to_bv 64 jcx). stepb_ft F_a576c D_a576c ltac:(condS).
        zv F_a5770 D_a5770 (Z_to_bv 64 jcx). apply mst_refl.
      - gres; pin; reflexivity.
      - solve_regs_agree. }
    destruct P as (r1 & S1 & E16 & AG1).
    destruct (sfi_y3b r1 m icy y3 Hi Hy3 ltac:(byag) ltac:(byag)) as (r2 & S2 & E15 & AG2).
    exists r2. split; [eapply msteps_trans; [exact S1 | exact S2] |]. split; [| split].
    + rewrite (AG2 16) by notin_list. rewrite E16. f_equal; lia.
    + exact E15.
    + eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
Qed.

Lemma sfi_y1 : forall regs m (j cx cyi icy y1 y2 y3 : Z), (0 <= j <= K)%Z -> (0 <= cx <= K)%Z ->
  (- K <= cyi <= K)%Z -> (- K <= icy <= K)%Z -> inm y1 -> inm y2 -> inm y3 ->
  getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 18 = Z_to_bv 64 j -> getr regs 29 = Z_to_bv 64 cx ->
  getr regs 20 = Z_to_bv 64 cyi -> getr regs 21 = Z_to_bv 64 icy ->
  getr regs 14 = Z_to_bv 64 y1 -> getr regs 16 = Z_to_bv 64 y2 -> getr regs 15 = Z_to_bv 64 y3 ->
  exists regs', msteps SEGS (mkst regs (0xa5728 : word) m rom) (mkst regs' (0xa56e4 : word) m rom)
    /\ getr regs' 14 = Z_to_bv 64 (Z.max y1 cyi) /\ getr regs' 16 = Z_to_bv 64 (Z.max y2 (j - cx))
    /\ getr regs' 15 = Z_to_bv 64 (Z.max y3 icy) /\ regs_agree (fun r => In r [7; 14; 15; 16; 17]%list) regs regs'.
Proof.
  intros regs m j cx cyi icy y1 y2 y3 Hj Hcx Hcyi Hicy Hy1 Hy2 Hy3 H22 H23 H18 H29 H20 H21 H14 H16 H15.
  destruct (Z.ltb_spec cyi y1) as [Lt|Ge].
  - assert (P : exists r1, msteps SEGS (mkst regs (0xa5728 : word) m rom) (mkst r1 (0xa5768 : word) m rom)
              /\ getr r1 7 = Z_to_bv 64 (j - cx) /\ regs_agree (fun r => In r [7; 17]%list) regs r1).
    { eexists. split; [| split].
      - stepb_ft F_a5728 D_a5728 ltac:(condR).
        zv F_a572c D_a572c (Z_to_bv 64 (j - cx)).
        subwv F_a5730 D_a5730 (Z_to_bv 64 (j - cx)).
        xor0 F_a5734 D_a5734.
        sltu00 F_a5738 D_a5738.
        zlit F_a573c D_a573c (Z_to_bv 64 0).
        zlit F_a5740 D_a5740 (Z_to_bv 64 0).
        stepb_ft F_a5744 D_a5744 ltac:(condR).
        sxw F_a5748 D_a5748 (Z_to_bv 64 cyi).
        stepb_tk F_a574c D_a574c ltac:(condS).
        apply mst_refl.
      - gres; pin; reflexivity.
      - solve_regs_agree. }
    destruct P as (r1 & S1 & E7 & AG1).
    destruct (sfi_y2b r1 m (j - cx) icy y2 y3 ltac:(lia) Hicy Hy2 Hy3 E7 ltac:(byag) ltac:(byag) ltac:(byag)) as (r2 & S2 & E16 & E15 & AG2).
    exists r2. split; [eapply msteps_trans; [exact S1 | exact S2] |]. split; [| split; [| split]].
    + rewrite (AG2 14) by notin_list. rewrite (AG1 14) by notin_list. rewrite H14. f_equal; lia.
    + exact E16.
    + exact E15.
    + eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
  - assert (P : exists r1, msteps SEGS (mkst regs (0xa5728 : word) m rom) (mkst r1 (0xa5754 : word) m rom)
              /\ getr r1 7 = Z_to_bv 64 (j - cx) /\ getr r1 14 = Z_to_bv 64 cyi /\ regs_agree (fun r => In r [7; 14; 17]%list) regs r1).
    { eexists. split; [| split; [| split]].
      - stepb_ft F_a5728 D_a5728 ltac:(condR).
        zv F_a572c D_a572c (Z_to_bv 64 (j - cx)).
        subwv F_a5730 D_a5730 (Z_to_bv 64 (j - cx)).
        xor0 F_a5734 D_a5734.
        sltu00 F_a5738 D_a5738.
        zlit F_a573c D_a573c (Z_to_bv 64 0).
        zlit F_a5740 D_a5740 (Z_to_bv 64 0).
        stepb_ft F_a5744 D_a5744 ltac:(condR).
        sxw F_a5748 D_a5748 (Z_to_bv 64 cyi).
        stepb_ft F_a574c D_a574c ltac:(condS).
        zv F_a5750 D_a5750 (Z_to_bv 64 cyi).
        apply mst_refl.
      - gres; pin; reflexivity.
      - gres; pin; reflexivity.
      - solve_regs_agree. }
    destruct P as (r1 & S1 & E7 & E14 & AG1).
    destruct (sfi_y2a r1 m (j - cx) icy y2 y3 ltac:(lia) Hicy Hy2 Hy3 E7 ltac:(byag) ltac:(byag) ltac:(byag)) as (r2 & S2 & E16 & E15 & AG2).
    exists r2. split; [eapply msteps_trans; [exact S1 | exact S2] |]. split; [| split; [| split]].
    + rewrite (AG2 14) by notin_list. rewrite E14. f_equal; lia.
    + exact E16.
    + exact E15.
    + eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
Qed.

Lemma sfi_hit : forall regs m (j cx cyi icy y0 y1 y2 y3 : Z), (0 <= j <= K)%Z -> (0 <= cx <= K)%Z ->
  (- K <= cyi <= K)%Z -> (- K <= icy <= K)%Z -> inm y0 -> inm y1 -> inm y2 -> inm y3 ->
  getr regs 29 = Z_to_bv 64 cx -> getr regs 18 = Z_to_bv 64 j -> getr regs 5 = Z_to_bv 64 y0 ->
  getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 20 = Z_to_bv 64 cyi -> getr regs 21 = Z_to_bv 64 icy ->
  getr regs 14 = Z_to_bv 64 y1 -> getr regs 16 = Z_to_bv 64 y2 -> getr regs 15 = Z_to_bv 64 y3 ->
  exists regs', msteps SEGS (mkst regs (0xa5710 : word) m rom) (mkst regs' (0xa56e4 : word) m rom)
    /\ getr regs' 5 = Z_to_bv 64 (Z.max y0 (cx - j)) /\ getr regs' 14 = Z_to_bv 64 (Z.max y1 cyi)
    /\ getr regs' 16 = Z_to_bv 64 (Z.max y2 (j - cx)) /\ getr regs' 15 = Z_to_bv 64 (Z.max y3 icy)
    /\ regs_agree (fun r => In r [5; 7; 14; 15; 16; 17]%list) regs regs'.
Proof.
  intros regs m j cx cyi icy y0 y1 y2 y3 Hj Hcx Hcyi Hicy Hy0 Hy1 Hy2 Hy3 H29 H18 H5 H22 H23 H20 H21 H14 H16 H15.
  destruct (Z.ltb_spec (cx - j) y0) as [Lt|Ge].
  - assert (P : exists r1, msteps SEGS (mkst regs (0xa5710 : word) m rom) (mkst r1 (0xa5728 : word) m rom)
              /\ regs_agree (fun r => In r [7; 17]%list) regs r1).
    { eexists. split.
      - zv F_a5710 D_a5710 (Z_to_bv 64 (cx - j)).
        subwv F_a5714 D_a5714 (Z_to_bv 64 (cx - j)).
        stepb_ft F_a5718 D_a5718 ltac:(condR).
        sxw F_a571c D_a571c (Z_to_bv 64 (cx - j)).
        stepb_tk F_a5720 D_a5720 ltac:(condS).
        apply mst_refl.
      - solve_regs_agree. }
    destruct P as (r1 & S1 & AG1).
    destruct (sfi_y1 r1 m j cx cyi icy y1 y2 y3 Hj Hcx Hcyi Hicy Hy1 Hy2 Hy3 ltac:(byag) ltac:(byag) ltac:(byag) ltac:(byag)
      ltac:(byag) ltac:(byag) ltac:(byag) ltac:(byag) ltac:(byag)) as (r2 & S2 & E14 & E16 & E15 & AG2).
    exists r2. split; [eapply msteps_trans; [exact S1 | exact S2] |]. split; [| split; [| split; [| split]]].
    + rewrite (AG2 5) by notin_list. rewrite (AG1 5) by notin_list. rewrite H5. f_equal; lia.
    + exact E14.
    + exact E16.
    + exact E15.
    + eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
  - assert (P : exists r1, msteps SEGS (mkst regs (0xa5710 : word) m rom) (mkst r1 (0xa5728 : word) m rom)
              /\ getr r1 5 = Z_to_bv 64 (cx - j) /\ regs_agree (fun r => In r [5; 7; 17]%list) regs r1).
    { eexists. split; [| split].
      - zv F_a5710 D_a5710 (Z_to_bv 64 (cx - j)).
        subwv F_a5714 D_a5714 (Z_to_bv 64 (cx - j)).
        stepb_ft F_a5718 D_a5718 ltac:(condR).
        sxw F_a571c D_a571c (Z_to_bv 64 (cx - j)).
        stepb_ft F_a5720 D_a5720 ltac:(condS).
        zv F_a5724 D_a5724 (Z_to_bv 64 (cx - j)).
        apply mst_refl.
      - gres; pin; reflexivity.
      - solve_regs_agree. }
    destruct P as (r1 & S1 & E5 & AG1).
    destruct (sfi_y1 r1 m j cx cyi icy y1 y2 y3 Hj Hcx Hcyi Hicy Hy1 Hy2 Hy3 ltac:(byag) ltac:(byag) ltac:(byag) ltac:(byag)
      ltac:(byag) ltac:(byag) ltac:(byag) ltac:(byag) ltac:(byag)) as (r2 & S2 & E14 & E16 & E15 & AG2).
    exists r2. split; [eapply msteps_trans; [exact S1 | exact S2] |]. split; [| split; [| split; [| split]]].
    + rewrite (AG2 5) by notin_list. rewrite E5. f_equal; lia.
    + exact E14.
    + exact E16.
    + exact E15.
    + eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
Qed.

Lemma sfi_step : forall regs m (row j sx cx cyi icy y0 y1 y2 y3 : Z) (bs : list byte),
  (1 <= row)%Z -> (row + 4 * sx < 2 ^ 64)%Z -> (0 <= j < sx)%Z -> (sx <= K)%Z -> (0 <= cx < sx)%Z ->
  (- K <= cyi <= K)%Z -> (- K <= icy <= K)%Z -> inm y0 -> inm y1 -> inm y2 -> inm y3 ->
  rdn SEGS m (Z_to_bv 64 (row + 4 * j)) 4 = Some bs ->
  getr regs 27 = Z_to_bv 64 (row + 4 * j) -> getr regs 24 = Z_to_bv 64 1 -> getr regs 19 = Z_to_bv 64 row -> getr regs 25 = Z_to_bv 64 1 ->
  getr regs 1 = Z_to_bv 64 (row + 4 * j) -> getr regs 30 = Z_to_bv 64 1 ->
  getr regs 29 = Z_to_bv 64 cx -> getr regs 18 = Z_to_bv 64 j -> getr regs 5 = Z_to_bv 64 y0 ->
  getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 20 = Z_to_bv 64 cyi -> getr regs 21 = Z_to_bv 64 icy ->
  getr regs 14 = Z_to_bv 64 y1 -> getr regs 16 = Z_to_bv 64 y2 -> getr regs 15 = Z_to_bv 64 y3 ->
  exists regs' y0' y1' y2' y3',
    msteps SEGS (mkst regs (0xa56f8 : word) m rom) (mkst regs' (0xa56e4 : word) m rom)
    /\ inm y0' /\ inm y1' /\ inm y2' /\ inm y3'
    /\ getr regs' 5 = Z_to_bv 64 y0' /\ getr regs' 14 = Z_to_bv 64 y1' /\ getr regs' 16 = Z_to_bv 64 y2' /\ getr regs' 15 = Z_to_bv 64 y3'
    /\ regs_agree (fun r => In r [5; 7; 14; 15; 16; 17]%list) regs regs'.
Proof.
  intros regs m row j sx cx cyi icy y0 y1 y2 y3 bs Hr Hr64 Hj Hsx Hcx Hcyi Hicy Hy0 Hy1 Hy2 Hy3 RB
    H27 H24 H19 H25 H1 H30 H29 H18 H5 H22 H23 H20 H21 H14 H16 H15.
  pose proof (rdn_length _ _ _ _ _ RB) as LB. pose proof (ble4_range bs LB) as BR.
  pose proof (sw32_range (bytes_le_to_Z bs)) as WR.
  assert (P : exists r1, msteps SEGS (mkst regs (0xa56f8 : word) m rom) (mkst r1 (0xa570c : word) m rom)
            /\ getr r1 17 = Z_to_bv 64 (sw32 (bytes_le_to_Z bs)) /\ regs_agree (fun r => In r [17]%list) regs r1).
  { eexists. split; [| split].
    - seqz0 F_a56f8 D_a56f8.
      stepb_ft F_a56fc D_a56fc ltac:(condR).
      stepb_ft F_a5700 D_a5700 ltac:(condZ).
      stepb_ft F_a5704 D_a5704 ltac:(condR).
      stepLD F_a5708 D_a5708 bs (Z_to_bv 64 (bytes_le_to_Z bs)) ltac:(addr_norm; exact RB) ltac:(rewrite u_Z2bv by lia; reflexivity).
      rewrite LeptArith2.v_lw_Z.
      apply mst_refl.
    - gres; reflexivity.
    - solve_regs_agree. }
  destruct P as (r1 & S1 & E17 & AG1).
  assert (B30 : getr r1 30 = Z_to_bv 64 1) by byag.
  destruct (Z.eqb_spec (sw32 (bytes_le_to_Z bs)) 1) as [Hw|Hw].
  - assert (S2 : msteps SEGS (mkst r1 (0xa570c : word) m rom) (mkst r1 (0xa5710 : word) m rom)).
    { stepb_ft F_a570c D_a570c ltac:(condE). apply mst_refl. }
    destruct (sfi_hit r1 m j cx cyi icy y0 y1 y2 y3 ltac:(lia) ltac:(lia) Hcyi Hicy Hy0 Hy1 Hy2 Hy3 ltac:(byag) ltac:(byag) ltac:(byag)
      ltac:(byag) ltac:(byag) ltac:(byag) ltac:(byag) ltac:(byag) ltac:(byag) ltac:(byag)) as (r2 & S3 & E5 & E14 & E16 & E15 & AG2).
    exists r2, (Z.max y0 (cx - j)), (Z.max y1 cyi), (Z.max y2 (j - cx)), (Z.max y3 icy).
    split; [eapply msteps_trans; [exact S1 | eapply msteps_trans; [exact S2 | exact S3]] |].
    split; [lia | split; [lia | split; [lia | split; [lia |]]]].
    split; [exact E5 | split; [exact E14 | split; [exact E16 | split; [exact E15 |]]]].
    eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
  - assert (S2 : msteps SEGS (mkst r1 (0xa570c : word) m rom) (mkst r1 (0xa56e4 : word) m rom)).
    { stepb_tk F_a570c D_a570c ltac:(condE). apply mst_refl. }
    exists r1, y0, y1, y2, y3.
    split; [eapply msteps_trans; [exact S1 | exact S2] |].
    split; [lia | split; [lia | split; [lia | split; [lia |]]]].
    split; [byag | split; [byag | split; [byag | split; [byag |]]]].
    regs_agree_weaken AG1.
Qed.

Lemma sfi_next_c : forall regs m (row j sx : Z), (1 <= row)%Z -> (row + 4 * sx < 2 ^ 64)%Z -> (0 <= j)%Z -> (j + 1 < sx)%Z -> (sx <= K)%Z ->
  getr regs 18 = Z_to_bv 64 j -> getr regs 1 = Z_to_bv 64 (row + 4 * j) -> getr regs 26 = Z_to_bv 64 (sx - j) -> getr regs 27 = Z_to_bv 64 (row + 4 * j) ->
  exists regs', msteps SEGS (mkst regs (0xa56e4 : word) m rom) (mkst regs' (0xa56f8 : word) m rom)
    /\ getr regs' 18 = Z_to_bv 64 (j + 1) /\ getr regs' 1 = Z_to_bv 64 (row + 4 * (j + 1)) /\ getr regs' 26 = Z_to_bv 64 (sx - (j + 1))
    /\ getr regs' 27 = Z_to_bv 64 (row + 4 * (j + 1)) /\ regs_agree (fun r => In r [1; 18; 26; 27]%list) regs regs'.
Proof.
  intros regs m row j sx Hr Hr64 Hj Hj1 Hsx H18 H1 H26 H27. eexists. split.
  - stepiv F_a56e4 D_a56e4 (Z_to_bv 64 (j + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).
    zv F_a56e8 D_a56e8 (Z_to_bv 64 (row + 4 * (j + 1))).
    zv F_a56ec D_a56ec (Z_to_bv 64 (sx - (j + 1))).
    zv F_a56f0 D_a56f0 (Z_to_bv 64 (row + 4 * (j + 1))).
    stepb_ft F_a56f4 D_a56f4 ltac:(condZ).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

Lemma sfi_next_e : forall regs m (row j sx : Z), (1 <= row)%Z -> (row + 4 * sx < 2 ^ 64)%Z -> (0 <= j)%Z -> (j + 1 = sx)%Z -> (sx <= K)%Z ->
  getr regs 18 = Z_to_bv 64 j -> getr regs 1 = Z_to_bv 64 (row + 4 * j) -> getr regs 26 = Z_to_bv 64 (sx - j) -> getr regs 27 = Z_to_bv 64 (row + 4 * j) ->
  exists regs', msteps SEGS (mkst regs (0xa56e4 : word) m rom) (mkst regs' (0xa5784 : word) m rom)
    /\ regs_agree (fun r => In r [1; 18; 26; 27]%list) regs regs'.
Proof.
  intros regs m row j sx Hr Hr64 Hj Hj1 Hsx H18 H1 H26 H27. eexists. split.
  - stepiv F_a56e4 D_a56e4 (Z_to_bv 64 (j + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).
    zv F_a56e8 D_a56e8 (Z_to_bv 64 (row + 4 * (j + 1))).
    zv F_a56ec D_a56ec (Z_to_bv 64 (sx - (j + 1))).
    zv F_a56f0 D_a56f0 (Z_to_bv 64 (row + 4 * (j + 1))).
    stepb_tk F_a56f4 D_a56f4 ltac:(condZ).
    apply mst_refl.
  - solve_regs_agree.
Qed.

Lemma sfi_loop : forall (n : nat) regs m (row j sx cx cyi icy y0 y1 y2 y3 : Z),
  (1 <= row)%Z -> (row + 4 * sx < 2 ^ 64)%Z -> (0 <= j)%Z -> (j + Z.of_nat n = sx - 1)%Z -> (sx <= K)%Z -> (0 <= cx < sx)%Z ->
  (- K <= cyi <= K)%Z -> (- K <= icy <= K)%Z -> inm y0 -> inm y1 -> inm y2 -> inm y3 ->
  (forall j', (j <= j' < sx)%Z -> exists bs, rdn SEGS m (Z_to_bv 64 (row + 4 * j')) 4 = Some bs) ->
  getr regs 18 = Z_to_bv 64 j -> getr regs 1 = Z_to_bv 64 (row + 4 * j) -> getr regs 26 = Z_to_bv 64 (sx - j) -> getr regs 27 = Z_to_bv 64 (row + 4 * j) ->
  getr regs 19 = Z_to_bv 64 row -> getr regs 24 = Z_to_bv 64 1 -> getr regs 25 = Z_to_bv 64 1 -> getr regs 30 = Z_to_bv 64 1 ->
  getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 29 = Z_to_bv 64 cx -> getr regs 20 = Z_to_bv 64 cyi -> getr regs 21 = Z_to_bv 64 icy ->
  getr regs 5 = Z_to_bv 64 y0 -> getr regs 14 = Z_to_bv 64 y1 -> getr regs 16 = Z_to_bv 64 y2 -> getr regs 15 = Z_to_bv 64 y3 ->
  exists regs' y0' y1' y2' y3',
    msteps SEGS (mkst regs (0xa56f8 : word) m rom) (mkst regs' (0xa5784 : word) m rom)
    /\ inm y0' /\ inm y1' /\ inm y2' /\ inm y3'
    /\ getr regs' 5 = Z_to_bv 64 y0' /\ getr regs' 14 = Z_to_bv 64 y1' /\ getr regs' 16 = Z_to_bv 64 y2' /\ getr regs' 15 = Z_to_bv 64 y3'
    /\ regs_agree (fun r => In r [1; 5; 7; 14; 15; 16; 17; 18; 26; 27]%list) regs regs'.
Proof.
  induction n as [|n IH]; intros regs m row j sx cx cyi icy y0 y1 y2 y3 Hr Hr64 Hj Hn Hsx Hcx Hcyi Hicy Hy0 Hy1 Hy2 Hy3 RB
    H18 H1 H26 H27 H19 H24 H25 H30 H22 H23 H29 H20 H21 H5 H14 H16 H15;
    destruct (RB j ltac:(lia)) as [bs RBj];
    destruct (sfi_step regs m row j sx cx cyi icy y0 y1 y2 y3 bs Hr Hr64 ltac:(lia) Hsx Hcx Hcyi Hicy Hy0 Hy1 Hy2 Hy3 RBj
      H27 H24 H19 H25 H1 H30 H29 H18 H5 H22 H23 H20 H21 H14 H16 H15)
      as (r1 & z0 & z1 & z2 & z3 & S1 & Hz0 & Hz1 & Hz2 & Hz3 & E5 & E14 & E16 & E15 & AG1).
  - destruct (sfi_next_e r1 m row j sx Hr Hr64 Hj ltac:(lia) Hsx ltac:(byag) ltac:(byag) ltac:(byag) ltac:(byag)) as (r2 & S2 & AG2).
    exists r2, z0, z1, z2, z3. split; [eapply msteps_trans; [exact S1 | exact S2] |].
    split; [lia | split; [lia | split; [lia | split; [lia |]]]].
    split; [byag | split; [byag | split; [byag | split; [byag |]]]].
    eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
  - destruct (sfi_next_c r1 m row j sx Hr Hr64 Hj ltac:(lia) Hsx ltac:(byag) ltac:(byag) ltac:(byag) ltac:(byag))
      as (r2 & S2 & F18 & F1 & F26 & F27 & AG2).
    destruct (IH r2 m row (j + 1)%Z sx cx cyi icy z0 z1 z2 z3 Hr Hr64 ltac:(lia) ltac:(lia) Hsx Hcx Hcyi Hicy Hz0 Hz1 Hz2 Hz3
      ltac:(intros j' Hj'; apply RB; lia) F18 F1 F26 F27 ltac:(byag) ltac:(byag) ltac:(byag) ltac:(byag) ltac:(byag) ltac:(byag)
      ltac:(byag) ltac:(byag) ltac:(byag) ltac:(byag) ltac:(byag) ltac:(byag) ltac:(byag))
      as (r3 & w0 & w1 & w2 & w3 & S3 & Hw0 & Hw1 & Hw2 & Hw3 & G5 & G14 & G16 & G15 & AG3).
    exists r3, w0, w1, w2, w3. split; [eapply msteps_trans; [exact S1 | eapply msteps_trans; [exact S2 | exact S3]] |].
    split; [lia | split; [lia | split; [lia | split; [lia |]]]].
    split; [exact G5 | split; [exact G14 | split; [exact G16 | split; [exact G15 |]]]].
    eapply regs_agree_trans; [regs_agree_weaken AG1 | eapply regs_agree_trans; [regs_agree_weaken AG2 | regs_agree_weaken AG3]].
Qed.

Lemma sfr_head : forall regs m (sel data row i sy sx cy : Z),
  (1 <= sel)%Z -> (sel + 32 < 2 ^ 64)%Z -> (1 <= data)%Z -> (data + 8 * sy < 2 ^ 64)%Z -> (data mod 8 = 0)%Z ->
  (1 <= row)%Z -> (row + 4 * sx < 2 ^ 64)%Z -> (row mod 4 = 0)%Z ->
  (0 <= i < sy)%Z -> (sy <= K)%Z -> (1 <= sx <= K)%Z -> (0 <= cy < sy)%Z ->
  rdn SEGS m (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 data) ->
  rdn SEGS m (Z_to_bv 64 (data + 8 * i)) 8 = Some (Z_to_le_bytes 8 row) ->
  getr regs 10 = Z_to_bv 64 sel -> getr regs 6 = Z_to_bv 64 i -> getr regs 8 = Z_to_bv 64 sx -> getr regs 13 = Z_to_bv 64 sx ->
  getr regs 28 = Z_to_bv 64 cy ->
  exists regs',
    msteps SEGS (mkst regs (0xa566c : word) m rom) (mkst regs' (0xa56f8 : word) m rom)
    /\ getr regs' 18 = Z_to_bv 64 0 /\ getr regs' 1 = Z_to_bv 64 (row + 4 * 0) /\ getr regs' 26 = Z_to_bv 64 (sx - 0)
    /\ getr regs' 27 = Z_to_bv 64 (row + 4 * 0) /\ getr regs' 19 = Z_to_bv 64 row /\ getr regs' 24 = Z_to_bv 64 1 /\ getr regs' 25 = Z_to_bv 64 1
    /\ getr regs' 22 = Z_to_bv 64 0 /\ getr regs' 23 = Z_to_bv 64 0 /\ getr regs' 20 = Z_to_bv 64 (cy - i) /\ getr regs' 21 = Z_to_bv 64 (i - cy)
    /\ regs_agree (fun r => In r [1; 7; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
Proof.
  intros regs m sel data row i sy sx cy Hsel Hsel' Hd Hd' ALd Hr Hr' ALr Hi Hsy Hsx Hcy RD RR H10 H6 H8 H13 H28.
  assert (ALd8 : ((data + 8 * i) mod 8 = 0)%Z) by (rewrite Z.mul_comm, Z_mod_plus_full; exact ALd).
  eexists. split.
  - stepb_ft F_a566c D_a566c ltac:(condZ).
    stepLD F_a5670 D_a5670 (Z_to_le_bytes 8 data) (Z_to_bv 64 data) ltac:(addr_norm; exact RD) ltac:(apply lez8; lia).
    stepiv F_a5674 D_a5674 (Z_to_bv 64 (8 * i)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 3)%Z with 8%Z; lia).
    zv F_a5678 D_a5678 (Z_to_bv 64 (data + 8 * i)).
    snez1 F_a567c D_a567c.
    seqz0 F_a5680 D_a5680.
    stepb_ft F_a5684 D_a5684 ltac:(condR).
    stepb_ft F_a5688 D_a5688 ltac:(condZ).
    stepb_ft F_a568c D_a568c ltac:(condZ).
    guard8 F_a5690 D_a5690 ALd8.
    stepb_ft F_a5694 D_a5694 ltac:(condR).
    zv F_a5698 D_a5698 (Z_to_bv 64 0).
    sxw F_a569c D_a569c (Z_to_bv 64 i).
    stepLD F_a56a0 D_a56a0 (Z_to_le_bytes 8 row) (Z_to_bv 64 row) ltac:(addr_norm; exact RR) ltac:(apply lez8; lia).
    zv F_a56a4 D_a56a4 (Z_to_bv 64 (cy - i)).
    subwv F_a56a8 D_a56a8 (Z_to_bv 64 (cy - i)).
    zv F_a56ac D_a56ac (Z_to_bv 64 (i - cy)).
    subwv F_a56b0 D_a56b0 (Z_to_bv 64 (i - cy)).
    xor0 F_a56b4 D_a56b4.
    xor0 F_a56b8 D_a56b8.
    sltu00 F_a56bc D_a56bc.
    sltu00 F_a56c0 D_a56c0.
    snez1 F_a56c4 D_a56c4.
    guard4 F_a56c8 D_a56c8 ALr.
    zlit F_a56cc D_a56cc (Z_to_bv 64 1).
    zlit F_a56d0 D_a56d0 (Z_to_bv 64 1).
    zv F_a56d4 D_a56d4 (Z_to_bv 64 sx).
    zv F_a56d8 D_a56d8 (Z_to_bv 64 row).
    zv F_a56dc D_a56dc (Z_to_bv 64 row).
    sn F_a56e0 D_a56e0.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (f_equal; lia). solve_regs_agree.
Qed.

Lemma sfr_tail_c : forall regs m (i sy : Z), (0 <= i)%Z -> (i + 1 < sy)%Z -> (sy <= K)%Z ->
  getr regs 6 = Z_to_bv 64 i -> getr regs 9 = Z_to_bv 64 2147483647 -> getr regs 31 = Z_to_bv 64 sy ->
  exists regs', msteps SEGS (mkst regs (0xa5784 : word) m rom) (mkst regs' (0xa566c : word) m rom)
    /\ getr regs' 6 = Z_to_bv 64 (i + 1) /\ regs_agree (fun r => In r [6]%list) regs regs'.
Proof.
  intros regs m i sy Hi Hi1 Hsy H6 H9 H31. eexists. split.
  - stepb_ft F_a5784 D_a5784 ltac:(condZ).
    zv F_a5788 D_a5788 (Z_to_bv 64 (i + 1)).
    stepb_tk F_a578c D_a578c ltac:(condZ).
    apply mst_refl.
  - split; [gres; pin; reflexivity | solve_regs_agree].
Qed.

Lemma sfr_tail_e : forall regs m (i sy : Z), (0 <= i)%Z -> (i + 1 = sy)%Z -> (sy <= K)%Z ->
  getr regs 6 = Z_to_bv 64 i -> getr regs 9 = Z_to_bv 64 2147483647 -> getr regs 31 = Z_to_bv 64 sy ->
  exists regs', msteps SEGS (mkst regs (0xa5784 : word) m rom) (mkst regs' (0xa5838 : word) m rom)
    /\ regs_agree (fun r => In r [6]%list) regs regs'.
Proof.
  intros regs m i sy Hi Hi1 Hsy H6 H9 H31. eexists. split.
  - stepb_ft F_a5784 D_a5784 ltac:(condZ).
    zv F_a5788 D_a5788 (Z_to_bv 64 (i + 1)).
    stepb_ft F_a578c D_a578c ltac:(condZ).
    sn F_a5790 D_a5790.
    apply mst_refl.
  - solve_regs_agree.
Qed.

Lemma sfr_loop : forall (n : nat) regs m (sel data i sy sx cy cx y0 y1 y2 y3 : Z) (rows : Z -> Z),
  (1 <= sel)%Z -> (sel + 32 < 2 ^ 64)%Z -> (1 <= data)%Z -> (data + 8 * sy < 2 ^ 64)%Z -> (data mod 8 = 0)%Z ->
  (0 <= i)%Z -> (i + Z.of_nat n = sy - 1)%Z -> (sy <= K)%Z -> (1 <= sx <= K)%Z -> (0 <= cx < sx)%Z -> (0 <= cy < sy)%Z ->
  inm y0 -> inm y1 -> inm y2 -> inm y3 ->
  rdn SEGS m (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 data) ->
  (forall i', (i <= i' < sy)%Z ->
     (1 <= rows i')%Z /\ (rows i' + 4 * sx < 2 ^ 64)%Z /\ (rows i' mod 4 = 0)%Z /\
     rdn SEGS m (Z_to_bv 64 (data + 8 * i')) 8 = Some (Z_to_le_bytes 8 (rows i')) /\
     (forall j', (0 <= j' < sx)%Z -> exists bs, rdn SEGS m (Z_to_bv 64 (rows i' + 4 * j')) 4 = Some bs)) ->
  getr regs 10 = Z_to_bv 64 sel -> getr regs 6 = Z_to_bv 64 i -> getr regs 8 = Z_to_bv 64 sx -> getr regs 13 = Z_to_bv 64 sx ->
  getr regs 9 = Z_to_bv 64 2147483647 -> getr regs 28 = Z_to_bv 64 cy -> getr regs 29 = Z_to_bv 64 cx -> getr regs 30 = Z_to_bv 64 1 ->
  getr regs 31 = Z_to_bv 64 sy ->
  getr regs 5 = Z_to_bv 64 y0 -> getr regs 14 = Z_to_bv 64 y1 -> getr regs 16 = Z_to_bv 64 y2 -> getr regs 15 = Z_to_bv 64 y3 ->
  exists regs' y0' y1' y2' y3',
    msteps SEGS (mkst regs (0xa566c : word) m rom) (mkst regs' (0xa5838 : word) m rom)
    /\ inm y0' /\ inm y1' /\ inm y2' /\ inm y3'
    /\ getr regs' 5 = Z_to_bv 64 y0' /\ getr regs' 14 = Z_to_bv 64 y1' /\ getr regs' 16 = Z_to_bv 64 y2' /\ getr regs' 15 = Z_to_bv 64 y3'
    /\ regs_agree (fun r => In r [1; 5; 6; 7; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
Proof.
  induction n as [|n IH]; intros regs m sel data i sy sx cy cx y0 y1 y2 y3 rows Hsel Hsel' Hd Hd' ALd Hi Hn Hsy Hsx Hcx Hcy
    Hy0 Hy1 Hy2 Hy3 RD HR H10 H6 H8 H13 H9 H28 H29 H30 H31 H5 H14 H16 H15;
    destruct (HR i ltac:(lia)) as (Hr1 & Hr2 & Hr3 & RR & RB);
    destruct (sfr_head regs m sel data (rows i) i sy sx cy Hsel Hsel' Hd Hd' ALd Hr1 Hr2 Hr3 ltac:(lia) Hsy Hsx Hcy RD RR H10 H6 H8 H13 H28)
      as (r1 & S1 & A18 & A1 & A26 & A27 & A19 & A24 & A25 & A22 & A23 & A20 & A21 & AG1);
    destruct (sfi_loop (Z.to_nat (sx - 1)) r1 m (rows i) 0 sx cx (cy - i) (i - cy) y0 y1 y2 y3 Hr1 Hr2 ltac:(lia) ltac:(lia) ltac:(lia) Hcx
      ltac:(lia) ltac:(lia) Hy0 Hy1 Hy2 Hy3 ltac:(intros j' Hj'; apply RB; lia) A18 A1 A26 A27 A19 A24 A25 ltac:(byag) A22 A23 ltac:(byag)
      A20 A21 ltac:(byag) ltac:(byag) ltac:(byag) ltac:(byag))
      as (r2 & z0 & z1 & z2 & z3 & S2 & Hz0 & Hz1 & Hz2 & Hz3 & E5 & E14 & E16 & E15 & AG2).
  - destruct (sfr_tail_e r2 m i sy Hi ltac:(lia) Hsy ltac:(byag) ltac:(byag) ltac:(byag)) as (r3 & S3 & AG3).
    exists r3, z0, z1, z2, z3. split; [eapply msteps_trans; [exact S1 | eapply msteps_trans; [exact S2 | exact S3]] |].
    split; [lia | split; [lia | split; [lia | split; [lia |]]]].
    split; [byag | split; [byag | split; [byag | split; [byag |]]]].
    eapply regs_agree_trans; [regs_agree_weaken AG1 | eapply regs_agree_trans; [regs_agree_weaken AG2 | regs_agree_weaken AG3]].
  - destruct (sfr_tail_c r2 m i sy Hi ltac:(lia) Hsy ltac:(byag) ltac:(byag) ltac:(byag)) as (r3 & S3 & F6 & AG3).
    destruct (IH r3 m sel data (i + 1)%Z sy sx cy cx z0 z1 z2 z3 rows Hsel Hsel' Hd Hd' ALd ltac:(lia) ltac:(lia) Hsy Hsx Hcx Hcy
      Hz0 Hz1 Hz2 Hz3 RD ltac:(intros i' Hi'; apply HR; lia) ltac:(byag) F6 ltac:(byag) ltac:(byag) ltac:(byag) ltac:(byag)
      ltac:(byag) ltac:(byag) ltac:(byag) ltac:(byag) ltac:(byag) ltac:(byag) ltac:(byag))
      as (r4 & w0 & w1 & w2 & w3 & S4 & Hw0 & Hw1 & Hw2 & Hw3 & G5 & G14 & G16 & G15 & AG4).
    exists r4, w0, w1, w2, w3.
    split; [eapply msteps_trans; [exact S1 | eapply msteps_trans; [exact S2 | eapply msteps_trans; [exact S3 | exact S4]]] |].
    split; [lia | split; [lia | split; [lia | split; [lia |]]]].
    split; [exact G5 | split; [exact G14 | split; [exact G16 | split; [exact G15 |]]]].
    eapply regs_agree_trans; [regs_agree_weaken AG1 | eapply regs_agree_trans; [regs_agree_weaken AG2 |
      eapply regs_agree_trans; [regs_agree_weaken AG3 | regs_agree_weaken AG4]]].
Qed.

Lemma sf_exit : forall regs regs0 m (s a1 a2 a3 a4 y0 y1 y2 y3 : Z) (ret : word),
  (128 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> inm y0 -> inm y1 -> inm y2 -> inm y3 ->
  (s <= a1)%Z -> (a1 + 4 < 2 ^ 64)%Z -> (s <= a2)%Z -> (a2 + 4 < 2 ^ 64)%Z ->
  (s <= a3)%Z -> (a3 + 4 < 2 ^ 64)%Z -> (s <= a4)%Z -> (a4 + 4 < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 a1) 4 = true -> store_ok SEGS m (Z_to_bv 64 a2) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 a3) 4 = true -> store_ok SEGS m (Z_to_bv 64 a4) 4 = true ->
  getr regs 2 = Z_to_bv 64 (s - 128) -> getr regs 11 = Z_to_bv 64 a1 -> getr regs 12 = Z_to_bv 64 a2 ->
  getr regs 5 = Z_to_bv 64 y0 -> getr regs 14 = Z_to_bv 64 y1 -> getr regs 16 = Z_to_bv 64 y2 -> getr regs 15 = Z_to_bv 64 y3 ->
  exists regs',
    msteps SEGS (mkst regs (0xa5838 : word) (O23LeptSelFMT.SFZ (FRS m s ret regs0 a3 a4) a1 a2 a3 a4) rom)
      (mkst regs' ret (O23LeptSelFMT.SFR (O23LeptSelFMT.SFZ (FRS m s ret regs0 a3 a4) a1 a2 a3 a4) a1 a2 a3 a4 y0 y1 y2 y3) rom)
    /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 1 = ret
    /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18 /\ getr regs' 19 = getr regs0 19
    /\ getr regs' 20 = getr regs0 20 /\ getr regs' 21 = getr regs0 21 /\ getr regs' 22 = getr regs0 22 /\ getr regs' 23 = getr regs0 23
    /\ getr regs' 24 = getr regs0 24 /\ getr regs' 25 = getr regs0 25 /\ getr regs' 26 = getr regs0 26 /\ getr regs' 27 = getr regs0 27
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
Proof.
  intros regs regs0 m s a1 a2 a3 a4 y0 y1 y2 y3 ret Hs Hs64 Hret Hy0 Hy1 Hy2 Hy3 Ha1 Ha1' Ha2 Ha2' Ha3 Ha3' Ha4 Ha4'
    S1 S2 S3 S4 H2 H11 H12 H5 H14 H16 H15.
  eexists. split.
  - unfold O23LeptSelFMT.SFR, O23LeptSelFMT.SFZ, O23LeptSelFMT.wr4, FRS.
    zv F_a5838 D_a5838 (Z_to_bv 64 0).
    stepST F_a583c D_a583c (Z_to_bv 64 a1) (Z_to_bv 64 y0) ltac:(sok_in S1).
    stepST F_a5840 D_a5840 (Z_to_bv 64 a2) (Z_to_bv 64 y1) ltac:(sok_in S2).
    stepLD8 F_a5844 D_a5844 (Z_to_bv 64 a3).
    stepST F_a5848 D_a5848 (Z_to_bv 64 a3) (Z_to_bv 64 y2) ltac:(sok_in S3).
    stepLD8 F_a584c D_a584c (Z_to_bv 64 a4).
    stepST F_a5850 D_a5850 (Z_to_bv 64 a4) (Z_to_bv 64 y3) ltac:(sok_in S4).
    stepLD8 F_a5854 D_a5854 ret.
    stepLD8 F_a5858 D_a5858 (getr regs0 8).
    stepLD8 F_a585c D_a585c (getr regs0 9).
    stepLD8 F_a5860 D_a5860 (getr regs0 18).
    stepLD8 F_a5864 D_a5864 (getr regs0 19).
    stepLD8 F_a5868 D_a5868 (getr regs0 20).
    stepLD8 F_a586c D_a586c (getr regs0 21).
    stepLD8 F_a5870 D_a5870 (getr regs0 22).
    stepLD8 F_a5874 D_a5874 (getr regs0 23).
    stepLD8 F_a5878 D_a5878 (getr regs0 24).
    stepLD8 F_a587c D_a587c (getr regs0 25).
    stepLD8 F_a5880 D_a5880 (getr regs0 26).
    stepLD8 F_a5884 D_a5884 (getr regs0 27).
    zv F_a5888 D_a5888 (Z_to_bv 64 s).
    stepret F_a588c D_a588c ret ltac:(reflexivity).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

End Segs.

Lemma FRS_low : forall m s ret regs (a1 a2 a3 a4 : Z) (x : word), (128 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (s <= a1)%Z -> (a1 + 4 < 2 ^ 64)%Z -> (s <= a2)%Z -> (a2 + 4 < 2 ^ 64)%Z ->
  (s <= a3)%Z -> (a3 + 4 < 2 ^ 64)%Z -> (s <= a4)%Z -> (a4 + 4 < 2 ^ 64)%Z ->
  (bv_unsigned x < s - 128)%Z -> O23LeptSelFMT.SFZ (FRS m s ret regs a3 a4) a1 a2 a3 a4 x = m x.
Proof.
  intros m s ret regs a1 a2 a3 a4 x Hs Hs64 Ha1 Ha1' Ha2 Ha2' Ha3 Ha3' Ha4 Ha4' Hx.
  unfold O23LeptSelFMT.SFZ, O23LeptSelFMT.wr4, FRS.
  rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; try lia.
  reflexivity.
Qed.

Lemma SFF_out : forall m s ret regs (a1 a2 a3 a4 y0 y1 y2 y3 : Z) (x : word), (128 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (s <= a1)%Z -> (a1 + 4 < 2 ^ 64)%Z -> (s <= a2)%Z -> (a2 + 4 < 2 ^ 64)%Z ->
  (s <= a3)%Z -> (a3 + 4 < 2 ^ 64)%Z -> (s <= a4)%Z -> (a4 + 4 < 2 ^ 64)%Z ->
  ~ (s - 128 <= bv_unsigned x < s)%Z ->
  O23LeptSelFMT.SFR (O23LeptSelFMT.SFZ (FRS m s ret regs a3 a4) a1 a2 a3 a4) a1 a2 a3 a4 y0 y1 y2 y3 x
  = O23LeptSelFMT.SFR m a1 a2 a3 a4 y0 y1 y2 y3 x.
Proof.
  intros m s ret regs a1 a2 a3 a4 y0 y1 y2 y3 x Hs Hs64 Ha1 Ha1' Ha2 Ha2' Ha3 Ha3' Ha4 Ha4' Hx.
  unfold O23LeptSelFMT.SFR, O23LeptSelFMT.wr4.
  apply O23LeptSelFMT.wb_eq_out; [rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
  intros X4. rewrite length_N_to_le_bytes, u_Z2bv in X4 by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in X4.
  apply O23LeptSelFMT.wb_eq_out; [rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
  intros X3. rewrite length_N_to_le_bytes, u_Z2bv in X3 by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in X3.
  apply O23LeptSelFMT.wb_eq_out; [rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
  intros X2. rewrite length_N_to_le_bytes, u_Z2bv in X2 by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in X2.
  apply O23LeptSelFMT.wb_eq_out; [rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
  intros X1. rewrite length_N_to_le_bytes, u_Z2bv in X1 by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in X1.
  unfold O23LeptSelFMT.SFZ, O23LeptSelFMT.wr4, FRS.
  rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; try lia.
  reflexivity.
Qed.

Definition SFMT_STACK : Z := 128.

Section W.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma sf_blk_rdn : forall C A m md (p : word) (n a : Z) (k : nat), Cok C -> W C A m md -> live A p = Some n ->
  (u p <= a)%Z -> (a + Z.of_nat k <= u p + n)%Z -> exists bs, rdn SEGS m (Z_to_bv 64 a) k = Some bs.
Proof.
  intros C A m md p n a k CK HW Lp Ha Hak.
  destruct k as [|k']; [exists []; reflexivity|].
  destruct (blk_range C A m md p n CK HW Lp ltac:(lia)) as [G TOP].
  pose proof CK as [T1 T2 T3 T4 T5]. pose proof (u64_range (c_sp0 C)) as Usp. pose proof LSTK_val as LV.
  set (f := fun i : nat => match m (Z_to_bv 64 (a + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end).
  assert (L : length (map f (seq 0 (S k'))) = S k') by (rewrite length_map, length_seq; reflexivity).
  assert (BA : bytes_at m a (map f (seq 0 (S k')))).
  { intros i Hi. rewrite L in Hi.
    rewrite nth_indep with (d' := f 0%nat) by (rewrite L; lia).
    rewrite map_nth, seq_nth by lia. unfold f. cbn [Nat.add]. rewrite Z2Nat.id by lia.
    destruct (m (Z_to_bv 64 (a + i))) eqn:E; [reflexivity|].
    exfalso. destruct (blk_byte C A m md p n (Z_to_bv 64 (a + i)) CK HW Lp ltac:(rewrite u_Z2bv by lia; lia)) as (_ & D & _).
    exact (D E). }
  pose proof (bytes_at_rdn SEGS m a (map f (seq 0 (S k'))) ltac:(lia) ltac:(rewrite L; lia) BA) as R.
  rewrite L in R. exists (map f (seq 0 (S k'))). exact R.
Qed.

Lemma W_SFR : forall C A m md (a1 a2 a3 a4 y0 y1 y2 y3 : Z), Cok C -> W C A m md ->
  (c_top C - LSTK <= a1)%Z -> (a1 + 4 <= c_top C)%Z -> (c_top C - LSTK <= a2)%Z -> (a2 + 4 <= c_top C)%Z ->
  (c_top C - LSTK <= a3)%Z -> (a3 + 4 <= c_top C)%Z -> (c_top C - LSTK <= a4)%Z -> (a4 + 4 <= c_top C)%Z ->
  (0 <= c_top C - LSTK)%Z ->
  W C A (O23LeptSelFMT.SFR m a1 a2 a3 a4 y0 y1 y2 y3) md.
Proof.
  intros C A m md a1 a2 a3 a4 y0 y1 y2 y3 CK HW B1 B1' B2 B2' B3 B3' B4 B4' B0.
  pose proof CK as [T1 T2 T3 T4 T5]. pose proof (u64_range (c_sp0 C)) as Usp.
  unfold O23LeptSelFMT.SFR, O23LeptSelFMT.wr4.
  repeat (apply W_store_win; [exact CK | | rewrite u_Z2bv by lia; lia
    | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
  exact HW.
Qed.

Lemma W_FRS : forall C A m md (s : Z) ret regs (a1 a2 a3 a4 : Z), Cok C -> W C A m md ->
  (c_top C - LSTK + 128 <= s)%Z -> (s <= c_top C)%Z -> (0 <= c_top C - LSTK)%Z ->
  (s <= a1)%Z -> (a1 + 4 <= c_top C)%Z -> (s <= a2)%Z -> (a2 + 4 <= c_top C)%Z ->
  (s <= a3)%Z -> (a3 + 4 <= c_top C)%Z -> (s <= a4)%Z -> (a4 + 4 <= c_top C)%Z ->
  W C A (O23LeptSelFMT.SFZ (FRS m s ret regs a3 a4) a1 a2 a3 a4) md.
Proof.
  intros C A m md s ret regs a1 a2 a3 a4 CK HW Hlo Hhi B0 B1 B1' B2 B2' B3 B3' B4 B4'.
  pose proof CK as [T1 T2 T3 T4 T5]. pose proof (u64_range (c_sp0 C)) as Usp.
  unfold O23LeptSelFMT.SFZ, O23LeptSelFMT.wr4, FRS.
  repeat (apply W_store_win; [exact CK | | rewrite u_Z2bv by lia; lia
    | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
  exact HW.
Qed.

Lemma sf_rows : forall C A m md M sel (v : selv), Cok C -> W C A m md -> sel_at (alloc_top (c_vm C)) A m sel v ->
  (forall x : word, (u x < alloc_top (c_vm C))%Z -> M x = m x) ->
  forall i', (0 <= i' < v_sy v)%Z ->
     (1 <= v_rows v i')%Z /\ (v_rows v i' + 4 * v_sx v < 2 ^ 64)%Z /\ (v_rows v i' mod 4 = 0)%Z /\
     rdn SEGS M (Z_to_bv 64 (v_data v + 8 * i')) 8 = Some (Z_to_le_bytes 8 (v_rows v i')) /\
     (forall j', (0 <= j' < v_sx v)%Z -> exists bs, rdn SEGS M (Z_to_bv 64 (v_rows v i' + 4 * j')) 4 = Some bs).
Proof.
  intros C A m md M sel v CK HW SA LOW i' Hi'.
  pose proof CK as [T1 T2 T3 T4 T5]. pose proof (u64_range (c_sp0 C)) as Usp. pose proof LSTK_val as LV.
  destruct SA as (Hsy & Hsx & _ & _ & _ & Bdat & _ & _ & HR & _).
  destruct Bdat as (Bd1 & Bd2 & Bd3).
  destruct (HR i' Hi') as (Brow & Lrow & _ & _ & BA). destruct Brow as (Br1 & Br2 & Br3). clear HR.
  split; [lia | split; [lia | split; [exact (al16_mod4 _ Br3) | split]]].
  - pose proof (bytes_at_rdn SEGS m (v_data v + 8 * i') (Z_to_le_bytes 8 (v_rows v i')) ltac:(lia)
      ltac:(rewrite length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) BA) as R.
    rewrite length_Z_to_le_bytes in R.
    rewrite (rdn_ext SEGS 8 M m (Z_to_bv 64 (v_data v + 8 * i'))); [exact R | rewrite u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    intros x Hx. apply LOW. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. lia.
  - intros j' Hj'.
    destruct (sf_blk_rdn C A m md _ (4 * v_sx v) (v_rows v i' + 4 * j') 4 CK HW Lrow ltac:(rewrite u_Z2bv by lia; lia)
      ltac:(rewrite u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as [bs R].
    exists bs.
    rewrite (rdn_ext SEGS 4 M m (Z_to_bv 64 (v_rows v i' + 4 * j'))); [exact R | rewrite u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    intros x Hx. apply LOW. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. lia.
Qed.

(* [comment removed for export] *)
Theorem selFindMaxTranslations_W : forall C A m md regs (s sel a1 a2 a3 a4 : Z) (v : selv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SFMT_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 sel ->
  getr regs 11 = Z_to_bv 64 a1 -> getr regs 12 = Z_to_bv 64 a2 -> getr regs 13 = Z_to_bv 64 a3 -> getr regs 14 = Z_to_bv 64 a4 ->
  (s <= a1)%Z -> (a1 + 4 <= c_top C)%Z -> (s <= a2)%Z -> (a2 + 4 <= c_top C)%Z ->
  (s <= a3)%Z -> (a3 + 4 <= c_top C)%Z -> (s <= a4)%Z -> (a4 + 4 <= c_top C)%Z -> 
  (a1 mod 4 = 0)%Z -> (a2 mod 4 = 0)%Z -> (a3 mod 4 = 0)%Z -> (a4 mod 4 = 0)%Z ->
  sel_at (alloc_top (c_vm C)) A m sel v -> (0 <= v_cx v < v_sx v)%Z -> (0 <= v_cy v < v_sy v)%Z ->
  (forall m' regs' (y0 y1 y2 y3 : Z), W C A m' md -> cs_kept regs regs' -> POSTM C A s (O23LeptSelFMT.SFR m a1 a2 a3 a4 y0 y1 y2 y3) m' ->
     (0 <= y0 <= 10000)%Z -> (0 <= y1 <= 10000)%Z -> (0 <= y2 <= 10000)%Z -> (0 <= y3 <= 10000)%Z ->
     getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0xa5590 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s sel a1 a2 a3 a4 v ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14
    Ha1 Ha1' Ha2 Ha2' Ha3 Ha3' Ha4 Ha4' AL1 AL2 AL3 AL4 SA Hcx Hcy HK.
  pose proof CK as [T1 T2 T3 T4 T5]. pose proof (u64_range (c_sp0 C)) as Usp. pose proof LSTK_val as LV.
  unfold SFMT_STACK in Hlo.
  pose proof SA as SA'. destruct SA' as (Hsy & Hsx & Bsel & _ & RC & Bdat & _ & _ & _ & _).
  destruct Bsel as (Bs1 & Bs2 & Bs3). destruct Bdat as (Bd1 & Bd2 & Bd3).
  assert (ALs : (sel mod 8 = 0)%Z) by (exact (al16_mod8 _ Bs3)).
  assert (ALd : (v_data v mod 8 = 0)%Z) by (exact (al16_mod8 _ Bd3)).
  pose proof (W_sok_win C A m md (s - 128) 128 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  pose proof (W_sok_win C A m md a1 4 CK HW ltac:(lia) ltac:(cbn; lia)) as S1.
  pose proof (W_sok_win C A m md a2 4 CK HW ltac:(lia) ltac:(cbn; lia)) as S2.
  pose proof (W_sok_win C A m md a3 4 CK HW ltac:(lia) ltac:(cbn; lia)) as S3.
  pose proof (W_sok_win C A m md a4 4 CK HW ltac:(lia) ltac:(cbn; lia)) as S4.
  assert (LOW : forall x : word, (u x < alloc_top (c_vm C))%Z -> O23LeptSelFMT.SFZ (FRS m s ret regs a3 a4) a1 a2 a3 a4 x = m x)
    by (intros x Hx; apply FRS_low; lia).
  assert (RC1 : RECat (O23LeptSelFMT.SFZ (FRS m s ret regs a3 a4) a1 a2 a3 a4) sel
                  (sel_flds (v_sy v) (v_sx v) (v_cy v) (v_cx v) (v_data v) (v_name v))).
  { apply (RECat_frame m); [exact RC|]. intros x Hx.
    change (Z.of_nat (flds_len (sel_flds (v_sy v) (v_sx v) (v_cy v) (v_cx v) (v_data v) (v_name v)))) with 32%Z in Hx.
    apply LOW. lia. }
  pose proof (REC_rd' SEGS _ sel _ 4 8 (Z_to_bv 64 (sel + 16)) (v_data v) RC1 ltac:(cbn; lia) eq_refl ltac:(f_equal; cbn; lia) eq_refl) as RD1.
  pose proof (sf_rows C A m md _ sel v CK HW SA LOW) as ROWS.
  destruct (sf_entry al_rom regs m s sel a1 a2 a3 a4 (v_sy v) (v_sx v) (v_cy v) (v_cx v) (v_data v) (v_name v) ret
    ltac:(lia) ltac:(lia) Bs1 ALs RC1 Hsy Hsx Hcx Hcy Ha1 ltac:(lia) Ha2 ltac:(lia) Ha3 ltac:(lia) Ha4 ltac:(lia)
    AL1 AL2 AL3 AL4 SOK S1 S2 S3 S4 H1 H2 H10 H11 H12 H13 H14)
    as (r1 & RUN1 & E2 & E10 & E11 & E12 & E13 & E8 & E9 & E6 & E5 & E14 & E15 & E16 & E28 & E29 & E30 & E31 & AG1).
  destruct (sfr_loop al_rom (Z.to_nat (v_sy v - 1)) r1 _ sel (v_data v) 0 (v_sy v) (v_sx v) (v_cy v) (v_cx v) 0 0 0 0 (v_rows v)
    Bs1 ltac:(lia) Bd1 ltac:(lia) ALd ltac:(lia) ltac:(lia) ltac:(lia) Hsx Hcx Hcy ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    RD1 ROWS E10 E6 E8 E13 E9 E28 E29 E30 E31 E5 E14 E16 E15)
    as (r2 & y0 & y1 & y2 & y3 & RUN2 & Hy0 & Hy1 & Hy2 & Hy3 & F5 & F14 & F16 & F15 & AG2).
  destruct (sf_exit al_rom r2 regs m s a1 a2 a3 a4 y0 y1 y2 y3 ret ltac:(lia) ltac:(lia) Hret Hy0 Hy1 Hy2 Hy3
    Ha1 ltac:(lia) Ha2 ltac:(lia) Ha3 ltac:(lia) Ha4 ltac:(lia) S1 S2 S3 S4 ltac:(byag) ltac:(byag) ltac:(byag) F5 F14 F16 F15)
    as (r3 & RUN3 & G2 & G10 & G1 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW))
    | eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] |].
  apply (HK _ r3 y0 y1 y2 y3).
  - apply W_SFR; [exact CK | apply W_FRS; [exact CK | exact HW | lia ..] | lia ..].
  - apply cs_kept_intro.
    + rewrite G2, H2. reflexivity.
    + rewrite (AG3 3), (AG2 3), (AG1 3) by notin_list. reflexivity.
    + rewrite (AG3 4), (AG2 4), (AG1 4) by notin_list. reflexivity.
    + exact G8.
    + exact G9.
    + exact G18.
    + exact G19.
    + exact G20.
    + exact G21.
    + exact G22.
    + exact G23.
    + exact G24.
    + exact G25.
    + exact G26.
    + exact G27.
  - apply (POSTM_range C A (O23LeptSelFMT.SFR m a1 a2 a3 a4 y0 y1 y2 y3) md _ (s - 128) s s CK).
    + apply W_SFR; [exact CK | exact HW | lia ..].
    + intros x Hx. apply SFF_out; lia.
    + lia.
    + lia.
    + lia.
  - exact Hy0.
  - exact Hy1.
  - exact Hy2.
  - exact Hy3.
  - exact G10.
Qed.

End W.
