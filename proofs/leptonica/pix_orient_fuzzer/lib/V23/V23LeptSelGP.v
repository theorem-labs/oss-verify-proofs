(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptRecs LeptSel LeptArith LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptSelGP.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptUb V23_code_port_selgp.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation "'u'" := bv_unsigned (only parsing).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
Ltac condR := pin; first [ apply c_eq_refl | vm_compute; reflexivity ].

Lemma wr4_rd_out : forall m a v (b : Z) (n : nat), (0 <= a)%Z -> (a + 4 <= 2 ^ 64)%Z -> (0 <= b)%Z -> (b + Z.of_nat n < 2 ^ 64)%Z ->
  (b + Z.of_nat n <= a \/ a + 4 <= b)%Z -> rdn SEGS (wr4 m a v) (Z_to_bv 64 b) n = rdn SEGS m (Z_to_bv 64 b) n.
Proof.
  intros m a v b n Ha Ha4 Hb Hbn D. unfold wr4. apply rdn_wbytes_out_Z.
  rewrite length_N_to_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.
Lemma wr4_rd_hit : forall m a v, (0 <= a)%Z -> (a + 4 <= 2 ^ 64)%Z -> (0 <= v < 2 ^ 32)%Z ->
  rdn SEGS (wr4 m a v) (Z_to_bv 64 a) 4 = Some (Z_to_le_bytes 4 v).
Proof.
  intros m a v Ha Ha4 Hv. unfold wr4. rewrite rdn_wbytes_hit4 by (rewrite u_Z2bv by lia; lia).
  rewrite w2b_Z by lia. reflexivity.
Qed.

Lemma SGP4_rd : forall m a1 a2 a3 a4 sy sx cy cx, cell_ok a1 -> cell_ok a2 -> cell_ok a3 -> cell_ok a4 ->
  cell_apart a1 a2 -> cell_apart a1 a3 -> cell_apart a1 a4 -> cell_apart a2 a3 -> cell_apart a2 a4 -> cell_apart a3 a4 ->
  (0 <= sy < 2 ^ 32)%Z -> (0 <= sx < 2 ^ 32)%Z -> (0 <= cy < 2 ^ 32)%Z -> (0 <= cx < 2 ^ 32)%Z ->
  rdn SEGS (SGP4 m a1 a2 a3 a4 sy sx cy cx) (Z_to_bv 64 a1) 4 = Some (Z_to_le_bytes 4 sy) /\
  rdn SEGS (SGP4 m a1 a2 a3 a4 sy sx cy cx) (Z_to_bv 64 a2) 4 = Some (Z_to_le_bytes 4 sx) /\
  rdn SEGS (SGP4 m a1 a2 a3 a4 sy sx cy cx) (Z_to_bv 64 a3) 4 = Some (Z_to_le_bytes 4 cy) /\
  rdn SEGS (SGP4 m a1 a2 a3 a4 sy sx cy cx) (Z_to_bv 64 a4) 4 = Some (Z_to_le_bytes 4 cx).
Proof.
  intros m a1 a2 a3 a4 sy sx cy cx C1 C2 C3 C4 D12 D13 D14 D23 D24 D34 Hsy Hsx Hcy Hcx.
  unfold cell_ok, cell_apart in *. unfold SGP4.
  split; [| split; [| split]].
  - rewrite (wr4_rd_out _ a4), (wr4_rd_out _ a3), (wr4_rd_out _ a2) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    apply wr4_rd_hit; lia.
  - rewrite (wr4_rd_out _ a4), (wr4_rd_out _ a3) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    apply wr4_rd_hit; lia.
  - rewrite (wr4_rd_out _ a4) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    apply wr4_rd_hit; lia.
  - apply wr4_rd_hit; lia.
Qed.
Lemma SGP2_rd : forall m a1 a2 sy sx, cell_ok a1 -> cell_ok a2 -> cell_apart a1 a2 -> (0 <= sy < 2 ^ 32)%Z -> (0 <= sx < 2 ^ 32)%Z ->
  rdn SEGS (SGP2 m a1 a2 sy sx) (Z_to_bv 64 a1) 4 = Some (Z_to_le_bytes 4 sy) /\
  rdn SEGS (SGP2 m a1 a2 sy sx) (Z_to_bv 64 a2) 4 = Some (Z_to_le_bytes 4 sx).
Proof.
  intros m a1 a2 sy sx C1 C2 D12 Hsy Hsx.
  unfold cell_ok, cell_apart in *. unfold SGP2.
  split.
  - rewrite (wr4_rd_out _ a2) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    apply wr4_rd_hit; lia.
  - apply wr4_rd_hit; lia.
Qed.

Section Segs.
  Context {fx : FPState}.
  Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma sgp4_run : forall regs m (sel a1 a2 a3 a4 sy sx cy cx data name : Z) (ret : word),
    RECat m sel (sel_flds sy sx cy cx data name) -> (1 <= sel)%Z ->
    (0 <= sy < 2 ^ 31)%Z -> (0 <= sx < 2 ^ 31)%Z -> (0 <= cy < 2 ^ 31)%Z -> (0 <= cx < 2 ^ 31)%Z ->
    cell_ok a1 -> cell_ok a2 -> cell_ok a3 -> cell_ok a4 ->
    store_ok SEGS m (Z_to_bv 64 a1) 4 = true -> store_ok SEGS m (Z_to_bv 64 a2) 4 = true ->
    store_ok SEGS m (Z_to_bv 64 a3) 4 = true -> store_ok SEGS m (Z_to_bv 64 a4) 4 = true ->
    (sel + 32 <= a1 \/ a1 + 4 <= sel)%Z -> (sel + 32 <= a2 \/ a2 + 4 <= sel)%Z ->
    (sel + 32 <= a3 \/ a3 + 4 <= sel)%Z -> (sel + 32 <= a4 \/ a4 + 4 <= sel)%Z ->
    (sel mod 8 = 0)%Z -> (a1 mod 4 = 0)%Z -> (a2 mod 4 = 0)%Z -> (a3 mod 4 = 0)%Z -> (a4 mod 4 = 0)%Z ->
    getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 sel ->
    getr regs 11 = Z_to_bv 64 a1 -> getr regs 12 = Z_to_bv 64 a2 -> getr regs 13 = Z_to_bv 64 a3 -> getr regs 14 = Z_to_bv 64 a4 ->
    exists regs',
      msteps SEGS (mkst regs (0xa4fd0 : word) m rom) (mkst regs' ret (SGP4 m a1 a2 a3 a4 sy sx cy cx) rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [5; 6; 10; 11; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m sel a1 a2 a3 a4 sy sx cy cx data name ret RC Hsel Hsy Hsx Hcy Hcx C1 C2 C3 C4 S1 S2 S3 S4 D1 D2 D3 D4
      AL0 AL1 AL2 AL3 AL4 H1 Hret H10 H11 H12 H13 H14.
    unfold cell_ok in C1, C2, C3, C4.
    pose proof (RECat_range _ _ _ RC) as [Hs0 Hs32].
    change (Z.of_nat (flds_len (sel_flds sy sx cy cx data name))) with 32%Z in Hs32.
    pose proof (REC_rd' SEGS m sel _ 0 4 (Z_to_bv 64 sel) sy RC ltac:(cbn; lia) eq_refl ltac:(f_equal; cbn; lia) eq_refl) as R0.
    pose proof (REC_rd' SEGS m sel _ 1 4 (Z_to_bv 64 (sel + 4)) sx RC ltac:(cbn; lia) eq_refl ltac:(f_equal; cbn; lia) eq_refl) as R1.
    pose proof (REC_rd' SEGS m sel _ 2 4 (Z_to_bv 64 (sel + 8)) cy RC ltac:(cbn; lia) eq_refl ltac:(f_equal; cbn; lia) eq_refl) as R2.
    pose proof (REC_rd' SEGS m sel _ 3 4 (Z_to_bv 64 (sel + 12)) cx RC ltac:(cbn; lia) eq_refl ltac:(f_equal; cbn; lia) eq_refl) as R3.
    unfold SGP4, wr4. eexists. split.
    - guard4 F_a4fd0 D_a4fd0 AL1.
      stepb_ft F_a4fd4 D_a4fd4 ltac:(condZ).
      stepb_ft F_a4fd8 D_a4fd8 ltac:(condR).
      stepST F_a4fdc D_a4fdc (Z_to_bv 64 a1) (Z_to_bv 64 0) ltac:(sok_in S1).
      guard4 F_a4fe0 D_a4fe0 AL2.
      stepb_ft F_a4fe4 D_a4fe4 ltac:(condZ).
      stepb_ft F_a4fe8 D_a4fe8 ltac:(condR).
      stepST F_a4fec D_a4fec (Z_to_bv 64 a2) (Z_to_bv 64 0) ltac:(sok_in S2).
      guard4 F_a4ff0 D_a4ff0 AL3.
      stepb_ft F_a4ff4 D_a4ff4 ltac:(condZ).
      stepb_ft F_a4ff8 D_a4ff8 ltac:(condR).
      stepST F_a4ffc D_a4ffc (Z_to_bv 64 a3) (Z_to_bv 64 0) ltac:(sok_in S3).
      guard4 F_a5000 D_a5000 AL4.
      stepb_ft F_a5004 D_a5004 ltac:(condZ).
      stepb_ft F_a5008 D_a5008 ltac:(condR).
      stepST F_a500c D_a500c (Z_to_bv 64 a4) (Z_to_bv 64 0) ltac:(sok_in S4).
      stepb_ft F_a5010 D_a5010 ltac:(condZ).
      guard8 F_a5014 D_a5014 AL0.
      stepb_ft F_a5018 D_a5018 ltac:(condZ).
      zv F_a501c D_a501c (Z_to_bv 64 0).
      stepb_ft F_a5020 D_a5020 ltac:(condR).
      stepLD F_a5024 D_a5024 (Z_to_le_bytes 4 sy) (Z_to_bv 64 sy)
        ltac:(addr_norm; rewrite ?Z.add_0_r; repeat rdn_peel1; exact R0) ltac:(apply lez4; lia).
      rewrite ?(v_lw_small sy) by lia.
      stepST F_a5028 D_a5028 (Z_to_bv 64 a1) (Z_to_bv 64 sy) ltac:(sok_in S1).
      stepb_ft F_a502c D_a502c ltac:(condZ).
      zv F_a5030 D_a5030 (Z_to_bv 64 0).
      stepb_ft F_a5034 D_a5034 ltac:(condR).
      stepLD F_a5038 D_a5038 (Z_to_le_bytes 4 sx) (Z_to_bv 64 sx)
        ltac:(addr_norm; repeat rdn_peel1; exact R1) ltac:(apply lez4; lia).
      rewrite ?(v_lw_small sx) by lia.
      stepST F_a503c D_a503c (Z_to_bv 64 a2) (Z_to_bv 64 sx) ltac:(sok_in S2).
      stepb_ft F_a5040 D_a5040 ltac:(condZ).
      zv F_a5044 D_a5044 (Z_to_bv 64 0).
      stepb_ft F_a5048 D_a5048 ltac:(condR).
      stepLD F_a504c D_a504c (Z_to_le_bytes 4 cy) (Z_to_bv 64 cy)
        ltac:(addr_norm; repeat rdn_peel1; exact R2) ltac:(apply lez4; lia).
      rewrite ?(v_lw_small cy) by lia.
      stepST F_a5050 D_a5050 (Z_to_bv 64 a3) (Z_to_bv 64 cy) ltac:(sok_in S3).
      stepb_ft F_a5054 D_a5054 ltac:(condZ).
      zv F_a5058 D_a5058 (Z_to_bv 64 0).
      stepb_ft F_a505c D_a505c ltac:(condR).
      stepLD F_a5060 D_a5060 (Z_to_le_bytes 4 cx) (Z_to_bv 64 cx)
        ltac:(addr_norm; repeat rdn_peel1; exact R3) ltac:(apply lez4; lia).
      rewrite ?(v_lw_small cx) by lia.
      stepST F_a5064 D_a5064 (Z_to_bv 64 a4) (Z_to_bv 64 cx) ltac:(sok_in S4).
      sn F_a5068 D_a5068.
      stepret F_a506c D_a506c ret ltac:(exact H1).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma sgp2_run : forall regs m (sel a1 a2 sy sx cy cx data name : Z) (ret : word),
    RECat m sel (sel_flds sy sx cy cx data name) -> (1 <= sel)%Z ->
    (0 <= sy < 2 ^ 31)%Z -> (0 <= sx < 2 ^ 31)%Z ->
    cell_ok a1 -> cell_ok a2 ->
    store_ok SEGS m (Z_to_bv 64 a1) 4 = true -> store_ok SEGS m (Z_to_bv 64 a2) 4 = true ->
    (sel + 32 <= a1 \/ a1 + 4 <= sel)%Z -> (sel + 32 <= a2 \/ a2 + 4 <= sel)%Z ->
    (sel mod 8 = 0)%Z -> (a1 mod 4 = 0)%Z -> (a2 mod 4 = 0)%Z ->
    getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 sel ->
    getr regs 11 = Z_to_bv 64 a1 -> getr regs 12 = Z_to_bv 64 a2 -> getr regs 13 = Z_to_bv 64 0 -> getr regs 14 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0xa4fd0 : word) m rom) (mkst regs' ret (SGP2 m a1 a2 sy sx) rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [5; 6; 10; 11; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m sel a1 a2 sy sx cy cx data name ret RC Hsel Hsy Hsx C1 C2 S1 S2 D1 D2 AL0 AL1 AL2 H1 Hret H10 H11 H12 H13 H14.
    unfold cell_ok in C1, C2.
    pose proof (RECat_range _ _ _ RC) as [Hs0 Hs32].
    change (Z.of_nat (flds_len (sel_flds sy sx cy cx data name))) with 32%Z in Hs32.
    pose proof (REC_rd' SEGS m sel _ 0 4 (Z_to_bv 64 sel) sy RC ltac:(cbn; lia) eq_refl ltac:(f_equal; cbn; lia) eq_refl) as R0.
    pose proof (REC_rd' SEGS m sel _ 1 4 (Z_to_bv 64 (sel + 4)) sx RC ltac:(cbn; lia) eq_refl ltac:(f_equal; cbn; lia) eq_refl) as R1.
    unfold SGP2, wr4. eexists. split.
    - guard4 F_a4fd0 D_a4fd0 AL1.
      stepb_ft F_a4fd4 D_a4fd4 ltac:(condZ).
      stepb_ft F_a4fd8 D_a4fd8 ltac:(condR).
      stepST F_a4fdc D_a4fdc (Z_to_bv 64 a1) (Z_to_bv 64 0) ltac:(sok_in S1).
      guard4 F_a4fe0 D_a4fe0 AL2.
      stepb_ft F_a4fe4 D_a4fe4 ltac:(condZ).
      stepb_ft F_a4fe8 D_a4fe8 ltac:(condR).
      stepST F_a4fec D_a4fec (Z_to_bv 64 a2) (Z_to_bv 64 0) ltac:(sok_in S2).
      sn F_a4ff0 D_a4ff0.
      stepb_tk F_a4ff4 D_a4ff4 ltac:(condR).
      sn F_a5000 D_a5000.
      stepb_tk F_a5004 D_a5004 ltac:(condR).
      stepb_ft F_a5010 D_a5010 ltac:(condZ).
      guard8 F_a5014 D_a5014 AL0.
      stepb_ft F_a5018 D_a5018 ltac:(condZ).
      zv F_a501c D_a501c (Z_to_bv 64 0).
      stepb_ft F_a5020 D_a5020 ltac:(condR).
      stepLD F_a5024 D_a5024 (Z_to_le_bytes 4 sy) (Z_to_bv 64 sy)
        ltac:(addr_norm; rewrite ?Z.add_0_r; repeat rdn_peel1; exact R0) ltac:(apply lez4; lia).
      rewrite ?(v_lw_small sy) by lia.
      stepST F_a5028 D_a5028 (Z_to_bv 64 a1) (Z_to_bv 64 sy) ltac:(sok_in S1).
      stepb_ft F_a502c D_a502c ltac:(condZ).
      zv F_a5030 D_a5030 (Z_to_bv 64 0).
      stepb_ft F_a5034 D_a5034 ltac:(condR).
      stepLD F_a5038 D_a5038 (Z_to_le_bytes 4 sx) (Z_to_bv 64 sx)
        ltac:(addr_norm; repeat rdn_peel1; exact R1) ltac:(apply lez4; lia).
      rewrite ?(v_lw_small sx) by lia.
      stepST F_a503c D_a503c (Z_to_bv 64 a2) (Z_to_bv 64 sx) ltac:(sok_in S2).
      stepb_tk F_a5040 D_a5040 ltac:(condR).
      stepb_tk F_a5054 D_a5054 ltac:(condR).
      sn F_a509c D_a509c.
      stepret F_a50a0 D_a50a0 ret ltac:(exact H1).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.
