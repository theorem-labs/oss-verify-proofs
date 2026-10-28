(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk PropExec MState.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem MemRange ZdWalkKit ZdCellKit SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface AZ_kx.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.
Notation FSE_INITDS_STACK_A := 16 (only parsing).

Section CANSEC1. Context {rc : runConstT}.
Definition APFSE_INITDS : Z := 0xae2ac.
(* [comment removed for export] *)
Definition FBITMASK : Z := 0x22660.
Definition FZEROFILLED : Z := 0x22700.
Definition fbitmask_bytes : list byte := Eval vm_compute in match image_bytes bsegs FBITMASK 128 with Some bs => bs | None => [] end.

Lemma fbitmask_at : forall m, mem_inv bsegs m -> bytes_at bsegs m FBITMASK fbitmask_bytes.
Proof.
  intros m MI. pose proof (ro_cells_image bsegs m FBITMASK fbitmask_bytes MI ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)) as [_ H].
  cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H.
Qed.
Lemma fbytes_eq_unsigned : forall a b : list byte, map (@bv_unsigned 8) a = map (@bv_unsigned 8) b -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; try discriminate; [reflexivity|].
  cbn [map] in H. injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.
(* [comment removed for export] *)
Lemma fbitmask_know : forall m nb, mem_inv bsegs m -> 0 <= nb <= 31 ->
  rdn bsegs m (wa (FBITMASK + 4 * nb)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (2^nb - 1))).
Proof.
  intros m nb MI H. replace (FBITMASK + 4 * nb) with (FBITMASK + Z.of_nat (Z.to_nat (4 * nb))) by lia.
  rewrite (bytes_at_rdn bsegs m FBITMASK fbitmask_bytes (Z.to_nat (4 * nb)) 4 (fbitmask_at m MI)) by (change (length fbitmask_bytes) with 128%nat; lia).
  f_equal. assert (C : exists k : nat, (k <= 31)%nat /\ nb = Z.of_nat k) by (exists (Z.to_nat nb); lia).
  destruct C as (k & Hk & ->). do 32 (destruct k as [|k]; [apply fbytes_eq_unsigned; vm_compute; reflexivity|]). lia.
Qed.
Lemma fuland_mask_lt : forall x nb, 0 <= nb <= 62 -> 0 <= Z.land x ((2^nb + -1) mod 2^64) < 2^nb.
Proof.
  intros x nb Hn. assert (P : 0 < 2^nb) by (apply Z.pow_pos_nonneg; lia).
  assert (Q : 2^nb <= 2^62) by (apply Z.pow_le_mono_r; lia).
  rewrite Z.mod_small by lia. replace (2^nb + -1) with (Z.ones nb) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia. apply Z.mod_pos_bound. exact P.
Qed.
(* [comment removed for export] *)
Lemma cb16_as_c8c8A : forall m A j, rw_cells bsegs m A [CB 16 j] -> exists w0 w1, rw_cells bsegs m A [C8 w0; C8 w1].
Proof.
  intros m A j H.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in H; [| reflexivity]. cbn [mk_CB_cells app] in H.
  lazymatch type of H with rw_cells _ _ _ (CB 8 ?j0 :: ?post) => destruct (cb8_as_c8 bsegs _ _ [] j0 post H) as [w0 H1] end. cbn [app] in H1.
  lazymatch type of H1 with rw_cells _ _ _ (?c0 :: CB 8 ?j1 :: ?post) => destruct (cb8_as_c8 bsegs _ _ [c0] j1 post H1) as [w1 H2] end. cbn [app] in H2.
  exists w0, w1. exact H2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fse_initds_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV ST BD SRC n DT tl bc lo : Z) (fastw : word) (pad : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' st cont' bc' ptr',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(ST, ST + 16); (BD, BD + 40); (SPV - FSE_INITDS_STACK_A, SPV)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ rw_cells bsegs m' ST [C8 (Z_to_bv 64 st); C8 (Z_to_bv 64 (DT + 4))] /\ 0 <= st < 2^tl
    /\ rw_cells bsegs m' BD (bitd_cells cont' (Z_to_bv 64 bc') pad ptr' SRC) /\ fbit_ok SRC n bc' ptr' /\ bc' <= bc + tl
    /\ rw_cells bsegs m' DT [C2 (Z_to_bv 64 tl); C2 fastw].

Definition fse_initds_stmtA : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV ST BD SRC n DT tl bc ptr lo : Z) (cont fastw : word) (pad src junk : list byte),
  mem_inv bsegs m -> stk bsegs m lo SPV -> 4096 <= lo -> lo <= SPV - FSE_INITDS_STACK_A -> SPV < 2^47 ->
  rw_cells bsegs m ST [CB 16 junk] ->
  rw_cells bsegs m BD (bitd_cells cont (Z_to_bv 64 bc) pad ptr SRC) -> fbit_ok SRC n bc ptr -> bc <= 2048 ->
  bytes_at bsegs m SRC src -> zlen src = n ->
  rw_cells bsegs m DT [C2 (Z_to_bv 64 tl); C2 fastw] -> 0 <= tl <= 12 ->
  ST mod 8 = 0 -> BD mod 8 = 0 -> DT mod 4 = 0 ->
  4096 <= ST -> ST + 16 < 2^47 -> 4096 <= BD -> BD + 40 < 2^47 -> 4096 <= SRC -> SRC + n < 2^47 -> 4096 <= DT -> DT + 4 < 2^47 ->
  (ST + 16 <= BD \/ BD + 40 <= ST) ->
  (ST + 16 <= SRC \/ SRC + n <= ST) -> (BD + 40 <= SRC \/ SRC + n <= BD) ->
  (ST + 16 <= DT \/ DT + 4 <= ST) -> (BD + 40 <= DT \/ DT + 4 <= BD) ->
  (ST + 16 <= lo \/ SPV <= ST) -> (BD + 40 <= lo \/ SPV <= BD) -> (SRC + n <= lo \/ SPV <= SRC) -> (DT + 4 <= lo \/ SPV <= DT) ->
  (* [comment removed for export] *)
  art m -> astk RNG lo SPV -> aro_client RNG m ->
  aro RNG m ST 16 -> aro RNG m BD 40 -> aro RNG m DT 4 -> (0 < n -> aro RNG m SRC n) ->
  app_blk ST (ST + 16) -> app_blk BD (BD + 40) ->
  evtF bsegs RNG (fse_initds_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV ST BD SRC n DT tl bc lo fastw pad m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ST) (Z_to_bv 64 BD) (Z_to_bv 64 DT) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APFSE_INITDS) fc None m (seg_rom bsegs)).
Definition fse_initds_atA (K : Z -> Z -> Z -> Z -> Z -> Prop) : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV ST BD SRC n DT tl bc ptr lo : Z) (cont fastw : word) (pad src junk : list byte),
  K bc tl ptr SRC n ->
  mem_inv bsegs m -> stk bsegs m lo SPV -> 4096 <= lo -> lo <= SPV - FSE_INITDS_STACK_A -> SPV < 2^47 ->
  rw_cells bsegs m ST [CB 16 junk] ->
  rw_cells bsegs m BD (bitd_cells cont (Z_to_bv 64 bc) pad ptr SRC) -> fbit_ok SRC n bc ptr -> bc <= 2048 ->
  bytes_at bsegs m SRC src -> zlen src = n ->
  rw_cells bsegs m DT [C2 (Z_to_bv 64 tl); C2 fastw] -> 0 <= tl <= 12 ->
  ST mod 8 = 0 -> BD mod 8 = 0 -> DT mod 4 = 0 ->
  4096 <= ST -> ST + 16 < 2^47 -> 4096 <= BD -> BD + 40 < 2^47 -> 4096 <= SRC -> SRC + n < 2^47 -> 4096 <= DT -> DT + 4 < 2^47 ->
  (ST + 16 <= BD \/ BD + 40 <= ST) ->
  (ST + 16 <= SRC \/ SRC + n <= ST) -> (BD + 40 <= SRC \/ SRC + n <= BD) ->
  (ST + 16 <= DT \/ DT + 4 <= ST) -> (BD + 40 <= DT \/ DT + 4 <= BD) ->
  (ST + 16 <= lo \/ SPV <= ST) -> (BD + 40 <= lo \/ SPV <= BD) -> (SRC + n <= lo \/ SPV <= SRC) -> (DT + 4 <= lo \/ SPV <= DT) ->
  (* [comment removed for export] *)
  art m -> astk RNG lo SPV -> aro_client RNG m ->
  aro RNG m ST 16 -> aro RNG m BD 40 -> aro RNG m DT 4 -> (0 < n -> aro RNG m SRC n) ->
  app_blk ST (ST + 16) -> app_blk BD (BD + 40) ->
  evtF bsegs RNG (fse_initds_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV ST BD SRC n DT tl bc lo fastw pad m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ST) (Z_to_bv 64 BD) (Z_to_bv 64 DT) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APFSE_INITDS) fc None m (seg_rom bsegs)).

Lemma fse_initds_of_cases : (forall K, fse_initds_atA K) -> fse_initds_stmtA.
Proof. intros H. unfold fse_initds_stmtA. intros. eapply (H (fun _ _ _ _ _ => True)); try eassumption. exact I. Qed.
End CANSEC1.


