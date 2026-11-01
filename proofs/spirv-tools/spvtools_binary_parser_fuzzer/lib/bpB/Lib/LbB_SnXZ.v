(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX BArr.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_FKit.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition SX_SF_RA : Z := 0xf9ad4.
Definition SX_RET : Z := 0xf9b20.

Section SnXZ.
  Context {HCEIL : HeapCeil}.

  Lemma sn_xe2 : forall (x1 x2 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (gp tp : word) (ra' s0' s1' s2' s3' s4' s5' s6' s7' s8' : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (ff fp SP r : Z),
    0 <= ff -> ff + 1024 <= 2 ^ 47 -> 0 <= fp -> fp + 1 <= 2 ^ 47 ->
    2 ^ 45 <= SP - 96 -> SP <= 2 ^ 47 -> (fp + 1 <= SP - 80 \/ SP <= fp) ->
    rw_cells asegs m (SP - 80) [C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra'] ->
    rw_cells asegs m (ff + 1016) [C8 (Z_to_bv 64 fp)] ->
    wr_at asegs m fp 1 -> mem_inv asegs m ->
    exists R' M',
      CatSim.msteps asegs
        (MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 SP) x9 x10
                 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) x19 (Z_to_bv 64 r) x21
                 x22 x23 x24 x25 x26 x27
                 x28 x29 x30 x31) F (Z_to_bv 64 SX_SF_RA) fc None m ro)
        (MS R' F (Z_to_bv 64 SX_RET) fc None M' ro)
      /\ R' = mkR ra' (Z_to_bv 64 SP) gp tp x5 x6 x7 s0' s1' (Z_to_bv 64 r) x11
                 x12 x13 x14 x15 x16 x17 s2' s3' s4' s5' s6' s7' s8' x25 x26 x27 x28 x29 x30 x31
      /\ munch [(fp, fp + 1)] m M' /\ wmono asegs m M' /\ mem_inv asegs M'
      /\ (forall lo hi, stk asegs m lo hi -> stk asegs M' lo hi)
      /\ mrd asegs M' (wa fp) = Some (b8 0).
Proof using.
  intros x1 x2 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         gp tp ra' s0' s1' s2' s3' s4' s5' s6' s7' s8' F fc m ro ff fp SP r
         ff_ge0 ff_top fp_ge0 fp_top sp_bot sp_top fp_clear frame_rw flag_rw fp_wr m_inv.
  (* The register file on entry, and an environment whose variables 32.. carry the values the run loads:
     the flag pointer kept at ff + 1016, then ra and s0 .. s8 from the frame. *)
  set (R0 := mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 SP) x9 x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 ff) x19 (Z_to_bv 64 r) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  set (Env0 := Eseed R0 [Z_to_bv 64 fp; ra'; s0'; s1'; s2'; s3'; s4'; s5'; s6'; s7'; s8']).
  assert (sp_val : bv_unsigned (ev Env0 8) = SP).
  { change (ev Env0 8) with (Z_to_bv 64 SP). apply u64_of_Z. lia. }
  assert (fp_val : bv_unsigned (ev Env0 32) = fp).
  { change (ev Env0 32) with (Z_to_bv 64 fp). apply u64_of_Z. lia. }
  assert (ff_val : bv_unsigned (ev Env0 18) = ff).
  { change (ev Env0 18) with (Z_to_bv 64 ff). apply u64_of_Z. lia. }
  (* The frame reads, the flag read and the store at fp that the run raises, proved from the premises first;
     the run's other side conditions are arithmetic, closed by lia inside `side`. *)
  assert (frame_read : forall (o : Z) (j : N),
            cell_at [C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra'] (Z.to_nat (o + 80))
              = Some (C8 (ev Env0 j)) ->
            -80 <= o <= -8 ->
            sc_denot asegs m Env0 (SCReadBase (SA (EVar 8) o) 8 false (EVar j))).
  { intros o j slot o_rng. cbn [sc_denot]. exists (le8 (ev Env0 j)). split.
    - pose proof (cells_at_read asegs m (SP - 80) _ _ _ (proj1 frame_rw) slot) as slot_bytes.
      rewrite ov_rdn in slot_bytes. cbn [csize cbytes] in slot_bytes.
      unfold adenot. cbn [edenot a_base a_off]. change (ev Env0 8) with (Z_to_bv 64 SP).
      rewrite v_addi_Z by lia. rewrite Z2Nat.id in slot_bytes by lia. unfold wa in slot_bytes.
      replace (SP + o) with (SP - 80 + (o + 80)) by lia. exact slot_bytes.
    - unfold extz, le8. rewrite SeqExec.bytes_le_to_Z_8. apply Z_to_bv_bv_unsigned. }
  assert (flag_read : sc_denot asegs m Env0 (SCReadBase (SA (EVar 18) 1016) 8 false (EVar 32))).
  { cbn [sc_denot]. exists (le8 (Z_to_bv 64 fp)). split.
    - pose proof (cells_at_read asegs m (ff + 1016) [C8 (Z_to_bv 64 fp)] 0 _ (proj1 flag_rw) eq_refl) as flag_bytes.
      rewrite ov_rdn in flag_bytes. cbn [csize cbytes Z.of_nat] in flag_bytes.
      unfold adenot. cbn [edenot a_base a_off]. change (ev Env0 18) with (Z_to_bv 64 ff).
      rewrite v_addi_Z by lia. rewrite Z.add_0_r in flag_bytes. exact flag_bytes.
    - unfold extz, le8. rewrite SeqExec.bytes_le_to_Z_8, Z_to_bv_bv_unsigned. reflexivity. }
  assert (fp_store : sc_denot asegs m Env0 (SCStoreOk (SA (EVar 32) 0) 1)).
  { cbn [sc_denot]. unfold adenot. cbn [edenot a_base a_off]. change (ev Env0 32) with (Z_to_bv 64 fp).
    rewrite v_addi_Z by lia. exact (wr_at_store_ok asegs m fp 1 0 1 fp_wr ltac:(lia) ltac:(lia)). }
  (* Run the segment symbolically from SX_SF_RA to the return at SX_RET. *)
  destruct (sym_exec asegs 40 true [SX_RET] scr_nil (SS SX_SF_RA sr_id [] [] 32) []) as [[fin scs] scr_end] eqn:run_eq.
  pose proof run_eq as run_val. vm_compute in run_val. injection run_val as fin_eq scs_eq _.
  assert (side : scs_denot asegs m Env0 scs).
  { rewrite <- scs_eq. unfold scs_denot.
    repeat first [apply Forall_nil | apply Forall_cons].
    all: lazymatch goal with
         | |- sc_denot _ _ _ (SCReadBase (SA (EVar 8) _) _ _ _) => apply frame_read; [reflexivity | lia]
         | |- sc_denot _ _ _ (SCReadBase (SA (EVar 18) _) _ _ _) => exact flag_read
         | |- sc_denot _ _ _ (SCStoreOk _ _) => exact fp_store
         | |- _ => cbn [sc_denot]; unfold flat, estart, elenZ; cbn [edenot a_base a_off];
                   rewrite ?sp_val, ?fp_val, ?ff_val, ?u64_of_Z by lia; lia
         end. }
  destruct (@run_sound (PropExec.mkFP F fc) asegs 40 [SX_RET] scr_nil SX_SF_RA sr_id [] 32 fin scs scr_end Env0 m ro R0
              run_eq (regs_ok_seed R0 _) (Forall_nil _) side) as (R' & regs_fin & log_ok & steps).
  rewrite <- fin_eq in regs_fin, log_ok, steps. cbn [s_regs s_log s_pc] in regs_fin, log_ok, steps.
  rewrite !mkst_MS in steps.
  set (M1 := mem_denot Env0 m [SE (SA (EVar 32) 0) 1 (ELit 0)]) in steps.
  (* What the final memory holds: the one byte at fp is zero, nothing else moved. *)
  assert (fp_zero : mrd asegs M1 (wa fp) = Some (b8 0)).
  { unfold mrd, M1. cbn [mem_denot]. unfold adenot. cbn [edenot a_base a_off].
    change (ev Env0 32) with (Z_to_bv 64 fp).
    rewrite v_addi_Z, Z.add_0_r, word_to_le_bytes_1 by lia. unfold wa.
    rewrite (wbytes_hit_byte [Z_to_bv 8 0] m (Z_to_bv 64 fp) fp (Z_to_bv 8 0)); [reflexivity | | |];
      cbn [length Z.of_nat]; rewrite ?u64_of_Z by lia.
    - lia.
    - lia.
    - rewrite Z.sub_diag. reflexivity. }
  assert (only_fp : munch [(fp, fp + 1)] m M1).
  { apply munch_mem_denot; [exact log_ok|].
    constructor; [|constructor]. cbn [inside e_addr e_width]. left.
    unfold estart. cbn [edenot a_base a_off]. rewrite fp_val. lia. }
  pose proof (msteps_mem_inv asegs _ _ steps m_inv) as inv_end.
  (* The register file at SX_RET, read back from the symbolic registers. *)
  assert (full0 : rfull R0) by (unfold R0; apply rfull_mkR).
  pose proof (msteps_full asegs _ _ steps full0) as full_end.
  exists R', M1.
  refine (conj steps (conj _ (conj only_fp (conj (wmono_mem_denot _ _ _)
            (conj inv_end (conj (fun lo hi stk_m => stk_mem_denot _ _ _ lo hi stk_m) fp_zero)))))).
  rewrite (rfull_eq R' full_end). f_equal; rewrite regs_fin; reflexivity.
Qed.
End SnXZ.
