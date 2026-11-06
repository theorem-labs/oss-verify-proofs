(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr FP.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit Lept_objkit Ed_fp Ed_iface Ed_fpkit Numa_kit LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Definition numaGetIValue_post (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (m : mem) (usp lo p : Z) (k : Z) : machine_state -> Prop :=
  fun ms' => exists (a1' a2' a3' a4' a5' a6' a7' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) (frm_clear fc') None m' (seg_rom asegs)
    /\ munch [(usp - 16, usp); (p, p + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
    /\ rw_cells asegs m' p [C4 (Z_to_bv 64 k)].

Lemma numaGetIValue_evt : forall (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (usp lo : Z) (live : list (Z * Z)) (na cap arr : Z) (vals : list word) (ks : list Z) (i p k : Z) (old : word),
  numa_obj live m na cap arr vals -> numa_ints vals ks -> acc asegs m na 32 -> acc asegs m arr (4 * cap) ->
  nth_error ks (Z.to_nat i) = Some k -> 0 <= i ->
  rw_cells asegs m p [C4 old] -> acc asegs m p 4 -> 0 < p -> p mod 8 = 0 ->
  ro_cells asegs m g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)] ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] -> ED_RO m ->
  stk asegs m lo usp -> lo <= usp - 16 -> usp <= 2^47 -> 0x10007fff8000 <= lo -> na + 32 <= lo -> arr + 4 * cap <= lo -> p + 4 <= lo ->
  (na + 32 <= 0x7fff7000 \/ 0x10007fff8000 <= na) -> (na + 32 <= 0x10000 \/ SEGTOP_A <= na) ->
  (arr + 4 * cap <= 0x7fff7000 \/ 0x10007fff8000 <= arr) -> (arr + 4 * cap <= 0x10000 \/ SEGTOP_A <= arr) ->
  (p + 4 <= 0x7fff7000 \/ 0x10007fff8000 <= p) -> SEGTOP_A <= p ->
  (p + 4 <= na \/ na + 32 <= p) -> (p + 4 <= arr \/ arr + 4 * cap <= p) ->
  mem_inv asegs m ->
  evt asegs (numaGetIValue_post ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F m usp lo p k)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 na) (Z_to_bv 64 i) (Z_to_bv 64 p) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_numaGetIValue) (frm_clear fc) None m (seg_rom asegs)).
Proof.
  intros until old. intros OB IV ACCn ACCa Hk Hi PC ACCp P0 P8 G1 G2 RO ST LO UHI LOH NLO ALO PLO NSH NSEG ASH ASEG PSH PSEG PNA PAR MI.
  pose proof (numa_obj_facts _ _ _ _ _ _ OB) as (LEN & CAP & NA0 & NA16 & AR0 & AR16 & INn & INa & NE).
  destruct (numa_ints_nth vals ks i IV) as (k' & Hk2 & Hw & LOK).
  { pose proof (nth_error_lt _ _ _ Hk). rewrite <- (numa_ints_length _ _ IV) in H. exact H. }
  rewrite Hk in Hk2. injection Hk2 as <-. unfold loc_ok, LOC_LO, LOC_HI in LOK.
  pose proof (nth_error_lt _ _ _ Hw) as IL.
  destruct OB as ((pad & NC) & (junk0 & AC) & _). unfold numa_cells in NC.
  destruct (numa_arr_view m arr cap vals junk0 AC ltac:(lia)) as (ws & UA & UAL). clear AC.
  assert (Hw' : nth_error (vals ++ ws) (Z.to_nat i) = Some (ival_w k)) by (rewrite nth_error_app1 by exact IL; exact Hw).
  remember (vals ++ ws) as aws eqn:EA. clear EA ws.
  destruct RO as (RO1 & RO2 & RO3 & RO4). unfold RO_SIGN_TAB, RO_HALF, RO_GUARD_LO, RO_GUARD_HI in RO1, RO2, RO3, RO4.
  unfold e_numaGetIValue, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SEGTOP_A, SHB in *.
  pose proof (munch_refl [(usp - 16, usp); (p, p + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lwalk [0xf0344; 0xf0464; 0xf03ac; 0xf041c; 0xf03e4; 0xf0474; 0xf04b8; 0xf0508; 0xf04e4; 0xf04f4].   (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with UAx : u32arr asegs mm arr ?wsx |- _ =>
      pose proof (u32arr_read asegs mm arr wsx i (ival_w k) _ UAx Hw' Hi eq_refl) as RDi end end.
  step.                                                    (* [comment removed for export] *)
  change (nan_box (bv_extract 0 32 (le_bytes_to_word (le4 (ival_w k))))) with (flw_val (ival_w k)).
  step. step. step. step.   (* [comment removed for export] *)
  step.                     (* [comment removed for export] *)
  step.                     (* [comment removed for export] *)
  destruct (Z_lt_ge_dec k 0) as [KN|KP].
  - (* [comment removed for export] *)
    pose proof (ival_sign_neg k ltac:(lia)) as SG. unfold S_ZERO in SG. rewrite SG. clear SG. change (bword true) with (Z_to_bv 64 1).
    step. step. step.          (* [comment removed for export] *)
    step. step.                (* [comment removed for export] *)
    step. step.                (* [comment removed for export] *)
    change (fma_d F_MADD RNE D_MONE D_HALF (fcvt_d_s RNE (flw_val (ival_w k)))) with (ival_round RNE D_MONE D_HALF (flw_val (ival_w k))) in *.
    step.                      (* [comment removed for export] *)
    rewrite (ival_guard_lo_neg k ltac:(lia)). change (bword true) with (Z_to_bv 64 1).
    step. brF.                 (* [comment removed for export] *)
    step. step. step.          (* [comment removed for export] *)
    rewrite (ival_guard_hi_neg k ltac:(lia)). change (bword true) with (Z_to_bv 64 1).
    step. brF.                 (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ ?FF _ _ _ _ _) => remember FF as F1 eqn:EF1 end.
    lwalk [0xf03a0; 0xf0464; 0xf04f4].   (* [comment removed for export] *)
    subst F1.
    step.                      (* [comment removed for export] *)
    rewrite (ival_exact_neg k ltac:(lia)) in *.
    lazymatch goal with |- evt _ _ (MS _ ?FF _ _ _ _ _) => remember FF as F2 eqn:EF2 end.
    lwalk (@nil Z).            (* [comment removed for export] *)
    apply evt_done. unfold numaGetIValue_post. do 10 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| eassumption].
  - (* [comment removed for export] *)
    pose proof (ival_sign k ltac:(lia)) as SG. unfold S_ZERO in SG. rewrite SG. clear SG. change (bword false) with (Z_to_bv 64 0).
    step. step. step.          (* [comment removed for export] *)
    step. step.                (* [comment removed for export] *)
    step. step.                (* [comment removed for export] *)
    change (fma_d F_MADD RNE D_ONE D_HALF (fcvt_d_s RNE (flw_val (ival_w k)))) with (ival_round RNE D_ONE D_HALF (flw_val (ival_w k))) in *.
    step.                      (* [comment removed for export] *)
    rewrite (ival_guard_lo k ltac:(lia)). change (bword true) with (Z_to_bv 64 1).
    step. brF.                 (* [comment removed for export] *)
    step. step. step.          (* [comment removed for export] *)
    rewrite (ival_guard_hi k ltac:(lia)). change (bword true) with (Z_to_bv 64 1).
    step. brF.                 (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ ?FF _ _ _ _ _) => remember FF as F1 eqn:EF1 end.
    lwalk [0xf03a0; 0xf0464; 0xf04f4].
    subst F1.
    step.                      (* [comment removed for export] *)
    rewrite (ival_exact k ltac:(lia)) in *.
    lazymatch goal with |- evt _ _ (MS _ ?FF _ _ _ _ _) => remember FF as F2 eqn:EF2 end.
    lwalk (@nil Z).
    apply evt_done. unfold numaGetIValue_post. do 10 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| eassumption].
Qed.
