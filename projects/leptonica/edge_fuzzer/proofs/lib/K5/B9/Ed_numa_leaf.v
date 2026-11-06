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
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit Lept_objkit Ed_fp Ed_iface Numa_kit LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Definition numaGetCount_post (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (usp lo n : Z) : machine_state -> Prop :=
  fun ms' => exists (a1' a2' : word) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(usp - 16, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp.

Lemma numaGetCount_evt : forall (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (usp lo : Z) (live : list (Z * Z)) (na cap arr : Z) (vals : list word),
  numa_obj live m na cap arr vals -> acc asegs m na 32 ->
  ro_cells asegs m g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)] ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo usp -> lo <= usp - 16 -> usp <= 2^47 -> 0x10007fff8000 <= lo -> na + 32 <= lo ->
  (na + 32 <= 0x7fff7000 \/ 0x10007fff8000 <= na) -> (na + 32 <= 0x10000 \/ SEGTOP_A <= na) ->
  mem_inv asegs m ->
  evt asegs (numaGetCount_post ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m usp lo (Z.of_nat (length vals)))
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 na) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_numaGetCount) fc None m (seg_rom asegs)).
Proof.
  intros until vals. intros OB ACC G1 G2 ST LO UHI LOH NLO NSH NSEG MI.
  pose proof (numa_obj_facts _ _ _ _ _ _ OB) as (LEN & CAP & NA0 & NA16 & AR0 & AR16 & INn & INa & NE).
  destruct OB as ((pad & NC) & _). unfold numa_cells in NC.
  unfold e_numaGetCount, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SEGTOP_A, SHB in *.
  pose proof (munch_refl [(usp - 16, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lwalk [0xefe0c; 0xefdc4; 0xefe28].      (* [comment removed for export] *)
  lwalk (@nil Z).                         (* [comment removed for export] *)
  rewrite sx32_small by lia.
  apply evt_done. unfold numaGetCount_post. do 3 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.

(* [comment removed for export] *)
Definition numaGetFValue_post (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (usp lo pf : Z) (w : word) : machine_state -> Prop :=
  fun ms' => exists (a1' a2' a3' a4' a5' a6' a7' : word) (F' : bvmap 5 word) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(usp - 16, usp); (pf, pf + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
    /\ rw_cells asegs m' pf [C4 (nan_box (bv_extract 0 32 (le_bytes_to_word (le4 w))))] /\ F' = bvmap_set (Z_to_bv 5 15) (nan_box (bv_extract 0 32 (le_bytes_to_word (le4 w)))) F.

Lemma numaGetFValue_evt : forall (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (usp lo : Z) (live : list (Z * Z)) (na cap arr : Z) (vals : list word) (i pf : Z) (w old : word),
  numa_obj live m na cap arr vals -> acc asegs m na 32 -> acc asegs m arr (4 * cap) ->
  nth_error vals (Z.to_nat i) = Some w -> 0 <= i ->
  rw_cells asegs m pf [C4 old] -> acc asegs m pf 4 -> 0 < pf -> pf mod 8 = 0 ->
  ro_cells asegs m g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)] ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo usp -> lo <= usp - 16 -> usp <= 2^47 -> 0x10007fff8000 <= lo -> na + 32 <= lo -> arr + 4 * cap <= lo -> pf + 4 <= lo ->
  (na + 32 <= 0x7fff7000 \/ 0x10007fff8000 <= na) -> (na + 32 <= 0x10000 \/ SEGTOP_A <= na) ->
  (arr + 4 * cap <= 0x7fff7000 \/ 0x10007fff8000 <= arr) -> (arr + 4 * cap <= 0x10000 \/ SEGTOP_A <= arr) ->
  (pf + 4 <= 0x7fff7000 \/ 0x10007fff8000 <= pf) -> SEGTOP_A <= pf ->
  (pf + 4 <= na \/ na + 32 <= pf) -> (pf + 4 <= arr \/ arr + 4 * cap <= pf) ->
  mem_inv asegs m ->
  evt asegs (numaGetFValue_post ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m usp lo pf w)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 na) (Z_to_bv 64 i) (Z_to_bv 64 pf) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_numaGetFValue) fc None m (seg_rom asegs)).
Proof.
  intros until old. intros OB ACCn ACCa Hw Hi PFC ACCp PF0 PF8 G1 G2 ST LO UHI LOH NLO ALO PLO NSH NSEG ASH ASEG PSH PSEG PNA PAR MI.
  pose proof (numa_obj_facts _ _ _ _ _ _ OB) as (LEN & CAP & NA0 & NA16 & AR0 & AR16 & INn & INa & NE).
  pose proof (nth_error_lt _ _ _ Hw) as IL.
  destruct OB as ((pad & NC) & (junk0 & AC) & _). unfold numa_cells in NC.
  destruct (numa_arr_view m arr cap vals junk0 AC ltac:(lia)) as (ws & UA & UAL). clear AC.
  assert (Hw' : nth_error (vals ++ ws) (Z.to_nat i) = Some w) by (rewrite nth_error_app1 by exact IL; exact Hw).
  remember (vals ++ ws) as aws eqn:EA. clear EA ws.
  unfold e_numaGetFValue, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SEGTOP_A, SHB in *.
  pose proof (munch_refl [(usp - 16, usp); (pf, pf + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lwalk [0xf01ec; 0xf0134; 0xf01a4; 0xf016c; 0xf01fc; 0xf0240; 0xf0290; 0xf026c; 0xf027c].
  lwalk [0xf0120; 0xf01ec; 0xf0134; 0xf01a4; 0xf016c; 0xf01fc; 0xf0240; 0xf0290; 0xf026c; 0xf027c].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with UAx : u32arr asegs mm arr ?wsx |- _ =>
      pose proof (u32arr_read asegs mm arr wsx i w _ UAx Hw' Hi eq_refl) as RDi end end.
  step.                                                    (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ (bvmap_set ?k ?v F) _ _ _ _ _) => remember (bvmap_set k v F) as F1 eqn:EF1 end.
  lwalk [0xf01ec; 0xf0134; 0xf01a4; 0xf016c; 0xf01fc; 0xf0240; 0xf0290; 0xf026c; 0xf027c].   (* [comment removed for export] *)
  lwalk (@nil Z).                                          (* [comment removed for export] *)
  subst F1.
  lazymatch goal with X : rw_cells asegs ?mm pf ?cc |- _ =>
    lazymatch cc with context [reg_get (bvmap_set ?k ?v F) ?r] => rewrite (freg_get_same F k r v) in X by reflexivity end end.
  apply evt_done. unfold numaGetFValue_post. do 9 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [eassumption| reflexivity].
Qed.
