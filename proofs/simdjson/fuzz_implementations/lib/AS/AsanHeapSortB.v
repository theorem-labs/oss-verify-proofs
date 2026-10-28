(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.simdjson.fuzz_implementations.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import PropExec StoreOk Hoare AgentLib.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AsanTablesB AsanPlanSoundSums AsanPlanImagesB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require AsanHeapSortDef AsanHeapSort.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition hs_code_okb (segs : list Segment) (p : Z) : bool :=
  forallb (fun k => match fetch_word segs (Z_to_bv 64 (p + 4 * Z.of_nat k)) with
                    | Some w => Z.eqb (bv_unsigned w) (bv_unsigned (nth k AsanHeapSortDef.HS_WORDS (Z_to_bv 32 0)))
                    | None => false
                    end) (seq 0 AsanHeapSortDef.HS_N).

Lemma hs_code_okb_sound : forall segs p, hs_code_okb segs p = true ->
  forall k, (k < AsanHeapSortDef.HS_N)%nat ->
  fetch_word segs (Z_to_bv 64 (p + 4 * Z.of_nat k)) = Some (nth k AsanHeapSortDef.HS_WORDS (Z_to_bv 32 0)).
Proof.
  intros segs p H k Hk. unfold hs_code_okb in H. rewrite forallb_forall in H.
  specialize (H k ltac:(apply in_seq; lia)).
  destruct (fetch_word segs (Z_to_bv 64 (p + 4 * Z.of_nat k))) as [w|]; [|discriminate].
  apply Z.eqb_eq in H. f_equal. apply bv_eq. exact H.
Qed.

Lemma asan_hs_code_all : hs_code_okb ASEGS (AP.x_hsort ASAN_B) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem asan_hsort_spec : AsanHeapSort.hsort_spec ASEGS (AP.x_hsort ASAN_B).
Proof.
  apply AsanHeapSort.hsort_spec_of_code.
  - vm_compute. discriminate.
  - unfold AsanHeapSortDef.HS_N. vm_compute. discriminate.
  - exact (hs_code_okb_sound ASEGS _ asan_hs_code_all).
Qed.

Section AsanNodes.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> AP.CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Variable FS0 : Fs.Fs.

Theorem asan_node_x_sound_XHeapSort : APS.x_stmt ASEGS ASAN_B nx0 LIMIT SINV argH FS0 AP.XHeapSort.
Proof. eapply APSX.node_x_sound_XHeapSort; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
       try apply asan_res_len; try apply asan_hull_ok. apply asan_hsort_spec. Qed.
End AsanNodes.
