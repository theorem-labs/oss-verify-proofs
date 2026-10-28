(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_QPut AW_Enqueue AW_CbRecycle AW_LCDealloc AW_DoRecycle.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
Section ARUN_1. Context {hAR : arun}.
Section DoRecycle.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.

  Ltac facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Definition dr_head_post' (SP : Z) (ra gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 : word)
      (C b len next last bytes bsize count e0 lo : Z) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) (T STK : Z) (j0 : list byte) (q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra : word) : machine_state -> Prop :=
    fun ms' => exists (m' : mem),
      munch [(lo, SP); (C, C + 32)] m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m' /\ dr_frame m' SP T STK j0 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra
      /\ rw_cells asegs m' C (qc_cells (len - 1) next (if next =? 0 then 0 else last) (bytes - bsize))
      /\ ( (count <> 0
            /\ ms' = MS (dr_regs SP (Z_to_bv 64 A_DR_INNER) gp tp t0 t1 t2 (Z_to_bv 64 (SP + -104)) (Z_to_bv 64 e0) a2 a3 a4 a5 a6 a7
                                 (Z_to_bv 64 b) (Z_to_bv 64 count) (Z_to_bv 64 (b + 152)) (Z_to_bv 64 (count + 16)) (Z_to_bv 64 16) s10 s11 t3 t4 t5 t6 C)
                        F (Z_to_bv 64 A_CB_RECYCLE) fc None m' (seg_rom asegs))
        \/ (count = 0
            /\ exists a0' a1' s7 s8 s9, ms' = MS (dr_regs SP ra gp tp t0 t1 t2 a0' a1' a2 a3 a4 a5 a6 a7
                                 (Z_to_bv 64 b) (Z_to_bv 64 count) s7 s8 s9 s10 s11 t3 t4 t5 t6 C)
                        F (Z_to_bv 64 A_DR_TAIL) fc None m' (seg_rom asegs)) ).

  #[using="IMG ALWF CSOK"] Lemma dr_head' : forall
      (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra : word)
      (SP C b len next last bytes bsize count lo T STK : Z) (j0 : list byte) (elems : list word) (F : bvmap 5 word) (fc : bv 32) (m0 m : mem),
      dr_frame m SP T STK j0 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra ->
      1 <= len < 2^63 -> 0 <= next < 2^64 -> 0 <= last < 2^64 -> 0 <= bsize <= bytes -> bytes < 2^63 ->
      0x65f000 <= b -> b + 8192 <= 2^47 -> 0 <= count <= 1021 -> length elems = Z.to_nat count ->
      SP <= C -> C + 32 <= 2^62 -> (C + 32 <= b \/ b + 8192 <= C) ->
      rw_cells asegs m C (qc_cells len b last bytes) -> crange CS C 32 ->
      rw_cells asegs m b (batch_hdr next bsize count) -> u64arr asegs m (b + 24) elems -> crange CS b 8192 ->
      ACEIL <= lo -> lo <= SP - 112 -> SP <= 2^62 -> (SP <= b \/ b + 8192 <= lo) ->
      munch [(lo, SP); (C, C + 32)] m0 m -> wmono asegs m0 m -> mem_inv asegs m -> crange CS lo (SP - lo) ->
      evtA asegs AL CS (dr_head_post' SP ra gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 C b len next last bytes bsize count
                          (match elems with [] => 0 | e :: _ => bv_unsigned e end) lo F fc m0 T STK j0 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra)
        (MS (dr_regs SP ra gp tp t0 t1 t2 (Z_to_bv 64 len) a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 C)
            F (Z_to_bv 64 A_DR_HEAD) fc None m (seg_rom asegs)).
  Proof.
    intros ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra SP C b len next last bytes bsize count lo T STK j0 elems F fc m0 m
      FR LB NXB LAB BSB BYB B0 B1 CNT EL C0 C1 CB QC CCS BH BE BCS LOIMG SPL SPH SEP MU WM MI SCS.
    facts. unfold qc_cells, batch_hdr, dr_regs, dr_frame in *. unfold A_DR_HEAD, A_DR_INNER, A_DR_TAIL, A_CB_RECYCLE, A_INSTANCE in *.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    zstep. if_cases Kn; zify_cond Kn.
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      zstep. if_cases Kc; zify_cond Kc.
      + (* [comment removed for export] *)
        apply evtA_done; unfold dr_head_post', dr_frame; eexists.
        split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [replace (next =? 0) with false by (symmetry; apply Z.eqb_neq; exact Kn); replace (len - 1) with (len + -1) by (clear; lia); assumption|right; split; [exact Kc| deexists 5; unfold dr_regs, A_INSTANCE; reflexivity]].
      + (* [comment removed for export] *)
        zstep. zstep. zstep.
        destruct elems as [|e0 er]; [exfalso; cbn in EL; clear -EL Kc CNT; lia|].
        pose proof (u64arr_read asegs _ (b + 24) (e0 :: er) 0 e0 _ BE eq_refl ltac:(clear; lia) eq_refl) as RD.
        replace (b + 24 + 8 * 0) with (b + 152 + -128) in RD by (clear; lia).
        zstep. clear RD. zstep. zstep.
        apply evtA_done; unfold dr_head_post', dr_frame; eexists.
        split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [replace (next =? 0) with false by (symmetry; apply Z.eqb_neq; exact Kn); replace (len - 1) with (len + -1) by (clear; lia); assumption|left; split; [exact Kc| unfold dr_regs, A_INSTANCE; rewrite Z_to_bv_bv_unsigned; reflexivity]].
    - (* [comment removed for export] *)
      zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      zstep. if_cases Kc; zify_cond Kc.
      + (* [comment removed for export] *)
        apply evtA_done; unfold dr_head_post', dr_frame; eexists.
        split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [subst next; cbn [Z.eqb]; replace (len - 1) with (len + -1) by (clear; lia); assumption|right; split; [exact Kc| deexists 5; unfold dr_regs, A_INSTANCE; reflexivity]].
      + (* [comment removed for export] *)
        zstep. zstep. zstep.
        destruct elems as [|e0 er]; [exfalso; cbn in EL; clear -EL Kc CNT; lia|].
        pose proof (u64arr_read asegs _ (b + 24) (e0 :: er) 0 e0 _ BE eq_refl ltac:(clear; lia) eq_refl) as RD.
        replace (b + 24 + 8 * 0) with (b + 152 + -128) in RD by (clear; lia).
        zstep. clear RD. zstep. zstep.
        apply evtA_done; unfold dr_head_post', dr_frame; eexists.
        split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [subst next; cbn [Z.eqb]; replace (len - 1) with (len + -1) by (clear; lia); assumption|left; split; [exact Kc| unfold dr_regs, A_INSTANCE; rewrite Z_to_bv_bv_unsigned; reflexivity]].
  Qed.

End DoRecycle.
End ARUN_1.
