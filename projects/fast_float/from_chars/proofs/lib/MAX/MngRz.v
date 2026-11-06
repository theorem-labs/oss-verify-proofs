(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem Require Import Monad Specs.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatSim ShapeSet RealizesCfg AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import MngWk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition svc_set (ms : machine_state) : machine_state :=
  {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
     ms_svc_pending := Some (ms_reg ms 17); ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
     ms_mem := ms_mem ms; ms_rom := ms_rom ms |}.

Section Svc.
Variable segs : list Segment.

#[using="Type"] Lemma ecall_step' : forall ms w, fetch_word segs (ms_pc ms) = Some w -> is_ecall w = true ->
  RiscvSemantics.step segs ms = MachineOk (svc_set ms).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms w Hf He. unfold RiscvSemantics.step, RiscvSemantics.step_accesses. rewrite Hf.
  unfold decode_exec_accesses. rewrite He. reflexivity.
Qed.

Context {fx : FPState}.

#[using="Type"] Lemma svc_after : forall regs pc m rom eff,
  advance_past_svc (apply_effect (svc_set (@mkst fx regs pc m rom)) eff) =
  @mkst fx (regupd regs 10 (eff_ret eff)) (bv_add pc (w64 4)) (mem_after m eff) rom.
Proof. LiaFast.lf_pins LiaFast.u0. intros. reflexivity. Qed.

#[using="Type"] Lemma svc_pending : forall regs pc m rom, ms_svc_pending (svc_set (@mkst fx regs pc m rom)) = Some (getr regs 17).
Proof. LiaFast.lf_pins LiaFast.u0. intros. reflexivity. Qed.

#[using="Type"] Lemma svc_gpr : forall regs pc m rom i, (i < 8)%nat ->
  ms_gpr (svc_set (@mkst fx regs pc m rom)) i = getr regs (Z_to_bv 5 (10 + Z.of_nat i)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc m rom i Hi. unfold ms_gpr, getr. cbn [ms_regs svc_set mkst].
  destruct (bv_eqb (Z_to_bv 5 (10 + Z.of_nat i)) 0) eqn:E; [|reflexivity].
  exfalso. unfold bv_eqb in E. apply Z.eqb_eq in E. rewrite Z_to_bv_unsigned in E.
  unfold bv_wrap in E. change (bv_modulus 5) with 32 in E. change (bv_unsigned (0 : bv 5)) with 0 in E.
  rewrite Z.mod_small in E by lia. lia.
Qed.
End Svc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma page_round_eq : forall x, page_round x = page_round_up_Z x.
Proof. intros x. reflexivity. Qed.

Lemma getr_w64 : forall (regs : bvmap 5 word) r a, bv_unsigned (getr regs r) = a mod 2 ^ 64 -> 0 <= a < 2 ^ 64 -> getr regs r = w64 a.
Proof.
  intros regs r a H Ha. apply bv_eq. rewrite H. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). reflexivity.
Qed.

Lemma u_w64 : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (w64 a) = a.
Proof. intros a Ha. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. exact Ha. Qed.

Lemma w_is0_w64 : forall a, 0 < a < 2 ^ 64 -> w_is0 (w64 a) = false.
Proof. intros a Ha. unfold w_is0, bv_eqb. rewrite u_w64 by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0. apply Z.eqb_neq. lia. Qed.

Lemma w_is0_0 : w_is0 (w64 0) = true.
Proof. reflexivity. Qed.

Section Nodes.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_ecall : forall regs pc m md K,
  m_halted md = None -> m_vm_lazy md = [] ->
  (exists w, fetch_word segs pc = Some w /\ is_ecall w = true) ->
  realizes_cfg segs cfg (mkCfg (svc_set (@mkst fx regs pc m rom)) md) K ->
  realizes_cfg segs cfg (mkCfg (@mkst fx regs pc m rom) md) K.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc m md K Hh Hl (w & Hf & He) H.
  exact (rzc_step segs cfg (@mkst fx regs pc m rom) md _ K Hh Hl eq_refl (ecall_step' segs (@mkst fx regs pc m rom) w Hf He) H).
Qed.

(* [comment removed for export] *)
Definition eff_munmap (a n : Z) : SyscallEffect := mkEffectU (w64 0) [] [] [(w64 a, w64 n)] [] [].

#[using="Type"] Lemma rz_munmap : forall L s r len regs pc m md K,
  at_ecall segs L s (KMunmap r len) regs pc ->
  m_halted md = None -> m_vm_lazy md = [] ->
  ly_reg L r mod PGSZ = 0 -> 1 <= len -> 0 <= ly_reg L r -> ly_reg L r + page_round len <= 2 ^ 47 ->
  map_has (vm_maps (m_vmmaps md)) (w64 (ly_reg L r)) (w64 (page_round len)) = true ->
  realizes_cfg segs cfg (mkCfg (@mkst fx (regupd regs 10 (w64 0)) (bv_add pc (w64 4))
                                   (mem_after m (eff_munmap (ly_reg L r) (page_round len))) rom)
                               (munmap_next (w64 (ly_reg L r)) (w64 (page_round len)) md)) K ->
  realizes_cfg segs cfg (mkCfg (@mkst fx regs pc m rom) md) K.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s r len regs pc m md K (Hec & no & args & Hreq & Hno & Hargs) Hh Hl Hal Hlen Ha0 Htop Hhas Hc.
  cbn [req_regs] in Hreq. injection Hreq as <- <-. cbn [args_match] in Hargs. destruct Hargs as (A0 & A1 & _).
  assert (PR : 0 <= page_round len) by (unfold page_round, PGSZ; apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia).
  assert (PL : len <= page_round len).
  { unfold page_round, PGSZ. pose proof (Z.mod_pos_bound (len + 4096 - 1) 4096 ltac:(lia)).
    pose proof (Z.div_mod (len + 4096 - 1) 4096 ltac:(lia)). lia. }
  assert (E0 : getr regs (Z_to_bv 5 (10 + 0)) = w64 (ly_reg L r)) by (apply getr_w64; [exact A0 | lia]).
  assert (E1 : getr regs (Z_to_bv 5 (10 + (0 + 1))) = w64 len) by (apply getr_w64; [exact A1 | lia]).
  apply rz_ecall; [exact Hh | exact Hl | exact Hec |].
  set (ms := svc_set (@mkst fx regs pc m rom)).
  assert (G0 : ms_gpr ms 0 = w64 (ly_reg L r)) by (unfold ms; rewrite svc_gpr by lia; exact E0).
  assert (G1 : ms_gpr ms 1 = w64 len) by (unfold ms; rewrite svc_gpr by lia; exact E1).
  apply (rzc_munmap_exact segs cfg ms md (getr regs 17) K Hh (svc_pending regs pc m rom) Hno).
  - rewrite G0, u_w64 by lia. apply Z.eqb_eq. exact Hal.
  - rewrite G1. apply w_is0_w64. lia.
  - rewrite G0, G1, !u_w64 by lia. rewrite <- page_round_eq. apply Z.ltb_ge. unfold TASK_SIZE. lia.
  - rewrite G0, G1, u_w64 by lia. rewrite <- page_round_eq. exact Hhas.
  - rewrite G0, G1, u_w64 by lia. rewrite <- page_round_eq. unfold ms. rewrite svc_after. exact Hc.
Qed.

(* [comment removed for export] *)
#[using="Hoff"] Lemma rz_mmap_rw : forall L s len regs pc m md K,
  at_ecall segs L s (KMmapRW len) regs pc ->
  m_halted md = None -> m_vm_lazy md = [] -> 1 <= len < 2 ^ 63 ->
  (exists a, fresh_rw_guard (w64 34) md (page_round len) a) ->
  (forall a, fresh_rw_guard (w64 34) md (page_round len) a ->
     realizes_cfg segs cfg (mkCfg (@mkst fx (regupd regs 10 a) (bv_add pc (w64 4))
                                      (mem_after m (mkEffect a [] [(a, w64 (page_round len))])) rom)
                                  (fresh_rw_next (w64 34) a (w64 (page_round len)) md)) K) ->
  realizes_cfg segs cfg (mkCfg (@mkst fx regs pc m rom) md) K.
Proof. LiaFast.lf_pins (fun (Hoff : LiaFast.U) => LiaFast.u0).
  intros L s len regs pc m md K (Hec & no & args & Hreq & Hno & Hargs) Hh Hl Hlen Hex Hc.
  cbn [req_regs] in Hreq. injection Hreq as <- <-. cbn [args_match] in Hargs. destruct Hargs as (A0 & A1 & A2 & A3 & A4 & A5 & _).
  assert (E1 : getr regs (Z_to_bv 5 (10 + (0 + 1))) = w64 len) by (apply getr_w64; [exact A1 | lia]).
  assert (E2 : getr regs (Z_to_bv 5 (10 + (0 + 1 + 1))) = w64 3) by (apply getr_w64; [exact A2 | lia]).
  assert (E3 : getr regs (Z_to_bv 5 (10 + (0 + 1 + 1 + 1))) = w64 34) by (apply getr_w64; [exact A3 | lia]).
  assert (E5 : getr regs (Z_to_bv 5 (10 + (0 + 1 + 1 + 1 + 1 + 1))) = w64 0) by (apply getr_w64; [exact A5 | lia]).
  apply rz_ecall; [exact Hh | exact Hl | exact Hec |].
  set (ms := svc_set (@mkst fx regs pc m rom)).
  assert (G1 : ms_gpr ms 1 = w64 len) by (unfold ms; rewrite svc_gpr by lia; exact E1).
  assert (G2 : ms_gpr ms 2 = w64 3) by (unfold ms; rewrite svc_gpr by lia; exact E2).
  assert (G3 : ms_gpr ms 3 = w64 34) by (unfold ms; rewrite svc_gpr by lia; exact E3).
  assert (G5 : ms_gpr ms 5 = w64 0) by (unfold ms; rewrite svc_gpr by lia; exact E5).
  apply (rzc_mmap_fresh_rw segs cfg Hoff ms md (getr regs 17) K Hh (svc_pending regs pc m rom) Hno).
  - rewrite G5. reflexivity.
  - rewrite G3. reflexivity.
  - rewrite G1. apply w_is0_w64. lia.
  - rewrite G2, G3, G5. reflexivity.
  - rewrite G3, G1, u_w64 by lia. rewrite <- page_round_eq. exact Hex.
  - intros a Ha. rewrite G3, G1, u_w64 by lia. rewrite G3, G1, u_w64 in Ha by lia. rewrite <- page_round_eq in Ha |- *.
    unfold ms. rewrite svc_after. exact (Hc a Ha).
Qed.

(* [comment removed for export] *)
#[using="Hoff"] Lemma rz_mmap_na : forall L s len regs pc m md K,
  at_ecall segs L s (KMmapNone len) regs pc ->
  m_halted md = None -> m_vm_lazy md = [] -> 1 <= len < 2 ^ 63 ->
  (exists a, place_ok md (page_round len) a) ->
  (forall a, place_ok md (page_round len) a ->
     realizes_cfg segs cfg (mkCfg (@mkst fx (regupd regs 10 a) (bv_add pc (w64 4))
                                      (mem_after m (mkEffectU a [] [] [(a, w64 (page_round len))] [] [])) rom)
                                  (fresh_na_next (w64 34) a (w64 (page_round len)) md)) K) ->
  realizes_cfg segs cfg (mkCfg (@mkst fx regs pc m rom) md) K.
Proof. LiaFast.lf_pins (fun (Hoff : LiaFast.U) => LiaFast.u0).
  intros L s len regs pc m md K (Hec & no & args & Hreq & Hno & Hargs) Hh Hl Hlen Hex Hc.
  cbn [req_regs] in Hreq. injection Hreq as <- <-. cbn [args_match] in Hargs. destruct Hargs as (A0 & A1 & A2 & A3 & A4 & A5 & _).
  assert (E1 : getr regs (Z_to_bv 5 (10 + (0 + 1))) = w64 len) by (apply getr_w64; [exact A1 | lia]).
  assert (E2 : getr regs (Z_to_bv 5 (10 + (0 + 1 + 1))) = w64 0) by (apply getr_w64; [exact A2 | lia]).
  assert (E3 : getr regs (Z_to_bv 5 (10 + (0 + 1 + 1 + 1))) = w64 34) by (apply getr_w64; [exact A3 | lia]).
  assert (E5 : getr regs (Z_to_bv 5 (10 + (0 + 1 + 1 + 1 + 1 + 1))) = w64 0) by (apply getr_w64; [exact A5 | lia]).
  apply rz_ecall; [exact Hh | exact Hl | exact Hec |].
  set (ms := svc_set (@mkst fx regs pc m rom)).
  assert (G1 : ms_gpr ms 1 = w64 len) by (unfold ms; rewrite svc_gpr by lia; exact E1).
  assert (G2 : ms_gpr ms 2 = w64 0) by (unfold ms; rewrite svc_gpr by lia; exact E2).
  assert (G3 : ms_gpr ms 3 = w64 34) by (unfold ms; rewrite svc_gpr by lia; exact E3).
  assert (G5 : ms_gpr ms 5 = w64 0) by (unfold ms; rewrite svc_gpr by lia; exact E5).
  apply (rzc_mmap_fresh_na segs cfg Hoff ms md (getr regs 17) K Hh (svc_pending regs pc m rom) Hno).
  - rewrite G5. reflexivity.
  - rewrite G3. reflexivity.
  - rewrite G1. apply w_is0_w64. lia.
  - rewrite G2, G3, G5. reflexivity.
  - rewrite G2, G3, G5. reflexivity.
  - rewrite G1, u_w64 by lia. rewrite <- page_round_eq. exact Hex.
  - intros a Ha. rewrite G3, G1, u_w64 by lia. rewrite G1, u_w64 in Ha by lia. rewrite <- page_round_eq in Ha |- *.
    unfold ms. rewrite svc_after. exact (Hc a Ha).
Qed.

(* [comment removed for export] *)
#[using="Hoff"] Lemma rz_mprotect : forall L s p regs pc m md K,
  at_ecall segs L s (KMprotect p) regs pc ->
  m_halted md = None -> m_vm_lazy md = [] ->
  loc_addr L (LMem p) mod PGSZ = 0 -> 0 <= loc_addr L (LMem p) -> loc_addr L (LMem p) + PGSZ < 2 ^ 64 ->
  map_contains (vm_noaccess (m_vmmaps md)) (w64 (loc_addr L (LMem p))) (w64 PGSZ)
    && map_contains (vm_maps (m_vmmaps md)) (w64 (loc_addr L (LMem p))) (w64 PGSZ) = true ->
  mprotect_budget_ok md (w64 (loc_addr L (LMem p))) (w64 PGSZ) = true ->
  realizes_cfg segs cfg (mkCfg (@mkst fx (regupd regs 10 (w64 0)) (bv_add pc (w64 4))
                                   (mem_after m (mkEffect (w64 0) [] [(w64 (loc_addr L (LMem p)), w64 PGSZ)])) rom)
                               (mprotect_model_next md (w64 (loc_addr L (LMem p))) (w64 PGSZ))) K ->
  realizes_cfg segs cfg (mkCfg (@mkst fx regs pc m rom) md) K.
Proof. LiaFast.lf_pins (fun (Hoff : LiaFast.U) => LiaFast.u0).
  intros L s p regs pc m md K (Hec & no & args & Hreq & Hno & Hargs) Hh Hl Hal Ha0 Hov Hcont Hbud Hc.
  cbn [req_regs] in Hreq. injection Hreq as <- <-. cbn [args_match] in Hargs. destruct Hargs as (A0 & A1 & A2 & _).
  assert (E0 : getr regs (Z_to_bv 5 (10 + 0)) = w64 (loc_addr L (LMem p))) by (apply getr_w64; [exact A0 | unfold PGSZ in Hov; lia]).
  assert (E1 : getr regs (Z_to_bv 5 (10 + (0 + 1))) = w64 PGSZ) by (apply getr_w64; [exact A1 | unfold PGSZ; lia]).
  assert (E2 : getr regs (Z_to_bv 5 (10 + (0 + 1 + 1))) = w64 3) by (apply getr_w64; [exact A2 | lia]).
  apply rz_ecall; [exact Hh | exact Hl | exact Hec |].
  set (ms := svc_set (@mkst fx regs pc m rom)).
  assert (G0 : ms_gpr ms 0 = w64 (loc_addr L (LMem p))) by (unfold ms; rewrite svc_gpr by lia; exact E0).
  assert (G1 : ms_gpr ms 1 = w64 PGSZ) by (unfold ms; rewrite svc_gpr by lia; exact E1).
  assert (G2 : ms_gpr ms 2 = w64 3) by (unfold ms; rewrite svc_gpr by lia; exact E2).
  apply (rzc_mprotect_expose segs cfg Hoff ms md (getr regs 17) (w64 (loc_addr L (LMem p))) (w64 PGSZ) K Hh (svc_pending regs pc m rom) Hno).
  - intros o. rewrite (syscall_spec_mprotect segs ms (getr regs 17) md o Hno). rewrite G0, G1, G2.
    assert (R1 : Z.eqb (bv_unsigned (w64 (loc_addr L (LMem p))) mod page_size) 0 = true) by (rewrite u_w64 by (unfold PGSZ in Hov; lia); apply Z.eqb_eq; exact Hal).
    assert (R2 : (two_pow_64 <=? bv_unsigned (w64 (loc_addr L (LMem p))) + page_round_up_Z (bv_unsigned (w64 PGSZ)))%Z = false).
    { rewrite u_w64 by (unfold PGSZ in Hov; lia). apply Z.leb_gt. unfold two_pow_64. change (page_round_up_Z (bv_unsigned (w64 PGSZ))) with 4096. unfold PGSZ in Hov. lia. }
    exact (mprotect_spec_expose (w64 (loc_addr L (LMem p))) (w64 PGSZ) (w64 3) (sys_input segs ms (getr regs 17)) md o eq_refl R1 eq_refl R2 eq_refl Hcont).
  - exact Hbud.
  - unfold ms. rewrite svc_after. exact Hc.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_brk_query : forall L s regs pc m md K,
  at_ecall segs L s KBrkQuery regs pc ->
  m_halted md = None -> m_vm_lazy md = [] ->
  realizes_cfg segs cfg (mkCfg (@mkst fx (regupd regs 10 (vm_brk (m_vmmaps md))) (bv_add pc (w64 4))
                                   (mem_after m (mkEffect (vm_brk (m_vmmaps md)) [] [])) rom) md) K ->
  realizes_cfg segs cfg (mkCfg (@mkst fx regs pc m rom) md) K.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s regs pc m md K (Hec & no & args & Hreq & Hno & Hargs) Hh Hl Hc.
  cbn [req_regs] in Hreq. injection Hreq as <- <-. cbn [args_match] in Hargs. destruct Hargs as (A0 & _).
  assert (E0 : getr regs (Z_to_bv 5 (10 + 0)) = w64 0) by (apply getr_w64; [exact A0 | lia]).
  apply rz_ecall; [exact Hh | exact Hl | exact Hec |].
  set (ms := svc_set (@mkst fx regs pc m rom)).
  assert (G0 : ms_gpr ms 0 = w64 0) by (unfold ms; rewrite svc_gpr by lia; exact E0).
  apply (rzc_brk_query segs cfg ms md (getr regs 17) (w64 0) K Hh (svc_pending regs pc m rom) Hno G0 (or_introl eq_refl)).
  unfold ms. rewrite svc_after. exact Hc.
Qed.

(* [comment removed for export] *)
#[using="Hoff"] Lemma rz_brk_grow : forall L s n regs pc m md K,
  at_ecall segs L s (KBrkGrow n) regs pc ->
  m_halted md = None -> m_vm_lazy md = [] ->
  0 < brk_cur L s + PGSZ * n < 2 ^ 64 ->
  bv_unsigned (min_brk (m_vmmaps md)) <= brk_cur L s + PGSZ * n ->
  bv_unsigned (vm_brk (m_vmmaps md)) < brk_cur L s + PGSZ * n ->
  (brk_grow_ok md (w64 (brk_cur L s + PGSZ * n)) (w64 (brk_cur L s + PGSZ * n)) = true ->
     realizes_cfg segs cfg (mkCfg (@mkst fx (regupd regs 10 (w64 (brk_cur L s + PGSZ * n))) (bv_add pc (w64 4))
          (mem_after m (brk_eff (w64 (brk_cur L s + PGSZ * n)) (w64 (brk_cur L s + PGSZ * n)) (vm_brk (m_vmmaps md)))) rom)
        (with_brk_next md (w64 (brk_cur L s + PGSZ * n)) (w64 (brk_cur L s + PGSZ * n)))) K) ->
  (brk_grow_ok md (w64 (brk_cur L s + PGSZ * n)) (w64 (brk_cur L s + PGSZ * n)) = false ->
     realizes_cfg segs cfg (mkCfg (@mkst fx (regupd regs 10 (vm_brk (m_vmmaps md))) (bv_add pc (w64 4))
          (mem_after m (mkEffect (vm_brk (m_vmmaps md)) [] [])) rom) md) K) ->
  realizes_cfg segs cfg (mkCfg (@mkst fx regs pc m rom) md) K.
Proof. LiaFast.lf_pins (fun (Hoff : LiaFast.U) => LiaFast.u0).
  intros L s n regs pc m md K (Hec & no & args & Hreq & Hno & Hargs) Hh Hl Hr Hmin Hgt Hc1 Hc2.
  cbn [req_regs] in Hreq. injection Hreq as <- <-. cbn [args_match] in Hargs. destruct Hargs as (A0 & _).
  assert (E0 : getr regs (Z_to_bv 5 (10 + 0)) = w64 (brk_cur L s + PGSZ * n)) by (apply getr_w64; [exact A0 | lia]).
  apply rz_ecall; [exact Hh | exact Hl | exact Hec |].
  set (ms := svc_set (@mkst fx regs pc m rom)).
  assert (G0 : ms_gpr ms 0 = w64 (brk_cur L s + PGSZ * n)) by (unfold ms; rewrite svc_gpr by lia; exact E0).
  assert (U0 : bv_unsigned (w64 (brk_cur L s + PGSZ * n)) = brk_cur L s + PGSZ * n) by (apply u_w64; lia).
  destruct (brk_grow_ok md (w64 (brk_cur L s + PGSZ * n)) (w64 (brk_cur L s + PGSZ * n))) eqn:Eg.
  - apply (rzc_brk_grow segs cfg Hoff ms md (getr regs 17) _ K Hh (svc_pending regs pc m rom) Hno G0).
    + apply w_is0_w64. lia.
    + rewrite U0. exact Hmin.
    + rewrite U0. exact Hgt.
    + exact Eg.
    + unfold ms. rewrite svc_after. exact (Hc1 eq_refl).
  - apply (rzc_brk_grow_forced_fail segs cfg ms md (getr regs 17) _ K Hh (svc_pending regs pc m rom) Hno G0).
    + apply w_is0_w64. lia.
    + rewrite U0. exact Hmin.
    + rewrite U0. exact Hgt.
    + exact Eg.
    + unfold ms. rewrite svc_after. exact (Hc2 eq_refl).
Qed.

(* [comment removed for export] *)
#[using="Hoff"] Lemma rz_guard : forall L s regs pc m md K,
  at_ecall segs L s KGuard regs pc ->
  m_halted md = None -> m_vm_lazy md = [] ->
  brk_base L s mod PGSZ = 0 -> 0 < brk_base L s -> brk_base L s + PGSZ <= alloc_top (m_vmmaps md) ->
  region_free (vm_reserved (m_vmmaps md)) (w64 (brk_base L s)) (w64 PGSZ)
    && map_contains (vm_maps (m_vmmaps md)) (w64 (brk_base L s)) (w64 PGSZ) = true ->
  realizes_cfg segs cfg (mkCfg (@mkst fx (regupd regs 10 (w64 (brk_base L s))) (bv_add pc (w64 4))
                                   (mem_after m (mkEffectU (w64 (brk_base L s)) [] [] [(w64 (brk_base L s), w64 PGSZ)] [] [])) rom)
                               (fixed_na_next (w64 50) (w64 (brk_base L s)) (w64 PGSZ) md)) K ->
  realizes_cfg segs cfg (mkCfg (@mkst fx regs pc m rom) md) K.
Proof. LiaFast.lf_pins (fun (Hoff : LiaFast.U) => LiaFast.u0).
  intros L s regs pc m md K (Hec & no & args & Hreq & Hno & Hargs) Hh Hl Hal Hpos Htop Hfree Hc.
  cbn [req_regs] in Hreq. injection Hreq as <- <-. cbn [args_match] in Hargs. destruct Hargs as (A0 & A1 & A2 & A3 & A4 & A5 & _).
  pose proof (alloc_top_lt (m_vmmaps md)) as Hat.
  assert (E0 : getr regs (Z_to_bv 5 (10 + 0)) = w64 (brk_base L s)) by (apply getr_w64; [exact A0 | unfold two_pow_64 in Hat; unfold PGSZ in Htop; lia]).
  assert (E1 : getr regs (Z_to_bv 5 (10 + (0 + 1))) = w64 PGSZ) by (apply getr_w64; [exact A1 | unfold PGSZ; lia]).
  assert (E2 : getr regs (Z_to_bv 5 (10 + (0 + 1 + 1))) = w64 0) by (apply getr_w64; [exact A2 | lia]).
  assert (E3 : getr regs (Z_to_bv 5 (10 + (0 + 1 + 1 + 1))) = w64 50) by (apply getr_w64; [exact A3 | lia]).
  assert (E5 : getr regs (Z_to_bv 5 (10 + (0 + 1 + 1 + 1 + 1 + 1))) = w64 0) by (apply getr_w64; [exact A5 | lia]).
  apply rz_ecall; [exact Hh | exact Hl | exact Hec |].
  set (ms := svc_set (@mkst fx regs pc m rom)).
  assert (G0 : ms_gpr ms 0 = w64 (brk_base L s)) by (unfold ms; rewrite svc_gpr by lia; exact E0).
  assert (G1 : ms_gpr ms 1 = w64 PGSZ) by (unfold ms; rewrite svc_gpr by lia; exact E1).
  assert (G2 : ms_gpr ms 2 = w64 0) by (unfold ms; rewrite svc_gpr by lia; exact E2).
  assert (G3 : ms_gpr ms 3 = w64 50) by (unfold ms; rewrite svc_gpr by lia; exact E3).
  assert (G5 : ms_gpr ms 5 = w64 0) by (unfold ms; rewrite svc_gpr by lia; exact E5).
  assert (UB : bv_unsigned (w64 (brk_base L s)) = brk_base L s) by (apply u_w64; unfold two_pow_64 in Hat; unfold PGSZ in Htop; lia).
  assert (BR := branch_fixed_na_contained segs ms (getr regs 17) md Hno).
  rewrite G0, G1, G2, G3, G5 in BR.
  change (Z_to_bv 64 (page_round_up_Z (bv_unsigned (w64 PGSZ)))) with (w64 PGSZ) in BR.
  specialize (BR eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl).
  assert (FG : fixed_gate md (w64 (brk_base L s)) (w64 PGSZ)).
  { unfold fixed_gate. rewrite UB. change (page_round_up_Z (bv_unsigned (w64 PGSZ))) with 4096. unfold PGSZ in *. unfold page_size. lia. }
  specialize (BR FG Hfree).
  eapply (rzc_silent1 segs cfg); [eapply (node_mmap_fixed_na_contained segs cfg Hoff ms md (getr regs 17) (w64 (brk_base L s)) (w64 PGSZ) (w64 50) Hh (svc_pending regs pc m rom) Hno) |].
  - rewrite UB. unfold PGSZ in Htop. lia.
  - exact BR.
  - unfold ms. rewrite svc_after. exact Hc.
Qed.
End Nodes.
