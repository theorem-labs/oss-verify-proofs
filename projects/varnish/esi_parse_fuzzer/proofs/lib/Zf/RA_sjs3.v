(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require ImgA RA_seql RA_f93z.

Module RA_pdfk.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA RA_seql.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor5a9.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_after_call segs m m' MU WM.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietml6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietml6.dlia3.
(* [comment removed for export] *)

Definition T_PTR : Z := 9.
Definition T_INT : Z := 10.

(* [comment removed for export] *)
Definition int_of_slot (v : word) : word := sx32 v.

Definition pop_arg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (ARG AP VA : Z) (slots : list word) (i : Z) (res : word) (old2 : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(ARG, ARG + 16); (AP, AP + 8)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' ARG [C8 res; CB 8 old2]
    /\ rw_cells rsegs m' AP [C8 (Z_to_bv 64 (VA + 8 * (i + 1)))]
    /\ va_area m' VA slots.

(* [comment removed for export] *)
Lemma pop_arg_int_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ARG AP VA : Z) (slots : list word) (i : Z) (v : word) (old1 old2 : list byte),
  a0 = Z_to_bv 64 ARG -> a1 = Z_to_bv 64 T_INT -> a2 = Z_to_bv 64 AP ->
  rw_cells rsegs m ARG [CB 8 old1; CB 8 old2] -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * i))] -> va_area m VA slots ->
  nth_error slots (Z.to_nat i) = Some v -> (0 <= i)%Z ->
  (ARG + 16 <= AP \/ AP + 8 <= ARG)%Z -> (AP + 8 <= VA)%Z -> (ARG + 16 <= VA)%Z ->
  mem_inv rsegs m ->
  evt rsegs (pop_arg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ARG AP VA slots i (sx32 v) old2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9f3a8) fc None m (seg_rom rsegs)).
Proof.
  intros until old2. intros -> -> -> HA HP HV Hn Hi SEP1 SEP2 SEP3 MI. unfold T_INT. unfold va_area in HV.
  pose proof (munch_refl [(ARG, ARG + 16); (AP, AP + 8)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (rw_cells_bound _ _ _ _ HA) as B1. pose proof (rw_cells_bound _ _ _ _ HP) as B2. pose proof (bytes_at_bound _ _ _ _ HV) as B3.
  cbn [cells_size csize Nat.add] in B1, B2. rewrite u64s_length in B3. pose proof (nth_error_lt _ _ _ Hn) as IL.
  do 3 zs. if_lit. do 7 zs.
  zs. zs. zs.
  pose proof (va_read4 _ VA slots i v (Z_to_bv 64 (VA + 8 * i)) HV Hn Hi eq_refl) as RD.
  zs. zs. zs.
  replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in * by lia.
  finish. all: unfold va_area; assumption.
Qed.

Lemma pop_arg_ptr_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ARG AP VA : Z) (slots : list word) (i : Z) (v : word) (old1 old2 : list byte),
  a0 = Z_to_bv 64 ARG -> a1 = Z_to_bv 64 T_PTR -> a2 = Z_to_bv 64 AP ->
  rw_cells rsegs m ARG [CB 8 old1; CB 8 old2] -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * i))] -> va_area m VA slots ->
  nth_error slots (Z.to_nat i) = Some v -> (0 <= i)%Z ->
  (ARG + 16 <= AP \/ AP + 8 <= ARG)%Z -> (AP + 8 <= VA)%Z -> (ARG + 16 <= VA)%Z ->
  mem_inv rsegs m ->
  evt rsegs (pop_arg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ARG AP VA slots i v old2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9f3a8) fc None m (seg_rom rsegs)).
Proof.
  intros until old2. intros -> -> -> HA HP HV Hn Hi SEP1 SEP2 SEP3 MI. unfold T_PTR. unfold va_area in HV.
  pose proof (munch_refl [(ARG, ARG + 16); (AP, AP + 8)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (rw_cells_bound _ _ _ _ HA) as B1. pose proof (rw_cells_bound _ _ _ _ HP) as B2. pose proof (bytes_at_bound _ _ _ _ HV) as B3.
  cbn [cells_size csize Nat.add] in B1, B2. rewrite u64s_length in B3. pose proof (nth_error_lt _ _ _ Hn) as IL.
  do 3 zs. if_lit. do 7 zs.
  zs. zs. zs.
  pose proof (va_read8 _ VA slots i v (Z_to_bv 64 (VA + 8 * i)) HV Hn Hi eq_refl) as RD.
  zs. zs. zs.
  replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in * by lia.
  finish. all: unfold va_area; assumption.
Qed.
End RA_pdfk.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.ImgA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_seql OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_f93z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_sjs3.RA_pdfk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIcp2qs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua AIcp3q7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpwpz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpwpz AIcpq85.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpwpz.AIcpdm8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpwpz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpq85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
Import ListNotations.
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac low_lemma P ::= RA_f93z.low_lemma_pf P.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= relow_store_hook m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= relow_all W m m' MU.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor5a9.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_after_call segs m m' MU WM.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietml6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietml6.dlia3.
(* [comment removed for export] *)
(* [comment removed for export] *) From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store_sfdx.
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FMT_C : list cell := [C1 (Z_to_bv 8 37); C1 (Z_to_bv 8 99); C1 (Z_to_bv 8 0)].   (* [comment removed for export] *)
Definition FMT_PFX : list cell :=                                                               (* [comment removed for export] *)
  [C1 (Z_to_bv 8 37); C1 (Z_to_bv 8 46); C1 (Z_to_bv 8 42); C1 (Z_to_bv 8 115); C1 (Z_to_bv 8 47); C1 (Z_to_bv 8 0)].
Definition FMT_HOST : list cell :=                                                              (* [comment removed for export] *)
  [C1 (Z_to_bv 8 72); C1 (Z_to_bv 8 111); C1 (Z_to_bv 8 115); C1 (Z_to_bv 8 116); C1 (Z_to_bv 8 58); C1 (Z_to_bv 8 32);
   C1 (Z_to_bv 8 37); C1 (Z_to_bv 8 46); C1 (Z_to_bv 8 42); C1 (Z_to_bv 8 115); C1 (Z_to_bv 8 37); C1 (Z_to_bv 8 99);
   C1 (Z_to_bv 8 0)].
Definition DIR_S : list cell := [C1 (Z_to_bv 8 37); C1 (Z_to_bv 8 46); C1 (Z_to_bv 8 42); C1 (Z_to_bv 8 115)].  (* [comment removed for export] *)
Definition DIR_C : list cell := [C1 (Z_to_bv 8 37); C1 (Z_to_bv 8 99)].                                             (* [comment removed for export] *)

(* [comment removed for export] *)
Definition sint32 (v : word) : Z := bv_swrap 32 (bv_unsigned v).
(* [comment removed for export] *)
Definition out_s (P : word) (hs : list byte) : list byte := firstn (Z.to_nat (strnlen_res (sint32 P) hs)) hs.
(* [comment removed for export] *)
Definition out_c (ch : word) : list byte := [Z_to_bv 8 (bv_unsigned ch mod 256)].

Lemma swrap32_id : forall z, (- 2^31 <= z < 2^31)%Z -> bv_swrap 32 z = z.
Proof. intros. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. cbn. lia. Qed.
Lemma sint32_range : forall v, (- 2^31 <= sint32 v < 2^31)%Z.
Proof. intros. unfold sint32. pose proof (bv_swrap_in_range 32 (bv_unsigned v) ltac:(discriminate)) as R.
  unfold bv_half_modulus, bv_modulus in R. cbn in R. lia. Qed.

Lemma signed_lit : forall z, (- 2^63 <= z < 2^63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof. intros. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. cbn. lia. Qed.

(* [comment removed for export] *)
Lemma fr1_recast : forall segs m a q0 q1 q2 q3 q4 rest,
  rw_cells segs m a (C8 q0 :: C8 q1 :: C8 q2 :: C8 q3 :: C8 q4 :: rest) ->
  rw_cells segs m a (CB 40 (le8 q0 ++ le8 q1 ++ le8 q2 ++ le8 q3 ++ le8 q4) :: rest).
Proof.
  intros. eapply rw_cells_recast; [exact H| |].
  - destruct H as [[W _] _]. cbn in W |- *. tauto.
  - cbn [cells_bytes cbytes]. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma fra_recast : forall segs m a v j, rw_cells segs m a [C8 v; CB 8 j] -> rw_cells segs m a [CB 8 (le8 v); CB 8 j].
Proof.
  intros. eapply rw_cells_recast; [exact H| |].
  - destruct H as [[W _] _]. cbn in W |- *. tauto.
  - reflexivity.
Qed.
Lemma fr2_recast3 : forall segs m a n1 n3 (l1 l3 : list byte) (b : byte) rest,
  rw_cells segs m a (CB n1 l1 :: C1 b :: CB n3 l3 :: rest) ->
  rw_cells segs m a (CB (n1 + 1 + n3) (l1 ++ b :: l3) :: rest).
Proof.
  intros. eapply rw_cells_recast; [exact H| |].
  - destruct H as [[W _] _]. cbn [cells_wf cell_wf] in W |- *. split; [rewrite length_app; cbn [length]; lia|tauto].
  - cbn [cells_bytes cbytes]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma ro_cells_app : forall segs m A cs1 cs2,
  ro_cells segs m A (cs1 ++ cs2) <-> ro_cells segs m A cs1 /\ ro_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold ro_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app. rewrite bytes_at_app.
  split.
  - intros ((W1 & W2) & (B1 & B2)). rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros ((W1 & B1) & (W2 & B2)). rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.
Lemma ro_cells_bytes_at : forall segs m A cs, ro_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [_ H]. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PC_TOP : Z := 0x9e628.
Definition INT_MAX : Z := 2147483647.

Section PCTOP.
  Context {Clg : Ceiling}.   (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo A Fp B D : Z) (n : nat) (mode : word) (VA : Z) (slots : list word) (HS : Z) (hs : list byte) (canary : word).
  Variables (FMT : list cell) (la : Z) (SB : Z) (K : nat) (m0 : word -> option byte).

  (* [comment removed for export] *)
  Definition pc_lits : list cell :=
    [C8 (Z_to_bv 64 18446744072850558157); C8 (Z_to_bv 64 18446744073709486079);
     C8 (Z_to_bv 64 (bv_unsigned sp + 96)); C8 (Z_to_bv 64 (bv_unsigned sp + 264)); C8 (Z_to_bv 64 (bv_unsigned sp + 0));
     C8 (Z_to_bv 64 75913); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 SSP_GUARD); C8 (Z_to_bv 64 214748364)].
  Definition pc_saved : list cell :=
    [C8 canary; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition pc_layout : Prop :=
    let q := bv_unsigned sp in
    Fp = (q + 416)%Z /\ B = (q + 16)%Z /\ (0 <= lo)%Z /\ (lo <= q - PC2_DEPTH)%Z /\ (alloc_ceiling <= lo)%Z   (* [comment removed for export] *)
    /\ (q + 672 <= VA)%Z /\ (VA + 8 * Z.of_nat (length slots) <= 2^63)%Z
    /\ (IMG_LO <= A)%Z /\ (A + Z.of_nat (cells_size FMT) <= RO_TOP)%Z /\ dst_ok D n /\ (D + Z.of_nat n <= lo)%Z
    /\ (HS + Z.of_nat (length hs) <= lo)%Z /\ (~ (D < HS + Z.of_nat (length hs) /\ HS < D + Z.of_nat n))%Z
    /\ dst_zone D (Z.of_nat n) /\ (Z.of_nat n <= 2^31)%Z /\ la = Z.of_nat (cells_size FMT).   (* [comment removed for export] *)

  Definition pctop (off cnt l i : Z) (o : list byte) : machine_state -> Prop :=
    fun ms => exists (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2x s6x s7x s8x s9x s11x t3 t4 t5 t6 : word)
                     (j40 ja1 ja2 j304 w p : list byte) (m : word -> option byte),
      ms = MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 37) (Z_to_bv 64 INT_MAX)
                   a0 a1 a2 a3 a4 a5 a6 a7 s2x (Z_to_bv 64 cnt) (Z_to_bv 64 Fp) (Z_to_bv 64 (A + off))
                   s6x s7x s8x s9x (Z_to_bv 64 l) s11x t3 t4 t5 t6)
              F (Z_to_bv 64 PC_TOP) fc None m (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - 4928, bv_unsigned sp + 8); (B, B + 80); (Fp, Fp + 248); (D, D + Z.of_nat n)]%Z m0 m
      /\ wmono rsegs m0 m /\ mem_inv rsegs m
      /\ stk rsegs m lo (bv_unsigned sp + -544)
      /\ ro_cells rsegs m A FMT
      /\ rw_cells rsegs m (bv_unsigned sp + -544) (CB 40 j40 :: pc_lits)
      /\ rw_cells rsegs m (bv_unsigned sp + -432) [CB 8 ja1; CB 8 ja2]
      /\ rw_cells rsegs m (bv_unsigned sp + -416) (CB 304 j304 :: pc_saved)
      /\ sink Fp B D n m mode w p /\ w ++ p = o
      /\ rw_cells rsegs m (bv_unsigned sp) [C8 (Z_to_bv 64 (VA + 8 * i))]
      /\ va_area m VA slots /\ bytes_at rsegs m HS hs /\ ssp_cells m canary
      /\ sf2 A la D n HS hs SB K (bv_unsigned sp - 544) (bv_unsigned sp + 96) m.
End PCTOP.

Ltac unpack_top H :=
  let w := fresh "w" in let p := fresh "p" in
  destruct H as (rax & x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & s2x & s6x & s7x & s8x & s9x & s11x & x3 & x4 & x5 & x6
                 & j40 & ja1 & ja2 & j304 & w & p & mq & -> & MU & WM & MI & ST & HF & FR1 & FRA & FR2 & SNK & HO & APC & VAA & HSB & [SSP1 SSP2] & SF);
  unfold pc_lits in FR1; unfold pc_saved in FR2; unfold GOT_SSP, SSP_GUARD in SSP1, SSP2, FR1; unfold va_area in VAA.

(* [comment removed for export] *)
Ltac sx1 := match goal with |- context [bv_swrap 32 ?z] =>
  lazymatch z with context [bv_swrap 32 _] => fail | _ => rewrite (swrap32_id z) by lia end end.
Ltac sx2 := match goal with |- context [bv_signed (Z_to_bv 64 ?z)] =>
  lazymatch z with context [bv_swrap 32 _] => fail | _ => rewrite (signed_lit z) by lia end end.
Ltac sx3 := match goal with |- context [(?a mod 18446744073709551616)%Z] =>
  lazymatch a with context [bv_swrap 32 _] => fail | _ => rewrite (Z.mod_small a 18446744073709551616) by lia end end.
Ltac sx := repeat first [sx1 | sx3]; repeat sx2.
Ltac sxh K := repeat match type of K with context [bv_swrap 32 ?z] =>
    lazymatch z with context [bv_swrap 32 _] => fail | _ => rewrite (swrap32_id z) in K by lia end end;
  repeat match type of K with context [(?a mod 18446744073709551616)%Z] =>
    lazymatch a with context [bv_swrap 32 _] => fail | _ => rewrite (Z.mod_small a 18446744073709551616) in K by lia end end;
  repeat match type of K with context [bv_signed (Z_to_bv 64 ?z)] =>
    lazymatch z with context [bv_swrap 32 _] => fail | _ => rewrite (signed_lit z) in K by lia end end.
Ltac brf K := if_cases K; zify_cond K; sxh K.
Ltac br K := brf K; try (exfalso; lia).
(* [comment removed for export] *)
Ltac pack_top :=
  unfold pctop, pc_lits, pc_saved, PC_TOP, INT_MAX, SSP_GUARD;
  hot_eexists_all;
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))))))));
  [ | eassumption | eassumption | assumption | try eassumption | eassumption | try eassumption | try eassumption | try eassumption
    | pack_sink | try reflexivity | try eassumption | first [eassumption | unfold va_area; eassumption] | eassumption
    | first [assumption | split; assumption] | assumption ].
(* [comment removed for export] *)
Ltac fwx_src := first [ assumption | left; reflexivity | left; lia
                      | right; match goal with R : range_ok _ ?a ?n |- range_ok _ ?a' ?n' => eapply (range_ok_sub _ a n a' n'); [exact R| lia| lia| lia] end
                      | right; match goal with SF : sf2 _ _ _ _ _ _ _ _ _ _ ?mm |- range_ok ?mm _ _ =>
                                 first [ eapply sf2_fmt_range; [exact SF| lia| lia| lia]
                                       | eapply sf2_stack_range; [exact SF| lia| lia| lia] ] end ].
Ltac fwritex_side :=
  lazymatch goal with
  | |- sink _ _ _ _ _ _ _ _ => pack_sink
  | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
  | |- bytes_at _ _ _ _ => rewrite ?unsigned_lit by lia; first [ eassumption | apply bytes_at_nil; lia ]
  | |- sn_layout _ _ _ _ _ _ _ _ => unfold sn_layout; rewrite ?unsigned_lit by lia; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [assumption | lia | eapply dst_zone_sub; [eassumption| lia| lia]]
  | |- mem_inv _ _ => assumption
  | |- sfx _ _ _ _ _ _ _ _ => rewrite ?unsigned_lit by lia; eapply sf2_sfx; [eassumption | fwx_src | lia]
  | |- @eq nat _ _ => reflexivity || (cbn; lia) || (rewrite ?length_app, ?firstn_length; cbn; lia)
  | |- ?G => first [ reflexivity | lia | idtac "FWX-SIDE-FAIL:" G; fail ]
  end.
Ltac call_fwritex :=
  call_icpt fwritex_spec by (idtac; fwritex_side);
  clear_rdf;
  match goal with H : stk _ _ _ _ |- _ => let n := fresh "ST" in rename H into n end;
  match goal with H : sink _ _ _ _ _ _ _ _ |- _ =>
    first [ rewrite fwx_fits in H by (cbn; lia) | rewrite fwx_spills in H by (cbn; lia) | idtac ]; cbn [fst snd] in H; rewrite ?app_nil_r in H;
    let a := fresh "FL" in let b := fresh "CKC" in let c := fresh "BUF" in let d := fresh "DST" in unpack_sink H a b c d end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma seg_entry : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte)
    (lo A Fp B D : Z) (n : nat) (mode : word) (VA : Z) (slots : list word) (HS : Z) (hs : list byte) (canary : word) (FMT : list cell)
    (la : Z) (SB : Z) (K : nat),
  let q := bv_unsigned sp in
  a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = sp -> a3 = Z_to_bv 64 (q + 96) -> a4 = Z_to_bv 64 (q + 264) ->
  stk rsegs m lo q -> ro_cells rsegs m A FMT -> ssp_cells m canary -> sink Fp B D n m mode [] [] ->
  rw_cells rsegs m q [C8 (Z_to_bv 64 VA)] -> va_area m VA slots -> bytes_at rsegs m HS hs ->
  mem_inv rsegs m ->
  sf2 A la D n HS hs SB K (q - 544) (q + 96) m ->
  pc_layout sp lo A Fp B D n VA slots HS hs FMT la ->
  evt rsegs (pctop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A Fp B D n mode VA slots HS hs canary FMT la SB K m 0 0 0 0 [])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PRINTF_CORE) fc None m (seg_rom rsegs)).
Proof.
  intros until K. cbv zeta. intros -> -> -> -> -> ST HF [SSP1 SSP2] SNK APC VAA HSB MI SF LAY.
  (first [ dand16 LAY as HFp HB LO0 LO GT VLO VHI ARL ART GD DLO HSL HSD KH N31 HLA | destruct LAY as (HFp & HB & LO0 & LO & GT & VLO & VHI & ARL & ART & GD & DLO & HSL & HSD & KH & N31 & HLA) ]).
  pose proof alloc_ceiling_val as CV.
  unfold GOT_SSP, SSP_GUARD, GLOBALS_TOP, RO_TOP, PC2_DEPTH, PRINTF_CORE, dst_ok, IMG_LO, IMG_HI in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 4928, bv_unsigned sp + 8); (B, B + 80); (Fp, Fp + 248); (D, D + Z.of_nat n)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (ro_cells_bound _ _ _ _ HF) as AB.
  unpack_sink SNK FL CKC BUF DST. unfold va_area in VAA.
  rewrite <- (Z_to_bv_bv_unsigned sp) at 1.
  carve_frame 544%nat ST.
  do 43 zs. name_junk FR.
  (* [comment removed for export] *)
  apply (rw_cells_split_CB rsegs _ _ [_;_;_;_;_;_;_;_;_;_] 320 _ _ [8; 8; 304]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app] in FR.
  apply (proj1 (rw_cells_app rsegs _ _ [_;_;_;_;_;_;_;_;_;_] _)) in FR. destruct FR as [FR1 FR].
  apply (proj1 (rw_cells_app rsegs _ _ [_;_] _)) in FR. destruct FR as [FRA FR2].
  cbn [cells_size csize Nat.add] in FRA, FR2.
  replace (bv_unsigned sp + -544 + Z.of_nat 112)%Z with (bv_unsigned sp + -432)%Z in FRA by lia.
  replace (bv_unsigned sp + -544 + Z.of_nat 112 + Z.of_nat 16)%Z with (bv_unsigned sp + -416)%Z in FR2 by lia.
  name_junk FRA. name_junk FR2.
  (* [comment removed for export] *)
  lazymatch type of FR1 with rw_cells _ ?mq ?a [?c0; ?c1; ?c2; ?c3; ?c4; C8 sp; ?c6; ?c7; ?c8; ?c9] =>
    assert (FR1' : rw_cells rsegs mq a [c0; c1; c2; c3; c4; C8 (Z_to_bv 64 (bv_unsigned sp + 0)); c6; c7; c8; c9])
      by (rewrite Z.add_0_r, (Z_to_bv_bv_unsigned sp); exact FR1); clear FR1; rename FR1' into FR1 end.
  apply evt_done. unfold pctop, pc_lits, pc_saved, PC_TOP, INT_MAX, SSP_GUARD.
  hot_eexists_all.
  split. { rewrite Z.add_0_r. reflexivity. }
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|]. split; [eassumption|].
  split; [exact FR1|]. split; [exact FRA|]. split; [exact FR2|].
  split; [pack_sink|]. split; [reflexivity|].
  split. { rewrite Z.mul_0_r, Z.add_0_r. exact APC. }
  split; [exact VAA|]. split; [assumption|]. split; [split; assumption|]. assumption.
Qed.

End CEIL.
