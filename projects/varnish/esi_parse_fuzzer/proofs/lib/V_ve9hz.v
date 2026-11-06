(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)

Definition vep_default_cb_entry := 0x1bd48%Z.
Definition CB_FRAME := 16%Z.

Definition vep_default_cb_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (l lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (v Fcb_x + l)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - CB_FRAME, bv_unsigned sp); (VEP + 56, VEP + 64)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' VEP (vep_cells (fupd v Fcb_x (v Fcb_x + l)%Z) tag q).

Lemma vep_default_cb_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (VC VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (l : Z)
         (vcpad : list byte) (resp wrk : Z) (vcrest : list byte) (lo : Z),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp) ->
  (lo + CB_FRAME <= bv_unsigned sp)%Z ->
  a0 = Z_to_bv 64 VC -> (0 < VC)%Z ->
  rw_cells rsegs m VC (vc_cells vcpad resp wrk vcrest) ->
  length vcpad = 12%nat -> length vcrest = 40%nat ->
  a1 = Z_to_bv 64 (VEP + 56) ->
  rw_cells rsegs m VEP (vep_cells v tag q) ->
  length tag = 8%nat -> vep_pads_wf q ->
  a2 = Z_to_bv 64 l ->
  (0 <= v Fcb_x)%Z -> (0 <= l)%Z -> (v Fcb_x + l < 2^62)%Z ->
  (* [comment removed for export] *)
  (VC + 72 <= bv_unsigned sp - CB_FRAME \/ bv_unsigned sp <= VC)%Z ->
  (VEP + 312 <= bv_unsigned sp - CB_FRAME \/ bv_unsigned sp <= VEP)%Z ->
  (VC + 72 <= VEP \/ VEP + 312 <= VC)%Z ->
  evt rsegs (vep_default_cb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc VEP v tag q l lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 vep_default_cb_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros MI ST LO A0 VC0 VCC LP LR A1 VEPC TAG PADS A2 B0 B1 B2 SEP1 SEP2 SEP3.
  rewrite A0, A1, A2.
  pose proof (munch_refl [(bv_unsigned sp - CB_FRAME, bv_unsigned sp); (VEP + 56, VEP + 64)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (rw_cells_bound _ _ _ _ VEPC) as VEPB. rewrite (vep_cells_size v tag q TAG PADS) in VEPB.
  (first [ dand7 PADS as P36 P124 P140 P196 P236 P268 P308 | destruct PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]).
  unfold vep_cells in VEPC. unfold vc_cells in VCC.
  pose proof (rw_cells_bound _ _ _ _ VCC) as VCB. cbn [cells_size csize Nat.add length] in VCB.
  unfold CB_FRAME in *. unfold vep_default_cb_entry.
  carve_frame 16%nat ST.
  zstep. zstep.
  (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K. { exfalso. first [rewrite Z.mod_small in K by lia | idtac]; lia. }
  clear K.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  zstep. if_cases K; zify_cond K. { exfalso. revert K. vm_compute. congruence. }
  clear K.
  (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K. { exfalso. first [rewrite Z.mod_small in K by lia | idtac]; lia. }
  clear K.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  release_frame FR ST (bv_unsigned sp). finish.   (* [comment removed for export] *)
Qed.
