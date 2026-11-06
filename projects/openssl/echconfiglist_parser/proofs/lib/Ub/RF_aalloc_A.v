(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Agent Require Import F_malloc_free F_malloc_fast MallocKit_B3.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import RMallocRep RMallocTree RMallocKit_B RF_get_meta.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

(* [comment removed for export] *)
Definition raa_pro_post (sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) (al n : Z) : machine_state -> Prop :=
  fun ms' => exists a2 m' junk,
    ms' = MS (mkR (Z_to_bv 64 0x2b7a8c) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 al) (Z_to_bv 64 n) (Z_to_bv 64 (n + al - 16)) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 rmalloc_entry) fc None m' (seg_rom usegs)
    /\ rw_cells usegs m' (bv_unsigned sp + -32) [CB 8 junk; C8 s1; C8 s0; C8 ra]
    /\ stk usegs m' lo (bv_unsigned sp + -32)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'.

Lemma raa_pro_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo al n : Z),
  a0 = Z_to_bv 64 al -> a1 = Z_to_bv 64 n -> (exists k, 4 <= k <= 6 /\ al = 2 ^ k) -> 1 <= n -> n + al < MMAP_THRESHOLD ->
  rw_cells usegs m (RCTX + 928) [C4 (wz 0); C4 (wz 0)] ->
  stk usegs m lo (bv_unsigned sp) -> 0x358000 <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv usegs m ->
  evt usegs (raa_pro_post sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra F fc lo m al n)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b79ec) fc None m (seg_rom usegs)).
Proof. try hcb. try hsb.
  intros until n. intros HA0 HA1 (k & Hk & Hal) N1 N RZ ST ILO LO MI. subst a0 a1.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold MMAP_THRESHOLD in N.
  assert (AL : al = 16 \/ al = 32 \/ al = 64).
  { assert (k = 4 \/ k = 5 \/ k = 6) as [->|[->| ->]] by lia; [left| right; left| right; right]; rewrite Hal; reflexivity. }
  clear Hk Hal k.
  change (RCTX + 928) with 0x356740 in RZ.
  carve_frame 32%nat ST. step. step. step. step.
  (* [comment removed for export] *)
  step. step. rewrite !unsigned_lit by lia. replace (Z.land al (al + -1)) with 0 by (destruct AL as [->|[->| ->]]; reflexivity).
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  (* [comment removed for export] *)
  step. rewrite ?unsigned_lit, Z.shiftr_div_pow2, Z.div_small by lia.
  step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  (* [comment removed for export] *)
  step. rewrite ?unsigned_lit, zb_lxor_ones by lia. step. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
  (* [comment removed for export] *)
  step. step. change (sx32 (wz 0)) with (Z_to_bv 64 0). step. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. }
  (* [comment removed for export] *)
  assert (FIN : forall a2v, evt usegs (raa_pro_post sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra F fc lo m al n)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 n) a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x2b7a78) fc None m0 (seg_rom usegs))).
  { intros a2v. step. step. step. rewrite ?unsigned_lit by lia. step. replace (al + n + -16) with (n + al - 16) by lia.
    step. apply evt_done. unfold raa_pro_post, rmalloc_entry. do 3 eexists. split; [reflexivity|].
    split; [exact FR|]. split; [exact ST|]. auto. }
  step. step. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia.
  - apply FIN.
  - step. replace (Z_to_bv 64 16) with (Z_to_bv 64 al) by (f_equal; lia). apply FIN.
Qed.
End HCW.
