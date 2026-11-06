(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import
  PropExec CatSim CatExec SeqExec StoreOk ShapeAlg ShapeAlgCfg LibWritev LibWritevCfg.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase AsanWWritev AsanWSw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import ListNotations.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Section RB.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variables b sr : Z.
Variables (wj1 wj2 : Z) (ij1 ij2 : bv 21).
Hypothesis HC : SWCode segs b sr wj1 wj2 ij1 ij2.

Let F_120 := F_120 segs b sr wj1 wj2 ij1 ij2 HC.
Let F_124 := F_124 segs b sr wj1 wj2 ij1 ij2 HC.
Let F_128 := F_128 segs b sr wj1 wj2 ij1 ij2 HC.
Let F_12c := F_12c segs b sr wj1 wj2 ij1 ij2 HC.
Let F_130 := F_130 segs b sr wj1 wj2 ij1 ij2 HC.
Let F_134 := F_134 segs b sr wj1 wj2 ij1 ij2 HC.
Let F_138 := F_138 segs b sr wj1 wj2 ij1 ij2 HC.
Let F_13c := F_13c segs b sr wj1 wj2 ij1 ij2 HC.
Let F_140 := F_140 segs b sr wj1 wj2 ij1 ij2 HC.
Let F_144 := F_144 segs b sr wj1 wj2 ij1 ij2 HC.
Let F_148 := F_148 segs b sr wj1 wj2 ij1 ij2 HC.
Let F_14c := F_14c segs b sr wj1 wj2 ij1 ij2 HC.
Let F_150 := F_150 segs b sr wj1 wj2 ij1 ij2 HC.
Let F_154 := F_154 segs b sr wj1 wj2 ij1 ij2 HC.
Let F_e4 := F_e4 segs b sr wj1 wj2 ij1 ij2 HC.
Let F_e8 := F_e8 segs b sr wj1 wj2 ij1 ij2 HC.
Let F_ec := F_ec segs b sr wj1 wj2 ij1 ij2 HC.
Let F_f0 := F_f0 segs b sr wj1 wj2 ij1 ij2 HC.
Let F_f4 := F_f4 segs b sr wj1 wj2 ij1 ij2 HC.
Let F_f8 := F_f8 segs b sr wj1 wj2 ij1 ij2 HC.
Let F_fc := F_fc segs b sr wj1 wj2 ij1 ij2 HC.
Let F_100 := F_100 segs b sr wj1 wj2 ij1 ij2 HC.
Let F_104 := F_104 segs b sr wj1 wj2 ij1 ij2 HC.
Let F_108 := F_108 segs b sr wj1 wj2 ij1 ij2 HC.
Let F_10c := F_10c segs b sr wj1 wj2 ij1 ij2 HC.

(* [comment removed for export] *)
Lemma rb_c0 : forall model S T (fd f iovp k rem cnt : Z) (b0 l0 : word),
  m_halted model = None ->
  ms_svc_pending S = None -> ms_pc_val S = pcw b 0x120 ->
  rg S 10 = Z_to_bv 64 k -> rg S 19 = Z_to_bv 64 iovp -> rg S 18 = Z_to_bv 64 cnt -> rg S 22 = Z_to_bv 64 rem ->
  rg S 9 = Z_to_bv 64 f ->
  (1 <= k <= bv_unsigned l0)%Z -> (k < rem <= 2 ^ 30)%Z -> (cnt = 1 \/ cnt = 2)%Z ->
  (0 <= iovp)%Z -> (iovp + 16 <= 2 ^ 47)%Z -> (0 <= f)%Z -> (f + 124 <= 2 ^ 47)%Z -> (0 < fd < 2 ^ 31)%Z ->
  no_lazy model iovp (iovp + 16) -> no_lazy model (f + 120) (f + 124) ->
  (f + 124 <= iovp \/ iovp + 16 <= f + 120)%Z ->
  rdn segs (ms_mem S) (Z_to_bv 64 iovp) 8 = Some (word_to_le_bytes 8 b0) ->
  rdn segs (ms_mem S) (Z_to_bv 64 (iovp + 8)) 8 = Some (word_to_le_bytes 8 l0) ->
  rdn segs (ms_mem S) (Z_to_bv 64 (f + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
  store_ok segs (ms_mem S) (Z_to_bv 64 iovp) 16 = true ->
  (bv_unsigned b0 + bv_unsigned l0 <= 2 ^ 47)%Z ->
  (forall S', SWF S S' iovp (iovp + 16) -> ms_pc_val S' = pcw b 0x110 ->
     rg S' 17 = Z_to_bv 64 66 -> rg S' 10 = Z_to_bv 64 fd -> rg S' 11 = Z_to_bv 64 iovp -> rg S' 20 = Z_to_bv 64 iovp ->
     rg S' 12 = Z_to_bv 64 cnt -> rg S' 18 = Z_to_bv 64 cnt -> rg S' 22 = Z_to_bv 64 (rem - k) ->
     ms_mem S' = write_to_mem (write_to_mem (ms_mem S) (Z_to_bv 64 iovp) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned b0 + k))))
                   (Z_to_bv 64 (iovp + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned l0 - k))) ->
     realizes_cfg segs cfg (mkCfg S' model) T) ->
  realizes_cfg segs cfg (mkCfg S model) T.
Proof.
  intros model S T fd f iovp k rem cnt b0 l0 Hh Hsvc Hpc Ha0 Hs3 Hs2 Hs6 Hs1' Hk Hrem Hcnt Hi1 Hi2 Hf1 Hf2 Hfdr NLA NLF Hdfd
         R0 R8 Rfd SOK Hb0 HT.
  pose proof (u64_range l0) as Hl0. pose proof (u64_range b0) as Hb0'.
  (* [comment removed for export] *)
  eapply rzc_acc; [ assumption | assumption | eapply wacc_Branch; [ fetch_tac F_120 | reflexivity | exact D_120 ] | apply acc_ok_nil | ].
  rgn. rewrite Ha0, branch_lt0_pos by lia. rewrite Hpc. pcn.
  (* [comment removed for export] *)
  wld F_124 D_124 R8 NLA. rgn; rwregs; rewrite ?load8; vnorm.
  (* [comment removed for export] *)
  wst wacc_Op F_128 D_128. rgn; rwregs; rewrite ?load8; vnorm.
  rewrite alu_sltu_w, bvu_z by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia.
  (* [comment removed for export] *)
  wst wacc_ShiftImm F_12c D_12c. nst. cnorm.
  (* [comment removed for export] *)
  wst wacc_Op F_130 D_130. nst.
  (* [comment removed for export] *)
  wld F_134 D_134 R0 NLA. nst.
  (* [comment removed for export] *)
  wst wacc_Op F_138 D_138. nst. cnorm.
  (* [comment removed for export] *)
  wst wacc_Op F_13c D_13c. nst. rewrite alu_and, and0_l.
  (* [comment removed for export] *)
  wst wacc_Op F_140 D_140. nst.
  (* [comment removed for export] *)
  wst wacc_Op F_144 D_144. nst. rewrite w_add_z.
  (* [comment removed for export] *)
  wsd F_148 D_148 SOK NLA. nst.
  (* [comment removed for export] *)
  eapply rzc_acc; [ assumption | reflexivity | eapply wacc_Branch; [ fetch_tac F_14c | reflexivity | exact D_14c ] | apply acc_ok_nil | ].
  nst. cbn [branch_taken]. unfold bv_ltu. rewrite bvu_z by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [negb]. pcn.
  (* [comment removed for export] *)
  wst wacc_OpImm F_e4 D_e4. nst.
  (* [comment removed for export] *)
  wst wacc_OpImm F_e8 D_e8. nst.
  (* [comment removed for export] *)
  wst wacc_Op F_ec D_ec. nst.
  (* [comment removed for export] *)
  wld F_f0 D_f0 R8 NLA. nst.
  (* [comment removed for export] *)
  wst wacc_Op F_f4 D_f4. nst.
  (* [comment removed for export] *)
  wld F_f8 D_f8 Rfd NLF. nst. rewrite load4_pos by lia.
  (* [comment removed for export] *)
  wst wacc_Op32 F_fc D_fc. nst. rewrite subw_z by lia.
  (* [comment removed for export] *)
  wst wacc_Op F_100 D_100. nst. rewrite w_sub_z.
  (* [comment removed for export] *)
  wsd F_104 D_104 SOK NLA. nst.
  (* [comment removed for export] *)
  wst wacc_OpImm F_108 D_108. nst.
  (* [comment removed for export] *)
  wst wacc_OpImm F_10c D_10c. nst.
  (* [comment removed for export] *)
  apply HT.
  - swf_chain Hsvc.
  - reflexivity.
  - rgn. reflexivity.
  - rgn. reflexivity.
  - rgn. reflexivity.
  - rgn. reflexivity.
  - rgn. reflexivity.
  - rgn. reflexivity.
  - rgn. reflexivity.
  - rewrite mem_setx. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rb_c1 : forall model S T (fd f iovp k rem : Z) (b0 l0 b1 l1 : word),
  m_halted model = None ->
  ms_svc_pending S = None -> ms_pc_val S = pcw b 0x120 ->
  rg S 10 = Z_to_bv 64 k -> rg S 19 = Z_to_bv 64 iovp -> rg S 18 = Z_to_bv 64 2 -> rg S 22 = Z_to_bv 64 rem ->
  rg S 9 = Z_to_bv 64 f ->
  (bv_unsigned l0 < k)%Z -> (1 <= k < rem)%Z -> (rem <= 2 ^ 30)%Z -> (rem = bv_unsigned l0 + bv_unsigned l1)%Z ->
  (0 <= iovp)%Z -> (iovp + 32 <= 2 ^ 47)%Z -> (0 <= f)%Z -> (f + 124 <= 2 ^ 47)%Z -> (0 < fd < 2 ^ 31)%Z ->
  no_lazy model iovp (iovp + 32) -> no_lazy model (f + 120) (f + 124) ->
  (f + 124 <= iovp \/ iovp + 32 <= f + 120)%Z ->
  rdn segs (ms_mem S) (Z_to_bv 64 (iovp + 8)) 8 = Some (word_to_le_bytes 8 l0) ->
  rdn segs (ms_mem S) (Z_to_bv 64 (iovp + 16)) 8 = Some (word_to_le_bytes 8 b1) ->
  rdn segs (ms_mem S) (Z_to_bv 64 (iovp + 24)) 8 = Some (word_to_le_bytes 8 l1) ->
  rdn segs (ms_mem S) (Z_to_bv 64 (f + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
  store_ok segs (ms_mem S) (Z_to_bv 64 iovp) 32 = true ->
  (bv_unsigned b1 + bv_unsigned l1 <= 2 ^ 47)%Z ->
  (forall S', SWF S S' iovp (iovp + 32) -> ms_pc_val S' = pcw b 0x110 ->
     rg S' 17 = Z_to_bv 64 66 -> rg S' 10 = Z_to_bv 64 fd -> rg S' 11 = Z_to_bv 64 (iovp + 16) ->
     rg S' 20 = Z_to_bv 64 (iovp + 16) ->
     rg S' 12 = Z_to_bv 64 1 -> rg S' 18 = Z_to_bv 64 1 -> rg S' 22 = Z_to_bv 64 (rem - k) ->
     ms_mem S' = write_to_mem (write_to_mem (ms_mem S) (Z_to_bv 64 (iovp + 16))
                                 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned b1 + (k - bv_unsigned l0)))))
                   (Z_to_bv 64 (iovp + 24)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned l1 - (k - bv_unsigned l0)))) ->
     realizes_cfg segs cfg (mkCfg S' model) T) ->
  realizes_cfg segs cfg (mkCfg S model) T.
Proof.
  intros model S T fd f iovp k rem b0 l0 b1 l1 Hh Hsvc Hpc Ha0 Hs3 Hs2 Hs6 Hs1' Hk Hk2 Hrem Hsum Hi1 Hi2 Hf1 Hf2 Hfdr
         NLA NLF Hdfd R8 R16 R24 Rfd SOK Hb1 HT.
  pose proof (u64_range l0) as Hl0. pose proof (u64_range l1) as Hl1. pose proof (u64_range b1) as Hb1'.
  (* [comment removed for export] *)
  eapply rzc_acc; [ assumption | assumption | eapply wacc_Branch; [ fetch_tac F_120 | reflexivity | exact D_120 ] | apply acc_ok_nil | ].
  rgn. rewrite Ha0, branch_lt0_pos by lia. rewrite Hpc. pcn.
  (* [comment removed for export] *)
  wld F_124 D_124 R8 NLA. nst.
  (* [comment removed for export] *)
  wst wacc_Op F_128 D_128. nst.
  rewrite alu_sltu_w, bvu_z by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
  (* [comment removed for export] *)
  wst wacc_ShiftImm F_12c D_12c. nst. cnorm.
  (* [comment removed for export] *)
  wst wacc_Op F_130 D_130. nst.
  (* [comment removed for export] *)
  wld F_134 D_134 R16 NLA. nst.
  (* [comment removed for export] *)
  wst wacc_Op F_138 D_138. nst. cnorm.
  (* [comment removed for export] *)
  wst wacc_Op F_13c D_13c. nst. rewrite alu_and, andm1_l'.
  (* [comment removed for export] *)
  wst wacc_Op F_140 D_140. nst. rewrite z_sub_w.
  (* [comment removed for export] *)
  wst wacc_Op F_144 D_144. nst. rewrite w_add_z.
  (* [comment removed for export] *)
  wsd F_148 D_148 SOK NLA. nst.
  (* [comment removed for export] *)
  eapply rzc_acc; [ assumption | reflexivity | eapply wacc_Branch; [ fetch_tac F_14c | reflexivity | exact D_14c ] | apply acc_ok_nil | ].
  nst. cbn [branch_taken]. unfold bv_ltu. rewrite bvu_z by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [negb]. pcn.
  (* [comment removed for export] *)
  wst wacc_OpImm F_150 D_150. nst.
  (* [comment removed for export] *)
  wst wacc_Jal F_154 D_154. nst.
  (* [comment removed for export] *)
  wst wacc_OpImm F_e8 D_e8. nst.
  (* [comment removed for export] *)
  wst wacc_Op F_ec D_ec. nst.
  (* [comment removed for export] *)
  wld F_f0 D_f0 R24 NLA. nst.
  (* [comment removed for export] *)
  wst wacc_Op F_f4 D_f4. nst.
  (* [comment removed for export] *)
  wld F_f8 D_f8 Rfd NLF. nst. rewrite load4_pos by lia.
  (* [comment removed for export] *)
  wst wacc_Op32 F_fc D_fc. nst. rewrite subw_z by lia. cnorm.
  (* [comment removed for export] *)
  wst wacc_Op F_100 D_100. nst. rewrite w_sub_z.
  (* [comment removed for export] *)
  wsd F_104 D_104 SOK NLA. nst.
  (* [comment removed for export] *)
  wst wacc_OpImm F_108 D_108. nst.
  (* [comment removed for export] *)
  wst wacc_OpImm F_10c D_10c. nst.
  (* [comment removed for export] *)
  apply HT.
  - swf_chain Hsvc.
  - reflexivity.
  - rgn. reflexivity.
  - rgn. reflexivity.
  - rgn. reflexivity.
  - rgn. reflexivity.
  - rgn. reflexivity.
  - rgn. reflexivity.
  - rgn. reflexivity.
  - rewrite mem_setx. reflexivity.
Qed.

End RB.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
