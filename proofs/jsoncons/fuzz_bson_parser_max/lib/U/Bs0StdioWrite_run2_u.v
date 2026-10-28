(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic
  ExitSim ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0StdioDefs_u Bs0StdioWrite_run1_u Bs0_code_r4b000_4c000_u Bs0_code_r4e000_4f000_u   .
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sw_regs_but (regs regs' : bvmap 5 word) : Prop :=
  getr regs' 2 = getr regs 2 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
  /\ getr regs' 21 = getr regs 21
  /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
  /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
  /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.

Lemma sw_c1_eq : forall regs mem rom (k : Z),
  getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 k ->
  (0 <= k < 2147483648)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x9ffe4 : word) mem rom) (mkst regs' (0x9ffec : word) mem rom)
    /\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
    /\ sw_regs_but regs regs'.
Proof.
  intros regs mem rom k Ha0 Hs6 K.
  eexists. split.
  - stepn F_9e9b0 D_9e9b0.
    stepn F_9997c D_9997c.
    stepn F_99980 D_99980.
    stepb_tk F_99984 D_99984 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_999b0 D_999b0 (0x9ffe8 : word) ltac:(bveq).
    stepb_ft F_9e9b4 D_9e9b4 ltac:(rewrite Ha0, Hs6; apply c_eq_refl).
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_c1_ne : forall regs mem rom (k rem : Z),
  getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 rem ->
  (0 <= k < 2147483648)%Z -> (0 <= rem < 2^64)%Z -> k <> rem ->
  exists regs',
    msteps RSEGS (mkst regs (0x9ffe4 : word) mem rom) (mkst regs' (0xa0078 : word) mem rom)
    /\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
    /\ sw_regs_but regs regs'.
Proof.
  intros regs mem rom k rem Ha0 Hs6 K REM NE.
  eexists. split.
  - stepn F_9e9b0 D_9e9b0.
    stepn F_9997c D_9997c.
    stepn F_99980 D_99980.
    stepb_tk F_99984 D_99984 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_999b0 D_999b0 (0x9ffe8 : word) ltac:(bveq).
    stepb_tk F_9e9b4 D_9e9b4 ltac:(rewrite Ha0, Hs6, c_eq_Z by lia; apply Z.eqb_neq; lia).
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_c2_eq : forall regs mem rom (k : Z),
  getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 k ->
  (0 <= k < 2147483648)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0xa006c : word) mem rom) (mkst regs' (0x9ffec : word) mem rom)
    /\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 20 /\ getr regs' 20 = getr regs 20
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
    /\ sw_regs_but regs regs'.
Proof.
  intros regs mem rom k Ha0 Hs6 K.
  eexists. split.
  - stepn F_9ea38 D_9ea38.
    stepn F_9997c D_9997c.
    stepn F_99980 D_99980.
    stepb_tk F_99984 D_99984 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_999b0 D_999b0 (0xa0070 : word) ltac:(bveq).
    stepn F_9ea3c D_9ea3c.
    stepb_tk F_9ea40 D_9ea40 ltac:(rewrite Ha0, Hs6; apply c_eq_refl).
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_c2_ne : forall regs mem rom (k rem : Z),
  getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 rem ->
  (0 <= k < 2147483648)%Z -> (0 <= rem < 2^64)%Z -> k <> rem ->
  exists regs',
    msteps RSEGS (mkst regs (0xa006c : word) mem rom) (mkst regs' (0xa0078 : word) mem rom)
    /\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 20 /\ getr regs' 20 = getr regs 20
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
    /\ sw_regs_but regs regs'.
Proof.
  intros regs mem rom k rem Ha0 Hs6 K REM NE.
  eexists. split.
  - stepn F_9ea38 D_9ea38.
    stepn F_9997c D_9997c.
    stepn F_99980 D_99980.
    stepb_tk F_99984 D_99984 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_999b0 D_999b0 (0xa0070 : word) ltac:(bveq).
    stepn F_9ea3c D_9ea3c.
    stepb_ft F_9ea40 D_9ea40 ltac:(rewrite Ha0, Hs6, c_eq_Z by lia; apply Z.eqb_neq; lia).
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sw_retry_a : forall regs mem rom (su f fd io ic cnt n0 rem : Z) (b0 : word),
  getr regs 10 = Z_to_bv 64 cnt -> getr regs 19 = Z_to_bv 64 io -> getr regs 18 = Z_to_bv 64 ic ->
  getr regs 22 = Z_to_bv 64 rem -> getr regs 9 = Z_to_bv 64 f -> getr regs 2 = Z_to_bv 64 (su - 112) ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  (0xb8000 <= f)%Z -> (f + 232 <= 0xea230)%Z ->
  (su - 104 <= io)%Z -> (io + 16 <= su - 72)%Z ->
  (1 <= ic <= 2)%Z ->
  (1 <= cnt <= n0)%Z -> (n0 < 2^62)%Z -> (cnt <= rem)%Z -> (rem < 2^62)%Z ->
  (bv_unsigned b0 + n0 <= 2^64)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 io) 8%nat = Some (word_to_le_bytes 8 b0) ->
  rdn RSEGS mem (Z_to_bv 64 (io + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 n0)) ->
  rdn RSEGS mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
  (0 < fd < 2147483648)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0xa0078 : word) mem rom)
      (mkst regs' (0xa0068 : word)
        (wbytes (wbytes mem (Z_to_bv 64 io) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned b0 + cnt))))
                (Z_to_bv 64 (io + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (n0 - cnt)))) rom)
    /\ getr regs' 17 = Z_to_bv 64 66 /\ getr regs' 10 = Z_to_bv 64 fd
    /\ getr regs' 11 = Z_to_bv 64 io /\ getr regs' 12 = Z_to_bv 64 ic
    /\ getr regs' 18 = Z_to_bv 64 ic /\ getr regs' 19 = Z_to_bv 64 io /\ getr regs' 20 = Z_to_bv 64 io
    /\ getr regs' 22 = Z_to_bv 64 (rem - cnt)
    /\ sw_regs_but regs regs'.
Proof.
  intros regs mem rom su f fd io ic cnt n0 rem b0
         Ha0 Hs3 Hs2 Hs6 Hs1 Hsp SUlo SUhi Flo Fhi IOlo IOhi IC CNT N0 CR REM B0 SOK Mb0 Mn0 Mfd FD.
  pose proof (u64_range b0) as Hb0.
  eexists. split.
  - (* [comment removed for export] *)
    stepb_ft F_9ea44 D_9ea44 ltac:(rewrite Ha0; apply c_lts_pos_0; lia).
    (* [comment removed for export] *)
    stepLD8 F_9ea48 D_9ea48 (Z_to_bv 64 n0).
    (* [comment removed for export] *)
    stepn F_9ea4c D_9ea4c. rewrite Ha0, (sltu_ge n0 cnt) by lia.
    (* [comment removed for export] *)
    stepn F_9ea50 D_9ea50.
    stepn F_9ea54 D_9ea54. rewrite Hs3.
    (* [comment removed for export] *)
    stepLD8 F_9ea58 D_9ea58 b0.
    (* [comment removed for export] *)
    stepn F_9ea5c D_9ea5c.
    stepn F_9ea60 D_9ea60. rewrite v_and_0_l.
    stepn F_9ea64 D_9ea64. rewrite Ha0, (v_sub_Z cnt 0) by lia. rewrite Z.sub_0_r.
    (* [comment removed for export] *)
    stepn F_9ea68 D_9ea68. rewrite (v_add_wZ b0 cnt) by lia.
    (* [comment removed for export] *)
    stepST F_9ea6c D_9ea6c (Z_to_bv 64 io) (Z_to_bv 64 (bv_unsigned b0 + cnt)) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepb_tk F_9ea70 D_9ea70 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; lia).
    (* [comment removed for export] *)
    stepn F_9ea08 D_9ea08.
    stepn F_9ea0c D_9ea0c.
    stepn F_9ea10 D_9ea10. rewrite Hs3, (v_add_ZZ' io 8) by lia.
    (* [comment removed for export] *)
    stepLD8 F_9ea14 D_9ea14 (Z_to_bv 64 n0).
    (* [comment removed for export] *)
    stepn F_9ea18 D_9ea18. rewrite Hs6, Ha0, (v_sub_Z rem cnt) by lia.
    (* [comment removed for export] *)
    stepLD F_9ea1c D_9ea1c (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small fd) by lia.
    (* [comment removed for export] *)
    stepn F_9ea20 D_9ea20. rewrite Hs2, (v_subw_small_lit ic 0) by lia. rewrite Z.sub_0_r.
    (* [comment removed for export] *)
    stepn F_9ea24 D_9ea24. rewrite (v_sub_Z n0 cnt) by lia.
    stepST F_9ea28 D_9ea28 (Z_to_bv 64 (io + 8)) (Z_to_bv 64 (n0 - cnt)) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepn F_9ea2c D_9ea2c.
    stepn F_9ea30 D_9ea30.
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity; try assumption.
Qed.


(* [comment removed for export] *)
Lemma sw_retry_b : forall regs mem rom (su f fd io cnt n0 n1 rem : Z) (b1 : word),
  getr regs 10 = Z_to_bv 64 cnt -> getr regs 19 = Z_to_bv 64 io -> getr regs 18 = Z_to_bv 64 2 ->
  getr regs 22 = Z_to_bv 64 rem -> getr regs 9 = Z_to_bv 64 f -> getr regs 2 = Z_to_bv 64 (su - 112) ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  (0xb8000 <= f)%Z -> (f + 232 <= 0xea230)%Z ->
  (su - 104 <= io)%Z -> (io + 32 <= su - 72)%Z ->
  (0 <= n0 < cnt)%Z -> (cnt <= rem)%Z -> (rem < 2^62)%Z -> (cnt - n0 <= n1)%Z -> (n1 < 2^62)%Z ->
  (bv_unsigned b1 + n1 <= 2^64)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 (io + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 n0)) ->
  rdn RSEGS mem (Z_to_bv 64 (io + 16)) 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn RSEGS mem (Z_to_bv 64 (io + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 n1)) ->
  rdn RSEGS mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
  (0 < fd < 2147483648)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0xa0078 : word) mem rom)
      (mkst regs' (0xa0068 : word)
        (wbytes (wbytes mem (Z_to_bv 64 (io + 16)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned b1 + (cnt - n0)))))
                (Z_to_bv 64 (io + 24)) (word_to_le_bytes 8 (Z_to_bv 64 (n1 - (cnt - n0))))) rom)
    /\ getr regs' 17 = Z_to_bv 64 66 /\ getr regs' 10 = Z_to_bv 64 fd
    /\ getr regs' 11 = Z_to_bv 64 (io + 16) /\ getr regs' 12 = Z_to_bv 64 1
    /\ getr regs' 18 = Z_to_bv 64 1 /\ getr regs' 19 = Z_to_bv 64 io /\ getr regs' 20 = Z_to_bv 64 (io + 16)
    /\ getr regs' 22 = Z_to_bv 64 (rem - cnt)
    /\ sw_regs_but regs regs'.
Proof.
  intros regs mem rom su f fd io cnt n0 n1 rem b1
         Ha0 Hs3 Hs2 Hs6 Hs1 Hsp SUlo SUhi Flo Fhi IOlo IOhi N0 CR REM N1 N1hi B1 SOK Mn0 Mb1 Mn1 Mfd FD.
  pose proof (u64_range b1) as Hb1.
  eexists. split.
  - (* [comment removed for export] *)
    stepb_ft F_9ea44 D_9ea44 ltac:(rewrite Ha0; apply c_lts_pos_0; lia).
    (* [comment removed for export] *)
    stepLD8 F_9ea48 D_9ea48 (Z_to_bv 64 n0).
    (* [comment removed for export] *)
    stepn F_9ea4c D_9ea4c. rewrite Ha0, (sltu_lt n0 cnt) by lia.
    (* [comment removed for export] *)
    stepn F_9ea50 D_9ea50.
    stepn F_9ea54 D_9ea54. rewrite Hs3, (v_add_ZZ' io 16) by lia.
    (* [comment removed for export] *)
    stepLD8 F_9ea58 D_9ea58 b1.
    (* [comment removed for export] *)
    stepn F_9ea5c D_9ea5c.
    stepn F_9ea60 D_9ea60. rewrite (v_and_m1_l n0) by lia.
    stepn F_9ea64 D_9ea64. rewrite Ha0, (v_sub_Z cnt n0) by lia.
    (* [comment removed for export] *)
    stepn F_9ea68 D_9ea68. rewrite (v_add_wZ b1 (cnt - n0)) by lia.
    (* [comment removed for export] *)
    stepST F_9ea6c D_9ea6c (Z_to_bv 64 (io + 16)) (Z_to_bv 64 (bv_unsigned b1 + (cnt - n0))) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepb_ft F_9ea70 D_9ea70 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_lt; lia).
    (* [comment removed for export] *)
    stepn F_9ea74 D_9ea74.
    stepn F_9ea78 D_9ea78.
    stepn F_9ea0c D_9ea0c.
    stepn F_9ea10 D_9ea10. rewrite Hs3, (v_add_ZZ' io 24) by lia.
    (* [comment removed for export] *)
    stepLD8 F_9ea14 D_9ea14 (Z_to_bv 64 n1).
    (* [comment removed for export] *)
    stepn F_9ea18 D_9ea18. rewrite Hs6, Ha0, (v_sub_Z rem cnt) by lia.
    (* [comment removed for export] *)
    stepLD F_9ea1c D_9ea1c (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small fd) by lia.
    (* [comment removed for export] *)
    stepn F_9ea20 D_9ea20. rewrite Hs2. vals_lit.
    (* [comment removed for export] *)
    stepn F_9ea24 D_9ea24. rewrite (v_sub_Z n1 (cnt - n0)) by lia.
    stepST F_9ea28 D_9ea28 (Z_to_bv 64 (io + 24)) (Z_to_bv 64 (n1 - (cnt - n0))) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepn F_9ea2c D_9ea2c.
    stepn F_9ea30 D_9ea30.
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity; try assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mem_sw2 (mem1 : word -> option byte) (f : Z) (bufp bufsz : word) :=
  wbytes (wbytes (wbytes mem1
    (Z_to_bv 64 (f + 32)) (word_to_le_bytes 8 (v_add bufp bufsz)))
    (Z_to_bv 64 (f + 40)) (word_to_le_bytes 8 bufp))
    (Z_to_bv 64 (f + 56)) (word_to_le_bytes 8 bufp).

Lemma sw_done : forall regs mem rom (su f : Z) (l bufp bufsz can ret s0v s1v s2v s3v s4v s5v s6v : word),
  getr regs 2 = Z_to_bv 64 (su - 112) ->
  getr regs 8 = l -> getr regs 9 = Z_to_bv 64 f ->
  getr regs 21 = Z_to_bv 64 0xea230 ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  (0xb8000 <= f)%Z -> (f + 232 <= 0xea230)%Z ->
  ret_ok ret ->
  rdn RSEGS mem (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 s0v) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 s1v) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 s2v) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 s3v) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 s4v) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 s5v) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 s6v) ->
  rdn RSEGS mem (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can) ->
  rdn RSEGS mem (Z_to_bv 64 0xea230) 8%nat = Some (word_to_le_bytes 8 can) ->
  rdn RSEGS mem (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp) ->
  rdn RSEGS mem (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz) ->
  exists regs',
    msteps RSEGS (mkst regs (0x9ffec : word) mem rom)
                 (mkst regs' ret (mem_sw2 mem f bufp bufsz) rom)
    /\ getr regs' 10 = l /\ getr regs' 2 = Z_to_bv 64 su /\ getr regs' 1 = ret
    /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
    /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
    /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
    /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Proof.
  intros regs mem rom su f l bufp bufsz can ret s0v s1v s2v s3v s4v s5v s6v
         Hsp Hs0 Hs1 Hs5 SUlo SUhi Flo Fhi Hret
         M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz.
  unfold mem_sw2. eexists. split.
  - (* [comment removed for export] *)
    stepLD F_9e9b8 D_9e9b8 (word_to_le_bytes 8 bufp) bufp ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_9e9bc D_9e9bc (word_to_le_bytes 8 bufsz) bufsz ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepn F_9e9c0 D_9e9c0.
    (* [comment removed for export] *)
    stepST F_9e9c4 D_9e9c4 (Z_to_bv 64 (f + 32)) (v_add bufp bufsz) ltac:(sok_data).
    stepST F_9e9c8 D_9e9c8 (Z_to_bv 64 (f + 40)) bufp ltac:(sok_data).
    stepST F_9e9cc D_9e9cc (Z_to_bv 64 (f + 56)) bufp ltac:(sok_data).
    (* [comment removed for export] *)
    stepn F_9e9d0 D_9e9d0. rewrite Hs0.
    stepLD F_9e9d4 D_9e9d4 (word_to_le_bytes 8 can) can ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_9e9d8 D_9e9d8 (word_to_le_bytes 8 can) can ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepb_ft F_9e9dc D_9e9dc ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD F_9e9e0 D_9e9e0 (word_to_le_bytes 8 ret) ret ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_9e9e4 D_9e9e4 (word_to_le_bytes 8 s0v) s0v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_9e9e8 D_9e9e8 (word_to_le_bytes 8 s1v) s1v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_9e9ec D_9e9ec (word_to_le_bytes 8 s2v) s2v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_9e9f0 D_9e9f0 (word_to_le_bytes 8 s3v) s3v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_9e9f4 D_9e9f4 (word_to_le_bytes 8 s4v) s4v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_9e9f8 D_9e9f8 (word_to_le_bytes 8 s5v) s5v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_9e9fc D_9e9fc (word_to_le_bytes 8 s6v) s6v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepn F_9ea00 D_9ea00. rewrite Hsp. sp_renorm.
    replace (su - 0)%Z with su by lia.
    stepret F_9ea04 D_9ea04 ret ltac:(reflexivity).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End FPX_1.


(* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
