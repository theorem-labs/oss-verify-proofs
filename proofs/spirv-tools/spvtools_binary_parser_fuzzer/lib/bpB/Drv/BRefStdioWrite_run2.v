(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Bs0Gc.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStepTac BHoare BWalkTac BStoreOk BStreamSim BMmapSim BLibAtomic BExitSim BShapeAlg BNodes.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BRefStdioDefs BRefStdioWrite_run1 B_code_163744_163e60 B_code_16b2d8_16b5b8.
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition sw_regs_but (regs regs' : bvmap 5 word) : Prop :=
  getr regs' 2 = getr regs 2 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
  /\ getr regs' 21 = getr regs 21
  /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
  /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
  /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.

Lemma sw_c1_eq `{fx : DFP} : forall regs mem rom (k : Z),
  getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 k ->
  (0 <= k < 2147483648)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x16ce5c : word) mem rom) (mkst regs' (0x16ce64 : word) mem rom)
    /\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
    /\ sw_regs_but regs regs'.
Proof.
  intros regs mem rom k Ha0 Hs6 K.
  eexists. split.
  - stepn F_16b4b4 D_16b4b4.
    stepn F_163e28 D_163e28.
    stepn F_163e2c D_163e2c.
    stepb_tk F_163e30 D_163e30 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_163e5c D_163e5c (0x16ce60 : word) ltac:(bveq).
    stepb_ft F_16b4b8 D_16b4b8 ltac:(rewrite Ha0, Hs6; apply c_eq_refl).
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_c1_ne `{fx : DFP} : forall regs mem rom (k rem : Z),
  getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 rem ->
  (0 <= k < 2147483648)%Z -> (0 <= rem < 2^64)%Z -> k <> rem ->
  exists regs',
    msteps RSEGS (mkst regs (0x16ce5c : word) mem rom) (mkst regs' (0x16cef0 : word) mem rom)
    /\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
    /\ sw_regs_but regs regs'.
Proof.
  intros regs mem rom k rem Ha0 Hs6 K REM NE.
  eexists. split.
  - stepn F_16b4b4 D_16b4b4.
    stepn F_163e28 D_163e28.
    stepn F_163e2c D_163e2c.
    stepb_tk F_163e30 D_163e30 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_163e5c D_163e5c (0x16ce60 : word) ltac:(bveq).
    stepb_tk F_16b4b8 D_16b4b8 ltac:(rewrite Ha0, Hs6, c_eq_Z by lia; apply Z.eqb_neq; lia).
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_c2_eq `{fx : DFP} : forall regs mem rom (k : Z),
  getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 k ->
  (0 <= k < 2147483648)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x16cee4 : word) mem rom) (mkst regs' (0x16ce64 : word) mem rom)
    /\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 20 /\ getr regs' 20 = getr regs 20
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
    /\ sw_regs_but regs regs'.
Proof.
  intros regs mem rom k Ha0 Hs6 K.
  eexists. split.
  - stepn F_16b53c D_16b53c.
    stepn F_163e28 D_163e28.
    stepn F_163e2c D_163e2c.
    stepb_tk F_163e30 D_163e30 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_163e5c D_163e5c (0x16cee8 : word) ltac:(bveq).
    stepn F_16b540 D_16b540.
    stepb_tk F_16b544 D_16b544 ltac:(rewrite Ha0, Hs6; apply c_eq_refl).
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_c2_ne `{fx : DFP} : forall regs mem rom (k rem : Z),
  getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 rem ->
  (0 <= k < 2147483648)%Z -> (0 <= rem < 2^64)%Z -> k <> rem ->
  exists regs',
    msteps RSEGS (mkst regs (0x16cee4 : word) mem rom) (mkst regs' (0x16cef0 : word) mem rom)
    /\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 20 /\ getr regs' 20 = getr regs 20
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
    /\ sw_regs_but regs regs'.
Proof.
  intros regs mem rom k rem Ha0 Hs6 K REM NE.
  eexists. split.
  - stepn F_16b53c D_16b53c.
    stepn F_163e28 D_163e28.
    stepn F_163e2c D_163e2c.
    stepb_tk F_163e30 D_163e30 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_163e5c D_163e5c (0x16cee8 : word) ltac:(bveq).
    stepn F_16b540 D_16b540.
    stepb_ft F_16b544 D_16b544 ltac:(rewrite Ha0, Hs6, c_eq_Z by lia; apply Z.eqb_neq; lia).
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_retry_a `{fx : DFP} : forall regs mem rom (su f fd io ic cnt n0 rem : Z) (b0 : word),
  getr regs 10 = Z_to_bv 64 cnt -> getr regs 19 = Z_to_bv 64 io -> getr regs 18 = Z_to_bv 64 ic ->
  getr regs 22 = Z_to_bv 64 rem -> getr regs 9 = Z_to_bv 64 f -> getr regs 2 = Z_to_bv 64 (su - 112) ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  (0x189920 <= f)%Z -> (f + 232 <= 0x189be8)%Z ->
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
    msteps RSEGS (mkst regs (0x16cef0 : word) mem rom)
      (mkst regs' (0x16cee0 : word)
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
  -
    stepb_ft F_16b548 D_16b548 ltac:(rewrite Ha0; apply c_lts_pos_0; lia).

    stepLD8 F_16b54c D_16b54c (Z_to_bv 64 n0).

    stepn F_16b550 D_16b550. rewrite Ha0, (sltu_ge n0 cnt) by lia.

    stepn F_16b554 D_16b554.
    stepn F_16b558 D_16b558. rewrite Hs3.

    stepLD8 F_16b55c D_16b55c b0.

    stepn F_16b560 D_16b560.
    stepn F_16b564 D_16b564. rewrite v_and_0_l.
    stepn F_16b568 D_16b568. rewrite Ha0, (v_sub_Z cnt 0) by lia. rewrite Z.sub_0_r.

    stepn F_16b56c D_16b56c. rewrite (v_add_wZ b0 cnt) by lia.

    stepST F_16b570 D_16b570 (Z_to_bv 64 io) (Z_to_bv 64 (bv_unsigned b0 + cnt)) ltac:(sok_frame SOK).

    stepb_tk F_16b574 D_16b574 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; lia).

    stepn F_16b50c D_16b50c.
    stepn F_16b510 D_16b510.
    stepn F_16b514 D_16b514. rewrite Hs3, (v_add_ZZ' io 8) by lia.

    stepLD8 F_16b518 D_16b518 (Z_to_bv 64 n0).

    stepn F_16b51c D_16b51c. rewrite Hs6, Ha0, (v_sub_Z rem cnt) by lia.

    stepLD F_16b520 D_16b520 (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small fd) by lia.

    stepn F_16b524 D_16b524. rewrite Hs2, (v_subw_small_lit ic 0) by lia. rewrite Z.sub_0_r.

    stepn F_16b528 D_16b528. rewrite (v_sub_Z n0 cnt) by lia.
    stepST F_16b52c D_16b52c (Z_to_bv 64 (io + 8)) (Z_to_bv 64 (n0 - cnt)) ltac:(sok_frame SOK).

    stepn F_16b530 D_16b530.
    stepn F_16b534 D_16b534.
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity; try assumption.
Qed.

Lemma sw_retry_b `{fx : DFP} : forall regs mem rom (su f fd io cnt n0 n1 rem : Z) (b1 : word),
  getr regs 10 = Z_to_bv 64 cnt -> getr regs 19 = Z_to_bv 64 io -> getr regs 18 = Z_to_bv 64 2 ->
  getr regs 22 = Z_to_bv 64 rem -> getr regs 9 = Z_to_bv 64 f -> getr regs 2 = Z_to_bv 64 (su - 112) ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  (0x189920 <= f)%Z -> (f + 232 <= 0x189be8)%Z ->
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
    msteps RSEGS (mkst regs (0x16cef0 : word) mem rom)
      (mkst regs' (0x16cee0 : word)
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
  -
    stepb_ft F_16b548 D_16b548 ltac:(rewrite Ha0; apply c_lts_pos_0; lia).

    stepLD8 F_16b54c D_16b54c (Z_to_bv 64 n0).

    stepn F_16b550 D_16b550. rewrite Ha0, (sltu_lt n0 cnt) by lia.

    stepn F_16b554 D_16b554.
    stepn F_16b558 D_16b558. rewrite Hs3, (v_add_ZZ' io 16) by lia.

    stepLD8 F_16b55c D_16b55c b1.

    stepn F_16b560 D_16b560.
    stepn F_16b564 D_16b564. rewrite (v_and_m1_l n0) by lia.
    stepn F_16b568 D_16b568. rewrite Ha0, (v_sub_Z cnt n0) by lia.

    stepn F_16b56c D_16b56c. rewrite (v_add_wZ b1 (cnt - n0)) by lia.

    stepST F_16b570 D_16b570 (Z_to_bv 64 (io + 16)) (Z_to_bv 64 (bv_unsigned b1 + (cnt - n0))) ltac:(sok_frame SOK).

    stepb_ft F_16b574 D_16b574 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_lt; lia).

    stepn F_16b578 D_16b578.
    stepn F_16b57c D_16b57c.
    stepn F_16b510 D_16b510.
    stepn F_16b514 D_16b514. rewrite Hs3, (v_add_ZZ' io 24) by lia.

    stepLD8 F_16b518 D_16b518 (Z_to_bv 64 n1).

    stepn F_16b51c D_16b51c. rewrite Hs6, Ha0, (v_sub_Z rem cnt) by lia.

    stepLD F_16b520 D_16b520 (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small fd) by lia.

    stepn F_16b524 D_16b524. rewrite Hs2. vals_lit.

    stepn F_16b528 D_16b528. rewrite (v_sub_Z n1 (cnt - n0)) by lia.
    stepST F_16b52c D_16b52c (Z_to_bv 64 (io + 24)) (Z_to_bv 64 (n1 - (cnt - n0))) ltac:(sok_frame SOK).

    stepn F_16b530 D_16b530.
    stepn F_16b534 D_16b534.
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity; try assumption.
Qed.

Definition mem_sw2 (mem1 : word -> option byte) (f : Z) (bufp bufsz : word) :=
  wbytes (wbytes (wbytes mem1
    (Z_to_bv 64 (f + 32)) (word_to_le_bytes 8 (v_add bufp bufsz)))
    (Z_to_bv 64 (f + 40)) (word_to_le_bytes 8 bufp))
    (Z_to_bv 64 (f + 56)) (word_to_le_bytes 8 bufp).

Lemma sw_done `{fx : DFP} : forall regs mem rom (su f : Z) (l bufp bufsz can ret s0v s1v s2v s3v s4v s5v s6v : word),
  getr regs 2 = Z_to_bv 64 (su - 112) ->
  getr regs 8 = l -> getr regs 9 = Z_to_bv 64 f ->
  getr regs 21 = Z_to_bv 64 0x6e5898 ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  (0x189920 <= f)%Z -> (f + 232 <= 0x189be8)%Z ->
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
  rdn RSEGS mem (Z_to_bv 64 0x6e5898) 8%nat = Some (word_to_le_bytes 8 can) ->
  rdn RSEGS mem (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp) ->
  rdn RSEGS mem (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz) ->
  exists regs',
    msteps RSEGS (mkst regs (0x16ce64 : word) mem rom)
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
  -
    stepLD F_16b4bc D_16b4bc (word_to_le_bytes 8 bufp) bufp ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_16b4c0 D_16b4c0 (word_to_le_bytes 8 bufsz) bufsz ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepn F_16b4c4 D_16b4c4.

    stepST F_16b4c8 D_16b4c8 (Z_to_bv 64 (f + 32)) (v_add bufp bufsz) ltac:(sok_data).
    stepST F_16b4cc D_16b4cc (Z_to_bv 64 (f + 40)) bufp ltac:(sok_data).
    stepST F_16b4d0 D_16b4d0 (Z_to_bv 64 (f + 56)) bufp ltac:(sok_data).

    stepn F_16b4d4 D_16b4d4. rewrite Hs0.
    stepLD F_16b4d8 D_16b4d8 (word_to_le_bytes 8 can) can ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_16b4dc D_16b4dc (word_to_le_bytes 8 can) can ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepb_ft F_16b4e0 D_16b4e0 ltac:(apply c_eq_refl).

    stepLD F_16b4e4 D_16b4e4 (word_to_le_bytes 8 ret) ret ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_16b4e8 D_16b4e8 (word_to_le_bytes 8 s0v) s0v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_16b4ec D_16b4ec (word_to_le_bytes 8 s1v) s1v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_16b4f0 D_16b4f0 (word_to_le_bytes 8 s2v) s2v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_16b4f4 D_16b4f4 (word_to_le_bytes 8 s3v) s3v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_16b4f8 D_16b4f8 (word_to_le_bytes 8 s4v) s4v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_16b4fc D_16b4fc (word_to_le_bytes 8 s5v) s5v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_16b500 D_16b500 (word_to_le_bytes 8 s6v) s6v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepn F_16b504 D_16b504. rewrite Hsp. sp_renorm.
    replace (su - 0)%Z with su by lia.
    stepret F_16b508 D_16b508 ret ltac:(reflexivity).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
