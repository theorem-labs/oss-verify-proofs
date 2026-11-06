(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.Asan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsStdioWrite_run1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsStdioWrite_run2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.LibAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsStdioWrite_run1.AsStdioDefs OSSVerify.Proofs.glaze.binary_reflection.lib.AsStdioWrite_run1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPGen1.
Context {fx : FPState}.

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
    msteps RSEGS (mkst regs (0xec9f0 : word) mem rom) (mkst regs' (0xec9f8 : word) mem rom)
    /\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
    /\ sw_regs_but regs regs'.
Proof.
  intros regs mem rom k Ha0 Hs6 K.
  eexists. split.
  - stepn F_ec9f4 D_ec9f4.
    stepn F_e7378 D_e7378.
    stepn F_e737c D_e737c.
    stepb_tk F_e7380 D_e7380 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_e73ac D_e73ac (0xec9f4 : word) ltac:(bveq).
    stepb_ft F_ec9f8 D_ec9f8 ltac:(rewrite Ha0, Hs6; apply c_eq_refl).
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_c1_ne : forall regs mem rom (k rem : Z),
  getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 rem ->
  (0 <= k < 2147483648)%Z -> (0 <= rem < 2^64)%Z -> k <> rem ->
  exists regs',
    msteps RSEGS (mkst regs (0xec9f0 : word) mem rom) (mkst regs' (0xeca84 : word) mem rom)
    /\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
    /\ sw_regs_but regs regs'.
Proof.
  intros regs mem rom k rem Ha0 Hs6 K REM NE.
  eexists. split.
  - stepn F_ec9f4 D_ec9f4.
    stepn F_e7378 D_e7378.
    stepn F_e737c D_e737c.
    stepb_tk F_e7380 D_e7380 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_e73ac D_e73ac (0xec9f4 : word) ltac:(bveq).
    stepb_tk F_ec9f8 D_ec9f8 ltac:(rewrite Ha0, Hs6, c_eq_Z by lia; apply Z.eqb_neq; lia).
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_c2_eq : forall regs mem rom (k : Z),
  getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 k ->
  (0 <= k < 2147483648)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0xeca78 : word) mem rom) (mkst regs' (0xec9f8 : word) mem rom)
    /\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 20 /\ getr regs' 20 = getr regs 20
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
    /\ sw_regs_but regs regs'.
Proof.
  intros regs mem rom k Ha0 Hs6 K.
  eexists. split.
  - stepn F_eca7c D_eca7c.
    stepn F_e7378 D_e7378.
    stepn F_e737c D_e737c.
    stepb_tk F_e7380 D_e7380 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_e73ac D_e73ac (0xeca7c : word) ltac:(bveq).
    stepn F_eca80 D_eca80.
    stepb_tk F_eca84 D_eca84 ltac:(rewrite Ha0, Hs6; apply c_eq_refl).
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_c2_ne : forall regs mem rom (k rem : Z),
  getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 rem ->
  (0 <= k < 2147483648)%Z -> (0 <= rem < 2^64)%Z -> k <> rem ->
  exists regs',
    msteps RSEGS (mkst regs (0xeca78 : word) mem rom) (mkst regs' (0xeca84 : word) mem rom)
    /\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 20 /\ getr regs' 20 = getr regs 20
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
    /\ sw_regs_but regs regs'.
Proof.
  intros regs mem rom k rem Ha0 Hs6 K REM NE.
  eexists. split.
  - stepn F_eca7c D_eca7c.
    stepn F_e7378 D_e7378.
    stepn F_e737c D_e737c.
    stepb_tk F_e7380 D_e7380 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_e73ac D_e73ac (0xeca7c : word) ltac:(bveq).
    stepn F_eca80 D_eca80.
    stepb_ft F_eca84 D_eca84 ltac:(rewrite Ha0, Hs6, c_eq_Z by lia; apply Z.eqb_neq; lia).
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
  (0x103920 <= f)%Z -> (f + 232 <= 0x103af8)%Z ->
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
    msteps RSEGS (mkst regs (0xeca84 : word) mem rom)
      (mkst regs' (0xeca74 : word)
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
    stepb_ft F_eca88 D_eca88 ltac:(rewrite Ha0; apply c_lts_pos_0; lia).
    (* [comment removed for export] *)
    stepLD8 F_eca8c D_eca8c (Z_to_bv 64 n0).
    (* [comment removed for export] *)
    stepn F_eca90 D_eca90. rewrite Ha0, (sltu_ge n0 cnt) by lia.
    (* [comment removed for export] *)
    stepn F_eca94 D_eca94.
    stepn F_eca98 D_eca98. rewrite Hs3.
    (* [comment removed for export] *)
    stepLD8 F_eca9c D_eca9c b0.
    (* [comment removed for export] *)
    stepn F_ecaa0 D_ecaa0.
    stepn F_ecaa4 D_ecaa4. rewrite v_and_0_l.
    stepn F_ecaa8 D_ecaa8. rewrite Ha0, (v_sub_Z cnt 0) by lia. rewrite Z.sub_0_r.
    (* [comment removed for export] *)
    stepn F_ecaac D_ecaac. rewrite (v_add_wZ b0 cnt) by lia.
    (* [comment removed for export] *)
    stepST F_ecab0 D_ecab0 (Z_to_bv 64 io) (Z_to_bv 64 (bv_unsigned b0 + cnt)) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepb_tk F_ecab4 D_ecab4 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; lia).
    (* [comment removed for export] *)
    stepn F_eca4c D_eca4c.
    stepn F_eca50 D_eca50.
    stepn F_eca54 D_eca54. rewrite Hs3, (v_add_ZZ' io 8) by lia.
    (* [comment removed for export] *)
    stepLD8 F_eca58 D_eca58 (Z_to_bv 64 n0).
    (* [comment removed for export] *)
    stepn F_eca5c D_eca5c. rewrite Hs6, Ha0, (v_sub_Z rem cnt) by lia.
    (* [comment removed for export] *)
    stepLD F_eca60 D_eca60 (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small fd) by lia.
    (* [comment removed for export] *)
    stepn F_eca64 D_eca64. rewrite Hs2, (v_subw_small_lit ic 0) by lia. rewrite Z.sub_0_r.
    (* [comment removed for export] *)
    stepn F_eca68 D_eca68. rewrite (v_sub_Z n0 cnt) by lia.
    stepST F_eca6c D_eca6c (Z_to_bv 64 (io + 8)) (Z_to_bv 64 (n0 - cnt)) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepn F_eca70 D_eca70.
    stepn F_eca74 D_eca74.
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity; try assumption.
Qed.


(* [comment removed for export] *)
Lemma sw_retry_b : forall regs mem rom (su f fd io cnt n0 n1 rem : Z) (b1 : word),
  getr regs 10 = Z_to_bv 64 cnt -> getr regs 19 = Z_to_bv 64 io -> getr regs 18 = Z_to_bv 64 2 ->
  getr regs 22 = Z_to_bv 64 rem -> getr regs 9 = Z_to_bv 64 f -> getr regs 2 = Z_to_bv 64 (su - 112) ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  (0x103920 <= f)%Z -> (f + 232 <= 0x103af8)%Z ->
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
    msteps RSEGS (mkst regs (0xeca84 : word) mem rom)
      (mkst regs' (0xeca74 : word)
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
    stepb_ft F_eca88 D_eca88 ltac:(rewrite Ha0; apply c_lts_pos_0; lia).
    (* [comment removed for export] *)
    stepLD8 F_eca8c D_eca8c (Z_to_bv 64 n0).
    (* [comment removed for export] *)
    stepn F_eca90 D_eca90. rewrite Ha0, (sltu_lt n0 cnt) by lia.
    (* [comment removed for export] *)
    stepn F_eca94 D_eca94.
    stepn F_eca98 D_eca98. rewrite Hs3, (v_add_ZZ' io 16) by lia.
    (* [comment removed for export] *)
    stepLD8 F_eca9c D_eca9c b1.
    (* [comment removed for export] *)
    stepn F_ecaa0 D_ecaa0.
    stepn F_ecaa4 D_ecaa4. rewrite (v_and_m1_l n0) by lia.
    stepn F_ecaa8 D_ecaa8. rewrite Ha0, (v_sub_Z cnt n0) by lia.
    (* [comment removed for export] *)
    stepn F_ecaac D_ecaac. rewrite (v_add_wZ b1 (cnt - n0)) by lia.
    (* [comment removed for export] *)
    stepST F_ecab0 D_ecab0 (Z_to_bv 64 (io + 16)) (Z_to_bv 64 (bv_unsigned b1 + (cnt - n0))) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepb_ft F_ecab4 D_ecab4 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_lt; lia).
    (* [comment removed for export] *)
    stepn F_ecab8 D_ecab8.
    stepn F_ecabc D_ecabc.
    stepn F_eca50 D_eca50.
    stepn F_eca54 D_eca54. rewrite Hs3, (v_add_ZZ' io 24) by lia.
    (* [comment removed for export] *)
    stepLD8 F_eca58 D_eca58 (Z_to_bv 64 n1).
    (* [comment removed for export] *)
    stepn F_eca5c D_eca5c. rewrite Hs6, Ha0, (v_sub_Z rem cnt) by lia.
    (* [comment removed for export] *)
    stepLD F_eca60 D_eca60 (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small fd) by lia.
    (* [comment removed for export] *)
    stepn F_eca64 D_eca64. rewrite Hs2. vals_lit.
    (* [comment removed for export] *)
    stepn F_eca68 D_eca68. rewrite (v_sub_Z n1 (cnt - n0)) by lia.
    stepST F_eca6c D_eca6c (Z_to_bv 64 (io + 24)) (Z_to_bv 64 (n1 - (cnt - n0))) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepn F_eca70 D_eca70.
    stepn F_eca74 D_eca74.
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
  getr regs 21 = Z_to_bv 64 0x65a780 ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  (0x103920 <= f)%Z -> (f + 232 <= 0x103af8)%Z ->
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
  rdn RSEGS mem (Z_to_bv 64 0x65a780) 8%nat = Some (word_to_le_bytes 8 can) ->
  rdn RSEGS mem (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp) ->
  rdn RSEGS mem (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz) ->
  exists regs',
    msteps RSEGS (mkst regs (0xec9f8 : word) mem rom)
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
    stepLD F_ec9fc D_ec9fc (word_to_le_bytes 8 bufp) bufp ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_eca00 D_eca00 (word_to_le_bytes 8 bufsz) bufsz ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepn F_eca04 D_eca04.
    (* [comment removed for export] *)
    stepST F_eca08 D_eca08 (Z_to_bv 64 (f + 32)) (v_add bufp bufsz) ltac:(sok_data).
    stepST F_eca0c D_eca0c (Z_to_bv 64 (f + 40)) bufp ltac:(sok_data).
    stepST F_eca10 D_eca10 (Z_to_bv 64 (f + 56)) bufp ltac:(sok_data).
    (* [comment removed for export] *)
    stepn F_eca14 D_eca14. rewrite Hs0.
    stepLD F_eca18 D_eca18 (word_to_le_bytes 8 can) can ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_eca1c D_eca1c (word_to_le_bytes 8 can) can ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepb_ft F_eca20 D_eca20 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD F_eca24 D_eca24 (word_to_le_bytes 8 ret) ret ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_eca28 D_eca28 (word_to_le_bytes 8 s0v) s0v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_eca2c D_eca2c (word_to_le_bytes 8 s1v) s1v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_eca30 D_eca30 (word_to_le_bytes 8 s2v) s2v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_eca34 D_eca34 (word_to_le_bytes 8 s3v) s3v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_eca38 D_eca38 (word_to_le_bytes 8 s4v) s4v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_eca3c D_eca3c (word_to_le_bytes 8 s5v) s5v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_eca40 D_eca40 (word_to_le_bytes 8 s6v) s6v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepn F_eca44 D_eca44. rewrite Hsp. sp_renorm.
    replace (su - 0)%Z with su by lia.
    stepret F_eca48 D_eca48 ret ltac:(reflexivity).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
End FPGen1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End AsStdioWrite_run2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsStdioWrite_run1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.LibAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.LibWritev OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsStdioWrite_run1.AsStdioDefs OSSVerify.Proofs.glaze.binary_reflection.lib.AsStdioWrite_run1 AsStdioWrite_run2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.
From Stdlib Require Import FunctionalExtensionality.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section FPGen1.
Context {fx : FPState}.
Variable R : shape_rel RSEGS.

Lemma rz_emit_nil : forall c K, R c K -> R c (t_emit [] K).
Proof.
  intros c K H. eapply (sr_conseq RSEGS R); [exact H|].
  apply t_eq_sym. apply t_emit_nil_eq. exact (sr_nonempty RSEGS R _ _ H).
Qed.

Lemma skipn_app_le : forall {A} (k : nat) (l1 l2 : list A),
  (k <= length l1)%nat -> skipn k (l1 ++ l2) = skipn k l1 ++ l2.
Proof.
  intros A k l1 l2 Hk. rewrite skipn_app. replace (k - length l1)%nat with 0%nat by lia. reflexivity.
Qed.

Lemma skipn_app_ge : forall {A} (k : nat) (l1 l2 : list A),
  (length l1 <= k)%nat -> skipn k (l1 ++ l2) = skipn (k - length l1) l2.
Proof.
  intros A k l1 l2 Hk. rewrite skipn_app. rewrite (proj1 (skipn_all_iff k l1) Hk). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma u_at_le : forall (b : word) (k : Z), (0 <= k)%Z -> (bv_unsigned b + k <= 2 ^ 64)%Z ->
  bv_unsigned (at_ b k) = (bv_unsigned b + k)%Z
  \/ (bv_unsigned (at_ b k) = 0 /\ bv_unsigned b + k = 2 ^ 64)%Z.
Proof.
  intros b k Hk Hle. unfold at_. pose proof (u64_range b).
  destruct (Z.eq_dec (bv_unsigned b + k) (2 ^ 64)) as [E|NE].
  - right. split; [|exact E]. rewrite E. vm_compute. reflexivity.
  - left. u_norm. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma munrestrict_munrestrict : forall (H : word -> bool) (F m m' : word -> option byte),
  munrestrict H (munrestrict H F m) m' = munrestrict H F m'.
Proof.
  intros H F m m'. apply functional_extensionality. intros a. unfold munrestrict. destruct (H a); reflexivity.
Qed.

Lemma mclean_mrestrict_id : forall (H : word -> bool) m, mclean H m -> mrestrict H m = m.
Proof.
  intros H m Hc. apply functional_extensionality. intros a. unfold mrestrict.
  destruct (H a) eqn:E; [symmetry; exact (Hc a E) | reflexivity].
Qed.

Lemma mclean_wbytes : forall (H : word -> bool) m (a : word) bs,
  mclean H m -> hid_off H (bv_unsigned a) (Z.of_nat (length bs)) -> (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  mclean H (wbytes m a bs).
Proof.
  intros H m a bs Hc Hh Hnw x Hx. pose proof (u64_range x).
  assert (D : (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned x)%Z).
  { destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned a)) as [L|Ge]; [left; exact L|].
    destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [L2|Ge2]; [|right; exact Ge2].
    exfalso. pose proof (Hh x ltac:(lia)). congruence. }
  rewrite (MemsetLibF.MemSplit.wbytes_outside bs m a x Hnw D). exact (Hc x Hx).
Qed.

(* [comment removed for export] *)
Definition MOK (A : list (Z * Z)) (model0 model : Model) : Prop :=
  MInv A model /\ same_but_materialized model0 model.

Lemma MOK_next : forall A model0 model mdl',
  MOK A model0 model -> MInv A mdl' -> same_but_materialized model mdl' -> MOK A model0 mdl'.
Proof.
  intros A model0 model mdl' [MI SB] MI' SB'. split; [exact MI'|]. eapply same_but_materialized_trans; eassumption.
Qed.

Section RZR.
  Variables (H : word -> bool) (A : list (Z * Z)) (F : word -> option byte) (model0 : Model).
  Hypothesis HH : H_off_segments RSEGS H.
  Hypothesis Hwx : wx_segs_nowrap RSEGS.
  Hypothesis Awf : A_wf A.
  Hypothesis Hh0 : m_halted model0 = None.
  Hypothesis Hcov0 : lazy_cover H (m_vm_lazy model0) A.

  Lemma MOK_halted : forall model, MOK A model0 model -> m_halted model = None.
  Proof. intros model [_ SB]. pose proof (same_but_materialized_frame _ _ SB) as F'. rewrite <- Hh0. tauto. Qed.
  Lemma MOK_cover : forall model, MOK A model0 model -> lazy_cover H (m_vm_lazy model) A.
  Proof.
    intros model [_ SB]. destruct (same_but_materialized_frame _ _ SB) as (_ & _ & E & _). rewrite E. exact Hcov0.
  Qed.
  Lemma MOK_fds : forall model, MOK A model0 model -> m_fds model = m_fds model0.
  Proof. intros model [_ SB]. pose proof (same_but_materialized_frame _ _ SB) as F'. tauto. Qed.
  Lemma MOK_minv : forall model, MOK A model0 model -> MInv A model.
  Proof. intros model [MI _]. exact MI. Qed.

  (* [comment removed for export] *)
  Let P_of (T : TSet) : config -> Prop := fun c => R c T.
  Let P_of_silent1 (T : TSet) : forall c c',
      AsVocab.AsanAcct.node_ok RSEGS c unit (fun _ => []) (fun _ => c') -> P_of T c' -> P_of T c :=
    fun c c' Hn Hr => sr_silent1 RSEGS R c c' T Hn Hr.
  Lemma sr_msteps_restricted_T : forall Am ms msr' model T,
    lazy_cover H (m_vm_lazy model) Am -> A_wf Am -> MInv Am model -> m_halted model = None ->
    msteps RSEGS (restrict H ms) msr' ->
    (forall model', MInv Am model' -> same_but_materialized model model' -> hclean H msr' ->
        R (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
    R (mkCfg ms model) T.
  Proof.
    intros Am ms msr' model T.
    exact (rz_msteps_restricted' RSEGS H HH Hwx (P_of T) (P_of_silent1 T) Am ms msr' model).
  Qed.

  (* [comment removed for export] *)
  Lemma rzR : forall regs (pc : word) m regs' (pc' : word) m' model T,
    MOK A model0 model -> mclean H m ->
    msteps RSEGS (mkst regs pc m (seg_rom RSEGS)) (mkst regs' pc' m' (seg_rom RSEGS)) ->
    (forall mdl', MOK A model0 mdl' -> mclean H m' ->
        R (mkCfg (mkst regs' pc' (munrestrict H F m') (seg_rom RSEGS)) mdl') T) ->
    R (mkCfg (mkst regs pc (munrestrict H F m) (seg_rom RSEGS)) model) T.
  Proof.
    intros regs pc m regs' pc' m' model T MK MC RUN K.
    apply (sr_msteps_restricted_T A (mkst regs pc (munrestrict H F m) (seg_rom RSEGS))
             (mkst regs' pc' m' (seg_rom RSEGS)) model T (MOK_cover model MK) Awf (MOK_minv model MK) (MOK_halted model MK)).
    - unfold restrict. cbn. rewrite mrestrict_munrestrict, (mclean_mrestrict_id H m MC). exact RUN.
    - intros mdl' MI' SB' HC. unfold unrestrict. cbn. rewrite munrestrict_munrestrict.
      apply (K mdl' (MOK_next A model0 model mdl' MK MI' SB')). intros a Ha. exact (HC a Ha).
  Qed.
End RZR.

Section Loop.
  Variables (su f fd : Z) (l bufp bufsz can ret : word).
  Variables (e8 e9 e18 e19 e20 e21 e22 g3 g4 g23 g24 g25 g26 g27 : word).
  Variable mem1 : word -> option byte.
  Variables (H : word -> bool) (A : list (Z * Z)) (F : word -> option byte) (model0 : Model).
  Variable K : TSet.
  Hypothesis HH : H_off_segments RSEGS H.
  Hypothesis Hwx : wx_segs_nowrap RSEGS.
  Hypothesis Awf : A_wf A.
  Hypothesis HW1 : HYP_writev1_wall_stmt R.
  Hypothesis HW2 : HYP_writev2_wall_stmt R.
  Hypothesis MC1 : mclean H mem1.
  Hypothesis AVfr : hid_off H (su - 112) 112.

  Hypothesis SUlo : (4294967296 + 112 <= su)%Z.
  Hypothesis SUhi : (su <= 0x800000000000)%Z.
  Hypothesis Flo : (0x103920 <= f)%Z.
  Hypothesis Fhi : (f + 232 <= 0x103af8)%Z.
  Hypothesis FD : (0 < fd < 2147483648)%Z.
  Hypothesis Hfd0 : fd_lookup (m_fds model0) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)).
  Hypothesis Hh0 : m_halted model0 = None.
  Hypothesis Hcov0 : lazy_cover H (m_vm_lazy model0) A.
  #[local] Abbreviation MOKm := (MOK A model0).
  Let rzr := rzR H A F model0 HH Hwx Awf Hh0 Hcov0.
  Hypothesis Hret : ret_ok ret.
  Hypothesis HKnil : K [].
  Hypothesis SOK1 : store_ok RSEGS mem1 (Z_to_bv 64 (su - 112)) 112%nat = true.
  Hypothesis M8  : rdn RSEGS mem1 (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret).
  Hypothesis M16 : rdn RSEGS mem1 (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 e8).
  Hypothesis M24 : rdn RSEGS mem1 (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 e9).
  Hypothesis M32 : rdn RSEGS mem1 (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 e18).
  Hypothesis M40 : rdn RSEGS mem1 (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 e19).
  Hypothesis M48 : rdn RSEGS mem1 (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 e20).
  Hypothesis M56 : rdn RSEGS mem1 (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 e21).
  Hypothesis M64 : rdn RSEGS mem1 (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 e22).
  Hypothesis M72 : rdn RSEGS mem1 (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can).
  Hypothesis Mcan : rdn RSEGS mem1 (Z_to_bv 64 0x65a780) 8%nat = Some (word_to_le_bytes 8 can).
  Hypothesis Mbuf : rdn RSEGS mem1 (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp).
  Hypothesis Mbsz : rdn RSEGS mem1 (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz).
  Hypothesis Mfd : rdn RSEGS mem1 (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)).

  (* [comment removed for export] *)
  Definition LM (m : word -> option byte) : Prop :=
    (forall x : word, ~ (su - 104 <= bv_unsigned x < su - 72)%Z -> m x = mem1 x) /\ mem_grows mem1 m.

  (* [comment removed for export] *)
  Hypothesis HK : forall regs' m mdl',
     getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
     getr regs' 8 = e8 -> getr regs' 9 = e9 ->
     getr regs' 18 = e18 -> getr regs' 19 = e19 -> getr regs' 20 = e20 ->
     getr regs' 21 = e21 -> getr regs' 22 = e22 -> getr regs' 23 = g23 ->
     getr regs' 24 = g24 -> getr regs' 25 = g25 -> getr regs' 26 = g26 ->
     getr regs' 27 = g27 -> getr regs' 3 = g3 -> getr regs' 4 = g4 ->
     LM m -> MOKm mdl' ->
     R (mkCfg (mkst regs' ret (munrestrict H F (mem_sw2 m f bufp bufsz)) (seg_rom RSEGS)) mdl') K.

  (* [comment removed for export] *)
  Definition RI (regs : bvmap 5 word) : Prop :=
    getr regs 2 = Z_to_bv 64 (su - 112) /\ getr regs 8 = l /\ getr regs 9 = Z_to_bv 64 f
    /\ getr regs 21 = Z_to_bv 64 0x65a780 /\ getr regs 3 = g3 /\ getr regs 4 = g4
    /\ getr regs 23 = g23 /\ getr regs 24 = g24 /\ getr regs 25 = g25
    /\ getr regs 26 = g26 /\ getr regs 27 = g27.

  Lemma RI_but : forall regs regs', RI regs -> sw_regs_but regs regs' -> RI regs'.
  Proof.
    intros regs regs' (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27)
           (P2 & P8 & P9 & P21 & P3 & P4 & P23 & P24 & P25 & P26 & P27).
    unfold RI. rewrite P2, P8, P9, P21, P3, P4, P23, P24, P25, P26, P27. repeat split; assumption.
  Qed.

  Lemma LM_refl : LM mem1.
  Proof. split; [intros; reflexivity | apply mem_grows_refl]. Qed.

  Lemma LM_rdn : forall m (a : word) n bs,
    LM m -> rdn RSEGS mem1 a n = Some bs ->
    (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
    (bv_unsigned a + Z.of_nat n <= su - 104 \/ su - 72 <= bv_unsigned a)%Z ->
    rdn RSEGS m a n = Some bs.
  Proof.
    intros m a n bs [E G] Hr Hnw D.
    rewrite (rdn_ext RSEGS n m mem1 a Hnw); [exact Hr|].
    intros x Hx. apply E. lia.
  Qed.

  Lemma LM_store_ok : forall m (a : word) n,
    LM m -> store_ok RSEGS mem1 a n = true -> store_ok RSEGS m a n = true.
  Proof. intros m a n [E G] Hs. eapply store_ok_mono; [exact G | exact Hs]. Qed.

  Lemma LM_wbytes8 : forall m (a : Z) (v : word),
    LM m -> (su - 104 <= a)%Z -> (a + 8 <= su - 72)%Z ->
    LM (wbytes m (Z_to_bv 64 a) (word_to_le_bytes 8 v)).
  Proof.
    intros m a v [E G] Hlo Hhi. split.
    - intros x Hx. rewrite wbytes_outside.
      + apply E, Hx.
      + unfold in_rng. rewrite length_N_to_le_bytes. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
      + rewrite length_N_to_le_bytes. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - eapply mem_grows_trans; [exact G | apply wbytes_grows].
  Qed.

  (* [comment removed for export] *)
  Lemma LM_mclean : forall m, LM m -> mclean H m.
  Proof.
    intros m [E G] x Hx. pose proof (u64_range x).
    destruct (Z.lt_ge_cases (bv_unsigned x) (su - 104)) as [L|Ge]; [rewrite (E x) by lia; exact (MC1 x Hx)|].
    destruct (Z.lt_ge_cases (bv_unsigned x) (su - 72)) as [L2|Ge2]; [|rewrite (E x) by lia; exact (MC1 x Hx)].
    exfalso. pose proof (AVfr x ltac:(lia)). congruence.
  Qed.
  Lemma LK_minv : forall model, MOKm model -> MInv A model.
  Proof. intros model [MI _]. exact MI. Qed.
  Lemma LK_halted : forall model, MOKm model -> m_halted model = None.
  Proof. intros model MK. exact (MOK_halted A model0 Hh0 model MK). Qed.
  Lemma LK_cover : forall model, MOKm model -> lazy_cover H (m_vm_lazy model) A.
  Proof. intros model MK. exact (MOK_cover H A model0 Hcov0 model MK). Qed.
  Lemma LK_fd : forall model, MOKm model -> fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)).
  Proof. intros model MK. rewrite (MOK_fds A model0 model MK). exact Hfd0. Qed.
  (* [comment removed for export] *)
  Lemma ra_frame : forall (a : Z) (n : nat), (su - 112 <= a)%Z -> (a + Z.of_nat n <= su)%Z ->
    range_avoids H (Z_to_bv 64 a) n.
  Proof.
    intros a n H1 H2. apply hid_off_range_avoids; [u_norm; lia|]. u_norm. eapply hid_off_sub; [exact AVfr | lia | lia].
  Qed.
  Lemma ra_buf : forall (b : word) (len k : nat), hid_off H (bv_unsigned b) (Z.of_nat len) ->
    (bv_unsigned b + Z.of_nat len <= 2 ^ 64)%Z -> (k <= len)%nat ->
    range_avoids H (Z_to_bv 64 (bv_unsigned b + Z.of_nat k)) (len - k)%nat.
  Proof.
    intros b len k Hb Hnw Hk. pose proof (u64_range b).
    destruct (Z.eq_dec (bv_unsigned b + Z.of_nat k) (2 ^ 64)) as [E|NE].
    - replace (len - k)%nat with 0%nat by lia. intros j Hj. lia.
    - apply hid_off_range_avoids; [u_norm; lia|]. u_norm. eapply hid_off_sub; [exact Hb | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma finish : forall regs m model,
    RI regs -> LM m -> MOKm model ->
    R (mkCfg (mkst regs (0xec9f8 : word) (munrestrict H F m) (seg_rom RSEGS)) model) K.
  Proof.
    intros regs m model RIr LMm MK.
    destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
    destruct (sw_done regs m (seg_rom RSEGS) su f l bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22)
      as (regs2 & RUN & Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q3 & Q4 & Q23 & Q24 & Q25 & Q26 & Q27);
      try assumption.
    all: try (eapply LM_rdn; [exact LMm | eassumption | u_norm; lia | u_norm; lia]).
    eapply rzr; [exact MK | apply LM_mclean; exact LMm | exact RUN |]; clear RUN; intros mdl1 MK1 MC2.
    apply HK; try assumption.
    - rewrite Q23; exact R23.
    - rewrite Q24; exact R24.
    - rewrite Q25; exact R25.
    - rewrite Q26; exact R26.
    - rewrite Q27; exact R27.
    - rewrite Q3; exact R3.
    - rewrite Q4; exact R4.
  Qed.

  Lemma finish_nil : forall regs m model,
    RI regs -> LM m -> MOKm model ->
    R (mkCfg (mkst regs (0xec9f8 : word) (munrestrict H F m) (seg_rom RSEGS)) model) (t_emit [] K).
  Proof. intros. apply rz_emit_nil. apply finish; assumption. Qed.


  (* [comment removed for export] *)
  Lemma pc_645ac : v_addi (0xeca74 : word) 4 = (0xeca78 : word).
  Proof. apply bv_eq; vm_compute; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma loop1 : forall n regs m (k : nat) (b : word) (bs : list byte) model,
    (length bs <= n)%nat ->
    RI regs -> LM m -> MOKm model -> hid_off H (bv_unsigned b) (Z.of_nat (length bs)) ->
    getr regs 10 = Z_to_bv 64 (Z.of_nat k) ->
    getr regs 22 = Z_to_bv 64 (Z.of_nat (length bs)) ->
    getr regs 18 = Z_to_bv 64 1 -> getr regs 19 = Z_to_bv 64 (su - 88) ->
    (1 <= k < length bs)%nat ->
    rdn RSEGS m (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 b) ->
    rdn RSEGS m (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.of_nat (length bs)))) ->
    rdn RSEGS mem1 b (length bs) = Some bs ->
    (bv_unsigned b + Z.of_nat (length bs) <= su - 112 \/ su <= bv_unsigned b)%Z ->
    (bv_unsigned b + Z.of_nat (length bs) <= 0x800000000000)%Z ->
    (0 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= 2 ^ 30)%Z ->
    R (mkCfg (mkst regs (0xeca84 : word) (munrestrict H F m) (seg_rom RSEGS)) model)
             (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs)) K).
  Proof.
    induction n as [|n IH]; intros regs m k b bs model LEN RIr LMm MK AVb Ha0 Hs6 Hs2 Hs3 Kb Mb Mn Bbs DISJ NW MAX M30.
    { exfalso. lia. }
    pose proof RIr as RIr'.
    destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
    pose proof (u64_range b) as Hb.
    (* [comment removed for export] *)
    destruct (sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 88) 1 (Z.of_nat k)
                (Z.of_nat (length bs)) (Z.of_nat (length bs)) b)
      as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
    { eapply LM_store_ok; [exact LMm | exact SOK1]. }
    { replace (su - 88 + 8)%Z with (su - 80)%Z by lia. exact Mn. }
    { eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
    eapply rzr; [exact MK | apply LM_mclean; exact LMm | exact RUN |]; clear RUN; intros mdlA MKA MCA.
    replace (su - 88 + 8)%Z with (su - 80)%Z in * by lia.
    set (m' := wbytes (wbytes m _ _) _ _) in *.
    assert (LMm' : LM m').
    { subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
    assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
    (* [comment removed for export] *)
    eapply (HW1 H A F regs1 (0xeca74 : word) m' mdlA W_eca78 fd
              (Z_to_bv 64 (su - 88)) (Z_to_bv 64 (bv_unsigned b + Z.of_nat k))
              (Z_to_bv 64 (Z.of_nat (length bs) - Z.of_nat k)) (skipn k bs) K
              HH Hwx Awf (LK_minv _ MKA) (LK_cover _ MKA) MCA F_eca78 E_eca78 (LK_halted _ MKA) (LK_fd _ MKA) FD
              Q17 Q10 Q11 Q12);
      [ | | | apply ra_frame; lia | | | | | | exact HKnil | ].
    - subst m'. rdn_solve.
    - subst m'. u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rdn_solve.
    - rewrite word_to_nat_Z by lia.
      replace (Z.to_nat (Z.of_nat (length bs) - Z.of_nat k)) with (length bs - k)%nat by lia.
      subst m'. repeat rdn_peel1.
      change (Z_to_bv 64 (bv_unsigned b + Z.of_nat k)) with (at_ b (Z.of_nat k)).
      apply (rdn_skipn RSEGS m (length bs) b bs k); [|lia].
      eapply LM_rdn; [exact LMm | exact Bbs | lia | lia].
    - rewrite word_to_nat_Z by lia.
      replace (Z.to_nat (Z.of_nat (length bs) - Z.of_nat k)) with (length bs - k)%nat by lia.
      apply ra_buf; [exact AVb | lia | lia].
    - u_norm. unfold TASK_SIZE in *. lia.
    - u_norm. unfold TASK_SIZE in *. lia.
    - u_norm. unfold TASK_SIZE in *. lia.
    - u_norm. unfold TASK_SIZE in *. lia.
    - (* [comment removed for export] *)
      intros k' mdlB K1 K2 MIB SBB. pose proof (MOK_next A model0 mdlA mdlB MKA MIB SBB) as MKB.
      rewrite pc_645ac. rewrite length_skipn in K2.
      destruct (Nat.eq_dec k' (length bs - k)) as [EQ|NE].
      + (* [comment removed for export] *)
        destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. rewrite Q22. f_equal. lia. }
        { lia. }
        eapply rzr; [exact MKB | exact MCA | exact RUN2 |]; clear RUN2; intros mdlC MKC MCC.
        rewrite (proj1 (skipn_all_iff k' (skipn k bs))) by (rewrite length_skipn; lia).
        apply finish_nil; [| exact LMm' | exact MKC].
        eapply RI_but; [exact RI1|].
        revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
      + (* [comment removed for export] *)
        destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                    (Z.of_nat (length bs) - Z.of_nat k))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. exact Q22. }
        { lia. }
        { lia. }
        { lia. }
        eapply rzr; [exact MKB | exact MCA | exact RUN2 |]; clear RUN2; intros mdlC MKC MCC.
        apply (IH regs2 m' k' (at_ b (Z.of_nat k)) (skipn k bs) mdlC).
        * rewrite length_skipn. lia.
        * eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        * exact LMm'.
        * exact MKC.
        * rewrite length_skipn. pose proof (u_at_le b (Z.of_nat k) ltac:(lia) ltac:(lia)) as [E|[E E2]];
            rewrite E; first [eapply hid_off_sub; [exact AVb | lia | lia] | apply hid_off_nil; lia].
        * exact P10.
        * rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
        * rewrite P18. gres. exact Q18.
        * rewrite P19. gres. exact Q20.
        * rewrite length_skipn. lia.
        * subst m'. unfold at_. rdn_solve.
        * subst m'. rewrite length_skipn.
          replace (Z.of_nat (length bs - k)) with (Z.of_nat (length bs) - Z.of_nat k)%Z by lia. rdn_solve.
        * rewrite length_skipn. apply (rdn_skipn RSEGS mem1 (length bs) b bs k); [exact Bbs|lia].
        * unfold at_. rewrite length_skipn. u_norm. lia.
        * unfold at_. rewrite length_skipn. u_norm. lia.
        * rewrite length_skipn. lia.
        * rewrite length_skipn. lia.
  Qed.


  (* [comment removed for export] *)
  Lemma loop2 : forall n regs m (k : nat) (b0 : word) (bs0 : list byte) (b1 : word) (bs1 : list byte) model,
    (length bs0 + length bs1 <= n)%nat ->
    RI regs -> LM m -> MOKm model ->
    hid_off H (bv_unsigned b0) (Z.of_nat (length bs0)) -> hid_off H (bv_unsigned b1) (Z.of_nat (length bs1)) ->
    getr regs 10 = Z_to_bv 64 (Z.of_nat k) ->
    getr regs 22 = Z_to_bv 64 (Z.of_nat (length bs0) + Z.of_nat (length bs1)) ->
    getr regs 18 = Z_to_bv 64 2 -> getr regs 19 = Z_to_bv 64 (su - 104) ->
    (1 <= k < length bs0 + length bs1)%nat ->
    rdn RSEGS m (Z_to_bv 64 (su - 104)) 8%nat = Some (word_to_le_bytes 8 b0) ->
    rdn RSEGS m (Z_to_bv 64 (su - 96)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.of_nat (length bs0)))) ->
    rdn RSEGS m (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 b1) ->
    rdn RSEGS m (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.of_nat (length bs1)))) ->
    rdn RSEGS mem1 b0 (length bs0) = Some bs0 ->
    rdn RSEGS mem1 b1 (length bs1) = Some bs1 ->
    (bv_unsigned b0 + Z.of_nat (length bs0) <= su - 112 \/ su <= bv_unsigned b0)%Z ->
    (bv_unsigned b0 + Z.of_nat (length bs0) <= 0x800000000000)%Z ->
    (bv_unsigned b1 + Z.of_nat (length bs1) <= su - 112 \/ su <= bv_unsigned b1)%Z ->
    (bv_unsigned b1 + Z.of_nat (length bs1) <= 0x800000000000)%Z ->
    (0 <= Z.of_nat (length bs0) + Z.of_nat (length bs1))%Z ->
    (Z.of_nat (length bs0) + Z.of_nat (length bs1) <= 2 ^ 30)%Z ->
    R (mkCfg (mkst regs (0xeca84 : word) (munrestrict H F m) (seg_rom RSEGS)) model)
             (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs0 ++ bs1))) K).
  Proof.
    induction n as [|n IH]; intros regs m k b0 bs0 b1 bs1 model LEN RIr LMm MK AVb0 AVb1 Ha0 Hs6 Hs2 Hs3 Kb
      Mb0 Mn0 Mb1 Mn1 Bbs0 Bbs1 DISJ0 NW0 DISJ1 NW1 MAX M30.
    { exfalso. lia. }
    pose proof RIr as RIr'.
    destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
    pose proof (u64_range b0) as Hb0. pose proof (u64_range b1) as Hb1.
    destruct (Nat.le_gt_cases k (length bs0)) as [LE|GT].
    - (* [comment removed for export] *)
      destruct (sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 104) 2 (Z.of_nat k)
                  (Z.of_nat (length bs0)) (Z.of_nat (length bs0) + Z.of_nat (length bs1)) b0)
        as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
      { eapply LM_store_ok; [exact LMm | exact SOK1]. }
      { replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact Mn0. }
      { eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
      eapply rzr; [exact MK | apply LM_mclean; exact LMm | exact RUN |]; clear RUN; intros mdlA MKA MCA.
      replace (su - 104 + 8)%Z with (su - 96)%Z in * by lia.
      set (m' := wbytes (wbytes m _ _) _ _) in *.
      assert (LMm' : LM m').
      { subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
      assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
      rewrite (skipn_app_le k bs0 bs1 LE).
      eapply (HW2 H A F regs1 (0xeca74 : word) m' mdlA W_eca78 fd
                (Z_to_bv 64 (su - 104)) (Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k))
                (Z_to_bv 64 (Z.of_nat (length bs0) - Z.of_nat k))
                b1 (Z_to_bv 64 (Z.of_nat (length bs1))) (skipn k bs0) bs1 K
                HH Hwx Awf (LK_minv _ MKA) (LK_cover _ MKA) MCA F_eca78 E_eca78 (LK_halted _ MKA) (LK_fd _ MKA) FD
                Q17 Q10 Q11 Q12);
        [ | | | | | | apply ra_frame; lia | | | | | | | | exact HKnil | ].
      + subst m'. rdn_solve.
      + subst m'. u_norm. replace (su - 104 + 8)%Z with (su - 96)%Z by lia. rdn_solve.
      + subst m'. u_norm. replace (su - 104 + 16)%Z with (su - 88)%Z by lia. repeat rdn_peel1. exact Mb1.
      + subst m'. u_norm. replace (su - 104 + 24)%Z with (su - 80)%Z by lia. repeat rdn_peel1. exact Mn1.
      + rewrite word_to_nat_Z by lia.
        replace (Z.to_nat (Z.of_nat (length bs0) - Z.of_nat k)) with (length bs0 - k)%nat by lia.
        destruct (Nat.eq_dec k (length bs0)) as [EK|NK].
        { replace (length bs0 - k)%nat with 0%nat by lia.
          rewrite (proj1 (skipn_all_iff k bs0)) by lia. reflexivity. }
        subst m'. repeat rdn_peel1.
        change (Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k)) with (at_ b0 (Z.of_nat k)).
        apply (rdn_skipn RSEGS m (length bs0) b0 bs0 k); [|lia].
        eapply LM_rdn; [exact LMm | exact Bbs0 | lia | lia].
      + rewrite word_to_nat_Z by lia. rewrite Nat2Z.id.
        subst m'. repeat rdn_peel1.
        eapply LM_rdn; [exact LMm | exact Bbs1 | lia | lia].
      + rewrite word_to_nat_Z by lia.
        replace (Z.to_nat (Z.of_nat (length bs0) - Z.of_nat k)) with (length bs0 - k)%nat by lia.
        apply ra_buf; [exact AVb0 | lia | lia].
      + rewrite word_to_nat_Z by lia. rewrite Nat2Z.id.
        pose proof (ra_buf b1 (length bs1) 0 AVb1 ltac:(lia) ltac:(lia)) as RA1.
        rewrite Z.add_0_r, (Z_to_bv_bv_unsigned 64 b1), Nat.sub_0_r in RA1. exact RA1.
      + u_norm. unfold TASK_SIZE in *. lia.
      + u_norm. unfold TASK_SIZE in *. lia.
      + u_norm. unfold TASK_SIZE in *. lia.
      + u_norm. unfold TASK_SIZE in *. lia.
      + u_norm. unfold TASK_SIZE in *. lia.
      + intros k' mdlB K1 K2 MIB SBB. pose proof (MOK_next A model0 mdlA mdlB MKA MIB SBB) as MKB.
        rewrite pc_645ac. rewrite length_app, length_skipn in K2.
        destruct (Nat.eq_dec k' (length bs0 - k + length bs1)) as [EQ|NE].
        * destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. rewrite Q22. f_equal. lia. }
          { lia. }
          eapply rzr; [exact MKB | exact MCA | exact RUN2 |]; clear RUN2; intros mdlC MKC MCC.
          rewrite (proj1 (skipn_all_iff k' (skipn k bs0 ++ bs1))) by (rewrite length_app, length_skipn; lia).
          apply finish_nil; [| exact LMm' | exact MKC].
          eapply RI_but; [exact RI1|].
          revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        * destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                      (Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. exact Q22. }
          { lia. }
          { lia. }
          { lia. }
          eapply rzr; [exact MKB | exact MCA | exact RUN2 |]; clear RUN2; intros mdlC MKC MCC.
          apply (IH regs2 m' k' (at_ b0 (Z.of_nat k)) (skipn k bs0) b1 bs1 mdlC).
          -- rewrite length_skipn. lia.
          -- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
          -- exact LMm'.
          -- exact MKC.
          -- rewrite length_skipn. pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)) as [E|[E E2]];
               rewrite E; first [eapply hid_off_sub; [exact AVb0 | lia | lia] | apply hid_off_nil; lia].
          -- exact AVb1.
          -- exact P10.
          -- rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
          -- rewrite P18. gres. exact Q18.
          -- rewrite P19. gres. exact Q20.
          -- rewrite length_skipn. lia.
          -- subst m'. unfold at_. rdn_solve.
          -- subst m'. rewrite length_skipn.
             replace (Z.of_nat (length bs0 - k)) with (Z.of_nat (length bs0) - Z.of_nat k)%Z by lia. rdn_solve.
          -- subst m'. repeat rdn_peel1. exact Mb1.
          -- subst m'. repeat rdn_peel1. exact Mn1.
          -- rewrite length_skipn. apply (rdn_skipn RSEGS mem1 (length bs0) b0 bs0 k); [exact Bbs0|lia].
          -- exact Bbs1.
          -- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
          -- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
          -- exact DISJ1.
          -- exact NW1.
          -- rewrite length_skipn. lia.
          -- rewrite length_skipn. lia.
    - (* [comment removed for export] *)
      destruct (sw_retry_b regs m (seg_rom RSEGS) su f fd (su - 104) (Z.of_nat k)
                  (Z.of_nat (length bs0)) (Z.of_nat (length bs1))
                  (Z.of_nat (length bs0) + Z.of_nat (length bs1)) b1)
        as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
      { eapply LM_store_ok; [exact LMm | exact SOK1]. }
      { replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact Mn0. }
      { replace (su - 104 + 16)%Z with (su - 88)%Z by lia. exact Mb1. }
      { replace (su - 104 + 24)%Z with (su - 80)%Z by lia. exact Mn1. }
      { eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
      eapply rzr; [exact MK | apply LM_mclean; exact LMm | exact RUN |]; clear RUN; intros mdlA MKA MCA.
      replace (su - 104 + 16)%Z with (su - 88)%Z in * by lia.
      replace (su - 104 + 24)%Z with (su - 80)%Z in * by lia.
      replace (Z.of_nat k - Z.of_nat (length bs0))%Z with (Z.of_nat (k - length bs0)) in * by lia.
      set (m' := wbytes (wbytes m _ _) _ _) in *.
      assert (LMm' : LM m').
      { subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
      assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
      rewrite (skipn_app_ge k bs0 bs1) by lia.
      eapply (HW1 H A F regs1 (0xeca74 : word) m' mdlA W_eca78 fd
                (Z_to_bv 64 (su - 88)) (Z_to_bv 64 (bv_unsigned b1 + Z.of_nat (k - length bs0)))
                (Z_to_bv 64 (Z.of_nat (length bs1) - Z.of_nat (k - length bs0)))
                (skipn (k - length bs0) bs1) K
                HH Hwx Awf (LK_minv _ MKA) (LK_cover _ MKA) MCA F_eca78 E_eca78 (LK_halted _ MKA) (LK_fd _ MKA) FD
                Q17 Q10 Q11 Q12);
        [ | | | apply ra_frame; lia | | | | | | exact HKnil | ].
      + subst m'. rdn_solve.
      + subst m'. u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rdn_solve.
      + rewrite word_to_nat_Z by lia.
        replace (Z.to_nat (Z.of_nat (length bs1) - Z.of_nat (k - length bs0))) with (length bs1 - (k - length bs0))%nat by lia.
        subst m'. repeat rdn_peel1.
        change (Z_to_bv 64 (bv_unsigned b1 + Z.of_nat (k - length bs0))) with (at_ b1 (Z.of_nat (k - length bs0))).
        apply (rdn_skipn RSEGS m (length bs1) b1 bs1 (k - length bs0)); [|lia].
        eapply LM_rdn; [exact LMm | exact Bbs1 | lia | lia].
      + rewrite word_to_nat_Z by lia.
        replace (Z.to_nat (Z.of_nat (length bs1) - Z.of_nat (k - length bs0))) with (length bs1 - (k - length bs0))%nat by lia.
        apply ra_buf; [exact AVb1 | lia | lia].
      + u_norm. unfold TASK_SIZE in *. lia.
      + u_norm. unfold TASK_SIZE in *. lia.
      + u_norm. unfold TASK_SIZE in *. lia.
      + u_norm. unfold TASK_SIZE in *. lia.
      + intros k' mdlB K1 K2 MIB SBB. pose proof (MOK_next A model0 mdlA mdlB MKA MIB SBB) as MKB.
        rewrite pc_645ac. rewrite length_skipn in K2.
        destruct (Nat.eq_dec k' (length bs1 - (k - length bs0))) as [EQ|NE].
        * destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. rewrite Q22. f_equal. lia. }
          { lia. }
          eapply rzr; [exact MKB | exact MCA | exact RUN2 |]; clear RUN2; intros mdlC MKC MCC.
          rewrite (proj1 (skipn_all_iff k' (skipn (k - length bs0) bs1))) by (rewrite length_skipn; lia).
          apply finish_nil; [| exact LMm' | exact MKC].
          eapply RI_but; [exact RI1|].
          revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        * destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                      (Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. exact Q22. }
          { lia. }
          { lia. }
          { lia. }
          eapply rzr; [exact MKB | exact MCA | exact RUN2 |]; clear RUN2; intros mdlC MKC MCC.
          apply (loop1 (length bs1) regs2 m' k' (at_ b1 (Z.of_nat (k - length bs0))) (skipn (k - length bs0) bs1) mdlC).
          -- rewrite length_skipn. lia.
          -- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
          -- exact LMm'.
          -- exact MKC.
          -- rewrite length_skipn. pose proof (u_at_le b1 (Z.of_nat (k - length bs0)) ltac:(lia) ltac:(lia)) as [E|[E E2]];
               rewrite E; first [eapply hid_off_sub; [exact AVb1 | lia | lia] | apply hid_off_nil; lia].
          -- exact P10.
          -- rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
          -- rewrite P18. gres. exact Q18.
          -- rewrite P19. gres. exact Q20.
          -- rewrite length_skipn. lia.
          -- subst m'. unfold at_. rdn_solve.
          -- subst m'. rewrite length_skipn.
             replace (Z.of_nat (length bs1 - (k - length bs0))) with (Z.of_nat (length bs1) - Z.of_nat (k - length bs0))%Z by lia.
             rdn_solve.
          -- rewrite length_skipn.
             apply (rdn_skipn RSEGS mem1 (length bs1) b1 bs1 (k - length bs0)); [exact Bbs1|lia].
          -- unfold at_. rewrite length_skipn. u_norm. lia.
          -- unfold at_. rewrite length_skipn. u_norm. lia.
          -- rewrite length_skipn. lia.
          -- rewrite length_skipn. lia.
  Qed.

End Loop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End FPGen1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
