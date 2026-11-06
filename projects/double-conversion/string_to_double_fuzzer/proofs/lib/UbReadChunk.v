(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ModelAmb.
From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk LibMaskBits SumWalkTac RefMemcpyLib UbMemcpyBase UbMemcpy.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require PropExec CatExec CatSim SeqExec StepTac StoreOk ShapeAlg Hoare WalkTac Frame MemSplit LibMaskBits SumWalkTac RefMemcpyLib SpecConsts SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefNodes LibKnowFrame RefReadLib UbReadBase UbReadStage.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec Ub_code_32468_33000 Ub_code_96000_97000 Ub_code_9b000_9c000 Ub_code_a6000_a7000 Ub_code_a7000_a8000 Ub_code_ab000_abc28           .
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast LiaTier.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast2.

(* [comment removed for export] *)
Module RefReadChunkW.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.PropExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SeqExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StepTac OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Hoare OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.WalkTac OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StoreOk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibMaskBits OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SumWalkTac OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbReadBase.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

#[local] Abbreviation RSEGS := ImgU.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPW_1. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Definition want (cap len : Z) : Z := if (cap - len <? 65536)%Z then (cap - len)%Z else 65536%Z.

#[using="Type"] Lemma want_range : forall cap len, (0 <= len < cap)%Z -> (1 <= want cap len <= 65536)%Z /\ (want cap len <= cap - len)%Z.
Proof. intros cap len H. unfold want. destruct (Z.ltb_spec (cap - len) 65536); lia. Qed.

(* [comment removed for export] *)
Definition loop_kept : list reg := [3; 4; 8; 18; 20; 21; 22; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
#[using="Type"] Lemma walkA : forall regs mem rom (sp0 buf len cap : Z),
  getr regs 2 = Z_to_bv 64 (sp0 - 128) -> getr regs 19 = Z_to_bv 64 len -> getr regs 21 = Z_to_bv 64 cap ->
  getr regs 9 = Z_to_bv 64 buf -> getr regs 20 = Z_to_bv 64 3 -> getr regs 22 = Z_to_bv 64 STAGE ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  (0 <= len < cap)%Z -> (cap <= 2 ^ 40)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = true ->
  exists regs',
    msteps RSEGS (mkst regs (0x32700 : word) mem rom)
                 (mkst regs' (0xa7d30 : word)
                       (wbytes mem (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x3271c))) rom)
    /\ getr regs' 17 = Z_to_bv 64 63 /\ getr regs' 10 = Z_to_bv 64 3
    /\ getr regs' 11 = Z_to_bv 64 STAGE /\ getr regs' 12 = Z_to_bv 64 (want cap len)
    /\ getr regs' 1 = Z_to_bv 64 0xabcb4 /\ getr regs' 2 = Z_to_bv 64 (sp0 - 144)
    /\ getr regs' 9 = Z_to_bv 64 buf /\ getr regs' 19 = Z_to_bv 64 len
    /\ (forall r, In r (23 :: loop_kept)%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 buf len cap Hsp Hs3 Hs5 Hs1 Hs4 Hs6 SPlo SPhi Hlen Hcap SOK.
  Ltac walkA_tail Hs4 Hs6 Hsp SOK sp0 :=
      stepn F_32710 D_32710; rewrite Hs4;
      stepn F_32714 D_32714; rewrite Hs6;
      stepn F_32718 D_32718;
      (* [comment removed for export] *)
      stepn F_abc8c D_abc8c; rewrite Hsp; sp_renorm;
      stepST F_abc90 D_abc90 (Z_to_bv 64 (sp0 - 136)) (Z_to_bv 64 0x3271c) ltac:(exact SOK);
      stepn F_abc94 D_abc94; stepn F_abc98 D_abc98; stepn F_abc9c D_abc9c; stepn F_abca0 D_abca0;
      stepn F_abca4 D_abca4; stepn F_abca8 D_abca8; stepn F_abcac D_abcac; stepn F_abcb0 D_abcb0;
      stepn F_a7d38 D_a7d38;
      stepn F_a7d14 D_a7d14; stepn F_a7d18 D_a7d18; stepn F_a7d1c D_a7d1c; stepn F_a7d20 D_a7d20;
      stepn F_a7d24 D_a7d24; stepn F_a7d28 D_a7d28; stepn F_a7d2c D_a7d2c;
      apply mst_refl.
  Ltac walkA_post :=
      repeat split; gres; try reflexivity; try assumption;
      intros r Hr; cbv [loop_kept In] in Hr;
      repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr.
  unfold want. destruct (Z.ltb_spec (cap - len) 65536) as [LT|GE]; eexists; split.
  - (* [comment removed for export] *)
    stepn F_32700 D_32700. rewrite Hs5, Hs3. rewrite (v_sub_ZZ cap len) by lia.
    (* [comment removed for export] *)
    stepn F_32704 D_32704.
    (* [comment removed for export] *)
    stepb_tk F_32708 D_32708 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
    walkA_tail Hs4 Hs6 Hsp SOK sp0.
  - walkA_post.
  - stepn F_32700 D_32700. rewrite Hs5, Hs3. rewrite (v_sub_ZZ cap len) by lia.
    stepn F_32704 D_32704.
    (* [comment removed for export] *)
    stepb_ft F_32708 D_32708 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
    stepn F_3270c D_3270c.
    walkA_tail Hs4 Hs6 Hsp SOK sp0.
  - walkA_post.
Qed.

(* [comment removed for export] *)
Definition loopB_kept : list reg := [3; 4; 8; 9; 18; 20; 21; 22; 24; 25; 26; 27]%bv.
End FPW_1.

Ltac kept_list l :=
  intros r Hr; cbv [l In] in Hr;
  repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr.

Section FPW_3. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
#[using="Type"] Lemma walkB : forall regs mem rom (sp0 buf len n : Z),
  getr regs 1 = Z_to_bv 64 0xabcb4 -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 n ->
  getr regs 19 = Z_to_bv 64 len -> getr regs 9 = Z_to_bv 64 buf -> getr regs 22 = Z_to_bv 64 STAGE ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  (0 < n <= 65536)%Z -> (0 <= len)%Z -> (0 <= buf)%Z -> (buf + len + n <= 2 ^ 62)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x3271c)) ->
  exists regs',
    msteps RSEGS (mkst regs (0xa7d34 : word) mem rom) (mkst regs' (0xa6e20 : word) mem rom)
    /\ getr regs' 1 = Z_to_bv 64 0x326b4 /\ getr regs' 2 = Z_to_bv 64 (sp0 - 128)
    /\ getr regs' 10 = Z_to_bv 64 (buf + len) /\ getr regs' 11 = Z_to_bv 64 STAGE /\ getr regs' 12 = Z_to_bv 64 n
    /\ getr regs' 23 = Z_to_bv 64 n /\ getr regs' 19 = Z_to_bv 64 len /\ getr regs' 9 = Z_to_bv 64 buf
    /\ (forall r, In r loopB_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 buf len n Hra Hsp Ha0 Hs3 Hs1 Hs6 SPlo SPhi Hn Hlen Hbuf Hbl RD.
  eexists. split.
  - (* [comment removed for export] *)
    stepret F_a7d34 D_a7d34 (0xabcb4 : word) ltac:(rewrite Hra; bveq).
    (* [comment removed for export] *)
    stepLD8 F_abcb4 D_abcb4 (Z_to_bv 64 0x3271c).
    (* [comment removed for export] *)
    stepn F_abcb8 D_abcb8. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_abcbc D_abcbc.
    (* [comment removed for export] *)
    stepn F_9694c D_9694c. stepn F_96950 D_96950.
    (* [comment removed for export] *)
    stepb_tk F_96954 D_96954 ltac:(rewrite Ha0; rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
    (* [comment removed for export] *)
    stepret F_96980 D_96980 (0x3271c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepb_ft F_3271c D_3271c ltac:(rewrite Ha0; apply c_lts_pos_0; u_norm; lia).
    (* [comment removed for export] *)
    stepn F_32720 D_32720. rewrite Ha0.
    (* [comment removed for export] *)
    stepb_tk F_32724 D_32724 ltac:(rewrite Ha0; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepn F_326a4 D_326a4. rewrite Hs1, Hs3. rewrite (v_add_ZZ buf len) by lia.
    stepn F_326a8 D_326a8. rewrite Hs6.
    stepn F_326ac D_326ac.
    stepn F_326b0 D_326b0.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia). all: kept_list loopB_kept.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma walkB2_full : forall regs mem rom (buf len n cap : Z),
  getr regs 23 = Z_to_bv 64 n -> getr regs 19 = Z_to_bv 64 len -> getr regs 9 = Z_to_bv 64 buf ->
  getr regs 21 = Z_to_bv 64 cap ->
  (0 <= len)%Z -> (0 <= n)%Z -> (len + n = cap)%Z -> (cap <= 2 ^ 40)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x326b4 : word) mem rom) (mkst regs' (0x326c8 : word) mem rom)
    /\ getr regs' 19 = Z_to_bv 64 cap /\ getr regs' 23 = Z_to_bv 64 buf /\ getr regs' 9 = Z_to_bv 64 buf
    /\ (forall r, In r (1 :: 2 :: 10 :: loopB_kept)%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom buf len n cap Hs7 Hs3 Hs1 Hs5 Hlen Hn Hfull Hcap.
  eexists. split.
  - (* [comment removed for export] *)
    stepn F_326b4 D_326b4. rewrite Hs7, Hs3. rewrite (v_add_ZZ n len) by lia.
    (* [comment removed for export] *)
    stepn F_326b8 D_326b8. rewrite Hs1.
    (* [comment removed for export] *)
    stepb_tk F_326bc D_326bc ltac:(rewrite Hs5; rewrite c_eq_Z by lia; apply Z.eqb_eq; lia).
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia). all: kept_list loopB_kept.
Qed.

#[using="Type"] Lemma walkB2_more : forall regs mem rom (buf len n cap : Z),
  getr regs 23 = Z_to_bv 64 n -> getr regs 19 = Z_to_bv 64 len -> getr regs 9 = Z_to_bv 64 buf ->
  getr regs 21 = Z_to_bv 64 cap ->
  (0 <= len)%Z -> (0 <= n)%Z -> (len + n < cap)%Z -> (cap <= 2 ^ 40)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x326b4 : word) mem rom) (mkst regs' (0x32700 : word) mem rom)
    /\ getr regs' 19 = Z_to_bv 64 (len + n) /\ getr regs' 23 = Z_to_bv 64 buf /\ getr regs' 9 = Z_to_bv 64 buf
    /\ (forall r, In r (1 :: 2 :: 10 :: loop_kept)%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom buf len n cap Hs7 Hs3 Hs1 Hs5 Hlen Hn Hmore Hcap.
  eexists. split.
  - stepn F_326b4 D_326b4. rewrite Hs7, Hs3. rewrite (v_add_ZZ n len) by lia.
    stepn F_326b8 D_326b8. rewrite Hs1.
    (* [comment removed for export] *)
    stepb_ft F_326bc D_326bc ltac:(rewrite Hs5; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepn F_326c0 D_326c0.
    stepn F_326c4 D_326c4.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia). all: kept_list loop_kept.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma walkBC : forall regs mem rom (sp0 buf len : Z),
  getr regs 1 = Z_to_bv 64 0xabcb4 -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 0 ->
  getr regs 19 = Z_to_bv 64 len -> getr regs 9 = Z_to_bv 64 buf -> getr regs 20 = Z_to_bv 64 3 ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z -> (0 <= len < 2 ^ 63)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x3271c)) ->
  store_ok RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = true ->
  exists regs',
    msteps RSEGS (mkst regs (0xa7d34 : word) mem rom)
                 (mkst regs' (0xa7d30 : word)
                       (wbytes mem (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x32730))) rom)
    /\ getr regs' 17 = Z_to_bv 64 57 /\ getr regs' 10 = Z_to_bv 64 3
    /\ getr regs' 1 = Z_to_bv 64 0xabc58 /\ getr regs' 2 = Z_to_bv 64 (sp0 - 144)
    /\ getr regs' 19 = Z_to_bv 64 len /\ getr regs' 23 = Z_to_bv 64 0
    /\ (forall r, In r loopB_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 buf len Hra Hsp Ha0 Hs3 Hs1 Hs4 SPlo SPhi Hlen RD SOK.
  eexists. split.
  - stepret F_a7d34 D_a7d34 (0xabcb4 : word) ltac:(rewrite Hra; bveq).
    stepLD8 F_abcb4 D_abcb4 (Z_to_bv 64 0x3271c).
    stepn F_abcb8 D_abcb8. rewrite Hsp. sp_renorm.
    stepn F_abcbc D_abcbc.
    stepn F_9694c D_9694c. stepn F_96950 D_96950.
    stepb_tk F_96954 D_96954 ltac:(rewrite Ha0; cond_compute).
    stepret F_96980 D_96980 (0x3271c : word) ltac:(bveq).
    stepb_ft F_3271c D_3271c ltac:(rewrite Ha0; cond_compute).
    (* [comment removed for export] *)
    stepn F_32720 D_32720. rewrite Ha0.
    (* [comment removed for export] *)
    stepb_ft F_32724 D_32724 ltac:(rewrite Ha0; cond_compute).
    (* [comment removed for export] *)
    stepn F_32728 D_32728. rewrite Hs4.
    stepn F_3272c D_3272c.
    (* [comment removed for export] *)
    stepn F_abc2c D_abc2c. sp_renorm.
    stepST F_abc30 D_abc30 (Z_to_bv 64 (sp0 - 136)) (Z_to_bv 64 0x32730) ltac:(exact SOK).
    stepn F_abc34 D_abc34.
    stepret F_9c0fc D_9c0fc (0xabc38 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_abc38 D_abc38. stepn F_abc3c D_abc3c. stepn F_abc40 D_abc40. stepn F_abc44 D_abc44.
    stepn F_abc48 D_abc48. stepn F_abc4c D_abc4c. stepn F_abc50 D_abc50. stepn F_abc54 D_abc54.
    stepn F_a7d38 D_a7d38.
    stepn F_a7d14 D_a7d14. stepn F_a7d18 D_a7d18. stepn F_a7d1c D_a7d1c. stepn F_a7d20 D_a7d20.
    stepn F_a7d24 D_a7d24. stepn F_a7d28 D_a7d28. stepn F_a7d2c D_a7d2c.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption. all: kept_list loopB_kept.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma walkD : forall regs mem rom (sp0 : Z),
  getr regs 1 = Z_to_bv 64 0xabc58 -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 0 ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x32730)) ->
  exists regs',
    msteps RSEGS (mkst regs (0xa7d34 : word) mem rom) (mkst regs' (0x32730 : word) mem rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp0 - 128)
    /\ (forall r, In r (9 :: 19 :: 23 :: loopB_kept)%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 Hra Hsp Ha0 SPlo SPhi RD.
  eexists. split.
  - stepret F_a7d34 D_a7d34 (0xabc58 : word) ltac:(rewrite Hra; bveq).
    (* [comment removed for export] *)
    stepn F_abc58 D_abc58. rewrite Ha0. rewrite v_addiw_id by (u_norm; lia).
    stepn F_abc5c D_abc5c. stepn F_abc60 D_abc60. stepn F_abc64 D_abc64. stepn F_abc68 D_abc68.
    (* [comment removed for export] *)
    stepn F_abc6c D_abc6c.
    stepn F_9694c D_9694c. stepn F_96950 D_96950.
    stepb_tk F_96954 D_96954 ltac:(cond_compute).
    stepret F_96980 D_96980 (0xabc70 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_abc70 D_abc70.
    stepLD8 F_abc74 D_abc74 (Z_to_bv 64 0x32730).
    stepn F_abc78 D_abc78. rewrite Hsp. sp_renorm.
    stepret F_abc7c D_abc7c (0x32730 : word) ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia). all: kept_list loopB_kept.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma walkA0 : forall regs mem rom (buf cap : Z),
  getr regs 10 = Z_to_bv 64 buf -> getr regs 21 = Z_to_bv 64 cap ->
  (0x1000 <= buf < 2 ^ 63)%Z -> (0 < cap <= 2 ^ 40)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x32688 : word) mem rom) (mkst regs' (0x32700 : word) mem rom)
    /\ getr regs' 9 = Z_to_bv 64 buf /\ getr regs' 23 = Z_to_bv 64 buf /\ getr regs' 19 = Z_to_bv 64 0
    /\ getr regs' 22 = Z_to_bv 64 STAGE
    /\ (forall r, In r [1; 2; 3; 4; 8; 18; 20; 21; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom buf cap Ha0 Hs5 Hbuf Hcap. eexists. split.
  - (* [comment removed for export] *)
    stepb_ft F_32688 D_32688 ltac:(rewrite Ha0; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    stepn F_3268c D_3268c. rewrite Ha0.          (* [comment removed for export] *)
    stepn F_32690 D_32690.                       (* [comment removed for export] *)
    stepn F_32694 D_32694.                       (* [comment removed for export] *)
    stepn F_32698 D_32698.                       (* [comment removed for export] *)
    stepb_tk F_3269c D_3269c ltac:(rewrite Hs5; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).  (* [comment removed for export] *)
    stepn F_326c0 D_326c0.                       (* [comment removed for export] *)
    stepn F_326c4 D_326c4.                       (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption.
    intros r Hr; cbv [In] in Hr; repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr.
Qed.

End FPW_3.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefReadChunkW.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.PropExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SeqExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StepTac OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StoreOk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ShapeAlg OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Hoare OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.WalkTac OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Frame OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MemSplit OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibMaskBits OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SumWalkTac OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbMemcpyBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbMemcpy OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SpecConsts OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2Sound OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymRun OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDrive OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDriveX OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefNodes OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibKnowFrame OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadLib OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbReadBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbReadStage RefReadChunkW.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac noncert_qtauto :=
  first [ solve [ repeat match goal with H : _ |- _ => clear H end; intuition fail ] | tauto ].
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

#[local] Abbreviation RSEGS := ImgU.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPW_4. Context {fx : PropExec.FPState}.


#[using="Type"] Lemma dropz_dropz : forall (a b : Z) l, (0 <= a)%Z -> (0 <= b)%Z ->
  dropz a (dropz b l) = dropz (b + a) l.
Proof.
  intros a b l Ha Hb. unfold dropz. rewrite skipn_skipn. f_equal. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pref_chain : forall (len n m : Z) l, (0 <= len)%Z -> (0 <= n)%Z -> (0 <= m)%Z ->
  pref n (dropz len l) ++ pref m (dropz (len + n) l) = pref (n + m) (dropz len l).
Proof.
  intros len n m l Hl Hn Hm. rewrite <- (dropz_dropz n len) by lia. apply pref_app; lia.
Qed.

#[using="Type"] Lemma pref_0 : forall l, pref 0 l = [].
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma read_chunk : forall content (len want : Z),
  (0 <= len <= Z.of_nat (length content))%Z -> (len < 2 ^ 62)%Z -> (0 <= want < 2 ^ 62)%Z ->
  let bs := file_read content (Z_to_bv 64 len) (Z_to_bv 64 want) in
  let n := Z.of_nat (length bs) in
  n = Z.min want (Z.of_nat (length content) - len) /\ bs = pref n (dropz len content).
Proof.
  intros content len want Hlen Hlen2 Hwant. cbn zeta.
  rewrite file_read_pref by lia.
  pose proof (pref_length want (dropz len content) ltac:(lia)) as PL.
  pose proof (dropz_length len content ltac:(lia)) as DL.
  split; [lia|].
  destruct (Z.le_gt_cases want (Z.of_nat (length content) - len)) as [Hle|Hgt].
  - f_equal. lia.
  - rewrite (pref_all want) by lia. symmetry. apply pref_all. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mid_regs (R : bvmap 5 word) (sp0 buf len cap : Z) : Prop :=
  getr R 2 = Z_to_bv 64 (sp0 - 128) /\ getr R 9 = Z_to_bv 64 buf /\ getr R 19 = Z_to_bv 64 len
  /\ getr R 20 = Z_to_bv 64 3 /\ getr R 21 = Z_to_bv 64 cap /\ getr R 22 = Z_to_bv 64 STAGE.

(* [comment removed for export] *)
Definition loop_post_regs (R R' : bvmap 5 word) (sp0 buf len' s7v : Z) : Prop :=
  getr R' 2 = Z_to_bv 64 (sp0 - 128) /\ getr R' 9 = Z_to_bv 64 buf /\ getr R' 23 = Z_to_bv 64 s7v
  /\ getr R' 19 = Z_to_bv 64 len'
  /\ (forall r, In r loop_kept -> getr R' r = getr R r).

(* [comment removed for export] *)
Definition loop_regions (sp0 buf len len' : Z) : list (word * Z) :=
  [(Z_to_bv 64 (sp0 - 136), 8%Z); (Z_to_bv 64 STAGE, 65536%Z); (Z_to_bv 64 (buf + len), (len' - len)%Z)].
Definition loop_post_mem (content : list byte) (M M' : word -> option byte) (sp0 buf len len' : Z) : Prop :=
  frame_mod M M' (loop_regions sp0 buf len len')
  /\ rdn RSEGS M' (Z_to_bv 64 (buf + len)) (Z.to_nat (len' - len)) = Some (pref (len' - len) (dropz len content)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma loop_kept_B : forall r, In r loop_kept -> In r loopB_kept.
Proof.
  intros r Hr. cbv [loop_kept In] in Hr. cbv [loopB_kept In].
  repeat (destruct Hr as [<-|Hr]; [noncert_qtauto|]). destruct Hr.
Qed.

#[using="Type"] Lemma kept_regupd10 : forall X (v : word) r, In r loop_kept -> getr (regupd X 10 v) r = getr X r.
Proof.
  intros X v r Hr. cbv [loop_kept In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [rewrite getr_other by reg_neq_tac; reflexivity|]). destruct Hr.
Qed.

#[using="Type"] Lemma loop_kept_callee : forall r, In r loop_kept -> In r callee_kept.
Proof.
  intros r Hr. cbv [loop_kept In] in Hr. cbv [callee_kept In].
  repeat (destruct Hr as [<-|Hr]; [noncert_qtauto|]). destruct Hr.
Qed.

#[using="Type"] Lemma post_regs_compose : forall R R2 R' sp0 buf len' s7v,
  loop_post_regs R2 R' sp0 buf len' s7v ->
  (forall r, In r loop_kept -> getr R2 r = getr R r) ->
  loop_post_regs R R' sp0 buf len' s7v.
Proof.
  intros R R2 R' sp0 buf len' s7v (P2 & P9 & P23 & P19 & PK) HK.
  repeat split; try assumption. intros r Hr. rewrite (PK r Hr). apply HK, Hr.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma frame_mod_intro : forall M M' rs,
  (forall a, outside a rs -> M' a = M a) -> mem_grows M M' -> frame_mod M M' rs.
Proof. intros M M' rs E G. split; [exact E | exact G]. Qed.

#[using="Type"] Lemma wbytes_out : forall M (a x : word) bs,
  (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned x)%Z ->
  wbytes M a bs x = M x.
Proof. intros M a x bs Hnw Hx. apply MemSplit.wbytes_outside; [exact Hnw | exact Hx]. Qed.

Section PostAlgebra.
  Variables (content : list byte) (M : word -> option byte) (sp0 buf len n : Z) (ra : word) (bs : list byte).
  Hypothesis Hlen : (0 <= len)%Z.
  Hypothesis Hn : (0 <= n <= 65536)%Z.
  Hypothesis Hbuf : (0xe6000 <= buf)%Z.
  Hypothesis Hsp : (sp0 <= 2 ^ 63)%Z.
  Hypothesis Hbsp : (buf + len + n <= sp0 - 144)%Z.
  Hypothesis Hbl : Z.of_nat (length bs) = n.
  Hypothesis Hbs : bs = pref n (dropz len content).

  (* [comment removed for export] *)
  #[local] Notation M1 := (wbytes M (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 ra)) (only parsing).
  #[local] Notation M2 := (wbytes (wbytes M1 (Z_to_bv 64 STAGE) bs) (Z_to_bv 64 (buf + len)) bs) (only parsing).

  #[using="Hlen Hn Hbuf Hsp Hbsp Hbl Hbs"] Lemma post_mem_here : loop_post_mem content M M2 sp0 buf len (len + n).
  Proof.
    pose proof (length_N_to_le_bytes 8 ra) as L8. unfold STAGE in *. split.
    - apply frame_mod_intro.
      + intros a [O1 [O2 [O3 _]]]. cbn [fst snd loop_regions] in *. unfold in_rng, STAGE in *. rewrite !u_small in * by lia.
        rewrite wbytes_out by (rewrite ?Hbl, ?u_small by lia; lia).
        rewrite wbytes_out by (rewrite ?Hbl, ?u_small by lia; lia).
        rewrite wbytes_out by (rewrite ?L8, ?u_small by lia; lia). reflexivity.
      + eapply mem_grows_trans; [apply wbytes_grows|]. eapply mem_grows_trans; apply wbytes_grows.
    - replace (len + n - len)%Z with n by lia. rewrite <- Hbs. replace (Z.to_nat n) with (length bs) by lia.
      apply rdn_wbytes_self. rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Hlen Hn Hbuf Hsp Hbsp Hbl Hbs"] Lemma post_mem_compose : forall M' (len' : Z),
    (len + n <= len')%Z -> (buf + len' <= sp0 - 144)%Z ->
    loop_post_mem content M2 M' sp0 buf (len + n) len' ->
    loop_post_mem content M M' sp0 buf len len'.
  Proof.
    intros M' len' Hl' Hb' [[FE FG] RD]. pose proof (length_N_to_le_bytes 8 ra) as L8. split.
    - apply frame_mod_intro.
      + intros a [O1 [O2 [O3 _]]]. cbn [fst snd loop_regions] in *. unfold in_rng, STAGE in *. rewrite !u_small in * by lia.
        rewrite FE by (cbn [outside loop_regions fst snd]; unfold in_rng, STAGE; rewrite !u_small by lia; repeat split; lia).
        rewrite wbytes_out by (rewrite ?Hbl, ?u_small by lia; lia).
        rewrite wbytes_out by (unfold STAGE; rewrite ?Hbl, ?u_small by lia; lia).
        rewrite wbytes_out by (rewrite ?L8, ?u_small by lia; lia). reflexivity.
      + eapply mem_grows_trans; [|exact FG].
        eapply mem_grows_trans; [apply wbytes_grows|]. eapply mem_grows_trans; apply wbytes_grows.
    - replace (Z.to_nat (len' - len)) with (length bs + Z.to_nat (len' - (len + n)))%nat by lia.
      replace (pref (len' - len) (dropz len content)) with (bs ++ pref (len' - (len + n)) (dropz (len + n) content))
        by (rewrite Hbs at 1; rewrite pref_chain by lia; f_equal; lia).
      apply SeqExec.rdn_app.
      + rewrite (frame_mod_rdn RSEGS M2 M' _ (length bs) (Z_to_bv 64 (buf + len)) (conj FE FG)).
        * apply rdn_wbytes_self. rewrite u_small by lia. lia.
        * intros i Hi. rewrite (u_small (buf + len)) by lia. cbn [outside loop_regions fst snd]. unfold in_rng, STAGE. rewrite ?Hbl, !u_small by lia. repeat split; lia.
        * rewrite u_small by lia. lia.
      + replace (Z_to_bv 64 (buf + len) + nat_to_word (length bs)) with (Z_to_bv 64 (buf + (len + n))); [exact RD|].
        unfold nat_to_word. apply bv_eq. rewrite bv_add_unsigned, !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia.
  Qed.
End PostAlgebra.

(* [comment removed for export] *)
#[using="Type"] Lemma post_mem_end : forall content M (sp0 buf len : Z) (ra1 ra2 : word),
  (0 <= len)%Z -> (len <= Z.of_nat (length content))%Z -> (sp0 <= 2 ^ 63)%Z -> (144 <= sp0)%Z -> (0 <= buf + len < 2 ^ 64)%Z ->
  (len = Z.of_nat (length content))%Z ->
  loop_post_mem content M
    (wbytes (wbytes M (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 ra1)) (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 ra2))
    sp0 buf len len.
Proof.
  intros content M sp0 buf len ra1 ra2 Hl HlL Hsp Hsp' Hb HL.
  pose proof (length_N_to_le_bytes 8 ra1) as L1. pose proof (length_N_to_le_bytes 8 ra2) as L2. split.
  - apply frame_mod_intro.
    + intros a [O1 _]. cbn [fst snd loop_regions] in O1. unfold in_rng in O1. rewrite !u_small in O1 by lia.
      rewrite wbytes_out by (rewrite ?L2, ?u_small by lia; lia).
      rewrite wbytes_out by (rewrite ?L1, ?u_small by lia; lia). reflexivity.
    + eapply mem_grows_trans; apply wbytes_grows.
  - rewrite Z.sub_diag. cbn [Z.to_nat rdn]. rewrite pref_0. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma stage_store_ok : forall M n, (Z.of_nat n <= 65536)%Z -> store_ok RSEGS M (Z_to_bv 64 STAGE) n = true.
Proof. intros M n Hn. unfold STAGE. apply data_store_ok; lia. Qed.

#[using="Type"] Lemma stage_access_okb : forall cnt, (0 <= cnt <= 65536)%Z -> access_okb (Z_to_bv 64 STAGE) cnt = true.
Proof. intros cnt Hc. apply access_okb_true_intro; unfold STAGE; rewrite ?u_small by lia; rewrite ?task_size_val; lia. Qed.

Section ChunkLoop.
  Variables (path content : list byte) (stdin0 : AmbIn) (fs0 : Fs) (tid : word) (V : VmMaps).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (UbReadStage.modelG path stdin0 fs0 tid) (only parsing).

  #[using="Hfile"] Theorem chunk_loop_mid : forall (fuel : nat) (R : bvmap 5 word) (M : word -> option byte) (sp0 buf len cap : Z) (K : TSet),
    (cap - len <= Z.of_nat fuel)%Z ->
    mid_regs R sp0 buf len cap ->
    (0 <= len < cap)%Z -> (cap <= 2 ^ 40)%Z -> (0xe6000 <= buf)%Z -> (buf + cap <= sp0 - 144)%Z ->
    (sp0 <= 2 ^ 47)%Z ->
    (len <= L)%Z ->
    store_ok RSEGS M (Z_to_bv 64 (sp0 - 136)) 8 = true ->
    store_ok RSEGS M (Z_to_bv 64 (buf + len)) (Z.to_nat (cap - len)) = true ->
    (* [comment removed for export] *)
    ((cap <= L)%Z -> forall R' M',
        loop_post_regs R R' sp0 buf cap buf -> loop_post_mem content M M' sp0 buf len cap ->
        realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x326c8) M' (seg_rom RSEGS)) (modelG cap V)) K) ->
    (* [comment removed for export] *)
    ((L < cap)%Z -> forall R' M',
        loop_post_regs R R' sp0 buf L 0 -> loop_post_mem content M M' sp0 buf len L ->
        realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x32730) M' (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)) K) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32700) M (seg_rom RSEGS)) (modelG len V)) K.
  Proof.
    induction fuel as [|fuel IH]; intros R M sp0 buf len cap K Hfuel (R2 & R9 & R19 & R20 & R21 & R22) Hlen Hcap Hbuf Hbc Hsp HlenL SOKs SOKb HFULL HEND.
    { exfalso. cbn in Hfuel. lia. }
    pose proof (want_range cap len Hlen) as [Hw1 Hw2].
    (* [comment removed for export] *)
    destruct (walkA R M (seg_rom RSEGS) sp0 buf len cap R2 R19 R21 R9 R20 R22
               ltac:(lia) ltac:(lia) Hlen Hcap SOKs)
      as (R1 & RUN1 & A17 & A10 & A11 & A12 & A1 & A2 & A9 & A19 & AK0).
    assert (AK : forall r, In r loop_kept -> getr R1 r = getr R r) by (intros r Hr; apply AK0; right; exact Hr).
    replace (Z_to_bv 64 0x32700) with (0x32700 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [reflexivity | reflexivity | exact RUN1 |]. clear RUN1.
    set (M1 := wbytes M (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x3271c))).
    assert (SOK1s : store_ok RSEGS M1 (Z_to_bv 64 (sp0 - 136)) 8 = true)
      by (eapply store_ok_mono; [apply wbytes_grows | exact SOKs]).
    assert (RD1 : rdn RSEGS M1 (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x3271c)))
      by (apply rdn_wbytes_hit8; rewrite u_small by lia; lia).
    (* [comment removed for export] *)
    pose proof (read_chunk content len (want cap len) ltac:(lia) ltac:(lia) ltac:(lia)) as RC. cbn zeta in RC.
    destruct RC as [RN RB].
    remember (file_read content (Z_to_bv 64 len) (Z_to_bv 64 (want cap len))) as bs eqn:Hbs.
    set (n := Z.of_nat (length bs)) in *.
    eapply (rz_read_file RSEGS R1 (0xa7d30 : word) M1 (modelG len V) W_a7d30 (Z_to_bv 64 3) path (Z_to_bv 64 len) content (want cap len) K F_a7d30 E_a7d30).
    - reflexivity.
    - reflexivity.
    - exact A17.
    - exact A10.
    - rewrite u_small by lia. lia.
    - reflexivity.
    - exact Hfile.
    - exact A12.
    - lia.
    - rewrite rw_bytes_max_val. lia.
    - lia.
    - rewrite A11. apply stage_store_ok. lia.
    - rewrite A11. apply stage_access_okb. lia.
    - cbv zeta. rewrite A12, A11, <- Hbs. rewrite modelG_read.
      change (len_word bs) with (Z_to_bv 64 n).
      replace (Z_to_bv 64 len + Z_to_bv 64 n) with (Z_to_bv 64 (len + n))
        by (apply bv_eq; rewrite bv_add_unsigned, !u_small by lia; rewrite bv_wrap_small; [lia | unfold bv_modulus; lia]).
      change (mkModelA (fds_file path (Z_to_bv 64 (len + n))) V stdin0 fs0 None (Some tid) None) with (modelG (len + n) V).
      replace (v_addi (0xa7d30 : word) 4) with (0xa7d34 : word) by (apply bv_eq; reflexivity).
      set (M2 := wbytes M1 (Z_to_bv 64 STAGE) bs).
      destruct (Z.eq_dec n 0) as [Hn0|Hn0].
      + (* [comment removed for export] *)
        assert (bs = []) as Hnil by (destruct bs; [reflexivity | subst n; cbn in Hn0; lia]).
        assert (HLe : L = len) by lia.
        subst M2. rewrite Hnil. cbn [wbytes]. rewrite Hn0.
        destruct (walkBC (regupd R1 10 (Z_to_bv 64 0)) M1 (seg_rom RSEGS) sp0 buf len
                   ltac:(gres; exact A1) ltac:(gres; exact A2) ltac:(gres; reflexivity)
                   ltac:(gres; exact A19) ltac:(gres; exact A9) ltac:(gres; rewrite (AK 20%bv) by (cbv; noncert_qtauto); exact R20)
                   ltac:(lia) ltac:(lia) ltac:(lia) RD1 SOK1s)
          as (R3 & RUN3 & C17 & C10 & C1 & C2 & C19 & C23 & CK).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN3 |]. clear RUN3.
        set (M3 := wbytes M1 (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x32730))).
        (* [comment removed for export] *)
        eapply (rz_close RSEGS R3 (0xa7d30 : word) M3 (modelG (len + 0) V) W_a7d30 (Z_to_bv 64 3) _ K F_a7d30 E_a7d30).
        * reflexivity.
        * reflexivity.
        * exact C17.
        * exact C10.
        * rewrite u_small by lia. lia.
        * reflexivity.
        * rewrite modelG_close.
          replace (v_addi (0xa7d30 : word) 4) with (0xa7d34 : word) by (apply bv_eq; reflexivity).
          destruct (walkD (regupd R3 10 (Z_to_bv 64 0)) M3 (seg_rom RSEGS) sp0
                     ltac:(gres; exact C1) ltac:(gres; exact C2) ltac:(gres; reflexivity) ltac:(lia) ltac:(lia)
                     ltac:(subst M3; apply rdn_wbytes_hit8; rewrite u_small by lia; lia))
            as (R4 & RUN4 & D2 & DK).
          eapply rz_msteps; [reflexivity | reflexivity | exact RUN4 |]. clear RUN4.
          replace (0x32730 : word) with (Z_to_bv 64 0x32730) by (apply bv_eq; reflexivity).
          apply (HEND ltac:(lia) R4 M3).
          -- (* [comment removed for export] *)
             split; [exact D2|]. split; [|split; [|split]].
             ++ rewrite (DK 9%bv) by (cbv; noncert_qtauto). rewrite getr_other by reg_neq_tac.
                rewrite (CK 9%bv) by (cbv; noncert_qtauto). rewrite getr_other by reg_neq_tac. exact A9.
             ++ rewrite (DK 23%bv) by (cbv; noncert_qtauto). rewrite getr_other by reg_neq_tac. exact C23.
             ++ rewrite (DK 19%bv) by (cbv; noncert_qtauto). rewrite getr_other by reg_neq_tac. rewrite C19. f_equal. lia.
             ++ intros r Hr. rewrite (DK r) by (cbn [In]; right; right; right; apply loop_kept_B, Hr).
                rewrite (kept_regupd10 _ _ r Hr). rewrite (CK r (loop_kept_B r Hr)). rewrite (kept_regupd10 _ _ r Hr). apply AK, Hr.
          -- (* [comment removed for export] *)
             subst M3 M1. rewrite <- HLe. apply post_mem_end; lia.
      + (* [comment removed for export] *)
        assert (RD2 : rdn RSEGS M2 (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x3271c))).
        { subst M2. unfold STAGE. rewrite rdn_wbytes_out; [exact RD1 | rewrite !u_small by lia; lia | rewrite u_small by lia; lia | rewrite u_small by lia; lia]. }
        destruct (walkB (regupd R1 10 (Z_to_bv 64 n)) M2 (seg_rom RSEGS) sp0 buf len n
                   ltac:(gres; exact A1) ltac:(gres; exact A2) ltac:(gres; reflexivity)
                   ltac:(gres; exact A19) ltac:(gres; exact A9) ltac:(gres; rewrite (AK 22%bv) by (cbv; noncert_qtauto); exact R22)
                   ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) RD2)
          as (R5 & RUN5 & B1 & B2 & B10 & B11 & B12 & B23 & B19 & B9 & BK).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN5 |]. clear RUN5.
        assert (BKK : forall r, In r loop_kept -> getr R5 r = getr R r).
        { intros r Hr. rewrite (BK r (loop_kept_B r Hr)). rewrite (kept_regupd10 _ _ r Hr). apply AK, Hr. }
        (* [comment removed for export] *)
        assert (SRC : rdn RSEGS M2 (Z_to_bv 64 STAGE) (length bs) = Some bs).
        { subst M2. apply rdn_wbytes_self. unfold STAGE. rewrite u_small by lia. lia. }
        assert (MC : mcH M2 (Z_to_bv 64 (buf + len)) (Z_to_bv 64 STAGE) n bs).
        { constructor.
          - lia.
          - lia.
          - exact SRC.
          - subst M2 M1. eapply store_ok_mono; [eapply mem_grows_trans; [apply wbytes_grows | apply wbytes_grows] |].
            eapply (store_ok_sub _ _ _ _ (Z.to_nat (cap - len))); [ | exact SOKb | | ]; rewrite ?u_small by lia; lia.
          - unfold STAGE. rewrite !u_small by lia. lia.
          - unfold STAGE. rewrite u_small by lia. lia.
          - rewrite u_small by lia. lia. }
        destruct (ref_memcpy M2 (Z_to_bv 64 (buf + len)) (Z_to_bv 64 STAGE) n bs (seg_rom RSEGS) MC R5 (0x326b4 : word)
                    ltac:(apply bv_eq; reflexivity) ltac:(rewrite B1; apply bv_eq; reflexivity) B10 B11 B12)
          as (R6 & RUN6 & KP6).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN6 |]. clear RUN6.
        set (M4 := wbytes M2 (Z_to_bv 64 (buf + len)) bs).
        assert (K6 : forall r, In r loop_kept -> getr R6 r = getr R r).
        { intros r Hr. rewrite (KP6 r (loop_kept_callee r Hr)). apply BKK, Hr. }
        assert (C9 : getr R6 9 = Z_to_bv 64 buf) by (rewrite (KP6 9%bv) by (cbv; noncert_qtauto); exact B9).
        assert (C23 : getr R6 23 = Z_to_bv 64 n) by (rewrite (KP6 23%bv) by (cbv; noncert_qtauto); exact B23).
        assert (C19 : getr R6 19 = Z_to_bv 64 len) by (rewrite (KP6 19%bv) by (cbv; noncert_qtauto); exact B19).
        assert (C21 : getr R6 21 = Z_to_bv 64 cap) by (rewrite (KP6 21%bv) by (cbv; noncert_qtauto); rewrite (BKK 21%bv) by (cbv; noncert_qtauto); exact R21).
        assert (C2 : getr R6 2 = Z_to_bv 64 (sp0 - 128)) by (rewrite (KP6 2%bv) by (cbv; noncert_qtauto); exact B2).
        assert (GR4 : mem_grows M M4).
        { subst M4 M2 M1. eapply mem_grows_trans; [|apply wbytes_grows]. eapply mem_grows_trans; [|apply wbytes_grows]. apply wbytes_grows. }
        destruct (Z.eq_dec (len + n) cap) as [Hfull|Hmore].
        * (* [comment removed for export] *)
          destruct (walkB2_full R6 M4 (seg_rom RSEGS) buf len n cap C23 C19 C9 C21 ltac:(lia) ltac:(lia) Hfull Hcap)
            as (R7 & RUN7 & E19 & E23 & E9 & EK).
          eapply rz_msteps; [reflexivity | reflexivity | exact RUN7 |]. clear RUN7.
          rewrite Hfull.
          replace (0x326c8 : word) with (Z_to_bv 64 0x326c8) by (apply bv_eq; reflexivity).
          apply (HFULL ltac:(lia) R7 M4).
          -- split; [rewrite (EK 2%bv) by (cbv; noncert_qtauto); exact C2|].
             split; [exact E9|]. split; [exact E23|]. split; [exact E19|].
             intros r Hr. rewrite (EK r) by (cbn [In]; right; right; right; apply loop_kept_B, Hr). apply K6, Hr.
          -- subst M4 M2 M1. rewrite <- Hfull. eapply post_mem_here; try lia. exact RB.
        * (* [comment removed for export] *)
          destruct (walkB2_more R6 M4 (seg_rom RSEGS) buf len n cap C23 C19 C9 C21 ltac:(lia) ltac:(lia) ltac:(lia) Hcap)
            as (R7 & RUN7 & E19 & E23 & E9 & EK).
          eapply rz_msteps; [reflexivity | reflexivity | exact RUN7 |]. clear RUN7.
          replace (0x32700 : word) with (Z_to_bv 64 0x32700) by (apply bv_eq; reflexivity).
          assert (EKK : forall r, In r loop_kept -> getr R7 r = getr R r).
          { intros r Hr. rewrite (EK r) by (cbn [In]; right; right; right; exact Hr). apply K6, Hr. }
          apply (IH R7 M4 sp0 buf (len + n)%Z cap K ltac:(lia)).
          -- repeat split.
             ++ rewrite (EK 2%bv) by (cbv; noncert_qtauto). exact C2.
             ++ exact E9.
             ++ exact E19.
             ++ rewrite (EKK 20%bv) by (cbv; noncert_qtauto). exact R20.
             ++ rewrite (EKK 21%bv) by (cbv; noncert_qtauto). exact R21.
             ++ rewrite (EKK 22%bv) by (cbv; noncert_qtauto). exact R22.
          -- lia.
          -- lia.
          -- lia.
          -- lia.
          -- lia.
          -- lia.
          -- eapply store_ok_mono; [exact GR4 | exact SOKs].
          -- eapply store_ok_mono; [exact GR4 |].
             eapply (store_ok_sub _ _ _ _ (Z.to_nat (cap - len))); [ | exact SOKb | | ]; rewrite ?u_small by lia; lia.
          -- intros HcL R' M' PR PM. apply (HFULL HcL R' M').
             ++ eapply post_regs_compose; [exact PR | exact EKK].
             ++ subst M4 M2 M1. eapply post_mem_compose; [ | | | | | | exact RB | | | exact PM]; lia.
          -- intros HLc R' M' PR PM. apply (HEND HLc R' M').
             ++ eapply post_regs_compose; [exact PR | exact EKK].
             ++ subst M4 M2 M1. eapply post_mem_compose; [ | | | | | | exact RB | | | exact PM]; lia.
  Qed.
End ChunkLoop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma frame_mod_split2 : forall M M' (a1 : word) (n1 : Z) (a2 : word) (n2 : Z),
  frame_mod M M' [(a1, n1); (a2, n2)] ->
  exists Mm, frame_mod M Mm [(a1, n1)] /\ frame_mod Mm M' [(a2, n2)].
Proof.
  intros M M' a1 n1 a2 n2 [EQ GR].
  exists (fun x => if in_rngb x a1 n1 then M' x else M x). split; split.
  - intros a [Ha _]. destruct (in_rngb a a1 n1) eqn:Hb; [|reflexivity].
    exfalso. apply Ha. apply in_rngb_spec. exact Hb.
  - intros x Hx. destruct (in_rngb x a1 n1); [apply GR, Hx | exact Hx].
  - intros a [Ha _]. destruct (in_rngb a a1 n1) eqn:Hb; [reflexivity|].
    apply EQ. cbn [outside]. split; [|split; [exact Ha | exact I]].
    intros Hin. apply in_rngb_spec in Hin. rewrite Hin in Hb. discriminate.
  - intros x Hx. destruct (in_rngb x a1 n1); [exact Hx | apply GR, Hx].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma know_ok_frame2 : forall E M M' kn (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z),
  know_ok RSEGS E M kn -> flat E (SA b1 k1) n1 -> flat E (SA b2 k2) n2 ->
  frame_mod M M' [(adenot E (SA b1 k1), n1); (adenot E (SA b2 k2), n2)] ->
  know_ok RSEGS E M' (kn_frame (kn_frame kn b1 k1 n1) b2 k2 n2).
Proof.
  intros E M M' kn b1 k1 n1 b2 k2 n2 HK F1 F2 FR.
  destruct (frame_mod_split2 _ _ _ _ _ _ FR) as (Mm & [E1 G1] & [E2 G2]).
  pose proof (flat_u E _ _ F1) as U1. pose proof (flat_u E _ _ F2) as U2.
  eapply know_ok_frame; [eapply know_ok_frame; [exact HK | exact F1 | | exact G1] | exact F2 | | exact G2].
  - intros x Hx. apply E1. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite U1. lia.
  - intros x Hx. apply E2. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite U2. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma frame_mod_split3 : forall M M' (a1 : word) (n1 : Z) (a2 : word) (n2 : Z) (a3 : word) (n3 : Z),
  frame_mod M M' [(a1, n1); (a2, n2); (a3, n3)] ->
  exists Mm, frame_mod M Mm [(a1, n1)] /\ frame_mod Mm M' [(a2, n2); (a3, n3)].
Proof.
  intros M M' a1 n1 a2 n2 a3 n3 [EQ GR].
  exists (fun x => if in_rngb x a1 n1 then M' x else M x). split; split.
  - intros a [Ha _]. destruct (in_rngb a a1 n1) eqn:Hb; [|reflexivity].
    exfalso. apply Ha. apply in_rngb_spec. exact Hb.
  - intros x Hx. destruct (in_rngb x a1 n1); [apply GR, Hx | exact Hx].
  - intros a [Ha [Hb3 _]]. destruct (in_rngb a a1 n1) eqn:Hb; [reflexivity|].
    apply EQ. cbn [outside]. split; [|split; [exact Ha | split; [exact Hb3 | exact I]]].
    intros Hin. apply in_rngb_spec in Hin. rewrite Hin in Hb. discriminate.
  - intros x Hx. destruct (in_rngb x a1 n1); [exact Hx | apply GR, Hx].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma know_ok_frame3 : forall E M M' kn (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) (b3 : expr) (k3 n3 : Z),
  know_ok RSEGS E M kn -> flat E (SA b1 k1) n1 -> flat E (SA b2 k2) n2 -> flat E (SA b3 k3) n3 ->
  frame_mod M M' [(adenot E (SA b1 k1), n1); (adenot E (SA b2 k2), n2); (adenot E (SA b3 k3), n3)] ->
  know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn b1 k1 n1) b2 k2 n2) b3 k3 n3).
Proof.
  intros E M M' kn b1 k1 n1 b2 k2 n2 b3 k3 n3 HK F1 F2 F3 FR.
  destruct (frame_mod_split3 _ _ _ _ _ _ _ _ FR) as (Mm & [E1 G1] & FR2).
  pose proof (flat_u E _ _ F1) as U1.
  eapply know_ok_frame2; [ | exact F2 | exact F3 | exact FR2].
  eapply know_ok_frame; [exact HK | exact F1 | | exact G1].
  intros x Hx. apply E1. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite U1. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma seg_rom_high : forall (a : word), (0xe6000 <= bv_unsigned a)%Z -> seg_rom RSEGS a = None.
Proof.
  intros a Ha. unfold seg_rom. unfold memory_read.
  cbn -[bv_unsigned Z.leb Z.ltb Z.add Z.sub N.leb N.ltb N.add bv_extract Z.of_N Z.to_N].
  cbn [Z.of_N].
  repeat (lazymatch goal with
          | |- context [((?lo <=? bv_unsigned a)%Z && ?c)%bool] =>
              replace c with false by (symmetry; apply Z.leb_gt; lia); rewrite andb_false_r
          end).
  reflexivity.
Qed.

#[using="Type"] Lemma rdn1_mem_high : forall M (a : word) (b : byte),
  (0xe6000 <= bv_unsigned a)%Z -> rdn RSEGS M a 1 = Some [b] -> M a = Some b.
Proof.
  intros M a b Ha H. cbn [rdn] in H. destruct (M a) as [b'|] eqn:Hm.
  - injection H as ->. reflexivity.
  - rewrite seg_rom_high in H by exact Ha. discriminate.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kblob_of_rdn : forall E M (e : expr) (a : word) (off n : Z) (k : nat) (bs : list byte),
  edenot E e = a -> eb E k = bs -> Z.of_nat (length bs) = n ->
  (0xe6000 <= bv_unsigned a + off)%Z -> (bv_unsigned a + off + n < 2 ^ 64)%Z ->
  rdn RSEGS M (Z_to_bv 64 (bv_unsigned a + off)) (length bs) = Some bs ->
  kentry_ok RSEGS E M (KBlob (SA e off) (ELit n) k).
Proof.
  intros E M e a off n k bs He Hb Hn Hlo Hhi RD.
  eapply (kblob_intro RSEGS E M e a off (ELit n) k bs He Hb); try lia.
  - cbn [edenot]. rewrite u_small by lia. lia.
  - intros i Hi.
    pose proof (SeqExec.rdn_nth RSEGS M (length bs) (Z_to_bv 64 (bv_unsigned a + off)) bs (Z.to_nat i) RD ltac:(lia)) as R1.
    apply rdn1_mem_high; [rewrite u_small by lia; lia|].
    replace (Z_to_bv 64 (bv_unsigned a + off + i)) with (Z_to_bv 64 (bv_unsigned a + off) + nat_to_word (Z.to_nat i)); [exact R1|].
    unfold nat_to_word. apply bv_eq. rewrite bv_add_unsigned, Z2Nat.id, !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pres_loop_post : forall content M0 M M' (sp0 : word) (buf len len' : Z),
  pres M0 M sp0 -> loop_post_mem content M M' (bv_unsigned sp0) buf len len' ->
  (0x7fff80000000 <= bv_unsigned sp0)%Z -> (0xe6000 <= buf + len)%Z -> (buf + len' <= bv_unsigned sp0 - 144)%Z -> (len <= len')%Z ->
  pres M0 M' sp0.
Proof.
  intros content M0 M M' sp0 buf len len' P [[EQ _] _] Hsp Hlo Hhi Hll x Hx.
  pose proof (u64_range sp0) as U.
  rewrite <- (P x Hx). apply EQ. cbn [outside loop_regions fst snd]. unfold in_rng, rd_cell, STAGE in *. rewrite !u_small by lia.
  repeat split; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma stack_writable_grows : forall M M' sp0, mem_grows M M' -> stack_writable M sp0 -> stack_writable M' sp0.
Proof. intros M M' sp0 G W d m Hd Hm. eapply store_ok_mono; [exact G | apply W; assumption]. Qed.
#[using="Type"] Lemma group_writable_grows : forall M M' gm, mem_grows M M' -> group_writable M gm -> group_writable M' gm.
Proof. intros M M' gm G W d m Hd Hm. eapply store_ok_mono; [exact G | apply W; assumption]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma content_at_buf : forall content M M' (sp0 buf held : Z),
  (0 <= held <= Z.of_nat (length content))%Z -> (0xe6000 <= buf)%Z -> (buf + Z.of_nat (length content) <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  rdn RSEGS M (Z_to_bv 64 buf) (Z.to_nat held) = Some (pref held content) ->
  loop_post_mem content M M' sp0 buf held (Z.of_nat (length content)) ->
  rdn RSEGS M' (Z_to_bv 64 buf) (length content) = Some content.
Proof.
  intros content M M' sp0 buf held Hh Hb Hbl Hsp HELD [FR RD].
  replace (length content) with (Z.to_nat held + Z.to_nat (Z.of_nat (length content) - held))%nat by lia.
  rewrite <- (pref_dropz_app held content) at 2. rewrite <- (pref_all (Z.of_nat (length content) - held) (dropz held content))
    by (rewrite dropz_length by lia; lia).
  apply SeqExec.rdn_app.
  - rewrite (frame_mod_rdn RSEGS M M' _ (Z.to_nat held) (Z_to_bv 64 buf) FR); [exact HELD| |rewrite u_small by lia; lia].
    intros i Hi. rewrite (u_small buf) by lia. cbn [outside loop_regions fst snd]. unfold in_rng, STAGE. rewrite !u_small by lia. repeat split; lia.
  - replace (Z_to_bv 64 buf + nat_to_word (Z.to_nat held)) with (Z_to_bv 64 (buf + held)); [exact RD|].
    unfold nat_to_word. apply bv_eq. rewrite bv_add_unsigned, Z2Nat.id, !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia.
Qed.
End FPW_4.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
