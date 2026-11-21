(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker (A1) tool *)
From LinuxProcessSemantics.LinuxProcessSem Require State Run. (* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import ModelAmb.
From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import TgtO_zlib_uncompress2_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk LibMaskBits SumWalkTac RefMemcpyLib.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require LiaFast.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require PropExec CatExec CatSim SeqExec StepTac StoreOk ShapeAlg Hoare WalkTac Frame MemSplit LibMaskBits SumWalkTac RefMemcpyLib SpecConsts SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefNodes LibKnowFrame RefReadLib. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require U7MemcpyBase U7Memcpy U7ReadBase U7ReadStage.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require Import U7_code_14708_15000 U7_code_1a000_1b000 U7_code_1c000_1d000 U7_code_21000_21d00.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
Module S0ReadChunkW.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Hoare OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.WalkTac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.LibMaskBits OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.SumWalkTac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.RefMemcpyLib.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.LiaFast.
(* [comment removed for export] *)
#[local] Abbreviation RS := U7ReadBase.RS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

#[local] Abbreviation RSEGS := TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition want (cap len : Z) : Z := if (cap - len <? 65536)%Z then (cap - len)%Z else 65536%Z.

Lemma want_range : forall cap len, (0 <= len < cap)%Z -> (1 <= want cap len <= 65536)%Z /\ (want cap len <= cap - len)%Z.
Proof. intros cap len H. unfold want. destruct (Z.ltb_spec (cap - len) 65536); lia. Qed.

(* [comment removed for export] *)
Definition loop_kept : list reg := [3; 4; 8; 18; 20; 21; 22; 24; 25; 26; 27]%bv.

Ltac kept_list l :=
  intros r Hr; cbv [l In] in Hr;
  repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr.

(* [comment removed for export] *)
Lemma walkA {RCa1 : RunCtx}  : forall regs mem rom (sp0 buf len cap : Z),
  getr regs 2 = Z_to_bv 64 (sp0 - 128) -> getr regs 19 = Z_to_bv 64 len -> getr regs 21 = Z_to_bv 64 cap ->
  getr regs 9 = Z_to_bv 64 buf -> getr regs 20 = Z_to_bv 64 3 -> getr regs 22 = Z_to_bv 64 RS ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  (0 <= len < cap)%Z -> (cap <= 2 ^ 40)%Z ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (sp0 - 136)) 8 = true ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x149c8 : word) mem rom)
                 (mkst regs' (0x21da0 : word)
                       (wbytes mem (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x149e4))) rom)
    /\ getr regs' 17 = Z_to_bv 64 63 /\ getr regs' 10 = Z_to_bv 64 3
    /\ getr regs' 11 = Z_to_bv 64 RS /\ getr regs' 12 = Z_to_bv 64 (want cap len)
    /\ getr regs' 1 = Z_to_bv 64 0x21e4c /\ getr regs' 2 = Z_to_bv 64 (sp0 - 144)
    /\ getr regs' 9 = Z_to_bv 64 buf /\ getr regs' 19 = Z_to_bv 64 len
    /\ (forall r, In r (23 :: loop_kept)%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 buf len cap Hsp Hs3 Hs5 Hs1 Hs4 Hs6 SPlo SPhi Hlen Hcap SOK.
  (* [comment removed for export] *)
  Ltac walkA_tail Hs4 Hs6 Hsp SOK sp0 :=
      stepn F_14930 D_14930; rewrite Hs4;
      stepn F_14934 D_14934; rewrite Hs6;
      stepn F_14938 D_14938;
      (* [comment removed for export] *)
      stepn F_21ccc D_21ccc; rewrite Hsp; sp_renorm;
      stepST F_21cd0 D_21cd0 (Z_to_bv 64 (sp0 - 136)) (Z_to_bv 64 0x149e4) ltac:(exact SOK);
      stepn F_21cd4 D_21cd4; stepn F_21cd8 D_21cd8; stepn F_21cdc D_21cdc; stepn F_21ce0 D_21ce0;
      stepn F_21ce4 D_21ce4; stepn F_21ce8 D_21ce8; stepn F_21cec D_21cec; stepn F_21cf0 D_21cf0;
      stepn F_21c50 D_21c50;
      stepn F_21c2c D_21c2c; stepn F_21c30 D_21c30; stepn F_21c34 D_21c34; stepn F_21c38 D_21c38;
      stepn F_21c3c D_21c3c; stepn F_21c40 D_21c40; stepn F_21c44 D_21c44;
      apply mst_refl.
  Ltac walkA_post :=
      repeat split; gres; try reflexivity; try assumption;
      intros r Hr; cbv [loop_kept In] in Hr;
      repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr.
  unfold want. destruct (Z.ltb_spec (cap - len) 65536) as [LT|GE]; eexists; split.
  - (* [comment removed for export] *)
    stepn F_14920 D_14920. rewrite Hs5, Hs3. rewrite (v_sub_ZZ cap len) by lia.
    (* [comment removed for export] *)
    stepn F_14924 D_14924.
    (* [comment removed for export] *)
    stepb_tk F_14928 D_14928 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
    walkA_tail Hs4 Hs6 Hsp SOK sp0.
  - walkA_post.
  - stepn F_14920 D_14920. rewrite Hs5, Hs3. rewrite (v_sub_ZZ cap len) by lia.
    stepn F_14924 D_14924.
    (* [comment removed for export] *)
    stepb_ft F_14928 D_14928 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
    stepn F_1492c D_1492c.
    walkA_tail Hs4 Hs6 Hsp SOK sp0.
  - walkA_post.
Qed.

(* [comment removed for export] *)
Definition loopB_kept : list reg := [3; 4; 8; 9; 18; 20; 21; 22; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Lemma walkB1 {RCa1 : RunCtx}  : forall regs mem rom (sp0 buf len n : Z),
  getr regs 1 = Z_to_bv 64 0x21e4c -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 n ->
  getr regs 19 = Z_to_bv 64 len -> getr regs 9 = Z_to_bv 64 buf -> getr regs 22 = Z_to_bv 64 RS ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  (0 < n <= 65536)%Z -> (0 <= len)%Z -> (0 <= buf)%Z -> (buf + len <= 2 ^ 62)%Z ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x149e4)) ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x21da4 : word) mem rom) (mkst regs' (0x2147c : word) mem rom)
    /\ getr regs' 1 = Z_to_bv 64 0x1497c /\ getr regs' 2 = Z_to_bv 64 (sp0 - 128)
    /\ getr regs' 10 = Z_to_bv 64 (buf + len) /\ getr regs' 11 = Z_to_bv 64 RS /\ getr regs' 12 = Z_to_bv 64 n
    /\ getr regs' 23 = Z_to_bv 64 n /\ getr regs' 19 = Z_to_bv 64 len /\ getr regs' 9 = Z_to_bv 64 buf
    /\ (forall r, In r loopB_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 buf len n Hra Hsp Ha0 Hs3 Hs1 Hs6 SPlo SPhi Hn Hlen Hbuf Hbl RD.
  eexists. split.
  - (* [comment removed for export] *)
    stepret F_21c4c D_21c4c (0x21e4c : word) ltac:(rewrite Hra; bveq).
    (* [comment removed for export] *)
    stepLD8 F_21cf4 D_21cf4 (Z_to_bv 64 0x149e4).
    (* [comment removed for export] *)
    stepn F_21cf8 D_21cf8. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_21cfc D_21cfc.
    (* [comment removed for export] *)
    stepn F_1a438 D_1a438. stepn F_1a43c D_1a43c.
    (* [comment removed for export] *)
    stepb_tk F_1a440 D_1a440 ltac:(rewrite Ha0; rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
    (* [comment removed for export] *)
    stepret F_1a46c D_1a46c (0x149e4 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepb_ft F_1493c D_1493c ltac:(rewrite Ha0; apply c_lts_pos_0; u_norm; lia).
    (* [comment removed for export] *)
    stepn F_14940 D_14940. rewrite Ha0.
    (* [comment removed for export] *)
    stepb_tk F_14944 D_14944 ltac:(rewrite Ha0; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepn F_148c4 D_148c4. rewrite Hs1, Hs3. rewrite (v_add_ZZ buf len) by lia.
    stepn F_148c8 D_148c8. rewrite Hs6.
    stepn F_148cc D_148cc.
    stepn F_148d0 D_148d0.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia). all: kept_list loopB_kept.
Qed.

(* [comment removed for export] *)
Lemma walkB2 {RCa1 : RunCtx}  : forall regs mem rom (buf len n cap : Z),
  getr regs 19 = Z_to_bv 64 len -> getr regs 23 = Z_to_bv 64 n -> getr regs 9 = Z_to_bv 64 buf ->
  getr regs 21 = Z_to_bv 64 cap ->
  (0 <= len)%Z -> (0 < n)%Z -> (len + n < cap)%Z -> (cap <= 2 ^ 40)%Z ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1497c : word) mem rom) (mkst regs' (0x149c8 : word) mem rom)
    /\ getr regs' 19 = Z_to_bv 64 (len + n) /\ getr regs' 23 = Z_to_bv 64 buf /\ getr regs' 9 = Z_to_bv 64 buf
    /\ (forall r, In r (1 :: 2 :: loop_kept)%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom buf len n cap Hs3 Hs7 Hs1 Hs5 Hlen Hn Hlc Hcap.
  eexists. split.
  - (* [comment removed for export] *)
    stepn F_148d4 D_148d4. rewrite Hs7, Hs3. rewrite (v_add_ZZ n len) by lia.
    (* [comment removed for export] *)
    stepn F_148d8 D_148d8. rewrite Hs1.
    (* [comment removed for export] *)
    stepb_ft F_148dc D_148dc ltac:(rewrite Hs5; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepn F_148e0 D_148e0.
    stepn F_148e4 D_148e4.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try (f_equal; lia). all: kept_list loop_kept.
Qed.

(* [comment removed for export] *)
Lemma walkB2F {RCa1 : RunCtx}  : forall regs mem rom (buf len n cap : Z),
  getr regs 19 = Z_to_bv 64 len -> getr regs 23 = Z_to_bv 64 n -> getr regs 9 = Z_to_bv 64 buf ->
  getr regs 21 = Z_to_bv 64 cap ->
  (0 <= len)%Z -> (0 < n)%Z -> (len + n = cap)%Z -> (cap <= 2 ^ 40)%Z ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1497c : word) mem rom) (mkst regs' (0x14990 : word) mem rom)
    /\ getr regs' 19 = Z_to_bv 64 cap /\ getr regs' 23 = Z_to_bv 64 buf /\ getr regs' 9 = Z_to_bv 64 buf
    /\ (forall r, In r (1 :: 2 :: loop_kept)%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom buf len n cap Hs3 Hs7 Hs1 Hs5 Hlen Hn Hlc Hcap.
  eexists. split.
  - stepn F_148d4 D_148d4. rewrite Hs7, Hs3. rewrite (v_add_ZZ n len) by lia.
    stepn F_148d8 D_148d8. rewrite Hs1.
    (* [comment removed for export] *)
    stepb_tk F_148dc D_148dc ltac:(rewrite Hs5; rewrite c_eq_Z by lia; apply Z.eqb_eq; lia).
    apply mst_refl.
  - rewrite <- Hlc. repeat split; gres; try reflexivity; try assumption; try (f_equal; lia). all: kept_list loop_kept.
Qed.

(* [comment removed for export] *)
Lemma walkBC {RCa1 : RunCtx}  : forall regs mem rom (sp0 buf len : Z),
  getr regs 1 = Z_to_bv 64 0x21e4c -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 0 ->
  getr regs 19 = Z_to_bv 64 len -> getr regs 9 = Z_to_bv 64 buf -> getr regs 20 = Z_to_bv 64 3 ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z -> (0 <= len < 2 ^ 63)%Z ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x149e4)) ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (sp0 - 136)) 8 = true ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x21da4 : word) mem rom)
                 (mkst regs' (0x21da0 : word)
                       (wbytes mem (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x149f8))) rom)
    /\ getr regs' 17 = Z_to_bv 64 57 /\ getr regs' 10 = Z_to_bv 64 3
    /\ getr regs' 1 = Z_to_bv 64 0x21df0 /\ getr regs' 2 = Z_to_bv 64 (sp0 - 144)
    /\ getr regs' 19 = Z_to_bv 64 len /\ getr regs' 23 = Z_to_bv 64 0
    /\ (forall r, In r loopB_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 buf len Hra Hsp Ha0 Hs3 Hs1 Hs4 SPlo SPhi Hlen RD SOK.
  eexists. split.
  - stepret F_21c4c D_21c4c (0x21e4c : word) ltac:(rewrite Hra; bveq).
    stepLD8 F_21cf4 D_21cf4 (Z_to_bv 64 0x149e4).
    stepn F_21cf8 D_21cf8. rewrite Hsp. sp_renorm.
    stepn F_21cfc D_21cfc.
    stepn F_1a438 D_1a438. stepn F_1a43c D_1a43c.
    stepb_tk F_1a440 D_1a440 ltac:(rewrite Ha0; cond_compute).
    stepret F_1a46c D_1a46c (0x149e4 : word) ltac:(bveq).
    stepb_ft F_1493c D_1493c ltac:(rewrite Ha0; cond_compute).
    (* [comment removed for export] *)
    stepn F_14940 D_14940. rewrite Ha0.
    (* [comment removed for export] *)
    stepb_ft F_14944 D_14944 ltac:(rewrite Ha0; cond_compute).
    (* [comment removed for export] *)
    stepn F_14948 D_14948. rewrite Hs4.
    stepn F_1494c D_1494c.
    (* [comment removed for export] *)
    stepn F_21c6c D_21c6c. sp_renorm.
    stepST F_21c70 D_21c70 (Z_to_bv 64 (sp0 - 136)) (Z_to_bv 64 0x149f8) ltac:(exact SOK).
    stepn F_21c74 D_21c74.
    stepret F_1c6fc D_1c6fc (0x21dd0 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_21c78 D_21c78. stepn F_21c7c D_21c7c. stepn F_21c80 D_21c80. stepn F_21c84 D_21c84.
    stepn F_21c88 D_21c88. stepn F_21c8c D_21c8c. stepn F_21c90 D_21c90. stepn F_21c94 D_21c94.
    stepn F_21c50 D_21c50.
    stepn F_21c2c D_21c2c. stepn F_21c30 D_21c30. stepn F_21c34 D_21c34. stepn F_21c38 D_21c38.
    stepn F_21c3c D_21c3c. stepn F_21c40 D_21c40. stepn F_21c44 D_21c44.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption. all: kept_list loopB_kept.
Qed.

(* [comment removed for export] *)
Lemma walkD {RCa1 : RunCtx}  : forall regs mem rom (sp0 : Z),
  getr regs 1 = Z_to_bv 64 0x21df0 -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 0 ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x149f8)) ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x21da4 : word) mem rom) (mkst regs' (0x149f8 : word) mem rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp0 - 128)
    /\ (forall r, In r (9 :: 19 :: 23 :: loopB_kept)%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 Hra Hsp Ha0 SPlo SPhi RD.
  eexists. split.
  - stepret F_21c4c D_21c4c (0x21df0 : word) ltac:(rewrite Hra; bveq).
    (* [comment removed for export] *)
    stepn F_21c98 D_21c98. rewrite Ha0. rewrite v_addiw_id by (u_norm; lia).
    stepn F_21c9c D_21c9c. stepn F_21ca0 D_21ca0. stepn F_21ca4 D_21ca4. stepn F_21ca8 D_21ca8.
    (* [comment removed for export] *)
    stepn F_21cac D_21cac.
    stepn F_1a438 D_1a438. stepn F_1a43c D_1a43c.
    stepb_tk F_1a440 D_1a440 ltac:(cond_compute).
    stepret F_1a46c D_1a46c (0x21e08 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_21cb0 D_21cb0.
    stepLD8 F_21cb4 D_21cb4 (Z_to_bv 64 0x149f8).
    stepn F_21cb8 D_21cb8. rewrite Hsp. sp_renorm.
    stepret F_21cbc D_21cbc (0x149f8 : word) ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia). all: kept_list loopB_kept.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S0ReadChunkW.

(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Hoare OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.WalkTac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Frame OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.MemSplit OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.LibMaskBits OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.SumWalkTac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.RefMemcpyLib OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.SpecConsts OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.SymExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.SymExec2 OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.SymExec2Sound OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.SymRun OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.SymDrive OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.SymDriveX OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.RefNodes OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.LibKnowFrame OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.RefReadLib OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U7MemcpyBase OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U7ReadBase OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U7ReadStage S0ReadChunkW.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.LiaFast.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac noncert_qtauto :=
  first [ solve [ repeat match goal with H : _ |- _ => clear H end; intuition fail ] | tauto ].
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

#[local] Abbreviation RSEGS := TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma dropz_dropz : forall (a b : Z) l, (0 <= a)%Z -> (0 <= b)%Z ->
  dropz a (dropz b l) = dropz (b + a) l.
Proof.
  intros a b l Ha Hb. unfold dropz. rewrite skipn_skipn. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma pref_chain : forall (len n m : Z) l, (0 <= len)%Z -> (0 <= n)%Z -> (0 <= m)%Z ->
  pref n (dropz len l) ++ pref m (dropz (len + n) l) = pref (n + m) (dropz len l).
Proof.
  intros len n m l Hl Hn Hm. rewrite <- (dropz_dropz n len) by lia. apply pref_app; lia.
Qed.

Lemma pref_0 : forall l, pref 0 l = [].
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma read_chunk : forall content (len want : Z),
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
  /\ getr R 20 = Z_to_bv 64 3 /\ getr R 21 = Z_to_bv 64 cap /\ getr R 22 = Z_to_bv 64 RS.

(* [comment removed for export] *)
Definition loop_post_regs (R R' : bvmap 5 word) (sp0 buf len' x7 : Z) : Prop :=
  getr R' 2 = Z_to_bv 64 (sp0 - 128) /\ getr R' 9 = Z_to_bv 64 buf /\ getr R' 23 = Z_to_bv 64 x7
  /\ getr R' 19 = Z_to_bv 64 len'
  /\ (forall r, In r loop_kept -> getr R' r = getr R r).

(* [comment removed for export] *)
Definition loop_post_mem {RCa1 : RunCtx}  (content : list byte) (M M' : word -> option byte) (sp0 buf len len' : Z) : Prop :=
  frame_mod M M' [(Z_to_bv 64 (sp0 - 136), 8%Z); (Z_to_bv 64 (buf + len), (len' - len)%Z); (Z_to_bv 64 RS, 65536%Z)]
  /\ rdn (run_segments RSEGS rc_inp rc_sp rc_mb) M' (Z_to_bv 64 (buf + len)) (Z.to_nat (len' - len)) = Some (pref (len' - len) (dropz len content)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma loop_kept_B : forall r, In r loop_kept -> In r loopB_kept.
Proof.
  intros r Hr. cbv [loop_kept In] in Hr. cbv [loopB_kept In].
  repeat (destruct Hr as [<-|Hr]; [noncert_qtauto|]). destruct Hr.
Qed.

Lemma loop_kept_callee : forall r, In r loop_kept -> In r callee_kept.
Proof.
  intros r Hr. cbv [loop_kept In] in Hr. cbv [callee_kept In].
  repeat (destruct Hr as [<-|Hr]; [noncert_qtauto|]). destruct Hr.
Qed.

(* [comment removed for export] *)

Lemma kept_regupd10 : forall X (v : word) r, In r loop_kept -> getr (regupd X 10 v) r = getr X r.
Proof.
  intros X v r Hr. cbv [loop_kept In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [rewrite getr_other by reg_neq_tac; reflexivity|]). destruct Hr.
Qed.

Lemma post_regs_compose : forall R R2 R' sp0 buf len' x7,
  loop_post_regs R2 R' sp0 buf len' x7 ->
  (forall r, In r loop_kept -> getr R2 r = getr R r) ->
  loop_post_regs R R' sp0 buf len' x7.
Proof.
  intros R R2 R' sp0 buf len' x7 (P2 & P9 & P23 & P19 & PK) HK.
  repeat split; try assumption. intros r Hr. rewrite (PK r Hr). apply HK, Hr.
Qed.

(* [comment removed for export] *)
Lemma frame_two : forall M (a1 a2 : word) bs1 bs2,
  (bv_unsigned a1 + Z.of_nat (length bs1) <= 2 ^ 64)%Z ->
  (bv_unsigned a2 + Z.of_nat (length bs2) <= 2 ^ 64)%Z ->
  frame_mod M (wbytes (wbytes M a1 bs1) a2 bs2) [(a1, Z.of_nat (length bs1)); (a2, Z.of_nat (length bs2))].
Proof.
  intros M a1 a2 bs1 bs2 H1 H2.
  change [(a1, Z.of_nat (length bs1)); (a2, Z.of_nat (length bs2))] with ([(a1, Z.of_nat (length bs1))] ++ [(a2, Z.of_nat (length bs2))]).
  eapply frame_mod_trans; apply frame_mod_wbytes; assumption.
Qed.

Lemma frame_three : forall M (a1 a2 a3 : word) bs1 bs2 bs3,
  (bv_unsigned a1 + Z.of_nat (length bs1) <= 2 ^ 64)%Z ->
  (bv_unsigned a2 + Z.of_nat (length bs2) <= 2 ^ 64)%Z ->
  (bv_unsigned a3 + Z.of_nat (length bs3) <= 2 ^ 64)%Z ->
  frame_mod M (wbytes (wbytes (wbytes M a1 bs1) a2 bs2) a3 bs3)
            [(a1, Z.of_nat (length bs1)); (a2, Z.of_nat (length bs2)); (a3, Z.of_nat (length bs3))].
Proof.
  intros M a1 a2 a3 bs1 bs2 bs3 H1 H2 H3.
  change [(a1, Z.of_nat (length bs1)); (a2, Z.of_nat (length bs2)); (a3, Z.of_nat (length bs3))]
    with ([(a1, Z.of_nat (length bs1)); (a2, Z.of_nat (length bs2))] ++ [(a3, Z.of_nat (length bs3))]).
  eapply frame_mod_trans; [apply frame_two; assumption | apply frame_mod_wbytes; assumption].
Qed.

Section PostAlgebra.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
  Variables (content : list byte) (M : word -> option byte) (sp0 buf len n : Z) (ra : word) (bs : list byte).
  Hypothesis Hlen : (0 <= len)%Z.
  Hypothesis Hn : (0 <= n <= 65536)%Z.
  Hypothesis Hbuf : (0x95000 <= buf)%Z.
  Hypothesis Hsp : (sp0 <= 2 ^ 63)%Z.
  Hypothesis Hbl : Z.of_nat (length bs) = n.
  Hypothesis Hbs : bs = pref n (dropz len content).

  (* [comment removed for export] *)
  #[local] Notation M3 := (wbytes (wbytes (wbytes M (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 ra)) (Z_to_bv 64 RS) bs) (Z_to_bv 64 (buf + len)) bs) (only parsing).

  (* [comment removed for export] *)
  Lemma post_mem_here : (buf + len + n <= sp0 - 144)%Z ->
    loop_post_mem content M M3 sp0 buf len (len + n).
  Proof.
    intros Hb. pose proof (length_N_to_le_bytes 8 ra) as L8. unfold loop_post_mem, RS. split.
    - eapply frame_mod_weaken; [|apply frame_three; rewrite ?L8, ?Hbl, u_small by lia; lia].
      intros a (O1 & O2 & O3 & _). cbn [outside]. rewrite L8, Hbl. replace (len + n - len)%Z with n in O2 by lia.
      unfold in_rng in *. rewrite !u_small in * by lia. repeat split; lia.
    - replace (len + n - len)%Z with n by lia. rewrite <- Hbs. replace (Z.to_nat n) with (length bs) by lia.
      apply rdn_wbytes_self. rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma post_mem_compose : forall M' (len' : Z),
    (len + n <= len')%Z -> (buf + len' <= sp0 - 144)%Z ->
    loop_post_mem content M3 M' sp0 buf (len + n) len' ->
    loop_post_mem content M M' sp0 buf len len'.
  Proof.
    intros M' len' Hl' Hb' [FR RD]. pose proof (length_N_to_le_bytes 8 ra) as L8. unfold loop_post_mem, RS in *. split.
    - eapply frame_mod_weaken.
      2: { eapply frame_mod_trans; [ | exact FR ]. apply frame_three; rewrite ?L8, ?Hbl, u_small by lia; lia. }
      intros a (O1 & O2 & O3 & _). cbn [outside app]. rewrite L8, Hbl. unfold in_rng in *. rewrite !u_small in * by lia.
      repeat split; lia.
    - replace (Z.to_nat (len' - len)) with (length bs + Z.to_nat (len' - (len + n)))%nat by lia.
      replace (pref (len' - len) (dropz len content)) with (bs ++ pref (len' - (len + n)) (dropz (len + n) content))
        by (rewrite Hbs at 1; rewrite pref_chain by lia; f_equal; lia).
      apply SeqExec.rdn_app.
      + rewrite (frame_mod_rdn (run_segments RSEGS rc_inp rc_sp rc_mb) M3 M' _ (length bs) (Z_to_bv 64 (buf + len)) FR).
        * apply rdn_wbytes_self. rewrite u_small by lia. lia.
        * intros i Hi. rewrite (u_small (buf + len)) by lia. cbn [outside]. unfold in_rng. rewrite ?Hbl, !u_small by lia. repeat split; lia.
        * rewrite u_small by lia. lia.
      + replace (Z_to_bv 64 (buf + len) + nat_to_word (length bs)) with (Z_to_bv 64 (buf + (len + n))); [exact RD|].
        unfold nat_to_word. apply bv_eq. rewrite bv_add_unsigned, !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia.
  Qed.
End PostAlgebra.

(* [comment removed for export] *)
Lemma post_mem_end {RCa1 : RunCtx}  : forall content M (sp0 buf len : Z) (ra1 ra2 : word),
  (0 <= len)%Z -> (len <= Z.of_nat (length content))%Z -> (sp0 <= 2 ^ 63)%Z -> (144 <= sp0)%Z ->
  (len = Z.of_nat (length content))%Z ->
  loop_post_mem content M
    (wbytes (wbytes M (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 ra1)) (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 ra2))
    sp0 buf len len.
Proof.
  intros content M sp0 buf len ra1 ra2 Hl HlL Hsp Hsp' HL.
  pose proof (length_N_to_le_bytes 8 ra1) as L1. pose proof (length_N_to_le_bytes 8 ra2) as L2. unfold loop_post_mem, RS. split.
  - eapply frame_mod_weaken; [|apply frame_two; rewrite ?L1, ?L2, u_small by lia; lia].
    intros a [O1 _]. cbn [outside]. rewrite L1, L2. noncert_qtauto.
  - rewrite Z.sub_diag. cbn [Z.to_nat rdn]. rewrite pref_0. reflexivity.
Qed.

Section ChunkLoop.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
  Variables (path content : list byte) (stdin0 : AmbIn) (fs0 : Fs) (tid : word) (V : VmMaps).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (U7ReadStage.modelG path stdin0 fs0 tid) (only parsing).

  (* [comment removed for export] *)
  Theorem chunk_loop_mid : forall (fuel : nat) (R : bvmap 5 word) (M : word -> option byte) (sp0 buf len cap : Z) (K : TSet),
    (cap - len <= Z.of_nat fuel)%Z ->
    mid_regs R sp0 buf len cap ->
    (0 <= len < cap)%Z -> (cap <= 2 ^ 40)%Z -> (0x95000 <= buf)%Z -> (buf + cap <= sp0 - 144)%Z ->
    (sp0 <= 2 ^ 47)%Z ->
    (len <= L)%Z ->
    store_ok (run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (sp0 - 136)) 8 = true ->
    store_ok (run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (buf + len)) (Z.to_nat (cap - len)) = true ->
    (* [comment removed for export] *)
    ((cap <= L)%Z -> forall R' M',
        loop_post_regs R R' sp0 buf cap buf -> loop_post_mem content M M' sp0 buf len cap ->
        realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst R' (Z_to_bv 64 0x14990) M' (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) (modelG cap V)) K) ->
    (* [comment removed for export] *)
    ((L < cap)%Z -> forall R' M',
        loop_post_regs R R' sp0 buf L 0 -> loop_post_mem content M M' sp0 buf len L ->
        realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst R' (Z_to_bv 64 0x149f8) M' (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) (model_post V stdin0 fs0 tid)) K) ->
    realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst R (Z_to_bv 64 0x149c8) M (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) (modelG len V)) K.
  Proof.
    induction fuel as [|fuel IH]; intros R M sp0 buf len cap K Hfuel (R2 & R9 & R19 & R20 & R21 & R22) Hlen Hcap Hbuf Hbc Hsp HlenL SOKs SOKb HFULL HEND.
    { exfalso. cbn in Hfuel. lia. }
    pose proof (want_range cap len Hlen) as [Hw1 Hw2].
    pose proof rw_bytes_max_ge16 as HRW.
    (* [comment removed for export] *)
    destruct (walkA R M (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp0 buf len cap R2 R19 R21 R9 R20 R22
               ltac:(lia) ltac:(lia) Hlen Hcap SOKs)
      as (R1 & RUN1 & A17 & A10 & A11 & A12 & A1 & A2 & A9 & A19 & AK0).
    assert (AK : forall r, In r loop_kept -> getr R1 r = getr R r) by (intros r Hr; apply AK0; right; exact Hr).
    replace (Z_to_bv 64 0x149c8) with (0x149c8 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [reflexivity | reflexivity | exact RUN1 |]. clear RUN1.
    set (M1 := wbytes M (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x149e4))).
    assert (SOK1s : store_ok (run_segments RSEGS rc_inp rc_sp rc_mb) M1 (Z_to_bv 64 (sp0 - 136)) 8 = true)
      by (eapply store_ok_mono; [apply wbytes_grows | exact SOKs]).
    assert (RD1 : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) M1 (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x149e4)))
      by (apply rdn_wbytes_hit8; rewrite u_small by lia; lia).
    (* [comment removed for export] *)
    pose proof (read_chunk content len (want cap len) ltac:(lia) ltac:(lia) ltac:(lia)) as RC. cbn zeta in RC.
    destruct RC as [RN RB].
    remember (file_read content (Z_to_bv 64 len) (Z_to_bv 64 (want cap len))) as bs eqn:Hbs.
    set (n := Z.of_nat (length bs)) in *.
    eapply (rz_read_file (run_segments RSEGS rc_inp rc_sp rc_mb) R1 (0x21da0 : word) M1 (modelG len V) W_21c48 (Z_to_bv 64 3) path (Z_to_bv 64 len) content (want cap len) K F_21c48 E_21c48).
    - reflexivity.
    - reflexivity.
    - exact A17.
    - exact A10.
    - rewrite u_small by lia. lia.
    - reflexivity.
    - exact Hfile.
    - exact A12.
    - lia.
    - lia.
    - lia.
    - rewrite A11. apply data_store_ok; unfold RS; lia.
    - rewrite A11. apply access_okb_true_intro_Z; [lia|]. unfold RS. rewrite u_small by lia. lia.
    - cbv zeta. rewrite A12, A11, <- Hbs. rewrite modelG_read.
      change (len_word bs) with (Z_to_bv 64 n).
      replace (Z_to_bv 64 len + Z_to_bv 64 n) with (Z_to_bv 64 (len + n))
        by (apply bv_eq; rewrite bv_add_unsigned, !u_small by lia; rewrite bv_wrap_small; [lia | unfold bv_modulus; lia]).
      change (mkModelA (fds_file path (Z_to_bv 64 (len + n))) V stdin0 fs0 None (Some tid) None) with (modelG (len + n) V).
      replace (v_addi (0x21da0 : word) 4) with (0x21da4 : word) by (apply bv_eq; reflexivity).
      set (M2 := wbytes M1 (Z_to_bv 64 RS) bs).
      destruct (Z.eq_dec n 0) as [Hn0|Hn0].
      + (* [comment removed for export] *)
        assert (bs = []) as Hnil by (destruct bs; [reflexivity | subst n; cbn in Hn0; lia]).
        assert (HLe : L = len) by lia.
        subst M2. rewrite Hnil. cbn [wbytes]. rewrite Hn0.
        destruct (walkBC (regupd R1 10 (Z_to_bv 64 0)) M1 (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp0 buf len
                   ltac:(gres; exact A1) ltac:(gres; exact A2) ltac:(gres; reflexivity)
                   ltac:(gres; exact A19) ltac:(gres; exact A9) ltac:(gres; rewrite (AK 20%bv) by (cbv; noncert_qtauto); exact R20)
                   ltac:(lia) ltac:(lia) ltac:(lia) RD1 SOK1s)
          as (R3 & RUN3 & C17 & C10 & C1 & C2 & C19 & C23 & CK).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN3 |]. clear RUN3.
        set (M3 := wbytes M1 (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x149f8))).
        (* [comment removed for export] *)
        eapply (rz_close (run_segments RSEGS rc_inp rc_sp rc_mb) R3 (0x21da0 : word) M3 (modelG (len + 0) V) W_21c48 (Z_to_bv 64 3) _ K F_21c48 E_21c48).
        * reflexivity.
        * reflexivity.
        * exact C17.
        * exact C10.
        * rewrite u_small by lia. lia.
        * reflexivity.
        * rewrite modelG_close.
          replace (v_addi (0x21da0 : word) 4) with (0x21da4 : word) by (apply bv_eq; reflexivity).
          destruct (walkD (regupd R3 10 (Z_to_bv 64 0)) M3 (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp0
                     ltac:(gres; exact C1) ltac:(gres; exact C2) ltac:(gres; reflexivity) ltac:(lia) ltac:(lia)
                     ltac:(subst M3; apply rdn_wbytes_hit8; rewrite u_small by lia; lia))
            as (R4 & RUN4 & D2 & DK).
          eapply rz_msteps; [reflexivity | reflexivity | exact RUN4 |]. clear RUN4.
          replace (0x149f8 : word) with (Z_to_bv 64 0x149f8) by (apply bv_eq; reflexivity).
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
        assert (RD2 : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) M2 (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x149e4))).
        { subst M2. unfold RS. rewrite rdn_wbytes_out; [exact RD1 | rewrite !u_small by lia; lia | rewrite u_small by lia; lia | rewrite u_small by lia; lia]. }
        destruct (walkB1 (regupd R1 10 (Z_to_bv 64 n)) M2 (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp0 buf len n
                   ltac:(gres; exact A1) ltac:(gres; exact A2) ltac:(gres; reflexivity)
                   ltac:(gres; exact A19) ltac:(gres; exact A9) ltac:(gres; rewrite (AK 22%bv) by (cbv; noncert_qtauto); exact R22)
                   ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) RD2)
          as (R2' & RUN2 & B1 & B2 & B10 & B11 & B12 & B23 & B19 & B9 & BK).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN2 |]. clear RUN2.
        assert (BKK : forall r, In r loop_kept -> getr R2' r = getr R r).
        { intros r Hr. rewrite (BK r (loop_kept_B r Hr)). rewrite (kept_regupd10 _ _ r Hr). apply AK, Hr. }
        (* [comment removed for export] *)
        assert (MC : mcH M2 (Z_to_bv 64 (buf + len)) (Z_to_bv 64 RS) n bs).
        { constructor.
          - lia.
          - lia.
          - subst M2. apply rdn_wbytes_self. unfold RS. rewrite u_small by lia. lia.
          - subst M2 M1. eapply store_ok_mono; [apply wbytes_grows|]. eapply store_ok_mono; [apply wbytes_grows|].
            eapply (store_ok_sub _ _ _ _ (Z.to_nat (cap - len))); [ | exact SOKb | | ]; rewrite ?u_small by lia; lia.
          - unfold RS. rewrite !u_small by lia. lia.
          - unfold RS. rewrite u_small by lia. lia.
          - rewrite u_small by lia. lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x1497c)) by (apply bv_eq; vm_compute; reflexivity).
        destruct (U7Memcpy.ref_memcpy M2 (Z_to_bv 64 (buf + len)) (Z_to_bv 64 RS) n bs (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) MC R2' (Z_to_bv 64 0x1497c)
                    RT ltac:(rewrite B1; apply bv_eq; reflexivity) B10 B11 B12) as (R3 & RUN3 & KP).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN3 |]. clear RUN3 RT.
        set (M3 := wbytes M2 (Z_to_bv 64 (buf + len)) bs).
        replace (Z_to_bv 64 0x1497c) with (0x1497c : word) by (apply bv_eq; reflexivity).
        assert (KPr : forall r, In r callee_kept -> getr R3 r = getr R2' r) by exact KP. clear KP.
        assert (C19 : getr R3 19 = Z_to_bv 64 len) by (rewrite (KPr 19%bv) by (cbv; noncert_qtauto); exact B19).
        assert (C23 : getr R3 23 = Z_to_bv 64 n) by (rewrite (KPr 23%bv) by (cbv; noncert_qtauto); exact B23).
        assert (C9 : getr R3 9 = Z_to_bv 64 buf) by (rewrite (KPr 9%bv) by (cbv; noncert_qtauto); exact B9).
        assert (C2 : getr R3 2 = Z_to_bv 64 (sp0 - 128)) by (rewrite (KPr 2%bv) by (cbv; noncert_qtauto); exact B2).
        assert (CKK : forall r, In r loop_kept -> getr R3 r = getr R r).
        { intros r Hr. rewrite (KPr r (loop_kept_callee r Hr)). apply BKK, Hr. }
        assert (C21 : getr R3 21 = Z_to_bv 64 cap) by (rewrite (CKK 21%bv) by (cbv; noncert_qtauto); exact R21).
        assert (GR3 : mem_grows M M3).
        { subst M3 M2 M1. eapply mem_grows_trans; [|apply wbytes_grows].
          eapply mem_grows_trans; [|apply wbytes_grows]. apply wbytes_grows. }
        destruct (Z.eq_dec (len + n) cap) as [Hfull|Hmore].
        * (* [comment removed for export] *)
          destruct (walkB2F R3 M3 (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) buf len n cap C19 C23 C9 C21 ltac:(lia) ltac:(lia) Hfull Hcap)
            as (R5 & RUN5 & F19 & F23 & F9 & FK).
          eapply rz_msteps; [reflexivity | reflexivity | exact RUN5 |]. clear RUN5.
          replace (0x14990 : word) with (Z_to_bv 64 0x14990) by (apply bv_eq; reflexivity).
          rewrite Hfull. apply (HFULL ltac:(lia) R5 M3).
          -- split; [rewrite (FK 2%bv) by (cbv; noncert_qtauto); exact C2|].
             split; [exact F9|]. split; [exact F23|]. split; [exact F19|].
             intros r Hr. rewrite (FK r) by (cbn [In]; right; right; exact Hr). apply CKK, Hr.
          -- subst M3 M2 M1. rewrite <- Hfull. apply post_mem_here; try lia. exact RB.
        * (* [comment removed for export] *)
          destruct (walkB2 R3 M3 (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) buf len n cap C19 C23 C9 C21 ltac:(lia) ltac:(lia) ltac:(lia) Hcap)
            as (R5 & RUN5 & E19 & E23 & E9 & EK).
          eapply rz_msteps; [reflexivity | reflexivity | exact RUN5 |]. clear RUN5.
          replace (0x149c8 : word) with (Z_to_bv 64 0x149c8) by (apply bv_eq; reflexivity).
          assert (EKK : forall r, In r loop_kept -> getr R5 r = getr R r).
          { intros r Hr. rewrite (EK r) by (cbn [In]; right; right; exact Hr). apply CKK, Hr. }
          apply (IH R5 M3 sp0 buf (len + n)%Z cap K ltac:(lia)).
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
          -- eapply store_ok_mono; [exact GR3 | exact SOKs].
          -- eapply store_ok_mono; [exact GR3 |].
             eapply (store_ok_sub _ _ _ _ (Z.to_nat (cap - len))); [ | exact SOKb | | ]; rewrite ?u_small by lia; lia.
          -- intros HcL R' M' PR PM. apply (HFULL HcL R' M').
             ++ eapply post_regs_compose; [exact PR | exact EKK].
             ++ subst M3 M2 M1. eapply post_mem_compose; [ | | | | | exact RB | | | exact PM]; lia.
          -- intros HLc R' M' PR PM. apply (HEND HLc R' M').
             ++ eapply post_regs_compose; [exact PR | exact EKK].
             ++ subst M3 M2 M1. eapply post_mem_compose; [ | | | | | exact RB | | | exact PM]; lia.
  Qed.
End ChunkLoop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma frame_mod_split2 : forall M M' (a1 : word) (n1 : Z) (a2 : word) (n2 : Z),
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
Lemma frame_mod_split3 : forall M M' (a1 : word) (n1 : Z) (a2 : word) (n2 : Z) (a3 : word) (n3 : Z),
  frame_mod M M' [(a1, n1); (a2, n2); (a3, n3)] ->
  exists Mm, frame_mod M Mm [(a1, n1)] /\ frame_mod Mm M' [(a2, n2); (a3, n3)].
Proof.
  intros M M' a1 n1 a2 n2 a3 n3 [EQ GR].
  exists (fun x => if in_rngb x a1 n1 then M' x else M x). split; split.
  - intros a [Ha _]. destruct (in_rngb a a1 n1) eqn:Hb; [|reflexivity].
    exfalso. apply Ha. apply in_rngb_spec. exact Hb.
  - intros x Hx. destruct (in_rngb x a1 n1); [apply GR, Hx | exact Hx].
  - intros a (Ha2 & Ha3 & _). destruct (in_rngb a a1 n1) eqn:Hb; [reflexivity|].
    apply EQ. cbn [outside]. split; [|split; [exact Ha2 | split; [exact Ha3 | exact I]]].
    intros Hin. apply in_rngb_spec in Hin. rewrite Hin in Hb. discriminate.
  - intros x Hx. destruct (in_rngb x a1 n1); [exact Hx | apply GR, Hx].
Qed.

(* [comment removed for export] *)
Lemma know_ok_frame2 {RCa1 : RunCtx}  : forall E M M' kn (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z),
  know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E M kn -> flat E (SA b1 k1) n1 -> flat E (SA b2 k2) n2 ->
  frame_mod M M' [(adenot E (SA b1 k1), n1); (adenot E (SA b2 k2), n2)] ->
  know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E M' (kn_frame (kn_frame kn b1 k1 n1) b2 k2 n2).
Proof.
  intros E M M' kn b1 k1 n1 b2 k2 n2 HK F1 F2 FR.
  destruct (frame_mod_split2 _ _ _ _ _ _ FR) as (Mm & [E1 G1] & [E2 G2]).
  pose proof (flat_u E _ _ F1) as U1. pose proof (flat_u E _ _ F2) as U2.
  eapply know_ok_frame; [eapply know_ok_frame; [exact HK | exact F1 | | exact G1] | exact F2 | | exact G2].
  - intros x Hx. apply E1. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite U1. lia.
  - intros x Hx. apply E2. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite U2. lia.
Qed.

(* [comment removed for export] *)
Lemma know_ok_frame3 {RCa1 : RunCtx}  : forall E M M' kn (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) (b3 : expr) (k3 n3 : Z),
  know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E M kn -> flat E (SA b1 k1) n1 -> flat E (SA b2 k2) n2 -> flat E (SA b3 k3) n3 ->
  frame_mod M M' [(adenot E (SA b1 k1), n1); (adenot E (SA b2 k2), n2); (adenot E (SA b3 k3), n3)] ->
  know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E M' (kn_frame (kn_frame (kn_frame kn b1 k1 n1) b2 k2 n2) b3 k3 n3).
Proof.
  intros E M M' kn b1 k1 n1 b2 k2 n2 b3 k3 n3 HK F1 F2 F3 FR.
  destruct (frame_mod_split3 _ _ _ _ _ _ _ _ FR) as (Mm & [E1 G1] & FR2).
  pose proof (flat_u E _ _ F1) as U1.
  apply (know_ok_frame2 E Mm M' _ b2 k2 n2 b3 k3 n3); [| exact F2 | exact F3 | exact FR2].
  eapply know_ok_frame; [exact HK | exact F1 | | exact G1].
  intros x Hx. apply E1. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite U1. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
