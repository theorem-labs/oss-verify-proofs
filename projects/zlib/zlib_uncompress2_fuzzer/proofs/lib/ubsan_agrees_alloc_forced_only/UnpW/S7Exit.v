(* reloc-zl14c *)
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
From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import SrcO_zlib_zlib_uncompress2_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require S7ExitBase.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require LiaFast.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg Nodes Spec LibWritev. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require S7StdioDefs S7StdioWrite.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require Import S7_code_146e4_15000 S7_code_18000_19000 S7_code_19000_1a000 S7_code_1a000_1b000 S7_code_1b000_1c000 S7_code_20000_20a30.   (* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
Module S0Exit_run1.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Hoare OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.WalkTac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StreamSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.MmapSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.LibAtomic OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S7ExitBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.LiaFast.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma rdn_wbytes_hit4 : forall segs m (a v : word),
  (bv_unsigned a + 4 <= 2^64)%Z ->
  rdn segs (wbytes m a (word_to_le_bytes 4 v)) a 4%nat = Some (word_to_le_bytes 4 v).
Proof.
  intros segs m a v Hnw.
  pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 v) m a) as H.
  rewrite length_N_to_le_bytes in H. apply H. exact Hnw.
Qed.

(* [comment removed for export] *)
Definition mem_w1 (mem : word -> option byte) (sp ra s0 : word) (tid : Z) :=
  wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 0x93220) (word_to_le_bytes 4 (Z_to_bv 64 tid)).

(* [comment removed for export] *)
Definition mem_foe (mem : word -> option byte) (sp code s1v s2v s3v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x19168)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3v).

(* [comment removed for export] *)
Definition mem_w1U (mem : word -> option byte) (sp ra s0 : word) (tid : Z) (code s1v s2v s3v : word) :=
  wbytes (mem_foe (mem_w1 mem sp ra s0 tid) sp code s1v s2v s3v)
    (Z_to_bv 64 0x93000) [Z_to_bv 8 1].

(* [comment removed for export] *)
Definition mem_w1R (mem : word -> option byte) (sp ra s0 : word) (tid : Z) (code s1v s2v s3v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (mem_foe (mem_w1 mem sp ra s0 tid) sp code s1v s2v s3v)
    (Z_to_bv 64 0x93008) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x93008) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x93008) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x93010) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x93000) [Z_to_bv 8 1].

(* [comment removed for export] *)
Lemma w1U {RCa1 : RunCtx}  : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x93220) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x9324b) 1%nat = Some [Z_to_bv 8 0] ->                                      (* [comment removed for export] *)
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x93010) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->          (* [comment removed for export] *)
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x93004) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->           (* [comment removed for export] *)
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x19104 : word) mem rom)
                 (mkst regs' (0x190b8 : word) (mem_w1U mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x1916c
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Mhead Malk.
  unfold mem_w1U, mem_foe, mem_w1. eexists. split.
  - (* [comment removed for export] *)
    stepn F_18f8c D_18f8c. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_18f90 D_18f90 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_18f94 D_18f94 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_18f98 D_18f98.
    stepn F_18f9c D_18f9c. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_18fa0 D_18fa0 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_18fa4 D_18fa4.
    stepn F_18fa8 D_18fa8.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_18fac | reflexivity | exact D_18fac
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_18fb0 | reflexivity | exact D_18fb0 | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_18fb4 | reflexivity | exact D_18fb4
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_18fb8 D_18fb8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_18fbc D_18fbc.
    (* [comment removed for export] *)
    stepb_ft F_18fc0 D_18fc0 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_18fc4 D_18fc4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_18fe8 D_18fe8. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_18fec D_18fec.
    (* [comment removed for export] *)
    stepn F_18da8 D_18da8. sp_renorm.
    stepST F_18dac D_18dac (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x19168) ltac:(sok_stack SOK).
    stepST F_18db0 D_18db0 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_18db4 D_18db4 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_18db8 D_18db8 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_18dbc D_18dbc (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_18dc0 D_18dc0. stepn F_18dc4 D_18dc4. stepn F_18dc8 D_18dc8. stepn F_18dcc D_18dcc. stepn F_18dd0 D_18dd0.
    (* [comment removed for export] *)
    stepn F_20660 D_20660.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_20664 | reflexivity | exact D_20664 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_20668 D_20668 ltac:(cond_compute).
    stepret F_20858 D_20858 (0x18f4c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_18dd4 D_18dd4 (Z_to_bv 64 0).
    stepb_tk F_18dd8 D_18dd8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_18e48 D_18e48.
    stepST F_18e4c D_18e4c (Z_to_bv 64 0x93000) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_18e50 D_18e50.
    (* [comment removed for export] *)
    stepLD8 F_18e54 D_18e54 (Z_to_bv 64 0x19168).
    stepLD8 F_18e58 D_18e58 code.
    stepLD8 F_18e5c D_18e5c (getr regs 9).
    stepLD8 F_18e60 D_18e60 (getr regs 18).
    stepLD8 F_18e64 D_18e64 (getr regs 19).
    stepn F_18e68 D_18e68. sp_renorm.
    stepn F_18e6c D_18e6c.
    (* [comment removed for export] *)
    stepLD F_208e8 D_208e8 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepb_ft F_208ec D_208ec ltac:(cond_compute).
    stepret F_208f0 D_208f0 (0x19168 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_18ff0 D_18ff0.
    apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.

(* [comment removed for export] *)
Lemma w1R {RCa1 : RunCtx}  : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x93220) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x9324b) 1%nat = Some [Z_to_bv 8 0] ->                                              (* [comment removed for export] *)
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x93010) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x93018)) ->     (* [comment removed for export] *)
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x93008) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->                   (* [comment removed for export] *)
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x93004) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->                   (* [comment removed for export] *)
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x93018) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->                  (* [comment removed for export] *)
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x93020) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x190b0)) ->            (* [comment removed for export] *)
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x93120) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x14cf4)) ->           (* [comment removed for export] *)
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x32ec4) 1%nat = Some [Z_to_bv 8 0] ->                                              (* [comment removed for export] *)
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x19104 : word) mem rom)
                 (mkst regs' (0x190b8 : word) (mem_w1R mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x1916c
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Mhead Mslot Malk Mnext Mf0 Ma0 Mincb.
  unfold mem_w1R, mem_foe, mem_w1. eexists. split.
  - (* [comment removed for export] *)
    stepn F_18f8c D_18f8c. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_18f90 D_18f90 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_18f94 D_18f94 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_18f98 D_18f98.
    stepn F_18f9c D_18f9c. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_18fa0 D_18fa0 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_18fa4 D_18fa4.
    stepn F_18fa8 D_18fa8.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_18fac | reflexivity | exact D_18fac
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_18fb0 | reflexivity | exact D_18fb0 | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_18fb4 | reflexivity | exact D_18fb4
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_18fb8 D_18fb8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_18fbc D_18fbc.
    (* [comment removed for export] *)
    stepb_ft F_18fc0 D_18fc0 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_18fc4 D_18fc4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_18fe8 D_18fe8. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_18fec D_18fec.
    (* [comment removed for export] *)
    stepn F_18da8 D_18da8. sp_renorm.
    stepST F_18dac D_18dac (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x19168) ltac:(sok_stack SOK).
    stepST F_18db0 D_18db0 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_18db4 D_18db4 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_18db8 D_18db8 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_18dbc D_18dbc (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_18dc0 D_18dc0. stepn F_18dc4 D_18dc4. stepn F_18dc8 D_18dc8. stepn F_18dcc D_18dcc. stepn F_18dd0 D_18dd0.
    (* [comment removed for export] *)
    stepn F_20660 D_20660.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_20664 | reflexivity | exact D_20664 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_20668 D_20668 ltac:(cond_compute).
    stepret F_20858 D_20858 (0x18f4c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_18dd4 D_18dd4 (Z_to_bv 64 0x93018).
    stepb_ft F_18dd8 D_18dd8 ltac:(cond_compute).
    stepLD F_18ddc D_18ddc (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 1) by lia.
    stepn F_18de0 D_18de0.
    (* [comment removed for export] *)
    stepn F_18df8 D_18df8.
    stepST F_18dfc D_18dfc (Z_to_bv 64 0x93008) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_18e00 D_18e00 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_18e04 D_18e04 (Z_to_bv 64 0x93018).
    stepn F_18e08 D_18e08. stepn F_18e0c D_18e0c.
    stepLD8 F_18e10 D_18e10 (Z_to_bv 64 0x190b0).
    stepLD8 F_18e14 D_18e14 (Z_to_bv 64 0x14cf4).
    (* [comment removed for export] *)
    stepn F_18e18 D_18e18. stepn F_18e1c D_18e1c.
    stepLD F_208e8 D_208e8 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepb_ft F_208ec D_208ec ltac:(cond_compute).
    stepret F_208f0 D_208f0 (0x18f98 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_18e20 D_18e20.
    stepjr F_18e24 D_18e24 (Z_to_bv 64 0x190b0) ltac:(gres; reflexivity). vnorm.
    stepjr F_18f38 D_18f38 (Z_to_bv 64 0x14cf4) ltac:(gres; reflexivity). vnorm.
    (* [comment removed for export] *)
    stepn F_14c58 D_14c58.
    stepLBU F_14c5c D_14c5c (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_14c60 D_14c60 ltac:(cond_compute).
    stepret F_14c64 D_14c64 (0x18fa0 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_18e28 D_18e28. stepn F_18e2c D_18e2c.
    stepn F_20660 D_20660.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_20664 | reflexivity | exact D_20664 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_20668 D_20668 ltac:(cond_compute).
    stepret F_20858 D_20858 (0x18fa8 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD F_18e30 D_18e30 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; apply rdn_wbytes_hit4; u_norm; lia) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepn F_18e34 D_18e34.
    stepST F_18e38 D_18e38 (Z_to_bv 64 0x93008) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_18e3c D_18e3c ltac:(cond_compute).
    stepLD8 F_18e40 D_18e40 (Z_to_bv 64 0x93018).
    stepn F_18e44 D_18e44.
    (* [comment removed for export] *)
    stepLD8 F_18de4 D_18de4 (Z_to_bv 64 0).
    stepn F_18de8 D_18de8.
    stepST F_18dec D_18dec (Z_to_bv 64 0x93008) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_18df0 D_18df0 (Z_to_bv 64 0x93010) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_18df4 D_18df4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_18e48 D_18e48.
    stepST F_18e4c D_18e4c (Z_to_bv 64 0x93000) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_18e50 D_18e50.
    (* [comment removed for export] *)
    stepLD8 F_18e54 D_18e54 (Z_to_bv 64 0x19168).
    stepLD8 F_18e58 D_18e58 code.
    stepLD8 F_18e5c D_18e5c (getr regs 9).
    stepLD8 F_18e60 D_18e60 (getr regs 18).
    stepLD8 F_18e64 D_18e64 (getr regs 19).
    stepn F_18e68 D_18e68. sp_renorm.
    stepn F_18e6c D_18e6c.
    (* [comment removed for export] *)
    stepLD F_208e8 D_208e8 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepb_ft F_208ec D_208ec ltac:(cond_compute).
    stepret F_208f0 D_208f0 (0x19168 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_18ff0 D_18ff0.
    apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.

(* [comment removed for export] *)
Definition mem_w2 (mem : word -> option byte) (sp code s1v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x1916c)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x190e8)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x21bb0)))
    (Z_to_bv 64 0x22eb8) [Z_to_bv 8 1].

Lemma w2 {RCa1 : RunCtx}  : forall regs mem rom (sp code s1v dso : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x1916c -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x21c50) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x21bb8)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x21c58) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x21bb0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x21bb0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1483c)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22eb8) 1%nat = Some [Z_to_bv 8 0] ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x21bf8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x18fe8)) ->     (* [comment removed for export] *)
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22c60) 8%nat = Some (word_to_le_bytes 8 dso) ->                    (* [comment removed for export] *)
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x21c00) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x190b8 : word) mem rom)
                 (mkst regs' (0x1b3c4 : word) (mem_w2 mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x19170
    /\ getr regs' 9 = s1v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof.
  intros regs mem rom sp code s1v dso Hsp Hs0 Hra Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mdso Mg2.
  unfold mem_w2. eexists. split.
  - (* [comment removed for export] *)
    stepn F_18f40 D_18f40. rewrite Hsp. sp_renorm.
    stepST F_18f44 D_18f44 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x1916c) ltac:(sok_stack SOK).
    stepST F_18f48 D_18f48 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_18f4c D_18f4c (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_18f50 D_18f50.
    stepn F_18f54 D_18f54.
    stepLD8 F_18f58 D_18f58 (Z_to_bv 64 0x21bb8).
    stepLD8 F_18f5c D_18f5c (Z_to_bv 64 0x21bb0).
    (* [comment removed for export] *)
    stepb_ft F_18f60 D_18f60 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_18f64 D_18f64 (Z_to_bv 64 0x1483c).
    stepn F_18f68 D_18f68.
    stepjr F_18f6c D_18f6c (Z_to_bv 64 0x1483c) ltac:(gres; reflexivity). vnorm.
    (* [comment removed for export] *)
    stepn F_147a0 D_147a0. sp_renorm.
    stepST F_147a4 D_147a4 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x190e8) ltac:(sok_stack SOK).
    stepST F_147a8 D_147a8 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x21bb0) ltac:(sok_stack SOK).
    stepn F_147ac D_147ac.
    stepn F_147b0 D_147b0.
    stepn F_147b4 D_147b4.
    (* [comment removed for export] *)
    stepLBU F_147b8 D_147b8 (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mcomp).
    stepn F_147bc D_147bc.
    stepb_tk F_147c0 D_147c0 ltac:(cond_compute).
    stepn F_147cc D_147cc.
    stepn F_147d0 D_147d0.
    stepn F_147d4 D_147d4.
    (* [comment removed for export] *)
    stepST F_147d8 D_147d8 (Z_to_bv 64 0x22eb8) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_147dc D_147dc.
    stepLD8 F_147e0 D_147e0 (Z_to_bv 64 0x18fe8).
    stepb_ft F_147e4 D_147e4 ltac:(cond_compute).
    stepn F_147e8 D_147e8.
    stepn F_147ec D_147ec. stepn F_147f0 D_147f0.
    stepLD8 F_147f4 D_147f4 dso.
    stepn F_147f8 D_147f8.
    stepret F_18e70 D_18e70 (0x14898 : word) ltac:(bveq).
    stepn F_147fc D_147fc.
    (* [comment removed for export] *)
    stepn F_14800 D_14800.
    stepLD8 F_14804 D_14804 (Z_to_bv 64 0).
    stepb_tk F_14808 D_14808 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_14820 D_14820 (Z_to_bv 64 0x190e8).
    stepLD8 F_14824 D_14824 (Z_to_bv 64 0x21bb0).
    stepn F_14828 D_14828. sp_renorm.
    stepret F_1482c D_1482c (0x190e8 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_18f70 D_18f70.
    stepb_ft F_18f74 D_18f74 ltac:(cond_compute).
    stepLD8 F_18f78 D_18f78 (Z_to_bv 64 0x1916c).
    stepLD8 F_18f7c D_18f7c code.
    stepLD8 F_18f80 D_18f80 s1v.
    stepn F_18f84 D_18f84. sp_renorm.
    (* [comment removed for export] *)
    stepn F_18f88 D_18f88.
    stepret F_18f3c D_18f3c (0x1916c : word) ltac:(bveq).
    stepn F_18ff4 D_18ff4.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S0Exit_run1.

(* [comment removed for export] *)
Module S0Exit_run2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Hoare OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.WalkTac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StreamSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.MmapSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.LibAtomic OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S7ExitBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.LiaFast.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition mem_w3a (mem : word -> option byte) (sp code : word) :=
  wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x19170)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x1b3d4)))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 code).

Lemma w3a {RCa1 : RunCtx}  : forall regs mem rom (sp code wp1 rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x19170 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  file_clean mem 0x22d78 wp1 rp1 ->
  file_clean mem 0x22c88 wp2 rp2 ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1b3c4 : word) mem rom)
                 (mkst regs' (0x19180 : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
  intros regs mem rom sp code wp1 rp1 wp2 rp2 Hsp Hs0 Hra SPlo SPhi SOK
         (Gnl & Gofl & Gin & Gout & Gerr)
         (F1l & F1wp & F1wb & F1rp & F1re) (F2l & F2wp & F2wb & F2rp & F2re).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  unfold mem_w3a. eexists. split.
  - (* [comment removed for export] *)
    stepn F_1b24c D_1b24c. rewrite Hsp. sp_renorm.
    stepST F_1b250 D_1b250 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x19170) ltac:(sok_stack SOK).
    stepST F_1b254 D_1b254 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_1b258 D_1b258.
    stepn F_1b3f0 D_1b3f0. sp_renorm.
    stepST F_1b3f4 D_1b3f4 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x1b3d4) ltac:(sok_stack SOK).
    stepST F_1b3f8 D_1b3f8 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_1b3fc D_1b3fc.
    stepn F_1b400 D_1b400.
    stepn F_1b404 D_1b404.
    (* [comment removed for export] *)
    stepn F_1b408 D_1b408.
    stepn F_20660 D_20660.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_20664 | reflexivity | exact D_20664 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_20668 D_20668 ltac:(cond_compute).
    stepret F_20858 D_20858 (0x1b584 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_1b40c D_1b40c.
    stepLD8 F_1b410 D_1b410 (Z_to_bv 64 0x1b3d4).
    stepLD8 F_1b414 D_1b414 code.
    stepn F_1b418 D_1b418. sp_renorm.
    stepret F_1b41c D_1b41c (0x1b3d4 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_1b25c D_1b25c (Z_to_bv 64 0).
    stepb_ft F_1b260 D_1b260 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_1b264 D_1b264.
    stepLD8 F_1b268 D_1b268 (Z_to_bv 64 0).
    stepb_tk F_1b26c D_1b26c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_1b2c0 D_1b2c0.
    stepLD8 F_1b2c4 D_1b2c4 (Z_to_bv 64 0x22d78).
    stepb_ft F_1b2c8 D_1b2c8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_1b2cc D_1b2cc (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_1b2d0 D_1b2d0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_1b2dc D_1b2dc wp1.
    stepLD8 F_1b2e0 D_1b2e0 wp1.
    stepb_tk F_1b2e4 D_1b2e4 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_1b2fc D_1b2fc rp1.
    stepLD8 F_1b300 D_1b300 rp1.
    stepb_tk F_1b304 D_1b304 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_1b31c D_1b31c.
    stepLD8 F_1b320 D_1b320 (Z_to_bv 64 0x22c88).
    stepb_ft F_1b324 D_1b324 ltac:(cond_compute).
    stepLD F_1b328 D_1b328 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_1b32c D_1b32c ltac:(cond_compute).
    stepLD8 F_1b338 D_1b338 wp2.
    stepLD8 F_1b33c D_1b33c wp2.
    stepb_tk F_1b340 D_1b340 ltac:(apply c_eq_refl).
    stepLD8 F_1b358 D_1b358 rp2.
    stepLD8 F_1b35c D_1b35c rp2.
    stepb_tk F_1b360 D_1b360 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_1b3e0 D_1b3e0 (Z_to_bv 64 0x19170).
    stepLD8 F_1b3e4 D_1b3e4 code.
    stepn F_1b3e8 D_1b3e8. sp_renorm.
    stepret F_1b3ec D_1b3ec (0x19170 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_18ff8 D_18ff8.
    stepn F_18ffc D_18ffc.
    stepn F_19000 D_19000.
    stepn F_19004 D_19004.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S0Exit_run2.

(* [comment removed for export] *)
Module S0Exit_run3.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Hoare OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.WalkTac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StreamSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.MmapSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.LibAtomic OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S7ExitBase S0Exit_run2.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.LiaFast.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition stdout_dirty_hdr {RCa1 : RunCtx}  (mem : word -> option byte) (wb wp : Z) : Prop :=
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x22d78 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x22d78 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp))
  /\ rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x22d78 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))
  /\ rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x22d78 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1b5d4)).

Lemma w3b1 {RCa1 : RunCtx}  : forall regs mem rom (sp code : word) (wb wp : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x19170 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  stdout_dirty_hdr mem wb wp ->
  (0 <= wb < 2^64)%Z -> (0 <= wp < 2^64)%Z -> wb <> wp ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1b3c4 : word) mem rom)
                 (mkst regs' (0x1b5d4 : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = Z_to_bv 64 0x22d78
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 1 = Z_to_bv 64 0x1b474
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 32)
    /\ getr regs' 8 = Z_to_bv 64 0x22d78
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4.
Proof.
  intros regs mem rom sp code wb wp Hsp Hs0 Hra SPlo SPhi SOK
         (Gnl & Gofl & Gin & Gout & Gerr) (F1l & F1wp & F1wb & F1wr) WB WP NE.
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1wr.
  unfold mem_w3a. eexists. split.
  - (* [comment removed for export] *)
    stepn F_1b24c D_1b24c. rewrite Hsp. sp_renorm.
    stepST F_1b250 D_1b250 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x19170) ltac:(sok_stack SOK).
    stepST F_1b254 D_1b254 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_1b258 D_1b258.
    stepn F_1b3f0 D_1b3f0. sp_renorm.
    stepST F_1b3f4 D_1b3f4 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x1b3d4) ltac:(sok_stack SOK).
    stepST F_1b3f8 D_1b3f8 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_1b3fc D_1b3fc.
    stepn F_1b400 D_1b400.
    stepn F_1b404 D_1b404.
    (* [comment removed for export] *)
    stepn F_1b408 D_1b408.
    stepn F_20660 D_20660.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_20664 | reflexivity | exact D_20664 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_20668 D_20668 ltac:(cond_compute).
    stepret F_20858 D_20858 (0x1b584 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_1b40c D_1b40c.
    stepLD8 F_1b410 D_1b410 (Z_to_bv 64 0x1b3d4).
    stepLD8 F_1b414 D_1b414 code.
    stepn F_1b418 D_1b418. sp_renorm.
    stepret F_1b41c D_1b41c (0x1b3d4 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_1b25c D_1b25c (Z_to_bv 64 0).
    stepb_ft F_1b260 D_1b260 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_1b264 D_1b264.
    stepLD8 F_1b268 D_1b268 (Z_to_bv 64 0).
    stepb_tk F_1b26c D_1b26c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_1b2c0 D_1b2c0.
    stepLD8 F_1b2c4 D_1b2c4 (Z_to_bv 64 0x22d78).
    stepb_ft F_1b2c8 D_1b2c8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_1b2cc D_1b2cc (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_1b2d0 D_1b2d0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_1b2dc D_1b2dc (Z_to_bv 64 wp).
    stepLD8 F_1b2e0 D_1b2e0 (Z_to_bv 64 wb).
    stepb_ft F_1b2e4 D_1b2e4 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepLD8 F_1b2e8 D_1b2e8 (Z_to_bv 64 0x1b5d4).
    stepn F_1b2ec D_1b2ec.
    stepn F_1b2f0 D_1b2f0.
    stepn F_1b2f4 D_1b2f4.
    stepjr F_1b2f8 D_1b2f8 (Z_to_bv 64 0x1b5d4) ltac:(gres; reflexivity). vnorm.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma w3b2 {RCa1 : RunCtx}  : forall regs mem rom (sp code rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 32) -> getr regs 8 = Z_to_bv 64 0x22d78 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x19170)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 32)) 8%nat = Some (word_to_le_bytes 8 code) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x22d78 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x22d78 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22d70) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x22c88)) ->
  file_clean mem 0x22c88 wp2 rp2 ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1b474 : word) mem rom)
                 (mkst regs' (0x19180 : word) mem rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
  intros regs mem rom sp code rp1 wp2 rp2 Hsp Hs0 SPlo SPhi M24 M32 F1rp F1re Gerr
         (F2l & F2wp & F2wb & F2rp & F2re).
  zaddr F1rp; zaddr F1re. zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_1b2fc D_1b2fc rp1.
    stepLD8 F_1b300 D_1b300 rp1.
    stepb_tk F_1b304 D_1b304 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_1b31c D_1b31c.
    stepLD8 F_1b320 D_1b320 (Z_to_bv 64 0x22c88).
    stepb_ft F_1b324 D_1b324 ltac:(cond_compute).
    stepLD F_1b328 D_1b328 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_1b32c D_1b32c ltac:(cond_compute).
    stepLD8 F_1b338 D_1b338 wp2.
    stepLD8 F_1b33c D_1b33c wp2.
    stepb_tk F_1b340 D_1b340 ltac:(apply c_eq_refl).
    stepLD8 F_1b358 D_1b358 rp2.
    stepLD8 F_1b35c D_1b35c rp2.
    stepb_tk F_1b360 D_1b360 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_1b3e0 D_1b3e0 (Z_to_bv 64 0x19170).
    stepLD8 F_1b3e4 D_1b3e4 code.
    stepn F_1b3e8 D_1b3e8. rewrite Hsp. sp_renorm.
    stepret F_1b3ec D_1b3ec (0x19170 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_18ff8 D_18ff8.
    stepn F_18ffc D_18ffc.
    stepn F_19000 D_19000.
    stepn F_19004 D_19004.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S0Exit_run3.

(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Hoare OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.WalkTac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StreamSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.MmapSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.LibAtomic OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.ExitSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Nodes OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.LibWritev OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S7StdioDefs S0Exit_run1 S0Exit_run2 S0Exit_run3 OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S7StdioWrite.S0StdioWrite_run1 OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S7StdioWrite.S0StdioWrite_run2 OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S7StdioWrite.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.LiaFast.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac zaddr_rec H := zaddr H.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem ref_exit_clean {RCa1 : RunCtx}  :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 wp1 rp1 : word),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  file_clean mem 0x22d78 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs (0x19104 : word) mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wp1 rp1 EC F1 Hh Hlazy.
  destruct EC. destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr). destruct ec_dso as [dso Mdso].
  destruct ec_atx as [(Ahead & Alock) | (Ahead & Aslot & Alock & Anext & Af0 & Aa0 & Aincb)].
  - (* [comment removed for export] *)
    (* [comment removed for export] *)
    destruct (w1U regs mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
      try assumption.
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
    (* [comment removed for export] *)
    destruct (w2 regs1 (mem_w1U mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp code (getr regs1 9) dso)
      as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
    all: try (unfold mem_w1U, mem_foe, mem_w1; first [store_ok_peel; exact ec_sok | rdn_solve]).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
    (* [comment removed for export] *)
    destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
    destruct F1 as (F1l & F1wp & F1wb & F1rp & F1re).
    zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
    zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
    destruct (w3a regs2 (mem_w2 (mem_w1U mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9))
                (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp code wp1 rp1 wp2 rp2)
      as (regs3 & RUN3 & R3a0 & R3a7 & R3sp); try assumption.
    1:{ unfold mem_w2, mem_w1U, mem_foe, mem_w1; store_ok_peel; exact ec_sok. }
    1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2, mem_w1U, mem_foe, mem_w1; rdn_solve. }
    1:{ repeat split; unfold mem_w2, mem_w1U, mem_foe, mem_w1; zaddr_goal; rdn_solve. }
    1:{ repeat split; unfold mem_w2, mem_w1U, mem_foe, mem_w1; zaddr_goal; rdn_solve. }
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
    (* [comment removed for export] *)
    eapply rz_exit_at; [exact F_19008 | exact E_19008 | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
  - (* [comment removed for export] *)
    (* [comment removed for export] *)
    destruct (w1R regs mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
      try assumption.
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
    (* [comment removed for export] *)
    destruct (w2 regs1 (mem_w1R mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp code (getr regs1 9) dso)
      as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
    all: try (unfold mem_w1R, mem_foe, mem_w1; first [store_ok_peel; exact ec_sok | rdn_solve]).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
    (* [comment removed for export] *)
    destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
    destruct F1 as (F1l & F1wp & F1wb & F1rp & F1re).
    zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
    zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
    destruct (w3a regs2 (mem_w2 (mem_w1R mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9))
                (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp code wp1 rp1 wp2 rp2)
      as (regs3 & RUN3 & R3a0 & R3a7 & R3sp); try assumption.
    1:{ unfold mem_w2, mem_w1R, mem_foe, mem_w1; store_ok_peel; exact ec_sok. }
    1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2, mem_w1R, mem_foe, mem_w1; rdn_solve. }
    1:{ repeat split; unfold mem_w2, mem_w1R, mem_foe, mem_w1; zaddr_goal; rdn_solve. }
    1:{ repeat split; unfold mem_w2, mem_w1R, mem_foe, mem_w1; zaddr_goal; rdn_solve. }
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
    (* [comment removed for export] *)
    eapply rz_exit_at; [exact F_19008 | exact E_19008 | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem ref_exit_flush {RCa1 : RunCtx}  :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  m_channel_reader model = true ->
  realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs (0x19104 : word) mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending EC SP Hh Hlazy Hfd Hrdr.
  destruct EC. destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr). destruct ec_dso as [dso Mdso].
  destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
  zaddr P1l; zaddr P1wp; zaddr P1wb; zaddr P1wr; zaddr P1buf; zaddr P1bsz; zaddr P1fd; zaddr P1rp; zaddr P1re.
  destruct ec_atx as [(Ahead & Alock) | (Ahead & Aslot & Alock & Anext & Af0 & Aa0 & Aincb)].
  - (* [comment removed for export] *)
    (* [comment removed for export] *)
    destruct (w1U regs mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
      try assumption.
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
    (* [comment removed for export] *)
    destruct (w2 regs1 (mem_w1U mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp code (getr regs1 9) dso)
      as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
    all: try (unfold mem_w1U, mem_foe, mem_w1; first [store_ok_peel; exact ec_sok | rdn_solve]).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
    (* [comment removed for export] *)
    destruct (w3b1 regs2 (mem_w2 (mem_w1U mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9))
                (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp code wb wp)
      as (regs3 & RUN3 & R3a0 & R3a1 & R3a2 & R3ra & R3sp & R3s0 & R3gp & R3tp); try assumption; try lia.
    1:{ unfold mem_w2, mem_w1U, mem_foe, mem_w1; store_ok_peel; exact ec_sok. }
    1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2, mem_w1U, mem_foe, mem_w1; rdn_solve. }
    1:{ repeat split; unfold mem_w2, mem_w1U, mem_foe, mem_w1; zaddr_goal; rdn_solve. }
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
    (* [comment removed for export] *)
    replace (Z_to_bv 64 0x1b474) with (0x1b474 : word) in R3ra by (apply bv_eq; reflexivity).
    unfold W. rewrite <- (app_nil_r pending).
    set (mem3 := mem_w3a (mem_w2 (mem_w1U mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9)) sp code).
    eapply (ref_stdio_write regs3 mem3 model (bv_unsigned sp - 32) 0x22d78 wb wp 1
              (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x1b474 : word) pending []);
      [ exact R3sp | exact R3a0 | exact R3a1 | exact R3a2 | exact R3ra
      | lia | lia
      | (* [comment removed for export] *)
        subst mem3; unfold mem_w3a, mem_w2, mem_w1U, mem_foe, mem_w1; sok_stack ec_sok
      | lia | lia
      | (* [comment removed for export] *) split; subst mem3; unfold mem_w3a, mem_w2, mem_w1U, mem_foe, mem_w1; zaddr_goal; rdn_solve
      | (* [comment removed for export] *) split; subst mem3; unfold mem_w3a, mem_w2, mem_w1U, mem_foe, mem_w1; rdn_solve
      | lia | exact Hfd | exact Hrdr | exact Hh | exact Hlazy
      | lia | lia | exact LEN
      | cbn [length]; u_norm; reflexivity
      | cbn [length]; lia
      | lia | u_norm; lia | u_norm; lia
      | unfold TASK_SIZE; lia | unfold TASK_SIZE; u_norm; lia
      | subst mem3; unfold mem_w3a, mem_w2, mem_w1U, mem_foe, mem_w1; repeat rdn_peel1; exact BYTES
      | reflexivity
      | apply ret_ok_even; reflexivity
      | apply t_emit_has_nil
      | ].
    intros regs4 mem4 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 POST.
      rewrite R3s0 in Q8.
      destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
      zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
      destruct (w3b2 regs4 mem4 (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp code rp1 wp2 rp2) as (regs5 & RUN5 & R5a0 & R5a7 & R5sp); try assumption.
      all: try (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2, mem_w1U, mem_foe, mem_w1; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]).
      1:{ repeat split; (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2, mem_w1U, mem_foe, mem_w1; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]). }
      eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN5 |]. clear RUN5.
      eapply rz_exit_at; [exact F_19008 | exact E_19008 | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
  - (* [comment removed for export] *)
    (* [comment removed for export] *)
    destruct (w1R regs mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
      try assumption.
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
    (* [comment removed for export] *)
    destruct (w2 regs1 (mem_w1R mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp code (getr regs1 9) dso)
      as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
    all: try (unfold mem_w1R, mem_foe, mem_w1; first [store_ok_peel; exact ec_sok | rdn_solve]).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
    (* [comment removed for export] *)
    destruct (w3b1 regs2 (mem_w2 (mem_w1R mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9))
                (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp code wb wp)
      as (regs3 & RUN3 & R3a0 & R3a1 & R3a2 & R3ra & R3sp & R3s0 & R3gp & R3tp); try assumption; try lia.
    1:{ unfold mem_w2, mem_w1R, mem_foe, mem_w1; store_ok_peel; exact ec_sok. }
    1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2, mem_w1R, mem_foe, mem_w1; rdn_solve. }
    1:{ repeat split; unfold mem_w2, mem_w1R, mem_foe, mem_w1; zaddr_goal; rdn_solve. }
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
    (* [comment removed for export] *)
    replace (Z_to_bv 64 0x1b474) with (0x1b474 : word) in R3ra by (apply bv_eq; reflexivity).
    unfold W. rewrite <- (app_nil_r pending).
    set (mem3 := mem_w3a (mem_w2 (mem_w1R mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9)) sp code).
    eapply (ref_stdio_write regs3 mem3 model (bv_unsigned sp - 32) 0x22d78 wb wp 1
              (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x1b474 : word) pending []);
      [ exact R3sp | exact R3a0 | exact R3a1 | exact R3a2 | exact R3ra
      | lia | lia
      | (* [comment removed for export] *)
        subst mem3; unfold mem_w3a, mem_w2, mem_w1R, mem_foe, mem_w1; sok_stack ec_sok
      | lia | lia
      | (* [comment removed for export] *) split; subst mem3; unfold mem_w3a, mem_w2, mem_w1R, mem_foe, mem_w1; zaddr_goal; rdn_solve
      | (* [comment removed for export] *) split; subst mem3; unfold mem_w3a, mem_w2, mem_w1R, mem_foe, mem_w1; rdn_solve
      | lia | exact Hfd | exact Hrdr | exact Hh | exact Hlazy
      | lia | lia | exact LEN
      | cbn [length]; u_norm; reflexivity
      | cbn [length]; lia
      | lia | u_norm; lia | u_norm; lia
      | unfold TASK_SIZE; lia | unfold TASK_SIZE; u_norm; lia
      | subst mem3; unfold mem_w3a, mem_w2, mem_w1R, mem_foe, mem_w1; repeat rdn_peel1; exact BYTES
      | reflexivity
      | apply ret_ok_even; reflexivity
      | apply t_emit_has_nil
      | ].
    intros regs4 mem4 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 POST.
      rewrite R3s0 in Q8.
      destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
      zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
      destruct (w3b2 regs4 mem4 (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp code rp1 wp2 rp2) as (regs5 & RUN5 & R5a0 & R5a7 & R5sp); try assumption.
      all: try (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2, mem_w1R, mem_foe, mem_w1; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]).
      1:{ repeat split; (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2, mem_w1R, mem_foe, mem_w1; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]). }
      eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN5 |]. clear RUN5.
      eapply rz_exit_at; [exact F_19008 | exact E_19008 | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma t_emit_nil_exit : forall code fs, t_eq (t_exit code fs) (t_emit [] (t_exit code fs)).
Proof.
  intros code fs. apply t_eq_sym. apply t_emit_nil_eq.
  unfold t_exit, t_emit. left. apply is_prefix_nil.
Qed.

Theorem ref_exit {RCa1 : RunCtx}  : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs (0x19104 : word) mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending (sp & tp & tid & wp2 & rp2 & EC & Hh & Hlazy & CASES).
  destruct CASES as [(-> & wp1 & rp1 & F1) | (wb & wp & bufp & bufsz & rp1 & can & SP & Hfd & Hrdr)].
  - eapply rz_conseq; [ | apply t_emit_nil_exit ].
    eapply ref_exit_clean; eassumption.
  - eapply ref_exit_flush; eassumption.
Qed.

(* [comment removed for export] *)
Corollary ref_exit_Z {RCa1 : RunCtx}  : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs (Z_to_bv 64 0x19104) mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros. replace (Z_to_bv 64 0x19104) with (0x19104 : word) by (apply bv_eq; reflexivity).
  apply ref_exit; assumption.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
