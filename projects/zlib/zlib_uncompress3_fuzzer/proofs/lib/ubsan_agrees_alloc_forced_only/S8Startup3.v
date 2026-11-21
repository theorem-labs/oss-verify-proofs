(* elf , front , img own, defs ,
   statements (TEMPLATE; synthesized from the run), context , conventions ;
   valtac4: 'reflexivity' from 'WalkTac.v stepld_pc value side; S0Startup2.v F_152d4'; split-rseq all. *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Src_zlib_zlib_uncompress3_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import StartupTac ArgvEnv RefLayout S8StartupDefs S8_code_18000_19000 S8_code_20000_20a98.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require L10Walk.
Ltac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac.chain_step ::= OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_chain_step.
Abbreviation SEGS := Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments.
Abbreviation RPH := Src_zlib_zlib_uncompress3_fuzzer_repro.M.phdrs.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma s2img_10040_4 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 65600) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 6)).
Proof. vm_refl_bv. Qed.
Lemma s2img_10050_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 65616) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 65600)).
Proof. vm_refl_bv. Qed.
Lemma s2img_10078_4 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 65656) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
Lemma s2img_100b0_4 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 65712) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
Lemma s2img_100e8_4 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 65768) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
Lemma s2img_10120_4 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 65824) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
Lemma s2img_10158_4 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 65880) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382482)).
Proof. vm_refl_bv. Qed.
Lemma s2img_10190_4 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 65936) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382480)).
Proof. vm_refl_bv. Qed.
Lemma s2img_101c8_4 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 65992) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382481)).
Proof. vm_refl_bv. Qed.
Lemma s2img_101f0_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 66032) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_10200_4 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 66048) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4)).
Proof. vm_refl_bv. Qed.
Lemma s2img_10238_4 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 66104) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1879048195)).
Proof. vm_refl_bv. Qed.
Lemma s2img_21bf0_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 138224) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_22e88_4 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 142984) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
Lemma s2img_92ff8_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 602104) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_93008_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 602120) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_93010_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 602128) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_93250_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 602704) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_93278_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 602744) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_93290_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 602768) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Section P4.
Variable sp0 : word.
Variable Jb : word -> option byte.
Variable inp : ProcInput.
Variables mbase brk : word.
#[local] Instance RC_a1_1 : RunCtx := mkRunCtx inp sp0 mbase.
Variable rdraw : EntryDraw.
Local Notation av := (in_argv inp) (only parsing).
Local Notation ev := (in_envp inp) (only parsing).
Local Notation uid := (in_uid inp) (only parsing).
Local Notation hw := (in_hwcap inp) (only parsing).
Local Notation gid := (in_gid inp) (only parsing).
Local Notation rseq := (kb_rseq (in_kernel inp)) (only parsing).
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.
Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH (Z_to_bv 64 (Z.of_N Src_zlib_zlib_uncompress3_fuzzer_repro.M.init_pc)) sp0 rdraw)) (only parsing).

  Lemma tls_c1 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word), wfJ sp0 Jb -> getr regs 1 = Z_to_bv 64 100992 -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) -> getr regs 3 = Z_to_bv 64 67584 -> getr regs 8 = pn_w inp rdraw -> getr regs 9 = s1v -> getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) -> getr regs 18 = Z_to_bv 64 602728 -> getr regs 19 = Z_to_bv 64 0 -> getr regs 20 = Z_to_bv 64 0 -> getr regs 21 = Z_to_bv 64 0 -> getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 0 -> getr regs 25 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 0 -> getr regs 27 = Z_to_bv 64 0 -> (forall regs', getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) -> getr regs' 3 = (Z_to_bv 64 67584) -> getr regs' 5 = (Z_to_bv 64 0) -> getr regs' 7 = (Z_to_bv 64 7) -> getr regs' 9 = (Z_to_bv 64 602728) -> getr regs' 10 = (Z_to_bv 64 56) -> getr regs' 11 = (Z_to_bv 64 602088) -> getr regs' 12 = (Z_to_bv 64 0) -> getr regs' 13 = (Z_to_bv 64 10) -> getr regs' 15 = (Z_to_bv 64 65600) -> getr regs' 16 = (Z_to_bv 64 6) -> getr regs' 17 = (Z_to_bv 64 0) -> getr regs' 22 = (Z_to_bv 64 0) -> getr regs' 23 = (Z_to_bv 64 0) -> getr regs' 24 = (Z_to_bv 64 0) -> getr regs' 25 = (Z_to_bv 64 0) -> getr regs' 26 = (Z_to_bv 64 0) -> getr regs' 27 = (Z_to_bv 64 0) -> getr regs' 28 = (Z_to_bv 64 1685382481) -> getr regs' 29 = (Z_to_bv 64 65600) -> getr regs' 30 = (Z_to_bv 64 131072) -> regs_agree (fun r => In r [2; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30]%list) regs regs' -> G (mkst regs' (0x18d18 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100992))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602728))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom)) -> G (mkst regs (0x18c90 : word) (CM (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (D_libc sp0 inp rdraw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { sv F_18b54 D_18b54 (Z_to_bv 64 (bv_unsigned sp0 - 480)).  (* 0x18c90 addi sp, sp, -0x40 *)
      stw TF_18c94 TD_18c94 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 100992) ltac:(ok_win HJ).  (* 0x18c94 sd ra, 0x38(sp) *)
      stw TF_18c98 TD_18c98 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w inp rdraw) ltac:(ok_win HJ).  (* 0x18c98 sd s0, 0x30(sp) *)
      stw TF_18c9c TD_18c9c (Z_to_bv 64 (bv_unsigned sp0 - 440)) (s1v) ltac:(ok_win HJ).  (* 0x18c9c sd s1, 0x28(sp) *)
      stw TF_18ca0 TD_18ca0 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 602728) ltac:(ok_win HJ).  (* 0x18ca0 sd s2, 0x20(sp) *)
      stw TF_18ca4 TD_18ca4 (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x18ca4 sd s3, 0x18(sp) *)
      stw TF_18ca8 TD_18ca8 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x18ca8 sd s4, 0x10(sp) *)
      stw TF_18cac TD_18cac (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x18cac sd s5, 0x8(sp) *)
      ld_step TF_18cb0 TD_18cb0 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18cb0 ld a3, 0x28(a0) *)
      sn TF_18cb4 TD_18cb4.  (* 0x18cb4 auipc a1, 0x7a *)
      sn TF_18cb8 TD_18cb8.  (* 0x18cb8 addi a1, a1, 0x334 *)
      sn TF_18cbc TD_18cbc.  (* 0x18cbc auipc a2, 0x7a *)
      sn TF_18cc0 TD_18cc0.  (* 0x18cc0 addi s1, a2, 0x5ac *)
      stepb_ft TF_18cc4 TD_18cc4 ltac:(pin; cond_compute).  (* 0x18cc4 beqz a3, 0x18da0 <static_init_tls+0x110> *)
      sn TF_18cc8 TD_18cc8.  (* 0x18cc8 li a2, 0x0 *)
      sn TF_18ccc TD_18ccc.  (* 0x18ccc li a7, 0x0 *)
      sn TF_18cd0 TD_18cd0.  (* 0x18cd0 auipc a4, 0xa *)
      ld_step TF_18cd4 TD_18cd4 (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18cd4 ld a5, 0x18(a0) *)
      ld_step TF_18cd8 TD_18cd8 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18cd8 ld a0, 0x20(a0) *)
      sn TF_18cdc TD_18cdc.  (* 0x18cdc li a6, 0x6 *)
      sn TF_18ce0 TD_18ce0.  (* 0x18ce0 auipc t0, 0x9 *)
      ld_step TF_18ce4 TD_18ce4 (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img s2img_22e88_4) ltac:(reflexivity).  (* 0x18ce4 lwu t5, 0x1b8(a4) *)
      ld_step TF_18ce8 TD_18ce8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_21bf0_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18ce8 ld t0, -0xf0(t0) *)
      sn TF_18cec TD_18cec.  (* 0x18cec li t1, 0x2 *)
      sn TF_18cf0 TD_18cf0.  (* 0x18cf0 li t2, 0x7 *)
      sn TF_18cf4 TD_18cf4.  (* 0x18cf4 lui t3, 0x6474e *)
      sn TF_18cf8 TD_18cf8.  (* 0x18cf8 addiw t3, t3, 0x551 *)
      sn TF_18cfc TD_18cfc.  (* 0x18cfc mv t4, a5 *)
      sn TF_18d00 TD_18d00.  (* 0x18d00 j 0x18d18 <static_init_tls+0x88> *)
      OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { sv F_18b54 D_18b54 (Z_to_bv 64 (bv_unsigned sp0 - 480)).  (* 0x18c90 addi sp, sp, -0x40 *)
      stw TF_18c94 TD_18c94 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 100992) ltac:(ok_win HJ).  (* 0x18c94 sd ra, 0x38(sp) *)
      stw TF_18c98 TD_18c98 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w inp rdraw) ltac:(ok_win HJ).  (* 0x18c98 sd s0, 0x30(sp) *)
      stw TF_18c9c TD_18c9c (Z_to_bv 64 (bv_unsigned sp0 - 440)) (s1v) ltac:(ok_win HJ).  (* 0x18c9c sd s1, 0x28(sp) *)
      stw TF_18ca0 TD_18ca0 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 602728) ltac:(ok_win HJ).  (* 0x18ca0 sd s2, 0x20(sp) *)
      stw TF_18ca4 TD_18ca4 (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x18ca4 sd s3, 0x18(sp) *)
      stw TF_18ca8 TD_18ca8 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x18ca8 sd s4, 0x10(sp) *)
      stw TF_18cac TD_18cac (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x18cac sd s5, 0x8(sp) *)
      ld_step TF_18cb0 TD_18cb0 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18cb0 ld a3, 0x28(a0) *)
      sn TF_18cb4 TD_18cb4.  (* 0x18cb4 auipc a1, 0x7a *)
      sn TF_18cb8 TD_18cb8.  (* 0x18cb8 addi a1, a1, 0x334 *)
      sn TF_18cbc TD_18cbc.  (* 0x18cbc auipc a2, 0x7a *)
      sn TF_18cc0 TD_18cc0.  (* 0x18cc0 addi s1, a2, 0x5ac *)
      stepb_ft TF_18cc4 TD_18cc4 ltac:(pin; cond_compute).  (* 0x18cc4 beqz a3, 0x18da0 <static_init_tls+0x110> *)
      sn TF_18cc8 TD_18cc8.  (* 0x18cc8 li a2, 0x0 *)
      sn TF_18ccc TD_18ccc.  (* 0x18ccc li a7, 0x0 *)
      sn TF_18cd0 TD_18cd0.  (* 0x18cd0 auipc a4, 0xa *)
      ld_step TF_18cd4 TD_18cd4 (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18cd4 ld a5, 0x18(a0) *)
      ld_step TF_18cd8 TD_18cd8 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18cd8 ld a0, 0x20(a0) *)
      sn TF_18cdc TD_18cdc.  (* 0x18cdc li a6, 0x6 *)
      sn TF_18ce0 TD_18ce0.  (* 0x18ce0 auipc t0, 0x9 *)
      ld_step TF_18ce4 TD_18ce4 (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img s2img_22e88_4) ltac:(reflexivity).  (* 0x18ce4 lwu t5, 0x1b8(a4) *)
      ld_step TF_18ce8 TD_18ce8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_21bf0_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18ce8 ld t0, -0xf0(t0) *)
      sn TF_18cec TD_18cec.  (* 0x18cec li t1, 0x2 *)
      sn TF_18cf0 TD_18cf0.  (* 0x18cf0 li t2, 0x7 *)
      sn TF_18cf4 TD_18cf4.  (* 0x18cf4 lui t3, 0x6474e *)
      sn TF_18cf8 TD_18cf8.  (* 0x18cf8 addiw t3, t3, 0x551 *)
      sn TF_18cfc TD_18cfc.  (* 0x18cfc mv t4, a5 *)
      sn TF_18d00 TD_18d00.  (* 0x18d00 j 0x18d18 <static_init_tls+0x88> *)
      OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma tls_c2 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word), wfJ sp0 Jb -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) -> getr regs 3 = Z_to_bv 64 67584 -> getr regs 5 = Z_to_bv 64 0 -> getr regs 7 = Z_to_bv 64 7 -> getr regs 9 = Z_to_bv 64 602728 -> getr regs 10 = Z_to_bv 64 56 -> getr regs 11 = Z_to_bv 64 602088 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 10 -> getr regs 15 = Z_to_bv 64 65600 -> getr regs 16 = Z_to_bv 64 6 -> getr regs 17 = Z_to_bv 64 0 -> getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 0 -> getr regs 25 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 0 -> getr regs 27 = Z_to_bv 64 0 -> getr regs 28 = Z_to_bv 64 1685382481 -> getr regs 29 = Z_to_bv 64 65600 -> getr regs 30 = Z_to_bv 64 131072 -> (forall regs', getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) -> getr regs' 3 = (Z_to_bv 64 67584) -> getr regs' 5 = (Z_to_bv 64 0) -> getr regs' 7 = (Z_to_bv 64 7) -> getr regs' 9 = (Z_to_bv 64 602728) -> getr regs' 10 = (Z_to_bv 64 56) -> getr regs' 11 = (Z_to_bv 64 602088) -> getr regs' 12 = (Z_to_bv 64 0) -> getr regs' 13 = (Z_to_bv 64 5) -> getr regs' 16 = (Z_to_bv 64 6) -> getr regs' 17 = (Z_to_bv 64 0) -> getr regs' 22 = (Z_to_bv 64 0) -> getr regs' 23 = (Z_to_bv 64 0) -> getr regs' 24 = (Z_to_bv 64 0) -> getr regs' 25 = (Z_to_bv 64 0) -> getr regs' 26 = (Z_to_bv 64 0) -> getr regs' 27 = (Z_to_bv 64 0) -> getr regs' 28 = (Z_to_bv 64 1685382481) -> getr regs' 29 = (Z_to_bv 64 65880) -> getr regs' 30 = (Z_to_bv 64 131072) -> regs_agree (fun r => In r [8; 12; 13; 17; 29; 31]%list) regs regs' -> G (mkst regs' (0x18d18 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100992))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602728))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom)) -> G (mkst regs (0x18d18 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100992))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602728))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H12 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { ld_step TF_18d18 TD_18d18 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img s2img_10040_4) ltac:(reflexivity).  (* 0x18d18 lw s0, 0x0(t4) *)
      stepb_tk TF_18d1c TD_18d1c ltac:(pin; cond_compute).  (* 0x18d1c beq s0, a6, 0x18d04 <static_init_tls+0x74> *)
      ld_step TF_18d04 TD_18d04 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img s2img_10050_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18d04 ld a2, 0x10(t4) *)
      sn TF_18d08 TD_18d08.  (* 0x18d08 sub a2, a5, a2 *)
      sn TF_18d0c TD_18d0c.  (* 0x18d0c addi a3, a3, -0x1 *)
      sn TF_18d10 TD_18d10.  (* 0x18d10 add t4, t4, a0 *)
      stepb_ft TF_18d14 TD_18d14 ltac:(pin; cond_compute).  (* 0x18d14 beqz a3, 0x18d68 <static_init_tls+0xd8> *)
      ld_step TF_18d18 TD_18d18 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_10078_4) ltac:(reflexivity).  (* 0x18d18 lw s0, 0x0(t4) *)
      stepb_ft TF_18d1c TD_18d1c ltac:(pin; cond_compute).  (* 0x18d1c beq s0, a6, 0x18d04 <static_init_tls+0x74> *)
      stepb_tk TF_18d20 TD_18d20 ltac:(pin; cond_compute).  (* 0x18d20 beqz t0, 0x18d34 <static_init_tls+0xa4> *)
      sn TF_18d34 TD_18d34.  (* 0x18d34 mv t6, t4 *)
      stepb_ft TF_18d38 TD_18d38 ltac:(pin; cond_compute).  (* 0x18d38 beq s0, t2, 0x18d40 <static_init_tls+0xb0> *)
      sn TF_18d3c TD_18d3c.  (* 0x18d3c mv t6, a7 *)
      stepb_tk TF_18d40 TD_18d40 ltac:(pin; cond_compute).  (* 0x18d40 bne s0, t3, 0x18d60 <static_init_tls+0xd0> *)
      sn TF_18d60 TD_18d60.  (* 0x18d60 mv a7, t6 *)
      sn TF_18d64 TD_18d64.  (* 0x18d64 j 0x18d0c <static_init_tls+0x7c> *)
      sn TF_18d0c TD_18d0c.  (* 0x18d0c addi a3, a3, -0x1 *)
      sn TF_18d10 TD_18d10.  (* 0x18d10 add t4, t4, a0 *)
      stepb_ft TF_18d14 TD_18d14 ltac:(pin; cond_compute).  (* 0x18d14 beqz a3, 0x18d68 <static_init_tls+0xd8> *)
      ld_step TF_18d18 TD_18d18 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_100b0_4) ltac:(reflexivity).  (* 0x18d18 lw s0, 0x0(t4) *)
      stepb_ft TF_18d1c TD_18d1c ltac:(pin; cond_compute).  (* 0x18d1c beq s0, a6, 0x18d04 <static_init_tls+0x74> *)
      stepb_tk TF_18d20 TD_18d20 ltac:(pin; cond_compute).  (* 0x18d20 beqz t0, 0x18d34 <static_init_tls+0xa4> *)
      sn TF_18d34 TD_18d34.  (* 0x18d34 mv t6, t4 *)
      stepb_ft TF_18d38 TD_18d38 ltac:(pin; cond_compute).  (* 0x18d38 beq s0, t2, 0x18d40 <static_init_tls+0xb0> *)
      sn TF_18d3c TD_18d3c.  (* 0x18d3c mv t6, a7 *)
      stepb_tk TF_18d40 TD_18d40 ltac:(pin; cond_compute).  (* 0x18d40 bne s0, t3, 0x18d60 <static_init_tls+0xd0> *)
      sn TF_18d60 TD_18d60.  (* 0x18d60 mv a7, t6 *)
      sn TF_18d64 TD_18d64.  (* 0x18d64 j 0x18d0c <static_init_tls+0x7c> *)
      sn TF_18d0c TD_18d0c.  (* 0x18d0c addi a3, a3, -0x1 *)
      sn TF_18d10 TD_18d10.  (* 0x18d10 add t4, t4, a0 *)
      stepb_ft TF_18d14 TD_18d14 ltac:(pin; cond_compute).  (* 0x18d14 beqz a3, 0x18d68 <static_init_tls+0xd8> *)
      ld_step TF_18d18 TD_18d18 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_100e8_4) ltac:(reflexivity).  (* 0x18d18 lw s0, 0x0(t4) *)
      stepb_ft TF_18d1c TD_18d1c ltac:(pin; cond_compute).  (* 0x18d1c beq s0, a6, 0x18d04 <static_init_tls+0x74> *)
      stepb_tk TF_18d20 TD_18d20 ltac:(pin; cond_compute).  (* 0x18d20 beqz t0, 0x18d34 <static_init_tls+0xa4> *)
      sn TF_18d34 TD_18d34.  (* 0x18d34 mv t6, t4 *)
      stepb_ft TF_18d38 TD_18d38 ltac:(pin; cond_compute).  (* 0x18d38 beq s0, t2, 0x18d40 <static_init_tls+0xb0> *)
      sn TF_18d3c TD_18d3c.  (* 0x18d3c mv t6, a7 *)
      stepb_tk TF_18d40 TD_18d40 ltac:(pin; cond_compute).  (* 0x18d40 bne s0, t3, 0x18d60 <static_init_tls+0xd0> *)
      sn TF_18d60 TD_18d60.  (* 0x18d60 mv a7, t6 *)
      sn TF_18d64 TD_18d64.  (* 0x18d64 j 0x18d0c <static_init_tls+0x7c> *)
      sn TF_18d0c TD_18d0c.  (* 0x18d0c addi a3, a3, -0x1 *)
      sn TF_18d10 TD_18d10.  (* 0x18d10 add t4, t4, a0 *)
      stepb_ft TF_18d14 TD_18d14 ltac:(pin; cond_compute).  (* 0x18d14 beqz a3, 0x18d68 <static_init_tls+0xd8> *)
      ld_step TF_18d18 TD_18d18 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_10120_4) ltac:(reflexivity).  (* 0x18d18 lw s0, 0x0(t4) *)
      stepb_ft TF_18d1c TD_18d1c ltac:(pin; cond_compute).  (* 0x18d1c beq s0, a6, 0x18d04 <static_init_tls+0x74> *)
      stepb_tk TF_18d20 TD_18d20 ltac:(pin; cond_compute).  (* 0x18d20 beqz t0, 0x18d34 <static_init_tls+0xa4> *)
      sn TF_18d34 TD_18d34.  (* 0x18d34 mv t6, t4 *)
      stepb_ft TF_18d38 TD_18d38 ltac:(pin; cond_compute).  (* 0x18d38 beq s0, t2, 0x18d40 <static_init_tls+0xb0> *)
      sn TF_18d3c TD_18d3c.  (* 0x18d3c mv t6, a7 *)
      stepb_tk TF_18d40 TD_18d40 ltac:(pin; cond_compute).  (* 0x18d40 bne s0, t3, 0x18d60 <static_init_tls+0xd0> *)
      sn TF_18d60 TD_18d60.  (* 0x18d60 mv a7, t6 *)
      sn TF_18d64 TD_18d64.  (* 0x18d64 j 0x18d0c <static_init_tls+0x7c> *)
      sn TF_18d0c TD_18d0c.  (* 0x18d0c addi a3, a3, -0x1 *)
      sn TF_18d10 TD_18d10.  (* 0x18d10 add t4, t4, a0 *)
      stepb_ft TF_18d14 TD_18d14 ltac:(pin; cond_compute).  (* 0x18d14 beqz a3, 0x18d68 <static_init_tls+0xd8> *)
      OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { ld_step TF_18d18 TD_18d18 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img s2img_10040_4) ltac:(reflexivity).  (* 0x18d18 lw s0, 0x0(t4) *)
      stepb_tk TF_18d1c TD_18d1c ltac:(pin; cond_compute).  (* 0x18d1c beq s0, a6, 0x18d04 <static_init_tls+0x74> *)
      ld_step TF_18d04 TD_18d04 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img s2img_10050_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18d04 ld a2, 0x10(t4) *)
      sn TF_18d08 TD_18d08.  (* 0x18d08 sub a2, a5, a2 *)
      sn TF_18d0c TD_18d0c.  (* 0x18d0c addi a3, a3, -0x1 *)
      sn TF_18d10 TD_18d10.  (* 0x18d10 add t4, t4, a0 *)
      stepb_ft TF_18d14 TD_18d14 ltac:(pin; cond_compute).  (* 0x18d14 beqz a3, 0x18d68 <static_init_tls+0xd8> *)
      ld_step TF_18d18 TD_18d18 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_10078_4) ltac:(reflexivity).  (* 0x18d18 lw s0, 0x0(t4) *)
      stepb_ft TF_18d1c TD_18d1c ltac:(pin; cond_compute).  (* 0x18d1c beq s0, a6, 0x18d04 <static_init_tls+0x74> *)
      stepb_tk TF_18d20 TD_18d20 ltac:(pin; cond_compute).  (* 0x18d20 beqz t0, 0x18d34 <static_init_tls+0xa4> *)
      sn TF_18d34 TD_18d34.  (* 0x18d34 mv t6, t4 *)
      stepb_ft TF_18d38 TD_18d38 ltac:(pin; cond_compute).  (* 0x18d38 beq s0, t2, 0x18d40 <static_init_tls+0xb0> *)
      sn TF_18d3c TD_18d3c.  (* 0x18d3c mv t6, a7 *)
      stepb_tk TF_18d40 TD_18d40 ltac:(pin; cond_compute).  (* 0x18d40 bne s0, t3, 0x18d60 <static_init_tls+0xd0> *)
      sn TF_18d60 TD_18d60.  (* 0x18d60 mv a7, t6 *)
      sn TF_18d64 TD_18d64.  (* 0x18d64 j 0x18d0c <static_init_tls+0x7c> *)
      sn TF_18d0c TD_18d0c.  (* 0x18d0c addi a3, a3, -0x1 *)
      sn TF_18d10 TD_18d10.  (* 0x18d10 add t4, t4, a0 *)
      stepb_ft TF_18d14 TD_18d14 ltac:(pin; cond_compute).  (* 0x18d14 beqz a3, 0x18d68 <static_init_tls+0xd8> *)
      ld_step TF_18d18 TD_18d18 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_100b0_4) ltac:(reflexivity).  (* 0x18d18 lw s0, 0x0(t4) *)
      stepb_ft TF_18d1c TD_18d1c ltac:(pin; cond_compute).  (* 0x18d1c beq s0, a6, 0x18d04 <static_init_tls+0x74> *)
      stepb_tk TF_18d20 TD_18d20 ltac:(pin; cond_compute).  (* 0x18d20 beqz t0, 0x18d34 <static_init_tls+0xa4> *)
      sn TF_18d34 TD_18d34.  (* 0x18d34 mv t6, t4 *)
      stepb_ft TF_18d38 TD_18d38 ltac:(pin; cond_compute).  (* 0x18d38 beq s0, t2, 0x18d40 <static_init_tls+0xb0> *)
      sn TF_18d3c TD_18d3c.  (* 0x18d3c mv t6, a7 *)
      stepb_tk TF_18d40 TD_18d40 ltac:(pin; cond_compute).  (* 0x18d40 bne s0, t3, 0x18d60 <static_init_tls+0xd0> *)
      sn TF_18d60 TD_18d60.  (* 0x18d60 mv a7, t6 *)
      sn TF_18d64 TD_18d64.  (* 0x18d64 j 0x18d0c <static_init_tls+0x7c> *)
      sn TF_18d0c TD_18d0c.  (* 0x18d0c addi a3, a3, -0x1 *)
      sn TF_18d10 TD_18d10.  (* 0x18d10 add t4, t4, a0 *)
      stepb_ft TF_18d14 TD_18d14 ltac:(pin; cond_compute).  (* 0x18d14 beqz a3, 0x18d68 <static_init_tls+0xd8> *)
      ld_step TF_18d18 TD_18d18 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_100e8_4) ltac:(reflexivity).  (* 0x18d18 lw s0, 0x0(t4) *)
      stepb_ft TF_18d1c TD_18d1c ltac:(pin; cond_compute).  (* 0x18d1c beq s0, a6, 0x18d04 <static_init_tls+0x74> *)
      stepb_tk TF_18d20 TD_18d20 ltac:(pin; cond_compute).  (* 0x18d20 beqz t0, 0x18d34 <static_init_tls+0xa4> *)
      sn TF_18d34 TD_18d34.  (* 0x18d34 mv t6, t4 *)
      stepb_ft TF_18d38 TD_18d38 ltac:(pin; cond_compute).  (* 0x18d38 beq s0, t2, 0x18d40 <static_init_tls+0xb0> *)
      sn TF_18d3c TD_18d3c.  (* 0x18d3c mv t6, a7 *)
      stepb_tk TF_18d40 TD_18d40 ltac:(pin; cond_compute).  (* 0x18d40 bne s0, t3, 0x18d60 <static_init_tls+0xd0> *)
      sn TF_18d60 TD_18d60.  (* 0x18d60 mv a7, t6 *)
      sn TF_18d64 TD_18d64.  (* 0x18d64 j 0x18d0c <static_init_tls+0x7c> *)
      sn TF_18d0c TD_18d0c.  (* 0x18d0c addi a3, a3, -0x1 *)
      sn TF_18d10 TD_18d10.  (* 0x18d10 add t4, t4, a0 *)
      stepb_ft TF_18d14 TD_18d14 ltac:(pin; cond_compute).  (* 0x18d14 beqz a3, 0x18d68 <static_init_tls+0xd8> *)
      ld_step TF_18d18 TD_18d18 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_10120_4) ltac:(reflexivity).  (* 0x18d18 lw s0, 0x0(t4) *)
      stepb_ft TF_18d1c TD_18d1c ltac:(pin; cond_compute).  (* 0x18d1c beq s0, a6, 0x18d04 <static_init_tls+0x74> *)
      stepb_tk TF_18d20 TD_18d20 ltac:(pin; cond_compute).  (* 0x18d20 beqz t0, 0x18d34 <static_init_tls+0xa4> *)
      sn TF_18d34 TD_18d34.  (* 0x18d34 mv t6, t4 *)
      stepb_ft TF_18d38 TD_18d38 ltac:(pin; cond_compute).  (* 0x18d38 beq s0, t2, 0x18d40 <static_init_tls+0xb0> *)
      sn TF_18d3c TD_18d3c.  (* 0x18d3c mv t6, a7 *)
      stepb_tk TF_18d40 TD_18d40 ltac:(pin; cond_compute).  (* 0x18d40 bne s0, t3, 0x18d60 <static_init_tls+0xd0> *)
      sn TF_18d60 TD_18d60.  (* 0x18d60 mv a7, t6 *)
      sn TF_18d64 TD_18d64.  (* 0x18d64 j 0x18d0c <static_init_tls+0x7c> *)
      sn TF_18d0c TD_18d0c.  (* 0x18d0c addi a3, a3, -0x1 *)
      sn TF_18d10 TD_18d10.  (* 0x18d10 add t4, t4, a0 *)
      stepb_ft TF_18d14 TD_18d14 ltac:(pin; cond_compute).  (* 0x18d14 beqz a3, 0x18d68 <static_init_tls+0xd8> *)
      OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma tls_c3 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word), wfJ sp0 Jb -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) -> getr regs 3 = Z_to_bv 64 67584 -> getr regs 5 = Z_to_bv 64 0 -> getr regs 7 = Z_to_bv 64 7 -> getr regs 9 = Z_to_bv 64 602728 -> getr regs 10 = Z_to_bv 64 56 -> getr regs 11 = Z_to_bv 64 602088 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 5 -> getr regs 16 = Z_to_bv 64 6 -> getr regs 17 = Z_to_bv 64 0 -> getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 0 -> getr regs 25 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 0 -> getr regs 27 = Z_to_bv 64 0 -> getr regs 28 = Z_to_bv 64 1685382481 -> getr regs 29 = Z_to_bv 64 65880 -> getr regs 30 = Z_to_bv 64 131072 -> (forall regs', getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) -> getr regs' 3 = (Z_to_bv 64 67584) -> getr regs' 9 = (Z_to_bv 64 602728) -> getr regs' 11 = (Z_to_bv 64 602088) -> getr regs' 12 = (Z_to_bv 64 0) -> getr regs' 17 = (Z_to_bv 64 0) -> getr regs' 22 = (Z_to_bv 64 0) -> getr regs' 23 = (Z_to_bv 64 0) -> getr regs' 24 = (Z_to_bv 64 0) -> getr regs' 25 = (Z_to_bv 64 0) -> getr regs' 26 = (Z_to_bv 64 0) -> getr regs' 27 = (Z_to_bv 64 0) -> regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' -> G (mkst regs' (0x18d68 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100992))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602728))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom)) -> G (mkst regs (0x18d18 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100992))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602728))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H12 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { ld_step TF_18d18 TD_18d18 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img s2img_10158_4) ltac:(reflexivity).  (* 0x18d18 lw s0, 0x0(t4) *)
      stepb_ft TF_18d1c TD_18d1c ltac:(pin; cond_compute).  (* 0x18d1c beq s0, a6, 0x18d04 <static_init_tls+0x74> *)
      stepb_tk TF_18d20 TD_18d20 ltac:(pin; cond_compute).  (* 0x18d20 beqz t0, 0x18d34 <static_init_tls+0xa4> *)
      sn TF_18d34 TD_18d34.  (* 0x18d34 mv t6, t4 *)
      stepb_ft TF_18d38 TD_18d38 ltac:(pin; cond_compute).  (* 0x18d38 beq s0, t2, 0x18d40 <static_init_tls+0xb0> *)
      sn TF_18d3c TD_18d3c.  (* 0x18d3c mv t6, a7 *)
      stepb_tk TF_18d40 TD_18d40 ltac:(pin; cond_compute).  (* 0x18d40 bne s0, t3, 0x18d60 <static_init_tls+0xd0> *)
      sn TF_18d60 TD_18d60.  (* 0x18d60 mv a7, t6 *)
      sn TF_18d64 TD_18d64.  (* 0x18d64 j 0x18d0c <static_init_tls+0x7c> *)
      sn TF_18d0c TD_18d0c.  (* 0x18d0c addi a3, a3, -0x1 *)
      sn TF_18d10 TD_18d10.  (* 0x18d10 add t4, t4, a0 *)
      stepb_ft TF_18d14 TD_18d14 ltac:(pin; cond_compute).  (* 0x18d14 beqz a3, 0x18d68 <static_init_tls+0xd8> *)
      ld_step TF_18d18 TD_18d18 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img s2img_10190_4) ltac:(reflexivity).  (* 0x18d18 lw s0, 0x0(t4) *)
      stepb_ft TF_18d1c TD_18d1c ltac:(pin; cond_compute).  (* 0x18d1c beq s0, a6, 0x18d04 <static_init_tls+0x74> *)
      stepb_tk TF_18d20 TD_18d20 ltac:(pin; cond_compute).  (* 0x18d20 beqz t0, 0x18d34 <static_init_tls+0xa4> *)
      sn TF_18d34 TD_18d34.  (* 0x18d34 mv t6, t4 *)
      stepb_ft TF_18d38 TD_18d38 ltac:(pin; cond_compute).  (* 0x18d38 beq s0, t2, 0x18d40 <static_init_tls+0xb0> *)
      sn TF_18d3c TD_18d3c.  (* 0x18d3c mv t6, a7 *)
      stepb_tk TF_18d40 TD_18d40 ltac:(pin; cond_compute).  (* 0x18d40 bne s0, t3, 0x18d60 <static_init_tls+0xd0> *)
      sn TF_18d60 TD_18d60.  (* 0x18d60 mv a7, t6 *)
      sn TF_18d64 TD_18d64.  (* 0x18d64 j 0x18d0c <static_init_tls+0x7c> *)
      sn TF_18d0c TD_18d0c.  (* 0x18d0c addi a3, a3, -0x1 *)
      sn TF_18d10 TD_18d10.  (* 0x18d10 add t4, t4, a0 *)
      stepb_ft TF_18d14 TD_18d14 ltac:(pin; cond_compute).  (* 0x18d14 beqz a3, 0x18d68 <static_init_tls+0xd8> *)
      ld_step TF_18d18 TD_18d18 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img s2img_101c8_4) ltac:(reflexivity).  (* 0x18d18 lw s0, 0x0(t4) *)
      stepb_ft TF_18d1c TD_18d1c ltac:(pin; cond_compute).  (* 0x18d1c beq s0, a6, 0x18d04 <static_init_tls+0x74> *)
      stepb_tk TF_18d20 TD_18d20 ltac:(pin; cond_compute).  (* 0x18d20 beqz t0, 0x18d34 <static_init_tls+0xa4> *)
      sn TF_18d34 TD_18d34.  (* 0x18d34 mv t6, t4 *)
      stepb_ft TF_18d38 TD_18d38 ltac:(pin; cond_compute).  (* 0x18d38 beq s0, t2, 0x18d40 <static_init_tls+0xb0> *)
      sn TF_18d3c TD_18d3c.  (* 0x18d3c mv t6, a7 *)
      stepb_ft TF_18d40 TD_18d40 ltac:(pin; cond_compute).  (* 0x18d40 bne s0, t3, 0x18d60 <static_init_tls+0xd0> *)
      ld_step TF_18d44 TD_18d44 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_101f0_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18d44 ld a7, 0x28(t4) *)
      stepb_tk TF_18d48 TD_18d48 ltac:(pin; cond_compute).  (* 0x18d48 bgeu t5, a7, 0x18d60 <static_init_tls+0xd0> *)
      sn TF_18d60 TD_18d60.  (* 0x18d60 mv a7, t6 *)
      sn TF_18d64 TD_18d64.  (* 0x18d64 j 0x18d0c <static_init_tls+0x7c> *)
      sn TF_18d0c TD_18d0c.  (* 0x18d0c addi a3, a3, -0x1 *)
      sn TF_18d10 TD_18d10.  (* 0x18d10 add t4, t4, a0 *)
      stepb_ft TF_18d14 TD_18d14 ltac:(pin; cond_compute).  (* 0x18d14 beqz a3, 0x18d68 <static_init_tls+0xd8> *)
      ld_step TF_18d18 TD_18d18 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img s2img_10200_4) ltac:(reflexivity).  (* 0x18d18 lw s0, 0x0(t4) *)
      stepb_ft TF_18d1c TD_18d1c ltac:(pin; cond_compute).  (* 0x18d1c beq s0, a6, 0x18d04 <static_init_tls+0x74> *)
      stepb_tk TF_18d20 TD_18d20 ltac:(pin; cond_compute).  (* 0x18d20 beqz t0, 0x18d34 <static_init_tls+0xa4> *)
      sn TF_18d34 TD_18d34.  (* 0x18d34 mv t6, t4 *)
      stepb_ft TF_18d38 TD_18d38 ltac:(pin; cond_compute).  (* 0x18d38 beq s0, t2, 0x18d40 <static_init_tls+0xb0> *)
      sn TF_18d3c TD_18d3c.  (* 0x18d3c mv t6, a7 *)
      stepb_tk TF_18d40 TD_18d40 ltac:(pin; cond_compute).  (* 0x18d40 bne s0, t3, 0x18d60 <static_init_tls+0xd0> *)
      sn TF_18d60 TD_18d60.  (* 0x18d60 mv a7, t6 *)
      sn TF_18d64 TD_18d64.  (* 0x18d64 j 0x18d0c <static_init_tls+0x7c> *)
      sn TF_18d0c TD_18d0c.  (* 0x18d0c addi a3, a3, -0x1 *)
      sn TF_18d10 TD_18d10.  (* 0x18d10 add t4, t4, a0 *)
      stepb_ft TF_18d14 TD_18d14 ltac:(pin; cond_compute).  (* 0x18d14 beqz a3, 0x18d68 <static_init_tls+0xd8> *)
      ld_step TF_18d18 TD_18d18 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img s2img_10238_4) ltac:(reflexivity).  (* 0x18d18 lw s0, 0x0(t4) *)
      stepb_ft TF_18d1c TD_18d1c ltac:(pin; cond_compute).  (* 0x18d1c beq s0, a6, 0x18d04 <static_init_tls+0x74> *)
      stepb_tk TF_18d20 TD_18d20 ltac:(pin; cond_compute).  (* 0x18d20 beqz t0, 0x18d34 <static_init_tls+0xa4> *)
      sn TF_18d34 TD_18d34.  (* 0x18d34 mv t6, t4 *)
      stepb_ft TF_18d38 TD_18d38 ltac:(pin; cond_compute).  (* 0x18d38 beq s0, t2, 0x18d40 <static_init_tls+0xb0> *)
      sn TF_18d3c TD_18d3c.  (* 0x18d3c mv t6, a7 *)
      stepb_tk TF_18d40 TD_18d40 ltac:(pin; cond_compute).  (* 0x18d40 bne s0, t3, 0x18d60 <static_init_tls+0xd0> *)
      sn TF_18d60 TD_18d60.  (* 0x18d60 mv a7, t6 *)
      sn TF_18d64 TD_18d64.  (* 0x18d64 j 0x18d0c <static_init_tls+0x7c> *)
      sn TF_18d0c TD_18d0c.  (* 0x18d0c addi a3, a3, -0x1 *)
      sn TF_18d10 TD_18d10.  (* 0x18d10 add t4, t4, a0 *)
      stepb_tk TF_18d14 TD_18d14 ltac:(pin; cond_compute).  (* 0x18d14 beqz a3, 0x18d68 <static_init_tls+0xd8> *)
      OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { ld_step TF_18d18 TD_18d18 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img s2img_10158_4) ltac:(reflexivity).  (* 0x18d18 lw s0, 0x0(t4) *)
      stepb_ft TF_18d1c TD_18d1c ltac:(pin; cond_compute).  (* 0x18d1c beq s0, a6, 0x18d04 <static_init_tls+0x74> *)
      stepb_tk TF_18d20 TD_18d20 ltac:(pin; cond_compute).  (* 0x18d20 beqz t0, 0x18d34 <static_init_tls+0xa4> *)
      sn TF_18d34 TD_18d34.  (* 0x18d34 mv t6, t4 *)
      stepb_ft TF_18d38 TD_18d38 ltac:(pin; cond_compute).  (* 0x18d38 beq s0, t2, 0x18d40 <static_init_tls+0xb0> *)
      sn TF_18d3c TD_18d3c.  (* 0x18d3c mv t6, a7 *)
      stepb_tk TF_18d40 TD_18d40 ltac:(pin; cond_compute).  (* 0x18d40 bne s0, t3, 0x18d60 <static_init_tls+0xd0> *)
      sn TF_18d60 TD_18d60.  (* 0x18d60 mv a7, t6 *)
      sn TF_18d64 TD_18d64.  (* 0x18d64 j 0x18d0c <static_init_tls+0x7c> *)
      sn TF_18d0c TD_18d0c.  (* 0x18d0c addi a3, a3, -0x1 *)
      sn TF_18d10 TD_18d10.  (* 0x18d10 add t4, t4, a0 *)
      stepb_ft TF_18d14 TD_18d14 ltac:(pin; cond_compute).  (* 0x18d14 beqz a3, 0x18d68 <static_init_tls+0xd8> *)
      ld_step TF_18d18 TD_18d18 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img s2img_10190_4) ltac:(reflexivity).  (* 0x18d18 lw s0, 0x0(t4) *)
      stepb_ft TF_18d1c TD_18d1c ltac:(pin; cond_compute).  (* 0x18d1c beq s0, a6, 0x18d04 <static_init_tls+0x74> *)
      stepb_tk TF_18d20 TD_18d20 ltac:(pin; cond_compute).  (* 0x18d20 beqz t0, 0x18d34 <static_init_tls+0xa4> *)
      sn TF_18d34 TD_18d34.  (* 0x18d34 mv t6, t4 *)
      stepb_ft TF_18d38 TD_18d38 ltac:(pin; cond_compute).  (* 0x18d38 beq s0, t2, 0x18d40 <static_init_tls+0xb0> *)
      sn TF_18d3c TD_18d3c.  (* 0x18d3c mv t6, a7 *)
      stepb_tk TF_18d40 TD_18d40 ltac:(pin; cond_compute).  (* 0x18d40 bne s0, t3, 0x18d60 <static_init_tls+0xd0> *)
      sn TF_18d60 TD_18d60.  (* 0x18d60 mv a7, t6 *)
      sn TF_18d64 TD_18d64.  (* 0x18d64 j 0x18d0c <static_init_tls+0x7c> *)
      sn TF_18d0c TD_18d0c.  (* 0x18d0c addi a3, a3, -0x1 *)
      sn TF_18d10 TD_18d10.  (* 0x18d10 add t4, t4, a0 *)
      stepb_ft TF_18d14 TD_18d14 ltac:(pin; cond_compute).  (* 0x18d14 beqz a3, 0x18d68 <static_init_tls+0xd8> *)
      ld_step TF_18d18 TD_18d18 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img s2img_101c8_4) ltac:(reflexivity).  (* 0x18d18 lw s0, 0x0(t4) *)
      stepb_ft TF_18d1c TD_18d1c ltac:(pin; cond_compute).  (* 0x18d1c beq s0, a6, 0x18d04 <static_init_tls+0x74> *)
      stepb_tk TF_18d20 TD_18d20 ltac:(pin; cond_compute).  (* 0x18d20 beqz t0, 0x18d34 <static_init_tls+0xa4> *)
      sn TF_18d34 TD_18d34.  (* 0x18d34 mv t6, t4 *)
      stepb_ft TF_18d38 TD_18d38 ltac:(pin; cond_compute).  (* 0x18d38 beq s0, t2, 0x18d40 <static_init_tls+0xb0> *)
      sn TF_18d3c TD_18d3c.  (* 0x18d3c mv t6, a7 *)
      stepb_ft TF_18d40 TD_18d40 ltac:(pin; cond_compute).  (* 0x18d40 bne s0, t3, 0x18d60 <static_init_tls+0xd0> *)
      ld_step TF_18d44 TD_18d44 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_101f0_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18d44 ld a7, 0x28(t4) *)
      stepb_tk TF_18d48 TD_18d48 ltac:(pin; cond_compute).  (* 0x18d48 bgeu t5, a7, 0x18d60 <static_init_tls+0xd0> *)
      sn TF_18d60 TD_18d60.  (* 0x18d60 mv a7, t6 *)
      sn TF_18d64 TD_18d64.  (* 0x18d64 j 0x18d0c <static_init_tls+0x7c> *)
      sn TF_18d0c TD_18d0c.  (* 0x18d0c addi a3, a3, -0x1 *)
      sn TF_18d10 TD_18d10.  (* 0x18d10 add t4, t4, a0 *)
      stepb_ft TF_18d14 TD_18d14 ltac:(pin; cond_compute).  (* 0x18d14 beqz a3, 0x18d68 <static_init_tls+0xd8> *)
      ld_step TF_18d18 TD_18d18 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img s2img_10200_4) ltac:(reflexivity).  (* 0x18d18 lw s0, 0x0(t4) *)
      stepb_ft TF_18d1c TD_18d1c ltac:(pin; cond_compute).  (* 0x18d1c beq s0, a6, 0x18d04 <static_init_tls+0x74> *)
      stepb_tk TF_18d20 TD_18d20 ltac:(pin; cond_compute).  (* 0x18d20 beqz t0, 0x18d34 <static_init_tls+0xa4> *)
      sn TF_18d34 TD_18d34.  (* 0x18d34 mv t6, t4 *)
      stepb_ft TF_18d38 TD_18d38 ltac:(pin; cond_compute).  (* 0x18d38 beq s0, t2, 0x18d40 <static_init_tls+0xb0> *)
      sn TF_18d3c TD_18d3c.  (* 0x18d3c mv t6, a7 *)
      stepb_tk TF_18d40 TD_18d40 ltac:(pin; cond_compute).  (* 0x18d40 bne s0, t3, 0x18d60 <static_init_tls+0xd0> *)
      sn TF_18d60 TD_18d60.  (* 0x18d60 mv a7, t6 *)
      sn TF_18d64 TD_18d64.  (* 0x18d64 j 0x18d0c <static_init_tls+0x7c> *)
      sn TF_18d0c TD_18d0c.  (* 0x18d0c addi a3, a3, -0x1 *)
      sn TF_18d10 TD_18d10.  (* 0x18d10 add t4, t4, a0 *)
      stepb_ft TF_18d14 TD_18d14 ltac:(pin; cond_compute).  (* 0x18d14 beqz a3, 0x18d68 <static_init_tls+0xd8> *)
      ld_step TF_18d18 TD_18d18 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img s2img_10238_4) ltac:(reflexivity).  (* 0x18d18 lw s0, 0x0(t4) *)
      stepb_ft TF_18d1c TD_18d1c ltac:(pin; cond_compute).  (* 0x18d1c beq s0, a6, 0x18d04 <static_init_tls+0x74> *)
      stepb_tk TF_18d20 TD_18d20 ltac:(pin; cond_compute).  (* 0x18d20 beqz t0, 0x18d34 <static_init_tls+0xa4> *)
      sn TF_18d34 TD_18d34.  (* 0x18d34 mv t6, t4 *)
      stepb_ft TF_18d38 TD_18d38 ltac:(pin; cond_compute).  (* 0x18d38 beq s0, t2, 0x18d40 <static_init_tls+0xb0> *)
      sn TF_18d3c TD_18d3c.  (* 0x18d3c mv t6, a7 *)
      stepb_tk TF_18d40 TD_18d40 ltac:(pin; cond_compute).  (* 0x18d40 bne s0, t3, 0x18d60 <static_init_tls+0xd0> *)
      sn TF_18d60 TD_18d60.  (* 0x18d60 mv a7, t6 *)
      sn TF_18d64 TD_18d64.  (* 0x18d64 j 0x18d0c <static_init_tls+0x7c> *)
      sn TF_18d0c TD_18d0c.  (* 0x18d0c addi a3, a3, -0x1 *)
      sn TF_18d10 TD_18d10.  (* 0x18d10 add t4, t4, a0 *)
      stepb_tk TF_18d14 TD_18d14 ltac:(pin; cond_compute).  (* 0x18d14 beqz a3, 0x18d68 <static_init_tls+0xd8> *)
      OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma tls_c4 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word), wfJ sp0 Jb -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) -> getr regs 3 = Z_to_bv 64 67584 -> getr regs 9 = Z_to_bv 64 602728 -> getr regs 11 = Z_to_bv 64 602088 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 17 = Z_to_bv 64 0 -> getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 0 -> getr regs 25 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 0 -> getr regs 27 = Z_to_bv 64 0 -> (forall regs', getr regs' 1 = (Z_to_bv 64 102084) -> getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) -> getr regs' 3 = (Z_to_bv 64 67584) -> getr regs' 4 = (Z_to_bv 64 471008) -> getr regs' 8 = (Z_to_bv 64 471008) -> getr regs' 10 = (Z_to_bv 64 602088) -> getr regs' 11 = (Z_to_bv 64 602784) -> getr regs' 12 = (Z_to_bv 64 0) -> getr regs' 13 = (Z_to_bv 64 470800) -> getr regs' 14 = (Z_to_bv 64 0) -> getr regs' 15 = (Z_to_bv 64 18446744073709080608) -> getr regs' 17 = (Z_to_bv 64 96) -> getr regs' 18 = (Z_to_bv 64 470808) -> getr regs' 19 = (Z_to_bv 64 0) -> getr regs' 20 = (Z_to_bv 64 471024) -> getr regs' 22 = (Z_to_bv 64 0) -> getr regs' 23 = (Z_to_bv 64 0) -> getr regs' 24 = (Z_to_bv 64 0) -> getr regs' 25 = (Z_to_bv 64 0) -> getr regs' 26 = (Z_to_bv 64 0) -> getr regs' 27 = (Z_to_bv 64 0) -> regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' -> G (mkst regs' (0x18eec : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100992))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602728))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602120) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602136) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602128) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602752) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602760) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 471024) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 471000) (word_to_le_bytes 8 (Z_to_bv 64 471024))) (Z_to_bv 64 470808) (word_to_le_bytes 8 (Z_to_bv 64 470808))) (Z_to_bv 64 602728) ([Z_to_bv 8 1])) (Z_to_bv 64 470848) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) -> G (mkst regs (0x18d68 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100992))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602728))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H12 H17 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { stepb_tk TF_18d68 TD_18d68 ltac:(pin; cond_compute).  (* 0x18d68 beqz a7, 0x18da0 <static_init_tls+0x110> *)
      ld_step TF_18da0 TD_18da0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_92ff8_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18da0 ld a2, 0x10(a1) *)
      ld_step TF_18da4 TD_18da4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_93008_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18da4 ld a3, 0x20(a1) *)
      ld_step TF_18da8 TD_18da8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_93010_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18da8 ld a0, 0x28(a1) *)
      sn TF_18dac TD_18dac.  (* 0x18dac add a4, a3, a2 *)
      sn TF_18db0 TD_18db0.  (* 0x18db0 addi a5, a0, -0x1 *)
      sn TF_18db4 TD_18db4.  (* 0x18db4 neg a4, a4 *)
      sn TF_18db8 TD_18db8.  (* 0x18db8 and a2, a5, a2 *)
      sn TF_18dbc TD_18dbc.  (* 0x18dbc and a4, a5, a4 *)
      sn TF_18dc0 TD_18dc0.  (* 0x18dc0 li a5, 0x7 *)
      sn TF_18dc4 TD_18dc4.  (* 0x18dc4 add a3, a4, a3 *)
      stw TF_18dc8 TD_18dc8 (Z_to_bv 64 602120) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x18dc8 sd a3, 0x20(a1) *)
      stw TF_18dcc TD_18dcc (Z_to_bv 64 602136) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x18dcc sd a2, 0x30(a1) *)
      stepb_ft TF_18dd0 TD_18dd0 ltac:(pin; cond_compute).  (* 0x18dd0 bltu a5, a0, 0x18ddc <static_init_tls+0x14c> *)
      sn TF_18dd4 TD_18dd4.  (* 0x18dd4 li a0, 0x8 *)
      stw TF_18dd8 TD_18dd8 (Z_to_bv 64 602128) (Z_to_bv 64 8) ltac:(ok_data).  (* 0x18dd8 sd a0, 0x28(a1) *)
      sn TF_18ddc TD_18ddc.  (* 0x18ddc add a2, a2, a3 *)
      sn TF_18de0 TD_18de0.  (* 0x18de0 lui a1, 0x20 *)
      sn TF_18de4 TD_18de4.  (* 0x18de4 add a2, a2, a0 *)
      sn TF_18de8 TD_18de8.  (* 0x18de8 addiw a3, a1, 0xd1 *)
      sn TF_18dec TD_18dec.  (* 0x18dec addi a1, a2, 0xdf *)
      sn TF_18df0 TD_18df0.  (* 0x18df0 andi a1, a1, -0x8 *)
      stw TF_18df4 TD_18df4 (Z_to_bv 64 602752) (Z_to_bv 64 224) ltac:(ok_data).  (* 0x18df4 sd a1, 0x18(s1) *)
      stw TF_18df8 TD_18df8 (Z_to_bv 64 602760) (Z_to_bv 64 8) ltac:(ok_data).  (* 0x18df8 sd a0, 0x20(s1) *)
      stepb_tk TF_18dfc TD_18dfc ltac:(pin; cond_compute).  (* 0x18dfc bltu a1, a3, 0x18e30 <static_init_tls+0x1a0> *)
      sn TF_18e30 TD_18e30.  (* 0x18e30 auipc a3, 0x5a *)
      ld_step TF_18e34 TD_18e34 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_93278_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18e34 ld s3, 0x10(s1) *)
      ld_step TF_18e38 TD_18e38 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_93290_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18e38 ld a2, 0x28(s1) *)
      sn TF_18e3c TD_18e3c.  (* 0x18e3c addi a4, a0, -0x1 *)
      sn TF_18e40 TD_18e40.  (* 0x18e40 li a5, -0xc8 *)
      sn TF_18e44 TD_18e44.  (* 0x18e44 addi a0, a3, 0xe8 *)
      sn TF_18e48 TD_18e48.  (* 0x18e48 sub a5, a5, a0 *)
      sn TF_18e4c TD_18e4c.  (* 0x18e4c and a4, a4, a5 *)
      sn TF_18e50 TD_18e50.  (* 0x18e50 not a3, a2 *)
      sn TF_18e54 TD_18e54.  (* 0x18e54 add s2, a0, a4 *)
      sn TF_18e58 TD_18e58.  (* 0x18e58 slli a3, a3, 0x3 *)
      sn TF_18e5c TD_18e5c.  (* 0x18e5c add a3, a0, a3 *)
      sn TF_18e60 TD_18e60.  (* 0x18e60 add s4, a3, a1 *)
      sn TF_18e64 TD_18e64.  (* 0x18e64 addi s0, s2, 0xc8 *)
      stepb_tk TF_18e68 TD_18e68 ltac:(pin; cond_compute).  (* 0x18e68 beqz s3, 0x18eb0 <static_init_tls+0x220> *)
      stw TF_18eb0 TD_18eb0 (Z_to_bv 64 471024) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x18eb0 sd a2, 0x0(s4) *)
      stw TF_18eb4 TD_18eb4 (Z_to_bv 64 471000) (Z_to_bv 64 471024) ltac:(ok_data).  (* 0x18eb4 sd s4, 0xc0(s2) *)
      stw TF_18eb8 TD_18eb8 (Z_to_bv 64 470808) (Z_to_bv 64 470808) ltac:(ok_data).  (* 0x18eb8 sd s2, 0x0(s2) *)
      sn TF_18ebc TD_18ebc.  (* 0x18ebc mv a0, s0 *)
      sn TF_18ec0 TD_18ec0.  (* 0x18ec0 jal 0x20b1c <__set_thread_area> *)
      sn F_209ec D_209ec.  (* 0x20b1c mv tp, a0 *)
      sn F_209f0 D_209f0.  (* 0x20b20 li a0, 0x0 *)
      stepret F_209f4 D_209f4 (0x18ec4 : word) ltac:(pin; first [reflexivity | bveq]).  (* 0x20b24 ret *)
      stepb_ft TF_18ec4 TD_18ec4 ltac:(pin; cond_compute).  (* 0x18ec4 bltz a0, 0x18f18 <static_init_tls+0x288> *)
      stepb_ft TF_18ec8 TD_18ec8 ltac:(pin; cond_compute).  (* 0x18ec8 bnez a0, 0x18ed4 <static_init_tls+0x244> *)
      sn TF_18ecc TD_18ecc.  (* 0x18ecc li a0, 0x1 *)
      stw TF_18ed0 TD_18ed0 (Z_to_bv 64 602728) (Z_to_bv 64 1) ltac:(ok_data).  (* 0x18ed0 sb a0, 0x0(s1) *)
      sn TF_18ed4 TD_18ed4.  (* 0x18ed4 li a0, 0x2 *)
      sn TF_18ed8 TD_18ed8.  (* 0x18ed8 auipc a1, 0x7a *)
      stw TF_18edc TD_18edc (Z_to_bv 64 470848) (Z_to_bv 64 2) ltac:(ok_data).  (* 0x18edc sw a0, 0x28(s2) *)
      sn TF_18ee0 TD_18ee0.  (* 0x18ee0 li a7, 0x60 *)
      sn TF_18ee4 TD_18ee4.  (* 0x18ee4 addi a0, a1, 0x110 *)
      sn TF_18ee8 TD_18ee8.  (* 0x18ee8 addi a1, s1, 0x38 *)
      OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { stepb_tk TF_18d68 TD_18d68 ltac:(pin; cond_compute).  (* 0x18d68 beqz a7, 0x18da0 <static_init_tls+0x110> *)
      ld_step TF_18da0 TD_18da0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_92ff8_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18da0 ld a2, 0x10(a1) *)
      ld_step TF_18da4 TD_18da4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_93008_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18da4 ld a3, 0x20(a1) *)
      ld_step TF_18da8 TD_18da8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_93010_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18da8 ld a0, 0x28(a1) *)
      sn TF_18dac TD_18dac.  (* 0x18dac add a4, a3, a2 *)
      sn TF_18db0 TD_18db0.  (* 0x18db0 addi a5, a0, -0x1 *)
      sn TF_18db4 TD_18db4.  (* 0x18db4 neg a4, a4 *)
      sn TF_18db8 TD_18db8.  (* 0x18db8 and a2, a5, a2 *)
      sn TF_18dbc TD_18dbc.  (* 0x18dbc and a4, a5, a4 *)
      sn TF_18dc0 TD_18dc0.  (* 0x18dc0 li a5, 0x7 *)
      sn TF_18dc4 TD_18dc4.  (* 0x18dc4 add a3, a4, a3 *)
      stw TF_18dc8 TD_18dc8 (Z_to_bv 64 602120) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x18dc8 sd a3, 0x20(a1) *)
      stw TF_18dcc TD_18dcc (Z_to_bv 64 602136) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x18dcc sd a2, 0x30(a1) *)
      stepb_ft TF_18dd0 TD_18dd0 ltac:(pin; cond_compute).  (* 0x18dd0 bltu a5, a0, 0x18ddc <static_init_tls+0x14c> *)
      sn TF_18dd4 TD_18dd4.  (* 0x18dd4 li a0, 0x8 *)
      stw TF_18dd8 TD_18dd8 (Z_to_bv 64 602128) (Z_to_bv 64 8) ltac:(ok_data).  (* 0x18dd8 sd a0, 0x28(a1) *)
      sn TF_18ddc TD_18ddc.  (* 0x18ddc add a2, a2, a3 *)
      sn TF_18de0 TD_18de0.  (* 0x18de0 lui a1, 0x20 *)
      sn TF_18de4 TD_18de4.  (* 0x18de4 add a2, a2, a0 *)
      sn TF_18de8 TD_18de8.  (* 0x18de8 addiw a3, a1, 0xd1 *)
      sn TF_18dec TD_18dec.  (* 0x18dec addi a1, a2, 0xdf *)
      sn TF_18df0 TD_18df0.  (* 0x18df0 andi a1, a1, -0x8 *)
      stw TF_18df4 TD_18df4 (Z_to_bv 64 602752) (Z_to_bv 64 224) ltac:(ok_data).  (* 0x18df4 sd a1, 0x18(s1) *)
      stw TF_18df8 TD_18df8 (Z_to_bv 64 602760) (Z_to_bv 64 8) ltac:(ok_data).  (* 0x18df8 sd a0, 0x20(s1) *)
      stepb_tk TF_18dfc TD_18dfc ltac:(pin; cond_compute).  (* 0x18dfc bltu a1, a3, 0x18e30 <static_init_tls+0x1a0> *)
      sn TF_18e30 TD_18e30.  (* 0x18e30 auipc a3, 0x5a *)
      ld_step TF_18e34 TD_18e34 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_93278_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18e34 ld s3, 0x10(s1) *)
      ld_step TF_18e38 TD_18e38 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_93290_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18e38 ld a2, 0x28(s1) *)
      sn TF_18e3c TD_18e3c.  (* 0x18e3c addi a4, a0, -0x1 *)
      sn TF_18e40 TD_18e40.  (* 0x18e40 li a5, -0xc8 *)
      sn TF_18e44 TD_18e44.  (* 0x18e44 addi a0, a3, 0xe8 *)
      sn TF_18e48 TD_18e48.  (* 0x18e48 sub a5, a5, a0 *)
      sn TF_18e4c TD_18e4c.  (* 0x18e4c and a4, a4, a5 *)
      sn TF_18e50 TD_18e50.  (* 0x18e50 not a3, a2 *)
      sn TF_18e54 TD_18e54.  (* 0x18e54 add s2, a0, a4 *)
      sn TF_18e58 TD_18e58.  (* 0x18e58 slli a3, a3, 0x3 *)
      sn TF_18e5c TD_18e5c.  (* 0x18e5c add a3, a0, a3 *)
      sn TF_18e60 TD_18e60.  (* 0x18e60 add s4, a3, a1 *)
      sn TF_18e64 TD_18e64.  (* 0x18e64 addi s0, s2, 0xc8 *)
      stepb_tk TF_18e68 TD_18e68 ltac:(pin; cond_compute).  (* 0x18e68 beqz s3, 0x18eb0 <static_init_tls+0x220> *)
      stw TF_18eb0 TD_18eb0 (Z_to_bv 64 471024) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x18eb0 sd a2, 0x0(s4) *)
      stw TF_18eb4 TD_18eb4 (Z_to_bv 64 471000) (Z_to_bv 64 471024) ltac:(ok_data).  (* 0x18eb4 sd s4, 0xc0(s2) *)
      stw TF_18eb8 TD_18eb8 (Z_to_bv 64 470808) (Z_to_bv 64 470808) ltac:(ok_data).  (* 0x18eb8 sd s2, 0x0(s2) *)
      sn TF_18ebc TD_18ebc.  (* 0x18ebc mv a0, s0 *)
      sn TF_18ec0 TD_18ec0.  (* 0x18ec0 jal 0x20b1c <__set_thread_area> *)
      sn F_209ec D_209ec.  (* 0x20b1c mv tp, a0 *)
      sn F_209f0 D_209f0.  (* 0x20b20 li a0, 0x0 *)
      stepret F_209f4 D_209f4 (0x18ec4 : word) ltac:(pin; first [reflexivity | bveq]).  (* 0x20b24 ret *)
      stepb_ft TF_18ec4 TD_18ec4 ltac:(pin; cond_compute).  (* 0x18ec4 bltz a0, 0x18f18 <static_init_tls+0x288> *)
      stepb_ft TF_18ec8 TD_18ec8 ltac:(pin; cond_compute).  (* 0x18ec8 bnez a0, 0x18ed4 <static_init_tls+0x244> *)
      sn TF_18ecc TD_18ecc.  (* 0x18ecc li a0, 0x1 *)
      stw TF_18ed0 TD_18ed0 (Z_to_bv 64 602728) (Z_to_bv 64 1) ltac:(ok_data).  (* 0x18ed0 sb a0, 0x0(s1) *)
      sn TF_18ed4 TD_18ed4.  (* 0x18ed4 li a0, 0x2 *)
      sn TF_18ed8 TD_18ed8.  (* 0x18ed8 auipc a1, 0x7a *)
      stw TF_18edc TD_18edc (Z_to_bv 64 470848) (Z_to_bv 64 2) ltac:(ok_data).  (* 0x18edc sw a0, 0x28(s2) *)
      sn TF_18ee0 TD_18ee0.  (* 0x18ee0 li a7, 0x60 *)
      sn TF_18ee4 TD_18ee4.  (* 0x18ee4 addi a0, a1, 0x110 *)
      sn TF_18ee8 TD_18ee8.  (* 0x18ee8 addi a1, s1, 0x38 *)
      OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma tls_c5 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word), wfJ sp0 Jb -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) -> getr regs 3 = Z_to_bv 64 67584 -> getr regs 4 = Z_to_bv 64 471008 -> getr regs 10 = tid -> getr regs 11 = Z_to_bv 64 602784 -> getr regs 18 = Z_to_bv 64 470808 -> getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 0 -> getr regs 25 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 0 -> getr regs 27 = Z_to_bv 64 0 -> (forall regs', getr regs' 1 = (Z_to_bv 64 100992) -> getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) -> getr regs' 3 = (Z_to_bv 64 67584) -> getr regs' 4 = (Z_to_bv 64 471008) -> getr regs' 8 = (pn_w inp rdraw) -> getr regs' 9 = (s1v) -> getr regs' 10 = (Z_to_bv 64 0) -> getr regs' 12 = (Z_to_bv 64 470928) -> getr regs' 18 = (Z_to_bv 64 602728) -> getr regs' 19 = (Z_to_bv 64 0) -> getr regs' 20 = (Z_to_bv 64 0) -> getr regs' 21 = (Z_to_bv 64 0) -> getr regs' 22 = (Z_to_bv 64 0) -> getr regs' 23 = (Z_to_bv 64 0) -> getr regs' 24 = (Z_to_bv 64 0) -> getr regs' 25 = (Z_to_bv 64 0) -> getr regs' 26 = (Z_to_bv 64 0) -> getr regs' 27 = (Z_to_bv 64 0) -> regs_agree (fun r => In r [1; 2; 8; 9; 10; 12; 18; 19; 20; 21]%list) regs regs' -> G (mkst regs' (0x18a80 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100992))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602728))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602120) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602136) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602128) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602752) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602760) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 471024) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 471000) (word_to_le_bytes 8 (Z_to_bv 64 471024))) (Z_to_bv 64 470808) (word_to_le_bytes 8 (Z_to_bv 64 470808))) (Z_to_bv 64 602728) ([Z_to_bv 8 1])) (Z_to_bv 64 470848) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470840) (word_to_le_bytes 4 tid)) (Z_to_bv 64 470960) (word_to_le_bytes 8 (Z_to_bv 64 602784))) (Z_to_bv 64 470928) (word_to_le_bytes 8 (Z_to_bv 64 470928))) (Z_to_bv 64 470816) (word_to_le_bytes 8 (Z_to_bv 64 470808))) (Z_to_bv 64 470824) (word_to_le_bytes 8 (Z_to_bv 64 470808))) (Z_to_bv 64 470832) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) -> G (mkst regs (0x18ef0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100992))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602728))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602120) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602136) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602128) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602752) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602760) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 471024) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 471000) (word_to_le_bytes 8 (Z_to_bv 64 471024))) (Z_to_bv 64 470808) (word_to_le_bytes 8 (Z_to_bv 64 470808))) (Z_to_bv 64 602728) ([Z_to_bv 8 1])) (Z_to_bv 64 470848) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { sn TF_18ef0 TD_18ef0.  (* 0x18ef0 addi a2, s2, 0x78 *)
      stw TF_18ef4 TD_18ef4 (Z_to_bv 64 470840) (tid) ltac:(ok_data).  (* 0x18ef4 sw a0, 0x20(s2) *)
      stw TF_18ef8 TD_18ef8 (Z_to_bv 64 470960) (Z_to_bv 64 602784) ltac:(ok_data).  (* 0x18ef8 sd a1, 0x98(s2) *)
      stw TF_18efc TD_18efc (Z_to_bv 64 470928) (Z_to_bv 64 470928) ltac:(ok_data).  (* 0x18efc sd a2, 0x78(s2) *)
      sn TF_18f00 TD_18f00.  (* 0x18f00 auipc a0, 0x7a *)
      ld_step TF_18f04 TD_18f04 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_93250_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18f04 ld a0, 0x350(a0) *)
      stw TF_18f08 TD_18f08 (Z_to_bv 64 470816) (Z_to_bv 64 470808) ltac:(ok_data).  (* 0x18f08 sd s2, 0x8(s2) *)
      stw TF_18f0c TD_18f0c (Z_to_bv 64 470824) (Z_to_bv 64 470808) ltac:(ok_data).  (* 0x18f0c sd s2, 0x10(s2) *)
      stw TF_18f10 TD_18f10 (Z_to_bv 64 470832) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x18f10 sd a0, 0x18(s2) *)
      sn TF_18f14 TD_18f14.  (* 0x18f14 j 0x18f1c <static_init_tls+0x28c> *)
      ld_step TF_18f1c TD_18f1c (word_to_le_bytes 8 (Z_to_bv 64 100992)) (Z_to_bv 64 100992) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18f1c ld ra, 0x38(sp) *)
      ld_step TF_18f20 TD_18f20 (word_to_le_bytes 8 (pn_w inp rdraw)) (pn_w inp rdraw) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18f20 ld s0, 0x30(sp) *)
      ld_step TF_18f24 TD_18f24 (word_to_le_bytes 8 s1v) (s1v) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18f24 ld s1, 0x28(sp) *)
      ld_step TF_18f28 TD_18f28 (word_to_le_bytes 8 (Z_to_bv 64 602728)) (Z_to_bv 64 602728) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18f28 ld s2, 0x20(sp) *)
      ld_step TF_18f2c TD_18f2c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18f2c ld s3, 0x18(sp) *)
      ld_step TF_18f30 TD_18f30 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18f30 ld s4, 0x10(sp) *)
      ld_step TF_18f34 TD_18f34 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18f34 ld s5, 0x8(sp) *)
      sv TF_18f38 TD_18f38 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* 0x18f38 addi sp, sp, 0x40 *)
      stepret TF_18f3c TD_18f3c (0x18a80 : word) ltac:(pin; first [reflexivity | bveq]).  (* 0x18f3c ret *)
      OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { sn TF_18ef0 TD_18ef0.  (* 0x18ef0 addi a2, s2, 0x78 *)
      stw TF_18ef4 TD_18ef4 (Z_to_bv 64 470840) (tid) ltac:(ok_data).  (* 0x18ef4 sw a0, 0x20(s2) *)
      stw TF_18ef8 TD_18ef8 (Z_to_bv 64 470960) (Z_to_bv 64 602784) ltac:(ok_data).  (* 0x18ef8 sd a1, 0x98(s2) *)
      stw TF_18efc TD_18efc (Z_to_bv 64 470928) (Z_to_bv 64 470928) ltac:(ok_data).  (* 0x18efc sd a2, 0x78(s2) *)
      sn TF_18f00 TD_18f00.  (* 0x18f00 auipc a0, 0x7a *)
      ld_step TF_18f04 TD_18f04 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_93250_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18f04 ld a0, 0x350(a0) *)
      stw TF_18f08 TD_18f08 (Z_to_bv 64 470816) (Z_to_bv 64 470808) ltac:(ok_data).  (* 0x18f08 sd s2, 0x8(s2) *)
      stw TF_18f0c TD_18f0c (Z_to_bv 64 470824) (Z_to_bv 64 470808) ltac:(ok_data).  (* 0x18f0c sd s2, 0x10(s2) *)
      stw TF_18f10 TD_18f10 (Z_to_bv 64 470832) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x18f10 sd a0, 0x18(s2) *)
      sn TF_18f14 TD_18f14.  (* 0x18f14 j 0x18f1c <static_init_tls+0x28c> *)
      ld_step TF_18f1c TD_18f1c (word_to_le_bytes 8 (Z_to_bv 64 100992)) (Z_to_bv 64 100992) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18f1c ld ra, 0x38(sp) *)
      ld_step TF_18f20 TD_18f20 (word_to_le_bytes 8 (pn_w inp rdraw)) (pn_w inp rdraw) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18f20 ld s0, 0x30(sp) *)
      ld_step TF_18f24 TD_18f24 (word_to_le_bytes 8 s1v) (s1v) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18f24 ld s1, 0x28(sp) *)
      ld_step TF_18f28 TD_18f28 (word_to_le_bytes 8 (Z_to_bv 64 602728)) (Z_to_bv 64 602728) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18f28 ld s2, 0x20(sp) *)
      ld_step TF_18f2c TD_18f2c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18f2c ld s3, 0x18(sp) *)
      ld_step TF_18f30 TD_18f30 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18f30 ld s4, 0x10(sp) *)
      ld_step TF_18f34 TD_18f34 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18f34 ld s5, 0x8(sp) *)
      sv TF_18f38 TD_18f38 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* 0x18f38 addi sp, sp, 0x40 *)
      stepret TF_18f3c TD_18f3c (0x18a80 : word) ltac:(pin; first [reflexivity | bveq]).  (* 0x18f3c ret *)
      OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

End P4.
