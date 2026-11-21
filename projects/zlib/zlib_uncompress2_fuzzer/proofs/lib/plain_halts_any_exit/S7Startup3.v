(* elf , front , img own, defs ,
   statements (TEMPLATE; synthesized from the run), context , conventions ;
   valtac4: 'reflexivity' from 'WalkTac.v stepld_pc value side; S0Startup2.v F_152d4'; split-rseq all. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_zlib_uncompress2_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit Require Import StartupTac ArgvEnv RefLayout S7StartupDefs S7_code_18000_19000 S7_code_20000_20a30.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit Require Import LiaFast.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit Require L10Walk.
Ltac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.StepTac.chain_step ::= OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.L10Walk.l10_chain_step.
Abbreviation SEGS := Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments.
Abbreviation RPH := Src_zlib_zlib_uncompress2_fuzzer_repro.M.phdrs.
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
Lemma s2img_21b88_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 138120) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_22e20_4 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 142880) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
Lemma s2img_92f98_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 602008) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_92fa8_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 602024) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_92fb0_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 602032) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_931f0_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 602608) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_93218_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 602648) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_93230_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 602672) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
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
Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH (Z_to_bv 64 (Z.of_N Src_zlib_zlib_uncompress2_fuzzer_repro.M.init_pc)) sp0 rdraw)) (only parsing).

  Lemma tls_c1 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word), wfJ sp0 Jb -> getr regs 1 = Z_to_bv 64 100888 -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) -> getr regs 3 = Z_to_bv 64 67584 -> getr regs 8 = pn_w inp rdraw -> getr regs 9 = s1v -> getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) -> getr regs 18 = Z_to_bv 64 602632 -> getr regs 19 = Z_to_bv 64 0 -> getr regs 20 = Z_to_bv 64 0 -> getr regs 21 = Z_to_bv 64 0 -> getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 0 -> getr regs 25 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 0 -> getr regs 27 = Z_to_bv 64 0 -> (forall regs', getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) -> getr regs' 3 = (Z_to_bv 64 67584) -> getr regs' 5 = (Z_to_bv 64 0) -> getr regs' 7 = (Z_to_bv 64 7) -> getr regs' 9 = (Z_to_bv 64 602632) -> getr regs' 10 = (Z_to_bv 64 56) -> getr regs' 11 = (Z_to_bv 64 601992) -> getr regs' 12 = (Z_to_bv 64 0) -> getr regs' 13 = (Z_to_bv 64 10) -> getr regs' 15 = (Z_to_bv 64 65600) -> getr regs' 16 = (Z_to_bv 64 6) -> getr regs' 17 = (Z_to_bv 64 0) -> getr regs' 22 = (Z_to_bv 64 0) -> getr regs' 23 = (Z_to_bv 64 0) -> getr regs' 24 = (Z_to_bv 64 0) -> getr regs' 25 = (Z_to_bv 64 0) -> getr regs' 26 = (Z_to_bv 64 0) -> getr regs' 27 = (Z_to_bv 64 0) -> getr regs' 28 = (Z_to_bv 64 1685382481) -> getr regs' 29 = (Z_to_bv 64 65600) -> getr regs' 30 = (Z_to_bv 64 131072) -> regs_agree (fun r => In r [2; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30]%list) regs regs' -> G (mkst regs' (0x18cb0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100888))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602632))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom)) -> G (mkst regs (0x18c28 : word) (CM (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (D_libc sp0 inp rdraw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { sv F_18aec D_18aec (Z_to_bv 64 (bv_unsigned sp0 - 480)).  (* 0x18c28 addi sp, sp, -0x40 *)
      stw TF_18c2c TD_18c2c (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 100888) ltac:(ok_win HJ).  (* 0x18c2c sd ra, 0x38(sp) *)
      stw TF_18c30 TD_18c30 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w inp rdraw) ltac:(ok_win HJ).  (* 0x18c30 sd s0, 0x30(sp) *)
      stw TF_18c34 TD_18c34 (Z_to_bv 64 (bv_unsigned sp0 - 440)) (s1v) ltac:(ok_win HJ).  (* 0x18c34 sd s1, 0x28(sp) *)
      stw TF_18c38 TD_18c38 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 602632) ltac:(ok_win HJ).  (* 0x18c38 sd s2, 0x20(sp) *)
      stw TF_18c3c TD_18c3c (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x18c3c sd s3, 0x18(sp) *)
      stw TF_18c40 TD_18c40 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x18c40 sd s4, 0x10(sp) *)
      stw TF_18c44 TD_18c44 (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x18c44 sd s5, 0x8(sp) *)
      ld_step TF_18c48 TD_18c48 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18c48 ld a3, 0x28(a0) *)
      sn TF_18c4c TD_18c4c.  (* 0x18c4c auipc a1, 0x7a *)
      sn TF_18c50 TD_18c50.  (* 0x18c50 addi a1, a1, 0x33c *)
      sn TF_18c54 TD_18c54.  (* 0x18c54 auipc a2, 0x7a *)
      sn TF_18c58 TD_18c58.  (* 0x18c58 addi s1, a2, 0x5b4 *)
      stepb_ft TF_18c5c TD_18c5c ltac:(pin; cond_compute).  (* 0x18c5c beqz a3, 0x18d38 <static_init_tls+0x110> *)
      sn TF_18c60 TD_18c60.  (* 0x18c60 li a2, 0x0 *)
      sn TF_18c64 TD_18c64.  (* 0x18c64 li a7, 0x0 *)
      sn TF_18c68 TD_18c68.  (* 0x18c68 auipc a4, 0xa *)
      ld_step TF_18c6c TD_18c6c (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18c6c ld a5, 0x18(a0) *)
      ld_step TF_18c70 TD_18c70 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18c70 ld a0, 0x20(a0) *)
      sn TF_18c74 TD_18c74.  (* 0x18c74 li a6, 0x6 *)
      sn TF_18c78 TD_18c78.  (* 0x18c78 auipc t0, 0x9 *)
      ld_step TF_18c7c TD_18c7c (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img s2img_22e20_4) ltac:(reflexivity).  (* 0x18c7c lwu t5, 0x1b8(a4) *)
      ld_step TF_18c80 TD_18c80 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_21b88_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18c80 ld t0, -0xf0(t0) *)
      sn TF_18c84 TD_18c84.  (* 0x18c84 li t1, 0x2 *)
      sn TF_18c88 TD_18c88.  (* 0x18c88 li t2, 0x7 *)
      sn TF_18c8c TD_18c8c.  (* 0x18c8c lui t3, 0x6474e *)
      sn TF_18c90 TD_18c90.  (* 0x18c90 addiw t3, t3, 0x551 *)
      sn TF_18c94 TD_18c94.  (* 0x18c94 mv t4, a5 *)
      sn TF_18c98 TD_18c98.  (* 0x18c98 j 0x18cb0 <static_init_tls+0x88> *)
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { sv F_18aec D_18aec (Z_to_bv 64 (bv_unsigned sp0 - 480)).  (* 0x18c28 addi sp, sp, -0x40 *)
      stw TF_18c2c TD_18c2c (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 100888) ltac:(ok_win HJ).  (* 0x18c2c sd ra, 0x38(sp) *)
      stw TF_18c30 TD_18c30 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w inp rdraw) ltac:(ok_win HJ).  (* 0x18c30 sd s0, 0x30(sp) *)
      stw TF_18c34 TD_18c34 (Z_to_bv 64 (bv_unsigned sp0 - 440)) (s1v) ltac:(ok_win HJ).  (* 0x18c34 sd s1, 0x28(sp) *)
      stw TF_18c38 TD_18c38 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 602632) ltac:(ok_win HJ).  (* 0x18c38 sd s2, 0x20(sp) *)
      stw TF_18c3c TD_18c3c (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x18c3c sd s3, 0x18(sp) *)
      stw TF_18c40 TD_18c40 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x18c40 sd s4, 0x10(sp) *)
      stw TF_18c44 TD_18c44 (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x18c44 sd s5, 0x8(sp) *)
      ld_step TF_18c48 TD_18c48 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18c48 ld a3, 0x28(a0) *)
      sn TF_18c4c TD_18c4c.  (* 0x18c4c auipc a1, 0x7a *)
      sn TF_18c50 TD_18c50.  (* 0x18c50 addi a1, a1, 0x33c *)
      sn TF_18c54 TD_18c54.  (* 0x18c54 auipc a2, 0x7a *)
      sn TF_18c58 TD_18c58.  (* 0x18c58 addi s1, a2, 0x5b4 *)
      stepb_ft TF_18c5c TD_18c5c ltac:(pin; cond_compute).  (* 0x18c5c beqz a3, 0x18d38 <static_init_tls+0x110> *)
      sn TF_18c60 TD_18c60.  (* 0x18c60 li a2, 0x0 *)
      sn TF_18c64 TD_18c64.  (* 0x18c64 li a7, 0x0 *)
      sn TF_18c68 TD_18c68.  (* 0x18c68 auipc a4, 0xa *)
      ld_step TF_18c6c TD_18c6c (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18c6c ld a5, 0x18(a0) *)
      ld_step TF_18c70 TD_18c70 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18c70 ld a0, 0x20(a0) *)
      sn TF_18c74 TD_18c74.  (* 0x18c74 li a6, 0x6 *)
      sn TF_18c78 TD_18c78.  (* 0x18c78 auipc t0, 0x9 *)
      ld_step TF_18c7c TD_18c7c (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img s2img_22e20_4) ltac:(reflexivity).  (* 0x18c7c lwu t5, 0x1b8(a4) *)
      ld_step TF_18c80 TD_18c80 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_21b88_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18c80 ld t0, -0xf0(t0) *)
      sn TF_18c84 TD_18c84.  (* 0x18c84 li t1, 0x2 *)
      sn TF_18c88 TD_18c88.  (* 0x18c88 li t2, 0x7 *)
      sn TF_18c8c TD_18c8c.  (* 0x18c8c lui t3, 0x6474e *)
      sn TF_18c90 TD_18c90.  (* 0x18c90 addiw t3, t3, 0x551 *)
      sn TF_18c94 TD_18c94.  (* 0x18c94 mv t4, a5 *)
      sn TF_18c98 TD_18c98.  (* 0x18c98 j 0x18cb0 <static_init_tls+0x88> *)
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma tls_c2 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word), wfJ sp0 Jb -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) -> getr regs 3 = Z_to_bv 64 67584 -> getr regs 5 = Z_to_bv 64 0 -> getr regs 7 = Z_to_bv 64 7 -> getr regs 9 = Z_to_bv 64 602632 -> getr regs 10 = Z_to_bv 64 56 -> getr regs 11 = Z_to_bv 64 601992 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 10 -> getr regs 15 = Z_to_bv 64 65600 -> getr regs 16 = Z_to_bv 64 6 -> getr regs 17 = Z_to_bv 64 0 -> getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 0 -> getr regs 25 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 0 -> getr regs 27 = Z_to_bv 64 0 -> getr regs 28 = Z_to_bv 64 1685382481 -> getr regs 29 = Z_to_bv 64 65600 -> getr regs 30 = Z_to_bv 64 131072 -> (forall regs', getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) -> getr regs' 3 = (Z_to_bv 64 67584) -> getr regs' 5 = (Z_to_bv 64 0) -> getr regs' 7 = (Z_to_bv 64 7) -> getr regs' 9 = (Z_to_bv 64 602632) -> getr regs' 10 = (Z_to_bv 64 56) -> getr regs' 11 = (Z_to_bv 64 601992) -> getr regs' 12 = (Z_to_bv 64 0) -> getr regs' 13 = (Z_to_bv 64 5) -> getr regs' 16 = (Z_to_bv 64 6) -> getr regs' 17 = (Z_to_bv 64 0) -> getr regs' 22 = (Z_to_bv 64 0) -> getr regs' 23 = (Z_to_bv 64 0) -> getr regs' 24 = (Z_to_bv 64 0) -> getr regs' 25 = (Z_to_bv 64 0) -> getr regs' 26 = (Z_to_bv 64 0) -> getr regs' 27 = (Z_to_bv 64 0) -> getr regs' 28 = (Z_to_bv 64 1685382481) -> getr regs' 29 = (Z_to_bv 64 65880) -> getr regs' 30 = (Z_to_bv 64 131072) -> regs_agree (fun r => In r [8; 12; 13; 17; 29; 31]%list) regs regs' -> G (mkst regs' (0x18cb0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100888))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602632))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom)) -> G (mkst regs (0x18cb0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100888))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602632))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H12 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { ld_step TF_18cb0 TD_18cb0 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img s2img_10040_4) ltac:(reflexivity).  (* 0x18cb0 lw s0, 0x0(t4) *)
      stepb_tk TF_18cb4 TD_18cb4 ltac:(pin; cond_compute).  (* 0x18cb4 beq s0, a6, 0x18c9c <static_init_tls+0x74> *)
      ld_step TF_18c9c TD_18c9c (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img s2img_10050_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18c9c ld a2, 0x10(t4) *)
      sn TF_18ca0 TD_18ca0.  (* 0x18ca0 sub a2, a5, a2 *)
      sn TF_18ca4 TD_18ca4.  (* 0x18ca4 addi a3, a3, -0x1 *)
      sn TF_18ca8 TD_18ca8.  (* 0x18ca8 add t4, t4, a0 *)
      stepb_ft TF_18cac TD_18cac ltac:(pin; cond_compute).  (* 0x18cac beqz a3, 0x18d00 <static_init_tls+0xd8> *)
      ld_step TF_18cb0 TD_18cb0 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_10078_4) ltac:(reflexivity).  (* 0x18cb0 lw s0, 0x0(t4) *)
      stepb_ft TF_18cb4 TD_18cb4 ltac:(pin; cond_compute).  (* 0x18cb4 beq s0, a6, 0x18c9c <static_init_tls+0x74> *)
      stepb_tk TF_18cb8 TD_18cb8 ltac:(pin; cond_compute).  (* 0x18cb8 beqz t0, 0x18ccc <static_init_tls+0xa4> *)
      sn TF_18ccc TD_18ccc.  (* 0x18ccc mv t6, t4 *)
      stepb_ft TF_18cd0 TD_18cd0 ltac:(pin; cond_compute).  (* 0x18cd0 beq s0, t2, 0x18cd8 <static_init_tls+0xb0> *)
      sn TF_18cd4 TD_18cd4.  (* 0x18cd4 mv t6, a7 *)
      stepb_tk TF_18cd8 TD_18cd8 ltac:(pin; cond_compute).  (* 0x18cd8 bne s0, t3, 0x18cf8 <static_init_tls+0xd0> *)
      sn TF_18cf8 TD_18cf8.  (* 0x18cf8 mv a7, t6 *)
      sn TF_18cfc TD_18cfc.  (* 0x18cfc j 0x18ca4 <static_init_tls+0x7c> *)
      sn TF_18ca4 TD_18ca4.  (* 0x18ca4 addi a3, a3, -0x1 *)
      sn TF_18ca8 TD_18ca8.  (* 0x18ca8 add t4, t4, a0 *)
      stepb_ft TF_18cac TD_18cac ltac:(pin; cond_compute).  (* 0x18cac beqz a3, 0x18d00 <static_init_tls+0xd8> *)
      ld_step TF_18cb0 TD_18cb0 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_100b0_4) ltac:(reflexivity).  (* 0x18cb0 lw s0, 0x0(t4) *)
      stepb_ft TF_18cb4 TD_18cb4 ltac:(pin; cond_compute).  (* 0x18cb4 beq s0, a6, 0x18c9c <static_init_tls+0x74> *)
      stepb_tk TF_18cb8 TD_18cb8 ltac:(pin; cond_compute).  (* 0x18cb8 beqz t0, 0x18ccc <static_init_tls+0xa4> *)
      sn TF_18ccc TD_18ccc.  (* 0x18ccc mv t6, t4 *)
      stepb_ft TF_18cd0 TD_18cd0 ltac:(pin; cond_compute).  (* 0x18cd0 beq s0, t2, 0x18cd8 <static_init_tls+0xb0> *)
      sn TF_18cd4 TD_18cd4.  (* 0x18cd4 mv t6, a7 *)
      stepb_tk TF_18cd8 TD_18cd8 ltac:(pin; cond_compute).  (* 0x18cd8 bne s0, t3, 0x18cf8 <static_init_tls+0xd0> *)
      sn TF_18cf8 TD_18cf8.  (* 0x18cf8 mv a7, t6 *)
      sn TF_18cfc TD_18cfc.  (* 0x18cfc j 0x18ca4 <static_init_tls+0x7c> *)
      sn TF_18ca4 TD_18ca4.  (* 0x18ca4 addi a3, a3, -0x1 *)
      sn TF_18ca8 TD_18ca8.  (* 0x18ca8 add t4, t4, a0 *)
      stepb_ft TF_18cac TD_18cac ltac:(pin; cond_compute).  (* 0x18cac beqz a3, 0x18d00 <static_init_tls+0xd8> *)
      ld_step TF_18cb0 TD_18cb0 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_100e8_4) ltac:(reflexivity).  (* 0x18cb0 lw s0, 0x0(t4) *)
      stepb_ft TF_18cb4 TD_18cb4 ltac:(pin; cond_compute).  (* 0x18cb4 beq s0, a6, 0x18c9c <static_init_tls+0x74> *)
      stepb_tk TF_18cb8 TD_18cb8 ltac:(pin; cond_compute).  (* 0x18cb8 beqz t0, 0x18ccc <static_init_tls+0xa4> *)
      sn TF_18ccc TD_18ccc.  (* 0x18ccc mv t6, t4 *)
      stepb_ft TF_18cd0 TD_18cd0 ltac:(pin; cond_compute).  (* 0x18cd0 beq s0, t2, 0x18cd8 <static_init_tls+0xb0> *)
      sn TF_18cd4 TD_18cd4.  (* 0x18cd4 mv t6, a7 *)
      stepb_tk TF_18cd8 TD_18cd8 ltac:(pin; cond_compute).  (* 0x18cd8 bne s0, t3, 0x18cf8 <static_init_tls+0xd0> *)
      sn TF_18cf8 TD_18cf8.  (* 0x18cf8 mv a7, t6 *)
      sn TF_18cfc TD_18cfc.  (* 0x18cfc j 0x18ca4 <static_init_tls+0x7c> *)
      sn TF_18ca4 TD_18ca4.  (* 0x18ca4 addi a3, a3, -0x1 *)
      sn TF_18ca8 TD_18ca8.  (* 0x18ca8 add t4, t4, a0 *)
      stepb_ft TF_18cac TD_18cac ltac:(pin; cond_compute).  (* 0x18cac beqz a3, 0x18d00 <static_init_tls+0xd8> *)
      ld_step TF_18cb0 TD_18cb0 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_10120_4) ltac:(reflexivity).  (* 0x18cb0 lw s0, 0x0(t4) *)
      stepb_ft TF_18cb4 TD_18cb4 ltac:(pin; cond_compute).  (* 0x18cb4 beq s0, a6, 0x18c9c <static_init_tls+0x74> *)
      stepb_tk TF_18cb8 TD_18cb8 ltac:(pin; cond_compute).  (* 0x18cb8 beqz t0, 0x18ccc <static_init_tls+0xa4> *)
      sn TF_18ccc TD_18ccc.  (* 0x18ccc mv t6, t4 *)
      stepb_ft TF_18cd0 TD_18cd0 ltac:(pin; cond_compute).  (* 0x18cd0 beq s0, t2, 0x18cd8 <static_init_tls+0xb0> *)
      sn TF_18cd4 TD_18cd4.  (* 0x18cd4 mv t6, a7 *)
      stepb_tk TF_18cd8 TD_18cd8 ltac:(pin; cond_compute).  (* 0x18cd8 bne s0, t3, 0x18cf8 <static_init_tls+0xd0> *)
      sn TF_18cf8 TD_18cf8.  (* 0x18cf8 mv a7, t6 *)
      sn TF_18cfc TD_18cfc.  (* 0x18cfc j 0x18ca4 <static_init_tls+0x7c> *)
      sn TF_18ca4 TD_18ca4.  (* 0x18ca4 addi a3, a3, -0x1 *)
      sn TF_18ca8 TD_18ca8.  (* 0x18ca8 add t4, t4, a0 *)
      stepb_ft TF_18cac TD_18cac ltac:(pin; cond_compute).  (* 0x18cac beqz a3, 0x18d00 <static_init_tls+0xd8> *)
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { ld_step TF_18cb0 TD_18cb0 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img s2img_10040_4) ltac:(reflexivity).  (* 0x18cb0 lw s0, 0x0(t4) *)
      stepb_tk TF_18cb4 TD_18cb4 ltac:(pin; cond_compute).  (* 0x18cb4 beq s0, a6, 0x18c9c <static_init_tls+0x74> *)
      ld_step TF_18c9c TD_18c9c (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img s2img_10050_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18c9c ld a2, 0x10(t4) *)
      sn TF_18ca0 TD_18ca0.  (* 0x18ca0 sub a2, a5, a2 *)
      sn TF_18ca4 TD_18ca4.  (* 0x18ca4 addi a3, a3, -0x1 *)
      sn TF_18ca8 TD_18ca8.  (* 0x18ca8 add t4, t4, a0 *)
      stepb_ft TF_18cac TD_18cac ltac:(pin; cond_compute).  (* 0x18cac beqz a3, 0x18d00 <static_init_tls+0xd8> *)
      ld_step TF_18cb0 TD_18cb0 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_10078_4) ltac:(reflexivity).  (* 0x18cb0 lw s0, 0x0(t4) *)
      stepb_ft TF_18cb4 TD_18cb4 ltac:(pin; cond_compute).  (* 0x18cb4 beq s0, a6, 0x18c9c <static_init_tls+0x74> *)
      stepb_tk TF_18cb8 TD_18cb8 ltac:(pin; cond_compute).  (* 0x18cb8 beqz t0, 0x18ccc <static_init_tls+0xa4> *)
      sn TF_18ccc TD_18ccc.  (* 0x18ccc mv t6, t4 *)
      stepb_ft TF_18cd0 TD_18cd0 ltac:(pin; cond_compute).  (* 0x18cd0 beq s0, t2, 0x18cd8 <static_init_tls+0xb0> *)
      sn TF_18cd4 TD_18cd4.  (* 0x18cd4 mv t6, a7 *)
      stepb_tk TF_18cd8 TD_18cd8 ltac:(pin; cond_compute).  (* 0x18cd8 bne s0, t3, 0x18cf8 <static_init_tls+0xd0> *)
      sn TF_18cf8 TD_18cf8.  (* 0x18cf8 mv a7, t6 *)
      sn TF_18cfc TD_18cfc.  (* 0x18cfc j 0x18ca4 <static_init_tls+0x7c> *)
      sn TF_18ca4 TD_18ca4.  (* 0x18ca4 addi a3, a3, -0x1 *)
      sn TF_18ca8 TD_18ca8.  (* 0x18ca8 add t4, t4, a0 *)
      stepb_ft TF_18cac TD_18cac ltac:(pin; cond_compute).  (* 0x18cac beqz a3, 0x18d00 <static_init_tls+0xd8> *)
      ld_step TF_18cb0 TD_18cb0 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_100b0_4) ltac:(reflexivity).  (* 0x18cb0 lw s0, 0x0(t4) *)
      stepb_ft TF_18cb4 TD_18cb4 ltac:(pin; cond_compute).  (* 0x18cb4 beq s0, a6, 0x18c9c <static_init_tls+0x74> *)
      stepb_tk TF_18cb8 TD_18cb8 ltac:(pin; cond_compute).  (* 0x18cb8 beqz t0, 0x18ccc <static_init_tls+0xa4> *)
      sn TF_18ccc TD_18ccc.  (* 0x18ccc mv t6, t4 *)
      stepb_ft TF_18cd0 TD_18cd0 ltac:(pin; cond_compute).  (* 0x18cd0 beq s0, t2, 0x18cd8 <static_init_tls+0xb0> *)
      sn TF_18cd4 TD_18cd4.  (* 0x18cd4 mv t6, a7 *)
      stepb_tk TF_18cd8 TD_18cd8 ltac:(pin; cond_compute).  (* 0x18cd8 bne s0, t3, 0x18cf8 <static_init_tls+0xd0> *)
      sn TF_18cf8 TD_18cf8.  (* 0x18cf8 mv a7, t6 *)
      sn TF_18cfc TD_18cfc.  (* 0x18cfc j 0x18ca4 <static_init_tls+0x7c> *)
      sn TF_18ca4 TD_18ca4.  (* 0x18ca4 addi a3, a3, -0x1 *)
      sn TF_18ca8 TD_18ca8.  (* 0x18ca8 add t4, t4, a0 *)
      stepb_ft TF_18cac TD_18cac ltac:(pin; cond_compute).  (* 0x18cac beqz a3, 0x18d00 <static_init_tls+0xd8> *)
      ld_step TF_18cb0 TD_18cb0 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_100e8_4) ltac:(reflexivity).  (* 0x18cb0 lw s0, 0x0(t4) *)
      stepb_ft TF_18cb4 TD_18cb4 ltac:(pin; cond_compute).  (* 0x18cb4 beq s0, a6, 0x18c9c <static_init_tls+0x74> *)
      stepb_tk TF_18cb8 TD_18cb8 ltac:(pin; cond_compute).  (* 0x18cb8 beqz t0, 0x18ccc <static_init_tls+0xa4> *)
      sn TF_18ccc TD_18ccc.  (* 0x18ccc mv t6, t4 *)
      stepb_ft TF_18cd0 TD_18cd0 ltac:(pin; cond_compute).  (* 0x18cd0 beq s0, t2, 0x18cd8 <static_init_tls+0xb0> *)
      sn TF_18cd4 TD_18cd4.  (* 0x18cd4 mv t6, a7 *)
      stepb_tk TF_18cd8 TD_18cd8 ltac:(pin; cond_compute).  (* 0x18cd8 bne s0, t3, 0x18cf8 <static_init_tls+0xd0> *)
      sn TF_18cf8 TD_18cf8.  (* 0x18cf8 mv a7, t6 *)
      sn TF_18cfc TD_18cfc.  (* 0x18cfc j 0x18ca4 <static_init_tls+0x7c> *)
      sn TF_18ca4 TD_18ca4.  (* 0x18ca4 addi a3, a3, -0x1 *)
      sn TF_18ca8 TD_18ca8.  (* 0x18ca8 add t4, t4, a0 *)
      stepb_ft TF_18cac TD_18cac ltac:(pin; cond_compute).  (* 0x18cac beqz a3, 0x18d00 <static_init_tls+0xd8> *)
      ld_step TF_18cb0 TD_18cb0 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_10120_4) ltac:(reflexivity).  (* 0x18cb0 lw s0, 0x0(t4) *)
      stepb_ft TF_18cb4 TD_18cb4 ltac:(pin; cond_compute).  (* 0x18cb4 beq s0, a6, 0x18c9c <static_init_tls+0x74> *)
      stepb_tk TF_18cb8 TD_18cb8 ltac:(pin; cond_compute).  (* 0x18cb8 beqz t0, 0x18ccc <static_init_tls+0xa4> *)
      sn TF_18ccc TD_18ccc.  (* 0x18ccc mv t6, t4 *)
      stepb_ft TF_18cd0 TD_18cd0 ltac:(pin; cond_compute).  (* 0x18cd0 beq s0, t2, 0x18cd8 <static_init_tls+0xb0> *)
      sn TF_18cd4 TD_18cd4.  (* 0x18cd4 mv t6, a7 *)
      stepb_tk TF_18cd8 TD_18cd8 ltac:(pin; cond_compute).  (* 0x18cd8 bne s0, t3, 0x18cf8 <static_init_tls+0xd0> *)
      sn TF_18cf8 TD_18cf8.  (* 0x18cf8 mv a7, t6 *)
      sn TF_18cfc TD_18cfc.  (* 0x18cfc j 0x18ca4 <static_init_tls+0x7c> *)
      sn TF_18ca4 TD_18ca4.  (* 0x18ca4 addi a3, a3, -0x1 *)
      sn TF_18ca8 TD_18ca8.  (* 0x18ca8 add t4, t4, a0 *)
      stepb_ft TF_18cac TD_18cac ltac:(pin; cond_compute).  (* 0x18cac beqz a3, 0x18d00 <static_init_tls+0xd8> *)
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma tls_c3 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word), wfJ sp0 Jb -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) -> getr regs 3 = Z_to_bv 64 67584 -> getr regs 5 = Z_to_bv 64 0 -> getr regs 7 = Z_to_bv 64 7 -> getr regs 9 = Z_to_bv 64 602632 -> getr regs 10 = Z_to_bv 64 56 -> getr regs 11 = Z_to_bv 64 601992 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 5 -> getr regs 16 = Z_to_bv 64 6 -> getr regs 17 = Z_to_bv 64 0 -> getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 0 -> getr regs 25 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 0 -> getr regs 27 = Z_to_bv 64 0 -> getr regs 28 = Z_to_bv 64 1685382481 -> getr regs 29 = Z_to_bv 64 65880 -> getr regs 30 = Z_to_bv 64 131072 -> (forall regs', getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) -> getr regs' 3 = (Z_to_bv 64 67584) -> getr regs' 9 = (Z_to_bv 64 602632) -> getr regs' 11 = (Z_to_bv 64 601992) -> getr regs' 12 = (Z_to_bv 64 0) -> getr regs' 17 = (Z_to_bv 64 0) -> getr regs' 22 = (Z_to_bv 64 0) -> getr regs' 23 = (Z_to_bv 64 0) -> getr regs' 24 = (Z_to_bv 64 0) -> getr regs' 25 = (Z_to_bv 64 0) -> getr regs' 26 = (Z_to_bv 64 0) -> getr regs' 27 = (Z_to_bv 64 0) -> regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' -> G (mkst regs' (0x18d00 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100888))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602632))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom)) -> G (mkst regs (0x18cb0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100888))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602632))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H12 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { ld_step TF_18cb0 TD_18cb0 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img s2img_10158_4) ltac:(reflexivity).  (* 0x18cb0 lw s0, 0x0(t4) *)
      stepb_ft TF_18cb4 TD_18cb4 ltac:(pin; cond_compute).  (* 0x18cb4 beq s0, a6, 0x18c9c <static_init_tls+0x74> *)
      stepb_tk TF_18cb8 TD_18cb8 ltac:(pin; cond_compute).  (* 0x18cb8 beqz t0, 0x18ccc <static_init_tls+0xa4> *)
      sn TF_18ccc TD_18ccc.  (* 0x18ccc mv t6, t4 *)
      stepb_ft TF_18cd0 TD_18cd0 ltac:(pin; cond_compute).  (* 0x18cd0 beq s0, t2, 0x18cd8 <static_init_tls+0xb0> *)
      sn TF_18cd4 TD_18cd4.  (* 0x18cd4 mv t6, a7 *)
      stepb_tk TF_18cd8 TD_18cd8 ltac:(pin; cond_compute).  (* 0x18cd8 bne s0, t3, 0x18cf8 <static_init_tls+0xd0> *)
      sn TF_18cf8 TD_18cf8.  (* 0x18cf8 mv a7, t6 *)
      sn TF_18cfc TD_18cfc.  (* 0x18cfc j 0x18ca4 <static_init_tls+0x7c> *)
      sn TF_18ca4 TD_18ca4.  (* 0x18ca4 addi a3, a3, -0x1 *)
      sn TF_18ca8 TD_18ca8.  (* 0x18ca8 add t4, t4, a0 *)
      stepb_ft TF_18cac TD_18cac ltac:(pin; cond_compute).  (* 0x18cac beqz a3, 0x18d00 <static_init_tls+0xd8> *)
      ld_step TF_18cb0 TD_18cb0 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img s2img_10190_4) ltac:(reflexivity).  (* 0x18cb0 lw s0, 0x0(t4) *)
      stepb_ft TF_18cb4 TD_18cb4 ltac:(pin; cond_compute).  (* 0x18cb4 beq s0, a6, 0x18c9c <static_init_tls+0x74> *)
      stepb_tk TF_18cb8 TD_18cb8 ltac:(pin; cond_compute).  (* 0x18cb8 beqz t0, 0x18ccc <static_init_tls+0xa4> *)
      sn TF_18ccc TD_18ccc.  (* 0x18ccc mv t6, t4 *)
      stepb_ft TF_18cd0 TD_18cd0 ltac:(pin; cond_compute).  (* 0x18cd0 beq s0, t2, 0x18cd8 <static_init_tls+0xb0> *)
      sn TF_18cd4 TD_18cd4.  (* 0x18cd4 mv t6, a7 *)
      stepb_tk TF_18cd8 TD_18cd8 ltac:(pin; cond_compute).  (* 0x18cd8 bne s0, t3, 0x18cf8 <static_init_tls+0xd0> *)
      sn TF_18cf8 TD_18cf8.  (* 0x18cf8 mv a7, t6 *)
      sn TF_18cfc TD_18cfc.  (* 0x18cfc j 0x18ca4 <static_init_tls+0x7c> *)
      sn TF_18ca4 TD_18ca4.  (* 0x18ca4 addi a3, a3, -0x1 *)
      sn TF_18ca8 TD_18ca8.  (* 0x18ca8 add t4, t4, a0 *)
      stepb_ft TF_18cac TD_18cac ltac:(pin; cond_compute).  (* 0x18cac beqz a3, 0x18d00 <static_init_tls+0xd8> *)
      ld_step TF_18cb0 TD_18cb0 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img s2img_101c8_4) ltac:(reflexivity).  (* 0x18cb0 lw s0, 0x0(t4) *)
      stepb_ft TF_18cb4 TD_18cb4 ltac:(pin; cond_compute).  (* 0x18cb4 beq s0, a6, 0x18c9c <static_init_tls+0x74> *)
      stepb_tk TF_18cb8 TD_18cb8 ltac:(pin; cond_compute).  (* 0x18cb8 beqz t0, 0x18ccc <static_init_tls+0xa4> *)
      sn TF_18ccc TD_18ccc.  (* 0x18ccc mv t6, t4 *)
      stepb_ft TF_18cd0 TD_18cd0 ltac:(pin; cond_compute).  (* 0x18cd0 beq s0, t2, 0x18cd8 <static_init_tls+0xb0> *)
      sn TF_18cd4 TD_18cd4.  (* 0x18cd4 mv t6, a7 *)
      stepb_ft TF_18cd8 TD_18cd8 ltac:(pin; cond_compute).  (* 0x18cd8 bne s0, t3, 0x18cf8 <static_init_tls+0xd0> *)
      ld_step TF_18cdc TD_18cdc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_101f0_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18cdc ld a7, 0x28(t4) *)
      stepb_tk TF_18ce0 TD_18ce0 ltac:(pin; cond_compute).  (* 0x18ce0 bgeu t5, a7, 0x18cf8 <static_init_tls+0xd0> *)
      sn TF_18cf8 TD_18cf8.  (* 0x18cf8 mv a7, t6 *)
      sn TF_18cfc TD_18cfc.  (* 0x18cfc j 0x18ca4 <static_init_tls+0x7c> *)
      sn TF_18ca4 TD_18ca4.  (* 0x18ca4 addi a3, a3, -0x1 *)
      sn TF_18ca8 TD_18ca8.  (* 0x18ca8 add t4, t4, a0 *)
      stepb_ft TF_18cac TD_18cac ltac:(pin; cond_compute).  (* 0x18cac beqz a3, 0x18d00 <static_init_tls+0xd8> *)
      ld_step TF_18cb0 TD_18cb0 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img s2img_10200_4) ltac:(reflexivity).  (* 0x18cb0 lw s0, 0x0(t4) *)
      stepb_ft TF_18cb4 TD_18cb4 ltac:(pin; cond_compute).  (* 0x18cb4 beq s0, a6, 0x18c9c <static_init_tls+0x74> *)
      stepb_tk TF_18cb8 TD_18cb8 ltac:(pin; cond_compute).  (* 0x18cb8 beqz t0, 0x18ccc <static_init_tls+0xa4> *)
      sn TF_18ccc TD_18ccc.  (* 0x18ccc mv t6, t4 *)
      stepb_ft TF_18cd0 TD_18cd0 ltac:(pin; cond_compute).  (* 0x18cd0 beq s0, t2, 0x18cd8 <static_init_tls+0xb0> *)
      sn TF_18cd4 TD_18cd4.  (* 0x18cd4 mv t6, a7 *)
      stepb_tk TF_18cd8 TD_18cd8 ltac:(pin; cond_compute).  (* 0x18cd8 bne s0, t3, 0x18cf8 <static_init_tls+0xd0> *)
      sn TF_18cf8 TD_18cf8.  (* 0x18cf8 mv a7, t6 *)
      sn TF_18cfc TD_18cfc.  (* 0x18cfc j 0x18ca4 <static_init_tls+0x7c> *)
      sn TF_18ca4 TD_18ca4.  (* 0x18ca4 addi a3, a3, -0x1 *)
      sn TF_18ca8 TD_18ca8.  (* 0x18ca8 add t4, t4, a0 *)
      stepb_ft TF_18cac TD_18cac ltac:(pin; cond_compute).  (* 0x18cac beqz a3, 0x18d00 <static_init_tls+0xd8> *)
      ld_step TF_18cb0 TD_18cb0 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img s2img_10238_4) ltac:(reflexivity).  (* 0x18cb0 lw s0, 0x0(t4) *)
      stepb_ft TF_18cb4 TD_18cb4 ltac:(pin; cond_compute).  (* 0x18cb4 beq s0, a6, 0x18c9c <static_init_tls+0x74> *)
      stepb_tk TF_18cb8 TD_18cb8 ltac:(pin; cond_compute).  (* 0x18cb8 beqz t0, 0x18ccc <static_init_tls+0xa4> *)
      sn TF_18ccc TD_18ccc.  (* 0x18ccc mv t6, t4 *)
      stepb_ft TF_18cd0 TD_18cd0 ltac:(pin; cond_compute).  (* 0x18cd0 beq s0, t2, 0x18cd8 <static_init_tls+0xb0> *)
      sn TF_18cd4 TD_18cd4.  (* 0x18cd4 mv t6, a7 *)
      stepb_tk TF_18cd8 TD_18cd8 ltac:(pin; cond_compute).  (* 0x18cd8 bne s0, t3, 0x18cf8 <static_init_tls+0xd0> *)
      sn TF_18cf8 TD_18cf8.  (* 0x18cf8 mv a7, t6 *)
      sn TF_18cfc TD_18cfc.  (* 0x18cfc j 0x18ca4 <static_init_tls+0x7c> *)
      sn TF_18ca4 TD_18ca4.  (* 0x18ca4 addi a3, a3, -0x1 *)
      sn TF_18ca8 TD_18ca8.  (* 0x18ca8 add t4, t4, a0 *)
      stepb_tk TF_18cac TD_18cac ltac:(pin; cond_compute).  (* 0x18cac beqz a3, 0x18d00 <static_init_tls+0xd8> *)
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { ld_step TF_18cb0 TD_18cb0 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img s2img_10158_4) ltac:(reflexivity).  (* 0x18cb0 lw s0, 0x0(t4) *)
      stepb_ft TF_18cb4 TD_18cb4 ltac:(pin; cond_compute).  (* 0x18cb4 beq s0, a6, 0x18c9c <static_init_tls+0x74> *)
      stepb_tk TF_18cb8 TD_18cb8 ltac:(pin; cond_compute).  (* 0x18cb8 beqz t0, 0x18ccc <static_init_tls+0xa4> *)
      sn TF_18ccc TD_18ccc.  (* 0x18ccc mv t6, t4 *)
      stepb_ft TF_18cd0 TD_18cd0 ltac:(pin; cond_compute).  (* 0x18cd0 beq s0, t2, 0x18cd8 <static_init_tls+0xb0> *)
      sn TF_18cd4 TD_18cd4.  (* 0x18cd4 mv t6, a7 *)
      stepb_tk TF_18cd8 TD_18cd8 ltac:(pin; cond_compute).  (* 0x18cd8 bne s0, t3, 0x18cf8 <static_init_tls+0xd0> *)
      sn TF_18cf8 TD_18cf8.  (* 0x18cf8 mv a7, t6 *)
      sn TF_18cfc TD_18cfc.  (* 0x18cfc j 0x18ca4 <static_init_tls+0x7c> *)
      sn TF_18ca4 TD_18ca4.  (* 0x18ca4 addi a3, a3, -0x1 *)
      sn TF_18ca8 TD_18ca8.  (* 0x18ca8 add t4, t4, a0 *)
      stepb_ft TF_18cac TD_18cac ltac:(pin; cond_compute).  (* 0x18cac beqz a3, 0x18d00 <static_init_tls+0xd8> *)
      ld_step TF_18cb0 TD_18cb0 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img s2img_10190_4) ltac:(reflexivity).  (* 0x18cb0 lw s0, 0x0(t4) *)
      stepb_ft TF_18cb4 TD_18cb4 ltac:(pin; cond_compute).  (* 0x18cb4 beq s0, a6, 0x18c9c <static_init_tls+0x74> *)
      stepb_tk TF_18cb8 TD_18cb8 ltac:(pin; cond_compute).  (* 0x18cb8 beqz t0, 0x18ccc <static_init_tls+0xa4> *)
      sn TF_18ccc TD_18ccc.  (* 0x18ccc mv t6, t4 *)
      stepb_ft TF_18cd0 TD_18cd0 ltac:(pin; cond_compute).  (* 0x18cd0 beq s0, t2, 0x18cd8 <static_init_tls+0xb0> *)
      sn TF_18cd4 TD_18cd4.  (* 0x18cd4 mv t6, a7 *)
      stepb_tk TF_18cd8 TD_18cd8 ltac:(pin; cond_compute).  (* 0x18cd8 bne s0, t3, 0x18cf8 <static_init_tls+0xd0> *)
      sn TF_18cf8 TD_18cf8.  (* 0x18cf8 mv a7, t6 *)
      sn TF_18cfc TD_18cfc.  (* 0x18cfc j 0x18ca4 <static_init_tls+0x7c> *)
      sn TF_18ca4 TD_18ca4.  (* 0x18ca4 addi a3, a3, -0x1 *)
      sn TF_18ca8 TD_18ca8.  (* 0x18ca8 add t4, t4, a0 *)
      stepb_ft TF_18cac TD_18cac ltac:(pin; cond_compute).  (* 0x18cac beqz a3, 0x18d00 <static_init_tls+0xd8> *)
      ld_step TF_18cb0 TD_18cb0 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img s2img_101c8_4) ltac:(reflexivity).  (* 0x18cb0 lw s0, 0x0(t4) *)
      stepb_ft TF_18cb4 TD_18cb4 ltac:(pin; cond_compute).  (* 0x18cb4 beq s0, a6, 0x18c9c <static_init_tls+0x74> *)
      stepb_tk TF_18cb8 TD_18cb8 ltac:(pin; cond_compute).  (* 0x18cb8 beqz t0, 0x18ccc <static_init_tls+0xa4> *)
      sn TF_18ccc TD_18ccc.  (* 0x18ccc mv t6, t4 *)
      stepb_ft TF_18cd0 TD_18cd0 ltac:(pin; cond_compute).  (* 0x18cd0 beq s0, t2, 0x18cd8 <static_init_tls+0xb0> *)
      sn TF_18cd4 TD_18cd4.  (* 0x18cd4 mv t6, a7 *)
      stepb_ft TF_18cd8 TD_18cd8 ltac:(pin; cond_compute).  (* 0x18cd8 bne s0, t3, 0x18cf8 <static_init_tls+0xd0> *)
      ld_step TF_18cdc TD_18cdc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_101f0_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18cdc ld a7, 0x28(t4) *)
      stepb_tk TF_18ce0 TD_18ce0 ltac:(pin; cond_compute).  (* 0x18ce0 bgeu t5, a7, 0x18cf8 <static_init_tls+0xd0> *)
      sn TF_18cf8 TD_18cf8.  (* 0x18cf8 mv a7, t6 *)
      sn TF_18cfc TD_18cfc.  (* 0x18cfc j 0x18ca4 <static_init_tls+0x7c> *)
      sn TF_18ca4 TD_18ca4.  (* 0x18ca4 addi a3, a3, -0x1 *)
      sn TF_18ca8 TD_18ca8.  (* 0x18ca8 add t4, t4, a0 *)
      stepb_ft TF_18cac TD_18cac ltac:(pin; cond_compute).  (* 0x18cac beqz a3, 0x18d00 <static_init_tls+0xd8> *)
      ld_step TF_18cb0 TD_18cb0 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img s2img_10200_4) ltac:(reflexivity).  (* 0x18cb0 lw s0, 0x0(t4) *)
      stepb_ft TF_18cb4 TD_18cb4 ltac:(pin; cond_compute).  (* 0x18cb4 beq s0, a6, 0x18c9c <static_init_tls+0x74> *)
      stepb_tk TF_18cb8 TD_18cb8 ltac:(pin; cond_compute).  (* 0x18cb8 beqz t0, 0x18ccc <static_init_tls+0xa4> *)
      sn TF_18ccc TD_18ccc.  (* 0x18ccc mv t6, t4 *)
      stepb_ft TF_18cd0 TD_18cd0 ltac:(pin; cond_compute).  (* 0x18cd0 beq s0, t2, 0x18cd8 <static_init_tls+0xb0> *)
      sn TF_18cd4 TD_18cd4.  (* 0x18cd4 mv t6, a7 *)
      stepb_tk TF_18cd8 TD_18cd8 ltac:(pin; cond_compute).  (* 0x18cd8 bne s0, t3, 0x18cf8 <static_init_tls+0xd0> *)
      sn TF_18cf8 TD_18cf8.  (* 0x18cf8 mv a7, t6 *)
      sn TF_18cfc TD_18cfc.  (* 0x18cfc j 0x18ca4 <static_init_tls+0x7c> *)
      sn TF_18ca4 TD_18ca4.  (* 0x18ca4 addi a3, a3, -0x1 *)
      sn TF_18ca8 TD_18ca8.  (* 0x18ca8 add t4, t4, a0 *)
      stepb_ft TF_18cac TD_18cac ltac:(pin; cond_compute).  (* 0x18cac beqz a3, 0x18d00 <static_init_tls+0xd8> *)
      ld_step TF_18cb0 TD_18cb0 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img s2img_10238_4) ltac:(reflexivity).  (* 0x18cb0 lw s0, 0x0(t4) *)
      stepb_ft TF_18cb4 TD_18cb4 ltac:(pin; cond_compute).  (* 0x18cb4 beq s0, a6, 0x18c9c <static_init_tls+0x74> *)
      stepb_tk TF_18cb8 TD_18cb8 ltac:(pin; cond_compute).  (* 0x18cb8 beqz t0, 0x18ccc <static_init_tls+0xa4> *)
      sn TF_18ccc TD_18ccc.  (* 0x18ccc mv t6, t4 *)
      stepb_ft TF_18cd0 TD_18cd0 ltac:(pin; cond_compute).  (* 0x18cd0 beq s0, t2, 0x18cd8 <static_init_tls+0xb0> *)
      sn TF_18cd4 TD_18cd4.  (* 0x18cd4 mv t6, a7 *)
      stepb_tk TF_18cd8 TD_18cd8 ltac:(pin; cond_compute).  (* 0x18cd8 bne s0, t3, 0x18cf8 <static_init_tls+0xd0> *)
      sn TF_18cf8 TD_18cf8.  (* 0x18cf8 mv a7, t6 *)
      sn TF_18cfc TD_18cfc.  (* 0x18cfc j 0x18ca4 <static_init_tls+0x7c> *)
      sn TF_18ca4 TD_18ca4.  (* 0x18ca4 addi a3, a3, -0x1 *)
      sn TF_18ca8 TD_18ca8.  (* 0x18ca8 add t4, t4, a0 *)
      stepb_tk TF_18cac TD_18cac ltac:(pin; cond_compute).  (* 0x18cac beqz a3, 0x18d00 <static_init_tls+0xd8> *)
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma tls_c4 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word), wfJ sp0 Jb -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) -> getr regs 3 = Z_to_bv 64 67584 -> getr regs 9 = Z_to_bv 64 602632 -> getr regs 11 = Z_to_bv 64 601992 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 17 = Z_to_bv 64 0 -> getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 0 -> getr regs 25 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 0 -> getr regs 27 = Z_to_bv 64 0 -> (forall regs', getr regs' 1 = (Z_to_bv 64 101980) -> getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) -> getr regs' 3 = (Z_to_bv 64 67584) -> getr regs' 4 = (Z_to_bv 64 470912) -> getr regs' 8 = (Z_to_bv 64 470912) -> getr regs' 10 = (Z_to_bv 64 601992) -> getr regs' 11 = (Z_to_bv 64 602688) -> getr regs' 12 = (Z_to_bv 64 0) -> getr regs' 13 = (Z_to_bv 64 470704) -> getr regs' 14 = (Z_to_bv 64 0) -> getr regs' 15 = (Z_to_bv 64 18446744073709080704) -> getr regs' 17 = (Z_to_bv 64 96) -> getr regs' 18 = (Z_to_bv 64 470712) -> getr regs' 19 = (Z_to_bv 64 0) -> getr regs' 20 = (Z_to_bv 64 470928) -> getr regs' 22 = (Z_to_bv 64 0) -> getr regs' 23 = (Z_to_bv 64 0) -> getr regs' 24 = (Z_to_bv 64 0) -> getr regs' 25 = (Z_to_bv 64 0) -> getr regs' 26 = (Z_to_bv 64 0) -> getr regs' 27 = (Z_to_bv 64 0) -> regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' -> G (mkst regs' (0x18e84 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100888))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602632))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602024) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602040) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602032) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602656) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602664) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 470928) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 470904) (word_to_le_bytes 8 (Z_to_bv 64 470928))) (Z_to_bv 64 470712) (word_to_le_bytes 8 (Z_to_bv 64 470712))) (Z_to_bv 64 602632) ([Z_to_bv 8 1])) (Z_to_bv 64 470752) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) -> G (mkst regs (0x18d00 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100888))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602632))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H12 H17 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { stepb_tk TF_18d00 TD_18d00 ltac:(pin; cond_compute).  (* 0x18d00 beqz a7, 0x18d38 <static_init_tls+0x110> *)
      ld_step TF_18d38 TD_18d38 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_92f98_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18d38 ld a2, 0x10(a1) *)
      ld_step TF_18d3c TD_18d3c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_92fa8_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18d3c ld a3, 0x20(a1) *)
      ld_step TF_18d40 TD_18d40 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_92fb0_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18d40 ld a0, 0x28(a1) *)
      sn TF_18d44 TD_18d44.  (* 0x18d44 add a4, a3, a2 *)
      sn TF_18d48 TD_18d48.  (* 0x18d48 addi a5, a0, -0x1 *)
      sn TF_18d4c TD_18d4c.  (* 0x18d4c neg a4, a4 *)
      sn TF_18d50 TD_18d50.  (* 0x18d50 and a2, a5, a2 *)
      sn TF_18d54 TD_18d54.  (* 0x18d54 and a4, a5, a4 *)
      sn TF_18d58 TD_18d58.  (* 0x18d58 li a5, 0x7 *)
      sn TF_18d5c TD_18d5c.  (* 0x18d5c add a3, a4, a3 *)
      stw TF_18d60 TD_18d60 (Z_to_bv 64 602024) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x18d60 sd a3, 0x20(a1) *)
      stw TF_18d64 TD_18d64 (Z_to_bv 64 602040) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x18d64 sd a2, 0x30(a1) *)
      stepb_ft TF_18d68 TD_18d68 ltac:(pin; cond_compute).  (* 0x18d68 bltu a5, a0, 0x18d74 <static_init_tls+0x14c> *)
      sn TF_18d6c TD_18d6c.  (* 0x18d6c li a0, 0x8 *)
      stw TF_18d70 TD_18d70 (Z_to_bv 64 602032) (Z_to_bv 64 8) ltac:(ok_data).  (* 0x18d70 sd a0, 0x28(a1) *)
      sn TF_18d74 TD_18d74.  (* 0x18d74 add a2, a2, a3 *)
      sn TF_18d78 TD_18d78.  (* 0x18d78 lui a1, 0x20 *)
      sn TF_18d7c TD_18d7c.  (* 0x18d7c add a2, a2, a0 *)
      sn TF_18d80 TD_18d80.  (* 0x18d80 addiw a3, a1, 0xd1 *)
      sn TF_18d84 TD_18d84.  (* 0x18d84 addi a1, a2, 0xdf *)
      sn TF_18d88 TD_18d88.  (* 0x18d88 andi a1, a1, -0x8 *)
      stw TF_18d8c TD_18d8c (Z_to_bv 64 602656) (Z_to_bv 64 224) ltac:(ok_data).  (* 0x18d8c sd a1, 0x18(s1) *)
      stw TF_18d90 TD_18d90 (Z_to_bv 64 602664) (Z_to_bv 64 8) ltac:(ok_data).  (* 0x18d90 sd a0, 0x20(s1) *)
      stepb_tk TF_18d94 TD_18d94 ltac:(pin; cond_compute).  (* 0x18d94 bltu a1, a3, 0x18dc8 <static_init_tls+0x1a0> *)
      sn TF_18dc8 TD_18dc8.  (* 0x18dc8 auipc a3, 0x5a *)
      ld_step TF_18dcc TD_18dcc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_93218_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18dcc ld s3, 0x10(s1) *)
      ld_step TF_18dd0 TD_18dd0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_93230_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18dd0 ld a2, 0x28(s1) *)
      sn TF_18dd4 TD_18dd4.  (* 0x18dd4 addi a4, a0, -0x1 *)
      sn TF_18dd8 TD_18dd8.  (* 0x18dd8 li a5, -0xc8 *)
      sn TF_18ddc TD_18ddc.  (* 0x18ddc addi a0, a3, 0xf0 *)
      sn TF_18de0 TD_18de0.  (* 0x18de0 sub a5, a5, a0 *)
      sn TF_18de4 TD_18de4.  (* 0x18de4 and a4, a4, a5 *)
      sn TF_18de8 TD_18de8.  (* 0x18de8 not a3, a2 *)
      sn TF_18dec TD_18dec.  (* 0x18dec add s2, a0, a4 *)
      sn TF_18df0 TD_18df0.  (* 0x18df0 slli a3, a3, 0x3 *)
      sn TF_18df4 TD_18df4.  (* 0x18df4 add a3, a0, a3 *)
      sn TF_18df8 TD_18df8.  (* 0x18df8 add s4, a3, a1 *)
      sn TF_18dfc TD_18dfc.  (* 0x18dfc addi s0, s2, 0xc8 *)
      stepb_tk TF_18e00 TD_18e00 ltac:(pin; cond_compute).  (* 0x18e00 beqz s3, 0x18e48 <static_init_tls+0x220> *)
      stw TF_18e48 TD_18e48 (Z_to_bv 64 470928) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x18e48 sd a2, 0x0(s4) *)
      stw TF_18e4c TD_18e4c (Z_to_bv 64 470904) (Z_to_bv 64 470928) ltac:(ok_data).  (* 0x18e4c sd s4, 0xc0(s2) *)
      stw TF_18e50 TD_18e50 (Z_to_bv 64 470712) (Z_to_bv 64 470712) ltac:(ok_data).  (* 0x18e50 sd s2, 0x0(s2) *)
      sn TF_18e54 TD_18e54.  (* 0x18e54 mv a0, s0 *)
      sn TF_18e58 TD_18e58.  (* 0x18e58 jal 0x20ab4 <__set_thread_area> *)
      sn F_20984 D_20984.  (* 0x20ab4 mv tp, a0 *)
      sn F_20988 D_20988.  (* 0x20ab8 li a0, 0x0 *)
      stepret F_2098c D_2098c (0x18e5c : word) ltac:(pin; first [reflexivity | bveq]).  (* 0x20abc ret *)
      stepb_ft TF_18e5c TD_18e5c ltac:(pin; cond_compute).  (* 0x18e5c bltz a0, 0x18eb0 <static_init_tls+0x288> *)
      stepb_ft TF_18e60 TD_18e60 ltac:(pin; cond_compute).  (* 0x18e60 bnez a0, 0x18e6c <static_init_tls+0x244> *)
      sn TF_18e64 TD_18e64.  (* 0x18e64 li a0, 0x1 *)
      stw TF_18e68 TD_18e68 (Z_to_bv 64 602632) (Z_to_bv 64 1) ltac:(ok_data).  (* 0x18e68 sb a0, 0x0(s1) *)
      sn TF_18e6c TD_18e6c.  (* 0x18e6c li a0, 0x2 *)
      sn TF_18e70 TD_18e70.  (* 0x18e70 auipc a1, 0x7a *)
      stw TF_18e74 TD_18e74 (Z_to_bv 64 470752) (Z_to_bv 64 2) ltac:(ok_data).  (* 0x18e74 sw a0, 0x28(s2) *)
      sn TF_18e78 TD_18e78.  (* 0x18e78 li a7, 0x60 *)
      sn TF_18e7c TD_18e7c.  (* 0x18e7c addi a0, a1, 0x118 *)
      sn TF_18e80 TD_18e80.  (* 0x18e80 addi a1, s1, 0x38 *)
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { stepb_tk TF_18d00 TD_18d00 ltac:(pin; cond_compute).  (* 0x18d00 beqz a7, 0x18d38 <static_init_tls+0x110> *)
      ld_step TF_18d38 TD_18d38 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_92f98_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18d38 ld a2, 0x10(a1) *)
      ld_step TF_18d3c TD_18d3c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_92fa8_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18d3c ld a3, 0x20(a1) *)
      ld_step TF_18d40 TD_18d40 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_92fb0_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18d40 ld a0, 0x28(a1) *)
      sn TF_18d44 TD_18d44.  (* 0x18d44 add a4, a3, a2 *)
      sn TF_18d48 TD_18d48.  (* 0x18d48 addi a5, a0, -0x1 *)
      sn TF_18d4c TD_18d4c.  (* 0x18d4c neg a4, a4 *)
      sn TF_18d50 TD_18d50.  (* 0x18d50 and a2, a5, a2 *)
      sn TF_18d54 TD_18d54.  (* 0x18d54 and a4, a5, a4 *)
      sn TF_18d58 TD_18d58.  (* 0x18d58 li a5, 0x7 *)
      sn TF_18d5c TD_18d5c.  (* 0x18d5c add a3, a4, a3 *)
      stw TF_18d60 TD_18d60 (Z_to_bv 64 602024) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x18d60 sd a3, 0x20(a1) *)
      stw TF_18d64 TD_18d64 (Z_to_bv 64 602040) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x18d64 sd a2, 0x30(a1) *)
      stepb_ft TF_18d68 TD_18d68 ltac:(pin; cond_compute).  (* 0x18d68 bltu a5, a0, 0x18d74 <static_init_tls+0x14c> *)
      sn TF_18d6c TD_18d6c.  (* 0x18d6c li a0, 0x8 *)
      stw TF_18d70 TD_18d70 (Z_to_bv 64 602032) (Z_to_bv 64 8) ltac:(ok_data).  (* 0x18d70 sd a0, 0x28(a1) *)
      sn TF_18d74 TD_18d74.  (* 0x18d74 add a2, a2, a3 *)
      sn TF_18d78 TD_18d78.  (* 0x18d78 lui a1, 0x20 *)
      sn TF_18d7c TD_18d7c.  (* 0x18d7c add a2, a2, a0 *)
      sn TF_18d80 TD_18d80.  (* 0x18d80 addiw a3, a1, 0xd1 *)
      sn TF_18d84 TD_18d84.  (* 0x18d84 addi a1, a2, 0xdf *)
      sn TF_18d88 TD_18d88.  (* 0x18d88 andi a1, a1, -0x8 *)
      stw TF_18d8c TD_18d8c (Z_to_bv 64 602656) (Z_to_bv 64 224) ltac:(ok_data).  (* 0x18d8c sd a1, 0x18(s1) *)
      stw TF_18d90 TD_18d90 (Z_to_bv 64 602664) (Z_to_bv 64 8) ltac:(ok_data).  (* 0x18d90 sd a0, 0x20(s1) *)
      stepb_tk TF_18d94 TD_18d94 ltac:(pin; cond_compute).  (* 0x18d94 bltu a1, a3, 0x18dc8 <static_init_tls+0x1a0> *)
      sn TF_18dc8 TD_18dc8.  (* 0x18dc8 auipc a3, 0x5a *)
      ld_step TF_18dcc TD_18dcc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_93218_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18dcc ld s3, 0x10(s1) *)
      ld_step TF_18dd0 TD_18dd0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_93230_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18dd0 ld a2, 0x28(s1) *)
      sn TF_18dd4 TD_18dd4.  (* 0x18dd4 addi a4, a0, -0x1 *)
      sn TF_18dd8 TD_18dd8.  (* 0x18dd8 li a5, -0xc8 *)
      sn TF_18ddc TD_18ddc.  (* 0x18ddc addi a0, a3, 0xf0 *)
      sn TF_18de0 TD_18de0.  (* 0x18de0 sub a5, a5, a0 *)
      sn TF_18de4 TD_18de4.  (* 0x18de4 and a4, a4, a5 *)
      sn TF_18de8 TD_18de8.  (* 0x18de8 not a3, a2 *)
      sn TF_18dec TD_18dec.  (* 0x18dec add s2, a0, a4 *)
      sn TF_18df0 TD_18df0.  (* 0x18df0 slli a3, a3, 0x3 *)
      sn TF_18df4 TD_18df4.  (* 0x18df4 add a3, a0, a3 *)
      sn TF_18df8 TD_18df8.  (* 0x18df8 add s4, a3, a1 *)
      sn TF_18dfc TD_18dfc.  (* 0x18dfc addi s0, s2, 0xc8 *)
      stepb_tk TF_18e00 TD_18e00 ltac:(pin; cond_compute).  (* 0x18e00 beqz s3, 0x18e48 <static_init_tls+0x220> *)
      stw TF_18e48 TD_18e48 (Z_to_bv 64 470928) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x18e48 sd a2, 0x0(s4) *)
      stw TF_18e4c TD_18e4c (Z_to_bv 64 470904) (Z_to_bv 64 470928) ltac:(ok_data).  (* 0x18e4c sd s4, 0xc0(s2) *)
      stw TF_18e50 TD_18e50 (Z_to_bv 64 470712) (Z_to_bv 64 470712) ltac:(ok_data).  (* 0x18e50 sd s2, 0x0(s2) *)
      sn TF_18e54 TD_18e54.  (* 0x18e54 mv a0, s0 *)
      sn TF_18e58 TD_18e58.  (* 0x18e58 jal 0x20ab4 <__set_thread_area> *)
      sn F_20984 D_20984.  (* 0x20ab4 mv tp, a0 *)
      sn F_20988 D_20988.  (* 0x20ab8 li a0, 0x0 *)
      stepret F_2098c D_2098c (0x18e5c : word) ltac:(pin; first [reflexivity | bveq]).  (* 0x20abc ret *)
      stepb_ft TF_18e5c TD_18e5c ltac:(pin; cond_compute).  (* 0x18e5c bltz a0, 0x18eb0 <static_init_tls+0x288> *)
      stepb_ft TF_18e60 TD_18e60 ltac:(pin; cond_compute).  (* 0x18e60 bnez a0, 0x18e6c <static_init_tls+0x244> *)
      sn TF_18e64 TD_18e64.  (* 0x18e64 li a0, 0x1 *)
      stw TF_18e68 TD_18e68 (Z_to_bv 64 602632) (Z_to_bv 64 1) ltac:(ok_data).  (* 0x18e68 sb a0, 0x0(s1) *)
      sn TF_18e6c TD_18e6c.  (* 0x18e6c li a0, 0x2 *)
      sn TF_18e70 TD_18e70.  (* 0x18e70 auipc a1, 0x7a *)
      stw TF_18e74 TD_18e74 (Z_to_bv 64 470752) (Z_to_bv 64 2) ltac:(ok_data).  (* 0x18e74 sw a0, 0x28(s2) *)
      sn TF_18e78 TD_18e78.  (* 0x18e78 li a7, 0x60 *)
      sn TF_18e7c TD_18e7c.  (* 0x18e7c addi a0, a1, 0x118 *)
      sn TF_18e80 TD_18e80.  (* 0x18e80 addi a1, s1, 0x38 *)
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma tls_c5 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word), wfJ sp0 Jb -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) -> getr regs 3 = Z_to_bv 64 67584 -> getr regs 4 = Z_to_bv 64 470912 -> getr regs 10 = tid -> getr regs 11 = Z_to_bv 64 602688 -> getr regs 18 = Z_to_bv 64 470712 -> getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 0 -> getr regs 25 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 0 -> getr regs 27 = Z_to_bv 64 0 -> (forall regs', getr regs' 1 = (Z_to_bv 64 100888) -> getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) -> getr regs' 3 = (Z_to_bv 64 67584) -> getr regs' 4 = (Z_to_bv 64 470912) -> getr regs' 8 = (pn_w inp rdraw) -> getr regs' 9 = (s1v) -> getr regs' 10 = (Z_to_bv 64 0) -> getr regs' 12 = (Z_to_bv 64 470832) -> getr regs' 18 = (Z_to_bv 64 602632) -> getr regs' 19 = (Z_to_bv 64 0) -> getr regs' 20 = (Z_to_bv 64 0) -> getr regs' 21 = (Z_to_bv 64 0) -> getr regs' 22 = (Z_to_bv 64 0) -> getr regs' 23 = (Z_to_bv 64 0) -> getr regs' 24 = (Z_to_bv 64 0) -> getr regs' 25 = (Z_to_bv 64 0) -> getr regs' 26 = (Z_to_bv 64 0) -> getr regs' 27 = (Z_to_bv 64 0) -> regs_agree (fun r => In r [1; 2; 8; 9; 10; 12; 18; 19; 20; 21]%list) regs regs' -> G (mkst regs' (0x18a18 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100888))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602632))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602024) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602040) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602032) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602656) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602664) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 470928) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 470904) (word_to_le_bytes 8 (Z_to_bv 64 470928))) (Z_to_bv 64 470712) (word_to_le_bytes 8 (Z_to_bv 64 470712))) (Z_to_bv 64 602632) ([Z_to_bv 8 1])) (Z_to_bv 64 470752) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470744) (word_to_le_bytes 4 tid)) (Z_to_bv 64 470864) (word_to_le_bytes 8 (Z_to_bv 64 602688))) (Z_to_bv 64 470832) (word_to_le_bytes 8 (Z_to_bv 64 470832))) (Z_to_bv 64 470720) (word_to_le_bytes 8 (Z_to_bv 64 470712))) (Z_to_bv 64 470728) (word_to_le_bytes 8 (Z_to_bv 64 470712))) (Z_to_bv 64 470736) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) -> G (mkst regs (0x18e88 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100888))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602632))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602024) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602040) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602032) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602656) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602664) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 470928) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 470904) (word_to_le_bytes 8 (Z_to_bv 64 470928))) (Z_to_bv 64 470712) (word_to_le_bytes 8 (Z_to_bv 64 470712))) (Z_to_bv 64 602632) ([Z_to_bv 8 1])) (Z_to_bv 64 470752) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { sn TF_18e88 TD_18e88.  (* 0x18e88 addi a2, s2, 0x78 *)
      stw TF_18e8c TD_18e8c (Z_to_bv 64 470744) (tid) ltac:(ok_data).  (* 0x18e8c sw a0, 0x20(s2) *)
      stw TF_18e90 TD_18e90 (Z_to_bv 64 470864) (Z_to_bv 64 602688) ltac:(ok_data).  (* 0x18e90 sd a1, 0x98(s2) *)
      stw TF_18e94 TD_18e94 (Z_to_bv 64 470832) (Z_to_bv 64 470832) ltac:(ok_data).  (* 0x18e94 sd a2, 0x78(s2) *)
      sn TF_18e98 TD_18e98.  (* 0x18e98 auipc a0, 0x7a *)
      ld_step TF_18e9c TD_18e9c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_931f0_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18e9c ld a0, 0x358(a0) *)
      stw TF_18ea0 TD_18ea0 (Z_to_bv 64 470720) (Z_to_bv 64 470712) ltac:(ok_data).  (* 0x18ea0 sd s2, 0x8(s2) *)
      stw TF_18ea4 TD_18ea4 (Z_to_bv 64 470728) (Z_to_bv 64 470712) ltac:(ok_data).  (* 0x18ea4 sd s2, 0x10(s2) *)
      stw TF_18ea8 TD_18ea8 (Z_to_bv 64 470736) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x18ea8 sd a0, 0x18(s2) *)
      sn TF_18eac TD_18eac.  (* 0x18eac j 0x18eb4 <static_init_tls+0x28c> *)
      ld_step TF_18eb4 TD_18eb4 (word_to_le_bytes 8 (Z_to_bv 64 100888)) (Z_to_bv 64 100888) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18eb4 ld ra, 0x38(sp) *)
      ld_step TF_18eb8 TD_18eb8 (word_to_le_bytes 8 (pn_w inp rdraw)) (pn_w inp rdraw) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18eb8 ld s0, 0x30(sp) *)
      ld_step TF_18ebc TD_18ebc (word_to_le_bytes 8 s1v) (s1v) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18ebc ld s1, 0x28(sp) *)
      ld_step TF_18ec0 TD_18ec0 (word_to_le_bytes 8 (Z_to_bv 64 602632)) (Z_to_bv 64 602632) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18ec0 ld s2, 0x20(sp) *)
      ld_step TF_18ec4 TD_18ec4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18ec4 ld s3, 0x18(sp) *)
      ld_step TF_18ec8 TD_18ec8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18ec8 ld s4, 0x10(sp) *)
      ld_step TF_18ecc TD_18ecc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18ecc ld s5, 0x8(sp) *)
      sv TF_18ed0 TD_18ed0 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* 0x18ed0 addi sp, sp, 0x40 *)
      stepret TF_18ed4 TD_18ed4 (0x18a18 : word) ltac:(pin; first [reflexivity | bveq]).  (* 0x18ed4 ret *)
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { sn TF_18e88 TD_18e88.  (* 0x18e88 addi a2, s2, 0x78 *)
      stw TF_18e8c TD_18e8c (Z_to_bv 64 470744) (tid) ltac:(ok_data).  (* 0x18e8c sw a0, 0x20(s2) *)
      stw TF_18e90 TD_18e90 (Z_to_bv 64 470864) (Z_to_bv 64 602688) ltac:(ok_data).  (* 0x18e90 sd a1, 0x98(s2) *)
      stw TF_18e94 TD_18e94 (Z_to_bv 64 470832) (Z_to_bv 64 470832) ltac:(ok_data).  (* 0x18e94 sd a2, 0x78(s2) *)
      sn TF_18e98 TD_18e98.  (* 0x18e98 auipc a0, 0x7a *)
      ld_step TF_18e9c TD_18e9c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_931f0_8) ltac:(apply bytes_le_to_Z_8).  (* 0x18e9c ld a0, 0x358(a0) *)
      stw TF_18ea0 TD_18ea0 (Z_to_bv 64 470720) (Z_to_bv 64 470712) ltac:(ok_data).  (* 0x18ea0 sd s2, 0x8(s2) *)
      stw TF_18ea4 TD_18ea4 (Z_to_bv 64 470728) (Z_to_bv 64 470712) ltac:(ok_data).  (* 0x18ea4 sd s2, 0x10(s2) *)
      stw TF_18ea8 TD_18ea8 (Z_to_bv 64 470736) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x18ea8 sd a0, 0x18(s2) *)
      sn TF_18eac TD_18eac.  (* 0x18eac j 0x18eb4 <static_init_tls+0x28c> *)
      ld_step TF_18eb4 TD_18eb4 (word_to_le_bytes 8 (Z_to_bv 64 100888)) (Z_to_bv 64 100888) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18eb4 ld ra, 0x38(sp) *)
      ld_step TF_18eb8 TD_18eb8 (word_to_le_bytes 8 (pn_w inp rdraw)) (pn_w inp rdraw) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18eb8 ld s0, 0x30(sp) *)
      ld_step TF_18ebc TD_18ebc (word_to_le_bytes 8 s1v) (s1v) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18ebc ld s1, 0x28(sp) *)
      ld_step TF_18ec0 TD_18ec0 (word_to_le_bytes 8 (Z_to_bv 64 602632)) (Z_to_bv 64 602632) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18ec0 ld s2, 0x20(sp) *)
      ld_step TF_18ec4 TD_18ec4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18ec4 ld s3, 0x18(sp) *)
      ld_step TF_18ec8 TD_18ec8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18ec8 ld s4, 0x10(sp) *)
      ld_step TF_18ecc TD_18ecc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x18ecc ld s5, 0x8(sp) *)
      sv TF_18ed0 TD_18ed0 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* 0x18ed0 addi sp, sp, 0x40 *)
      stepret TF_18ed4 TD_18ed4 (0x18a18 : word) ltac:(pin; first [reflexivity | bveq]).  (* 0x18ed4 ret *)
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

End P4.
