(* elf , front , img own, defs ,
   statements (TEMPLATE; synthesized from the run), context , conventions ;
   valtac4: 'reflexivity' from 'WalkTac.v stepld_pc value side; S0Startup2.v F_152d4'; split-rseq all. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import StartupTac ArgvEnv RefLayout U9StartupDefs U9_code_19000_1a000 U9_code_1a000_1b000 U9_code_21000_21d44.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import LiaFast.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require L10Walk.
Ltac OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac.chain_step ::= OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_chain_step.
Abbreviation SEGS := Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments.
Abbreviation RPH := Tgt_zlib_uncompress_fuzzer_ubsan.M.phdrs.
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
Lemma s2img_22e48_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 142920) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_240e0_4 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 147680) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
Lemma s2img_94258_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 606808) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_94268_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 606824) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_94270_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 606832) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_944b0_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 607408) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_944d8_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 607448) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_944f0_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 607472) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
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
Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH (Z_to_bv 64 (Z.of_N Tgt_zlib_uncompress_fuzzer_ubsan.M.init_pc)) sp0 rdraw)) (only parsing).

  Lemma tls_c1 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word), wfJ sp0 Jb -> getr regs 1 = Z_to_bv 64 105688 -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) -> getr regs 3 = Z_to_bv 64 67584 -> getr regs 8 = pn_w inp rdraw -> getr regs 9 = s1v -> getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) -> getr regs 18 = Z_to_bv 64 607432 -> getr regs 19 = Z_to_bv 64 0 -> getr regs 20 = Z_to_bv 64 0 -> getr regs 21 = Z_to_bv 64 0 -> getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 0 -> getr regs 25 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 0 -> getr regs 27 = Z_to_bv 64 0 -> (forall regs', getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) -> getr regs' 3 = (Z_to_bv 64 67584) -> getr regs' 5 = (Z_to_bv 64 0) -> getr regs' 7 = (Z_to_bv 64 7) -> getr regs' 9 = (Z_to_bv 64 607432) -> getr regs' 10 = (Z_to_bv 64 56) -> getr regs' 11 = (Z_to_bv 64 606792) -> getr regs' 12 = (Z_to_bv 64 0) -> getr regs' 13 = (Z_to_bv 64 10) -> getr regs' 15 = (Z_to_bv 64 65600) -> getr regs' 16 = (Z_to_bv 64 6) -> getr regs' 17 = (Z_to_bv 64 0) -> getr regs' 22 = (Z_to_bv 64 0) -> getr regs' 23 = (Z_to_bv 64 0) -> getr regs' 24 = (Z_to_bv 64 0) -> getr regs' 25 = (Z_to_bv 64 0) -> getr regs' 26 = (Z_to_bv 64 0) -> getr regs' 27 = (Z_to_bv 64 0) -> getr regs' 28 = (Z_to_bv 64 1685382481) -> getr regs' 29 = (Z_to_bv 64 65600) -> getr regs' 30 = (Z_to_bv 64 131072) -> regs_agree (fun r => In r [2; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30]%list) regs regs' -> G (mkst regs' (0x19f70 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105688))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607432))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom)) -> G (mkst regs (0x19ee8 : word) (CM (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (D_libc sp0 inp rdraw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { sv F_19e00 D_19e00 (Z_to_bv 64 (bv_unsigned sp0 - 480)).  (* 0x19ee8 addi sp, sp, -0x40 *)
      stw TF_19eec TD_19eec (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 105688) ltac:(ok_win HJ).  (* 0x19eec sd ra, 0x38(sp) *)
      stw TF_19ef0 TD_19ef0 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w inp rdraw) ltac:(ok_win HJ).  (* 0x19ef0 sd s0, 0x30(sp) *)
      stw TF_19ef4 TD_19ef4 (Z_to_bv 64 (bv_unsigned sp0 - 440)) (s1v) ltac:(ok_win HJ).  (* 0x19ef4 sd s1, 0x28(sp) *)
      stw TF_19ef8 TD_19ef8 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 607432) ltac:(ok_win HJ).  (* 0x19ef8 sd s2, 0x20(sp) *)
      stw TF_19efc TD_19efc (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x19efc sd s3, 0x18(sp) *)
      stw TF_19f00 TD_19f00 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x19f00 sd s4, 0x10(sp) *)
      stw TF_19f04 TD_19f04 (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x19f04 sd s5, 0x8(sp) *)
      ld_step TF_19f08 TD_19f08 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x19f08 ld a3, 0x28(a0) *)
      sn TF_19f0c TD_19f0c.  (* 0x19f0c auipc a1, 0x7a *)
      sn TF_19f10 TD_19f10.  (* 0x19f10 addi a1, a1, 0x33c *)
      sn TF_19f14 TD_19f14.  (* 0x19f14 auipc a2, 0x7a *)
      sn TF_19f18 TD_19f18.  (* 0x19f18 addi s1, a2, 0x5b4 *)
      stepb_ft TF_19f1c TD_19f1c ltac:(pin; cond_compute).  (* 0x19f1c beqz a3, 0x19ff8 <static_init_tls+0x110> *)
      sn TF_19f20 TD_19f20.  (* 0x19f20 li a2, 0x0 *)
      sn TF_19f24 TD_19f24.  (* 0x19f24 li a7, 0x0 *)
      sn TF_19f28 TD_19f28.  (* 0x19f28 auipc a4, 0xa *)
      ld_step TF_19f2c TD_19f2c (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x19f2c ld a5, 0x18(a0) *)
      ld_step TF_19f30 TD_19f30 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x19f30 ld a0, 0x20(a0) *)
      sn TF_19f34 TD_19f34.  (* 0x19f34 li a6, 0x6 *)
      sn TF_19f38 TD_19f38.  (* 0x19f38 auipc t0, 0x9 *)
      ld_step TF_19f3c TD_19f3c (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img s2img_240e0_4) ltac:(reflexivity).  (* 0x19f3c lwu t5, 0x1b8(a4) *)
      ld_step TF_19f40 TD_19f40 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_22e48_8) ltac:(apply bytes_le_to_Z_8).  (* 0x19f40 ld t0, -0xf0(t0) *)
      sn TF_19f44 TD_19f44.  (* 0x19f44 li t1, 0x2 *)
      sn TF_19f48 TD_19f48.  (* 0x19f48 li t2, 0x7 *)
      sn TF_19f4c TD_19f4c.  (* 0x19f4c lui t3, 0x6474e *)
      sn TF_19f50 TD_19f50.  (* 0x19f50 addiw t3, t3, 0x551 *)
      sn TF_19f54 TD_19f54.  (* 0x19f54 mv t4, a5 *)
      sn TF_19f58 TD_19f58.  (* 0x19f58 j 0x19f70 <static_init_tls+0x88> *)
      OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { sv F_19e00 D_19e00 (Z_to_bv 64 (bv_unsigned sp0 - 480)).  (* 0x19ee8 addi sp, sp, -0x40 *)
      stw TF_19eec TD_19eec (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 105688) ltac:(ok_win HJ).  (* 0x19eec sd ra, 0x38(sp) *)
      stw TF_19ef0 TD_19ef0 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w inp rdraw) ltac:(ok_win HJ).  (* 0x19ef0 sd s0, 0x30(sp) *)
      stw TF_19ef4 TD_19ef4 (Z_to_bv 64 (bv_unsigned sp0 - 440)) (s1v) ltac:(ok_win HJ).  (* 0x19ef4 sd s1, 0x28(sp) *)
      stw TF_19ef8 TD_19ef8 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 607432) ltac:(ok_win HJ).  (* 0x19ef8 sd s2, 0x20(sp) *)
      stw TF_19efc TD_19efc (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x19efc sd s3, 0x18(sp) *)
      stw TF_19f00 TD_19f00 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x19f00 sd s4, 0x10(sp) *)
      stw TF_19f04 TD_19f04 (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x19f04 sd s5, 0x8(sp) *)
      ld_step TF_19f08 TD_19f08 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x19f08 ld a3, 0x28(a0) *)
      sn TF_19f0c TD_19f0c.  (* 0x19f0c auipc a1, 0x7a *)
      sn TF_19f10 TD_19f10.  (* 0x19f10 addi a1, a1, 0x33c *)
      sn TF_19f14 TD_19f14.  (* 0x19f14 auipc a2, 0x7a *)
      sn TF_19f18 TD_19f18.  (* 0x19f18 addi s1, a2, 0x5b4 *)
      stepb_ft TF_19f1c TD_19f1c ltac:(pin; cond_compute).  (* 0x19f1c beqz a3, 0x19ff8 <static_init_tls+0x110> *)
      sn TF_19f20 TD_19f20.  (* 0x19f20 li a2, 0x0 *)
      sn TF_19f24 TD_19f24.  (* 0x19f24 li a7, 0x0 *)
      sn TF_19f28 TD_19f28.  (* 0x19f28 auipc a4, 0xa *)
      ld_step TF_19f2c TD_19f2c (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x19f2c ld a5, 0x18(a0) *)
      ld_step TF_19f30 TD_19f30 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x19f30 ld a0, 0x20(a0) *)
      sn TF_19f34 TD_19f34.  (* 0x19f34 li a6, 0x6 *)
      sn TF_19f38 TD_19f38.  (* 0x19f38 auipc t0, 0x9 *)
      ld_step TF_19f3c TD_19f3c (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img s2img_240e0_4) ltac:(reflexivity).  (* 0x19f3c lwu t5, 0x1b8(a4) *)
      ld_step TF_19f40 TD_19f40 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_22e48_8) ltac:(apply bytes_le_to_Z_8).  (* 0x19f40 ld t0, -0xf0(t0) *)
      sn TF_19f44 TD_19f44.  (* 0x19f44 li t1, 0x2 *)
      sn TF_19f48 TD_19f48.  (* 0x19f48 li t2, 0x7 *)
      sn TF_19f4c TD_19f4c.  (* 0x19f4c lui t3, 0x6474e *)
      sn TF_19f50 TD_19f50.  (* 0x19f50 addiw t3, t3, 0x551 *)
      sn TF_19f54 TD_19f54.  (* 0x19f54 mv t4, a5 *)
      sn TF_19f58 TD_19f58.  (* 0x19f58 j 0x19f70 <static_init_tls+0x88> *)
      OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma tls_c2 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word), wfJ sp0 Jb -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) -> getr regs 3 = Z_to_bv 64 67584 -> getr regs 5 = Z_to_bv 64 0 -> getr regs 7 = Z_to_bv 64 7 -> getr regs 9 = Z_to_bv 64 607432 -> getr regs 10 = Z_to_bv 64 56 -> getr regs 11 = Z_to_bv 64 606792 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 10 -> getr regs 15 = Z_to_bv 64 65600 -> getr regs 16 = Z_to_bv 64 6 -> getr regs 17 = Z_to_bv 64 0 -> getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 0 -> getr regs 25 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 0 -> getr regs 27 = Z_to_bv 64 0 -> getr regs 28 = Z_to_bv 64 1685382481 -> getr regs 29 = Z_to_bv 64 65600 -> getr regs 30 = Z_to_bv 64 131072 -> (forall regs', getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) -> getr regs' 3 = (Z_to_bv 64 67584) -> getr regs' 5 = (Z_to_bv 64 0) -> getr regs' 7 = (Z_to_bv 64 7) -> getr regs' 9 = (Z_to_bv 64 607432) -> getr regs' 10 = (Z_to_bv 64 56) -> getr regs' 11 = (Z_to_bv 64 606792) -> getr regs' 12 = (Z_to_bv 64 0) -> getr regs' 13 = (Z_to_bv 64 5) -> getr regs' 16 = (Z_to_bv 64 6) -> getr regs' 17 = (Z_to_bv 64 0) -> getr regs' 22 = (Z_to_bv 64 0) -> getr regs' 23 = (Z_to_bv 64 0) -> getr regs' 24 = (Z_to_bv 64 0) -> getr regs' 25 = (Z_to_bv 64 0) -> getr regs' 26 = (Z_to_bv 64 0) -> getr regs' 27 = (Z_to_bv 64 0) -> getr regs' 28 = (Z_to_bv 64 1685382481) -> getr regs' 29 = (Z_to_bv 64 65880) -> getr regs' 30 = (Z_to_bv 64 131072) -> regs_agree (fun r => In r [8; 12; 13; 17; 29; 31]%list) regs regs' -> G (mkst regs' (0x19f70 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105688))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607432))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom)) -> G (mkst regs (0x19f70 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105688))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607432))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H12 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { ld_step TF_19f70 TD_19f70 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img s2img_10040_4) ltac:(reflexivity).  (* 0x19f70 lw s0, 0x0(t4) *)
      stepb_tk TF_19f74 TD_19f74 ltac:(pin; cond_compute).  (* 0x19f74 beq s0, a6, 0x19f5c <static_init_tls+0x74> *)
      ld_step TF_19f5c TD_19f5c (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img s2img_10050_8) ltac:(apply bytes_le_to_Z_8).  (* 0x19f5c ld a2, 0x10(t4) *)
      sn TF_19f60 TD_19f60.  (* 0x19f60 sub a2, a5, a2 *)
      sn TF_19f64 TD_19f64.  (* 0x19f64 addi a3, a3, -0x1 *)
      sn TF_19f68 TD_19f68.  (* 0x19f68 add t4, t4, a0 *)
      stepb_ft TF_19f6c TD_19f6c ltac:(pin; cond_compute).  (* 0x19f6c beqz a3, 0x19fc0 <static_init_tls+0xd8> *)
      ld_step TF_19f70 TD_19f70 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_10078_4) ltac:(reflexivity).  (* 0x19f70 lw s0, 0x0(t4) *)
      stepb_ft TF_19f74 TD_19f74 ltac:(pin; cond_compute).  (* 0x19f74 beq s0, a6, 0x19f5c <static_init_tls+0x74> *)
      stepb_tk TF_19f78 TD_19f78 ltac:(pin; cond_compute).  (* 0x19f78 beqz t0, 0x19f8c <static_init_tls+0xa4> *)
      sn TF_19f8c TD_19f8c.  (* 0x19f8c mv t6, t4 *)
      stepb_ft TF_19f90 TD_19f90 ltac:(pin; cond_compute).  (* 0x19f90 beq s0, t2, 0x19f98 <static_init_tls+0xb0> *)
      sn TF_19f94 TD_19f94.  (* 0x19f94 mv t6, a7 *)
      stepb_tk TF_19f98 TD_19f98 ltac:(pin; cond_compute).  (* 0x19f98 bne s0, t3, 0x19fb8 <static_init_tls+0xd0> *)
      sn TF_19fb8 TD_19fb8.  (* 0x19fb8 mv a7, t6 *)
      sn TF_19fbc TD_19fbc.  (* 0x19fbc j 0x19f64 <static_init_tls+0x7c> *)
      sn TF_19f64 TD_19f64.  (* 0x19f64 addi a3, a3, -0x1 *)
      sn TF_19f68 TD_19f68.  (* 0x19f68 add t4, t4, a0 *)
      stepb_ft TF_19f6c TD_19f6c ltac:(pin; cond_compute).  (* 0x19f6c beqz a3, 0x19fc0 <static_init_tls+0xd8> *)
      ld_step TF_19f70 TD_19f70 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_100b0_4) ltac:(reflexivity).  (* 0x19f70 lw s0, 0x0(t4) *)
      stepb_ft TF_19f74 TD_19f74 ltac:(pin; cond_compute).  (* 0x19f74 beq s0, a6, 0x19f5c <static_init_tls+0x74> *)
      stepb_tk TF_19f78 TD_19f78 ltac:(pin; cond_compute).  (* 0x19f78 beqz t0, 0x19f8c <static_init_tls+0xa4> *)
      sn TF_19f8c TD_19f8c.  (* 0x19f8c mv t6, t4 *)
      stepb_ft TF_19f90 TD_19f90 ltac:(pin; cond_compute).  (* 0x19f90 beq s0, t2, 0x19f98 <static_init_tls+0xb0> *)
      sn TF_19f94 TD_19f94.  (* 0x19f94 mv t6, a7 *)
      stepb_tk TF_19f98 TD_19f98 ltac:(pin; cond_compute).  (* 0x19f98 bne s0, t3, 0x19fb8 <static_init_tls+0xd0> *)
      sn TF_19fb8 TD_19fb8.  (* 0x19fb8 mv a7, t6 *)
      sn TF_19fbc TD_19fbc.  (* 0x19fbc j 0x19f64 <static_init_tls+0x7c> *)
      sn TF_19f64 TD_19f64.  (* 0x19f64 addi a3, a3, -0x1 *)
      sn TF_19f68 TD_19f68.  (* 0x19f68 add t4, t4, a0 *)
      stepb_ft TF_19f6c TD_19f6c ltac:(pin; cond_compute).  (* 0x19f6c beqz a3, 0x19fc0 <static_init_tls+0xd8> *)
      ld_step TF_19f70 TD_19f70 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_100e8_4) ltac:(reflexivity).  (* 0x19f70 lw s0, 0x0(t4) *)
      stepb_ft TF_19f74 TD_19f74 ltac:(pin; cond_compute).  (* 0x19f74 beq s0, a6, 0x19f5c <static_init_tls+0x74> *)
      stepb_tk TF_19f78 TD_19f78 ltac:(pin; cond_compute).  (* 0x19f78 beqz t0, 0x19f8c <static_init_tls+0xa4> *)
      sn TF_19f8c TD_19f8c.  (* 0x19f8c mv t6, t4 *)
      stepb_ft TF_19f90 TD_19f90 ltac:(pin; cond_compute).  (* 0x19f90 beq s0, t2, 0x19f98 <static_init_tls+0xb0> *)
      sn TF_19f94 TD_19f94.  (* 0x19f94 mv t6, a7 *)
      stepb_tk TF_19f98 TD_19f98 ltac:(pin; cond_compute).  (* 0x19f98 bne s0, t3, 0x19fb8 <static_init_tls+0xd0> *)
      sn TF_19fb8 TD_19fb8.  (* 0x19fb8 mv a7, t6 *)
      sn TF_19fbc TD_19fbc.  (* 0x19fbc j 0x19f64 <static_init_tls+0x7c> *)
      sn TF_19f64 TD_19f64.  (* 0x19f64 addi a3, a3, -0x1 *)
      sn TF_19f68 TD_19f68.  (* 0x19f68 add t4, t4, a0 *)
      stepb_ft TF_19f6c TD_19f6c ltac:(pin; cond_compute).  (* 0x19f6c beqz a3, 0x19fc0 <static_init_tls+0xd8> *)
      ld_step TF_19f70 TD_19f70 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_10120_4) ltac:(reflexivity).  (* 0x19f70 lw s0, 0x0(t4) *)
      stepb_ft TF_19f74 TD_19f74 ltac:(pin; cond_compute).  (* 0x19f74 beq s0, a6, 0x19f5c <static_init_tls+0x74> *)
      stepb_tk TF_19f78 TD_19f78 ltac:(pin; cond_compute).  (* 0x19f78 beqz t0, 0x19f8c <static_init_tls+0xa4> *)
      sn TF_19f8c TD_19f8c.  (* 0x19f8c mv t6, t4 *)
      stepb_ft TF_19f90 TD_19f90 ltac:(pin; cond_compute).  (* 0x19f90 beq s0, t2, 0x19f98 <static_init_tls+0xb0> *)
      sn TF_19f94 TD_19f94.  (* 0x19f94 mv t6, a7 *)
      stepb_tk TF_19f98 TD_19f98 ltac:(pin; cond_compute).  (* 0x19f98 bne s0, t3, 0x19fb8 <static_init_tls+0xd0> *)
      sn TF_19fb8 TD_19fb8.  (* 0x19fb8 mv a7, t6 *)
      sn TF_19fbc TD_19fbc.  (* 0x19fbc j 0x19f64 <static_init_tls+0x7c> *)
      sn TF_19f64 TD_19f64.  (* 0x19f64 addi a3, a3, -0x1 *)
      sn TF_19f68 TD_19f68.  (* 0x19f68 add t4, t4, a0 *)
      stepb_ft TF_19f6c TD_19f6c ltac:(pin; cond_compute).  (* 0x19f6c beqz a3, 0x19fc0 <static_init_tls+0xd8> *)
      OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { ld_step TF_19f70 TD_19f70 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img s2img_10040_4) ltac:(reflexivity).  (* 0x19f70 lw s0, 0x0(t4) *)
      stepb_tk TF_19f74 TD_19f74 ltac:(pin; cond_compute).  (* 0x19f74 beq s0, a6, 0x19f5c <static_init_tls+0x74> *)
      ld_step TF_19f5c TD_19f5c (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img s2img_10050_8) ltac:(apply bytes_le_to_Z_8).  (* 0x19f5c ld a2, 0x10(t4) *)
      sn TF_19f60 TD_19f60.  (* 0x19f60 sub a2, a5, a2 *)
      sn TF_19f64 TD_19f64.  (* 0x19f64 addi a3, a3, -0x1 *)
      sn TF_19f68 TD_19f68.  (* 0x19f68 add t4, t4, a0 *)
      stepb_ft TF_19f6c TD_19f6c ltac:(pin; cond_compute).  (* 0x19f6c beqz a3, 0x19fc0 <static_init_tls+0xd8> *)
      ld_step TF_19f70 TD_19f70 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_10078_4) ltac:(reflexivity).  (* 0x19f70 lw s0, 0x0(t4) *)
      stepb_ft TF_19f74 TD_19f74 ltac:(pin; cond_compute).  (* 0x19f74 beq s0, a6, 0x19f5c <static_init_tls+0x74> *)
      stepb_tk TF_19f78 TD_19f78 ltac:(pin; cond_compute).  (* 0x19f78 beqz t0, 0x19f8c <static_init_tls+0xa4> *)
      sn TF_19f8c TD_19f8c.  (* 0x19f8c mv t6, t4 *)
      stepb_ft TF_19f90 TD_19f90 ltac:(pin; cond_compute).  (* 0x19f90 beq s0, t2, 0x19f98 <static_init_tls+0xb0> *)
      sn TF_19f94 TD_19f94.  (* 0x19f94 mv t6, a7 *)
      stepb_tk TF_19f98 TD_19f98 ltac:(pin; cond_compute).  (* 0x19f98 bne s0, t3, 0x19fb8 <static_init_tls+0xd0> *)
      sn TF_19fb8 TD_19fb8.  (* 0x19fb8 mv a7, t6 *)
      sn TF_19fbc TD_19fbc.  (* 0x19fbc j 0x19f64 <static_init_tls+0x7c> *)
      sn TF_19f64 TD_19f64.  (* 0x19f64 addi a3, a3, -0x1 *)
      sn TF_19f68 TD_19f68.  (* 0x19f68 add t4, t4, a0 *)
      stepb_ft TF_19f6c TD_19f6c ltac:(pin; cond_compute).  (* 0x19f6c beqz a3, 0x19fc0 <static_init_tls+0xd8> *)
      ld_step TF_19f70 TD_19f70 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_100b0_4) ltac:(reflexivity).  (* 0x19f70 lw s0, 0x0(t4) *)
      stepb_ft TF_19f74 TD_19f74 ltac:(pin; cond_compute).  (* 0x19f74 beq s0, a6, 0x19f5c <static_init_tls+0x74> *)
      stepb_tk TF_19f78 TD_19f78 ltac:(pin; cond_compute).  (* 0x19f78 beqz t0, 0x19f8c <static_init_tls+0xa4> *)
      sn TF_19f8c TD_19f8c.  (* 0x19f8c mv t6, t4 *)
      stepb_ft TF_19f90 TD_19f90 ltac:(pin; cond_compute).  (* 0x19f90 beq s0, t2, 0x19f98 <static_init_tls+0xb0> *)
      sn TF_19f94 TD_19f94.  (* 0x19f94 mv t6, a7 *)
      stepb_tk TF_19f98 TD_19f98 ltac:(pin; cond_compute).  (* 0x19f98 bne s0, t3, 0x19fb8 <static_init_tls+0xd0> *)
      sn TF_19fb8 TD_19fb8.  (* 0x19fb8 mv a7, t6 *)
      sn TF_19fbc TD_19fbc.  (* 0x19fbc j 0x19f64 <static_init_tls+0x7c> *)
      sn TF_19f64 TD_19f64.  (* 0x19f64 addi a3, a3, -0x1 *)
      sn TF_19f68 TD_19f68.  (* 0x19f68 add t4, t4, a0 *)
      stepb_ft TF_19f6c TD_19f6c ltac:(pin; cond_compute).  (* 0x19f6c beqz a3, 0x19fc0 <static_init_tls+0xd8> *)
      ld_step TF_19f70 TD_19f70 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_100e8_4) ltac:(reflexivity).  (* 0x19f70 lw s0, 0x0(t4) *)
      stepb_ft TF_19f74 TD_19f74 ltac:(pin; cond_compute).  (* 0x19f74 beq s0, a6, 0x19f5c <static_init_tls+0x74> *)
      stepb_tk TF_19f78 TD_19f78 ltac:(pin; cond_compute).  (* 0x19f78 beqz t0, 0x19f8c <static_init_tls+0xa4> *)
      sn TF_19f8c TD_19f8c.  (* 0x19f8c mv t6, t4 *)
      stepb_ft TF_19f90 TD_19f90 ltac:(pin; cond_compute).  (* 0x19f90 beq s0, t2, 0x19f98 <static_init_tls+0xb0> *)
      sn TF_19f94 TD_19f94.  (* 0x19f94 mv t6, a7 *)
      stepb_tk TF_19f98 TD_19f98 ltac:(pin; cond_compute).  (* 0x19f98 bne s0, t3, 0x19fb8 <static_init_tls+0xd0> *)
      sn TF_19fb8 TD_19fb8.  (* 0x19fb8 mv a7, t6 *)
      sn TF_19fbc TD_19fbc.  (* 0x19fbc j 0x19f64 <static_init_tls+0x7c> *)
      sn TF_19f64 TD_19f64.  (* 0x19f64 addi a3, a3, -0x1 *)
      sn TF_19f68 TD_19f68.  (* 0x19f68 add t4, t4, a0 *)
      stepb_ft TF_19f6c TD_19f6c ltac:(pin; cond_compute).  (* 0x19f6c beqz a3, 0x19fc0 <static_init_tls+0xd8> *)
      ld_step TF_19f70 TD_19f70 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_10120_4) ltac:(reflexivity).  (* 0x19f70 lw s0, 0x0(t4) *)
      stepb_ft TF_19f74 TD_19f74 ltac:(pin; cond_compute).  (* 0x19f74 beq s0, a6, 0x19f5c <static_init_tls+0x74> *)
      stepb_tk TF_19f78 TD_19f78 ltac:(pin; cond_compute).  (* 0x19f78 beqz t0, 0x19f8c <static_init_tls+0xa4> *)
      sn TF_19f8c TD_19f8c.  (* 0x19f8c mv t6, t4 *)
      stepb_ft TF_19f90 TD_19f90 ltac:(pin; cond_compute).  (* 0x19f90 beq s0, t2, 0x19f98 <static_init_tls+0xb0> *)
      sn TF_19f94 TD_19f94.  (* 0x19f94 mv t6, a7 *)
      stepb_tk TF_19f98 TD_19f98 ltac:(pin; cond_compute).  (* 0x19f98 bne s0, t3, 0x19fb8 <static_init_tls+0xd0> *)
      sn TF_19fb8 TD_19fb8.  (* 0x19fb8 mv a7, t6 *)
      sn TF_19fbc TD_19fbc.  (* 0x19fbc j 0x19f64 <static_init_tls+0x7c> *)
      sn TF_19f64 TD_19f64.  (* 0x19f64 addi a3, a3, -0x1 *)
      sn TF_19f68 TD_19f68.  (* 0x19f68 add t4, t4, a0 *)
      stepb_ft TF_19f6c TD_19f6c ltac:(pin; cond_compute).  (* 0x19f6c beqz a3, 0x19fc0 <static_init_tls+0xd8> *)
      OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma tls_c3 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word), wfJ sp0 Jb -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) -> getr regs 3 = Z_to_bv 64 67584 -> getr regs 5 = Z_to_bv 64 0 -> getr regs 7 = Z_to_bv 64 7 -> getr regs 9 = Z_to_bv 64 607432 -> getr regs 10 = Z_to_bv 64 56 -> getr regs 11 = Z_to_bv 64 606792 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 5 -> getr regs 16 = Z_to_bv 64 6 -> getr regs 17 = Z_to_bv 64 0 -> getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 0 -> getr regs 25 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 0 -> getr regs 27 = Z_to_bv 64 0 -> getr regs 28 = Z_to_bv 64 1685382481 -> getr regs 29 = Z_to_bv 64 65880 -> getr regs 30 = Z_to_bv 64 131072 -> (forall regs', getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) -> getr regs' 3 = (Z_to_bv 64 67584) -> getr regs' 9 = (Z_to_bv 64 607432) -> getr regs' 11 = (Z_to_bv 64 606792) -> getr regs' 12 = (Z_to_bv 64 0) -> getr regs' 17 = (Z_to_bv 64 0) -> getr regs' 22 = (Z_to_bv 64 0) -> getr regs' 23 = (Z_to_bv 64 0) -> getr regs' 24 = (Z_to_bv 64 0) -> getr regs' 25 = (Z_to_bv 64 0) -> getr regs' 26 = (Z_to_bv 64 0) -> getr regs' 27 = (Z_to_bv 64 0) -> regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' -> G (mkst regs' (0x19fc0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105688))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607432))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom)) -> G (mkst regs (0x19f70 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105688))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607432))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H12 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { ld_step TF_19f70 TD_19f70 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img s2img_10158_4) ltac:(reflexivity).  (* 0x19f70 lw s0, 0x0(t4) *)
      stepb_ft TF_19f74 TD_19f74 ltac:(pin; cond_compute).  (* 0x19f74 beq s0, a6, 0x19f5c <static_init_tls+0x74> *)
      stepb_tk TF_19f78 TD_19f78 ltac:(pin; cond_compute).  (* 0x19f78 beqz t0, 0x19f8c <static_init_tls+0xa4> *)
      sn TF_19f8c TD_19f8c.  (* 0x19f8c mv t6, t4 *)
      stepb_ft TF_19f90 TD_19f90 ltac:(pin; cond_compute).  (* 0x19f90 beq s0, t2, 0x19f98 <static_init_tls+0xb0> *)
      sn TF_19f94 TD_19f94.  (* 0x19f94 mv t6, a7 *)
      stepb_tk TF_19f98 TD_19f98 ltac:(pin; cond_compute).  (* 0x19f98 bne s0, t3, 0x19fb8 <static_init_tls+0xd0> *)
      sn TF_19fb8 TD_19fb8.  (* 0x19fb8 mv a7, t6 *)
      sn TF_19fbc TD_19fbc.  (* 0x19fbc j 0x19f64 <static_init_tls+0x7c> *)
      sn TF_19f64 TD_19f64.  (* 0x19f64 addi a3, a3, -0x1 *)
      sn TF_19f68 TD_19f68.  (* 0x19f68 add t4, t4, a0 *)
      stepb_ft TF_19f6c TD_19f6c ltac:(pin; cond_compute).  (* 0x19f6c beqz a3, 0x19fc0 <static_init_tls+0xd8> *)
      ld_step TF_19f70 TD_19f70 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img s2img_10190_4) ltac:(reflexivity).  (* 0x19f70 lw s0, 0x0(t4) *)
      stepb_ft TF_19f74 TD_19f74 ltac:(pin; cond_compute).  (* 0x19f74 beq s0, a6, 0x19f5c <static_init_tls+0x74> *)
      stepb_tk TF_19f78 TD_19f78 ltac:(pin; cond_compute).  (* 0x19f78 beqz t0, 0x19f8c <static_init_tls+0xa4> *)
      sn TF_19f8c TD_19f8c.  (* 0x19f8c mv t6, t4 *)
      stepb_ft TF_19f90 TD_19f90 ltac:(pin; cond_compute).  (* 0x19f90 beq s0, t2, 0x19f98 <static_init_tls+0xb0> *)
      sn TF_19f94 TD_19f94.  (* 0x19f94 mv t6, a7 *)
      stepb_tk TF_19f98 TD_19f98 ltac:(pin; cond_compute).  (* 0x19f98 bne s0, t3, 0x19fb8 <static_init_tls+0xd0> *)
      sn TF_19fb8 TD_19fb8.  (* 0x19fb8 mv a7, t6 *)
      sn TF_19fbc TD_19fbc.  (* 0x19fbc j 0x19f64 <static_init_tls+0x7c> *)
      sn TF_19f64 TD_19f64.  (* 0x19f64 addi a3, a3, -0x1 *)
      sn TF_19f68 TD_19f68.  (* 0x19f68 add t4, t4, a0 *)
      stepb_ft TF_19f6c TD_19f6c ltac:(pin; cond_compute).  (* 0x19f6c beqz a3, 0x19fc0 <static_init_tls+0xd8> *)
      ld_step TF_19f70 TD_19f70 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img s2img_101c8_4) ltac:(reflexivity).  (* 0x19f70 lw s0, 0x0(t4) *)
      stepb_ft TF_19f74 TD_19f74 ltac:(pin; cond_compute).  (* 0x19f74 beq s0, a6, 0x19f5c <static_init_tls+0x74> *)
      stepb_tk TF_19f78 TD_19f78 ltac:(pin; cond_compute).  (* 0x19f78 beqz t0, 0x19f8c <static_init_tls+0xa4> *)
      sn TF_19f8c TD_19f8c.  (* 0x19f8c mv t6, t4 *)
      stepb_ft TF_19f90 TD_19f90 ltac:(pin; cond_compute).  (* 0x19f90 beq s0, t2, 0x19f98 <static_init_tls+0xb0> *)
      sn TF_19f94 TD_19f94.  (* 0x19f94 mv t6, a7 *)
      stepb_ft TF_19f98 TD_19f98 ltac:(pin; cond_compute).  (* 0x19f98 bne s0, t3, 0x19fb8 <static_init_tls+0xd0> *)
      ld_step TF_19f9c TD_19f9c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_101f0_8) ltac:(apply bytes_le_to_Z_8).  (* 0x19f9c ld a7, 0x28(t4) *)
      stepb_tk TF_19fa0 TD_19fa0 ltac:(pin; cond_compute).  (* 0x19fa0 bgeu t5, a7, 0x19fb8 <static_init_tls+0xd0> *)
      sn TF_19fb8 TD_19fb8.  (* 0x19fb8 mv a7, t6 *)
      sn TF_19fbc TD_19fbc.  (* 0x19fbc j 0x19f64 <static_init_tls+0x7c> *)
      sn TF_19f64 TD_19f64.  (* 0x19f64 addi a3, a3, -0x1 *)
      sn TF_19f68 TD_19f68.  (* 0x19f68 add t4, t4, a0 *)
      stepb_ft TF_19f6c TD_19f6c ltac:(pin; cond_compute).  (* 0x19f6c beqz a3, 0x19fc0 <static_init_tls+0xd8> *)
      ld_step TF_19f70 TD_19f70 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img s2img_10200_4) ltac:(reflexivity).  (* 0x19f70 lw s0, 0x0(t4) *)
      stepb_ft TF_19f74 TD_19f74 ltac:(pin; cond_compute).  (* 0x19f74 beq s0, a6, 0x19f5c <static_init_tls+0x74> *)
      stepb_tk TF_19f78 TD_19f78 ltac:(pin; cond_compute).  (* 0x19f78 beqz t0, 0x19f8c <static_init_tls+0xa4> *)
      sn TF_19f8c TD_19f8c.  (* 0x19f8c mv t6, t4 *)
      stepb_ft TF_19f90 TD_19f90 ltac:(pin; cond_compute).  (* 0x19f90 beq s0, t2, 0x19f98 <static_init_tls+0xb0> *)
      sn TF_19f94 TD_19f94.  (* 0x19f94 mv t6, a7 *)
      stepb_tk TF_19f98 TD_19f98 ltac:(pin; cond_compute).  (* 0x19f98 bne s0, t3, 0x19fb8 <static_init_tls+0xd0> *)
      sn TF_19fb8 TD_19fb8.  (* 0x19fb8 mv a7, t6 *)
      sn TF_19fbc TD_19fbc.  (* 0x19fbc j 0x19f64 <static_init_tls+0x7c> *)
      sn TF_19f64 TD_19f64.  (* 0x19f64 addi a3, a3, -0x1 *)
      sn TF_19f68 TD_19f68.  (* 0x19f68 add t4, t4, a0 *)
      stepb_ft TF_19f6c TD_19f6c ltac:(pin; cond_compute).  (* 0x19f6c beqz a3, 0x19fc0 <static_init_tls+0xd8> *)
      ld_step TF_19f70 TD_19f70 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img s2img_10238_4) ltac:(reflexivity).  (* 0x19f70 lw s0, 0x0(t4) *)
      stepb_ft TF_19f74 TD_19f74 ltac:(pin; cond_compute).  (* 0x19f74 beq s0, a6, 0x19f5c <static_init_tls+0x74> *)
      stepb_tk TF_19f78 TD_19f78 ltac:(pin; cond_compute).  (* 0x19f78 beqz t0, 0x19f8c <static_init_tls+0xa4> *)
      sn TF_19f8c TD_19f8c.  (* 0x19f8c mv t6, t4 *)
      stepb_ft TF_19f90 TD_19f90 ltac:(pin; cond_compute).  (* 0x19f90 beq s0, t2, 0x19f98 <static_init_tls+0xb0> *)
      sn TF_19f94 TD_19f94.  (* 0x19f94 mv t6, a7 *)
      stepb_tk TF_19f98 TD_19f98 ltac:(pin; cond_compute).  (* 0x19f98 bne s0, t3, 0x19fb8 <static_init_tls+0xd0> *)
      sn TF_19fb8 TD_19fb8.  (* 0x19fb8 mv a7, t6 *)
      sn TF_19fbc TD_19fbc.  (* 0x19fbc j 0x19f64 <static_init_tls+0x7c> *)
      sn TF_19f64 TD_19f64.  (* 0x19f64 addi a3, a3, -0x1 *)
      sn TF_19f68 TD_19f68.  (* 0x19f68 add t4, t4, a0 *)
      stepb_tk TF_19f6c TD_19f6c ltac:(pin; cond_compute).  (* 0x19f6c beqz a3, 0x19fc0 <static_init_tls+0xd8> *)
      OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { ld_step TF_19f70 TD_19f70 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img s2img_10158_4) ltac:(reflexivity).  (* 0x19f70 lw s0, 0x0(t4) *)
      stepb_ft TF_19f74 TD_19f74 ltac:(pin; cond_compute).  (* 0x19f74 beq s0, a6, 0x19f5c <static_init_tls+0x74> *)
      stepb_tk TF_19f78 TD_19f78 ltac:(pin; cond_compute).  (* 0x19f78 beqz t0, 0x19f8c <static_init_tls+0xa4> *)
      sn TF_19f8c TD_19f8c.  (* 0x19f8c mv t6, t4 *)
      stepb_ft TF_19f90 TD_19f90 ltac:(pin; cond_compute).  (* 0x19f90 beq s0, t2, 0x19f98 <static_init_tls+0xb0> *)
      sn TF_19f94 TD_19f94.  (* 0x19f94 mv t6, a7 *)
      stepb_tk TF_19f98 TD_19f98 ltac:(pin; cond_compute).  (* 0x19f98 bne s0, t3, 0x19fb8 <static_init_tls+0xd0> *)
      sn TF_19fb8 TD_19fb8.  (* 0x19fb8 mv a7, t6 *)
      sn TF_19fbc TD_19fbc.  (* 0x19fbc j 0x19f64 <static_init_tls+0x7c> *)
      sn TF_19f64 TD_19f64.  (* 0x19f64 addi a3, a3, -0x1 *)
      sn TF_19f68 TD_19f68.  (* 0x19f68 add t4, t4, a0 *)
      stepb_ft TF_19f6c TD_19f6c ltac:(pin; cond_compute).  (* 0x19f6c beqz a3, 0x19fc0 <static_init_tls+0xd8> *)
      ld_step TF_19f70 TD_19f70 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img s2img_10190_4) ltac:(reflexivity).  (* 0x19f70 lw s0, 0x0(t4) *)
      stepb_ft TF_19f74 TD_19f74 ltac:(pin; cond_compute).  (* 0x19f74 beq s0, a6, 0x19f5c <static_init_tls+0x74> *)
      stepb_tk TF_19f78 TD_19f78 ltac:(pin; cond_compute).  (* 0x19f78 beqz t0, 0x19f8c <static_init_tls+0xa4> *)
      sn TF_19f8c TD_19f8c.  (* 0x19f8c mv t6, t4 *)
      stepb_ft TF_19f90 TD_19f90 ltac:(pin; cond_compute).  (* 0x19f90 beq s0, t2, 0x19f98 <static_init_tls+0xb0> *)
      sn TF_19f94 TD_19f94.  (* 0x19f94 mv t6, a7 *)
      stepb_tk TF_19f98 TD_19f98 ltac:(pin; cond_compute).  (* 0x19f98 bne s0, t3, 0x19fb8 <static_init_tls+0xd0> *)
      sn TF_19fb8 TD_19fb8.  (* 0x19fb8 mv a7, t6 *)
      sn TF_19fbc TD_19fbc.  (* 0x19fbc j 0x19f64 <static_init_tls+0x7c> *)
      sn TF_19f64 TD_19f64.  (* 0x19f64 addi a3, a3, -0x1 *)
      sn TF_19f68 TD_19f68.  (* 0x19f68 add t4, t4, a0 *)
      stepb_ft TF_19f6c TD_19f6c ltac:(pin; cond_compute).  (* 0x19f6c beqz a3, 0x19fc0 <static_init_tls+0xd8> *)
      ld_step TF_19f70 TD_19f70 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img s2img_101c8_4) ltac:(reflexivity).  (* 0x19f70 lw s0, 0x0(t4) *)
      stepb_ft TF_19f74 TD_19f74 ltac:(pin; cond_compute).  (* 0x19f74 beq s0, a6, 0x19f5c <static_init_tls+0x74> *)
      stepb_tk TF_19f78 TD_19f78 ltac:(pin; cond_compute).  (* 0x19f78 beqz t0, 0x19f8c <static_init_tls+0xa4> *)
      sn TF_19f8c TD_19f8c.  (* 0x19f8c mv t6, t4 *)
      stepb_ft TF_19f90 TD_19f90 ltac:(pin; cond_compute).  (* 0x19f90 beq s0, t2, 0x19f98 <static_init_tls+0xb0> *)
      sn TF_19f94 TD_19f94.  (* 0x19f94 mv t6, a7 *)
      stepb_ft TF_19f98 TD_19f98 ltac:(pin; cond_compute).  (* 0x19f98 bne s0, t3, 0x19fb8 <static_init_tls+0xd0> *)
      ld_step TF_19f9c TD_19f9c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_101f0_8) ltac:(apply bytes_le_to_Z_8).  (* 0x19f9c ld a7, 0x28(t4) *)
      stepb_tk TF_19fa0 TD_19fa0 ltac:(pin; cond_compute).  (* 0x19fa0 bgeu t5, a7, 0x19fb8 <static_init_tls+0xd0> *)
      sn TF_19fb8 TD_19fb8.  (* 0x19fb8 mv a7, t6 *)
      sn TF_19fbc TD_19fbc.  (* 0x19fbc j 0x19f64 <static_init_tls+0x7c> *)
      sn TF_19f64 TD_19f64.  (* 0x19f64 addi a3, a3, -0x1 *)
      sn TF_19f68 TD_19f68.  (* 0x19f68 add t4, t4, a0 *)
      stepb_ft TF_19f6c TD_19f6c ltac:(pin; cond_compute).  (* 0x19f6c beqz a3, 0x19fc0 <static_init_tls+0xd8> *)
      ld_step TF_19f70 TD_19f70 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img s2img_10200_4) ltac:(reflexivity).  (* 0x19f70 lw s0, 0x0(t4) *)
      stepb_ft TF_19f74 TD_19f74 ltac:(pin; cond_compute).  (* 0x19f74 beq s0, a6, 0x19f5c <static_init_tls+0x74> *)
      stepb_tk TF_19f78 TD_19f78 ltac:(pin; cond_compute).  (* 0x19f78 beqz t0, 0x19f8c <static_init_tls+0xa4> *)
      sn TF_19f8c TD_19f8c.  (* 0x19f8c mv t6, t4 *)
      stepb_ft TF_19f90 TD_19f90 ltac:(pin; cond_compute).  (* 0x19f90 beq s0, t2, 0x19f98 <static_init_tls+0xb0> *)
      sn TF_19f94 TD_19f94.  (* 0x19f94 mv t6, a7 *)
      stepb_tk TF_19f98 TD_19f98 ltac:(pin; cond_compute).  (* 0x19f98 bne s0, t3, 0x19fb8 <static_init_tls+0xd0> *)
      sn TF_19fb8 TD_19fb8.  (* 0x19fb8 mv a7, t6 *)
      sn TF_19fbc TD_19fbc.  (* 0x19fbc j 0x19f64 <static_init_tls+0x7c> *)
      sn TF_19f64 TD_19f64.  (* 0x19f64 addi a3, a3, -0x1 *)
      sn TF_19f68 TD_19f68.  (* 0x19f68 add t4, t4, a0 *)
      stepb_ft TF_19f6c TD_19f6c ltac:(pin; cond_compute).  (* 0x19f6c beqz a3, 0x19fc0 <static_init_tls+0xd8> *)
      ld_step TF_19f70 TD_19f70 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img s2img_10238_4) ltac:(reflexivity).  (* 0x19f70 lw s0, 0x0(t4) *)
      stepb_ft TF_19f74 TD_19f74 ltac:(pin; cond_compute).  (* 0x19f74 beq s0, a6, 0x19f5c <static_init_tls+0x74> *)
      stepb_tk TF_19f78 TD_19f78 ltac:(pin; cond_compute).  (* 0x19f78 beqz t0, 0x19f8c <static_init_tls+0xa4> *)
      sn TF_19f8c TD_19f8c.  (* 0x19f8c mv t6, t4 *)
      stepb_ft TF_19f90 TD_19f90 ltac:(pin; cond_compute).  (* 0x19f90 beq s0, t2, 0x19f98 <static_init_tls+0xb0> *)
      sn TF_19f94 TD_19f94.  (* 0x19f94 mv t6, a7 *)
      stepb_tk TF_19f98 TD_19f98 ltac:(pin; cond_compute).  (* 0x19f98 bne s0, t3, 0x19fb8 <static_init_tls+0xd0> *)
      sn TF_19fb8 TD_19fb8.  (* 0x19fb8 mv a7, t6 *)
      sn TF_19fbc TD_19fbc.  (* 0x19fbc j 0x19f64 <static_init_tls+0x7c> *)
      sn TF_19f64 TD_19f64.  (* 0x19f64 addi a3, a3, -0x1 *)
      sn TF_19f68 TD_19f68.  (* 0x19f68 add t4, t4, a0 *)
      stepb_tk TF_19f6c TD_19f6c ltac:(pin; cond_compute).  (* 0x19f6c beqz a3, 0x19fc0 <static_init_tls+0xd8> *)
      OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma tls_c4 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word), wfJ sp0 Jb -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) -> getr regs 3 = Z_to_bv 64 67584 -> getr regs 9 = Z_to_bv 64 607432 -> getr regs 11 = Z_to_bv 64 606792 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 17 = Z_to_bv 64 0 -> getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 0 -> getr regs 25 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 0 -> getr regs 27 = Z_to_bv 64 0 -> (forall regs', getr regs' 1 = (Z_to_bv 64 106780) -> getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) -> getr regs' 3 = (Z_to_bv 64 67584) -> getr regs' 4 = (Z_to_bv 64 475712) -> getr regs' 8 = (Z_to_bv 64 475712) -> getr regs' 10 = (Z_to_bv 64 606792) -> getr regs' 11 = (Z_to_bv 64 607488) -> getr regs' 12 = (Z_to_bv 64 0) -> getr regs' 13 = (Z_to_bv 64 475504) -> getr regs' 14 = (Z_to_bv 64 0) -> getr regs' 15 = (Z_to_bv 64 18446744073709075904) -> getr regs' 17 = (Z_to_bv 64 96) -> getr regs' 18 = (Z_to_bv 64 475512) -> getr regs' 19 = (Z_to_bv 64 0) -> getr regs' 20 = (Z_to_bv 64 475728) -> getr regs' 22 = (Z_to_bv 64 0) -> getr regs' 23 = (Z_to_bv 64 0) -> getr regs' 24 = (Z_to_bv 64 0) -> getr regs' 25 = (Z_to_bv 64 0) -> getr regs' 26 = (Z_to_bv 64 0) -> getr regs' 27 = (Z_to_bv 64 0) -> regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' -> G (mkst regs' (0x1a144 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105688))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607432))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 606824) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606840) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606832) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 607456) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 607464) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 475728) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 475704) (word_to_le_bytes 8 (Z_to_bv 64 475728))) (Z_to_bv 64 475512) (word_to_le_bytes 8 (Z_to_bv 64 475512))) (Z_to_bv 64 607432) ([Z_to_bv 8 1])) (Z_to_bv 64 475552) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) -> G (mkst regs (0x19fc0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105688))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607432))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H12 H17 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { stepb_tk TF_19fc0 TD_19fc0 ltac:(pin; cond_compute).  (* 0x19fc0 beqz a7, 0x19ff8 <static_init_tls+0x110> *)
      ld_step TF_19ff8 TD_19ff8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_94258_8) ltac:(apply bytes_le_to_Z_8).  (* 0x19ff8 ld a2, 0x10(a1) *)
      ld_step TF_19ffc TD_19ffc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_94268_8) ltac:(apply bytes_le_to_Z_8).  (* 0x19ffc ld a3, 0x20(a1) *)
      ld_step TF_1a000 TD_1a000 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_94270_8) ltac:(apply bytes_le_to_Z_8).  (* 0x1a000 ld a0, 0x28(a1) *)
      sn TF_1a004 TD_1a004.  (* 0x1a004 add a4, a3, a2 *)
      sn TF_1a008 TD_1a008.  (* 0x1a008 addi a5, a0, -0x1 *)
      sn TF_1a00c TD_1a00c.  (* 0x1a00c neg a4, a4 *)
      sn TF_1a010 TD_1a010.  (* 0x1a010 and a2, a5, a2 *)
      sn TF_1a014 TD_1a014.  (* 0x1a014 and a4, a5, a4 *)
      sn TF_1a018 TD_1a018.  (* 0x1a018 li a5, 0x7 *)
      sn TF_1a01c TD_1a01c.  (* 0x1a01c add a3, a4, a3 *)
      stw TF_1a020 TD_1a020 (Z_to_bv 64 606824) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x1a020 sd a3, 0x20(a1) *)
      stw TF_1a024 TD_1a024 (Z_to_bv 64 606840) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x1a024 sd a2, 0x30(a1) *)
      stepb_ft TF_1a028 TD_1a028 ltac:(pin; cond_compute).  (* 0x1a028 bltu a5, a0, 0x1a034 <static_init_tls+0x14c> *)
      sn TF_1a02c TD_1a02c.  (* 0x1a02c li a0, 0x8 *)
      stw TF_1a030 TD_1a030 (Z_to_bv 64 606832) (Z_to_bv 64 8) ltac:(ok_data).  (* 0x1a030 sd a0, 0x28(a1) *)
      sn TF_1a034 TD_1a034.  (* 0x1a034 add a2, a2, a3 *)
      sn TF_1a038 TD_1a038.  (* 0x1a038 lui a1, 0x20 *)
      sn TF_1a03c TD_1a03c.  (* 0x1a03c add a2, a2, a0 *)
      sn TF_1a040 TD_1a040.  (* 0x1a040 addiw a3, a1, 0xd1 *)
      sn TF_1a044 TD_1a044.  (* 0x1a044 addi a1, a2, 0xdf *)
      sn TF_1a048 TD_1a048.  (* 0x1a048 andi a1, a1, -0x8 *)
      stw TF_1a04c TD_1a04c (Z_to_bv 64 607456) (Z_to_bv 64 224) ltac:(ok_data).  (* 0x1a04c sd a1, 0x18(s1) *)
      stw TF_1a050 TD_1a050 (Z_to_bv 64 607464) (Z_to_bv 64 8) ltac:(ok_data).  (* 0x1a050 sd a0, 0x20(s1) *)
      stepb_tk TF_1a054 TD_1a054 ltac:(pin; cond_compute).  (* 0x1a054 bltu a1, a3, 0x1a088 <static_init_tls+0x1a0> *)
      sn TF_1a088 TD_1a088.  (* 0x1a088 auipc a3, 0x5a *)
      ld_step TF_1a08c TD_1a08c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_944d8_8) ltac:(apply bytes_le_to_Z_8).  (* 0x1a08c ld s3, 0x10(s1) *)
      ld_step TF_1a090 TD_1a090 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_944f0_8) ltac:(apply bytes_le_to_Z_8).  (* 0x1a090 ld a2, 0x28(s1) *)
      sn TF_1a094 TD_1a094.  (* 0x1a094 addi a4, a0, -0x1 *)
      sn TF_1a098 TD_1a098.  (* 0x1a098 li a5, -0xc8 *)
      sn TF_1a09c TD_1a09c.  (* 0x1a09c addi a0, a3, 0xf0 *)
      sn TF_1a0a0 TD_1a0a0.  (* 0x1a0a0 sub a5, a5, a0 *)
      sn TF_1a0a4 TD_1a0a4.  (* 0x1a0a4 and a4, a4, a5 *)
      sn TF_1a0a8 TD_1a0a8.  (* 0x1a0a8 not a3, a2 *)
      sn TF_1a0ac TD_1a0ac.  (* 0x1a0ac add s2, a0, a4 *)
      sn TF_1a0b0 TD_1a0b0.  (* 0x1a0b0 slli a3, a3, 0x3 *)
      sn TF_1a0b4 TD_1a0b4.  (* 0x1a0b4 add a3, a0, a3 *)
      sn TF_1a0b8 TD_1a0b8.  (* 0x1a0b8 add s4, a3, a1 *)
      sn TF_1a0bc TD_1a0bc.  (* 0x1a0bc addi s0, s2, 0xc8 *)
      stepb_tk TF_1a0c0 TD_1a0c0 ltac:(pin; cond_compute).  (* 0x1a0c0 beqz s3, 0x1a108 <static_init_tls+0x220> *)
      stw TF_1a108 TD_1a108 (Z_to_bv 64 475728) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x1a108 sd a2, 0x0(s4) *)
      stw TF_1a10c TD_1a10c (Z_to_bv 64 475704) (Z_to_bv 64 475728) ltac:(ok_data).  (* 0x1a10c sd s4, 0xc0(s2) *)
      stw TF_1a110 TD_1a110 (Z_to_bv 64 475512) (Z_to_bv 64 475512) ltac:(ok_data).  (* 0x1a110 sd s2, 0x0(s2) *)
      sn TF_1a114 TD_1a114.  (* 0x1a114 mv a0, s0 *)
      sn TF_1a118 TD_1a118.  (* 0x1a118 jal 0x21d74 <__set_thread_area> *)
      sn F_21c98 D_21c98.  (* 0x21d74 mv tp, a0 *)
      sn F_21c9c D_21c9c.  (* 0x21d78 li a0, 0x0 *)
      stepret F_21ca0 D_21ca0 (0x1a11c : word) ltac:(pin; first [reflexivity | bveq]).  (* 0x21d7c ret *)
      stepb_ft TF_1a11c TD_1a11c ltac:(pin; cond_compute).  (* 0x1a11c bltz a0, 0x1a170 <static_init_tls+0x288> *)
      stepb_ft TF_1a120 TD_1a120 ltac:(pin; cond_compute).  (* 0x1a120 bnez a0, 0x1a12c <static_init_tls+0x244> *)
      sn TF_1a124 TD_1a124.  (* 0x1a124 li a0, 0x1 *)
      stw TF_1a128 TD_1a128 (Z_to_bv 64 607432) (Z_to_bv 64 1) ltac:(ok_data).  (* 0x1a128 sb a0, 0x0(s1) *)
      sn TF_1a12c TD_1a12c.  (* 0x1a12c li a0, 0x2 *)
      sn TF_1a130 TD_1a130.  (* 0x1a130 auipc a1, 0x7a *)
      stw TF_1a134 TD_1a134 (Z_to_bv 64 475552) (Z_to_bv 64 2) ltac:(ok_data).  (* 0x1a134 sw a0, 0x28(s2) *)
      sn TF_1a138 TD_1a138.  (* 0x1a138 li a7, 0x60 *)
      sn TF_1a13c TD_1a13c.  (* 0x1a13c addi a0, a1, 0x118 *)
      sn TF_1a140 TD_1a140.  (* 0x1a140 addi a1, s1, 0x38 *)
      OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { stepb_tk TF_19fc0 TD_19fc0 ltac:(pin; cond_compute).  (* 0x19fc0 beqz a7, 0x19ff8 <static_init_tls+0x110> *)
      ld_step TF_19ff8 TD_19ff8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_94258_8) ltac:(apply bytes_le_to_Z_8).  (* 0x19ff8 ld a2, 0x10(a1) *)
      ld_step TF_19ffc TD_19ffc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_94268_8) ltac:(apply bytes_le_to_Z_8).  (* 0x19ffc ld a3, 0x20(a1) *)
      ld_step TF_1a000 TD_1a000 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_94270_8) ltac:(apply bytes_le_to_Z_8).  (* 0x1a000 ld a0, 0x28(a1) *)
      sn TF_1a004 TD_1a004.  (* 0x1a004 add a4, a3, a2 *)
      sn TF_1a008 TD_1a008.  (* 0x1a008 addi a5, a0, -0x1 *)
      sn TF_1a00c TD_1a00c.  (* 0x1a00c neg a4, a4 *)
      sn TF_1a010 TD_1a010.  (* 0x1a010 and a2, a5, a2 *)
      sn TF_1a014 TD_1a014.  (* 0x1a014 and a4, a5, a4 *)
      sn TF_1a018 TD_1a018.  (* 0x1a018 li a5, 0x7 *)
      sn TF_1a01c TD_1a01c.  (* 0x1a01c add a3, a4, a3 *)
      stw TF_1a020 TD_1a020 (Z_to_bv 64 606824) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x1a020 sd a3, 0x20(a1) *)
      stw TF_1a024 TD_1a024 (Z_to_bv 64 606840) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x1a024 sd a2, 0x30(a1) *)
      stepb_ft TF_1a028 TD_1a028 ltac:(pin; cond_compute).  (* 0x1a028 bltu a5, a0, 0x1a034 <static_init_tls+0x14c> *)
      sn TF_1a02c TD_1a02c.  (* 0x1a02c li a0, 0x8 *)
      stw TF_1a030 TD_1a030 (Z_to_bv 64 606832) (Z_to_bv 64 8) ltac:(ok_data).  (* 0x1a030 sd a0, 0x28(a1) *)
      sn TF_1a034 TD_1a034.  (* 0x1a034 add a2, a2, a3 *)
      sn TF_1a038 TD_1a038.  (* 0x1a038 lui a1, 0x20 *)
      sn TF_1a03c TD_1a03c.  (* 0x1a03c add a2, a2, a0 *)
      sn TF_1a040 TD_1a040.  (* 0x1a040 addiw a3, a1, 0xd1 *)
      sn TF_1a044 TD_1a044.  (* 0x1a044 addi a1, a2, 0xdf *)
      sn TF_1a048 TD_1a048.  (* 0x1a048 andi a1, a1, -0x8 *)
      stw TF_1a04c TD_1a04c (Z_to_bv 64 607456) (Z_to_bv 64 224) ltac:(ok_data).  (* 0x1a04c sd a1, 0x18(s1) *)
      stw TF_1a050 TD_1a050 (Z_to_bv 64 607464) (Z_to_bv 64 8) ltac:(ok_data).  (* 0x1a050 sd a0, 0x20(s1) *)
      stepb_tk TF_1a054 TD_1a054 ltac:(pin; cond_compute).  (* 0x1a054 bltu a1, a3, 0x1a088 <static_init_tls+0x1a0> *)
      sn TF_1a088 TD_1a088.  (* 0x1a088 auipc a3, 0x5a *)
      ld_step TF_1a08c TD_1a08c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_944d8_8) ltac:(apply bytes_le_to_Z_8).  (* 0x1a08c ld s3, 0x10(s1) *)
      ld_step TF_1a090 TD_1a090 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_944f0_8) ltac:(apply bytes_le_to_Z_8).  (* 0x1a090 ld a2, 0x28(s1) *)
      sn TF_1a094 TD_1a094.  (* 0x1a094 addi a4, a0, -0x1 *)
      sn TF_1a098 TD_1a098.  (* 0x1a098 li a5, -0xc8 *)
      sn TF_1a09c TD_1a09c.  (* 0x1a09c addi a0, a3, 0xf0 *)
      sn TF_1a0a0 TD_1a0a0.  (* 0x1a0a0 sub a5, a5, a0 *)
      sn TF_1a0a4 TD_1a0a4.  (* 0x1a0a4 and a4, a4, a5 *)
      sn TF_1a0a8 TD_1a0a8.  (* 0x1a0a8 not a3, a2 *)
      sn TF_1a0ac TD_1a0ac.  (* 0x1a0ac add s2, a0, a4 *)
      sn TF_1a0b0 TD_1a0b0.  (* 0x1a0b0 slli a3, a3, 0x3 *)
      sn TF_1a0b4 TD_1a0b4.  (* 0x1a0b4 add a3, a0, a3 *)
      sn TF_1a0b8 TD_1a0b8.  (* 0x1a0b8 add s4, a3, a1 *)
      sn TF_1a0bc TD_1a0bc.  (* 0x1a0bc addi s0, s2, 0xc8 *)
      stepb_tk TF_1a0c0 TD_1a0c0 ltac:(pin; cond_compute).  (* 0x1a0c0 beqz s3, 0x1a108 <static_init_tls+0x220> *)
      stw TF_1a108 TD_1a108 (Z_to_bv 64 475728) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x1a108 sd a2, 0x0(s4) *)
      stw TF_1a10c TD_1a10c (Z_to_bv 64 475704) (Z_to_bv 64 475728) ltac:(ok_data).  (* 0x1a10c sd s4, 0xc0(s2) *)
      stw TF_1a110 TD_1a110 (Z_to_bv 64 475512) (Z_to_bv 64 475512) ltac:(ok_data).  (* 0x1a110 sd s2, 0x0(s2) *)
      sn TF_1a114 TD_1a114.  (* 0x1a114 mv a0, s0 *)
      sn TF_1a118 TD_1a118.  (* 0x1a118 jal 0x21d74 <__set_thread_area> *)
      sn F_21c98 D_21c98.  (* 0x21d74 mv tp, a0 *)
      sn F_21c9c D_21c9c.  (* 0x21d78 li a0, 0x0 *)
      stepret F_21ca0 D_21ca0 (0x1a11c : word) ltac:(pin; first [reflexivity | bveq]).  (* 0x21d7c ret *)
      stepb_ft TF_1a11c TD_1a11c ltac:(pin; cond_compute).  (* 0x1a11c bltz a0, 0x1a170 <static_init_tls+0x288> *)
      stepb_ft TF_1a120 TD_1a120 ltac:(pin; cond_compute).  (* 0x1a120 bnez a0, 0x1a12c <static_init_tls+0x244> *)
      sn TF_1a124 TD_1a124.  (* 0x1a124 li a0, 0x1 *)
      stw TF_1a128 TD_1a128 (Z_to_bv 64 607432) (Z_to_bv 64 1) ltac:(ok_data).  (* 0x1a128 sb a0, 0x0(s1) *)
      sn TF_1a12c TD_1a12c.  (* 0x1a12c li a0, 0x2 *)
      sn TF_1a130 TD_1a130.  (* 0x1a130 auipc a1, 0x7a *)
      stw TF_1a134 TD_1a134 (Z_to_bv 64 475552) (Z_to_bv 64 2) ltac:(ok_data).  (* 0x1a134 sw a0, 0x28(s2) *)
      sn TF_1a138 TD_1a138.  (* 0x1a138 li a7, 0x60 *)
      sn TF_1a13c TD_1a13c.  (* 0x1a13c addi a0, a1, 0x118 *)
      sn TF_1a140 TD_1a140.  (* 0x1a140 addi a1, s1, 0x38 *)
      OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma tls_c5 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word), wfJ sp0 Jb -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) -> getr regs 3 = Z_to_bv 64 67584 -> getr regs 4 = Z_to_bv 64 475712 -> getr regs 10 = tid -> getr regs 11 = Z_to_bv 64 607488 -> getr regs 18 = Z_to_bv 64 475512 -> getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 0 -> getr regs 25 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 0 -> getr regs 27 = Z_to_bv 64 0 -> (forall regs', getr regs' 1 = (Z_to_bv 64 105688) -> getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) -> getr regs' 3 = (Z_to_bv 64 67584) -> getr regs' 4 = (Z_to_bv 64 475712) -> getr regs' 8 = (pn_w inp rdraw) -> getr regs' 9 = (s1v) -> getr regs' 10 = (Z_to_bv 64 0) -> getr regs' 12 = (Z_to_bv 64 475632) -> getr regs' 18 = (Z_to_bv 64 607432) -> getr regs' 19 = (Z_to_bv 64 0) -> getr regs' 20 = (Z_to_bv 64 0) -> getr regs' 21 = (Z_to_bv 64 0) -> getr regs' 22 = (Z_to_bv 64 0) -> getr regs' 23 = (Z_to_bv 64 0) -> getr regs' 24 = (Z_to_bv 64 0) -> getr regs' 25 = (Z_to_bv 64 0) -> getr regs' 26 = (Z_to_bv 64 0) -> getr regs' 27 = (Z_to_bv 64 0) -> regs_agree (fun r => In r [1; 2; 8; 9; 10; 12; 18; 19; 20; 21]%list) regs regs' -> G (mkst regs' (0x19cd8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105688))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607432))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 606824) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606840) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606832) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 607456) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 607464) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 475728) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 475704) (word_to_le_bytes 8 (Z_to_bv 64 475728))) (Z_to_bv 64 475512) (word_to_le_bytes 8 (Z_to_bv 64 475512))) (Z_to_bv 64 607432) ([Z_to_bv 8 1])) (Z_to_bv 64 475552) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 475544) (word_to_le_bytes 4 tid)) (Z_to_bv 64 475664) (word_to_le_bytes 8 (Z_to_bv 64 607488))) (Z_to_bv 64 475632) (word_to_le_bytes 8 (Z_to_bv 64 475632))) (Z_to_bv 64 475520) (word_to_le_bytes 8 (Z_to_bv 64 475512))) (Z_to_bv 64 475528) (word_to_le_bytes 8 (Z_to_bv 64 475512))) (Z_to_bv 64 475536) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) -> G (mkst regs (0x1a148 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105688))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607432))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 606824) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606840) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606832) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 607456) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 607464) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 475728) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 475704) (word_to_le_bytes 8 (Z_to_bv 64 475728))) (Z_to_bv 64 475512) (word_to_le_bytes 8 (Z_to_bv 64 475512))) (Z_to_bv 64 607432) ([Z_to_bv 8 1])) (Z_to_bv 64 475552) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { sn TF_1a148 TD_1a148.  (* 0x1a148 addi a2, s2, 0x78 *)
      stw TF_1a14c TD_1a14c (Z_to_bv 64 475544) (tid) ltac:(ok_data).  (* 0x1a14c sw a0, 0x20(s2) *)
      stw TF_1a150 TD_1a150 (Z_to_bv 64 475664) (Z_to_bv 64 607488) ltac:(ok_data).  (* 0x1a150 sd a1, 0x98(s2) *)
      stw TF_1a154 TD_1a154 (Z_to_bv 64 475632) (Z_to_bv 64 475632) ltac:(ok_data).  (* 0x1a154 sd a2, 0x78(s2) *)
      sn TF_1a158 TD_1a158.  (* 0x1a158 auipc a0, 0x7a *)
      ld_step TF_1a15c TD_1a15c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_944b0_8) ltac:(apply bytes_le_to_Z_8).  (* 0x1a15c ld a0, 0x358(a0) *)
      stw TF_1a160 TD_1a160 (Z_to_bv 64 475520) (Z_to_bv 64 475512) ltac:(ok_data).  (* 0x1a160 sd s2, 0x8(s2) *)
      stw TF_1a164 TD_1a164 (Z_to_bv 64 475528) (Z_to_bv 64 475512) ltac:(ok_data).  (* 0x1a164 sd s2, 0x10(s2) *)
      stw TF_1a168 TD_1a168 (Z_to_bv 64 475536) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x1a168 sd a0, 0x18(s2) *)
      sn TF_1a16c TD_1a16c.  (* 0x1a16c j 0x1a174 <static_init_tls+0x28c> *)
      ld_step TF_1a174 TD_1a174 (word_to_le_bytes 8 (Z_to_bv 64 105688)) (Z_to_bv 64 105688) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x1a174 ld ra, 0x38(sp) *)
      ld_step TF_1a178 TD_1a178 (word_to_le_bytes 8 (pn_w inp rdraw)) (pn_w inp rdraw) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x1a178 ld s0, 0x30(sp) *)
      ld_step TF_1a17c TD_1a17c (word_to_le_bytes 8 s1v) (s1v) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x1a17c ld s1, 0x28(sp) *)
      ld_step TF_1a180 TD_1a180 (word_to_le_bytes 8 (Z_to_bv 64 607432)) (Z_to_bv 64 607432) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x1a180 ld s2, 0x20(sp) *)
      ld_step TF_1a184 TD_1a184 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x1a184 ld s3, 0x18(sp) *)
      ld_step TF_1a188 TD_1a188 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x1a188 ld s4, 0x10(sp) *)
      ld_step TF_1a18c TD_1a18c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x1a18c ld s5, 0x8(sp) *)
      sv TF_1a190 TD_1a190 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* 0x1a190 addi sp, sp, 0x40 *)
      stepret TF_1a194 TD_1a194 (0x19cd8 : word) ltac:(pin; first [reflexivity | bveq]).  (* 0x1a194 ret *)
      OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { sn TF_1a148 TD_1a148.  (* 0x1a148 addi a2, s2, 0x78 *)
      stw TF_1a14c TD_1a14c (Z_to_bv 64 475544) (tid) ltac:(ok_data).  (* 0x1a14c sw a0, 0x20(s2) *)
      stw TF_1a150 TD_1a150 (Z_to_bv 64 475664) (Z_to_bv 64 607488) ltac:(ok_data).  (* 0x1a150 sd a1, 0x98(s2) *)
      stw TF_1a154 TD_1a154 (Z_to_bv 64 475632) (Z_to_bv 64 475632) ltac:(ok_data).  (* 0x1a154 sd a2, 0x78(s2) *)
      sn TF_1a158 TD_1a158.  (* 0x1a158 auipc a0, 0x7a *)
      ld_step TF_1a15c TD_1a15c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_944b0_8) ltac:(apply bytes_le_to_Z_8).  (* 0x1a15c ld a0, 0x358(a0) *)
      stw TF_1a160 TD_1a160 (Z_to_bv 64 475520) (Z_to_bv 64 475512) ltac:(ok_data).  (* 0x1a160 sd s2, 0x8(s2) *)
      stw TF_1a164 TD_1a164 (Z_to_bv 64 475528) (Z_to_bv 64 475512) ltac:(ok_data).  (* 0x1a164 sd s2, 0x10(s2) *)
      stw TF_1a168 TD_1a168 (Z_to_bv 64 475536) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x1a168 sd a0, 0x18(s2) *)
      sn TF_1a16c TD_1a16c.  (* 0x1a16c j 0x1a174 <static_init_tls+0x28c> *)
      ld_step TF_1a174 TD_1a174 (word_to_le_bytes 8 (Z_to_bv 64 105688)) (Z_to_bv 64 105688) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x1a174 ld ra, 0x38(sp) *)
      ld_step TF_1a178 TD_1a178 (word_to_le_bytes 8 (pn_w inp rdraw)) (pn_w inp rdraw) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x1a178 ld s0, 0x30(sp) *)
      ld_step TF_1a17c TD_1a17c (word_to_le_bytes 8 s1v) (s1v) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x1a17c ld s1, 0x28(sp) *)
      ld_step TF_1a180 TD_1a180 (word_to_le_bytes 8 (Z_to_bv 64 607432)) (Z_to_bv 64 607432) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x1a180 ld s2, 0x20(sp) *)
      ld_step TF_1a184 TD_1a184 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x1a184 ld s3, 0x18(sp) *)
      ld_step TF_1a188 TD_1a188 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x1a188 ld s4, 0x10(sp) *)
      ld_step TF_1a18c TD_1a18c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x1a18c ld s5, 0x8(sp) *)
      sv TF_1a190 TD_1a190 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* 0x1a190 addi sp, sp, 0x40 *)
      stepret TF_1a194 TD_1a194 (0x19cd8 : word) ltac:(pin; first [reflexivity | bveq]).  (* 0x1a194 ret *)
      OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

End P4.
