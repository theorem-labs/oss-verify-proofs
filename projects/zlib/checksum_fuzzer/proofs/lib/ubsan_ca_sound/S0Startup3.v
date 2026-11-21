(* elf , front , img own, defs ,
   statements (TEMPLATE; synthesized from the run), context , conventions ;
   valtac4: 'reflexivity' from 'WalkTac.v stepld_pc value side; S0Startup2.v F_152d4'; split-rseq all. *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import RunCtx.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.World Require Import Src_zlib_checksum_fuzzer_repro.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import StartupTac ArgvEnv RefLayout S0StartupDefs S0_code_15000_16000 S0_code_1d000_1d640.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import LiaFast.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require L10Walk.
Ltac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.StepTac.chain_step ::= OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_chain_step.
Abbreviation SEGS := Src_zlib_checksum_fuzzer_repro.M.loaded_segments.
Abbreviation RPH := Src_zlib_checksum_fuzzer_repro.M.phdrs.
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
Lemma s2img_1e708_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 124680) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_1f9a0_4 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 129440) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
Lemma s2img_4fb18_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 326424) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_4fb28_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 326440) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_4fb30_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 326448) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_4fd78_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 327032) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_4fda0_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 327072) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_4fdb8_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 327096) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
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
Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH (Z_to_bv 64 (Z.of_N Src_zlib_checksum_fuzzer_repro.M.init_pc)) sp0 rdraw)) (only parsing).

  Lemma tls_c1 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word), wfJ sp0 Jb -> getr regs 1 = Z_to_bv 64 87040 -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) -> getr regs 3 = Z_to_bv 64 67584 -> getr regs 8 = pn_w inp rdraw -> getr regs 9 = s1v -> getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) -> getr regs 18 = Z_to_bv 64 327056 -> getr regs 19 = Z_to_bv 64 0 -> getr regs 20 = Z_to_bv 64 0 -> getr regs 21 = Z_to_bv 64 0 -> getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 0 -> getr regs 25 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 0 -> getr regs 27 = Z_to_bv 64 0 -> (forall regs', getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) -> getr regs' 3 = (Z_to_bv 64 67584) -> getr regs' 5 = (Z_to_bv 64 0) -> getr regs' 7 = (Z_to_bv 64 7) -> getr regs' 9 = (Z_to_bv 64 327056) -> getr regs' 10 = (Z_to_bv 64 56) -> getr regs' 11 = (Z_to_bv 64 326408) -> getr regs' 12 = (Z_to_bv 64 0) -> getr regs' 13 = (Z_to_bv 64 10) -> getr regs' 15 = (Z_to_bv 64 65600) -> getr regs' 16 = (Z_to_bv 64 6) -> getr regs' 17 = (Z_to_bv 64 0) -> getr regs' 22 = (Z_to_bv 64 0) -> getr regs' 23 = (Z_to_bv 64 0) -> getr regs' 24 = (Z_to_bv 64 0) -> getr regs' 25 = (Z_to_bv 64 0) -> getr regs' 26 = (Z_to_bv 64 0) -> getr regs' 27 = (Z_to_bv 64 0) -> getr regs' 28 = (Z_to_bv 64 1685382481) -> getr regs' 29 = (Z_to_bv 64 65600) -> getr regs' 30 = (Z_to_bv 64 131072) -> regs_agree (fun r => In r [2; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30]%list) regs regs' -> G (mkst regs' (0x15698 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87040))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom)) -> G (mkst regs (0x15610 : word) (CM (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (D_libc sp0 inp rdraw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { sv F_15564 D_15564 (Z_to_bv 64 (bv_unsigned sp0 - 480)).  (* 0x15610 addi sp, sp, -0x40 *)
      stw TF_15614 TD_15614 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 87040) ltac:(ok_win HJ).  (* 0x15614 sd ra, 0x38(sp) *)
      stw TF_15618 TD_15618 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w inp rdraw) ltac:(ok_win HJ).  (* 0x15618 sd s0, 0x30(sp) *)
      stw TF_1561c TD_1561c (Z_to_bv 64 (bv_unsigned sp0 - 440)) (s1v) ltac:(ok_win HJ).  (* 0x1561c sd s1, 0x28(sp) *)
      stw TF_15620 TD_15620 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 327056) ltac:(ok_win HJ).  (* 0x15620 sd s2, 0x20(sp) *)
      stw TF_15624 TD_15624 (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x15624 sd s3, 0x18(sp) *)
      stw TF_15628 TD_15628 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x15628 sd s4, 0x10(sp) *)
      stw TF_1562c TD_1562c (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x1562c sd s5, 0x8(sp) *)
      ld_step TF_15630 TD_15630 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x15630 ld a3, 0x28(a0) *)
      sn TF_15634 TD_15634.  (* 0x15634 auipc a1, 0x3a *)
      sn TF_15638 TD_15638.  (* 0x15638 addi a1, a1, 0x4d4 *)
      sn TF_1563c TD_1563c.  (* 0x1563c auipc a2, 0x3a *)
      sn TF_15640 TD_15640.  (* 0x15640 addi s1, a2, 0x754 *)
      stepb_ft TF_15644 TD_15644 ltac:(pin; cond_compute).  (* 0x15644 beqz a3, 0x15720 <static_init_tls+0x110> *)
      sn TF_15648 TD_15648.  (* 0x15648 li a2, 0x0 *)
      sn TF_1564c TD_1564c.  (* 0x1564c li a7, 0x0 *)
      sn TF_15650 TD_15650.  (* 0x15650 auipc a4, 0xa *)
      ld_step TF_15654 TD_15654 (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x15654 ld a5, 0x18(a0) *)
      ld_step TF_15658 TD_15658 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x15658 ld a0, 0x20(a0) *)
      sn TF_1565c TD_1565c.  (* 0x1565c li a6, 0x6 *)
      sn TF_15660 TD_15660.  (* 0x15660 auipc t0, 0x9 *)
      ld_step TF_15664 TD_15664 (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img s2img_1f9a0_4) ltac:(reflexivity).  (* 0x15664 lwu t5, 0x350(a4) *)
      ld_step TF_15668 TD_15668 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_1e708_8) ltac:(apply bytes_le_to_Z_8).  (* 0x15668 ld t0, 0xa8(t0) *)
      sn TF_1566c TD_1566c.  (* 0x1566c li t1, 0x2 *)
      sn TF_15670 TD_15670.  (* 0x15670 li t2, 0x7 *)
      sn TF_15674 TD_15674.  (* 0x15674 lui t3, 0x6474e *)
      sn TF_15678 TD_15678.  (* 0x15678 addiw t3, t3, 0x551 *)
      sn TF_1567c TD_1567c.  (* 0x1567c mv t4, a5 *)
      sn TF_15680 TD_15680.  (* 0x15680 j 0x15698 <static_init_tls+0x88> *)
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { sv F_15564 D_15564 (Z_to_bv 64 (bv_unsigned sp0 - 480)).  (* 0x15610 addi sp, sp, -0x40 *)
      stw TF_15614 TD_15614 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 87040) ltac:(ok_win HJ).  (* 0x15614 sd ra, 0x38(sp) *)
      stw TF_15618 TD_15618 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w inp rdraw) ltac:(ok_win HJ).  (* 0x15618 sd s0, 0x30(sp) *)
      stw TF_1561c TD_1561c (Z_to_bv 64 (bv_unsigned sp0 - 440)) (s1v) ltac:(ok_win HJ).  (* 0x1561c sd s1, 0x28(sp) *)
      stw TF_15620 TD_15620 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 327056) ltac:(ok_win HJ).  (* 0x15620 sd s2, 0x20(sp) *)
      stw TF_15624 TD_15624 (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x15624 sd s3, 0x18(sp) *)
      stw TF_15628 TD_15628 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x15628 sd s4, 0x10(sp) *)
      stw TF_1562c TD_1562c (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x1562c sd s5, 0x8(sp) *)
      ld_step TF_15630 TD_15630 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x15630 ld a3, 0x28(a0) *)
      sn TF_15634 TD_15634.  (* 0x15634 auipc a1, 0x3a *)
      sn TF_15638 TD_15638.  (* 0x15638 addi a1, a1, 0x4d4 *)
      sn TF_1563c TD_1563c.  (* 0x1563c auipc a2, 0x3a *)
      sn TF_15640 TD_15640.  (* 0x15640 addi s1, a2, 0x754 *)
      stepb_ft TF_15644 TD_15644 ltac:(pin; cond_compute).  (* 0x15644 beqz a3, 0x15720 <static_init_tls+0x110> *)
      sn TF_15648 TD_15648.  (* 0x15648 li a2, 0x0 *)
      sn TF_1564c TD_1564c.  (* 0x1564c li a7, 0x0 *)
      sn TF_15650 TD_15650.  (* 0x15650 auipc a4, 0xa *)
      ld_step TF_15654 TD_15654 (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x15654 ld a5, 0x18(a0) *)
      ld_step TF_15658 TD_15658 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x15658 ld a0, 0x20(a0) *)
      sn TF_1565c TD_1565c.  (* 0x1565c li a6, 0x6 *)
      sn TF_15660 TD_15660.  (* 0x15660 auipc t0, 0x9 *)
      ld_step TF_15664 TD_15664 (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img s2img_1f9a0_4) ltac:(reflexivity).  (* 0x15664 lwu t5, 0x350(a4) *)
      ld_step TF_15668 TD_15668 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_1e708_8) ltac:(apply bytes_le_to_Z_8).  (* 0x15668 ld t0, 0xa8(t0) *)
      sn TF_1566c TD_1566c.  (* 0x1566c li t1, 0x2 *)
      sn TF_15670 TD_15670.  (* 0x15670 li t2, 0x7 *)
      sn TF_15674 TD_15674.  (* 0x15674 lui t3, 0x6474e *)
      sn TF_15678 TD_15678.  (* 0x15678 addiw t3, t3, 0x551 *)
      sn TF_1567c TD_1567c.  (* 0x1567c mv t4, a5 *)
      sn TF_15680 TD_15680.  (* 0x15680 j 0x15698 <static_init_tls+0x88> *)
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma tls_c2 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word), wfJ sp0 Jb -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) -> getr regs 3 = Z_to_bv 64 67584 -> getr regs 5 = Z_to_bv 64 0 -> getr regs 7 = Z_to_bv 64 7 -> getr regs 9 = Z_to_bv 64 327056 -> getr regs 10 = Z_to_bv 64 56 -> getr regs 11 = Z_to_bv 64 326408 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 10 -> getr regs 15 = Z_to_bv 64 65600 -> getr regs 16 = Z_to_bv 64 6 -> getr regs 17 = Z_to_bv 64 0 -> getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 0 -> getr regs 25 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 0 -> getr regs 27 = Z_to_bv 64 0 -> getr regs 28 = Z_to_bv 64 1685382481 -> getr regs 29 = Z_to_bv 64 65600 -> getr regs 30 = Z_to_bv 64 131072 -> (forall regs', getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) -> getr regs' 3 = (Z_to_bv 64 67584) -> getr regs' 5 = (Z_to_bv 64 0) -> getr regs' 7 = (Z_to_bv 64 7) -> getr regs' 9 = (Z_to_bv 64 327056) -> getr regs' 10 = (Z_to_bv 64 56) -> getr regs' 11 = (Z_to_bv 64 326408) -> getr regs' 12 = (Z_to_bv 64 0) -> getr regs' 13 = (Z_to_bv 64 5) -> getr regs' 16 = (Z_to_bv 64 6) -> getr regs' 17 = (Z_to_bv 64 0) -> getr regs' 22 = (Z_to_bv 64 0) -> getr regs' 23 = (Z_to_bv 64 0) -> getr regs' 24 = (Z_to_bv 64 0) -> getr regs' 25 = (Z_to_bv 64 0) -> getr regs' 26 = (Z_to_bv 64 0) -> getr regs' 27 = (Z_to_bv 64 0) -> getr regs' 28 = (Z_to_bv 64 1685382481) -> getr regs' 29 = (Z_to_bv 64 65880) -> getr regs' 30 = (Z_to_bv 64 131072) -> regs_agree (fun r => In r [8; 12; 13; 17; 29; 31]%list) regs regs' -> G (mkst regs' (0x15698 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87040))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom)) -> G (mkst regs (0x15698 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87040))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H12 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { ld_step TF_15698 TD_15698 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img s2img_10040_4) ltac:(reflexivity).  (* 0x15698 lw s0, 0x0(t4) *)
      stepb_tk TF_1569c TD_1569c ltac:(pin; cond_compute).  (* 0x1569c beq s0, a6, 0x15684 <static_init_tls+0x74> *)
      ld_step TF_15684 TD_15684 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img s2img_10050_8) ltac:(apply bytes_le_to_Z_8).  (* 0x15684 ld a2, 0x10(t4) *)
      sn TF_15688 TD_15688.  (* 0x15688 sub a2, a5, a2 *)
      sn TF_1568c TD_1568c.  (* 0x1568c addi a3, a3, -0x1 *)
      sn TF_15690 TD_15690.  (* 0x15690 add t4, t4, a0 *)
      stepb_ft TF_15694 TD_15694 ltac:(pin; cond_compute).  (* 0x15694 beqz a3, 0x156e8 <static_init_tls+0xd8> *)
      ld_step TF_15698 TD_15698 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_10078_4) ltac:(reflexivity).  (* 0x15698 lw s0, 0x0(t4) *)
      stepb_ft TF_1569c TD_1569c ltac:(pin; cond_compute).  (* 0x1569c beq s0, a6, 0x15684 <static_init_tls+0x74> *)
      stepb_tk TF_156a0 TD_156a0 ltac:(pin; cond_compute).  (* 0x156a0 beqz t0, 0x156b4 <static_init_tls+0xa4> *)
      sn TF_156b4 TD_156b4.  (* 0x156b4 mv t6, t4 *)
      stepb_ft TF_156b8 TD_156b8 ltac:(pin; cond_compute).  (* 0x156b8 beq s0, t2, 0x156c0 <static_init_tls+0xb0> *)
      sn TF_156bc TD_156bc.  (* 0x156bc mv t6, a7 *)
      stepb_tk TF_156c0 TD_156c0 ltac:(pin; cond_compute).  (* 0x156c0 bne s0, t3, 0x156e0 <static_init_tls+0xd0> *)
      sn TF_156e0 TD_156e0.  (* 0x156e0 mv a7, t6 *)
      sn TF_156e4 TD_156e4.  (* 0x156e4 j 0x1568c <static_init_tls+0x7c> *)
      sn TF_1568c TD_1568c.  (* 0x1568c addi a3, a3, -0x1 *)
      sn TF_15690 TD_15690.  (* 0x15690 add t4, t4, a0 *)
      stepb_ft TF_15694 TD_15694 ltac:(pin; cond_compute).  (* 0x15694 beqz a3, 0x156e8 <static_init_tls+0xd8> *)
      ld_step TF_15698 TD_15698 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_100b0_4) ltac:(reflexivity).  (* 0x15698 lw s0, 0x0(t4) *)
      stepb_ft TF_1569c TD_1569c ltac:(pin; cond_compute).  (* 0x1569c beq s0, a6, 0x15684 <static_init_tls+0x74> *)
      stepb_tk TF_156a0 TD_156a0 ltac:(pin; cond_compute).  (* 0x156a0 beqz t0, 0x156b4 <static_init_tls+0xa4> *)
      sn TF_156b4 TD_156b4.  (* 0x156b4 mv t6, t4 *)
      stepb_ft TF_156b8 TD_156b8 ltac:(pin; cond_compute).  (* 0x156b8 beq s0, t2, 0x156c0 <static_init_tls+0xb0> *)
      sn TF_156bc TD_156bc.  (* 0x156bc mv t6, a7 *)
      stepb_tk TF_156c0 TD_156c0 ltac:(pin; cond_compute).  (* 0x156c0 bne s0, t3, 0x156e0 <static_init_tls+0xd0> *)
      sn TF_156e0 TD_156e0.  (* 0x156e0 mv a7, t6 *)
      sn TF_156e4 TD_156e4.  (* 0x156e4 j 0x1568c <static_init_tls+0x7c> *)
      sn TF_1568c TD_1568c.  (* 0x1568c addi a3, a3, -0x1 *)
      sn TF_15690 TD_15690.  (* 0x15690 add t4, t4, a0 *)
      stepb_ft TF_15694 TD_15694 ltac:(pin; cond_compute).  (* 0x15694 beqz a3, 0x156e8 <static_init_tls+0xd8> *)
      ld_step TF_15698 TD_15698 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_100e8_4) ltac:(reflexivity).  (* 0x15698 lw s0, 0x0(t4) *)
      stepb_ft TF_1569c TD_1569c ltac:(pin; cond_compute).  (* 0x1569c beq s0, a6, 0x15684 <static_init_tls+0x74> *)
      stepb_tk TF_156a0 TD_156a0 ltac:(pin; cond_compute).  (* 0x156a0 beqz t0, 0x156b4 <static_init_tls+0xa4> *)
      sn TF_156b4 TD_156b4.  (* 0x156b4 mv t6, t4 *)
      stepb_ft TF_156b8 TD_156b8 ltac:(pin; cond_compute).  (* 0x156b8 beq s0, t2, 0x156c0 <static_init_tls+0xb0> *)
      sn TF_156bc TD_156bc.  (* 0x156bc mv t6, a7 *)
      stepb_tk TF_156c0 TD_156c0 ltac:(pin; cond_compute).  (* 0x156c0 bne s0, t3, 0x156e0 <static_init_tls+0xd0> *)
      sn TF_156e0 TD_156e0.  (* 0x156e0 mv a7, t6 *)
      sn TF_156e4 TD_156e4.  (* 0x156e4 j 0x1568c <static_init_tls+0x7c> *)
      sn TF_1568c TD_1568c.  (* 0x1568c addi a3, a3, -0x1 *)
      sn TF_15690 TD_15690.  (* 0x15690 add t4, t4, a0 *)
      stepb_ft TF_15694 TD_15694 ltac:(pin; cond_compute).  (* 0x15694 beqz a3, 0x156e8 <static_init_tls+0xd8> *)
      ld_step TF_15698 TD_15698 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_10120_4) ltac:(reflexivity).  (* 0x15698 lw s0, 0x0(t4) *)
      stepb_ft TF_1569c TD_1569c ltac:(pin; cond_compute).  (* 0x1569c beq s0, a6, 0x15684 <static_init_tls+0x74> *)
      stepb_tk TF_156a0 TD_156a0 ltac:(pin; cond_compute).  (* 0x156a0 beqz t0, 0x156b4 <static_init_tls+0xa4> *)
      sn TF_156b4 TD_156b4.  (* 0x156b4 mv t6, t4 *)
      stepb_ft TF_156b8 TD_156b8 ltac:(pin; cond_compute).  (* 0x156b8 beq s0, t2, 0x156c0 <static_init_tls+0xb0> *)
      sn TF_156bc TD_156bc.  (* 0x156bc mv t6, a7 *)
      stepb_tk TF_156c0 TD_156c0 ltac:(pin; cond_compute).  (* 0x156c0 bne s0, t3, 0x156e0 <static_init_tls+0xd0> *)
      sn TF_156e0 TD_156e0.  (* 0x156e0 mv a7, t6 *)
      sn TF_156e4 TD_156e4.  (* 0x156e4 j 0x1568c <static_init_tls+0x7c> *)
      sn TF_1568c TD_1568c.  (* 0x1568c addi a3, a3, -0x1 *)
      sn TF_15690 TD_15690.  (* 0x15690 add t4, t4, a0 *)
      stepb_ft TF_15694 TD_15694 ltac:(pin; cond_compute).  (* 0x15694 beqz a3, 0x156e8 <static_init_tls+0xd8> *)
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { ld_step TF_15698 TD_15698 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img s2img_10040_4) ltac:(reflexivity).  (* 0x15698 lw s0, 0x0(t4) *)
      stepb_tk TF_1569c TD_1569c ltac:(pin; cond_compute).  (* 0x1569c beq s0, a6, 0x15684 <static_init_tls+0x74> *)
      ld_step TF_15684 TD_15684 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img s2img_10050_8) ltac:(apply bytes_le_to_Z_8).  (* 0x15684 ld a2, 0x10(t4) *)
      sn TF_15688 TD_15688.  (* 0x15688 sub a2, a5, a2 *)
      sn TF_1568c TD_1568c.  (* 0x1568c addi a3, a3, -0x1 *)
      sn TF_15690 TD_15690.  (* 0x15690 add t4, t4, a0 *)
      stepb_ft TF_15694 TD_15694 ltac:(pin; cond_compute).  (* 0x15694 beqz a3, 0x156e8 <static_init_tls+0xd8> *)
      ld_step TF_15698 TD_15698 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_10078_4) ltac:(reflexivity).  (* 0x15698 lw s0, 0x0(t4) *)
      stepb_ft TF_1569c TD_1569c ltac:(pin; cond_compute).  (* 0x1569c beq s0, a6, 0x15684 <static_init_tls+0x74> *)
      stepb_tk TF_156a0 TD_156a0 ltac:(pin; cond_compute).  (* 0x156a0 beqz t0, 0x156b4 <static_init_tls+0xa4> *)
      sn TF_156b4 TD_156b4.  (* 0x156b4 mv t6, t4 *)
      stepb_ft TF_156b8 TD_156b8 ltac:(pin; cond_compute).  (* 0x156b8 beq s0, t2, 0x156c0 <static_init_tls+0xb0> *)
      sn TF_156bc TD_156bc.  (* 0x156bc mv t6, a7 *)
      stepb_tk TF_156c0 TD_156c0 ltac:(pin; cond_compute).  (* 0x156c0 bne s0, t3, 0x156e0 <static_init_tls+0xd0> *)
      sn TF_156e0 TD_156e0.  (* 0x156e0 mv a7, t6 *)
      sn TF_156e4 TD_156e4.  (* 0x156e4 j 0x1568c <static_init_tls+0x7c> *)
      sn TF_1568c TD_1568c.  (* 0x1568c addi a3, a3, -0x1 *)
      sn TF_15690 TD_15690.  (* 0x15690 add t4, t4, a0 *)
      stepb_ft TF_15694 TD_15694 ltac:(pin; cond_compute).  (* 0x15694 beqz a3, 0x156e8 <static_init_tls+0xd8> *)
      ld_step TF_15698 TD_15698 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_100b0_4) ltac:(reflexivity).  (* 0x15698 lw s0, 0x0(t4) *)
      stepb_ft TF_1569c TD_1569c ltac:(pin; cond_compute).  (* 0x1569c beq s0, a6, 0x15684 <static_init_tls+0x74> *)
      stepb_tk TF_156a0 TD_156a0 ltac:(pin; cond_compute).  (* 0x156a0 beqz t0, 0x156b4 <static_init_tls+0xa4> *)
      sn TF_156b4 TD_156b4.  (* 0x156b4 mv t6, t4 *)
      stepb_ft TF_156b8 TD_156b8 ltac:(pin; cond_compute).  (* 0x156b8 beq s0, t2, 0x156c0 <static_init_tls+0xb0> *)
      sn TF_156bc TD_156bc.  (* 0x156bc mv t6, a7 *)
      stepb_tk TF_156c0 TD_156c0 ltac:(pin; cond_compute).  (* 0x156c0 bne s0, t3, 0x156e0 <static_init_tls+0xd0> *)
      sn TF_156e0 TD_156e0.  (* 0x156e0 mv a7, t6 *)
      sn TF_156e4 TD_156e4.  (* 0x156e4 j 0x1568c <static_init_tls+0x7c> *)
      sn TF_1568c TD_1568c.  (* 0x1568c addi a3, a3, -0x1 *)
      sn TF_15690 TD_15690.  (* 0x15690 add t4, t4, a0 *)
      stepb_ft TF_15694 TD_15694 ltac:(pin; cond_compute).  (* 0x15694 beqz a3, 0x156e8 <static_init_tls+0xd8> *)
      ld_step TF_15698 TD_15698 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_100e8_4) ltac:(reflexivity).  (* 0x15698 lw s0, 0x0(t4) *)
      stepb_ft TF_1569c TD_1569c ltac:(pin; cond_compute).  (* 0x1569c beq s0, a6, 0x15684 <static_init_tls+0x74> *)
      stepb_tk TF_156a0 TD_156a0 ltac:(pin; cond_compute).  (* 0x156a0 beqz t0, 0x156b4 <static_init_tls+0xa4> *)
      sn TF_156b4 TD_156b4.  (* 0x156b4 mv t6, t4 *)
      stepb_ft TF_156b8 TD_156b8 ltac:(pin; cond_compute).  (* 0x156b8 beq s0, t2, 0x156c0 <static_init_tls+0xb0> *)
      sn TF_156bc TD_156bc.  (* 0x156bc mv t6, a7 *)
      stepb_tk TF_156c0 TD_156c0 ltac:(pin; cond_compute).  (* 0x156c0 bne s0, t3, 0x156e0 <static_init_tls+0xd0> *)
      sn TF_156e0 TD_156e0.  (* 0x156e0 mv a7, t6 *)
      sn TF_156e4 TD_156e4.  (* 0x156e4 j 0x1568c <static_init_tls+0x7c> *)
      sn TF_1568c TD_1568c.  (* 0x1568c addi a3, a3, -0x1 *)
      sn TF_15690 TD_15690.  (* 0x15690 add t4, t4, a0 *)
      stepb_ft TF_15694 TD_15694 ltac:(pin; cond_compute).  (* 0x15694 beqz a3, 0x156e8 <static_init_tls+0xd8> *)
      ld_step TF_15698 TD_15698 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_10120_4) ltac:(reflexivity).  (* 0x15698 lw s0, 0x0(t4) *)
      stepb_ft TF_1569c TD_1569c ltac:(pin; cond_compute).  (* 0x1569c beq s0, a6, 0x15684 <static_init_tls+0x74> *)
      stepb_tk TF_156a0 TD_156a0 ltac:(pin; cond_compute).  (* 0x156a0 beqz t0, 0x156b4 <static_init_tls+0xa4> *)
      sn TF_156b4 TD_156b4.  (* 0x156b4 mv t6, t4 *)
      stepb_ft TF_156b8 TD_156b8 ltac:(pin; cond_compute).  (* 0x156b8 beq s0, t2, 0x156c0 <static_init_tls+0xb0> *)
      sn TF_156bc TD_156bc.  (* 0x156bc mv t6, a7 *)
      stepb_tk TF_156c0 TD_156c0 ltac:(pin; cond_compute).  (* 0x156c0 bne s0, t3, 0x156e0 <static_init_tls+0xd0> *)
      sn TF_156e0 TD_156e0.  (* 0x156e0 mv a7, t6 *)
      sn TF_156e4 TD_156e4.  (* 0x156e4 j 0x1568c <static_init_tls+0x7c> *)
      sn TF_1568c TD_1568c.  (* 0x1568c addi a3, a3, -0x1 *)
      sn TF_15690 TD_15690.  (* 0x15690 add t4, t4, a0 *)
      stepb_ft TF_15694 TD_15694 ltac:(pin; cond_compute).  (* 0x15694 beqz a3, 0x156e8 <static_init_tls+0xd8> *)
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma tls_c3 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word), wfJ sp0 Jb -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) -> getr regs 3 = Z_to_bv 64 67584 -> getr regs 5 = Z_to_bv 64 0 -> getr regs 7 = Z_to_bv 64 7 -> getr regs 9 = Z_to_bv 64 327056 -> getr regs 10 = Z_to_bv 64 56 -> getr regs 11 = Z_to_bv 64 326408 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 5 -> getr regs 16 = Z_to_bv 64 6 -> getr regs 17 = Z_to_bv 64 0 -> getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 0 -> getr regs 25 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 0 -> getr regs 27 = Z_to_bv 64 0 -> getr regs 28 = Z_to_bv 64 1685382481 -> getr regs 29 = Z_to_bv 64 65880 -> getr regs 30 = Z_to_bv 64 131072 -> (forall regs', getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) -> getr regs' 3 = (Z_to_bv 64 67584) -> getr regs' 9 = (Z_to_bv 64 327056) -> getr regs' 11 = (Z_to_bv 64 326408) -> getr regs' 12 = (Z_to_bv 64 0) -> getr regs' 17 = (Z_to_bv 64 0) -> getr regs' 22 = (Z_to_bv 64 0) -> getr regs' 23 = (Z_to_bv 64 0) -> getr regs' 24 = (Z_to_bv 64 0) -> getr regs' 25 = (Z_to_bv 64 0) -> getr regs' 26 = (Z_to_bv 64 0) -> getr regs' 27 = (Z_to_bv 64 0) -> regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' -> G (mkst regs' (0x156e8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87040))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom)) -> G (mkst regs (0x15698 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87040))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H12 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { ld_step TF_15698 TD_15698 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img s2img_10158_4) ltac:(reflexivity).  (* 0x15698 lw s0, 0x0(t4) *)
      stepb_ft TF_1569c TD_1569c ltac:(pin; cond_compute).  (* 0x1569c beq s0, a6, 0x15684 <static_init_tls+0x74> *)
      stepb_tk TF_156a0 TD_156a0 ltac:(pin; cond_compute).  (* 0x156a0 beqz t0, 0x156b4 <static_init_tls+0xa4> *)
      sn TF_156b4 TD_156b4.  (* 0x156b4 mv t6, t4 *)
      stepb_ft TF_156b8 TD_156b8 ltac:(pin; cond_compute).  (* 0x156b8 beq s0, t2, 0x156c0 <static_init_tls+0xb0> *)
      sn TF_156bc TD_156bc.  (* 0x156bc mv t6, a7 *)
      stepb_tk TF_156c0 TD_156c0 ltac:(pin; cond_compute).  (* 0x156c0 bne s0, t3, 0x156e0 <static_init_tls+0xd0> *)
      sn TF_156e0 TD_156e0.  (* 0x156e0 mv a7, t6 *)
      sn TF_156e4 TD_156e4.  (* 0x156e4 j 0x1568c <static_init_tls+0x7c> *)
      sn TF_1568c TD_1568c.  (* 0x1568c addi a3, a3, -0x1 *)
      sn TF_15690 TD_15690.  (* 0x15690 add t4, t4, a0 *)
      stepb_ft TF_15694 TD_15694 ltac:(pin; cond_compute).  (* 0x15694 beqz a3, 0x156e8 <static_init_tls+0xd8> *)
      ld_step TF_15698 TD_15698 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img s2img_10190_4) ltac:(reflexivity).  (* 0x15698 lw s0, 0x0(t4) *)
      stepb_ft TF_1569c TD_1569c ltac:(pin; cond_compute).  (* 0x1569c beq s0, a6, 0x15684 <static_init_tls+0x74> *)
      stepb_tk TF_156a0 TD_156a0 ltac:(pin; cond_compute).  (* 0x156a0 beqz t0, 0x156b4 <static_init_tls+0xa4> *)
      sn TF_156b4 TD_156b4.  (* 0x156b4 mv t6, t4 *)
      stepb_ft TF_156b8 TD_156b8 ltac:(pin; cond_compute).  (* 0x156b8 beq s0, t2, 0x156c0 <static_init_tls+0xb0> *)
      sn TF_156bc TD_156bc.  (* 0x156bc mv t6, a7 *)
      stepb_tk TF_156c0 TD_156c0 ltac:(pin; cond_compute).  (* 0x156c0 bne s0, t3, 0x156e0 <static_init_tls+0xd0> *)
      sn TF_156e0 TD_156e0.  (* 0x156e0 mv a7, t6 *)
      sn TF_156e4 TD_156e4.  (* 0x156e4 j 0x1568c <static_init_tls+0x7c> *)
      sn TF_1568c TD_1568c.  (* 0x1568c addi a3, a3, -0x1 *)
      sn TF_15690 TD_15690.  (* 0x15690 add t4, t4, a0 *)
      stepb_ft TF_15694 TD_15694 ltac:(pin; cond_compute).  (* 0x15694 beqz a3, 0x156e8 <static_init_tls+0xd8> *)
      ld_step TF_15698 TD_15698 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img s2img_101c8_4) ltac:(reflexivity).  (* 0x15698 lw s0, 0x0(t4) *)
      stepb_ft TF_1569c TD_1569c ltac:(pin; cond_compute).  (* 0x1569c beq s0, a6, 0x15684 <static_init_tls+0x74> *)
      stepb_tk TF_156a0 TD_156a0 ltac:(pin; cond_compute).  (* 0x156a0 beqz t0, 0x156b4 <static_init_tls+0xa4> *)
      sn TF_156b4 TD_156b4.  (* 0x156b4 mv t6, t4 *)
      stepb_ft TF_156b8 TD_156b8 ltac:(pin; cond_compute).  (* 0x156b8 beq s0, t2, 0x156c0 <static_init_tls+0xb0> *)
      sn TF_156bc TD_156bc.  (* 0x156bc mv t6, a7 *)
      stepb_ft TF_156c0 TD_156c0 ltac:(pin; cond_compute).  (* 0x156c0 bne s0, t3, 0x156e0 <static_init_tls+0xd0> *)
      ld_step TF_156c4 TD_156c4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_101f0_8) ltac:(apply bytes_le_to_Z_8).  (* 0x156c4 ld a7, 0x28(t4) *)
      stepb_tk TF_156c8 TD_156c8 ltac:(pin; cond_compute).  (* 0x156c8 bgeu t5, a7, 0x156e0 <static_init_tls+0xd0> *)
      sn TF_156e0 TD_156e0.  (* 0x156e0 mv a7, t6 *)
      sn TF_156e4 TD_156e4.  (* 0x156e4 j 0x1568c <static_init_tls+0x7c> *)
      sn TF_1568c TD_1568c.  (* 0x1568c addi a3, a3, -0x1 *)
      sn TF_15690 TD_15690.  (* 0x15690 add t4, t4, a0 *)
      stepb_ft TF_15694 TD_15694 ltac:(pin; cond_compute).  (* 0x15694 beqz a3, 0x156e8 <static_init_tls+0xd8> *)
      ld_step TF_15698 TD_15698 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img s2img_10200_4) ltac:(reflexivity).  (* 0x15698 lw s0, 0x0(t4) *)
      stepb_ft TF_1569c TD_1569c ltac:(pin; cond_compute).  (* 0x1569c beq s0, a6, 0x15684 <static_init_tls+0x74> *)
      stepb_tk TF_156a0 TD_156a0 ltac:(pin; cond_compute).  (* 0x156a0 beqz t0, 0x156b4 <static_init_tls+0xa4> *)
      sn TF_156b4 TD_156b4.  (* 0x156b4 mv t6, t4 *)
      stepb_ft TF_156b8 TD_156b8 ltac:(pin; cond_compute).  (* 0x156b8 beq s0, t2, 0x156c0 <static_init_tls+0xb0> *)
      sn TF_156bc TD_156bc.  (* 0x156bc mv t6, a7 *)
      stepb_tk TF_156c0 TD_156c0 ltac:(pin; cond_compute).  (* 0x156c0 bne s0, t3, 0x156e0 <static_init_tls+0xd0> *)
      sn TF_156e0 TD_156e0.  (* 0x156e0 mv a7, t6 *)
      sn TF_156e4 TD_156e4.  (* 0x156e4 j 0x1568c <static_init_tls+0x7c> *)
      sn TF_1568c TD_1568c.  (* 0x1568c addi a3, a3, -0x1 *)
      sn TF_15690 TD_15690.  (* 0x15690 add t4, t4, a0 *)
      stepb_ft TF_15694 TD_15694 ltac:(pin; cond_compute).  (* 0x15694 beqz a3, 0x156e8 <static_init_tls+0xd8> *)
      ld_step TF_15698 TD_15698 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img s2img_10238_4) ltac:(reflexivity).  (* 0x15698 lw s0, 0x0(t4) *)
      stepb_ft TF_1569c TD_1569c ltac:(pin; cond_compute).  (* 0x1569c beq s0, a6, 0x15684 <static_init_tls+0x74> *)
      stepb_tk TF_156a0 TD_156a0 ltac:(pin; cond_compute).  (* 0x156a0 beqz t0, 0x156b4 <static_init_tls+0xa4> *)
      sn TF_156b4 TD_156b4.  (* 0x156b4 mv t6, t4 *)
      stepb_ft TF_156b8 TD_156b8 ltac:(pin; cond_compute).  (* 0x156b8 beq s0, t2, 0x156c0 <static_init_tls+0xb0> *)
      sn TF_156bc TD_156bc.  (* 0x156bc mv t6, a7 *)
      stepb_tk TF_156c0 TD_156c0 ltac:(pin; cond_compute).  (* 0x156c0 bne s0, t3, 0x156e0 <static_init_tls+0xd0> *)
      sn TF_156e0 TD_156e0.  (* 0x156e0 mv a7, t6 *)
      sn TF_156e4 TD_156e4.  (* 0x156e4 j 0x1568c <static_init_tls+0x7c> *)
      sn TF_1568c TD_1568c.  (* 0x1568c addi a3, a3, -0x1 *)
      sn TF_15690 TD_15690.  (* 0x15690 add t4, t4, a0 *)
      stepb_tk TF_15694 TD_15694 ltac:(pin; cond_compute).  (* 0x15694 beqz a3, 0x156e8 <static_init_tls+0xd8> *)
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { ld_step TF_15698 TD_15698 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img s2img_10158_4) ltac:(reflexivity).  (* 0x15698 lw s0, 0x0(t4) *)
      stepb_ft TF_1569c TD_1569c ltac:(pin; cond_compute).  (* 0x1569c beq s0, a6, 0x15684 <static_init_tls+0x74> *)
      stepb_tk TF_156a0 TD_156a0 ltac:(pin; cond_compute).  (* 0x156a0 beqz t0, 0x156b4 <static_init_tls+0xa4> *)
      sn TF_156b4 TD_156b4.  (* 0x156b4 mv t6, t4 *)
      stepb_ft TF_156b8 TD_156b8 ltac:(pin; cond_compute).  (* 0x156b8 beq s0, t2, 0x156c0 <static_init_tls+0xb0> *)
      sn TF_156bc TD_156bc.  (* 0x156bc mv t6, a7 *)
      stepb_tk TF_156c0 TD_156c0 ltac:(pin; cond_compute).  (* 0x156c0 bne s0, t3, 0x156e0 <static_init_tls+0xd0> *)
      sn TF_156e0 TD_156e0.  (* 0x156e0 mv a7, t6 *)
      sn TF_156e4 TD_156e4.  (* 0x156e4 j 0x1568c <static_init_tls+0x7c> *)
      sn TF_1568c TD_1568c.  (* 0x1568c addi a3, a3, -0x1 *)
      sn TF_15690 TD_15690.  (* 0x15690 add t4, t4, a0 *)
      stepb_ft TF_15694 TD_15694 ltac:(pin; cond_compute).  (* 0x15694 beqz a3, 0x156e8 <static_init_tls+0xd8> *)
      ld_step TF_15698 TD_15698 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img s2img_10190_4) ltac:(reflexivity).  (* 0x15698 lw s0, 0x0(t4) *)
      stepb_ft TF_1569c TD_1569c ltac:(pin; cond_compute).  (* 0x1569c beq s0, a6, 0x15684 <static_init_tls+0x74> *)
      stepb_tk TF_156a0 TD_156a0 ltac:(pin; cond_compute).  (* 0x156a0 beqz t0, 0x156b4 <static_init_tls+0xa4> *)
      sn TF_156b4 TD_156b4.  (* 0x156b4 mv t6, t4 *)
      stepb_ft TF_156b8 TD_156b8 ltac:(pin; cond_compute).  (* 0x156b8 beq s0, t2, 0x156c0 <static_init_tls+0xb0> *)
      sn TF_156bc TD_156bc.  (* 0x156bc mv t6, a7 *)
      stepb_tk TF_156c0 TD_156c0 ltac:(pin; cond_compute).  (* 0x156c0 bne s0, t3, 0x156e0 <static_init_tls+0xd0> *)
      sn TF_156e0 TD_156e0.  (* 0x156e0 mv a7, t6 *)
      sn TF_156e4 TD_156e4.  (* 0x156e4 j 0x1568c <static_init_tls+0x7c> *)
      sn TF_1568c TD_1568c.  (* 0x1568c addi a3, a3, -0x1 *)
      sn TF_15690 TD_15690.  (* 0x15690 add t4, t4, a0 *)
      stepb_ft TF_15694 TD_15694 ltac:(pin; cond_compute).  (* 0x15694 beqz a3, 0x156e8 <static_init_tls+0xd8> *)
      ld_step TF_15698 TD_15698 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img s2img_101c8_4) ltac:(reflexivity).  (* 0x15698 lw s0, 0x0(t4) *)
      stepb_ft TF_1569c TD_1569c ltac:(pin; cond_compute).  (* 0x1569c beq s0, a6, 0x15684 <static_init_tls+0x74> *)
      stepb_tk TF_156a0 TD_156a0 ltac:(pin; cond_compute).  (* 0x156a0 beqz t0, 0x156b4 <static_init_tls+0xa4> *)
      sn TF_156b4 TD_156b4.  (* 0x156b4 mv t6, t4 *)
      stepb_ft TF_156b8 TD_156b8 ltac:(pin; cond_compute).  (* 0x156b8 beq s0, t2, 0x156c0 <static_init_tls+0xb0> *)
      sn TF_156bc TD_156bc.  (* 0x156bc mv t6, a7 *)
      stepb_ft TF_156c0 TD_156c0 ltac:(pin; cond_compute).  (* 0x156c0 bne s0, t3, 0x156e0 <static_init_tls+0xd0> *)
      ld_step TF_156c4 TD_156c4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_101f0_8) ltac:(apply bytes_le_to_Z_8).  (* 0x156c4 ld a7, 0x28(t4) *)
      stepb_tk TF_156c8 TD_156c8 ltac:(pin; cond_compute).  (* 0x156c8 bgeu t5, a7, 0x156e0 <static_init_tls+0xd0> *)
      sn TF_156e0 TD_156e0.  (* 0x156e0 mv a7, t6 *)
      sn TF_156e4 TD_156e4.  (* 0x156e4 j 0x1568c <static_init_tls+0x7c> *)
      sn TF_1568c TD_1568c.  (* 0x1568c addi a3, a3, -0x1 *)
      sn TF_15690 TD_15690.  (* 0x15690 add t4, t4, a0 *)
      stepb_ft TF_15694 TD_15694 ltac:(pin; cond_compute).  (* 0x15694 beqz a3, 0x156e8 <static_init_tls+0xd8> *)
      ld_step TF_15698 TD_15698 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img s2img_10200_4) ltac:(reflexivity).  (* 0x15698 lw s0, 0x0(t4) *)
      stepb_ft TF_1569c TD_1569c ltac:(pin; cond_compute).  (* 0x1569c beq s0, a6, 0x15684 <static_init_tls+0x74> *)
      stepb_tk TF_156a0 TD_156a0 ltac:(pin; cond_compute).  (* 0x156a0 beqz t0, 0x156b4 <static_init_tls+0xa4> *)
      sn TF_156b4 TD_156b4.  (* 0x156b4 mv t6, t4 *)
      stepb_ft TF_156b8 TD_156b8 ltac:(pin; cond_compute).  (* 0x156b8 beq s0, t2, 0x156c0 <static_init_tls+0xb0> *)
      sn TF_156bc TD_156bc.  (* 0x156bc mv t6, a7 *)
      stepb_tk TF_156c0 TD_156c0 ltac:(pin; cond_compute).  (* 0x156c0 bne s0, t3, 0x156e0 <static_init_tls+0xd0> *)
      sn TF_156e0 TD_156e0.  (* 0x156e0 mv a7, t6 *)
      sn TF_156e4 TD_156e4.  (* 0x156e4 j 0x1568c <static_init_tls+0x7c> *)
      sn TF_1568c TD_1568c.  (* 0x1568c addi a3, a3, -0x1 *)
      sn TF_15690 TD_15690.  (* 0x15690 add t4, t4, a0 *)
      stepb_ft TF_15694 TD_15694 ltac:(pin; cond_compute).  (* 0x15694 beqz a3, 0x156e8 <static_init_tls+0xd8> *)
      ld_step TF_15698 TD_15698 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img s2img_10238_4) ltac:(reflexivity).  (* 0x15698 lw s0, 0x0(t4) *)
      stepb_ft TF_1569c TD_1569c ltac:(pin; cond_compute).  (* 0x1569c beq s0, a6, 0x15684 <static_init_tls+0x74> *)
      stepb_tk TF_156a0 TD_156a0 ltac:(pin; cond_compute).  (* 0x156a0 beqz t0, 0x156b4 <static_init_tls+0xa4> *)
      sn TF_156b4 TD_156b4.  (* 0x156b4 mv t6, t4 *)
      stepb_ft TF_156b8 TD_156b8 ltac:(pin; cond_compute).  (* 0x156b8 beq s0, t2, 0x156c0 <static_init_tls+0xb0> *)
      sn TF_156bc TD_156bc.  (* 0x156bc mv t6, a7 *)
      stepb_tk TF_156c0 TD_156c0 ltac:(pin; cond_compute).  (* 0x156c0 bne s0, t3, 0x156e0 <static_init_tls+0xd0> *)
      sn TF_156e0 TD_156e0.  (* 0x156e0 mv a7, t6 *)
      sn TF_156e4 TD_156e4.  (* 0x156e4 j 0x1568c <static_init_tls+0x7c> *)
      sn TF_1568c TD_1568c.  (* 0x1568c addi a3, a3, -0x1 *)
      sn TF_15690 TD_15690.  (* 0x15690 add t4, t4, a0 *)
      stepb_tk TF_15694 TD_15694 ltac:(pin; cond_compute).  (* 0x15694 beqz a3, 0x156e8 <static_init_tls+0xd8> *)
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma tls_c4 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word), wfJ sp0 Jb -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) -> getr regs 3 = Z_to_bv 64 67584 -> getr regs 9 = Z_to_bv 64 327056 -> getr regs 11 = Z_to_bv 64 326408 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 17 = Z_to_bv 64 0 -> getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 0 -> getr regs 25 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 0 -> getr regs 27 = Z_to_bv 64 0 -> (forall regs', getr regs' 1 = (Z_to_bv 64 88132) -> getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) -> getr regs' 3 = (Z_to_bv 64 67584) -> getr regs' 4 = (Z_to_bv 64 195328) -> getr regs' 8 = (Z_to_bv 64 195328) -> getr regs' 10 = (Z_to_bv 64 326408) -> getr regs' 11 = (Z_to_bv 64 327112) -> getr regs' 12 = (Z_to_bv 64 0) -> getr regs' 13 = (Z_to_bv 64 195120) -> getr regs' 14 = (Z_to_bv 64 0) -> getr regs' 15 = (Z_to_bv 64 18446744073709356288) -> getr regs' 17 = (Z_to_bv 64 96) -> getr regs' 18 = (Z_to_bv 64 195128) -> getr regs' 19 = (Z_to_bv 64 0) -> getr regs' 20 = (Z_to_bv 64 195344) -> getr regs' 22 = (Z_to_bv 64 0) -> getr regs' 23 = (Z_to_bv 64 0) -> getr regs' 24 = (Z_to_bv 64 0) -> getr regs' 25 = (Z_to_bv 64 0) -> getr regs' 26 = (Z_to_bv 64 0) -> getr regs' 27 = (Z_to_bv 64 0) -> regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' -> G (mkst regs' (0x1586c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87040))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 326440) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 326456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 326448) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 327080) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 327088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 195344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 195320) (word_to_le_bytes 8 (Z_to_bv 64 195344))) (Z_to_bv 64 195128) (word_to_le_bytes 8 (Z_to_bv 64 195128))) (Z_to_bv 64 327056) ([Z_to_bv 8 1])) (Z_to_bv 64 195168) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) -> G (mkst regs (0x156e8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87040))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H12 H17 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { stepb_tk TF_156e8 TD_156e8 ltac:(pin; cond_compute).  (* 0x156e8 beqz a7, 0x15720 <static_init_tls+0x110> *)
      ld_step TF_15720 TD_15720 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_4fb18_8) ltac:(apply bytes_le_to_Z_8).  (* 0x15720 ld a2, 0x10(a1) *)
      ld_step TF_15724 TD_15724 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_4fb28_8) ltac:(apply bytes_le_to_Z_8).  (* 0x15724 ld a3, 0x20(a1) *)
      ld_step TF_15728 TD_15728 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_4fb30_8) ltac:(apply bytes_le_to_Z_8).  (* 0x15728 ld a0, 0x28(a1) *)
      sn TF_1572c TD_1572c.  (* 0x1572c add a4, a3, a2 *)
      sn TF_15730 TD_15730.  (* 0x15730 addi a5, a0, -0x1 *)
      sn TF_15734 TD_15734.  (* 0x15734 neg a4, a4 *)
      sn TF_15738 TD_15738.  (* 0x15738 and a2, a5, a2 *)
      sn TF_1573c TD_1573c.  (* 0x1573c and a4, a5, a4 *)
      sn TF_15740 TD_15740.  (* 0x15740 li a5, 0x7 *)
      sn TF_15744 TD_15744.  (* 0x15744 add a3, a4, a3 *)
      stw TF_15748 TD_15748 (Z_to_bv 64 326440) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x15748 sd a3, 0x20(a1) *)
      stw TF_1574c TD_1574c (Z_to_bv 64 326456) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x1574c sd a2, 0x30(a1) *)
      stepb_ft TF_15750 TD_15750 ltac:(pin; cond_compute).  (* 0x15750 bltu a5, a0, 0x1575c <static_init_tls+0x14c> *)
      sn TF_15754 TD_15754.  (* 0x15754 li a0, 0x8 *)
      stw TF_15758 TD_15758 (Z_to_bv 64 326448) (Z_to_bv 64 8) ltac:(ok_data).  (* 0x15758 sd a0, 0x28(a1) *)
      sn TF_1575c TD_1575c.  (* 0x1575c add a2, a2, a3 *)
      sn TF_15760 TD_15760.  (* 0x15760 lui a1, 0x20 *)
      sn TF_15764 TD_15764.  (* 0x15764 add a2, a2, a0 *)
      sn TF_15768 TD_15768.  (* 0x15768 addiw a3, a1, 0xd1 *)
      sn TF_1576c TD_1576c.  (* 0x1576c addi a1, a2, 0xdf *)
      sn TF_15770 TD_15770.  (* 0x15770 andi a1, a1, -0x8 *)
      stw TF_15774 TD_15774 (Z_to_bv 64 327080) (Z_to_bv 64 224) ltac:(ok_data).  (* 0x15774 sd a1, 0x18(s1) *)
      stw TF_15778 TD_15778 (Z_to_bv 64 327088) (Z_to_bv 64 8) ltac:(ok_data).  (* 0x15778 sd a0, 0x20(s1) *)
      stepb_tk TF_1577c TD_1577c ltac:(pin; cond_compute).  (* 0x1577c bltu a1, a3, 0x157b0 <static_init_tls+0x1a0> *)
      sn TF_157b0 TD_157b0.  (* 0x157b0 auipc a3, 0x1a *)
      ld_step TF_157b4 TD_157b4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_4fda0_8) ltac:(apply bytes_le_to_Z_8).  (* 0x157b4 ld s3, 0x10(s1) *)
      ld_step TF_157b8 TD_157b8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_4fdb8_8) ltac:(apply bytes_le_to_Z_8).  (* 0x157b8 ld a2, 0x28(s1) *)
      sn TF_157bc TD_157bc.  (* 0x157bc addi a4, a0, -0x1 *)
      sn TF_157c0 TD_157c0.  (* 0x157c0 li a5, -0xc8 *)
      sn TF_157c4 TD_157c4.  (* 0x157c4 addi a0, a3, 0x288 *)
      sn TF_157c8 TD_157c8.  (* 0x157c8 sub a5, a5, a0 *)
      sn TF_157cc TD_157cc.  (* 0x157cc and a4, a4, a5 *)
      sn TF_157d0 TD_157d0.  (* 0x157d0 not a3, a2 *)
      sn TF_157d4 TD_157d4.  (* 0x157d4 add s2, a0, a4 *)
      sn TF_157d8 TD_157d8.  (* 0x157d8 slli a3, a3, 0x3 *)
      sn TF_157dc TD_157dc.  (* 0x157dc add a3, a0, a3 *)
      sn TF_157e0 TD_157e0.  (* 0x157e0 add s4, a3, a1 *)
      sn TF_157e4 TD_157e4.  (* 0x157e4 addi s0, s2, 0xc8 *)
      stepb_tk TF_157e8 TD_157e8 ltac:(pin; cond_compute).  (* 0x157e8 beqz s3, 0x15830 <static_init_tls+0x220> *)
      stw TF_15830 TD_15830 (Z_to_bv 64 195344) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x15830 sd a2, 0x0(s4) *)
      stw TF_15834 TD_15834 (Z_to_bv 64 195320) (Z_to_bv 64 195344) ltac:(ok_data).  (* 0x15834 sd s4, 0xc0(s2) *)
      stw TF_15838 TD_15838 (Z_to_bv 64 195128) (Z_to_bv 64 195128) ltac:(ok_data).  (* 0x15838 sd s2, 0x0(s2) *)
      sn TF_1583c TD_1583c.  (* 0x1583c mv a0, s0 *)
      sn TF_15840 TD_15840.  (* 0x15840 jal 0x1d634 <__set_thread_area> *)
      sn F_1d594 D_1d594.  (* 0x1d634 mv tp, a0 *)
      sn F_1d598 D_1d598.  (* 0x1d638 li a0, 0x0 *)
      stepret F_1d59c D_1d59c (0x15844 : word) ltac:(pin; first [reflexivity | bveq]).  (* 0x1d63c ret *)
      stepb_ft TF_15844 TD_15844 ltac:(pin; cond_compute).  (* 0x15844 bltz a0, 0x15898 <static_init_tls+0x288> *)
      stepb_ft TF_15848 TD_15848 ltac:(pin; cond_compute).  (* 0x15848 bnez a0, 0x15854 <static_init_tls+0x244> *)
      sn TF_1584c TD_1584c.  (* 0x1584c li a0, 0x1 *)
      stw TF_15850 TD_15850 (Z_to_bv 64 327056) (Z_to_bv 64 1) ltac:(ok_data).  (* 0x15850 sb a0, 0x0(s1) *)
      sn TF_15854 TD_15854.  (* 0x15854 li a0, 0x2 *)
      sn TF_15858 TD_15858.  (* 0x15858 auipc a1, 0x3a *)
      stw TF_1585c TD_1585c (Z_to_bv 64 195168) (Z_to_bv 64 2) ltac:(ok_data).  (* 0x1585c sw a0, 0x28(s2) *)
      sn TF_15860 TD_15860.  (* 0x15860 li a7, 0x60 *)
      sn TF_15864 TD_15864.  (* 0x15864 addi a0, a1, 0x2b0 *)
      sn TF_15868 TD_15868.  (* 0x15868 addi a1, s1, 0x38 *)
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { stepb_tk TF_156e8 TD_156e8 ltac:(pin; cond_compute).  (* 0x156e8 beqz a7, 0x15720 <static_init_tls+0x110> *)
      ld_step TF_15720 TD_15720 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_4fb18_8) ltac:(apply bytes_le_to_Z_8).  (* 0x15720 ld a2, 0x10(a1) *)
      ld_step TF_15724 TD_15724 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_4fb28_8) ltac:(apply bytes_le_to_Z_8).  (* 0x15724 ld a3, 0x20(a1) *)
      ld_step TF_15728 TD_15728 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_4fb30_8) ltac:(apply bytes_le_to_Z_8).  (* 0x15728 ld a0, 0x28(a1) *)
      sn TF_1572c TD_1572c.  (* 0x1572c add a4, a3, a2 *)
      sn TF_15730 TD_15730.  (* 0x15730 addi a5, a0, -0x1 *)
      sn TF_15734 TD_15734.  (* 0x15734 neg a4, a4 *)
      sn TF_15738 TD_15738.  (* 0x15738 and a2, a5, a2 *)
      sn TF_1573c TD_1573c.  (* 0x1573c and a4, a5, a4 *)
      sn TF_15740 TD_15740.  (* 0x15740 li a5, 0x7 *)
      sn TF_15744 TD_15744.  (* 0x15744 add a3, a4, a3 *)
      stw TF_15748 TD_15748 (Z_to_bv 64 326440) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x15748 sd a3, 0x20(a1) *)
      stw TF_1574c TD_1574c (Z_to_bv 64 326456) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x1574c sd a2, 0x30(a1) *)
      stepb_ft TF_15750 TD_15750 ltac:(pin; cond_compute).  (* 0x15750 bltu a5, a0, 0x1575c <static_init_tls+0x14c> *)
      sn TF_15754 TD_15754.  (* 0x15754 li a0, 0x8 *)
      stw TF_15758 TD_15758 (Z_to_bv 64 326448) (Z_to_bv 64 8) ltac:(ok_data).  (* 0x15758 sd a0, 0x28(a1) *)
      sn TF_1575c TD_1575c.  (* 0x1575c add a2, a2, a3 *)
      sn TF_15760 TD_15760.  (* 0x15760 lui a1, 0x20 *)
      sn TF_15764 TD_15764.  (* 0x15764 add a2, a2, a0 *)
      sn TF_15768 TD_15768.  (* 0x15768 addiw a3, a1, 0xd1 *)
      sn TF_1576c TD_1576c.  (* 0x1576c addi a1, a2, 0xdf *)
      sn TF_15770 TD_15770.  (* 0x15770 andi a1, a1, -0x8 *)
      stw TF_15774 TD_15774 (Z_to_bv 64 327080) (Z_to_bv 64 224) ltac:(ok_data).  (* 0x15774 sd a1, 0x18(s1) *)
      stw TF_15778 TD_15778 (Z_to_bv 64 327088) (Z_to_bv 64 8) ltac:(ok_data).  (* 0x15778 sd a0, 0x20(s1) *)
      stepb_tk TF_1577c TD_1577c ltac:(pin; cond_compute).  (* 0x1577c bltu a1, a3, 0x157b0 <static_init_tls+0x1a0> *)
      sn TF_157b0 TD_157b0.  (* 0x157b0 auipc a3, 0x1a *)
      ld_step TF_157b4 TD_157b4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_4fda0_8) ltac:(apply bytes_le_to_Z_8).  (* 0x157b4 ld s3, 0x10(s1) *)
      ld_step TF_157b8 TD_157b8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_4fdb8_8) ltac:(apply bytes_le_to_Z_8).  (* 0x157b8 ld a2, 0x28(s1) *)
      sn TF_157bc TD_157bc.  (* 0x157bc addi a4, a0, -0x1 *)
      sn TF_157c0 TD_157c0.  (* 0x157c0 li a5, -0xc8 *)
      sn TF_157c4 TD_157c4.  (* 0x157c4 addi a0, a3, 0x288 *)
      sn TF_157c8 TD_157c8.  (* 0x157c8 sub a5, a5, a0 *)
      sn TF_157cc TD_157cc.  (* 0x157cc and a4, a4, a5 *)
      sn TF_157d0 TD_157d0.  (* 0x157d0 not a3, a2 *)
      sn TF_157d4 TD_157d4.  (* 0x157d4 add s2, a0, a4 *)
      sn TF_157d8 TD_157d8.  (* 0x157d8 slli a3, a3, 0x3 *)
      sn TF_157dc TD_157dc.  (* 0x157dc add a3, a0, a3 *)
      sn TF_157e0 TD_157e0.  (* 0x157e0 add s4, a3, a1 *)
      sn TF_157e4 TD_157e4.  (* 0x157e4 addi s0, s2, 0xc8 *)
      stepb_tk TF_157e8 TD_157e8 ltac:(pin; cond_compute).  (* 0x157e8 beqz s3, 0x15830 <static_init_tls+0x220> *)
      stw TF_15830 TD_15830 (Z_to_bv 64 195344) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x15830 sd a2, 0x0(s4) *)
      stw TF_15834 TD_15834 (Z_to_bv 64 195320) (Z_to_bv 64 195344) ltac:(ok_data).  (* 0x15834 sd s4, 0xc0(s2) *)
      stw TF_15838 TD_15838 (Z_to_bv 64 195128) (Z_to_bv 64 195128) ltac:(ok_data).  (* 0x15838 sd s2, 0x0(s2) *)
      sn TF_1583c TD_1583c.  (* 0x1583c mv a0, s0 *)
      sn TF_15840 TD_15840.  (* 0x15840 jal 0x1d634 <__set_thread_area> *)
      sn F_1d594 D_1d594.  (* 0x1d634 mv tp, a0 *)
      sn F_1d598 D_1d598.  (* 0x1d638 li a0, 0x0 *)
      stepret F_1d59c D_1d59c (0x15844 : word) ltac:(pin; first [reflexivity | bveq]).  (* 0x1d63c ret *)
      stepb_ft TF_15844 TD_15844 ltac:(pin; cond_compute).  (* 0x15844 bltz a0, 0x15898 <static_init_tls+0x288> *)
      stepb_ft TF_15848 TD_15848 ltac:(pin; cond_compute).  (* 0x15848 bnez a0, 0x15854 <static_init_tls+0x244> *)
      sn TF_1584c TD_1584c.  (* 0x1584c li a0, 0x1 *)
      stw TF_15850 TD_15850 (Z_to_bv 64 327056) (Z_to_bv 64 1) ltac:(ok_data).  (* 0x15850 sb a0, 0x0(s1) *)
      sn TF_15854 TD_15854.  (* 0x15854 li a0, 0x2 *)
      sn TF_15858 TD_15858.  (* 0x15858 auipc a1, 0x3a *)
      stw TF_1585c TD_1585c (Z_to_bv 64 195168) (Z_to_bv 64 2) ltac:(ok_data).  (* 0x1585c sw a0, 0x28(s2) *)
      sn TF_15860 TD_15860.  (* 0x15860 li a7, 0x60 *)
      sn TF_15864 TD_15864.  (* 0x15864 addi a0, a1, 0x2b0 *)
      sn TF_15868 TD_15868.  (* 0x15868 addi a1, s1, 0x38 *)
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma tls_c5 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word), wfJ sp0 Jb -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) -> getr regs 3 = Z_to_bv 64 67584 -> getr regs 4 = Z_to_bv 64 195328 -> getr regs 10 = tid -> getr regs 11 = Z_to_bv 64 327112 -> getr regs 18 = Z_to_bv 64 195128 -> getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 0 -> getr regs 25 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 0 -> getr regs 27 = Z_to_bv 64 0 -> (forall regs', getr regs' 1 = (Z_to_bv 64 87040) -> getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) -> getr regs' 3 = (Z_to_bv 64 67584) -> getr regs' 4 = (Z_to_bv 64 195328) -> getr regs' 8 = (pn_w inp rdraw) -> getr regs' 9 = (s1v) -> getr regs' 10 = (Z_to_bv 64 0) -> getr regs' 12 = (Z_to_bv 64 195248) -> getr regs' 18 = (Z_to_bv 64 327056) -> getr regs' 19 = (Z_to_bv 64 0) -> getr regs' 20 = (Z_to_bv 64 0) -> getr regs' 21 = (Z_to_bv 64 0) -> getr regs' 22 = (Z_to_bv 64 0) -> getr regs' 23 = (Z_to_bv 64 0) -> getr regs' 24 = (Z_to_bv 64 0) -> getr regs' 25 = (Z_to_bv 64 0) -> getr regs' 26 = (Z_to_bv 64 0) -> getr regs' 27 = (Z_to_bv 64 0) -> regs_agree (fun r => In r [1; 2; 8; 9; 10; 12; 18; 19; 20; 21]%list) regs regs' -> G (mkst regs' (0x15400 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87040))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 326440) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 326456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 326448) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 327080) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 327088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 195344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 195320) (word_to_le_bytes 8 (Z_to_bv 64 195344))) (Z_to_bv 64 195128) (word_to_le_bytes 8 (Z_to_bv 64 195128))) (Z_to_bv 64 327056) ([Z_to_bv 8 1])) (Z_to_bv 64 195168) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 195160) (word_to_le_bytes 4 tid)) (Z_to_bv 64 195280) (word_to_le_bytes 8 (Z_to_bv 64 327112))) (Z_to_bv 64 195248) (word_to_le_bytes 8 (Z_to_bv 64 195248))) (Z_to_bv 64 195136) (word_to_le_bytes 8 (Z_to_bv 64 195128))) (Z_to_bv 64 195144) (word_to_le_bytes 8 (Z_to_bv 64 195128))) (Z_to_bv 64 195152) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) -> G (mkst regs (0x15870 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87040))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 326440) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 326456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 326448) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 327080) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 327088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 195344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 195320) (word_to_le_bytes 8 (Z_to_bv 64 195344))) (Z_to_bv 64 195128) (word_to_le_bytes 8 (Z_to_bv 64 195128))) (Z_to_bv 64 327056) ([Z_to_bv 8 1])) (Z_to_bv 64 195168) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { sn TF_15870 TD_15870.  (* 0x15870 addi a2, s2, 0x78 *)
      stw TF_15874 TD_15874 (Z_to_bv 64 195160) (tid) ltac:(ok_data).  (* 0x15874 sw a0, 0x20(s2) *)
      stw TF_15878 TD_15878 (Z_to_bv 64 195280) (Z_to_bv 64 327112) ltac:(ok_data).  (* 0x15878 sd a1, 0x98(s2) *)
      stw TF_1587c TD_1587c (Z_to_bv 64 195248) (Z_to_bv 64 195248) ltac:(ok_data).  (* 0x1587c sd a2, 0x78(s2) *)
      sn TF_15880 TD_15880.  (* 0x15880 auipc a0, 0x3a *)
      ld_step TF_15884 TD_15884 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_4fd78_8) ltac:(apply bytes_le_to_Z_8).  (* 0x15884 ld a0, 0x4f8(a0) *)
      stw TF_15888 TD_15888 (Z_to_bv 64 195136) (Z_to_bv 64 195128) ltac:(ok_data).  (* 0x15888 sd s2, 0x8(s2) *)
      stw TF_1588c TD_1588c (Z_to_bv 64 195144) (Z_to_bv 64 195128) ltac:(ok_data).  (* 0x1588c sd s2, 0x10(s2) *)
      stw TF_15890 TD_15890 (Z_to_bv 64 195152) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x15890 sd a0, 0x18(s2) *)
      sn TF_15894 TD_15894.  (* 0x15894 j 0x1589c <static_init_tls+0x28c> *)
      ld_step TF_1589c TD_1589c (word_to_le_bytes 8 (Z_to_bv 64 87040)) (Z_to_bv 64 87040) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x1589c ld ra, 0x38(sp) *)
      ld_step TF_158a0 TD_158a0 (word_to_le_bytes 8 (pn_w inp rdraw)) (pn_w inp rdraw) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x158a0 ld s0, 0x30(sp) *)
      ld_step TF_158a4 TD_158a4 (word_to_le_bytes 8 s1v) (s1v) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x158a4 ld s1, 0x28(sp) *)
      ld_step TF_158a8 TD_158a8 (word_to_le_bytes 8 (Z_to_bv 64 327056)) (Z_to_bv 64 327056) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x158a8 ld s2, 0x20(sp) *)
      ld_step TF_158ac TD_158ac (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x158ac ld s3, 0x18(sp) *)
      ld_step TF_158b0 TD_158b0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x158b0 ld s4, 0x10(sp) *)
      ld_step TF_158b4 TD_158b4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x158b4 ld s5, 0x8(sp) *)
      sv TF_158b8 TD_158b8 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* 0x158b8 addi sp, sp, 0x40 *)
      stepret TF_158bc TD_158bc (0x15400 : word) ltac:(pin; first [reflexivity | bveq]).  (* 0x158bc ret *)
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { sn TF_15870 TD_15870.  (* 0x15870 addi a2, s2, 0x78 *)
      stw TF_15874 TD_15874 (Z_to_bv 64 195160) (tid) ltac:(ok_data).  (* 0x15874 sw a0, 0x20(s2) *)
      stw TF_15878 TD_15878 (Z_to_bv 64 195280) (Z_to_bv 64 327112) ltac:(ok_data).  (* 0x15878 sd a1, 0x98(s2) *)
      stw TF_1587c TD_1587c (Z_to_bv 64 195248) (Z_to_bv 64 195248) ltac:(ok_data).  (* 0x1587c sd a2, 0x78(s2) *)
      sn TF_15880 TD_15880.  (* 0x15880 auipc a0, 0x3a *)
      ld_step TF_15884 TD_15884 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_4fd78_8) ltac:(apply bytes_le_to_Z_8).  (* 0x15884 ld a0, 0x4f8(a0) *)
      stw TF_15888 TD_15888 (Z_to_bv 64 195136) (Z_to_bv 64 195128) ltac:(ok_data).  (* 0x15888 sd s2, 0x8(s2) *)
      stw TF_1588c TD_1588c (Z_to_bv 64 195144) (Z_to_bv 64 195128) ltac:(ok_data).  (* 0x1588c sd s2, 0x10(s2) *)
      stw TF_15890 TD_15890 (Z_to_bv 64 195152) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x15890 sd a0, 0x18(s2) *)
      sn TF_15894 TD_15894.  (* 0x15894 j 0x1589c <static_init_tls+0x28c> *)
      ld_step TF_1589c TD_1589c (word_to_le_bytes 8 (Z_to_bv 64 87040)) (Z_to_bv 64 87040) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x1589c ld ra, 0x38(sp) *)
      ld_step TF_158a0 TD_158a0 (word_to_le_bytes 8 (pn_w inp rdraw)) (pn_w inp rdraw) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x158a0 ld s0, 0x30(sp) *)
      ld_step TF_158a4 TD_158a4 (word_to_le_bytes 8 s1v) (s1v) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x158a4 ld s1, 0x28(sp) *)
      ld_step TF_158a8 TD_158a8 (word_to_le_bytes 8 (Z_to_bv 64 327056)) (Z_to_bv 64 327056) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x158a8 ld s2, 0x20(sp) *)
      ld_step TF_158ac TD_158ac (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x158ac ld s3, 0x18(sp) *)
      ld_step TF_158b0 TD_158b0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x158b0 ld s4, 0x10(sp) *)
      ld_step TF_158b4 TD_158b4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x158b4 ld s5, 0x8(sp) *)
      sv TF_158b8 TD_158b8 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* 0x158b8 addi sp, sp, 0x40 *)
      stepret TF_158bc TD_158bc (0x15400 : word) ltac:(pin; first [reflexivity | bveq]).  (* 0x158bc ret *)
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

End P4.
