(* elf , front , img own, defs ,
   statements (TEMPLATE; synthesized from the run), context , conventions ;
   valtac4: 'reflexivity' from 'WalkTac.v stepld_pc value side; S0Startup2.v F_152d4'; split-rseq all. *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import RunCtx.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.World Require Import Tgt_checksum_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import StartupTac ArgvEnv RefLayout U0StartupDefs U0_code_15000_16000 U0_code_1d000_1d8c4.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import LiaFast.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require L10Walk.
Ltac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.StepTac.chain_step ::= OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_chain_step.
Abbreviation SEGS := Tgt_checksum_fuzzer_ubsan.M.loaded_segments.
Abbreviation RPH := Tgt_checksum_fuzzer_ubsan.M.phdrs.
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
Lemma s2img_1e990_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 125328) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_1fc28_4 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 130088) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
Lemma s2img_4fd98_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 327064) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_4fda8_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 327080) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_4fdb0_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 327088) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_4fff8_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 327672) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_50020_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 327712) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma s2img_50038_8 {RCa1 : RunCtx} : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments SEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 327736) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
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
Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH (Z_to_bv 64 (Z.of_N Tgt_checksum_fuzzer_ubsan.M.init_pc)) sp0 rdraw)) (only parsing).

  Lemma tls_c1 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word), wfJ sp0 Jb -> getr regs 1 = Z_to_bv 64 87684 -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) -> getr regs 3 = Z_to_bv 64 67584 -> getr regs 8 = pn_w inp rdraw -> getr regs 9 = s1v -> getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) -> getr regs 18 = Z_to_bv 64 327696 -> getr regs 19 = Z_to_bv 64 0 -> getr regs 20 = Z_to_bv 64 0 -> getr regs 21 = Z_to_bv 64 0 -> getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 0 -> getr regs 25 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 0 -> getr regs 27 = Z_to_bv 64 0 -> (forall regs', getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) -> getr regs' 3 = (Z_to_bv 64 67584) -> getr regs' 5 = (Z_to_bv 64 0) -> getr regs' 7 = (Z_to_bv 64 7) -> getr regs' 9 = (Z_to_bv 64 327696) -> getr regs' 10 = (Z_to_bv 64 56) -> getr regs' 11 = (Z_to_bv 64 327048) -> getr regs' 12 = (Z_to_bv 64 0) -> getr regs' 13 = (Z_to_bv 64 10) -> getr regs' 15 = (Z_to_bv 64 65600) -> getr regs' 16 = (Z_to_bv 64 6) -> getr regs' 17 = (Z_to_bv 64 0) -> getr regs' 22 = (Z_to_bv 64 0) -> getr regs' 23 = (Z_to_bv 64 0) -> getr regs' 24 = (Z_to_bv 64 0) -> getr regs' 25 = (Z_to_bv 64 0) -> getr regs' 26 = (Z_to_bv 64 0) -> getr regs' 27 = (Z_to_bv 64 0) -> getr regs' 28 = (Z_to_bv 64 1685382481) -> getr regs' 29 = (Z_to_bv 64 65600) -> getr regs' 30 = (Z_to_bv 64 131072) -> regs_agree (fun r => In r [2; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30]%list) regs regs' -> G (mkst regs' (0x1591c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87684))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327696))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom)) -> G (mkst regs (0x15894 : word) (CM (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (D_libc sp0 inp rdraw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { sv F_157e8 D_157e8 (Z_to_bv 64 (bv_unsigned sp0 - 480)).  (* 0x15894 addi sp, sp, -0x40 *)
      stw TF_15898 TD_15898 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 87684) ltac:(ok_win HJ).  (* 0x15898 sd ra, 0x38(sp) *)
      stw TF_1589c TD_1589c (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w inp rdraw) ltac:(ok_win HJ).  (* 0x1589c sd s0, 0x30(sp) *)
      stw TF_158a0 TD_158a0 (Z_to_bv 64 (bv_unsigned sp0 - 440)) (s1v) ltac:(ok_win HJ).  (* 0x158a0 sd s1, 0x28(sp) *)
      stw TF_158a4 TD_158a4 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 327696) ltac:(ok_win HJ).  (* 0x158a4 sd s2, 0x20(sp) *)
      stw TF_158a8 TD_158a8 (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x158a8 sd s3, 0x18(sp) *)
      stw TF_158ac TD_158ac (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x158ac sd s4, 0x10(sp) *)
      stw TF_158b0 TD_158b0 (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x158b0 sd s5, 0x8(sp) *)
      ld_step TF_158b4 TD_158b4 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x158b4 ld a3, 0x28(a0) *)
      sn TF_158b8 TD_158b8.  (* 0x158b8 auipc a1, 0x3a *)
      sn TF_158bc TD_158bc.  (* 0x158bc addi a1, a1, 0x4d0 *)
      sn TF_158c0 TD_158c0.  (* 0x158c0 auipc a2, 0x3a *)
      sn TF_158c4 TD_158c4.  (* 0x158c4 addi s1, a2, 0x750 *)
      stepb_ft TF_158c8 TD_158c8 ltac:(pin; cond_compute).  (* 0x158c8 beqz a3, 0x159a4 <static_init_tls+0x110> *)
      sn TF_158cc TD_158cc.  (* 0x158cc li a2, 0x0 *)
      sn TF_158d0 TD_158d0.  (* 0x158d0 li a7, 0x0 *)
      sn TF_158d4 TD_158d4.  (* 0x158d4 auipc a4, 0xa *)
      ld_step TF_158d8 TD_158d8 (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x158d8 ld a5, 0x18(a0) *)
      ld_step TF_158dc TD_158dc (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x158dc ld a0, 0x20(a0) *)
      sn TF_158e0 TD_158e0.  (* 0x158e0 li a6, 0x6 *)
      sn TF_158e4 TD_158e4.  (* 0x158e4 auipc t0, 0x9 *)
      ld_step TF_158e8 TD_158e8 (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img s2img_1fc28_4) ltac:(reflexivity).  (* 0x158e8 lwu t5, 0x354(a4) *)
      ld_step TF_158ec TD_158ec (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_1e990_8) ltac:(apply bytes_le_to_Z_8).  (* 0x158ec ld t0, 0xac(t0) *)
      sn TF_158f0 TD_158f0.  (* 0x158f0 li t1, 0x2 *)
      sn TF_158f4 TD_158f4.  (* 0x158f4 li t2, 0x7 *)
      sn TF_158f8 TD_158f8.  (* 0x158f8 lui t3, 0x6474e *)
      sn TF_158fc TD_158fc.  (* 0x158fc addiw t3, t3, 0x551 *)
      sn TF_15900 TD_15900.  (* 0x15900 mv t4, a5 *)
      sn TF_15904 TD_15904.  (* 0x15904 j 0x1591c <static_init_tls+0x88> *)
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { sv F_157e8 D_157e8 (Z_to_bv 64 (bv_unsigned sp0 - 480)).  (* 0x15894 addi sp, sp, -0x40 *)
      stw TF_15898 TD_15898 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 87684) ltac:(ok_win HJ).  (* 0x15898 sd ra, 0x38(sp) *)
      stw TF_1589c TD_1589c (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w inp rdraw) ltac:(ok_win HJ).  (* 0x1589c sd s0, 0x30(sp) *)
      stw TF_158a0 TD_158a0 (Z_to_bv 64 (bv_unsigned sp0 - 440)) (s1v) ltac:(ok_win HJ).  (* 0x158a0 sd s1, 0x28(sp) *)
      stw TF_158a4 TD_158a4 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 327696) ltac:(ok_win HJ).  (* 0x158a4 sd s2, 0x20(sp) *)
      stw TF_158a8 TD_158a8 (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x158a8 sd s3, 0x18(sp) *)
      stw TF_158ac TD_158ac (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x158ac sd s4, 0x10(sp) *)
      stw TF_158b0 TD_158b0 (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* 0x158b0 sd s5, 0x8(sp) *)
      ld_step TF_158b4 TD_158b4 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x158b4 ld a3, 0x28(a0) *)
      sn TF_158b8 TD_158b8.  (* 0x158b8 auipc a1, 0x3a *)
      sn TF_158bc TD_158bc.  (* 0x158bc addi a1, a1, 0x4d0 *)
      sn TF_158c0 TD_158c0.  (* 0x158c0 auipc a2, 0x3a *)
      sn TF_158c4 TD_158c4.  (* 0x158c4 addi s1, a2, 0x750 *)
      stepb_ft TF_158c8 TD_158c8 ltac:(pin; cond_compute).  (* 0x158c8 beqz a3, 0x159a4 <static_init_tls+0x110> *)
      sn TF_158cc TD_158cc.  (* 0x158cc li a2, 0x0 *)
      sn TF_158d0 TD_158d0.  (* 0x158d0 li a7, 0x0 *)
      sn TF_158d4 TD_158d4.  (* 0x158d4 auipc a4, 0xa *)
      ld_step TF_158d8 TD_158d8 (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x158d8 ld a5, 0x18(a0) *)
      ld_step TF_158dc TD_158dc (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x158dc ld a0, 0x20(a0) *)
      sn TF_158e0 TD_158e0.  (* 0x158e0 li a6, 0x6 *)
      sn TF_158e4 TD_158e4.  (* 0x158e4 auipc t0, 0x9 *)
      ld_step TF_158e8 TD_158e8 (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img s2img_1fc28_4) ltac:(reflexivity).  (* 0x158e8 lwu t5, 0x354(a4) *)
      ld_step TF_158ec TD_158ec (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_1e990_8) ltac:(apply bytes_le_to_Z_8).  (* 0x158ec ld t0, 0xac(t0) *)
      sn TF_158f0 TD_158f0.  (* 0x158f0 li t1, 0x2 *)
      sn TF_158f4 TD_158f4.  (* 0x158f4 li t2, 0x7 *)
      sn TF_158f8 TD_158f8.  (* 0x158f8 lui t3, 0x6474e *)
      sn TF_158fc TD_158fc.  (* 0x158fc addiw t3, t3, 0x551 *)
      sn TF_15900 TD_15900.  (* 0x15900 mv t4, a5 *)
      sn TF_15904 TD_15904.  (* 0x15904 j 0x1591c <static_init_tls+0x88> *)
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma tls_c2 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word), wfJ sp0 Jb -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) -> getr regs 3 = Z_to_bv 64 67584 -> getr regs 5 = Z_to_bv 64 0 -> getr regs 7 = Z_to_bv 64 7 -> getr regs 9 = Z_to_bv 64 327696 -> getr regs 10 = Z_to_bv 64 56 -> getr regs 11 = Z_to_bv 64 327048 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 10 -> getr regs 15 = Z_to_bv 64 65600 -> getr regs 16 = Z_to_bv 64 6 -> getr regs 17 = Z_to_bv 64 0 -> getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 0 -> getr regs 25 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 0 -> getr regs 27 = Z_to_bv 64 0 -> getr regs 28 = Z_to_bv 64 1685382481 -> getr regs 29 = Z_to_bv 64 65600 -> getr regs 30 = Z_to_bv 64 131072 -> (forall regs', getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) -> getr regs' 3 = (Z_to_bv 64 67584) -> getr regs' 5 = (Z_to_bv 64 0) -> getr regs' 7 = (Z_to_bv 64 7) -> getr regs' 9 = (Z_to_bv 64 327696) -> getr regs' 10 = (Z_to_bv 64 56) -> getr regs' 11 = (Z_to_bv 64 327048) -> getr regs' 12 = (Z_to_bv 64 0) -> getr regs' 13 = (Z_to_bv 64 5) -> getr regs' 16 = (Z_to_bv 64 6) -> getr regs' 17 = (Z_to_bv 64 0) -> getr regs' 22 = (Z_to_bv 64 0) -> getr regs' 23 = (Z_to_bv 64 0) -> getr regs' 24 = (Z_to_bv 64 0) -> getr regs' 25 = (Z_to_bv 64 0) -> getr regs' 26 = (Z_to_bv 64 0) -> getr regs' 27 = (Z_to_bv 64 0) -> getr regs' 28 = (Z_to_bv 64 1685382481) -> getr regs' 29 = (Z_to_bv 64 65880) -> getr regs' 30 = (Z_to_bv 64 131072) -> regs_agree (fun r => In r [8; 12; 13; 17; 29; 31]%list) regs regs' -> G (mkst regs' (0x1591c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87684))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327696))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom)) -> G (mkst regs (0x1591c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87684))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327696))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H12 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { ld_step TF_1591c TD_1591c (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img s2img_10040_4) ltac:(reflexivity).  (* 0x1591c lw s0, 0x0(t4) *)
      stepb_tk TF_15920 TD_15920 ltac:(pin; cond_compute).  (* 0x15920 beq s0, a6, 0x15908 <static_init_tls+0x74> *)
      ld_step TF_15908 TD_15908 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img s2img_10050_8) ltac:(apply bytes_le_to_Z_8).  (* 0x15908 ld a2, 0x10(t4) *)
      sn TF_1590c TD_1590c.  (* 0x1590c sub a2, a5, a2 *)
      sn TF_15910 TD_15910.  (* 0x15910 addi a3, a3, -0x1 *)
      sn TF_15914 TD_15914.  (* 0x15914 add t4, t4, a0 *)
      stepb_ft TF_15918 TD_15918 ltac:(pin; cond_compute).  (* 0x15918 beqz a3, 0x1596c <static_init_tls+0xd8> *)
      ld_step TF_1591c TD_1591c (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_10078_4) ltac:(reflexivity).  (* 0x1591c lw s0, 0x0(t4) *)
      stepb_ft TF_15920 TD_15920 ltac:(pin; cond_compute).  (* 0x15920 beq s0, a6, 0x15908 <static_init_tls+0x74> *)
      stepb_tk TF_15924 TD_15924 ltac:(pin; cond_compute).  (* 0x15924 beqz t0, 0x15938 <static_init_tls+0xa4> *)
      sn TF_15938 TD_15938.  (* 0x15938 mv t6, t4 *)
      stepb_ft TF_1593c TD_1593c ltac:(pin; cond_compute).  (* 0x1593c beq s0, t2, 0x15944 <static_init_tls+0xb0> *)
      sn TF_15940 TD_15940.  (* 0x15940 mv t6, a7 *)
      stepb_tk TF_15944 TD_15944 ltac:(pin; cond_compute).  (* 0x15944 bne s0, t3, 0x15964 <static_init_tls+0xd0> *)
      sn TF_15964 TD_15964.  (* 0x15964 mv a7, t6 *)
      sn TF_15968 TD_15968.  (* 0x15968 j 0x15910 <static_init_tls+0x7c> *)
      sn TF_15910 TD_15910.  (* 0x15910 addi a3, a3, -0x1 *)
      sn TF_15914 TD_15914.  (* 0x15914 add t4, t4, a0 *)
      stepb_ft TF_15918 TD_15918 ltac:(pin; cond_compute).  (* 0x15918 beqz a3, 0x1596c <static_init_tls+0xd8> *)
      ld_step TF_1591c TD_1591c (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_100b0_4) ltac:(reflexivity).  (* 0x1591c lw s0, 0x0(t4) *)
      stepb_ft TF_15920 TD_15920 ltac:(pin; cond_compute).  (* 0x15920 beq s0, a6, 0x15908 <static_init_tls+0x74> *)
      stepb_tk TF_15924 TD_15924 ltac:(pin; cond_compute).  (* 0x15924 beqz t0, 0x15938 <static_init_tls+0xa4> *)
      sn TF_15938 TD_15938.  (* 0x15938 mv t6, t4 *)
      stepb_ft TF_1593c TD_1593c ltac:(pin; cond_compute).  (* 0x1593c beq s0, t2, 0x15944 <static_init_tls+0xb0> *)
      sn TF_15940 TD_15940.  (* 0x15940 mv t6, a7 *)
      stepb_tk TF_15944 TD_15944 ltac:(pin; cond_compute).  (* 0x15944 bne s0, t3, 0x15964 <static_init_tls+0xd0> *)
      sn TF_15964 TD_15964.  (* 0x15964 mv a7, t6 *)
      sn TF_15968 TD_15968.  (* 0x15968 j 0x15910 <static_init_tls+0x7c> *)
      sn TF_15910 TD_15910.  (* 0x15910 addi a3, a3, -0x1 *)
      sn TF_15914 TD_15914.  (* 0x15914 add t4, t4, a0 *)
      stepb_ft TF_15918 TD_15918 ltac:(pin; cond_compute).  (* 0x15918 beqz a3, 0x1596c <static_init_tls+0xd8> *)
      ld_step TF_1591c TD_1591c (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_100e8_4) ltac:(reflexivity).  (* 0x1591c lw s0, 0x0(t4) *)
      stepb_ft TF_15920 TD_15920 ltac:(pin; cond_compute).  (* 0x15920 beq s0, a6, 0x15908 <static_init_tls+0x74> *)
      stepb_tk TF_15924 TD_15924 ltac:(pin; cond_compute).  (* 0x15924 beqz t0, 0x15938 <static_init_tls+0xa4> *)
      sn TF_15938 TD_15938.  (* 0x15938 mv t6, t4 *)
      stepb_ft TF_1593c TD_1593c ltac:(pin; cond_compute).  (* 0x1593c beq s0, t2, 0x15944 <static_init_tls+0xb0> *)
      sn TF_15940 TD_15940.  (* 0x15940 mv t6, a7 *)
      stepb_tk TF_15944 TD_15944 ltac:(pin; cond_compute).  (* 0x15944 bne s0, t3, 0x15964 <static_init_tls+0xd0> *)
      sn TF_15964 TD_15964.  (* 0x15964 mv a7, t6 *)
      sn TF_15968 TD_15968.  (* 0x15968 j 0x15910 <static_init_tls+0x7c> *)
      sn TF_15910 TD_15910.  (* 0x15910 addi a3, a3, -0x1 *)
      sn TF_15914 TD_15914.  (* 0x15914 add t4, t4, a0 *)
      stepb_ft TF_15918 TD_15918 ltac:(pin; cond_compute).  (* 0x15918 beqz a3, 0x1596c <static_init_tls+0xd8> *)
      ld_step TF_1591c TD_1591c (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_10120_4) ltac:(reflexivity).  (* 0x1591c lw s0, 0x0(t4) *)
      stepb_ft TF_15920 TD_15920 ltac:(pin; cond_compute).  (* 0x15920 beq s0, a6, 0x15908 <static_init_tls+0x74> *)
      stepb_tk TF_15924 TD_15924 ltac:(pin; cond_compute).  (* 0x15924 beqz t0, 0x15938 <static_init_tls+0xa4> *)
      sn TF_15938 TD_15938.  (* 0x15938 mv t6, t4 *)
      stepb_ft TF_1593c TD_1593c ltac:(pin; cond_compute).  (* 0x1593c beq s0, t2, 0x15944 <static_init_tls+0xb0> *)
      sn TF_15940 TD_15940.  (* 0x15940 mv t6, a7 *)
      stepb_tk TF_15944 TD_15944 ltac:(pin; cond_compute).  (* 0x15944 bne s0, t3, 0x15964 <static_init_tls+0xd0> *)
      sn TF_15964 TD_15964.  (* 0x15964 mv a7, t6 *)
      sn TF_15968 TD_15968.  (* 0x15968 j 0x15910 <static_init_tls+0x7c> *)
      sn TF_15910 TD_15910.  (* 0x15910 addi a3, a3, -0x1 *)
      sn TF_15914 TD_15914.  (* 0x15914 add t4, t4, a0 *)
      stepb_ft TF_15918 TD_15918 ltac:(pin; cond_compute).  (* 0x15918 beqz a3, 0x1596c <static_init_tls+0xd8> *)
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { ld_step TF_1591c TD_1591c (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img s2img_10040_4) ltac:(reflexivity).  (* 0x1591c lw s0, 0x0(t4) *)
      stepb_tk TF_15920 TD_15920 ltac:(pin; cond_compute).  (* 0x15920 beq s0, a6, 0x15908 <static_init_tls+0x74> *)
      ld_step TF_15908 TD_15908 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img s2img_10050_8) ltac:(apply bytes_le_to_Z_8).  (* 0x15908 ld a2, 0x10(t4) *)
      sn TF_1590c TD_1590c.  (* 0x1590c sub a2, a5, a2 *)
      sn TF_15910 TD_15910.  (* 0x15910 addi a3, a3, -0x1 *)
      sn TF_15914 TD_15914.  (* 0x15914 add t4, t4, a0 *)
      stepb_ft TF_15918 TD_15918 ltac:(pin; cond_compute).  (* 0x15918 beqz a3, 0x1596c <static_init_tls+0xd8> *)
      ld_step TF_1591c TD_1591c (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_10078_4) ltac:(reflexivity).  (* 0x1591c lw s0, 0x0(t4) *)
      stepb_ft TF_15920 TD_15920 ltac:(pin; cond_compute).  (* 0x15920 beq s0, a6, 0x15908 <static_init_tls+0x74> *)
      stepb_tk TF_15924 TD_15924 ltac:(pin; cond_compute).  (* 0x15924 beqz t0, 0x15938 <static_init_tls+0xa4> *)
      sn TF_15938 TD_15938.  (* 0x15938 mv t6, t4 *)
      stepb_ft TF_1593c TD_1593c ltac:(pin; cond_compute).  (* 0x1593c beq s0, t2, 0x15944 <static_init_tls+0xb0> *)
      sn TF_15940 TD_15940.  (* 0x15940 mv t6, a7 *)
      stepb_tk TF_15944 TD_15944 ltac:(pin; cond_compute).  (* 0x15944 bne s0, t3, 0x15964 <static_init_tls+0xd0> *)
      sn TF_15964 TD_15964.  (* 0x15964 mv a7, t6 *)
      sn TF_15968 TD_15968.  (* 0x15968 j 0x15910 <static_init_tls+0x7c> *)
      sn TF_15910 TD_15910.  (* 0x15910 addi a3, a3, -0x1 *)
      sn TF_15914 TD_15914.  (* 0x15914 add t4, t4, a0 *)
      stepb_ft TF_15918 TD_15918 ltac:(pin; cond_compute).  (* 0x15918 beqz a3, 0x1596c <static_init_tls+0xd8> *)
      ld_step TF_1591c TD_1591c (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_100b0_4) ltac:(reflexivity).  (* 0x1591c lw s0, 0x0(t4) *)
      stepb_ft TF_15920 TD_15920 ltac:(pin; cond_compute).  (* 0x15920 beq s0, a6, 0x15908 <static_init_tls+0x74> *)
      stepb_tk TF_15924 TD_15924 ltac:(pin; cond_compute).  (* 0x15924 beqz t0, 0x15938 <static_init_tls+0xa4> *)
      sn TF_15938 TD_15938.  (* 0x15938 mv t6, t4 *)
      stepb_ft TF_1593c TD_1593c ltac:(pin; cond_compute).  (* 0x1593c beq s0, t2, 0x15944 <static_init_tls+0xb0> *)
      sn TF_15940 TD_15940.  (* 0x15940 mv t6, a7 *)
      stepb_tk TF_15944 TD_15944 ltac:(pin; cond_compute).  (* 0x15944 bne s0, t3, 0x15964 <static_init_tls+0xd0> *)
      sn TF_15964 TD_15964.  (* 0x15964 mv a7, t6 *)
      sn TF_15968 TD_15968.  (* 0x15968 j 0x15910 <static_init_tls+0x7c> *)
      sn TF_15910 TD_15910.  (* 0x15910 addi a3, a3, -0x1 *)
      sn TF_15914 TD_15914.  (* 0x15914 add t4, t4, a0 *)
      stepb_ft TF_15918 TD_15918 ltac:(pin; cond_compute).  (* 0x15918 beqz a3, 0x1596c <static_init_tls+0xd8> *)
      ld_step TF_1591c TD_1591c (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_100e8_4) ltac:(reflexivity).  (* 0x1591c lw s0, 0x0(t4) *)
      stepb_ft TF_15920 TD_15920 ltac:(pin; cond_compute).  (* 0x15920 beq s0, a6, 0x15908 <static_init_tls+0x74> *)
      stepb_tk TF_15924 TD_15924 ltac:(pin; cond_compute).  (* 0x15924 beqz t0, 0x15938 <static_init_tls+0xa4> *)
      sn TF_15938 TD_15938.  (* 0x15938 mv t6, t4 *)
      stepb_ft TF_1593c TD_1593c ltac:(pin; cond_compute).  (* 0x1593c beq s0, t2, 0x15944 <static_init_tls+0xb0> *)
      sn TF_15940 TD_15940.  (* 0x15940 mv t6, a7 *)
      stepb_tk TF_15944 TD_15944 ltac:(pin; cond_compute).  (* 0x15944 bne s0, t3, 0x15964 <static_init_tls+0xd0> *)
      sn TF_15964 TD_15964.  (* 0x15964 mv a7, t6 *)
      sn TF_15968 TD_15968.  (* 0x15968 j 0x15910 <static_init_tls+0x7c> *)
      sn TF_15910 TD_15910.  (* 0x15910 addi a3, a3, -0x1 *)
      sn TF_15914 TD_15914.  (* 0x15914 add t4, t4, a0 *)
      stepb_ft TF_15918 TD_15918 ltac:(pin; cond_compute).  (* 0x15918 beqz a3, 0x1596c <static_init_tls+0xd8> *)
      ld_step TF_1591c TD_1591c (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img s2img_10120_4) ltac:(reflexivity).  (* 0x1591c lw s0, 0x0(t4) *)
      stepb_ft TF_15920 TD_15920 ltac:(pin; cond_compute).  (* 0x15920 beq s0, a6, 0x15908 <static_init_tls+0x74> *)
      stepb_tk TF_15924 TD_15924 ltac:(pin; cond_compute).  (* 0x15924 beqz t0, 0x15938 <static_init_tls+0xa4> *)
      sn TF_15938 TD_15938.  (* 0x15938 mv t6, t4 *)
      stepb_ft TF_1593c TD_1593c ltac:(pin; cond_compute).  (* 0x1593c beq s0, t2, 0x15944 <static_init_tls+0xb0> *)
      sn TF_15940 TD_15940.  (* 0x15940 mv t6, a7 *)
      stepb_tk TF_15944 TD_15944 ltac:(pin; cond_compute).  (* 0x15944 bne s0, t3, 0x15964 <static_init_tls+0xd0> *)
      sn TF_15964 TD_15964.  (* 0x15964 mv a7, t6 *)
      sn TF_15968 TD_15968.  (* 0x15968 j 0x15910 <static_init_tls+0x7c> *)
      sn TF_15910 TD_15910.  (* 0x15910 addi a3, a3, -0x1 *)
      sn TF_15914 TD_15914.  (* 0x15914 add t4, t4, a0 *)
      stepb_ft TF_15918 TD_15918 ltac:(pin; cond_compute).  (* 0x15918 beqz a3, 0x1596c <static_init_tls+0xd8> *)
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma tls_c3 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word), wfJ sp0 Jb -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) -> getr regs 3 = Z_to_bv 64 67584 -> getr regs 5 = Z_to_bv 64 0 -> getr regs 7 = Z_to_bv 64 7 -> getr regs 9 = Z_to_bv 64 327696 -> getr regs 10 = Z_to_bv 64 56 -> getr regs 11 = Z_to_bv 64 327048 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 5 -> getr regs 16 = Z_to_bv 64 6 -> getr regs 17 = Z_to_bv 64 0 -> getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 0 -> getr regs 25 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 0 -> getr regs 27 = Z_to_bv 64 0 -> getr regs 28 = Z_to_bv 64 1685382481 -> getr regs 29 = Z_to_bv 64 65880 -> getr regs 30 = Z_to_bv 64 131072 -> (forall regs', getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) -> getr regs' 3 = (Z_to_bv 64 67584) -> getr regs' 9 = (Z_to_bv 64 327696) -> getr regs' 11 = (Z_to_bv 64 327048) -> getr regs' 12 = (Z_to_bv 64 0) -> getr regs' 17 = (Z_to_bv 64 0) -> getr regs' 22 = (Z_to_bv 64 0) -> getr regs' 23 = (Z_to_bv 64 0) -> getr regs' 24 = (Z_to_bv 64 0) -> getr regs' 25 = (Z_to_bv 64 0) -> getr regs' 26 = (Z_to_bv 64 0) -> getr regs' 27 = (Z_to_bv 64 0) -> regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' -> G (mkst regs' (0x1596c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87684))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327696))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom)) -> G (mkst regs (0x1591c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87684))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327696))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H12 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { ld_step TF_1591c TD_1591c (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img s2img_10158_4) ltac:(reflexivity).  (* 0x1591c lw s0, 0x0(t4) *)
      stepb_ft TF_15920 TD_15920 ltac:(pin; cond_compute).  (* 0x15920 beq s0, a6, 0x15908 <static_init_tls+0x74> *)
      stepb_tk TF_15924 TD_15924 ltac:(pin; cond_compute).  (* 0x15924 beqz t0, 0x15938 <static_init_tls+0xa4> *)
      sn TF_15938 TD_15938.  (* 0x15938 mv t6, t4 *)
      stepb_ft TF_1593c TD_1593c ltac:(pin; cond_compute).  (* 0x1593c beq s0, t2, 0x15944 <static_init_tls+0xb0> *)
      sn TF_15940 TD_15940.  (* 0x15940 mv t6, a7 *)
      stepb_tk TF_15944 TD_15944 ltac:(pin; cond_compute).  (* 0x15944 bne s0, t3, 0x15964 <static_init_tls+0xd0> *)
      sn TF_15964 TD_15964.  (* 0x15964 mv a7, t6 *)
      sn TF_15968 TD_15968.  (* 0x15968 j 0x15910 <static_init_tls+0x7c> *)
      sn TF_15910 TD_15910.  (* 0x15910 addi a3, a3, -0x1 *)
      sn TF_15914 TD_15914.  (* 0x15914 add t4, t4, a0 *)
      stepb_ft TF_15918 TD_15918 ltac:(pin; cond_compute).  (* 0x15918 beqz a3, 0x1596c <static_init_tls+0xd8> *)
      ld_step TF_1591c TD_1591c (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img s2img_10190_4) ltac:(reflexivity).  (* 0x1591c lw s0, 0x0(t4) *)
      stepb_ft TF_15920 TD_15920 ltac:(pin; cond_compute).  (* 0x15920 beq s0, a6, 0x15908 <static_init_tls+0x74> *)
      stepb_tk TF_15924 TD_15924 ltac:(pin; cond_compute).  (* 0x15924 beqz t0, 0x15938 <static_init_tls+0xa4> *)
      sn TF_15938 TD_15938.  (* 0x15938 mv t6, t4 *)
      stepb_ft TF_1593c TD_1593c ltac:(pin; cond_compute).  (* 0x1593c beq s0, t2, 0x15944 <static_init_tls+0xb0> *)
      sn TF_15940 TD_15940.  (* 0x15940 mv t6, a7 *)
      stepb_tk TF_15944 TD_15944 ltac:(pin; cond_compute).  (* 0x15944 bne s0, t3, 0x15964 <static_init_tls+0xd0> *)
      sn TF_15964 TD_15964.  (* 0x15964 mv a7, t6 *)
      sn TF_15968 TD_15968.  (* 0x15968 j 0x15910 <static_init_tls+0x7c> *)
      sn TF_15910 TD_15910.  (* 0x15910 addi a3, a3, -0x1 *)
      sn TF_15914 TD_15914.  (* 0x15914 add t4, t4, a0 *)
      stepb_ft TF_15918 TD_15918 ltac:(pin; cond_compute).  (* 0x15918 beqz a3, 0x1596c <static_init_tls+0xd8> *)
      ld_step TF_1591c TD_1591c (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img s2img_101c8_4) ltac:(reflexivity).  (* 0x1591c lw s0, 0x0(t4) *)
      stepb_ft TF_15920 TD_15920 ltac:(pin; cond_compute).  (* 0x15920 beq s0, a6, 0x15908 <static_init_tls+0x74> *)
      stepb_tk TF_15924 TD_15924 ltac:(pin; cond_compute).  (* 0x15924 beqz t0, 0x15938 <static_init_tls+0xa4> *)
      sn TF_15938 TD_15938.  (* 0x15938 mv t6, t4 *)
      stepb_ft TF_1593c TD_1593c ltac:(pin; cond_compute).  (* 0x1593c beq s0, t2, 0x15944 <static_init_tls+0xb0> *)
      sn TF_15940 TD_15940.  (* 0x15940 mv t6, a7 *)
      stepb_ft TF_15944 TD_15944 ltac:(pin; cond_compute).  (* 0x15944 bne s0, t3, 0x15964 <static_init_tls+0xd0> *)
      ld_step TF_15948 TD_15948 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_101f0_8) ltac:(apply bytes_le_to_Z_8).  (* 0x15948 ld a7, 0x28(t4) *)
      stepb_tk TF_1594c TD_1594c ltac:(pin; cond_compute).  (* 0x1594c bgeu t5, a7, 0x15964 <static_init_tls+0xd0> *)
      sn TF_15964 TD_15964.  (* 0x15964 mv a7, t6 *)
      sn TF_15968 TD_15968.  (* 0x15968 j 0x15910 <static_init_tls+0x7c> *)
      sn TF_15910 TD_15910.  (* 0x15910 addi a3, a3, -0x1 *)
      sn TF_15914 TD_15914.  (* 0x15914 add t4, t4, a0 *)
      stepb_ft TF_15918 TD_15918 ltac:(pin; cond_compute).  (* 0x15918 beqz a3, 0x1596c <static_init_tls+0xd8> *)
      ld_step TF_1591c TD_1591c (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img s2img_10200_4) ltac:(reflexivity).  (* 0x1591c lw s0, 0x0(t4) *)
      stepb_ft TF_15920 TD_15920 ltac:(pin; cond_compute).  (* 0x15920 beq s0, a6, 0x15908 <static_init_tls+0x74> *)
      stepb_tk TF_15924 TD_15924 ltac:(pin; cond_compute).  (* 0x15924 beqz t0, 0x15938 <static_init_tls+0xa4> *)
      sn TF_15938 TD_15938.  (* 0x15938 mv t6, t4 *)
      stepb_ft TF_1593c TD_1593c ltac:(pin; cond_compute).  (* 0x1593c beq s0, t2, 0x15944 <static_init_tls+0xb0> *)
      sn TF_15940 TD_15940.  (* 0x15940 mv t6, a7 *)
      stepb_tk TF_15944 TD_15944 ltac:(pin; cond_compute).  (* 0x15944 bne s0, t3, 0x15964 <static_init_tls+0xd0> *)
      sn TF_15964 TD_15964.  (* 0x15964 mv a7, t6 *)
      sn TF_15968 TD_15968.  (* 0x15968 j 0x15910 <static_init_tls+0x7c> *)
      sn TF_15910 TD_15910.  (* 0x15910 addi a3, a3, -0x1 *)
      sn TF_15914 TD_15914.  (* 0x15914 add t4, t4, a0 *)
      stepb_ft TF_15918 TD_15918 ltac:(pin; cond_compute).  (* 0x15918 beqz a3, 0x1596c <static_init_tls+0xd8> *)
      ld_step TF_1591c TD_1591c (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img s2img_10238_4) ltac:(reflexivity).  (* 0x1591c lw s0, 0x0(t4) *)
      stepb_ft TF_15920 TD_15920 ltac:(pin; cond_compute).  (* 0x15920 beq s0, a6, 0x15908 <static_init_tls+0x74> *)
      stepb_tk TF_15924 TD_15924 ltac:(pin; cond_compute).  (* 0x15924 beqz t0, 0x15938 <static_init_tls+0xa4> *)
      sn TF_15938 TD_15938.  (* 0x15938 mv t6, t4 *)
      stepb_ft TF_1593c TD_1593c ltac:(pin; cond_compute).  (* 0x1593c beq s0, t2, 0x15944 <static_init_tls+0xb0> *)
      sn TF_15940 TD_15940.  (* 0x15940 mv t6, a7 *)
      stepb_tk TF_15944 TD_15944 ltac:(pin; cond_compute).  (* 0x15944 bne s0, t3, 0x15964 <static_init_tls+0xd0> *)
      sn TF_15964 TD_15964.  (* 0x15964 mv a7, t6 *)
      sn TF_15968 TD_15968.  (* 0x15968 j 0x15910 <static_init_tls+0x7c> *)
      sn TF_15910 TD_15910.  (* 0x15910 addi a3, a3, -0x1 *)
      sn TF_15914 TD_15914.  (* 0x15914 add t4, t4, a0 *)
      stepb_tk TF_15918 TD_15918 ltac:(pin; cond_compute).  (* 0x15918 beqz a3, 0x1596c <static_init_tls+0xd8> *)
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { ld_step TF_1591c TD_1591c (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img s2img_10158_4) ltac:(reflexivity).  (* 0x1591c lw s0, 0x0(t4) *)
      stepb_ft TF_15920 TD_15920 ltac:(pin; cond_compute).  (* 0x15920 beq s0, a6, 0x15908 <static_init_tls+0x74> *)
      stepb_tk TF_15924 TD_15924 ltac:(pin; cond_compute).  (* 0x15924 beqz t0, 0x15938 <static_init_tls+0xa4> *)
      sn TF_15938 TD_15938.  (* 0x15938 mv t6, t4 *)
      stepb_ft TF_1593c TD_1593c ltac:(pin; cond_compute).  (* 0x1593c beq s0, t2, 0x15944 <static_init_tls+0xb0> *)
      sn TF_15940 TD_15940.  (* 0x15940 mv t6, a7 *)
      stepb_tk TF_15944 TD_15944 ltac:(pin; cond_compute).  (* 0x15944 bne s0, t3, 0x15964 <static_init_tls+0xd0> *)
      sn TF_15964 TD_15964.  (* 0x15964 mv a7, t6 *)
      sn TF_15968 TD_15968.  (* 0x15968 j 0x15910 <static_init_tls+0x7c> *)
      sn TF_15910 TD_15910.  (* 0x15910 addi a3, a3, -0x1 *)
      sn TF_15914 TD_15914.  (* 0x15914 add t4, t4, a0 *)
      stepb_ft TF_15918 TD_15918 ltac:(pin; cond_compute).  (* 0x15918 beqz a3, 0x1596c <static_init_tls+0xd8> *)
      ld_step TF_1591c TD_1591c (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img s2img_10190_4) ltac:(reflexivity).  (* 0x1591c lw s0, 0x0(t4) *)
      stepb_ft TF_15920 TD_15920 ltac:(pin; cond_compute).  (* 0x15920 beq s0, a6, 0x15908 <static_init_tls+0x74> *)
      stepb_tk TF_15924 TD_15924 ltac:(pin; cond_compute).  (* 0x15924 beqz t0, 0x15938 <static_init_tls+0xa4> *)
      sn TF_15938 TD_15938.  (* 0x15938 mv t6, t4 *)
      stepb_ft TF_1593c TD_1593c ltac:(pin; cond_compute).  (* 0x1593c beq s0, t2, 0x15944 <static_init_tls+0xb0> *)
      sn TF_15940 TD_15940.  (* 0x15940 mv t6, a7 *)
      stepb_tk TF_15944 TD_15944 ltac:(pin; cond_compute).  (* 0x15944 bne s0, t3, 0x15964 <static_init_tls+0xd0> *)
      sn TF_15964 TD_15964.  (* 0x15964 mv a7, t6 *)
      sn TF_15968 TD_15968.  (* 0x15968 j 0x15910 <static_init_tls+0x7c> *)
      sn TF_15910 TD_15910.  (* 0x15910 addi a3, a3, -0x1 *)
      sn TF_15914 TD_15914.  (* 0x15914 add t4, t4, a0 *)
      stepb_ft TF_15918 TD_15918 ltac:(pin; cond_compute).  (* 0x15918 beqz a3, 0x1596c <static_init_tls+0xd8> *)
      ld_step TF_1591c TD_1591c (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img s2img_101c8_4) ltac:(reflexivity).  (* 0x1591c lw s0, 0x0(t4) *)
      stepb_ft TF_15920 TD_15920 ltac:(pin; cond_compute).  (* 0x15920 beq s0, a6, 0x15908 <static_init_tls+0x74> *)
      stepb_tk TF_15924 TD_15924 ltac:(pin; cond_compute).  (* 0x15924 beqz t0, 0x15938 <static_init_tls+0xa4> *)
      sn TF_15938 TD_15938.  (* 0x15938 mv t6, t4 *)
      stepb_ft TF_1593c TD_1593c ltac:(pin; cond_compute).  (* 0x1593c beq s0, t2, 0x15944 <static_init_tls+0xb0> *)
      sn TF_15940 TD_15940.  (* 0x15940 mv t6, a7 *)
      stepb_ft TF_15944 TD_15944 ltac:(pin; cond_compute).  (* 0x15944 bne s0, t3, 0x15964 <static_init_tls+0xd0> *)
      ld_step TF_15948 TD_15948 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_101f0_8) ltac:(apply bytes_le_to_Z_8).  (* 0x15948 ld a7, 0x28(t4) *)
      stepb_tk TF_1594c TD_1594c ltac:(pin; cond_compute).  (* 0x1594c bgeu t5, a7, 0x15964 <static_init_tls+0xd0> *)
      sn TF_15964 TD_15964.  (* 0x15964 mv a7, t6 *)
      sn TF_15968 TD_15968.  (* 0x15968 j 0x15910 <static_init_tls+0x7c> *)
      sn TF_15910 TD_15910.  (* 0x15910 addi a3, a3, -0x1 *)
      sn TF_15914 TD_15914.  (* 0x15914 add t4, t4, a0 *)
      stepb_ft TF_15918 TD_15918 ltac:(pin; cond_compute).  (* 0x15918 beqz a3, 0x1596c <static_init_tls+0xd8> *)
      ld_step TF_1591c TD_1591c (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img s2img_10200_4) ltac:(reflexivity).  (* 0x1591c lw s0, 0x0(t4) *)
      stepb_ft TF_15920 TD_15920 ltac:(pin; cond_compute).  (* 0x15920 beq s0, a6, 0x15908 <static_init_tls+0x74> *)
      stepb_tk TF_15924 TD_15924 ltac:(pin; cond_compute).  (* 0x15924 beqz t0, 0x15938 <static_init_tls+0xa4> *)
      sn TF_15938 TD_15938.  (* 0x15938 mv t6, t4 *)
      stepb_ft TF_1593c TD_1593c ltac:(pin; cond_compute).  (* 0x1593c beq s0, t2, 0x15944 <static_init_tls+0xb0> *)
      sn TF_15940 TD_15940.  (* 0x15940 mv t6, a7 *)
      stepb_tk TF_15944 TD_15944 ltac:(pin; cond_compute).  (* 0x15944 bne s0, t3, 0x15964 <static_init_tls+0xd0> *)
      sn TF_15964 TD_15964.  (* 0x15964 mv a7, t6 *)
      sn TF_15968 TD_15968.  (* 0x15968 j 0x15910 <static_init_tls+0x7c> *)
      sn TF_15910 TD_15910.  (* 0x15910 addi a3, a3, -0x1 *)
      sn TF_15914 TD_15914.  (* 0x15914 add t4, t4, a0 *)
      stepb_ft TF_15918 TD_15918 ltac:(pin; cond_compute).  (* 0x15918 beqz a3, 0x1596c <static_init_tls+0xd8> *)
      ld_step TF_1591c TD_1591c (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img s2img_10238_4) ltac:(reflexivity).  (* 0x1591c lw s0, 0x0(t4) *)
      stepb_ft TF_15920 TD_15920 ltac:(pin; cond_compute).  (* 0x15920 beq s0, a6, 0x15908 <static_init_tls+0x74> *)
      stepb_tk TF_15924 TD_15924 ltac:(pin; cond_compute).  (* 0x15924 beqz t0, 0x15938 <static_init_tls+0xa4> *)
      sn TF_15938 TD_15938.  (* 0x15938 mv t6, t4 *)
      stepb_ft TF_1593c TD_1593c ltac:(pin; cond_compute).  (* 0x1593c beq s0, t2, 0x15944 <static_init_tls+0xb0> *)
      sn TF_15940 TD_15940.  (* 0x15940 mv t6, a7 *)
      stepb_tk TF_15944 TD_15944 ltac:(pin; cond_compute).  (* 0x15944 bne s0, t3, 0x15964 <static_init_tls+0xd0> *)
      sn TF_15964 TD_15964.  (* 0x15964 mv a7, t6 *)
      sn TF_15968 TD_15968.  (* 0x15968 j 0x15910 <static_init_tls+0x7c> *)
      sn TF_15910 TD_15910.  (* 0x15910 addi a3, a3, -0x1 *)
      sn TF_15914 TD_15914.  (* 0x15914 add t4, t4, a0 *)
      stepb_tk TF_15918 TD_15918 ltac:(pin; cond_compute).  (* 0x15918 beqz a3, 0x1596c <static_init_tls+0xd8> *)
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma tls_c4 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word), wfJ sp0 Jb -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) -> getr regs 3 = Z_to_bv 64 67584 -> getr regs 9 = Z_to_bv 64 327696 -> getr regs 11 = Z_to_bv 64 327048 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 17 = Z_to_bv 64 0 -> getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 0 -> getr regs 25 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 0 -> getr regs 27 = Z_to_bv 64 0 -> (forall regs', getr regs' 1 = (Z_to_bv 64 88776) -> getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) -> getr regs' 3 = (Z_to_bv 64 67584) -> getr regs' 4 = (Z_to_bv 64 195968) -> getr regs' 8 = (Z_to_bv 64 195968) -> getr regs' 10 = (Z_to_bv 64 327048) -> getr regs' 11 = (Z_to_bv 64 327752) -> getr regs' 12 = (Z_to_bv 64 0) -> getr regs' 13 = (Z_to_bv 64 195760) -> getr regs' 14 = (Z_to_bv 64 0) -> getr regs' 15 = (Z_to_bv 64 18446744073709355648) -> getr regs' 17 = (Z_to_bv 64 96) -> getr regs' 18 = (Z_to_bv 64 195768) -> getr regs' 19 = (Z_to_bv 64 0) -> getr regs' 20 = (Z_to_bv 64 195984) -> getr regs' 22 = (Z_to_bv 64 0) -> getr regs' 23 = (Z_to_bv 64 0) -> getr regs' 24 = (Z_to_bv 64 0) -> getr regs' 25 = (Z_to_bv 64 0) -> getr regs' 26 = (Z_to_bv 64 0) -> getr regs' 27 = (Z_to_bv 64 0) -> regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' -> G (mkst regs' (0x15af0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87684))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327696))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 327080) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327096) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 327720) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 327728) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 195984) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 195960) (word_to_le_bytes 8 (Z_to_bv 64 195984))) (Z_to_bv 64 195768) (word_to_le_bytes 8 (Z_to_bv 64 195768))) (Z_to_bv 64 327696) ([Z_to_bv 8 1])) (Z_to_bv 64 195808) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) -> G (mkst regs (0x1596c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87684))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327696))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 inp rdraw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H12 H17 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { stepb_tk TF_1596c TD_1596c ltac:(pin; cond_compute).  (* 0x1596c beqz a7, 0x159a4 <static_init_tls+0x110> *)
      ld_step TF_159a4 TD_159a4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_4fd98_8) ltac:(apply bytes_le_to_Z_8).  (* 0x159a4 ld a2, 0x10(a1) *)
      ld_step TF_159a8 TD_159a8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_4fda8_8) ltac:(apply bytes_le_to_Z_8).  (* 0x159a8 ld a3, 0x20(a1) *)
      ld_step TF_159ac TD_159ac (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_4fdb0_8) ltac:(apply bytes_le_to_Z_8).  (* 0x159ac ld a0, 0x28(a1) *)
      sn TF_159b0 TD_159b0.  (* 0x159b0 add a4, a3, a2 *)
      sn TF_159b4 TD_159b4.  (* 0x159b4 addi a5, a0, -0x1 *)
      sn TF_159b8 TD_159b8.  (* 0x159b8 neg a4, a4 *)
      sn TF_159bc TD_159bc.  (* 0x159bc and a2, a5, a2 *)
      sn TF_159c0 TD_159c0.  (* 0x159c0 and a4, a5, a4 *)
      sn TF_159c4 TD_159c4.  (* 0x159c4 li a5, 0x7 *)
      sn TF_159c8 TD_159c8.  (* 0x159c8 add a3, a4, a3 *)
      stw TF_159cc TD_159cc (Z_to_bv 64 327080) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x159cc sd a3, 0x20(a1) *)
      stw TF_159d0 TD_159d0 (Z_to_bv 64 327096) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x159d0 sd a2, 0x30(a1) *)
      stepb_ft TF_159d4 TD_159d4 ltac:(pin; cond_compute).  (* 0x159d4 bltu a5, a0, 0x159e0 <static_init_tls+0x14c> *)
      sn TF_159d8 TD_159d8.  (* 0x159d8 li a0, 0x8 *)
      stw TF_159dc TD_159dc (Z_to_bv 64 327088) (Z_to_bv 64 8) ltac:(ok_data).  (* 0x159dc sd a0, 0x28(a1) *)
      sn TF_159e0 TD_159e0.  (* 0x159e0 add a2, a2, a3 *)
      sn TF_159e4 TD_159e4.  (* 0x159e4 lui a1, 0x20 *)
      sn TF_159e8 TD_159e8.  (* 0x159e8 add a2, a2, a0 *)
      sn TF_159ec TD_159ec.  (* 0x159ec addiw a3, a1, 0xd1 *)
      sn TF_159f0 TD_159f0.  (* 0x159f0 addi a1, a2, 0xdf *)
      sn TF_159f4 TD_159f4.  (* 0x159f4 andi a1, a1, -0x8 *)
      stw TF_159f8 TD_159f8 (Z_to_bv 64 327720) (Z_to_bv 64 224) ltac:(ok_data).  (* 0x159f8 sd a1, 0x18(s1) *)
      stw TF_159fc TD_159fc (Z_to_bv 64 327728) (Z_to_bv 64 8) ltac:(ok_data).  (* 0x159fc sd a0, 0x20(s1) *)
      stepb_tk TF_15a00 TD_15a00 ltac:(pin; cond_compute).  (* 0x15a00 bltu a1, a3, 0x15a34 <static_init_tls+0x1a0> *)
      sn TF_15a34 TD_15a34.  (* 0x15a34 auipc a3, 0x1a *)
      ld_step TF_15a38 TD_15a38 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_50020_8) ltac:(apply bytes_le_to_Z_8).  (* 0x15a38 ld s3, 0x10(s1) *)
      ld_step TF_15a3c TD_15a3c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_50038_8) ltac:(apply bytes_le_to_Z_8).  (* 0x15a3c ld a2, 0x28(s1) *)
      sn TF_15a40 TD_15a40.  (* 0x15a40 addi a4, a0, -0x1 *)
      sn TF_15a44 TD_15a44.  (* 0x15a44 li a5, -0xc8 *)
      sn TF_15a48 TD_15a48.  (* 0x15a48 addi a0, a3, 0x284 *)
      sn TF_15a4c TD_15a4c.  (* 0x15a4c sub a5, a5, a0 *)
      sn TF_15a50 TD_15a50.  (* 0x15a50 and a4, a4, a5 *)
      sn TF_15a54 TD_15a54.  (* 0x15a54 not a3, a2 *)
      sn TF_15a58 TD_15a58.  (* 0x15a58 add s2, a0, a4 *)
      sn TF_15a5c TD_15a5c.  (* 0x15a5c slli a3, a3, 0x3 *)
      sn TF_15a60 TD_15a60.  (* 0x15a60 add a3, a0, a3 *)
      sn TF_15a64 TD_15a64.  (* 0x15a64 add s4, a3, a1 *)
      sn TF_15a68 TD_15a68.  (* 0x15a68 addi s0, s2, 0xc8 *)
      stepb_tk TF_15a6c TD_15a6c ltac:(pin; cond_compute).  (* 0x15a6c beqz s3, 0x15ab4 <static_init_tls+0x220> *)
      stw TF_15ab4 TD_15ab4 (Z_to_bv 64 195984) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x15ab4 sd a2, 0x0(s4) *)
      stw TF_15ab8 TD_15ab8 (Z_to_bv 64 195960) (Z_to_bv 64 195984) ltac:(ok_data).  (* 0x15ab8 sd s4, 0xc0(s2) *)
      stw TF_15abc TD_15abc (Z_to_bv 64 195768) (Z_to_bv 64 195768) ltac:(ok_data).  (* 0x15abc sd s2, 0x0(s2) *)
      sn TF_15ac0 TD_15ac0.  (* 0x15ac0 mv a0, s0 *)
      sn TF_15ac4 TD_15ac4.  (* 0x15ac4 jal 0x1d8b8 <__set_thread_area> *)
      sn F_1d818 D_1d818.  (* 0x1d8b8 mv tp, a0 *)
      sn F_1d81c D_1d81c.  (* 0x1d8bc li a0, 0x0 *)
      stepret F_1d820 D_1d820 (0x15ac8 : word) ltac:(pin; first [reflexivity | bveq]).  (* 0x1d8c0 ret *)
      stepb_ft TF_15ac8 TD_15ac8 ltac:(pin; cond_compute).  (* 0x15ac8 bltz a0, 0x15b1c <static_init_tls+0x288> *)
      stepb_ft TF_15acc TD_15acc ltac:(pin; cond_compute).  (* 0x15acc bnez a0, 0x15ad8 <static_init_tls+0x244> *)
      sn TF_15ad0 TD_15ad0.  (* 0x15ad0 li a0, 0x1 *)
      stw TF_15ad4 TD_15ad4 (Z_to_bv 64 327696) (Z_to_bv 64 1) ltac:(ok_data).  (* 0x15ad4 sb a0, 0x0(s1) *)
      sn TF_15ad8 TD_15ad8.  (* 0x15ad8 li a0, 0x2 *)
      sn TF_15adc TD_15adc.  (* 0x15adc auipc a1, 0x3a *)
      stw TF_15ae0 TD_15ae0 (Z_to_bv 64 195808) (Z_to_bv 64 2) ltac:(ok_data).  (* 0x15ae0 sw a0, 0x28(s2) *)
      sn TF_15ae4 TD_15ae4.  (* 0x15ae4 li a7, 0x60 *)
      sn TF_15ae8 TD_15ae8.  (* 0x15ae8 addi a0, a1, 0x2ac *)
      sn TF_15aec TD_15aec.  (* 0x15aec addi a1, s1, 0x38 *)
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { stepb_tk TF_1596c TD_1596c ltac:(pin; cond_compute).  (* 0x1596c beqz a7, 0x159a4 <static_init_tls+0x110> *)
      ld_step TF_159a4 TD_159a4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_4fd98_8) ltac:(apply bytes_le_to_Z_8).  (* 0x159a4 ld a2, 0x10(a1) *)
      ld_step TF_159a8 TD_159a8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_4fda8_8) ltac:(apply bytes_le_to_Z_8).  (* 0x159a8 ld a3, 0x20(a1) *)
      ld_step TF_159ac TD_159ac (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_4fdb0_8) ltac:(apply bytes_le_to_Z_8).  (* 0x159ac ld a0, 0x28(a1) *)
      sn TF_159b0 TD_159b0.  (* 0x159b0 add a4, a3, a2 *)
      sn TF_159b4 TD_159b4.  (* 0x159b4 addi a5, a0, -0x1 *)
      sn TF_159b8 TD_159b8.  (* 0x159b8 neg a4, a4 *)
      sn TF_159bc TD_159bc.  (* 0x159bc and a2, a5, a2 *)
      sn TF_159c0 TD_159c0.  (* 0x159c0 and a4, a5, a4 *)
      sn TF_159c4 TD_159c4.  (* 0x159c4 li a5, 0x7 *)
      sn TF_159c8 TD_159c8.  (* 0x159c8 add a3, a4, a3 *)
      stw TF_159cc TD_159cc (Z_to_bv 64 327080) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x159cc sd a3, 0x20(a1) *)
      stw TF_159d0 TD_159d0 (Z_to_bv 64 327096) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x159d0 sd a2, 0x30(a1) *)
      stepb_ft TF_159d4 TD_159d4 ltac:(pin; cond_compute).  (* 0x159d4 bltu a5, a0, 0x159e0 <static_init_tls+0x14c> *)
      sn TF_159d8 TD_159d8.  (* 0x159d8 li a0, 0x8 *)
      stw TF_159dc TD_159dc (Z_to_bv 64 327088) (Z_to_bv 64 8) ltac:(ok_data).  (* 0x159dc sd a0, 0x28(a1) *)
      sn TF_159e0 TD_159e0.  (* 0x159e0 add a2, a2, a3 *)
      sn TF_159e4 TD_159e4.  (* 0x159e4 lui a1, 0x20 *)
      sn TF_159e8 TD_159e8.  (* 0x159e8 add a2, a2, a0 *)
      sn TF_159ec TD_159ec.  (* 0x159ec addiw a3, a1, 0xd1 *)
      sn TF_159f0 TD_159f0.  (* 0x159f0 addi a1, a2, 0xdf *)
      sn TF_159f4 TD_159f4.  (* 0x159f4 andi a1, a1, -0x8 *)
      stw TF_159f8 TD_159f8 (Z_to_bv 64 327720) (Z_to_bv 64 224) ltac:(ok_data).  (* 0x159f8 sd a1, 0x18(s1) *)
      stw TF_159fc TD_159fc (Z_to_bv 64 327728) (Z_to_bv 64 8) ltac:(ok_data).  (* 0x159fc sd a0, 0x20(s1) *)
      stepb_tk TF_15a00 TD_15a00 ltac:(pin; cond_compute).  (* 0x15a00 bltu a1, a3, 0x15a34 <static_init_tls+0x1a0> *)
      sn TF_15a34 TD_15a34.  (* 0x15a34 auipc a3, 0x1a *)
      ld_step TF_15a38 TD_15a38 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_50020_8) ltac:(apply bytes_le_to_Z_8).  (* 0x15a38 ld s3, 0x10(s1) *)
      ld_step TF_15a3c TD_15a3c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_50038_8) ltac:(apply bytes_le_to_Z_8).  (* 0x15a3c ld a2, 0x28(s1) *)
      sn TF_15a40 TD_15a40.  (* 0x15a40 addi a4, a0, -0x1 *)
      sn TF_15a44 TD_15a44.  (* 0x15a44 li a5, -0xc8 *)
      sn TF_15a48 TD_15a48.  (* 0x15a48 addi a0, a3, 0x284 *)
      sn TF_15a4c TD_15a4c.  (* 0x15a4c sub a5, a5, a0 *)
      sn TF_15a50 TD_15a50.  (* 0x15a50 and a4, a4, a5 *)
      sn TF_15a54 TD_15a54.  (* 0x15a54 not a3, a2 *)
      sn TF_15a58 TD_15a58.  (* 0x15a58 add s2, a0, a4 *)
      sn TF_15a5c TD_15a5c.  (* 0x15a5c slli a3, a3, 0x3 *)
      sn TF_15a60 TD_15a60.  (* 0x15a60 add a3, a0, a3 *)
      sn TF_15a64 TD_15a64.  (* 0x15a64 add s4, a3, a1 *)
      sn TF_15a68 TD_15a68.  (* 0x15a68 addi s0, s2, 0xc8 *)
      stepb_tk TF_15a6c TD_15a6c ltac:(pin; cond_compute).  (* 0x15a6c beqz s3, 0x15ab4 <static_init_tls+0x220> *)
      stw TF_15ab4 TD_15ab4 (Z_to_bv 64 195984) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x15ab4 sd a2, 0x0(s4) *)
      stw TF_15ab8 TD_15ab8 (Z_to_bv 64 195960) (Z_to_bv 64 195984) ltac:(ok_data).  (* 0x15ab8 sd s4, 0xc0(s2) *)
      stw TF_15abc TD_15abc (Z_to_bv 64 195768) (Z_to_bv 64 195768) ltac:(ok_data).  (* 0x15abc sd s2, 0x0(s2) *)
      sn TF_15ac0 TD_15ac0.  (* 0x15ac0 mv a0, s0 *)
      sn TF_15ac4 TD_15ac4.  (* 0x15ac4 jal 0x1d8b8 <__set_thread_area> *)
      sn F_1d818 D_1d818.  (* 0x1d8b8 mv tp, a0 *)
      sn F_1d81c D_1d81c.  (* 0x1d8bc li a0, 0x0 *)
      stepret F_1d820 D_1d820 (0x15ac8 : word) ltac:(pin; first [reflexivity | bveq]).  (* 0x1d8c0 ret *)
      stepb_ft TF_15ac8 TD_15ac8 ltac:(pin; cond_compute).  (* 0x15ac8 bltz a0, 0x15b1c <static_init_tls+0x288> *)
      stepb_ft TF_15acc TD_15acc ltac:(pin; cond_compute).  (* 0x15acc bnez a0, 0x15ad8 <static_init_tls+0x244> *)
      sn TF_15ad0 TD_15ad0.  (* 0x15ad0 li a0, 0x1 *)
      stw TF_15ad4 TD_15ad4 (Z_to_bv 64 327696) (Z_to_bv 64 1) ltac:(ok_data).  (* 0x15ad4 sb a0, 0x0(s1) *)
      sn TF_15ad8 TD_15ad8.  (* 0x15ad8 li a0, 0x2 *)
      sn TF_15adc TD_15adc.  (* 0x15adc auipc a1, 0x3a *)
      stw TF_15ae0 TD_15ae0 (Z_to_bv 64 195808) (Z_to_bv 64 2) ltac:(ok_data).  (* 0x15ae0 sw a0, 0x28(s2) *)
      sn TF_15ae4 TD_15ae4.  (* 0x15ae4 li a7, 0x60 *)
      sn TF_15ae8 TD_15ae8.  (* 0x15ae8 addi a0, a1, 0x2ac *)
      sn TF_15aec TD_15aec.  (* 0x15aec addi a1, s1, 0x38 *)
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma tls_c5 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word), wfJ sp0 Jb -> getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) -> getr regs 3 = Z_to_bv 64 67584 -> getr regs 4 = Z_to_bv 64 195968 -> getr regs 10 = tid -> getr regs 11 = Z_to_bv 64 327752 -> getr regs 18 = Z_to_bv 64 195768 -> getr regs 22 = Z_to_bv 64 0 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 0 -> getr regs 25 = Z_to_bv 64 0 -> getr regs 26 = Z_to_bv 64 0 -> getr regs 27 = Z_to_bv 64 0 -> (forall regs', getr regs' 1 = (Z_to_bv 64 87684) -> getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) -> getr regs' 3 = (Z_to_bv 64 67584) -> getr regs' 4 = (Z_to_bv 64 195968) -> getr regs' 8 = (pn_w inp rdraw) -> getr regs' 9 = (s1v) -> getr regs' 10 = (Z_to_bv 64 0) -> getr regs' 12 = (Z_to_bv 64 195888) -> getr regs' 18 = (Z_to_bv 64 327696) -> getr regs' 19 = (Z_to_bv 64 0) -> getr regs' 20 = (Z_to_bv 64 0) -> getr regs' 21 = (Z_to_bv 64 0) -> getr regs' 22 = (Z_to_bv 64 0) -> getr regs' 23 = (Z_to_bv 64 0) -> getr regs' 24 = (Z_to_bv 64 0) -> getr regs' 25 = (Z_to_bv 64 0) -> getr regs' 26 = (Z_to_bv 64 0) -> getr regs' 27 = (Z_to_bv 64 0) -> regs_agree (fun r => In r [1; 2; 8; 9; 10; 12; 18; 19; 20; 21]%list) regs regs' -> G (mkst regs' (0x15684 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87684))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327696))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 327080) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327096) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 327720) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 327728) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 195984) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 195960) (word_to_le_bytes 8 (Z_to_bv 64 195984))) (Z_to_bv 64 195768) (word_to_le_bytes 8 (Z_to_bv 64 195768))) (Z_to_bv 64 327696) ([Z_to_bv 8 1])) (Z_to_bv 64 195808) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 195800) (word_to_le_bytes 4 tid)) (Z_to_bv 64 195920) (word_to_le_bytes 8 (Z_to_bv 64 327752))) (Z_to_bv 64 195888) (word_to_le_bytes 8 (Z_to_bv 64 195888))) (Z_to_bv 64 195776) (word_to_le_bytes 8 (Z_to_bv 64 195768))) (Z_to_bv 64 195784) (word_to_le_bytes 8 (Z_to_bv 64 195768))) (Z_to_bv 64 195792) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) -> G (mkst regs (0x15af4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87684))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327696))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 327080) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327096) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 327720) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 327728) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 195984) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 195960) (word_to_le_bytes 8 (Z_to_bv 64 195984))) (Z_to_bv 64 195768) (word_to_le_bytes 8 (Z_to_bv 64 195768))) (Z_to_bv 64 327696) ([Z_to_bv 8 1])) (Z_to_bv 64 195808) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { sn TF_15af4 TD_15af4.  (* 0x15af4 addi a2, s2, 0x78 *)
      stw TF_15af8 TD_15af8 (Z_to_bv 64 195800) (tid) ltac:(ok_data).  (* 0x15af8 sw a0, 0x20(s2) *)
      stw TF_15afc TD_15afc (Z_to_bv 64 195920) (Z_to_bv 64 327752) ltac:(ok_data).  (* 0x15afc sd a1, 0x98(s2) *)
      stw TF_15b00 TD_15b00 (Z_to_bv 64 195888) (Z_to_bv 64 195888) ltac:(ok_data).  (* 0x15b00 sd a2, 0x78(s2) *)
      sn TF_15b04 TD_15b04.  (* 0x15b04 auipc a0, 0x3a *)
      ld_step TF_15b08 TD_15b08 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_4fff8_8) ltac:(apply bytes_le_to_Z_8).  (* 0x15b08 ld a0, 0x4f4(a0) *)
      stw TF_15b0c TD_15b0c (Z_to_bv 64 195776) (Z_to_bv 64 195768) ltac:(ok_data).  (* 0x15b0c sd s2, 0x8(s2) *)
      stw TF_15b10 TD_15b10 (Z_to_bv 64 195784) (Z_to_bv 64 195768) ltac:(ok_data).  (* 0x15b10 sd s2, 0x10(s2) *)
      stw TF_15b14 TD_15b14 (Z_to_bv 64 195792) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x15b14 sd a0, 0x18(s2) *)
      sn TF_15b18 TD_15b18.  (* 0x15b18 j 0x15b20 <static_init_tls+0x28c> *)
      ld_step TF_15b20 TD_15b20 (word_to_le_bytes 8 (Z_to_bv 64 87684)) (Z_to_bv 64 87684) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x15b20 ld ra, 0x38(sp) *)
      ld_step TF_15b24 TD_15b24 (word_to_le_bytes 8 (pn_w inp rdraw)) (pn_w inp rdraw) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x15b24 ld s0, 0x30(sp) *)
      ld_step TF_15b28 TD_15b28 (word_to_le_bytes 8 s1v) (s1v) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x15b28 ld s1, 0x28(sp) *)
      ld_step TF_15b2c TD_15b2c (word_to_le_bytes 8 (Z_to_bv 64 327696)) (Z_to_bv 64 327696) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x15b2c ld s2, 0x20(sp) *)
      ld_step TF_15b30 TD_15b30 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x15b30 ld s3, 0x18(sp) *)
      ld_step TF_15b34 TD_15b34 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x15b34 ld s4, 0x10(sp) *)
      ld_step TF_15b38 TD_15b38 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x15b38 ld s5, 0x8(sp) *)
      sv TF_15b3c TD_15b3c (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* 0x15b3c addi sp, sp, 0x40 *)
      stepret TF_15b40 TD_15b40 (0x15684 : word) ltac:(pin; first [reflexivity | bveq]).  (* 0x15b40 ret *)
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { sn TF_15af4 TD_15af4.  (* 0x15af4 addi a2, s2, 0x78 *)
      stw TF_15af8 TD_15af8 (Z_to_bv 64 195800) (tid) ltac:(ok_data).  (* 0x15af8 sw a0, 0x20(s2) *)
      stw TF_15afc TD_15afc (Z_to_bv 64 195920) (Z_to_bv 64 327752) ltac:(ok_data).  (* 0x15afc sd a1, 0x98(s2) *)
      stw TF_15b00 TD_15b00 (Z_to_bv 64 195888) (Z_to_bv 64 195888) ltac:(ok_data).  (* 0x15b00 sd a2, 0x78(s2) *)
      sn TF_15b04 TD_15b04.  (* 0x15b04 auipc a0, 0x3a *)
      ld_step TF_15b08 TD_15b08 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img s2img_4fff8_8) ltac:(apply bytes_le_to_Z_8).  (* 0x15b08 ld a0, 0x4f4(a0) *)
      stw TF_15b0c TD_15b0c (Z_to_bv 64 195776) (Z_to_bv 64 195768) ltac:(ok_data).  (* 0x15b0c sd s2, 0x8(s2) *)
      stw TF_15b10 TD_15b10 (Z_to_bv 64 195784) (Z_to_bv 64 195768) ltac:(ok_data).  (* 0x15b10 sd s2, 0x10(s2) *)
      stw TF_15b14 TD_15b14 (Z_to_bv 64 195792) (Z_to_bv 64 0) ltac:(ok_data).  (* 0x15b14 sd a0, 0x18(s2) *)
      sn TF_15b18 TD_15b18.  (* 0x15b18 j 0x15b20 <static_init_tls+0x28c> *)
      ld_step TF_15b20 TD_15b20 (word_to_le_bytes 8 (Z_to_bv 64 87684)) (Z_to_bv 64 87684) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x15b20 ld ra, 0x38(sp) *)
      ld_step TF_15b24 TD_15b24 (word_to_le_bytes 8 (pn_w inp rdraw)) (pn_w inp rdraw) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x15b24 ld s0, 0x30(sp) *)
      ld_step TF_15b28 TD_15b28 (word_to_le_bytes 8 s1v) (s1v) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x15b28 ld s1, 0x28(sp) *)
      ld_step TF_15b2c TD_15b2c (word_to_le_bytes 8 (Z_to_bv 64 327696)) (Z_to_bv 64 327696) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x15b2c ld s2, 0x20(sp) *)
      ld_step TF_15b30 TD_15b30 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x15b30 ld s3, 0x18(sp) *)
      ld_step TF_15b34 TD_15b34 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x15b34 ld s4, 0x10(sp) *)
      ld_step TF_15b38 TD_15b38 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* 0x15b38 ld s5, 0x8(sp) *)
      sv TF_15b3c TD_15b3c (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* 0x15b3c addi sp, sp, 0x40 *)
      stepret TF_15b40 TD_15b40 (0x15684 : word) ltac:(pin; first [reflexivity | bveq]).  (* 0x15b40 ret *)
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

End P4.
