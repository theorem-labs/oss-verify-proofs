(* Segment M02 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (UBSan, ELF afc060e3cc9c), piece D (U/Prog/Seg/M02D.v):
   0x13e44 .. `jal calloc` at 0x13e7c.
   m_find(m = 0x50(sp), "nosuch0" (seg_spec.STR_NOSUCH, 0x10540), 7) (0x13e54, m_find_contract); `bnez a0` to
   0x13e6c when the model has the name, else check_absent(c = 0x48(sp), "nosuch0") (0x13e68, check_absent_contract,
   premise SegModel.absent from M02_model's probe_ok rc mc S_nosuch); then s0 = cap (`ld 0x20(sp)`), s4 = cap + 1,
   a1 = 18, a0 = s4 and `jal calloc` (CallocBigC.CALLOC_PC 0x172a0, ra = 0x13e80).
   Part of the proof of LLVMFuzzerTestOneInput: this file is piece D of segment M02 of its walk; no released proof
   of fuzz_segconf's LLVMFuzzerTestOneInput exists, written new. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require M02_bridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env m_find_c check_absent_c
  reac_segconf_find_c reac_segconf_role_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.Seg Require Import Tac_b1 M02D M02K.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg.M02_bridge.M02Bridge.
Import ListNotations.
Open Scope Z_scope.

Lemma m02d_nosuch_len : Z.of_nat (length (zb S_nosuch)) = 7.
Proof. reflexivity. Qed.

Lemma m02d_nosuch_zs : zs (zb S_nosuch) = S_nosuch.
Proof. vm_compute. reflexivity. Qed.

Theorem m02_D : m_find_contract -> check_absent_contract -> M02_D_stmt.
Proof.
  intros MF CA. unfold M02_D_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m0 m S c mm cap rc mc ret Esp E2 E11 FRM HMod HM HI.
  subst sp s2 s11. unfold M02_FRAME.
  pose proof (m02_bnds S c mm cap rc mc m0 HM) as (H16 & HT & H47 & Hc0 & Hc16 & Hc & Hm0 & Hm16 & Hm).
  pose proof HMod as (_ & _ & _ & _ & _ & HPn).
  pose proof (mb_mconf_n rsegs m0 mm mc (m02_mconf S c mm cap rc mc m0 m0 HM (m02_inv_refl _ _ _ _ _ _ _ HM)))
    as (_ & HL32).
  unfold SEG_C_SIZE, SEG_M_SIZE in Hc, Hm.
  (* the continuation at 0x13e6c: s0 = cap, s4 = cap + 1, a1 = 18, a0 = s4, jal calloc *)
  assert (TAIL : forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26
                         x28 x29 x30 x31 : word) (m2 : word -> option byte),
    M02_inv S m0 m2 ->
    evt rsegs (M02_post S mm cap gp tp m0)
      (MS (mkR x1 (Z_to_bv 64 (S - 240)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               (bv_not (Z_to_bv 64 mm)) x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (mm + MC_N)) x28 x29 x30 x31)
          F (Z_to_bv 64 0x13e6c) fc None m2 (seg_rom rsegs))).
  { intros x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
      m2 HI2.
    pose proof (b1_ld8 _ _ _ (m02_cap S c mm cap rc mc m0 m2 HM HI2)) as RC. unfold M02_FRAME in RC.
    m02_show zstep. m02_show zstep. m02_show zstep. m02_show zstep. m02_show zstep.
    apply evt_done. unfold M02_post. do 24 eexists.
    m02_show ltac:(split; [reflexivity|]). split; [exact FRM | exact HI2]. }
  (* 0x13e44 auipc; 0x13e48 addi a1 = "nosuch0"; 0x13e4c a2 = 7; 0x13e50 ld a0,0x50(sp) = m; 0x13e54 jal m_find *)
  pose proof (b1_ld8 _ _ _ (m02_cellm S c mm cap rc mc m0 m HM HI)) as RM.
  unfold M02_FRAME in RM.
  m02_show zstep. m02_show zstep. m02_show zstep. m02_show zstep. m02_show zstep.
  clear RM.
  eapply evt_cut.
  { apply MF with (lo := S - 65536) (mc := mc) (l := zb S_nosuch).
    m02_show ltac:(rewrite !unsigned_lit by lia;
      apply (m02_mfp S c mm cap rc mc m0 m HM HI);
      [ exact (proj1 (proj1 (bytes_at_app rsegs m _ _ _) (m02_nosuch m (m02_mem_inv S m0 m HI))))
      | rewrite m02d_nosuch_len; unfold apart, M02_FRAME; left; lia ]). }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> &
              MU & WM & MI & ST & _).
  rewrite ret_pc_even by (try lia; reflexivity).
  m02_show ltac:(rewrite !unsigned_lit in MU by lia).
  assert (HI1 : M02_inv S m0 m1)
    by (apply (m02_inv_step S m0 m m1 _ HI MU WM MI); unfold M_FIND_STACK; [m02_subfp | m02_low]).
  clear MU WM MI ST HI.
  rewrite !unsigned_lit by lia.
  rewrite m02d_nosuch_zs.
  unfold m_find_ptr.
  destruct (m_find mc S_nosuch) as [i|] eqn:EF.
  - (* the model has the name: 0x13e58 bnez taken *)
    pose proof (mb_mfind_lt mc S_nosuch i EF) as Hi.
    m02_show zstep. m02_tkn.
    apply TAIL. exact HI1.
  - (* not in the model: check_absent(c, "nosuch0") *)
    unfold probe_ok in HPn. rewrite EF in HPn.
    m02_show zstep. m02_ntk.
    pose proof (b1_ld8 _ _ _ (m02_cellc S c mm cap rc mc m0 m1 HM HI1)) as RC. unfold M02_FRAME in RC.
    m02_show zstep. m02_show zstep. m02_show zstep. m02_show zstep.
    clear RC.
    eapply evt_cut.
    { apply CA with (lo := S - 65536) (rc := rc) (nm := S_nosuch).
      m02_show ltac:(rewrite !unsigned_lit by lia; split; [|exact HPn];
        apply (m02_qp S c mm cap rc mc m0 m1 HM HI1);
        [ unfold CHECK_ABSENT_STACK, ROLE_STACK, FIND_STACK, M02_FRAME; lia | unfold STR_NOSUCH; lia
        | exact (m02_nosuch_z m1 (m02_mem_inv S m0 m1 HI1))
        | replace (Z.of_nat (length S_nosuch)) with 7 by reflexivity;
          unfold apart, M02_FRAME, STR_NOSUCH; left; lia ]). }
    intros ms' (u0 & u1 & u2 & u10 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u3 & u4 & u5 & u6 & m2 & -> &
                MU & WM & MI & ST & _).
    rewrite ret_pc_even by (try lia; reflexivity).
    m02_show ltac:(rewrite !unsigned_lit in MU by lia).
    assert (HI2 : M02_inv S m0 m2)
      by (apply (m02_inv_step S m0 m1 m2 _ HI1 MU WM MI);
          unfold CHECK_ABSENT_STACK, ROLE_STACK, FIND_STACK; [m02_subfp | m02_low]).
    apply TAIL. exact HI2.
Qed.
