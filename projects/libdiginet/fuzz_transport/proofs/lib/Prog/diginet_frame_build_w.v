(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame proofs/libdiginet/fuzz_frame/lib/Prog/diginet_frame_build_w.v at b8f2ecf2c3ff0406d93584348ebba6e5957c14ce to fuzz_transport's images *)
(* Walk of diginet_frame_build in fuzz_transport.plain against diginet_frame_build_contract_w.
   Mode 0 or 1: the walk is diginet_frame_build_holds, with diginet_body_check_contract from
   diginet_body_check_contract_w; build_code_w and build_out_w are then build_code and build_out.
   With body = 0 the body is empty, and the entry state with a5 = 0 is that of
   diginet_frame_build_contract with body = 2^64 (Z_to_bv 64 (2^64) = Z_to_bv 64 0), which that
   contract admits. The binary does not test body against 0 alone: the test at 0x17944..0x17950
   is body_len == 0 || body != 0.
   Another mode: the prologue 0x178d8..0x17908 sets s8 = -1; the tests of buf, dst, src and h
   (0x1790c..0x17924) do not jump; at 0x17934 bltu 1, a7 jumps to 0x17aa4, because a7 =
   mode mod 2^64 is more than 1 for an int mode other than 0 and 1 (mode_bad_u); the epilogue
   returns sext.w s8 = -1. The function writes only the 96 bytes of its frame.
   diginet_frame_build_contract_of_w: the wide contract gives the narrow one.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac
  Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import diginet_frame_build_c diginet_body_check_c
  memcpy_c memset_c diginet_frame_build diginet_body_check_w_c diginet_body_check_w diginet_frame_build_w_c.
Import ListNotations.
Open Scope Z_scope.

Lemma build_code_w_ok : forall bb cap mode, (mode =? 0) || (mode =? 1) = true ->
  build_code_w bb cap mode = build_code bb cap.
Proof. intros bb cap mode H. unfold build_code_w. rewrite H. reflexivity. Qed.

Lemma build_out_w_ok : forall dmac smac send ack retry cmd ncmds bb mode oj, (mode =? 0) || (mode =? 1) = true ->
  build_out_w dmac smac send ack retry cmd ncmds bb mode oj = build_out dmac smac send ack retry cmd ncmds bb mode oj.
Proof. intros dmac smac send ack retry cmd ncmds bb mode oj H. unfold build_out_w, build_out, build_code_w. rewrite H. reflexivity. Qed.

Lemma mode_ok_cases : forall mode, (mode =? 0) || (mode =? 1) = true -> mode = 0 \/ mode = 1.
Proof.
  intros mode H. apply orb_true_iff in H. destruct H as [H|H]; apply Z.eqb_eq in H; [left | right]; exact H.
Qed.

(* The register a7 = Z_to_bv 64 mode of an int mode other than 0 and 1 is more than 1 unsigned. *)
Lemma mode_bad_u : forall mode, -2^31 <= mode < 2^31 -> (mode =? 0) || (mode =? 1) = false -> 1 < mode mod 2^64.
Proof.
  intros mode Hm H. apply orb_false_iff in H. destruct H as [H0 H1].
  apply Z.eqb_neq in H0. apply Z.eqb_neq in H1.
  destruct (Z_lt_le_dec mode 0) as [Ng|Ps].
  - rewrite <- (Z_mod_plus_full mode 1 (2^64)). rewrite Z.mod_small by lia. lia.
  - rewrite Z.mod_small by lia. lia.
Qed.

Theorem diginet_frame_build_holds_w :
  diginet_body_check_contract_w -> memcpy_contract -> memset_contract -> diginet_frame_build_contract_w.
Proof.
  intros DBCW MCPY MSET.
  pose proof (diginet_frame_build_holds (diginet_body_check_contract_of_w DBCW) MCPY MSET) as N.
  unfold diginet_frame_build_contract in N.
  unfold diginet_frame_build_contract_w.
  intros ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    out dst src hp body mode lo send ack retry cmd ncmds dmac smac bb oj
    HO Hdst Hsrc Hhp Hbody Hmode Hsend Hack Hretry Hcmd Hncmds Hhp64 Ldm BDM Lsm BSM BHP BB RWO
    Ddst Dsrc Dhp Dbody ST LO Dosp Ddsp Dssp Dhsp Dbsp MI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (Z.of_N 64) with 64 in Rsp.
  pose proof (rw_cells_bound _ _ _ _ RWO) as Roj. cbn [cells_size csize] in Roj. rewrite Nat.add_0_r in Roj.
  destruct ((mode =? 0) || (mode =? 1)) eqn:MO.
  - (* mode 0 or 1: diginet_frame_build_holds *)
    pose proof (mode_ok_cases mode MO) as Hm01.
    rewrite (build_code_w_ok bb (Z.of_nat (length oj)) mode MO).
    rewrite (build_out_w_ok dmac smac send ack retry cmd ncmds bb mode oj MO).
    destruct (Z.eq_dec body 0) as [B0|B0].
    + (* body = 0 with an empty body: a5 = 0 is the register value of the address 2^64 *)
      assert (L0 : length bb = 0%nat) by (destruct Hbody as [H|H]; [contradiction | exact H]).
      replace (Z_to_bv 64 body) with (Z_to_bv 64 (2^64)) by (rewrite B0; symmetry; exact bcw_null).
      hide Ddst. hide Dsrc. hide Dhp. hide Dbody. hide Dosp. hide Ddsp. hide Dssp. hide Dhsp. hide Dbsp.
      hide Hbody. hide Hm01.
      assert (T1 : 2^64 <> 0) by lia.
      assert (T2 : out + Z.of_nat (length oj) <= 2^64 \/ 2^64 + Z.of_nat (length bb) <= out) by (left; lia).
      assert (T3 : 2^64 + Z.of_nat (length bb) <= bv_unsigned sp - 240 \/ bv_unsigned sp <= 2^64)
        by (right; lia).
      exact (N ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
               out dst src hp (2^64) mode lo send ack retry cmd ncmds dmac smac bb oj
               HO Hdst Hsrc Hhp T1 Hm01 Hsend Hack Hretry Hcmd Hncmds Hhp64 Ldm BDM Lsm BSM BHP
               (bcw_empty_at m bb L0) RWO Ddst Dsrc Dhp T2 ST LO Dosp Ddsp Dssp Dhsp T3 MI).
    + exact (N ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
               out dst src hp body mode lo send ack retry cmd ncmds dmac smac bb oj
               HO Hdst Hsrc Hhp B0 Hm01 Hsend Hack Hretry Hcmd Hncmds Hhp64 Ldm BDM Lsm BSM BHP BB RWO
               Ddst Dsrc Dhp Dbody ST LO Dosp Ddsp Dssp Dhsp Dbsp MI).
  - (* another mode: 0x17934 jumps to the exit with s8 = -1 *)
    assert (BC : build_code_w bb (Z.of_nat (length oj)) mode = -1)
      by (unfold build_code_w; rewrite MO; reflexivity).
    assert (BO : build_out_w dmac smac send ack retry cmd ncmds bb mode oj = oj)
      by (unfold build_out_w; rewrite BC; reflexivity).
    rewrite BC, BO.
    assert (MB : keep (1 < mode mod 2^64)) by exact (mode_bad_u mode Hmode MO).
    clear N DBCW MCPY MSET BC BO.
    unfold DIGINET_FRAME_BUILD.
    pose proof (bytes_at_bound _ _ _ _ BDM) as Rdst. rewrite Ldm in Rdst.
    pose proof (bytes_at_bound _ _ _ _ BSM) as Rsrc. rewrite Lsm in Rsrc.
    pose proof ST as (Rlo & Rhi & _).
    pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (out, out + Z.of_nat (length oj))] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    (* The fence of the frame. *)
    pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp)] m) as MUS.
    pose proof (wmono_refl rsegs m) as WMS.
    clear Hbody BB BDM BSM BHP Ddst Dsrc Dhp Dbody Ddsp Dssp Dhsp Dbsp.
    hide Dosp. hide RWO.
    carve_frame 96%nat ST.
    do 13 step.
    (* 0x1790c .. 0x17924: buf, dst, src and h are not 0 *)
    step. take false.
    step. step. take false.
    step. step. take false.
    step. step. take false.
    (* 0x17934: bltu 1, a7 *)
    do 4 step.
    take_by true ltac:(unfold_cond; fold_lit_ux; rewrite unsigned_lit_wrap; apply Z.ltb_lt;
                       unfold keep in MB; exact MB).
    (* 0x17aa4 .. 0x17ad8: a0 = sext.w s8, the epilogue *)
    do 14 step.
    release_frame FR ST (bv_unsigned sp).
    xport RWO R MUS WMS ltac:(unfold keep in Dosp).
    apply evt_done. do 15 eexists. split;
      [ f_equal; fin_regs
      | split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; exact R ].
Qed.

Lemma diginet_frame_build_contract_of_w : diginet_frame_build_contract_w -> diginet_frame_build_contract.
Proof.
  unfold diginet_frame_build_contract_w, diginet_frame_build_contract.
  intros W ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    out dst src hp body mode lo send ack retry cmd ncmds dmac smac bb oj
    HO Hdst Hsrc Hhp Hbody Hmode Hsend Hack Hretry Hcmd Hncmds Hhp64 Ldm BDM Lsm BSM BHP BB RWO
    Ddst Dsrc Dhp Dbody ST LO Dosp Ddsp Dssp Dhsp Dbsp MI.
  assert (MO : (mode =? 0) || (mode =? 1) = true)
    by (destruct Hmode as [-> | ->]; reflexivity).
  assert (HM : -2^31 <= mode < 2^31) by (destruct Hmode as [-> | ->]; lia).
  rewrite <- (build_code_w_ok bb (Z.of_nat (length oj)) mode MO).
  rewrite <- (build_out_w_ok dmac smac send ack retry cmd ncmds bb mode oj MO).
  exact (W ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
           out dst src hp body mode lo send ack retry cmd ncmds dmac smac bb oj
           HO Hdst Hsrc Hhp (or_introl Hbody) HM Hsend Hack Hretry Hcmd Hncmds Hhp64 Ldm BDM Lsm BSM BHP BB RWO
           Ddst Dsrc Dhp Dbody ST LO Dosp Ddsp Dssp Dhsp Dbsp MI).
Qed.
