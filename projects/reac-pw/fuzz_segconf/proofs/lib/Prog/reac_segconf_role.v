(** reac_segconf_role (plain build, 0x158c0): proof of [reac_segconf_role_contract] (Prog/reac_segconf_role_c.v) from
    reac_segconf_find's contract (Prog/reac_segconf_find_c.v).

    Code (plain image): `addi sp,sp,-16; sd ra,8(sp); sd s0,0(sp); mv s0,a2;
    jal reac_segconf_find` (0x15824) with a0 = c and a1 = name unchanged; `beqz a0` to the epilogue 0x158f4 (a0 = 0);
    `mv a1,a0; lw a0,0x14(a0); beqz a0` (s->role_set); `li a0,1; beqz s0` (out = NULL); `lw a1,0x10(a1); sw a1,0(s0)`
    (the store to *out of s->role); the epilogue restores ra and s0 and returns.
    The loads read c->seg[i] for SegModel.r_find rc nm = Some i (seg_query_facts.sq_role_set, sq_role); the word the
    store writes is le4 of the sign-extended load of le4 r, which is le4 r since 0 <= r < 2^32 (sq_le4_sx32). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_query_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import reac_segconf_find_c reac_segconf_role_c.
Import ListNotations.
Open Scope Z_scope.

(** A conditional branch taken / not taken, the other side refuted by arithmetic. *)
Ltac tkn := let K := fresh "K" in
  if_cases K; [clear K | exfalso; zify_cond K; zb_masks; Z.div_mod_to_equations; lia].
Ltac ntk := let K := fresh "K" in
  if_cases K; [exfalso; zify_cond K; zb_masks; Z.div_mod_to_equations; lia | clear K].

(** The return when nothing was stored: the footprint is the frames [Sp - 48, Sp) (MU's), and the memory post is True
    (no role) or vacuous (out = NULL). *)
Ltac close_frames MU :=
  finish; try (rewrite unsigned_lit by lia; assumption);
  lazymatch goal with
  | |- munch _ _ _ =>
      eapply munch_weaken; [|exact MU]; unfold sub_fp, role_W, ROLE_STACK, FIND_STACK;
      cbn [outside Z.eqb]; intros x [Hx _]; split; [lia | exact I]
  | |- _ => cbv beta; first [exact I | intros HZ; exfalso; apply HZ; reflexivity]
  end.

Theorem reac_segconf_role_holds : reac_segconf_find_contract -> reac_segconf_role_contract.
Proof.
  intros HF. unfold reac_segconf_role_contract, role_pre, REAC_SEGCONF_ROLE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo rc nm
    [(Hc0 & Hc16 & (bs & HB & HE) & HAc & Hn0 & (nbs & HN & HNz & HN0) & HAn & (ST & HK & HS16 & HW) & MI) HOUT].
  unfold apart, SEG_C_SIZE, ROLE_STACK, FIND_STACK in *.
  pose proof (sq_rconf_len rc bs HE) as [HL HL32].
  pose proof (bytes_at_bound _ _ _ _ HB) as HBB.
  assert (HNL : length nm = length nbs) by (rewrite <- HNz; unfold zs; apply length_map).
  pose proof (proj1 ST) as LO0.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 a0) as Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
  change (bv_modulus 64) with (2 ^ 64) in Rsp, Ra0, Ra1, Ra2.
  pose proof (Z_to_bv_lit_self sp) as Esp. pose proof (Z_to_bv_lit_self a0) as Ea0.
  pose proof (Z_to_bv_lit_self a1) as Ea1. pose proof (Z_to_bv_lit_self a2) as Ea2.
  set (Sp := bv_unsigned sp) in *. set (C := bv_unsigned a0) in *. set (Nm := bv_unsigned a1) in *.
  set (Out := bv_unsigned a2) in *.
  rewrite <- Esp, <- Ea0, <- Ea1, <- Ea2. clearbody Sp C Nm Out. clear Esp Ea0 Ea1 Ea2.
  pose proof (munch_refl [(Sp - 48, Sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  (* prologue: the frame [Sp - 16, Sp) holds s0 and ra *)
  zstep. carve_frame 16%nat ST.
  zstep. zstep. zstep. zstep.
  (* reac_segconf_find(c, name) at Sp - 16 *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    eapply evt_cut; [eapply HF with (lo := lo) (rc := rc) (nm := nm) |] end.
  { rewrite !unsigned_lit by lia. unfold query_pre, stack_ok, rconf_at, cstrz_at, apart, SEG_C_SIZE, FIND_STACK.
    split; [exact Hc0|]. split; [exact Hc16|]. split; [exists bs; split; assumption|].
    split; [lia|]. split; [exact Hn0|]. split; [exists nbs; split; [assumption | split; assumption]|].
    split; [lia|].
    split; [split; [assumption | split; [lia | split; [Z.div_mod_to_equations; lia | intros a Ha; apply HW; lia]]]|].
    assumption. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> &
              MU2 & WM2 & MI2 & ST2 & _).
  unfold FIND_STACK in MU2. rewrite ?unsigned_lit in MU2, ST2 by lia. rewrite (unsigned_lit C) by lia.
  lazymatch type of MU2 with munch _ ?m1 _ =>
    transport_after_call rsegs m1 m2 MU2 WM2; clear MU2 WM2;
    try match goal with H : mem_inv rsegs m1 |- _ => clear H end; try clear m1 end.
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite sq_find_ptr. unfold r_role.
  destruct (r_find rc nm) as [i|] eqn:RF.
  - (* found: s = c + 356 i *)
    pose proof (sq_find_lt rc nm i RF) as Hi.
    assert (Hi32 : (i < 32)%nat) by lia.
    pose proof (sq_role_set rsegs m2 C bs rc i HB HE Hi) as RSET. unfold RS_ROLE_SET in RSET.
    zstep. ntk.
    zstep.
    destruct (rs_role_set (r_seg rc i)) eqn:RSS; cbn [b2z] in RSET.
    + (* role_set: a0 = 1 *)
      zstep. change (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1). zstep. ntk. zstep.
      destruct (Z.eqb_spec Out 0) as [HO0|HO0].
      * (* out = NULL: no store *)
        subst Out. zstep. tkn.
        zstep. zstep. zstep. release_frame FR ST2 Sp. zstep.
        close_frames MU.
      * destruct HOUT as [HO0' | (HO4 & HOW & HOA)]; [contradiction|].
        pose proof HOW as (HOW0 & HOW4 & _).
        zstep. ntk.
        pose proof (sq_role rsegs m2 C bs rc i HB HE Hi) as [RR RROLE]. unfold RS_ROLE in RROLE.
        zstep.
        pose proof (wr_at_store_ok rsegs m2 Out 4 0 4 (wr_at_transport rsegs _ _ _ _ HOW WM) ltac:(lia) ltac:(lia))
          as HS.
        rewrite Z.add_0_r in HS.
        step.
        set (v := rs_role (r_seg rc i)) in *.
        replace (le4 (sx32 (Z_to_bv 64 v))) with (le4 (Z_to_bv 64 v)) by (symmetry; apply sq_le4_sx32; exact RR).
        change (Z_to_bv 64 Out) with (wa Out).
        assert (HQ : bytes_at rsegs (write_to_mem m2 (wa Out) (le4 (Z_to_bv 64 v))) Out (le4 (Z_to_bv 64 v)))
          by (apply bytes_at_write_same; rewrite ?length_le4; lia).
        apply (rw_cells_frame rsegs m2 _ _ Out (le4 (Z_to_bv 64 v))) in FR;
          [| lia | rewrite length_le4; lia | rewrite length_le4; cbn [cells_size csize Nat.add]; lia].
        apply (stk_write rsegs m2 lo (Sp + -16) Out (le4 (Z_to_bv 64 v))) in ST2; [| lia | rewrite length_le4; lia].
        apply (munch_weaken _ [(Sp - 48, Sp); (Out, Out + 4)]) in MU;
          [| unfold sub_fp; cbn [outside]; intros x (Hx1 & Hx2 & _); split; [exact Hx1 | exact I]].
        apply (munch_write _ m m2 Out (le4 (Z_to_bv 64 v))) in MU;
          [| lia | rewrite length_le4; lia | rewrite length_le4; cbn [inside]; lia].
        apply (wmono_write rsegs m m2 (wa Out) (le4 (Z_to_bv 64 v))) in WM.
        apply (mem_inv_store rsegs m2 (wa Out) (le4 (Z_to_bv 64 v))) in MI2; [| rewrite length_le4; exact HS].
        set (m3 := write_to_mem m2 (wa Out) (le4 (Z_to_bv 64 v))) in *. clearbody m3.
        zstep. zstep. zstep. release_frame FR ST2 Sp. zstep.
        finish; try (rewrite unsigned_lit by lia; assumption).
        all: lazymatch goal with
          | |- munch _ _ _ =>
              eapply munch_weaken; [|exact MU]; unfold sub_fp, role_W, ROLE_STACK, FIND_STACK;
              replace (Out =? 0) with false by (symmetry; apply Z.eqb_neq; exact HO0);
              cbn [outside]; intros x (Hx1 & Hx2 & _); split; [lia | split; [exact Hx2 | exact I]]
          | |- _ => cbv beta; intros _; exact HQ
          end.
    + (* role not set: a0 = 0 *)
      zstep. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0). zstep. tkn.
      zstep. zstep. zstep. release_frame FR ST2 Sp. zstep.
      close_frames MU.
  - (* not found: a0 = 0 *)
    zstep. tkn.
    zstep. zstep. zstep. release_frame FR ST2 Sp. zstep.
    close_frames MU.
Qed.
