(* proves the UBSan contract of diginet_mac_is_digidesign (fuzz_transport.ubsan, 0x17fb0), with its two pointer-overflow traps not taken. *)
(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame proofs/libdiginet/fuzz_frame/lib/U/Prog/diginet_mac_is_digidesign.v at 9bd29914ffdef650a37285056a472ff186b4331a to fuzz_transport's images *)
(* Walk of diginet_mac_is_digidesign (src/diginet_frame.c:50-53 at 835f336c) in fuzz_transport.ubsan, 0x17fb0.
   The UBSan checks at 0x17fc0 (mac = 2^64 - 1) and 0x17fd4 (mac > 2^64 - 3) branch to the trap at
   0x17ff0; bytes_at of the 6 bytes gives mac + 6 <= 2^64, so neither is taken. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import FrameBytes diginet_mac_is_digidesign_c.
Import ListNotations.
Open Scope Z_scope.

Ltac uns := rewrite ?unsigned_lit by lia.
Ltac br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; uns; solve_cond_rec]
  end.

Theorem diginet_mac_is_digidesign_holds : diginet_mac_is_digidesign_contract.
Proof.
  unfold diginet_mac_is_digidesign_contract, DIGINET_MAC_IS_DIGIDESIGN.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mac l
    Hmac Hlen BA.
  pose proof (bytes_at_bound rsegs m mac l BA) as BB. rewrite Hlen in BB. change (Z.of_nat 6) with 6 in BB.
  pose proof (rd1 m _ l 0 BA ltac:(lia)) as R0. change (Z.of_nat 0) with 0 in R0. rewrite Z.add_0_r in R0.
  pose proof (rd1 m _ l 1 BA ltac:(lia)) as R1. change (Z.of_nat 1) with 1 in R1.
  pose proof (rd1 m _ l 2 BA ltac:(lia)) as R2. change (Z.of_nat 2) with 2 in R2.
  remember (nth 0 l (Z_to_bv 8 0)) as b0 eqn:E0.
  remember (nth 1 l (Z_to_bv 8 0)) as b1 eqn:E1.
  remember (nth 2 l (Z_to_bv 8 0)) as b2 eqn:E2.
  assert (OUI : oui_of l = (bv_unsigned b0 =? 0) && (bv_unsigned b1 =? 160) && (bv_unsigned b2 =? 126)).
  { unfold oui_of, at8, bz, b8. rewrite <- E0, <- E1, <- E2. reflexivity. }
  pose proof (byte_range b0) as X0. pose proof (byte_range b1) as X1. pose proof (byte_range b2) as X2.
  (* 0x17fb0 beqz a0: mac is not 0. *)
  step. br false.
  step. step.
  if_cases Ka.
  - zify_cond Ka. rewrite zxb_u in Ka.
    assert (W : oui_of l = false) by (rewrite OUI, (proj2 (Z.eqb_neq _ _) Ka); reflexivity).
    step. step. apply evt_done. rewrite W. do 2 eexists. reflexivity.
  - zify_cond Ka. rewrite zxb_u in Ka.
    (* 0x17fc0 beq a0, -1: the UBSan trap of mac + 1, not taken (mac + 6 <= 2^64). *)
    step. step. br false.
    step. step. step.
    if_cases Kb.
    + zify_cond Kb. rewrite zxb_u in Kb.
      assert (W : oui_of l = false) by (rewrite OUI, Ka, (proj2 (Z.eqb_neq _ _) Kb); reflexivity).
      step. step. apply evt_done. rewrite W. do 2 eexists. reflexivity.
    + zify_cond Kb. rewrite zxb_u in Kb.
      (* 0x17fd4 bltu -3, a0: the UBSan trap of mac + 2, not taken. *)
      step. step. br false.
      step. step. step. step.
      apply evt_done.
      assert (A0 : v_sltiu (Z_to_bv 64 (bv_unsigned (zxb b2) + -126)) 1 = Z_to_bv 64 (if oui_of l then 1 else 0)).
      { unfold v_sltiu, zxb. rewrite zxb_u, OUI, Ka, Kb, !Z.eqb_refl. cbn [andb].
        destruct (Z.eq_dec (bv_unsigned b2) 126) as [E|E].
        - rewrite E. vm_compute. reflexivity.
        - rewrite (proj2 (Z.eqb_neq _ _) E).
          rewrite unsigned_lit_wrap. change (bv_wrap 64 1) with 1.
          replace ((bv_unsigned b2 + -126) mod 2 ^ 64 <? 1) with false; [reflexivity|].
          symmetry. apply Z.ltb_ge. Z.div_mod_to_equations. lia. }
      rewrite A0. do 2 eexists. reflexivity.
Qed.
