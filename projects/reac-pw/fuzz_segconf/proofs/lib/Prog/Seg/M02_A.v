(* Segment M02 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain, ELF 8dec0b814e6f): piece A of its inner walk
   (M02D.M02_A_stmt), 0x13ae0 .. 0x13b88.
   - 0x13ae0 .. 0x13aec: check_segments(c = s8, m = s0, returned = s4 = b2z ret) (check_segments_contract, its
     premise from M02_model's check_segments rc mc ret = true);
   - 0x13af0 `lw a0,0(s10)`: m->n = length (mc_seg mc) <= 32 (M02Bridge.mb_mconf_n); `blez` to 0x13b88 when it is 0;
   - else s1 = i = 0, s2 = 0x5a, s3 = m, and the loop: turn i (M02_AT.m02_turn, check_seg rc of the i-th segment
     from M02_model's forallb) to the latch 0x13b78, `lw a0,0(s10)` (m->n again), s1 += 1, s3 += 0x100,
     `blt s1,a0` back to 0x13b04; the induction is on the turns left (check_segments.v's LOOP form).
   The post is M02_mid 0x13b88 with the memory an M02_inv successor of m0.
   Part of the proof of LLVMFuzzerTestOneInput: piece A of segment M02 of its walk; no released proof of
   fuzz_segconf's LLVMFuzzerTestOneInput exists, written new (segment walk). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import check_segments_c reac_segconf_role_c
  check_role_c reac_segconf_model_c check_model_c reac_segconf_ignored_c check_ignore_c reac_segconf_role_file_c
  reac_segconf_ignore_file_c check_provenance_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require check_segments.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import M02D M02K M02_AT.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require M02_bridge.
Import M02_bridge.M02Bridge.
Import check_segments.CsPure.
Import M02_AT.M02APure.
Import ListNotations.
Open Scope Z_scope.

Theorem m02_A : check_segments_c.check_segments_contract -> reac_segconf_role_c.reac_segconf_role_contract ->
  check_role_c.check_role_contract -> reac_segconf_model_c.reac_segconf_model_contract ->
  check_model_c.check_model_contract -> reac_segconf_ignored_c.reac_segconf_ignored_contract ->
  check_ignore_c.check_ignore_contract -> reac_segconf_role_file_c.reac_segconf_role_file_contract ->
  reac_segconf_ignore_file_c.reac_segconf_ignore_file_contract -> check_provenance_c.check_provenance_contract ->
  M02D.M02_A_stmt.
Proof.
  intros CSEG HRo HCR HMo HCM HIg HCI HRF HIF HCP.
  unfold M02_A_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m
    St c mm cap rc mc ret Esp Es0 Es8 Es10 Es4 FRM MOD HM HI.
  subst sp s0 s8 s10 s4.
  pose proof HM as (_ & _ & _ & H16 & HT & H47 & _ & _ & _ & Hc0 & Hc16 & Hc & Hm0 & Hm16 & Hm & _).
  unfold SEG_C_SIZE in Hc. unfold SEG_M_SIZE in Hm.
  assert (Hb : 0 <= b2z ret <= 1) by (unfold b2z; destruct ret; lia).
  pose proof MOD as (CS & FA & _).
  unfold M02_FRAME.
  lazymatch goal with |- evt _ ?Q _ => set (Post := Q) end.
  (* 0x13ae0 mv a0,s8; mv a1,s0; mv a2,s4; jal check_segments *)
  do 4 zstep. rewrite ?Z.add_0_r, ?Z.add_0_l.
  eapply evt_cut.
  { eapply CSEG with (lo := St - 65536) (rc := rc) (mc := mc) (ret := ret).
    unfold check_segments_pre, apart, SEG_C_SIZE, SEG_M_SIZE. rewrite !unsigned_lit by lia.
    split; [lia|]. split; [exact Hc16|]. split; [eapply m02_rconf; eassumption|]. split; [left; lia|].
    split; [lia|]. split; [exact Hm16|]. split; [eapply m02_mconf; eassumption|]. split; [left; lia|].
    split; [reflexivity|]. split; [exact CS|].
    split; [eapply m02_stack_ok; try eassumption; unfold CHECK_SEGMENTS_STACK, M02_FRAME; lia|].
    eapply m02_mem_inv; eassumption. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m1 & -> & MU1 & WM1 & MI1 & _ & _).
  assert (HI1 : M02_inv St m0 m1)
    by (eapply m02_inv_call; [exact MU1 | exact HI | word_eq_tac | exact WM1 | exact MI1
                            | unfold CHECK_SEGMENTS_STACK; lia | lia | lia]).
  clear MU1 WM1 HI.
  rewrite ret_pc_even by (try lia; reflexivity).
  (* m->n *)
  assert (MC1 : mconf_at rsegs m1 mm mc) by (eapply m02_mconf; eassumption).
  destruct (mb_mconf_n rsegs m1 mm mc MC1) as [RN L32]. clear MC1.
  set (n := length (mc_seg mc)) in *. assert (En : n = length (mc_seg mc)) by reflexivity. clearbody n.
  (* The loop at 0x13b04 with j turns done and k left. *)
  assert (LOOP : forall k j (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' t3' t4' t5' t6' w9 w18 w19 : word)
      (m' : word -> option byte),
    (j + k = n)%nat -> (0 < k)%nat -> M02_inv St m0 m' ->
    w9 = Z_to_bv 64 (Z.of_nat j) -> w18 = Z_to_bv 64 90 -> w19 = Z_to_bv 64 (mm + 256 * Z.of_nat j) ->
    evt rsegs Post
      (MS (mkR ra' (Z_to_bv 64 (St - 208)) gp tp t0' t1' t2' (Z_to_bv 64 mm) w9 a0' a1' a2' a3' a4' a5' a6' a7'
               w18 w19 s4' s5 s6 s7 (Z_to_bv 64 c) s9 (Z_to_bv 64 (mm + MC_N)) s11 t3' t4' t5' t6')
          F (Z_to_bv 64 0x13b04) fc None m' (seg_rom rsegs))).
  { induction k as [|k IH];
      intros j ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' t3' t4' t5' t6' w9 w18 w19 m' Hjk Hk HIj
        E9 E18 E19; [lia|].
    subst w9 w18 w19.
    assert (Hj : (j < length (mc_seg mc))%nat) by lia.
    eapply evt_cut.
    { eapply (m02_turn HRo HCR HMo HCM HIg HCI HRF HIF HCP);
        [exact HM | exact Hj | exact (mb_check_seg_nth rc (mc_seg mc) j FA Hj) | exact HIj]. }
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & -> & HI'').
    unfold M02_FRAME.
    (* 0x13b78 lw a0,0(s10); addi s1,s1,1; addi s3,s3,0x100; blt s1,a0 *)
    assert (MCj : mconf_at rsegs m'' mm mc) by (eapply m02_mconf; eassumption).
    destruct (mb_mconf_n rsegs m'' mm mc MCj) as [RN' _]. rewrite <- En in RN'. clear MCj.
    zstep. clear RN'.
    rewrite (sx32_small (Z.of_nat n)) by lia.
    zstep. zstep. zstep.
    rewrite ?m02_lts by lia.
    destruct k as [|k].
    - cs_ntk.
      apply evt_done. unfold Post, M02_mid.
      do 28 eexists. split; [reflexivity|]. split; [exact FRM|]. split; [exact HI'' | exact I].
    - cs_tkn.
      eapply (IH (S j)); [lia | lia | exact HI'' | word_eq_tac | reflexivity | word_eq_tac]. }
  (* 0x13af0 lw a0,0(s10) *)
  zstep. clear RN.
  rewrite (sx32_small (Z.of_nat n)) by lia.
  (* 0x13af4 blez a0 *)
  zstep.
  rewrite ?m02_lts by lia.
  destruct (Nat.eq_dec n 0) as [N0|N0].
  - cs_tkn.
    apply evt_done. unfold Post, M02_mid.
    do 28 eexists. split; [reflexivity|]. split; [exact FRM|]. split; [exact HI1 | exact I].
  - cs_ntk.
    (* 0x13af8 mv s1,zero; addi s2,zero,0x5a; mv s3,s0 *)
    do 3 zstep.
    eapply (LOOP n 0%nat); [lia | lia | exact HI1 | word_eq_tac | word_eq_tac | word_eq_tac].
Qed.
