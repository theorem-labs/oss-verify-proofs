(* The walk of on_announce (transport/src/diginet_session.c:184-221) in the plain image, entry 0x16804, against
   on_announce_c.v. A section over the caller's registers, frame and world; one lemma per segment of the code:
   oa_epi (0x16860, the common return), oa_e0w (0x1699c), oa_e0 (0x16948), oa_fg (0x169d4), oa_tail (0x168f4, the
   DESK notice and the branches after it), oa_loop (0x168c8, find_mac), oa_seg (0x168a4), oa_main (0x16804, the
   parse and the personality). The frame of 336 bytes is kept as five blocks: the FOREIGN notice (sp - 336), the DESK
   notice (sp - 264), the announce (sp - 192), the STATE notice (sp - 152) and the saved registers (sp - 80). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TImg TSess0 TCb TSess TNeed.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TImgP TContract TSessC.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import codec_cells bcmp_c memset_c
  diginet_announce_parse_c diginet_personality_from_name_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import diginet_session_wake_c maybe_online_c
  notice_c on_announce_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import on_announce_lem.
Import ListNotations.
Open Scope Z_scope.

Section OnAnnounce.

Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (lo fp buf now : Z) (b fj B' : list byte) (TF : option tframe).

Hypothesis Hnow : 0 <= now < 2^64.
Hypothesis FC : fr_code b = 0.
Hypothesis Pbuf : 0 < buf.
Hypothesis Lbuf : buf + Z.of_nat (length b) < 2^64.
Hypothesis OWbuf : buf + Z.of_nat (length b) <= W_BASE_PLAIN \/ W_BASE_PLAIN + W_LEN <= buf.
Hypothesis OSbuf : buf + Z.of_nat (length b) <= bv_unsigned sp - 1184 \/ bv_unsigned sp <= buf.
Hypothesis Pfp : 0 < fp.
Hypothesis Lfp : fp + 64 < 2^64.
Hypothesis OWfp : fp + 64 <= W_BASE_PLAIN \/ W_BASE_PLAIN + W_LEN <= fp.
Hypothesis OSfp : fp + 64 <= bv_unsigned sp - 1184 \/ bv_unsigned sp <= fp.
Hypothesis Afp : fp mod 8 = 0.
Hypothesis TF0 : tframe_at m0 sp 1184 TF.
Hypothesis RI0 : TContract.relro_img m0.
Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
Hypothesis LO : lo + 1184 <= bv_unsigned sp.
Hypothesis WO : W_BASE_PLAIN + W_LEN <= bv_unsigned sp - 1184.
Hypothesis Hlo : 0 <= lo.

Hypothesis HBCMP : bcmp_contract.
Hypothesis HMEMSET : memset_contract.
Hypothesis HPARSE : diginet_announce_parse_contract.
Hypothesis HPFN : diginet_personality_from_name_contract.
Hypothesis HWAKE : diginet_session_wake_contract.
Hypothesis HMAYBE : maybe_online_contract.
Hypothesis HNOTICE : notice_contract.

(* after a callee: carry every fact across its footprint, drop the old memory *)
Ltac oa_after MU WM :=
  lazymatch type of MU with
  | munch _ ?ma ?mb =>
      transport_after_call rsegs ma mb MU WM; clear MU WM;
      try match goal with H : mem_inv rsegs ma |- _ => clear H end; try clear ma
  end.

(* the post of on_announce_contract *)
Definition oa_Q : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 1184, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m0 m' /\
    wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
    wmem rsegs m' B' /\ g_fail_next B' <= 1.

Ltac oa_facts :=
  wk_facts;
  try (assert (Eoff : OFF_g_s = 1648) by reflexivity);
  pose proof (bv_unsigned_in_range 64 sp) as Rsp; unfold bv_modulus in Rsp; change (2 ^ Z.of_N 64) with (2^64) in Rsp;
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -336)) = bv_unsigned sp + -336) by (apply unsigned_lit; lia);
  try unfold oa_W in *;
  unfold notice_contract, notice_FRAME, notice_ENTRY in HNOTICE;
  unfold maybe_online_contract, maybe_online_FRAME, maybe_online_ENTRY in HMAYBE;
  unfold diginet_session_wake_contract, diginet_session_wake_FRAME, diginet_session_wake_ENTRY in HWAKE;
  unfold diginet_announce_parse_contract, DIGINET_ANNOUNCE_PARSE in HPARSE;
  unfold diginet_personality_from_name_contract, DIGINET_PERSONALITY_FROM_NAME,
    DIGINET_PERSONALITY_FROM_NAME_DEPTH in HPFN;
  unfold memset_contract, MEMSET in HMEMSET;
  unfold bcmp_contract, BCMP in HBCMP.

(* 0x16860: the common epilogue (restore ra, s0-s8, pop the 336-byte frame, ret) *)
Lemma oa_epi : forall (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8'
                       t3' t4' t5' t6' : word) (m : word -> option byte) (J0 J1 J2 J3 : list byte),
  rw_cells rsegs m (bv_unsigned sp + -336) [CB 72 J0] ->
  rw_cells rsegs m (bv_unsigned sp + -264) [CB 72 J1] ->
  rw_cells rsegs m (bv_unsigned sp + -192) [CB 40 J2] ->
  rw_cells rsegs m (bv_unsigned sp + -152) [CB 72 J3] ->
  rw_cells rsegs m (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (bv_unsigned sp + -336) ->
  munch (oa_W sp) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  wmem rsegs m B' -> g_fail_next B' <= 1 ->
  evt rsegs oa_Q
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -336)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
             s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x16860) fc None m (seg_rom rsegs)).
Proof.
  intros ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' t3' t4' t5' t6' m
    J0 J1 J2 J3 R0 R1 R2 R3 R4 ST MU WMO MI WM GF.
  oa_facts.
  do 10 step.
  release_frame R0 ST (bv_unsigned sp + -264).
  release_frame R1 ST (bv_unsigned sp + -192).
  release_frame R2 ST (bv_unsigned sp + -152).
  release_frame R3 ST (bv_unsigned sp + -80).
  release_frame R4 ST (bv_unsigned sp).
  do 2 step.
  apply evt_done. unfold oa_Q. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WMO|]. split; [exact MI|]. split; [exact ST|]. split; [exact WM | exact GF].
Qed.

(* 0x1699c: diginet_session.c:204-205, the state test after the e0 *)
Lemma oa_e0w : forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' t3' t4' t5' t6' : word)
    (m : word -> option byte) (B3 : list byte) (J0 J1 J2 J3 : list byte),
  (if (S_state B3 =? DIGINET_S_IDLE) && negb (S_cfg_auto_wake B3 =? 0) then
     match diginet_session_wake_m timg_plain TF B3 now with
     | None => None
     | Some (B, _) => Some (B, tt)
     end
   else Some (B3, tt)) = Some (B', tt) ->
  wmem rsegs m B3 -> g_fail_next B3 <= 1 ->
  rw_cells rsegs m (bv_unsigned sp + -336) [CB 72 J0] ->
  rw_cells rsegs m (bv_unsigned sp + -264) [CB 72 J1] ->
  rw_cells rsegs m (bv_unsigned sp + -192) [CB 40 J2] ->
  rw_cells rsegs m (bv_unsigned sp + -152) [CB 72 J3] ->
  rw_cells rsegs m (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (bv_unsigned sp + -336) ->
  munch (oa_W sp) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  evt rsegs oa_Q
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -336)) gp tp t0' t1' t2' (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
             (Z_to_bv 64 now) (Z_to_bv 64 (S_state B3)) a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8'
             s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x1699c) fc None m (seg_rom rsegs)).
Proof.
  intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' t3' t4' t5' t6' m B3
    J0 J1 J2 J3 HM WM GF R0 R1 R2 R3 R4 ST MU WMO MI.
  oa_facts.
  pose proof (s32_range B3 A_S_state) as Rst. change (s32_at B3 A_S_state) with (S_state B3) in Rst.
  (* bnez a0 *)
  step.
  rewrite oa_eqb0 by lia.
  destruct (Z.eqb_spec (S_state B3) 0) as [S0|S0]; cbn [negb]; cbv iota.
  2:{ (* not IDLE: return *)
    unfold DIGINET_S_IDLE in HM. rewrite (proj2 (Z.eqb_neq _ _) S0) in HM. cbv beta iota delta [andb] in HM.
    injection HM as HE; subst.
    eapply oa_epi; [exact R0 | exact R1 | exact R2 | exact R3 | exact R4 | exact ST | exact MU | exact WMO
                   | exact MI | exact WM | exact GF]. }
  unfold DIGINET_S_IDLE in HM. rewrite S0, Z.eqb_refl in HM. cbv beta iota delta [andb] in HM.
  (* lw a0, 16(s0): cfg.auto_wake; beqz *)
  do 2 step.
  change (s32_at B3 1664) with (S_cfg_auto_wake B3) in *.
  pose proof (s32_range B3 A_S_cfg_auto_wake) as Raw. change (s32_at B3 A_S_cfg_auto_wake) with (S_cfg_auto_wake B3) in Raw.
  rewrite oa_eqb0 by lia.
  destruct (Z.eqb_spec (S_cfg_auto_wake B3) 0) as [W0|W0]; cbv iota.
  { cbv beta iota delta [negb] in HM.
    injection HM as HE; subst.
    eapply oa_epi; [exact R0 | exact R1 | exact R2 | exact R3 | exact R4 | exact ST | exact MU | exact WMO
                   | exact MI | exact WM | exact GF]. }
  cbv beta iota delta [negb] in HM.
  destruct (diginet_session_wake_m timg_plain TF B3 now) as [[Bw r]|] eqn:HW; [|discriminate HM].
  injection HM as HE; subst.
  (* mv a0, s0; mv a1, s1; jal diginet_session_wake *)
  do 3 step.
  eapply evt_cut.
  { eapply HWAKE with (lo := lo) (TF := TF) (B := B3);
      [ reflexivity | reflexivity | exact Hnow | exact WM | exact GF | exact HW
      | eapply oa_tframe; [exact TF0 | exact MU | rewrite Hsp; lia | rewrite Hsp; lia]
      | eapply oa_relro; [exact RI0 | exact MU | lia]
      | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST | rewrite Hsp; lia
      | unfold w_off_stack; rewrite Hsp; lia | exact MI ]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & Eq & MUc & WMc & MI4 & ST4 & WM4 & GF4).
  subst ms'. rewrite Hsp in MUc, ST4. clear WM.
  transport_after_call rsegs m m4 MUc WMc. clear MUc WMc MI. try clear m.
  rewrite (ret_pc_even 0x169b4) by (first [lia | reflexivity]).
  step.
  eapply oa_epi; [exact R0 | exact R1 | exact R2 | exact R3 | exact R4 | exact ST4 | exact MU | exact WMO
                 | exact MI4 | exact WM4 | exact GF4].
Qed.

(* 0x16948: the e0 branch (diginet_session.c:200-206): foreign = 0; an ONLINE session is lost (session_lost and
   set_state inlined: the STATE notice); then the auto-wake test *)
Lemma oa_e0 : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' t3' t4' t5' t6' : word)
    (m : word -> option byte) (B2 : list byte) (off : Z) (J0 J1 J2 J3 : list byte),
  oa_rest_m timg_plain TF B2 DIGINET_CMD_ANNOUNCE off (oa_ann (fr_body b)) now = Some (B', tt) ->
  wmem rsegs m B2 -> g_fail_next B2 <= 1 ->
  rw_cells rsegs m (bv_unsigned sp + -336) [CB 72 J0] ->
  rw_cells rsegs m (bv_unsigned sp + -264) [CB 72 J1] ->
  rw_cells rsegs m (bv_unsigned sp + -192) [CB 40 J2] ->
  rw_cells rsegs m (bv_unsigned sp + -152) [CB 72 J3] ->
  rw_cells rsegs m (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (bv_unsigned sp + -336) ->
  munch (oa_W sp) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  evt rsegs oa_Q
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -336)) gp tp t0' t1' t2' (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
             (Z_to_bv 64 now) a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x16948) fc None m (seg_rom rsegs)).
Proof.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' t3' t4' t5' t6' m B2 off
    J0 J1 J2 J3 HM WM GF R0 R1 R2 R3 R4 ST MU WMO MI.
  oa_facts.
  pose proof (wm_len _ _ _ _ WM) as LB2.
  pose proof (s32_range B2 A_S_state) as Rst. change (s32_at B2 A_S_state) with (S_state B2) in Rst.
  unfold oa_rest_m in HM. change (DIGINET_CMD_ANNOUNCE =? DIGINET_CMD_ANNOUNCE) with true in HM.
  cbv beta iota zeta in HM.
  assert (SF : S_state (set_S_foreign B2 0) = S_state B2).
  { unfold S_state, set_S_foreign, A_S_state, A_S_foreign. apply s32_at_upd_out; rewrite ?length_put, ?LB2;
      unfold OFF_g_s, W_LEN; lia. }
  rewrite SF in HM.
  assert (GF3 : g_fail_next (set_S_foreign B2 0) <= 1).
  { unfold set_S_foreign, A_S_foreign. rewrite oa_gf_upd; [exact GF | exact LB2 | ..]; rewrite ?length_put;
      unfold OFF_g_fail_next, OFF_g_s, W_LEN; lia. }
  pose proof (oa_len_upd B2 (put 4 0) A_S_foreign LB2 ltac:(unfold A_S_foreign, OFF_g_s; lia)
                ltac:(rewrite length_put; unfold A_S_foreign, OFF_g_s, W_LEN; lia)) as LB3.
  change (upd B2 A_S_foreign (put 4 0)) with (set_S_foreign B2 0) in LB3.
  (* lw a0, 112(s0); li s2, 2; sw zero, 136(s0); bne a0, s2 *)
  do 4 step.
  change (s32_at B2 1760) with (S_state B2) in *.
  change (upd B2 1784 (put 4 0)) with (set_S_foreign B2 0) in *.
  rewrite oa_eqb by lia.
  destruct (Z.eqb_spec (S_state B2) 2) as [S2|S2]; cbn [negb]; cbv iota.
  2:{ (* not ONLINE: nothing lost *)
    unfold DIGINET_S_ONLINE in HM. rewrite (proj2 (Z.eqb_neq _ _) S2) in HM. cbv beta iota in HM.
    rewrite <- SF.
    eapply oa_e0w; [exact HM | exact WMw | exact GF3 | exact R0 | exact R1 | exact R2 | exact R3 | exact R4
                   | exact ST | exact MU | exact WMO | exact MI]. }
  unfold DIGINET_S_ONLINE in HM. rewrite S2, Z.eqb_refl in HM. cbv beta iota in HM.
  (* session_lost inlined: dcv = 0, inflight = 0, then set_state (IDLE, DESK_OFFLINE) *)
  apply oa_cut with (k := 16%nat) in R3; [|lia]. destruct R3 as [R3 R3z]. change (Z.of_nat 16) with 16 in R3z.
  cbn [Nat.sub] in R3z. replace (bv_unsigned sp + -152 + 16) with (bv_unsigned sp + -136) in R3z by lia.
  do 6 step.
  set (B3 := set_S_foreign B2 0) in *.
  set (B4 := set_S_desk_counter_valid (set_S_inflight B3 0) 0).
  assert (EB4 : upd (upd B3 1816 (put 4 0)) 1860 (put 4 0) = B4).
  { unfold B4, set_S_desk_counter_valid, set_S_inflight, A_S_desk_counter_valid, A_S_inflight.
    change (OFF_g_s + 168) with 1816. change (OFF_g_s + 212) with 1860.
    apply upd_upd_comm; rewrite ?length_put, ?LB3; unfold W_LEN; lia. }
  assert (LB4 : length B4 = Z.to_nat W_LEN).
  { rewrite <- EB4. apply oa_len_upd; [apply oa_len_upd; [exact LB3 | ..] | ..]; rewrite ?length_put; unfold W_LEN; lia. }
  assert (GF4 : g_fail_next B4 <= 1).
  { rewrite <- EB4. rewrite oa_gf_upd; [rewrite oa_gf_upd; [exact GF3 | exact LB3 | ..] | apply oa_len_upd; [exact LB3|..] | ..];
      rewrite ?length_put; unfold OFF_g_fail_next, W_LEN; lia. }
  assert (S4 : S_state B4 = 2).
  { rewrite <- EB4. unfold S_state, A_S_state. change (OFF_g_s + 112) with 1760.
    assert (L13 : length (upd B3 1816 (put 4 0)) = Z.to_nat W_LEN)
      by (apply oa_len_upd; [exact LB3 | lia | rewrite length_put; unfold W_LEN; lia]).
    rewrite s32_at_upd_out by (rewrite ?length_put, ?L13; unfold W_LEN; lia).
    rewrite s32_at_upd_out by (rewrite ?length_put, ?LB3; unfold W_LEN; lia).
    change (s32_at B3 1760) with (S_state B3). rewrite SF. exact S2. }
  rewrite EB4 in WMw.
  unfold session_lost_m, set_state_m in HM. fold B4 in HM. cbv zeta in HM.
  rewrite S4 in HM. change (2 =? DIGINET_S_IDLE) with false in HM. cbv beta iota in HM.
  (* memset (sp + 200, 0, 56) *)
  eapply evt_cut.
  { eapply HMEMSET; [rewrite !unsigned_lit by lia; exact R3z | exact MI]. }
  intros ms' PO. unfold memset_post in PO.
  destruct PO as (u0 & u1 & u2 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & u3 & u4 & u5 & u6 & m2 & -> & MU1 & WM1
                  & MI1 & RW1).
  rewrite !unsigned_lit in MU1, RW1 by lia.
  change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (Z_to_bv 8 0) in RW1.
  transport_after_call rsegs m1 m2 MU1 WM1. clear MU1 WM1 MI. try clear m1.
  rewrite (ret_pc_even 0x16970) by (first [lia | reflexivity]).
  do 9 step.
  change (u_at B4 1744 8) with (S_notify B4) in *.
  change (upd B4 1760 (put 4 0)) with (set_S_state B4 DIGINET_S_IDLE) in *.
  assert (SN : S_notify (set_S_state B4 DIGINET_S_IDLE) = S_notify B4).
  { unfold S_notify, set_S_state, A_S_notify, A_S_state. apply u_at_upd_out; rewrite ?length_put, ?LB4;
      unfold OFF_g_s, W_LEN; lia. }
  unfold call_notify in HM. rewrite SN in HM.
  destruct (Z.eqb_spec (S_notify B4) (ti_notice timg_plain)) as [EN|EN]; [|discriminate HM].
  change (ti_notice timg_plain) with 0x149e4 in EN. rewrite EN.
  destruct (notice_m timg_plain TF (set_S_state B4 DIGINET_S_IDLE) _) as [[B5 []]|] eqn:HN; [|discriminate HM].
  step.
  try rewrite (ret_pc_even 0x149e4) by (first [lia | reflexivity]).
  replace (bv_unsigned sp + -136) with (bv_unsigned sp + -152 + 16) in RW1 by lia.
  change (Z.to_nat 56) with 56%nat in RW1.
  assert (NT : ntc_at m (bv_unsigned sp + -152)
                 (Ntc DIGINET_N_STATE DIGINET_S_IDLE 2 DIGINET_R_DESK_OFFLINE 0 0 0 0 None [] 0)
                 (Z_to_bv 64 (bv_unsigned sp + -336)) 48).
  { apply oa_ntc_e0; [exact R3 | exact RW1 | lia | Z.div_mod_to_equations; lia | unfold off_world; lia
                     | unfold off_window; rewrite Hsp; lia | rewrite Hsp; lia]. }
  pose proof (oa_len_upd B4 (put 4 0) A_S_state LB4 ltac:(unfold A_S_state, OFF_g_s; lia)
                ltac:(rewrite length_put; unfold A_S_state, OFF_g_s, W_LEN; lia)) as LB4s.
  change (upd B4 A_S_state (put 4 0)) with (set_S_state B4 DIGINET_S_IDLE) in LB4s.
  assert (GF4s : g_fail_next (set_S_state B4 DIGINET_S_IDLE) <= 1).
  { unfold set_S_state, A_S_state. rewrite oa_gf_upd; [exact GF4 | exact LB4 | ..]; rewrite ?length_put;
      unfold OFF_g_fail_next, OFF_g_s, W_LEN; lia. }
  eapply evt_cut.
  { eapply HNOTICE with (p := bv_unsigned sp + -152) (Fr := TF) (lo := lo);
      [ reflexivity | exact NT
      | eapply oa_tframe; [exact TF0 | exact MU | rewrite Hsp; lia | rewrite Hsp; lia]
      | eapply oa_relro; [exact RI0 | exact MU | lia]
      | exact WMw0 | exact HN
      | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST | rewrite Hsp; lia
      | unfold w_off_stack; rewrite Hsp; lia | exact MI1 ]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & Eq & MUc & WMc & MI3 & ST3 & WM3).
  subst ms'. rewrite Hsp in MUc, ST3. clear WMw0.
  transport_after_call rsegs m m3 MUc WMc. clear MUc WMc MI1. try clear m.
  rewrite (ret_pc_even 0x16998) by (first [lia | reflexivity]).
  pose proof (fun H => oa_notice_fail _ _ _ _ _ LB4s H HN) as GF5. specialize (GF5 (or_intror (or_introl eq_refl))).
  rewrite <- GF5 in GF4s. clear GF5.
  (* lw a0, 112(s0) *)
  step.
  change (s32_at B5 1760) with (S_state B5) in *.
  apply oa_forget in R3. cbn [cells_size csize Nat.add] in R3.
  pose proof (oa_join _ _ (bv_unsigned sp + -152 + 16) _ _ R3 ltac:(cbn; lia) RW1) as R3'. clear R3 RW1.
  apply oa_forget in R3'. cbn [cells_size csize Nat.add] in R3'.
  eapply oa_e0w; [exact HM | exact WM3 | exact GF4s | exact R0 | exact R1 | exact R2 | exact R3' | exact R4
                 | exact ST3 | exact MU | exact WMO | exact MI3].
Qed.

(* 0x169d4: an e1 naming another host (diginet_session.c:215-220): foreign = 1, the FOREIGN notice, then a WAKING
   or ONLINE session is lost (session_lost and set_state inlined: the STATE notice) *)
Lemma oa_fg : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s1' s2' s3' s4' s5' s6' s7' s8' t3' t4' t5' t6' : word)
    (m : word -> option byte) (B2 : list byte) (off : Z) (aj J0 J1 J3 : list byte),
  off < 0 ->
  oa_rest_m timg_plain TF B2 DIGINET_CMD_ANNOUNCE_SESSION off (oa_ann (fr_body b)) now = Some (B', tt) ->
  wmem rsegs m B2 -> g_fail_next B2 <= 1 ->
  rw_cells rsegs m (bv_unsigned sp + -336) [CB 72 J0] ->
  rw_cells rsegs m (bv_unsigned sp + -264) [CB 72 J1] ->
  rw_cells rsegs m (bv_unsigned sp + -192) (ann_cells (buf + 30) (fr_body b) aj) ->
  rw_cells rsegs m (bv_unsigned sp + -152) [CB 72 J3] ->
  rw_cells rsegs m (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (bv_unsigned sp + -336) ->
  munch (oa_W sp) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  evt rsegs oa_Q
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -336)) gp tp t0' t1' t2' (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
             s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x169d4) fc None m (seg_rom rsegs)).
Proof.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s1' s2' s3' s4' s5' s6' s7' s8' t3' t4' t5' t6' m B2 off
    aj J0 J1 J3 Lo HM WM GF R0 R1 R2 R3 R4 ST MU WMO MI.
  oa_facts.
  pose proof (wm_len _ _ _ _ WM) as LB2.
  pose proof (s32_range B2 A_S_state) as Rst. change (s32_at B2 A_S_state) with (S_state B2) in Rst.
  unfold oa_rest_m in HM. change (DIGINET_CMD_ANNOUNCE_SESSION =? DIGINET_CMD_ANNOUNCE) with false in HM.
  rewrite (proj2 (Z.leb_gt 0 off) Lo) in HM. cbv beta iota zeta in HM.
  set (B3 := set_S_foreign B2 1) in *.
  assert (SF : S_state B3 = S_state B2).
  { unfold B3, S_state, set_S_foreign, A_S_state, A_S_foreign. apply s32_at_upd_out; rewrite ?length_put, ?LB2;
      unfold OFF_g_s, W_LEN; lia. }
  rewrite SF in HM.
  assert (LB3 : length B3 = Z.to_nat W_LEN).
  { unfold B3, set_S_foreign. apply oa_len_upd; [exact LB2 | ..]; rewrite ?length_put; unfold A_S_foreign, OFF_g_s, W_LEN; lia. }
  assert (GF3 : g_fail_next B3 <= 1).
  { unfold B3, set_S_foreign, A_S_foreign. rewrite oa_gf_upd; [exact GF | exact LB2 | ..]; rewrite ?length_put;
      unfold OFF_g_fail_next, OFF_g_s, W_LEN; lia. }
  pose proof (oa_ann_bytes _ _ _ _ _ R2) as [AV AN].
  do 14 step.
  change (s32_at B2 1760) with (S_state B2) in *.
  change (upd B2 1784 (put 4 1)) with B3 in WMw.
  (* memset (&n.personality, 0, 40): n at sp - 336, the 40 bytes from sp - 304 *)
  lazymatch type of R0 with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?R) =>
    change (c1 :: c2 :: c3 :: c4 :: c5 :: R) with ([c1; c2; c3; c4; c5] ++ R) in R0 end.
  apply oa_split with (B := bv_unsigned sp + -304) in R0; [|cbn; lia]. destruct R0 as [R0 R0z].
  eapply evt_cut.
  { eapply HMEMSET; [rewrite !unsigned_lit by lia; exact R0z | exact MI]. }
  intros ms' PO. unfold memset_post in PO.
  destruct PO as (u0 & u1 & u2 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & u3 & u4 & u5 & u6 & m2 & -> & MU1 & WM1
                  & MI1 & RW1).
  rewrite !unsigned_lit in MU1, RW1 by lia.
  change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (Z_to_bv 8 0) in RW1.
  change (Z.to_nat 40) with 40%nat in RW1.
  transport_after_call rsegs m m2 MU1 WM1. clear MU1 WM1 MI. try clear m.
  rewrite (ret_pc_even 0x16a0c) by (first [lia | reflexivity]).
  (* ld a2, 96(s0); ld a0, 104(s0); mv a1, sp; jalr a2 *)
  do 3 step.
  change (u_at B3 1744 8) with (S_notify B3) in *.
  unfold call_notify in HM.
  destruct (Z.eqb_spec (S_notify B3) (ti_notice timg_plain)) as [EN|EN]; [|discriminate HM].
  change (ti_notice timg_plain) with 0x149e4 in EN. rewrite EN.
  destruct (notice_m timg_plain TF B3 _) as [[B6 []]|] eqn:HN; [|discriminate HM].
  step.
  try rewrite (ret_pc_even 0x149e4) by (first [lia | reflexivity]).
  replace (bv_unsigned sp + -304) with (bv_unsigned sp + -336 + 32) in RW1 by lia.
  assert (NT : ntc_at m2 (bv_unsigned sp + -336)
                 (Ntc DIGINET_N_FOREIGN (S_state B2) 0 0 0 0 0 0 (Some (oa_ann (fr_body b))) [] 0)
                 (Z_to_bv 64 (bv_unsigned sp + -336)) 48).
  { eapply oa_ntc_fg; [exact R0 | exact RW1 | lia | lia | lia | Z.div_mod_to_equations; lia | unfold off_world; lia
                      | unfold off_window; rewrite Hsp; lia | rewrite Hsp; lia | lia | Z.div_mod_to_equations; lia
                      | exact AV | exact AN | unfold off_world; lia | unfold off_window; rewrite Hsp; lia]. }
  unfold ann_cells in R2. apply oa_forget in R2. cbn [cells_size csize Nat.add] in R2.
  eapply evt_cut.
  { eapply HNOTICE with (p := bv_unsigned sp + -336) (Fr := TF) (lo := lo);
      [ reflexivity | exact NT
      | eapply oa_tframe; [exact TF0 | exact MU | rewrite Hsp; lia | rewrite Hsp; lia]
      | eapply oa_relro; [exact RI0 | exact MU | lia]
      | exact WMw | exact HN
      | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST | rewrite Hsp; lia
      | unfold w_off_stack; rewrite Hsp; lia | exact MI1 ]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & Eq & MUc & WMc & MI3 & ST3 & WM3).
  subst ms'. rewrite Hsp in MUc, ST3. clear WMw.
  transport_after_call rsegs m2 m3 MUc WMc. clear MUc WMc MI1. try clear m2.
  rewrite (ret_pc_even 0x16a1c) by (first [lia | reflexivity]).
  pose proof (fun H => oa_notice_fail _ _ _ _ _ LB3 H HN) as GF5. specialize (GF5 (or_intror (or_intror eq_refl))).
  rewrite <- GF5 in GF3. clear GF5 NT AV AN.
  (* lw s1, 112(s0); addiw a0, s1, -1; bltu s3, a0 *)
  do 3 step.
  change (s32_at B6 1760) with (S_state B6) in *.
  pose proof (wm_len _ _ _ _ WM3) as LB6.
  pose proof (s32_range B6 A_S_state) as Rst6. change (s32_at B6 A_S_state) with (S_state B6) in Rst6.
  rewrite oa_fgcond by lia.
  destruct ((S_state B6 =? DIGINET_S_ONLINE) || (S_state B6 =? DIGINET_S_WAKING)) eqn:EL; cbn [negb]; cbv iota.
  2:{ (* neither WAKING nor ONLINE: return *)
    cbv beta iota in HM. injection HM as HE; subst.
    apply oa_forget in R0. cbn [cells_size csize Nat.add] in R0.
    pose proof (oa_join _ _ (bv_unsigned sp + -336 + 32) _ _ R0 ltac:(cbn; lia) RW1) as R0'. clear R0 RW1.
    apply oa_forget in R0'. cbn [cells_size csize Nat.add] in R0'.
    eapply oa_epi; [exact R0' | exact R1 | exact R2 | exact R3 | exact R4 | exact ST3 | exact MU | exact WMO
                   | exact MI3 | exact WM3 | exact GF3]. }
  cbv beta iota in HM.
  assert (Sst : S_state B6 = 1 \/ S_state B6 = 2).
  { apply orb_true_iff in EL. unfold DIGINET_S_ONLINE, DIGINET_S_WAKING in EL.
    destruct EL as [E|E]; apply Z.eqb_eq in E; lia. }
  (* session_lost inlined: dcv = 0, inflight = 0, then set_state (IDLE, FOREIGN) *)
  apply oa_cut with (k := 16%nat) in R3; [|lia]. destruct R3 as [R3 R3z]. change (Z.of_nat 16) with 16 in R3z.
  cbn [Nat.sub] in R3z. replace (bv_unsigned sp + -152 + 16) with (bv_unsigned sp + -136) in R3z by lia.
  do 6 step.
  set (B7 := set_S_desk_counter_valid (set_S_inflight B6 0) 0).
  assert (EB7 : upd (upd B6 1816 (put 4 0)) 1860 (put 4 0) = B7).
  { unfold B7, set_S_desk_counter_valid, set_S_inflight, A_S_desk_counter_valid, A_S_inflight.
    change (OFF_g_s + 168) with 1816. change (OFF_g_s + 212) with 1860.
    apply upd_upd_comm; rewrite ?length_put, ?LB6; unfold W_LEN; lia. }
  assert (LB7 : length B7 = Z.to_nat W_LEN).
  { rewrite <- EB7. apply oa_len_upd; [apply oa_len_upd; [exact LB6 | ..] | ..]; rewrite ?length_put; unfold W_LEN; lia. }
  assert (GF7 : g_fail_next B7 <= 1).
  { rewrite <- EB7. rewrite oa_gf_upd; [rewrite oa_gf_upd; [exact GF3 | exact LB6 | ..] | apply oa_len_upd; [exact LB6|..] | ..];
      rewrite ?length_put; unfold OFF_g_fail_next, W_LEN; lia. }
  assert (S7 : S_state B7 = S_state B6).
  { rewrite <- EB7. unfold S_state, A_S_state. change (OFF_g_s + 112) with 1760.
    assert (L13 : length (upd B6 1816 (put 4 0)) = Z.to_nat W_LEN)
      by (apply oa_len_upd; [exact LB6 | lia | rewrite length_put; unfold W_LEN; lia]).
    rewrite s32_at_upd_out by (rewrite ?length_put, ?L13; unfold W_LEN; lia).
    rewrite s32_at_upd_out by (rewrite ?length_put, ?LB6; unfold W_LEN; lia). reflexivity. }
  match goal with WMx : wmem rsegs _ (upd (upd B6 1816 (put 4 0)) 1860 (put 4 0)) |- _ => rewrite EB7 in WMx end.
  unfold session_lost_m, set_state_m in HM. fold B7 in HM. cbv zeta in HM.
  rewrite S7 in HM. replace (S_state B6 =? DIGINET_S_IDLE) with false in HM
    by (symmetry; apply Z.eqb_neq; unfold DIGINET_S_IDLE; lia). cbv beta iota in HM.
  (* memset (sp + 200, 0, 56) *)
  eapply evt_cut.
  { eapply HMEMSET; [rewrite !unsigned_lit by lia; exact R3z | eassumption]. }
  intros ms' PO. unfold memset_post in PO.
  destruct PO as (v0 & v1 & v2 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & v3 & v4 & v5 & v6 & m4 & -> & MU1 & WM1
                  & MI4 & RW4).
  rewrite !unsigned_lit in MU1, RW4 by lia.
  change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (Z_to_bv 8 0) in RW4.
  change (Z.to_nat 56) with 56%nat in RW4.
  oa_after MU1 WM1.
  rewrite (ret_pc_even 0x16a40) by (first [lia | reflexivity]).
  do 9 step.
  change (u_at B7 1744 8) with (S_notify B7) in *.
  change (upd B7 1760 (put 4 0)) with (set_S_state B7 DIGINET_S_IDLE) in *.
  assert (SN : S_notify (set_S_state B7 DIGINET_S_IDLE) = S_notify B7).
  { unfold S_notify, set_S_state, A_S_notify, A_S_state. apply u_at_upd_out; rewrite ?length_put, ?LB7;
      unfold OFF_g_s, W_LEN; lia. }
  unfold call_notify in HM. rewrite SN in HM.
  destruct (Z.eqb_spec (S_notify B7) (ti_notice timg_plain)) as [EN7|EN7]; [|discriminate HM].
  change (ti_notice timg_plain) with 0x149e4 in EN7. rewrite EN7.
  step.
  try rewrite (ret_pc_even 0x149e4) by (first [lia | reflexivity]).
  replace (bv_unsigned sp + -136) with (bv_unsigned sp + -152 + 16) in RW4 by lia.
  assert (NT : ntc_at m1 (bv_unsigned sp + -152)
                 (Ntc DIGINET_N_STATE DIGINET_S_IDLE (S_state B6) DIGINET_R_FOREIGN 0 0 0 0 None [] 0)
                 (Z_to_bv 64 (bv_unsigned sp + -336)) 48).
  { apply oa_ntc_fgst; [exact R3 | exact RW4 | lia | lia | Z.div_mod_to_equations; lia | unfold off_world; lia
                       | unfold off_window; rewrite Hsp; lia | rewrite Hsp; lia]. }
  pose proof (oa_len_upd B7 (put 4 0) A_S_state LB7 ltac:(unfold A_S_state, OFF_g_s; lia)
                ltac:(rewrite length_put; unfold A_S_state, OFF_g_s, W_LEN; lia)) as LB7s.
  change (upd B7 A_S_state (put 4 0)) with (set_S_state B7 DIGINET_S_IDLE) in LB7s.
  assert (GF7s : g_fail_next (set_S_state B7 DIGINET_S_IDLE) <= 1).
  { unfold set_S_state, A_S_state. rewrite oa_gf_upd; [exact GF7 | exact LB7 | ..]; rewrite ?length_put;
      unfold OFF_g_fail_next, OFF_g_s, W_LEN; lia. }
  eapply evt_cut.
  { eapply HNOTICE with (p := bv_unsigned sp + -152) (Fr := TF) (lo := lo) (B' := B');
      [ reflexivity | exact NT
      | eapply oa_tframe; [exact TF0 | exact MU | rewrite Hsp; lia | rewrite Hsp; lia]
      | eapply oa_relro; [exact RI0 | exact MU | lia]
      | exact WMw | exact HM
      | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST3 | rewrite Hsp; lia
      | unfold w_off_stack; rewrite Hsp; lia | exact MI4 ]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & Eq & MUc & WMc & MI5 & ST5 & WM5).
  subst ms'. rewrite Hsp in MUc, ST5. clear WMw.
  oa_after MUc WMc.
  rewrite (ret_pc_even 0x16a68) by (first [lia | reflexivity]).
  pose proof (fun H => oa_notice_fail _ _ _ _ _ LB7s H HM) as GF8. specialize (GF8 (or_intror (or_introl eq_refl))).
  rewrite <- GF8 in GF7s. clear GF8.
  step.
  apply oa_forget in R0. cbn [cells_size csize Nat.add] in R0.
  pose proof (oa_join _ _ (bv_unsigned sp + -336 + 32) _ _ R0 ltac:(cbn; lia) RW1) as R0'. clear R0 RW1.
  apply oa_forget in R0'. cbn [cells_size csize Nat.add] in R0'.
  apply oa_forget in R3. cbn [cells_size csize Nat.add] in R3.
  pose proof (oa_join _ _ (bv_unsigned sp + -152 + 16) _ _ R3 ltac:(cbn; lia) RW4) as R3'. clear R3 RW4.
  apply oa_forget in R3'. cbn [cells_size csize Nat.add] in R3'.
  eapply oa_epi; [exact R0' | exact R1 | exact R2 | exact R3' | exact R4 | exact ST5 | exact MU | exact WMO
                 | exact MI5 | exact WM5 | exact GF7s].
Qed.

Lemma oa_tail : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s6' s7' s8' t3' t4' t5' t6' : word)
    (m : word -> option byte) (B1 : list byte) (pv off : Z) (aj J0 J1 J3 : list byte),
  ann_code (fr_cmd b) (fr_body_len b) = 0 ->
  0 <= pv < 2^64 -> -2^31 <= off < 2^31 ->
  match call_notify timg_plain TF B1
          (Ntc DIGINET_N_DESK (S_state B1) 0 0 0 0 off pv (Some (oa_ann (fr_body b))) [] 0) with
  | None => None
  | Some (B2, _) => oa_rest_m timg_plain TF B2 (fr_cmd b) off (oa_ann (fr_body b)) now
  end = Some (B', tt) ->
  wmem rsegs m B1 -> g_fail_next B1 <= 1 ->
  rw_cells rsegs m (bv_unsigned sp + -336) [CB 72 J0] ->
  rw_cells rsegs m (bv_unsigned sp + -264) [CB 72 J1] ->
  rw_cells rsegs m (bv_unsigned sp + -192) (ann_cells (buf + 30) (fr_body b) aj) ->
  rw_cells rsegs m (bv_unsigned sp + -152) [CB 72 J3] ->
  rw_cells rsegs m (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells rsegs m fp (dframe_cells buf b fj) ->
  stk rsegs m lo (bv_unsigned sp + -336) ->
  munch (oa_W sp) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  evt rsegs oa_Q
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -336)) gp tp t0' t1' t2' (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
             (Z_to_bv 64 now) a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 fp) (Z_to_bv 64 pv) (Z_to_bv 64 off)
             s5' s6' s7' s8' s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x168f4) fc None m (seg_rom rsegs)).
Proof.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s6' s7' s8' t3' t4' t5' t6' m B1 pv off aj J0 J1 J3
    C0 Hpv Hoff HM WM GF R0 R1 R2 R3 R4 FRC ST MU WMO MI.
  oa_facts.
  unfold dframe_cells in FRC.
  pose proof (oa_cmd_ok _ _ C0) as [Ccmd Cblen].
  pose proof (oa_cmd_range b) as Rcmd.
  pose proof (oa_body_len b FC) as (BL0 & BL1 & BL2).
  pose proof (wm_len _ _ _ _ WM) as LB1.
  do 14 step.
  change (s32_at B1 1760) with (S_state B1) in *.
  pose proof (s32_range B1 A_S_state) as Rst. change (s32_at B1 A_S_state) with (S_state B1) in Rst.
  (* memset (&n.body, 0, 28): n is at sp - 264, the 28 bytes from sp - 220 *)
  lazymatch type of R1 with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?R) =>
    change (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: R) with ([c1; c2; c3; c4; c5; c6; c7] ++ R) in R1 end.
  apply oa_split with (B := bv_unsigned sp + -220) in R1; [|cbn; lia]. destruct R1 as [R1 R1z].
  eapply evt_cut.
  { eapply HMEMSET; [rewrite !unsigned_lit by lia; exact R1z | exact MI]. }
  intros ms' PO. unfold memset_post in PO.
  destruct PO as (u0 & u1 & u2 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & u3 & u4 & u5 & u6 & m2 & -> & MU1 & WM1
                  & MI1 & RW1).
  rewrite !unsigned_lit in MU1, RW1 by lia.
  change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (Z_to_bv 8 0) in RW1.
  transport_after_call rsegs m1 m2 MU1 WM1. clear MU1 WM1 MI. try clear m1.
  rewrite (ret_pc_even 0x1692c) by (first [lia | reflexivity]).
  do 3 step.
  change (u_at B1 1744 8) with (S_notify B1) in *.
  change (u_at B1 1752 8) with (S_notify_ctx B1) in *.
  unfold call_notify in HM.
  destruct (Z.eqb_spec (S_notify B1) (ti_notice timg_plain)) as [EN|EN]; [|discriminate HM].
  change (ti_notice timg_plain) with notice_ENTRY in EN. rewrite EN.
  destruct (notice_m timg_plain TF B1 _) as [[B2 []]|] eqn:HN; [|discriminate HM].
  step.
  unfold notice_ENTRY. rewrite (ret_pc_even 0x149e4) by (first [lia | reflexivity]).
  replace (bv_unsigned sp + -220) with (bv_unsigned sp + -264 + 44) in RW1 by lia.
  pose proof (oa_ann_bytes _ _ _ _ _ R2) as [AV AN].
  assert (NT : ntc_at m2 (bv_unsigned sp + -264)
                 (Ntc DIGINET_N_DESK (S_state B1) 0 0 0 0 off pv (Some (oa_ann (fr_body b))) [] 0)
                 (Z_to_bv 64 (bv_unsigned sp + -336)) 48).
  { eapply oa_ntc_desk; [exact R1 | exact RW1 | lia | lia | lia | lia | lia | .. ].
    - Z.div_mod_to_equations; lia.
    - unfold off_world; lia.
    - unfold off_window; rewrite Hsp; lia.
    - rewrite Hsp; lia.
    - lia.
    - Z.div_mod_to_equations; lia.
    - exact AV.
    - exact AN.
    - unfold off_world; lia.
    - unfold off_window; rewrite Hsp; lia. }
  eapply evt_cut.
  { eapply HNOTICE with (p := bv_unsigned sp + -264) (Fr := TF) (B := B1) (lo := lo);
      [ reflexivity | exact NT
      | eapply oa_tframe; [exact TF0 | exact MU | rewrite Hsp; lia | rewrite Hsp; lia]
      | eapply oa_relro; [exact RI0 | exact MU | lia]
      | exact WM | exact HN
      | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST | rewrite Hsp; lia
      | unfold w_off_stack; rewrite Hsp; lia | exact MI1 ]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & Eq & MUc & WMc & MI3 & ST3 & WM3).
  subst ms'. rewrite Hsp in MUc, ST3. clear WM.
  transport_after_call rsegs m2 m3 MUc WMc. clear MUc WMc MI1. try clear m2.
  rewrite (ret_pc_even 0x1693c) by (first [lia | reflexivity]).
  pose proof (fun H => oa_notice_fail _ _ _ _ _ LB1 H HN) as GF2. specialize (GF2 (or_introl eq_refl)).
  rewrite <- GF2 in GF. clear GF2. clear NT AV AN.
  step.
  rewrite (oa_zxb (fr_cmd b)) by lia.
  (* the two R1 pieces and the announce, as plain blocks for the branches *)
  pose proof (oa_join _ _ (bv_unsigned sp + -264 + 44) _ _ R1 ltac:(cbn; lia) RW1) as R1'. clear R1 RW1.
  apply oa_forget in R1'. cbn [cells_size csize Nat.add cells_bytes cbytes app] in R1'.
  destruct Ccmd as [Ce|Ce]; rewrite Ce in HM |- *.
  - (* e0: li a1, 224; bne falls through *)
    step. step. unfold DIGINET_CMD_ANNOUNCE. if_false.
    apply oa_forget in R2. cbn [cells_size csize Nat.add] in R2.
    eapply oa_e0; [exact HM | exact WM3 | exact GF | exact R0 | exact R1' | exact R2 | exact R3 | exact R4
                  | exact ST3 | exact MU | exact WMO | exact MI3].
  - (* e1: li a1, 224; bne to 0x169b8 *)
    step. step. unfold DIGINET_CMD_ANNOUNCE_SESSION. if_true.
    (* bltz s4 *)
    step. rewrite oa_ltz by lia.
    destruct (Z.ltb_spec off 0) as [Lo|Lo]; cbv iota.
    + eapply oa_fg; [exact Lo | exact HM | exact WM3 | exact GF | exact R0 | exact R1' | exact R2 | exact R3
                    | exact R4 | exact ST3 | exact MU | exact WMO | exact MI3].
    + (* the e1 names this host: foreign = 0, e1_named_us = 1 (one sd of 1 << 32), maybe_online *)
      unfold oa_rest_m in HM. change (225 =? DIGINET_CMD_ANNOUNCE) with false in HM.
      rewrite (proj2 (Z.leb_le 0 off) Lo) in HM. cbv beta iota zeta in HM.
      pose proof (wm_len _ _ _ _ WM3) as LB2.
      do 3 step.
      assert (EB : upd B2 1784 (put 8 4294967296) = set_S_e1_named_us (set_S_foreign B2 0) 1).
      { unfold set_S_e1_named_us, set_S_foreign, A_S_e1_named_us, A_S_foreign. change (OFF_g_s + 140) with 1788.
        change (OFF_g_s + 136) with 1784. rewrite oa_put8_e1.
        rewrite oa_upd_app; [reflexivity | lia | rewrite LB2; rewrite !length_put; unfold W_LEN; lia]. }
      rewrite EB in WMw. clear EB.
      assert (GF3 : g_fail_next (set_S_e1_named_us (set_S_foreign B2 0) 1) <= 1).
      { unfold set_S_e1_named_us, set_S_foreign, A_S_e1_named_us, A_S_foreign.
        rewrite oa_gf_upd; [rewrite oa_gf_upd; [exact GF | exact LB2 | ..] | apply oa_len_upd; [exact LB2 | ..] | ..];
          rewrite ?length_put; unfold OFF_g_fail_next, W_LEN; lia. }
      do 2 step.
      eapply evt_cut.
      { eapply HMAYBE with (lo := lo) (TF := TF);
          [ reflexivity | exact WMw | exact GF3 | exact HM
          | eapply oa_tframe; [exact TF0 | exact MU | rewrite Hsp; lia | rewrite Hsp; lia]
          | eapply oa_relro; [exact RI0 | exact MU | lia]
          | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST3 | rewrite Hsp; lia
          | unfold w_off_stack; rewrite Hsp; lia | exact MI3 ]. }
      intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & Eq & MUc & WMc & MI4 & ST4 & WM4
                  & GF4).
      subst ms'. rewrite Hsp in MUc, ST4. clear WMw.
      transport_after_call rsegs m m4 MUc WMc. clear MUc WMc MI3. try clear m.
      rewrite (ret_pc_even 0x169d0) by (first [lia | reflexivity]).
      step.
      apply oa_forget in R2. cbn [cells_size csize Nat.add] in R2.
      eapply oa_epi; [exact R0 | exact R1' | exact R2 | exact R3 | exact R4 | exact ST4 | exact MU | exact WMO
                     | exact MI4 | exact WM4 | exact GF4].
Qed.

(* 0x168c8: find_mac's loop (diginet_session.c:170-172), i = s8, s6 = i + 6, s5 = unknown_len = 15, s7 = unknown *)
Lemma oa_loop : forall (fuel : nat) (i : Z)
    (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
    (m : word -> option byte) (B1 : list byte) (pv : Z) (aj J0 J1 J3 : list byte),
  0 <= i -> i + Z.of_nat (S fuel) = 10 ->
  ann_code (fr_cmd b) (fr_body_len b) = 0 ->
  0 <= pv < 2^64 ->
  match call_notify timg_plain TF B1
          (Ntc DIGINET_N_DESK (S_state B1) 0 0 0 0
             (find_mac_loop (ann_unknown (fr_body b)) (S_cfg_host_mac B1) i (S fuel)) pv
             (Some (oa_ann (fr_body b))) [] 0) with
  | None => None
  | Some (B2, _) => oa_rest_m timg_plain TF B2 (fr_cmd b)
                      (find_mac_loop (ann_unknown (fr_body b)) (S_cfg_host_mac B1) i (S fuel))
                      (oa_ann (fr_body b)) now
  end = Some (B', tt) ->
  wmem rsegs m B1 -> g_fail_next B1 <= 1 ->
  rw_cells rsegs m (bv_unsigned sp + -336) [CB 72 J0] ->
  rw_cells rsegs m (bv_unsigned sp + -264) [CB 72 J1] ->
  rw_cells rsegs m (bv_unsigned sp + -192) (ann_cells (buf + 30) (fr_body b) aj) ->
  rw_cells rsegs m (bv_unsigned sp + -152) [CB 72 J3] ->
  rw_cells rsegs m (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells rsegs m fp (dframe_cells buf b fj) ->
  bytes_at rsegs m (buf + 30) (fr_body b) ->
  stk rsegs m lo (bv_unsigned sp + -336) ->
  munch (oa_W sp) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  evt rsegs oa_Q
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -336)) gp tp t0' t1' t2' (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
             (Z_to_bv 64 now) a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 fp) (Z_to_bv 64 pv) (Z_to_bv 64 (-1))
             (Z_to_bv 64 15) (Z_to_bv 64 (i + 6)) (Z_to_bv 64 (buf + 30)) (Z_to_bv 64 i) s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x168c8) fc None m (seg_rom rsegs)).
Proof.
  induction fuel as [|fuel IH]; intros i ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m B1 pv
    aj J0 J1 J3 Hi Hf C0 Hpv HM WM GF R0 R1 R2 R3 R4 FRC BB ST MU WMO MI.
  all: oa_facts.
  all: pose proof (oa_cmd_ok _ _ C0) as [Ccmd Cblen].
  all: pose proof (oa_body_len b FC) as (BL0 & BL1 & BL2).
  all: assert (LS : bytes_at rsegs m (buf + 30 + i) (firstn 6 (skipn (Z.to_nat i) (fr_body b))))
         by (replace (buf + 30 + i) with (buf + 30 + Z.of_nat (Z.to_nat i)) by lia;
             apply oa_bytes_sub; [exact BB | lia]).
  all: assert (RS : bytes_at rsegs m (W_BASE_PLAIN + OFF_g_s) (S_cfg_host_mac B1))
         by (unfold S_cfg_host_mac, A_S_cfg_host_mac; apply (wm_src rsegs W_BASE_PLAIN m B1 (OFF_g_s + 0 + 0));
             [exact WM | lia | lia | unfold OFF_g_s, W_LEN; cbn; lia]).
  all: assert (LRS : length (S_cfg_host_mac B1) = 6%nat)
         by (unfold S_cfg_host_mac; apply length_sub; [unfold A_S_cfg_host_mac; lia |
             rewrite (wm_len _ _ _ _ WM); unfold A_S_cfg_host_mac, OFF_g_s, W_LEN; cbn; lia]).
  all: assert (LLS : length (firstn 6 (skipn (Z.to_nat i) (fr_body b))) = 6%nat)
         by (rewrite length_firstn, length_skipn; lia).
  all: destruct (memcmp_model_total (firstn 6 (skipn (Z.to_nat i) (fr_body b))) (S_cfg_host_mac B1) 6
                   ltac:(lia) ltac:(lia)) as [v Hv].
  all: pose proof (oa_memcmp_range _ _ _ _ Hv) as Rv.
  all: pose proof (fun H1 H2 => oa_memcmp6 _ _ _ H1 H2 Hv) as Ev.
  all: specialize (Ev ltac:(lia) ltac:(lia)).
  all: rewrite <- (oa_unknown_at (fr_body b) i) in Ev by lia.
  all: rewrite oa_memeq6 in Ev.
  all: do 5 step.
  all: eapply evt_cut; [eapply HBCMP with (ls := firstn 6 (skipn (Z.to_nat i) (fr_body b))) (rs := S_cfg_host_mac B1)
                          (v := v);
                         [ rewrite unsigned_lit by lia; replace (buf + 30 + (i + 6) + -6) with (buf + 30 + i) by lia;
                           exact LS
                         | rewrite unsigned_lit by lia; exact RS
                         | rewrite unsigned_lit by lia; exact Hv
                         | exact MI ] |].
  all: intros ms' PO; unfold memcmp_post in PO;
       destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m' & -> & MU1 & WM1
                       & MI1 & _ & _).
  all: oa_after MU1 WM1.
  all: rewrite (ret_pc_even 0x168dc) by (first [lia | reflexivity]).
  all: step.
  all: rewrite oa_eqb0 by lia.
  all: rewrite oa_find_mac_S in HM.
  all: destruct (Z.eqb_spec v 0) as [V0|V0]; cbv iota.
  1,3: (* the 6 bytes at i are the host's MAC: found at i *)
       rewrite <- Ev in HM; cbv iota in HM;
       step;
       eapply oa_tail; [exact C0 | exact Hpv | lia | exact HM | exact WM | exact GF | exact R0 | exact R1 | exact R2
                       | exact R3 | exact R4 | exact FRC | exact ST | exact MU | exact WMO | exact MI1].
  all: rewrite <- Ev in HM; cbv iota in HM.
  all: do 3 step.
  all: unfold bv_ltu; rewrite !unsigned_lit by lia.
  - (* i = 9: the last offset; not found *)
    replace (15 <? i + 7) with true by (symmetry; apply Z.ltb_lt; cbn in Hf; lia). cbn [negb]; cbv iota.
    cbn [find_mac_loop] in HM.
    step.
    eapply oa_tail; [exact C0 | exact Hpv | lia | exact HM | exact WM | exact GF | exact R0 | exact R1 | exact R2
                    | exact R3 | exact R4 | exact FRC | exact ST | exact MU | exact WMO | exact MI1].
  - (* the next offset *)
    replace (15 <? i + 7) with false by (symmetry; apply Z.ltb_ge; rewrite Nat2Z.inj_succ in Hf; lia).
    cbn [negb]; cbv iota.
    try rewrite unsigned_lit by lia. rewrite (oa_swrap_small (i + 1)) by lia.
    replace (i + 7) with (i + 1 + 6) by lia.
    eapply IH; [lia | rewrite Nat2Z.inj_succ in Hf; lia | exact C0 | exact Hpv | exact HM | exact WM | exact GF
               | exact R0 | exact R1 | exact R2 | exact R3 | exact R4 | exact FRC | exact BB | exact ST | exact MU
               | exact WMO | exact MI1].
Qed.


(* 0x168a4: diginet_session.c:194, find_mac for an e1 (its loop is oa_loop), then the DESK notice (oa_tail) *)
Lemma oa_seg : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s7' s8' t3' t4' t5' t6' : word)
    (m : word -> option byte) (B1 : list byte) (pv : Z) (aj J0 J1 J3 : list byte),
  ann_code (fr_cmd b) (fr_body_len b) = 0 ->
  0 <= pv < 2^64 ->
  (let off := if fr_cmd b =? DIGINET_CMD_ANNOUNCE_SESSION
              then find_mac_m (ann_unknown (fr_body b)) 15 (S_cfg_host_mac B1) else -1 in
   match call_notify timg_plain TF B1
           (Ntc DIGINET_N_DESK (S_state B1) 0 0 0 0 off pv (Some (oa_ann (fr_body b))) [] 0) with
   | None => None
   | Some (B2, _) => oa_rest_m timg_plain TF B2 (fr_cmd b) off (oa_ann (fr_body b)) now
   end) = Some (B', tt) ->
  wmem rsegs m B1 -> g_fail_next B1 <= 1 ->
  rw_cells rsegs m (bv_unsigned sp + -336) [CB 72 J0] ->
  rw_cells rsegs m (bv_unsigned sp + -264) [CB 72 J1] ->
  rw_cells rsegs m (bv_unsigned sp + -192) (ann_cells (buf + 30) (fr_body b) aj) ->
  rw_cells rsegs m (bv_unsigned sp + -152) [CB 72 J3] ->
  rw_cells rsegs m (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells rsegs m fp (dframe_cells buf b fj) ->
  bytes_at rsegs m (buf + 30) (fr_body b) ->
  stk rsegs m lo (bv_unsigned sp + -336) ->
  munch (oa_W sp) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  evt rsegs oa_Q
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -336)) gp tp t0' t1' t2' (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
             (Z_to_bv 64 now) a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 fp) (Z_to_bv 64 pv)
             s4' s5' s6' s7' s8' s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x168a4) fc None m (seg_rom rsegs)).
Proof.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s7' s8' t3' t4' t5' t6' m B1 pv aj J0 J1 J3
    C0 Hpv HM WM GF R0 R1 R2 R3 R4 FRC BB ST MU WMO MI.
  oa_facts.
  pose proof (oa_cmd_ok _ _ C0) as [Ccmd Cblen].
  pose proof (oa_cmd_range b) as Rcmd.
  pose proof FRC as FRC0. unfold dframe_cells in FRC.
  (* lbu a0, 30(s2); li a1, 225; li s4, -1; bne a0, a1 *)
  do 4 step.
  rewrite (oa_zxb (fr_cmd b)) by lia.
  rewrite oa_eqb by lia.
  cbv zeta in HM. unfold DIGINET_CMD_ANNOUNCE_SESSION in HM.
  destruct (Z.eqb_spec (fr_cmd b) 225) as [E1|E1]; cbn [negb]; cbv iota.
  2:{ (* not an e1: no find_mac, off = -1 *)
    cbv iota in HM.
    eapply oa_tail; [exact C0 | exact Hpv | lia | exact HM | exact WM | exact GF | exact R0 | exact R1 | exact R2
                    | exact R3 | exact R4 | exact FRC0 | exact ST | exact MU | exact WMO | exact MI]. }
  cbv iota in HM. unfold find_mac_m in HM. change (Z.to_nat (15 - DIGINET_MAC_LEN + 1)) with 10%nat in HM.
  pose proof R2 as R2a. unfold ann_cells in R2.
  (* ld s5, 176(sp) (unknown_len = 15); li s6, 6; bltu s5, s6 *)
  do 3 step. if_false.
  (* ld s7, 168(sp) (unknown = body); li s8, 0 *)
  do 2 step.
  clear R2. rename R2a into R2.
  eapply (oa_loop 9 0); [lia | reflexivity | exact C0 | exact Hpv | exact HM | exact WM | exact GF | exact R0 | exact R1
                        | exact R2 | exact R3 | exact R4 | exact FRC0 | exact BB | exact ST | exact MU | exact WMO
                        | exact MI].
Qed.

(* 0x16804: the prologue, diginet_announce_parse (:187) and its failure (:188-189), diginet_personality_from_name
   (:191-193), then oa_seg *)
Lemma oa_main : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (B : list byte),
  wmem rsegs m0 B -> g_fail_next B <= 1 -> on_announce_m timg_plain TF B b now = Some (B', tt) ->
  bytes_at rsegs m0 buf b -> rw_cells rsegs m0 fp (dframe_cells buf b fj) ->
  stk rsegs m0 lo (bv_unsigned sp) -> mem_inv rsegs m0 ->
  evt rsegs oa_Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) (Z_to_bv 64 fp) (Z_to_bv 64 now)
             a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16804) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 B WM GF HM BB FRC ST MI.
  oa_facts.
  pose proof (wm_len _ _ _ _ WM) as LB.
  unfold dframe_cells in FRC.
  pose proof ST as (Hlo0 & _ & _).
  pose proof (munch_refl [(bv_unsigned sp - 1184, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m0) as MU.
  pose proof (wmono_refl rsegs m0) as WMO.
  pose proof (oa_body_len b FC) as (BL0 & BL1 & BL2).
  pose proof (oa_cmd_range b) as Rcmd.
  carve_frame 336%nat ST.
  (* addi sp, sp, -336; sd ra, s0-s8 *)
  do 11 step.
  lazymatch goal with FR : rw_cells _ _ (bv_unsigned sp + -336) (CB 256 ?J :: ?R) |- _ =>
    set (Jf := J) in FR; clearbody Jf;
    change (CB 256 Jf :: R) with ([CB 256 Jf] ++ R) in FR;
    apply oa_split with (B := bv_unsigned sp + -80) in FR; [|cbn; lia];
    destruct FR as [FRL R4] end.
  apply oa_cut with (k := 72%nat) in FRL; [|lia]. destruct FRL as [R0 FRL]. change (Z.of_nat 72) with 72 in FRL.
  cbn [Nat.sub] in FRL.
  apply oa_cut with (k := 72%nat) in FRL; [|lia]. destruct FRL as [R1 FRL]. change (Z.of_nat 72) with 72 in FRL.
  cbn [Nat.sub] in FRL.
  apply oa_cut with (k := 40%nat) in FRL; [|lia]. destruct FRL as [R2 R3]. change (Z.of_nat 40) with 40 in R3.
  cbn [Nat.sub] in R3.
  replace (bv_unsigned sp + -336 + 72) with (bv_unsigned sp + -264) in R1 by lia.
  replace (bv_unsigned sp + -336 + 72 + 72) with (bv_unsigned sp + -192) in R2 by lia.
  replace (bv_unsigned sp + -336 + 72 + 72 + 40) with (bv_unsigned sp + -152) in R3 by lia.
  lazymatch type of R0 with rw_cells _ _ _ [CB _ ?J] => set (J0 := J) in R0; clearbody J0 end.
  lazymatch type of R1 with rw_cells _ _ _ [CB _ ?J] => set (J1 := J) in R1; clearbody J1 end.
  lazymatch type of R2 with rw_cells _ _ _ [CB _ ?J] => set (aj := J) in R2; clearbody aj end.
  lazymatch type of R3 with rw_cells _ _ _ [CB _ ?J] => set (J3 := J) in R3; clearbody J3 end.
  clear Jf.
  (* what diginet_announce_parse reads of the frame *)
  assert (Hcmd : bytes_at rsegs m1 (fp + 30) [DgnSpec.b8 (fr_cmd b)])
    by exact (oa_cell_bytes m1 fp _ 30 _ FRC eq_refl).
  assert (Hbl : bytes_at rsegs m1 (fp + 32)
                  (le8 (Z_to_bv 64 (buf + 30)) ++ le8 (Z_to_bv 64 (Z.of_nat (length (fr_body b)))))).
  { apply bytes_at_app. split.
    - exact (oa_cell_bytes m1 fp _ 32 _ FRC eq_refl).
    - rewrite length_le8. rewrite BL2, Z2Nat.id by lia.
      replace (fp + 32 + Z.of_nat 8) with (fp + Z.of_nat 40) by lia.
      exact (oa_cell_bytes m1 fp _ 40 _ FRC eq_refl). }
  assert (Hbb : bytes_at rsegs m1 (buf + 30) (fr_body b)).
  { unfold fr_body. change (buf + 30) with (buf + Z.of_nat 30). apply oa_bytes_sub; [exact BB|]. lia. }
  (* mv s1, a2; mv s2, a1; mv s0, a0; addi a1, sp, 144; mv a0, s2; jal diginet_announce_parse *)
  do 6 step.
  eapply evt_cut.
  { eapply HPARSE with (f := fp) (ap := bv_unsigned sp + -192) (cmd := fr_cmd b) (body := buf + 30)
      (bb := fr_body b) (aj := aj);
      [ lia | lia | exact Rcmd | lia | exact Hcmd | exact Hbl | exact Hbb | exact R2 | lia
      | rewrite BL2, Z2Nat.id by lia; lia | exact MI ]. }
  intros ms' (a1' & a2' & a3' & a4' & a5' & a6' & m2 & -> & MUc & WMc & MI2 & R2').
  oa_after MUc WMc.
  rewrite (ret_pc_even 92232) by (first [lia | reflexivity]).
  rewrite BL2, Z2Nat.id in R2' |- * by lia.
  assert (Rcode : -9 <= ann_code (fr_cmd b) (fr_body_len b) <= 0)
    by (unfold ann_code; destruct (negb _); [lia|]; destruct (_ <? 33); lia).
  rewrite oa_unfold in HM.
  (* beqz a0 *)
  step.
  rewrite oa_eqb0 by lia.
  unfold DIGINET_OK in HM.
  destruct (Z.eqb_spec (ann_code (fr_cmd b) (fr_body_len b)) 0) as [C0|C0]; cbv iota.
  2:{ (* the parse failed: stats.rx_ignored++ (:188-189) and return *)
    cbv beta iota delta [negb] in HM. injection HM as HE.
    do 5 step.
    change (u_at B 19832 8) with (S_stats_rx_ignored B) in *.
    lazymatch goal with WMx : wmem rsegs ?mm (upd B 19832 _) |- _ => rename mm into mf; rename WMx into WMf end.
    assert (WM' : wmem rsegs mf B').
    { rewrite <- HE. unfold set_S_stats_rx_ignored, u64, A_S_stats_rx_ignored. rewrite put_mod64 by lia.
      exact WMf. }
    assert (GF' : g_fail_next B' <= 1).
    { rewrite <- HE. unfold set_S_stats_rx_ignored, A_S_stats_rx_ignored. rewrite oa_gf_upd; [exact GF | exact LB | ..];
        rewrite ?length_put; unfold OFF_g_fail_next, OFF_g_s, W_LEN; lia. }
    eapply oa_epi; [exact R0 | exact R1 | exact R2' | exact R3 | exact R4 | exact ST | exact MU | exact WMO
                   | exact MI2 | exact WM' | exact GF']. }
  cbv beta iota delta [negb] in HM. cbv zeta in HM.
  (* addi a0, sp, 154 (a.name); jal diginet_personality_from_name *)
  do 2 step.
  destruct (stk_split rsegs m2 lo (bv_unsigned sp + -384) (bv_unsigned sp + -336) ST ltac:(lia)) as [STlo SThi].
  clear ST.
  pose proof (oa_cell_bytes m2 _ _ 10 _ R2' eq_refl) as NM. cbn [cbytes] in NM. change (Z.of_nat 10) with 10 in NM.
  eapply evt_cut.
  { eapply HPFN with (lo := bv_unsigned sp + -384) (tb := ann_name (fr_body b) (firstn 10 (skipn 10 aj))).
    unfold diginet_personality_from_name_pre.
    rewrite Hsp, unsigned_lit by lia.
    split; [lia|]. split; [split; [replace (bv_unsigned sp + -182) with (bv_unsigned sp + -192 + 10) by lia;
                                   exact NM | apply oa_name_nul]|].
    split; [right; lia|]. split; [exact (oa_relro m0 m2 sp RI0 MU WO)|].
    split; [unfold disj, codec_cells.RELRO_BASE, codec_cells.RELRO_LEN; lia|].
    split; [exact MI2|]. split; [exact SThi | unfold DIGINET_PERSONALITY_FROM_NAME_DEPTH; lia]. }
  intros ms' (a1'' & a2'' & a3'' & m3 & -> & MUc & WMc & MI3 & ST3).
  rewrite Hsp in MUc, ST3.
  oa_after MUc WMc.
  pose proof (stk_merge rsegs m3 lo (bv_unsigned sp + -384) (bv_unsigned sp + -336) STlo ST3 ltac:(lia)) as ST.
  clear STlo ST3.
  rewrite (ret_pc_even 92312) by (first [lia | reflexivity]).
  rewrite oa_from_name.
  change (ti_personalities timg_plain) with PERS in HM.
  (* mv s3, a0; beqz a0; sd s3, 128(s0) (s->personality) *)
  destruct (TNeed.diginet_personality_from_name _) as [i|] eqn:Ep; cbv iota in HM.
  - pose proof (oa_pfn_range _ _ Ep) as Ri.
    do 2 step.
    rewrite oa_eqb0 by (unfold PERS; lia).
    replace (PERS + 24 * i =? 0) with false by (symmetry; apply Z.eqb_neq; unfold PERS; lia). cbv iota.
    step.
    change (upd B 1776 (put 8 (PERS + 24 * i))) with (set_S_personality B (PERS + 24 * i)) in *.
    assert (GF1 : g_fail_next (set_S_personality B (PERS + 24 * i)) <= 1).
    { unfold set_S_personality, A_S_personality. rewrite oa_gf_upd; [exact GF | exact LB | ..];
        rewrite ?length_put; unfold OFF_g_fail_next, OFF_g_s, W_LEN; lia. }
    eapply oa_seg; [exact C0 | unfold PERS; lia | exact HM | exact WMw | exact GF1 | exact R0 | exact R1 | exact R2'
                   | exact R3 | exact R4 | exact FRC | exact Hbb | exact ST | exact MU | exact WMO | exact MI3].
  - do 2 step.
    rewrite oa_eqb0 by lia. cbv iota.
    eapply oa_seg; [exact C0 | lia | exact HM | exact WM | exact GF | exact R0 | exact R1 | exact R2'
                   | exact R3 | exact R4 | exact FRC | exact Hbb | exact ST | exact MU | exact WMO | exact MI3].
Qed.

End OnAnnounce.

Theorem on_announce_holds :
  bcmp_contract -> memset_contract -> diginet_announce_parse_contract -> diginet_personality_from_name_contract ->
  diginet_session_wake_contract -> maybe_online_contract -> notice_contract ->
  on_announce_contract.
Proof.
  intros HB HMS HP HPF HW HMO HN.
  unfold on_announce_contract, on_announce_ENTRY, on_announce_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo fp buf now b fj B B' TF A0 A1 A2 Hnow DF WM GF HM TFa RI SP16 ST LO WO MI.
  subst a0 a1 a2.
  destruct DF as (FC & BB & (Pbuf & Lbuf & OWbuf & OSbuf) & FRC & (Pfp & Lfp & OWfp & OSfp) & Afp).
  unfold off_world, off_window in OWbuf, OSbuf, OWfp, OSfp. unfold w_off_stack in WO.
  pose proof ST as (Hlo & _ & _).
  eapply oa_main with (m0 := m) (lo := lo) (fp := fp) (buf := buf) (now := now) (b := b) (fj := fj) (B' := B')
    (TF := TF) (B := B).
  all: match goal with |- ?T => match goal with H : T |- _ => exact H end end.
Qed.
