(* check_inflight_acked (fuzz/fuzz_transport.c:476-484), entry 0x15ed0, 18 instructions:
     0x15ed0 auipc a1,0x2d / addi a1,a1,504   a1 = &g_fail_next = W_BASE_UBSAN + OFF_g_fail_next
     0x15ed8 lw a2,332(a1)                     GOT.acked
     0x15edc lw a3,560(a1)                     OW.acked
     0x15ee0 blt a3,a2,0x15f08                 abort when OW.acked < GOT.acked
     0x15ee4 andi a2,a0,7
     0x15ee8 bnez a2,0x15f14                   UBSan trap (unimp) when n is not 8-aligned
     0x15eec lw a2,64(a0)                      n->counter
     0x15ef0 lw a3,568(a1)                     OW.acked_counter
     0x15ef4 bne a2,a3,0x15f08                 abort
     0x15ef8 lhu a0,68(a0)                     n->retry
     0x15efc lw a1,572(a1)                     OW.acked_retry
     0x15f00 bne a1,a0,0x15f08                 abort
     0x15f04 ret
     0x15f08 addi sp,sp,-16 / sd ra,8(sp) / jal abort; 0x15f14 unimp
   The model premise check_inflight_acked_m B n = Some (B', tt) makes each of the three abort branches
   contradictory, and ntc_at's 8-alignment of n the trap branch (all closed by exfalso); the path that returns
   reads only, so memory is unchanged.
   The world fields are moved to the literal offsets the loads compute (65300, 65528, 65536, 65540) by rewriting
   with cia_got / cia_ow / cia_owc / cia_owr, not by `change` (in the plain walk, a lemma that did
   `change (OW_acked B) with (s32_at B 65528)` and the three others exhausted 24 GB at its Qed). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract check_inflight_acked_c.
Import ListNotations.
Open Scope Z_scope.

(* blt on two sign-extended 32-bit values is the signed comparison of the values *)
Lemma cia_lts : forall x y, -2^31 <= x < 2^31 -> -2^31 <= y < 2^31 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !Z_to_bv_signed.
  assert (H : bv_half_modulus 64 = 9223372036854775808) by reflexivity.
  rewrite !bv_swrap_small by (rewrite H; lia). reflexivity.
Qed.

(* the model premise (TCb.v check_inflight_acked_m) as the facts the three abort branches test *)
Lemma cia_model : forall B n B',
  check_inflight_acked_m B n = Some (B', tt) ->
  GOT_acked B <= OW_acked B /\ n_counter n = OW_acked_counter B /\ n_retry n = OW_acked_retry B /\ B' = B.
Proof.
  intros B n B' HM. unfold check_inflight_acked_m in HM.
  destruct (OW_acked B <? GOT_acked B) eqn:E1; cbv beta iota delta [negb orb] in HM; [discriminate HM|].
  destruct (n_counter n =? OW_acked_counter B) eqn:E2; cbv beta iota delta [negb orb] in HM; [|discriminate HM].
  destruct (n_retry n =? OW_acked_retry B) eqn:E3; cbv beta iota delta [negb orb] in HM; [|discriminate HM].
  injection HM as HB. subst B'.
  apply Z.ltb_ge in E1. apply Z.eqb_eq in E2. apply Z.eqb_eq in E3.
  split; [exact E1|]. split; [exact E2|]. split; [exact E3 | reflexivity].
Qed.

(* the world fields at the offsets the loads compute (TWorld.v: OFF_GOT = 0xfe3c, OFF_OW = 0xff20) *)
Lemma cia_got : forall B, s32_at B 65300 = GOT_acked B.
Proof.
  intros B. unfold GOT_acked, A_GOT_acked, OFF_GOT.
  replace (65084 + 216) with 65300 by reflexivity. reflexivity.
Qed.
Lemma cia_ow : forall B, s32_at B 65528 = OW_acked B.
Proof.
  intros B. unfold OW_acked, A_OW_acked, OFF_OW.
  replace (65312 + 216) with 65528 by reflexivity. reflexivity.
Qed.
Lemma cia_owc : forall B, u_at B 65536 4 = OW_acked_counter B.
Proof.
  intros B. unfold OW_acked_counter, A_OW_acked_counter, OFF_OW.
  replace (65312 + 224) with 65536 by reflexivity. reflexivity.
Qed.
Lemma cia_owr : forall B, u_at B 65540 4 = OW_acked_retry B.
Proof.
  intros B. unfold OW_acked_retry, A_OW_acked_retry, OFF_OW.
  replace (65312 + 228) with 65540 by reflexivity. reflexivity.
Qed.

(* the branch at the head of the goal: its taken side is the abort (or trap) path, closed by exfalso *)
Ltac cia_branch :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let E := fresh "BR" in destruct c eqn:E; cbv iota; [exfalso | clear E]
  end.

Theorem check_inflight_acked_holds : check_inflight_acked_contract.
Proof.
  unfold check_inflight_acked_contract, check_inflight_acked_ENTRY, check_inflight_acked_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo B B' p n -> NT WM HM SP16 ST LO WOS MI.
  destruct (cia_model B n B' HM) as (M1 & CTR & RTY & ->). clear HM.
  rewrite <- cia_got, <- cia_ow in M1. rewrite <- cia_owc in CTR. rewrite <- cia_owr in RTY.
  unfold ntc_at in NT.
  destruct NT as (_ & P8 & _ & _ & NB & HNB & LNB & _ & _ & _ & _ & _ & _ & _ & NC & NR & _).
  pose proof (bytes_at_bound rsegs m p NB HNB) as PB. rewrite LNB in PB.
  assert (AND7 : Z.land p 7 = 0).
  { change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (p mod 8 = 0). exact P8. }
  assert (EC : s32_at NB 64 = s32_at B 65536) by (unfold s32_at; rewrite NC, CTR; reflexivity).
  assert (ER : s32_at B 65540 = u_at NB 68 2).
  { unfold s32_at. rewrite <- RTY, <- NR. pose proof (u_at_range NB 68 2) as RR.
    change (2 ^ (8 * Z.of_nat 2)) with 65536 in RR.
    apply bv_swrap_small. change (bv_half_modulus 32) with 2147483648. lia. }
  clear CTR RTY NC NR.
  assert (RD64 : ov_read_bytes rsegs m (Z_to_bv 64 (p + 64)) 4 = Some (sub NB 64 4))
    by (apply (bytes_at_read rsegs m p NB 64 4 HNB); [lia | rewrite LNB; first [lia | (cbn; lia)]]).
  assert (RD68 : ov_read_bytes rsegs m (Z_to_bv 64 (p + 68)) 2 = Some (sub NB 68 2))
    by (apply (bytes_at_read rsegs m p NB 68 2 HNB); [lia | rewrite LNB; first [lia | (cbn; lia)]]).
  (* 0x15ed0 auipc, 0x15ed4 addi: a1 = &g_fail_next; 0x15ed8 lw a2: GOT.acked; 0x15edc lw a3: OW.acked *)
  step. step. step. step.
  (* 0x15ee0 blt a3,a2: GOT.acked <= OW.acked *)
  step.
  cia_branch.
  { rewrite cia_lts in BR by apply s32_range. apply Z.ltb_lt in BR. lia. }
  (* 0x15ee4 andi a2,a0,7; 0x15ee8 bnez a2: n is 8-aligned *)
  step. step.
  cia_branch.
  { rewrite unsigned_lit in BR by lia. rewrite AND7, bv_eqb_refl in BR. cbn in BR. discriminate BR. }
  (* 0x15eec lw a2,64(a0): the notice's counter *)
  step. rewrite wm_lw. clear RD64.
  (* 0x15ef0 lw a3,568(a1): OW.acked_counter *)
  step.
  (* 0x15ef4 bne a2,a3 *)
  step.
  cia_branch.
  { rewrite EC, bv_eqb_refl in BR. cbn in BR. discriminate BR. }
  (* 0x15ef8 lhu a0,68(a0): the notice's retry *)
  step. rewrite wm_lhu. clear RD68.
  (* 0x15efc lw a1,572(a1): OW.acked_retry *)
  step.
  (* 0x15f00 bne a1,a0 *)
  step.
  cia_branch.
  { rewrite ER, bv_eqb_refl in BR. cbn in BR. discriminate BR. }
  (* 0x15f04 ret *)
  step.
  apply evt_done. cbv beta.
  do 15 eexists. exists m. split; [reflexivity|].
  split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|].
  split; [reflexivity | exact WM].
Qed.
