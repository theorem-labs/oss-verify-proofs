(* check_keepalive_settle (fuzz/fuzz_transport.c:773-783), entry 0x1662c, 21 instructions:
     0x1662c auipc a0,0x2d   ; 0x16630 addi a0,a0,-1380   a0 = &g_fail_next = W_BASE_UBSAN + 0xfdc8
     0x16634 lw    a1,4(a0)  ; 0x16638 bnez a1,ret        g_raw (world offset 0xfdcc)
     0x1663c auipc a1,0x1d   ; 0x16640 addi a1,a1,-828    a1 = &M = W_BASE_UBSAN
     0x16644 lw    a2,12(a1) ; 0x16648 li   a3,2 ; 0x1664c bne a2,a3,ret    M.state
     0x16650 lw    a2,96(a1) ; 0x16654 bnez a2,ret        M.fly.on
     0x16658 ld    a0,32(a0) ; 0x1665c ld   a2,56(a1)     g_now (world offset 0xfde8), M.backoff_until
     0x16660 bltu  a0,a2,ret
     0x16664 ld    a1,48(a1) ; 0x16668 bgeu a0,a1,abort   M.next_ka
     0x1666c ret
     0x16670 addi sp,sp,-16 ; sd ra,8(sp) ; jal abort
     0x1667c unimp
   The function has no UBSan check of its own. The first four branches may each go to the ret or fall through: the
   walk splits on each. The model premise check_keepalive_settle_m B = Some (B', tt) says the five tests do not all
   hold, so when the first four fall through, g_now < M.next_ka and the bgeu to 0x16670 is not taken: the walk never
   reaches abort, and needs no callee contract. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract check_keepalive_settle_c.
Import ListNotations.
Open Scope Z_scope.

(* beqz / bne on two values in the signed 64-bit range: the machine test is the Z test *)
Lemma cks_eqb : forall v w, -2^63 <= v < 2^63 -> -2^63 <= w < 2^63 ->
  bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 w) = (v =? w).
Proof.
  intros v w Hv Hw. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec v w) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply N.
  assert (D : (v - w) mod 2^64 = 0) by (rewrite Zminus_mod, E, Z.sub_diag; reflexivity).
  clear E N.
  apply Z.mod_divide in D; [|lia]. destruct D as [c Ec]. lia.
Qed.

(* bltu / bgeu on two values in the unsigned 64-bit range: the machine test is the Z test *)
Lemma cks_ltu : forall v w, 0 <= v < 2^64 -> 0 <= w < 2^64 ->
  bv_ltu (Z_to_bv 64 v) (Z_to_bv 64 w) = (v <? w).
Proof. intros v w Hv Hw. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

(* the model premise (TCb.v check_keepalive_settle_m; g_raw at world offset 0xfdcc = 64972, M.state 12, M.fly.on 96,
   M.backoff_until 56, M.next_ka 48, g_now 0xfde8 = 65000): the world is returned unchanged, and when the first four
   tests hold, the fifth (M.next_ka <= g_now) does not *)
Lemma cks_model : forall B B',
  check_keepalive_settle_m B = Some (B', tt) ->
  B' = B /\
  (s32_at B 64972 = 0 -> s32_at B 12 = 2 -> s32_at B 96 = 0 -> u_at B 56 8 <= u_at B 65000 8 ->
   u_at B 65000 8 < u_at B 48 8).
Proof.
  intros B B' HM. unfold check_keepalive_settle_m in HM.
  destruct (negb (truth (g_raw B)) && (M_state B =? S_ONLINE) && negb (truth (M_fly_on B))
            && (M_backoff_until B <=? g_now B) && (M_next_ka B <=? g_now B)) eqn:C; [discriminate HM|].
  injection HM as HB. split; [symmetry; exact HB|].
  intros E1 E2 E3 E4. apply Z.nle_gt. intros E5.
  (* then all five tests hold, each from its fact, and the model would return None *)
  assert (T : negb (truth (g_raw B)) && (M_state B =? S_ONLINE) && negb (truth (M_fly_on B))
              && (M_backoff_until B <=? g_now B) && (M_next_ka B <=? g_now B) = true).
  { apply andb_true_intro; split; [|apply Z.leb_le; exact E5].
    apply andb_true_intro; split; [|apply Z.leb_le; exact E4].
    apply andb_true_intro; split; [|apply negb_true_iff, negb_false_iff, Z.eqb_eq; exact E3].
    apply andb_true_intro; split; [|apply Z.eqb_eq; exact E2].
    apply negb_true_iff, negb_false_iff, Z.eqb_eq; exact E1. }
  exact (Bool.diff_true_false (eq_trans (eq_sym T) C)).
Qed.

(* a branch to the ret at 0x1666c, or the fall-through into it: step the ret and give the post *)
Ltac cks_ret :=
  step; apply evt_done; cbv beta;
  do 16 eexists; split; [reflexivity|];
  split; [apply munch_refl|]; split; [apply wmono_refl|];
  split; [eassumption|]; split; [eassumption|]; split; [reflexivity | eassumption].

Theorem check_keepalive_settle_holds : check_keepalive_settle_contract.
Proof.
  unfold check_keepalive_settle_contract, check_keepalive_settle_ENTRY, check_keepalive_settle_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo B B' WM HM S16 ST LO WO MI.
  destruct (cks_model B B' HM) as (-> & DUE). clear HM.
  pose proof (s32_range B 64972) as R1.
  pose proof (s32_range B 12) as R2.
  pose proof (s32_range B 96) as R3.
  assert (R4 : 0 <= u_at B 65000 8 < 2 ^ 64) by exact (u_at_range B 65000 8).
  assert (R5 : 0 <= u_at B 56 8 < 2 ^ 64) by exact (u_at_range B 56 8).
  assert (R6 : 0 <= u_at B 48 8 < 2 ^ 64) by exact (u_at_range B 48 8).
  (* 0x1662c auipc, 0x16630 addi: a0 = &g_fail_next *)
  step. step.
  (* 0x16634 lw a1,4(a0): g_raw, a world load *)
  step.
  (* 0x16638 bnez a1: to the ret when g_raw <> 0 *)
  step.
  rewrite cks_eqb by lia.
  destruct (Z.eqb_spec (s32_at B 64972) 0) as [E1|E1]; cbn [negb]; [|cks_ret].
  (* 0x1663c auipc, 0x16640 addi: a1 = &M *)
  step. step.
  (* 0x16644 lw a2,12(a1): M.state; 0x16648 li a3,2 *)
  step. step.
  (* 0x1664c bne a2,a3: to the ret when M.state <> ONLINE *)
  step.
  rewrite cks_eqb by lia.
  destruct (Z.eqb_spec (s32_at B 12) 2) as [E2|E2]; cbn [negb]; [|cks_ret].
  (* 0x16650 lw a2,96(a1): M.fly.on *)
  step.
  (* 0x16654 bnez a2: to the ret when M.fly.on <> 0 *)
  step.
  rewrite cks_eqb by lia.
  destruct (Z.eqb_spec (s32_at B 96) 0) as [E3|E3]; cbn [negb]; [|cks_ret].
  (* 0x16658 ld a0,32(a0): g_now; 0x1665c ld a2,56(a1): M.backoff_until *)
  step. step.
  (* 0x16660 bltu a0,a2: to the ret when g_now < M.backoff_until *)
  step.
  rewrite cks_ltu by lia.
  destruct (Z.ltb_spec (u_at B 65000 8) (u_at B 56 8)) as [E4|E4]; cbn [negb]; [cks_ret|].
  (* 0x16664 ld a1,48(a1): M.next_ka *)
  step.
  (* 0x16668 bgeu a0,a1: to abort when g_now >= M.next_ka, which the model premise rules out *)
  step.
  rewrite cks_ltu by lia.
  destruct (Z.ltb_spec (u_at B 65000 8) (u_at B 48 8)) as [E5|E5]; cbn [negb]; [cks_ret|].
  exfalso. specialize (DUE E1 E2 E3 E4). lia.
Qed.
