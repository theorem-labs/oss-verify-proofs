(* check_inflight_lost (fuzz/fuzz_transport.c:486-495), entry 0x159f0, 17 instructions:
     0x159f0 auipc a1,0x1d ; 0x159f4 addi a1,a1,-608      a1 = &M = W_BASE_PLAIN
     0x159f8 lw    a2,96(a1)  ; 0x159fc beqz a2,abort    M.fly.on
     0x15a00 lw    a2,64(a0)  ; 0x15a04 lw   a3,104(a1)  n->counter, M.fly.counter
     0x15a08 bne   a2,a3,abort
     0x15a0c lw    a1,108(a1)                            M.fly.retries
     0x15a10 auipc a2,0x2d    ; 0x15a14 lw   a2,-1120(a2)  g_cfg.max_retries (W_BASE_PLAIN + 0xfe20)
     0x15a18 bne   a1,a2,abort
     0x15a1c lhu   a0,68(a0)  ; 0x15a20 bne  a1,a0,abort n->retry
     0x15a24 ret
     0x15a28 addi sp,sp,-16 ; sd ra,8(sp) ; jal abort
   The model premise check_inflight_lost_m B n = Some (B', tt) gives the four facts the branches test, so every
   branch to 0x15a28 is not taken: the walk never reaches abort, and needs no callee contract. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TImgP TContract check_inflight_lost_c.
Import ListNotations.
Open Scope Z_scope.

(* a branch the walk does not take: its condition is false *)
Ltac cil_br_false tac :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota | symmetry; tac]
  end.

(* beqz on a sign-extended 32-bit value *)
Lemma cil_eqb0 : forall v, -2^63 <= v < 2^63 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  destruct (Z.eqb_spec v 0) as [->|N]; [reflexivity|].
  apply Z.eqb_neq. intros E. apply Z.mod_divide in E; [|lia]. destruct E as [c Ec]. nia.
Qed.

(* a non-negative 32-bit value below 2^31 is its own signed reading *)
Lemma cil_swrap_small : forall x, 0 <= x < 2^31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  rewrite Z.mod_small by lia. lia.
Qed.

(* the model premise, as the facts the four branches test (TCb.v check_inflight_lost_m; M.fly.on at world offset
   96, M.fly.counter 104, M.fly.retries 108, g_cfg.max_retries 0xfe20 = 65056) *)
Lemma cil_model : forall B n B',
  check_inflight_lost_m B n = Some (B', tt) ->
  s32_at B 96 <> 0 /\ n_counter n = u_at B 104 4 /\ u_at B 108 4 = u_at B 65056 4 /\
  n_retry n = u_at B 65056 4 /\ B' = B.
Proof.
  intros B n B' HM. unfold check_inflight_lost_m, truth in HM.
  change (M_fly_on B) with (s32_at B 96) in HM.
  change (M_fly_counter B) with (u_at B 104 4) in HM.
  change (M_fly_retries B) with (u_at B 108 4) in HM.
  change (Cfg_max_retries B) with (u_at B 65056 4) in HM.
  destruct (s32_at B 96 =? 0) eqn:E1; cbv beta iota delta [negb orb] in HM; [discriminate HM|].
  destruct (n_counter n =? u_at B 104 4) eqn:E2; cbv beta iota delta [negb orb] in HM; [|discriminate HM].
  destruct (u_at B 108 4 =? u_at B 65056 4) eqn:E3; cbv beta iota delta [negb orb] in HM; [|discriminate HM].
  destruct (n_retry n =? u_at B 65056 4) eqn:E4; cbv beta iota delta [negb orb] in HM; [|discriminate HM].
  injection HM as HB. subst B'.
  apply Z.eqb_neq in E1. apply Z.eqb_eq in E2. apply Z.eqb_eq in E3. apply Z.eqb_eq in E4.
  repeat split; first [exact E1 | exact E2 | exact E3 | exact E4 | reflexivity].
Qed.

Theorem check_inflight_lost_holds : check_inflight_lost_contract.
Proof.
  unfold check_inflight_lost_contract, check_inflight_lost_ENTRY, check_inflight_lost_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo B B' p n -> NT WM HM S16 ST LO OS MI.
  destruct (cil_model B n B' HM) as (ON & CTR & RET & RTY & ->). clear HM.
  unfold ntc_at in NT.
  destruct NT as (_ & _ & _ & _ & NB & HNB & LNB & _ & _ & _ & _ & _ & _ & _ & NC & NR & _).
  pose proof (bytes_at_bound rsegs m p NB HNB) as PB. rewrite LNB in PB.
  pose proof (s32_range B 96) as R96.
  assert (E64 : s32_at NB 64 = s32_at B 104) by (unfold s32_at; rewrite NC, CTR; reflexivity).
  assert (E108 : s32_at B 108 = s32_at B 65056) by (unfold s32_at; rewrite RET; reflexivity).
  assert (RR : 0 <= n_retry n < 65536).
  { rewrite <- NR. pose proof (u_at_range NB 68 2) as R. change (2 ^ (8 * Z.of_nat 2)) with 65536 in R. lia. }
  assert (E68 : s32_at B 108 = u_at NB 68 2).
  { unfold s32_at. rewrite RET, <- RTY, NR. apply cil_swrap_small. lia. }
  assert (RD64 : ov_read_bytes rsegs m (Z_to_bv 64 (p + 64)) 4 = Some (sub NB 64 4))
    by (apply (bytes_at_read rsegs m p NB 64 4 HNB); [lia | rewrite LNB; first [lia | (cbn; lia)]]).
  assert (RD68 : ov_read_bytes rsegs m (Z_to_bv 64 (p + 68)) 2 = Some (sub NB 68 2))
    by (apply (bytes_at_read rsegs m p NB 68 2 HNB); [lia | rewrite LNB; first [lia | (cbn; lia)]]).
  (* 0x159f0 auipc, 0x159f4 addi: a1 = &M *)
  step. step.
  (* 0x159f8 lw a2,96(a1): M.fly.on, a world load *)
  step.
  (* 0x159fc beqz a2: M.fly.on <> 0 *)
  step.
  cil_br_false ltac:(rewrite cil_eqb0 by lia; apply Z.eqb_neq; exact ON).
  (* 0x15a00 lw a2,64(a0): the notice's counter *)
  step. rewrite wm_lw. clear RD64.
  (* 0x15a04 lw a3,104(a1): M.fly.counter *)
  step.
  (* 0x15a08 bne a2,a3 *)
  step.
  cil_br_false ltac:(rewrite E64, bv_eqb_refl; reflexivity).
  (* 0x15a0c lw a1,108(a1): M.fly.retries; 0x15a10 auipc, 0x15a14 lw a2: g_cfg.max_retries *)
  step. step. step.
  (* 0x15a18 bne a1,a2 *)
  step.
  cil_br_false ltac:(rewrite E108, bv_eqb_refl; reflexivity).
  (* 0x15a1c lhu a0,68(a0): the notice's retry *)
  step. rewrite wm_lhu. clear RD68.
  (* 0x15a20 bne a1,a0 *)
  step.
  cil_br_false ltac:(rewrite E68, bv_eqb_refl; reflexivity).
  (* 0x15a24 ret *)
  step.
  apply evt_done. cbv beta.
  do 15 eexists. exists m. split; [reflexivity|].
  split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|].
  split; [reflexivity | exact WM].
Qed.
