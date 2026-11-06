(* check_latest_display (fuzz/fuzz_transport.c:646-654), entry 0x158c8, 16 instructions:
     0x158c8 auipc a0,0x1e ; 0x158cc addi a0,a0,-1480   a0 = &M = W_BASE_UBSAN
     0x158d0 lw    a1,72(a0)                            M.display_sent
     0x158d4 beqz  a1,0x158f4                           no display write sent: return
     0x158d8 auipc a1,0x2d ; 0x158dc addi a1,a1,2032    a1 = &g_fail_next = W_BASE_UBSAN + 0xfdc8
     0x158e0 ld    a2,32(a1)                            g_now (world offset 0xfde8 = 65000)
     0x158e4 ld    a0,64(a0)                            M.last_display
     0x158e8 lwu   a1,104(a1)                           g_cfg.display_gap_us (world offset 0xfe30 = 65072)
     0x158ec sub   a2,a2,a0
     0x158f0 bltu  a2,a1,0x158f8                        g_now - M.last_display < gap: abort
     0x158f4 ret
     0x158f8 addi sp,sp,-16 ; 0x158fc sd ra,8(sp) ; 0x15900 jal abort ; 0x15904 unimp
   The model premise check_latest_display_m B = Some (B', tt) gives: when M.display_sent <> 0,
   (g_now - M.last_display) mod 2^64 >= g_cfg.display_gap_us, so the branch to 0x158f8 is not taken; the walk never
   reaches abort, and needs no callee contract. Both paths return without touching the stack or memory. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem check_latest_display_c.
Import ListNotations.
Open Scope Z_scope.

(* beqz on a sign-extended 32-bit value *)
Lemma cld_eqb0 : forall v, -2^63 <= v < 2^63 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  destruct (Z.eqb_spec v 0) as [->|N]; [reflexivity|].
  apply Z.eqb_neq. intros E. apply Z.mod_divide in E; [|lia]. destruct E as [c Ec]. nia.
Qed.

(* the model premise, as the facts the two branches test (TCb.v check_latest_display_m; M.display_sent at world
   offset 72, M.last_display 64, g_now 0xfde8 = 65000, g_cfg.display_gap_us 0xfe30 = 65072) *)
Lemma cld_model : forall B B',
  check_latest_display_m B = Some (B', tt) ->
  B' = B /\ (s32_at B 72 <> 0 -> (u64 (u_at B 65000 8 - u_at B 64 8) <? u_at B 65072 4) = false).
Proof.
  intros B B' HM. unfold check_latest_display_m, truth in HM.
  change (M_display_sent B) with (s32_at B 72) in HM.
  change (g_now B) with (u_at B 65000 8) in HM.
  change (M_last_display B) with (u_at B 64 8) in HM.
  change (Cfg_display_gap_us B) with (u_at B 65072 4) in HM.
  destruct (s32_at B 72 =? 0) eqn:E1; cbv beta iota delta [negb andb] in HM.
  - injection HM as HB. split; [symmetry; exact HB|].
    intros N. apply Z.eqb_eq in E1. contradiction.
  - destruct (u64 (u_at B 65000 8 - u_at B 64 8) <? u_at B 65072 4) eqn:E2; [discriminate HM|].
    injection HM as HB. split; [symmetry; exact HB | intros _; reflexivity].
Qed.

Theorem check_latest_display_holds : check_latest_display_contract.
Proof.
  unfold check_latest_display_contract, check_latest_display_ENTRY, check_latest_display_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo B B'
    WM HM Hal ST LO WO MI.
  destruct (cld_model B B' HM) as [-> GAP]. clear HM.
  pose proof (s32_range B 72) as R0.
  assert (R1 : 0 <= u_at B 65000 8 < 2 ^ 64) by exact (u_at_range B 65000 8).
  assert (R2 : 0 <= u_at B 64 8 < 2 ^ 64) by exact (u_at_range B 64 8).
  assert (R3 : 0 <= u_at B 65072 4 < 2 ^ 64).
  { pose proof (u_at_range B 65072 4) as R. change (2 ^ (8 * Z.of_nat 4)) with 4294967296 in R.
    change (2 ^ 64) with 18446744073709551616. lia. }
  wk_facts.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  (* 0x158c8 auipc, 0x158cc addi: a0 = &M *)
  step. step.
  (* 0x158d0 lw a1,72(a0): M.display_sent, a world load *)
  step.
  (* 0x158d4 beqz a1: taken iff M.display_sent = 0 *)
  step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with (s32_at B 72 =? 0) by (symmetry; apply cld_eqb0; lia)
  end.
  destruct (Z.eqb_spec (s32_at B 72) 0) as [D|D]; cbv iota.
  - (* no display write sent: 0x158f4 ret *)
    step.
    apply evt_done. hnf. do 16 eexists. split; [reflexivity|].
    refine (conj _ (conj _ (conj _ (conj _ (conj eq_refl _))))).
    all: eassumption.
  - (* 0x158d8 auipc, 0x158dc addi: a1 = &g_fail_next *)
    step. step.
    (* 0x158e0 ld a2,32(a1): g_now; 0x158e4 ld a0,64(a0): M.last_display; 0x158e8 lwu a1,104(a1): the gap *)
    step. step. step.
    (* 0x158ec sub a2,a2,a0 *)
    step.
    (* 0x158f0 bltu a2,a1: (g_now - M.last_display) mod 2^64 >= the gap, falls through *)
    step.
    lazymatch goal with
    | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        replace c with false;
        [ cbv iota
        | symmetry; rewrite bv_ltu_Z, ?unsigned_lit_wrap;
          rewrite ?(Z.mod_small (u_at B 65000 8)), ?(Z.mod_small (u_at B 64 8)), ?(Z.mod_small (u_at B 65072 4))
            by lia;
          exact (GAP D) ]
    end.
    (* 0x158f4 ret *)
    step.
    apply evt_done. hnf. do 16 eexists. split; [reflexivity|].
    refine (conj _ (conj _ (conj _ (conj _ (conj eq_refl _))))).
    all: eassumption.
Qed.
