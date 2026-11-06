(* The walk of m_lost in the plain image, against m_lost_c.v. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TImg TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract m_lost_c.
Import ListNotations.
Open Scope Z_scope.

(* beqz on a sign-extended int *)
Lemma m_lost_eqb0 : forall x, -2^31 <= x < 2^31 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = (x =? 0).
Proof.
  intros x Hx. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  destruct (Z.eqb_spec x 0) as [->|Hne]; [reflexivity|].
  apply Z.eqb_neq. rewrite Zmod_0_l. intro E. Z.div_mod_to_equations. lia.
Qed.

(* blt on two sign-extended ints *)
Lemma m_lost_lts : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
  bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
  intros a b Ha Hb. unfold bv_lts. rewrite !Z_to_bv_signed.
  rewrite !bv_swrap_small by (change (bv_half_modulus 64) with (2^63); lia). reflexivity.
Qed.

Ltac m_lost_side :=
  unfold A_M_state, A_M_desk_counter_valid, A_M_fly_on, OFF_M in *;
  repeat (rewrite length_upd_put; [ | lia | ]);
  rewrite ?length_put; lia.

(* The stores into OW.t[OW.n] (fuzz_transport.c:201-203) address &g_fail_next + 12 * n + imm, a literal plus a
   scaled index plus an immediate, which the kit's world hook (TWorldMem.v wk_offset) does not read. So before such
   a store the walk proves its target writable at world offset k (wm_store_ok): the kit's solve_store then matches
   the store address against this fact by lia and writes at W_BASE_PLAIN + k, which the world hook reads as offset
   k, so [step] leaves the world as upd B k bs. *)
Ltac m_lost_pre_store k :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    lazymatch goal with
    | H : rw_cells segs m W_BASE_PLAIN [CB (Z.to_nat W_LEN) ?B] |- _ =>
        let HS := fresh "HSi" in
        assert (HS : store_ok segs m (Z_to_bv 64 (W_BASE_PLAIN + k)) 4 = true)
          by (apply (wm_store_ok segs W_BASE_PLAIN m B k 4); [exact H | lia | lia | reflexivity])
    end
  end.

Theorem m_lost_holds : m_lost_contract.
Proof.
  unfold m_lost_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo B B'
    why -> Hwhy SPA ST LO WOS MI WM HM.
  change m_lost_FRAME with 0 in *. unfold m_lost_ENTRY.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  unfold w_off_stack in WOS.
  pose proof (munch_refl [(bv_unsigned sp - 0, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMO.
  pose proof (wm_len _ _ _ _ WM) as LB.
  wk_facts.
  assert (LB0 : Z.of_nat (length B) = 65616)
    by (rewrite LB, Z2Nat.id by (unfold W_LEN; lia); exact Ew).
  (* 0x158ac auipc, addi: a1 = &M; lw a2 = M.state; sw M.desk_counter_valid = 0; sw M.fly.on = 0 *)
  step. step. step. step. step.
  (* the world is the model's B1 = set_M_desk_counter_valid (set_M_fly_on B 0) 0; a2 is M_state B1 *)
  assert (EB1 : upd (upd B 76 (put 4 0)) 96 (put 4 0) = set_M_desk_counter_valid (set_M_fly_on B 0) 0).
  { unfold set_M_desk_counter_valid, set_M_fly_on.
    change A_M_desk_counter_valid with 76. change A_M_fly_on with 96.
    apply upd_upd_comm; rewrite ?length_put; lia. }
  assert (EST : s32_at B 12 = M_state (set_M_desk_counter_valid (set_M_fly_on B 0) 0)).
  { unfold M_state, set_M_desk_counter_valid, set_M_fly_on.
    change A_M_state with 12. change A_M_desk_counter_valid with 76. change A_M_fly_on with 96.
    rewrite !s32_at_upd_out; [ reflexivity | m_lost_side .. ]. }
  lazymatch goal with H : rw_cells _ _ W_BASE_PLAIN _ |- _ => rewrite EB1 in H end.
  rewrite EST.
  unfold m_lost_m, m_set_m, int_inc in HM.
  set (B1 := set_M_desk_counter_valid (set_M_fly_on B 0) 0) in *.
  clearbody B1. clear EB1 EST.
  (* 0x158c0 beqz a2 *)
  step.
  rewrite (m_lost_eqb0 (M_state B1)) by (unfold M_state; apply s32_range).
  destruct (Z.eqb_spec (M_state B1) 0) as [E0|E0].
  - (* M.state == S_IDLE: m_set returns at once (fuzz_transport.c:198-199) *)
    replace (M_state B1 =? S_IDLE) with true in HM by (symmetry; apply Z.eqb_eq; exact E0).
    cbv beta iota in HM. injection HM as HB'. subst B'.
    replace (M_state B1 =? 0) with true by (symmetry; apply Z.eqb_eq; exact E0). cbv iota.
    step.
    apply evt_done. unfold QQ. do 16 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    lazymatch goal with H : rw_cells rsegs ?mm W_BASE_PLAIN _ |- rw_cells rsegs ?mm W_BASE_PLAIN _ => exact H end.
  - replace (M_state B1 =? S_IDLE) with false in HM by (symmetry; apply Z.eqb_neq; exact E0).
    cbv beta iota zeta in HM.
    replace (M_state B1 =? 0) with false by (symmetry; apply Z.eqb_neq; exact E0). cbv iota.
    change (OW_n B1) with (s32_at B1 65312) in HM.
    (* 0x158c4 auipc, addi: a3 = &g_fail_next; lw a4 = OW.n; li a5, 15; blt a5, a4 *)
    step. step. step.
    pose proof (s32_range B1 65312) as Rn.
    set (n := s32_at B1 65312) in *. clearbody n.
    step. step.
    rewrite (m_lost_lts 15 n) by lia.
    destruct (Z.ltb_spec 15 n) as [L15|L15].
    + (* OW.n >= TRANS_MAX: no entry is written (:200) *)
      replace (n <? TRANS_MAX) with false in HM by (symmetry; apply Z.ltb_ge; unfold TRANS_MAX; lia).
      cbv beta iota in HM.
      (* OW.n == INT_MAX: OW.n++ overflows (:205); the model is None there, so the premise HM excludes it *)
      destruct (Z.eq_dec n INT_MAX) as [EI|EI].
      { rewrite EI, Z.eqb_refl in HM. cbv beta iota in HM. discriminate HM. }
      replace (n =? INT_MAX) with false in HM by (symmetry; apply Z.eqb_neq; exact EI).
      cbv beta iota in HM. injection HM as HB'. subst B'.
      replace (15 <? n) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      (* 0x158f4 addi a4 = OW.n + 1; sw OW.n; sw M.state = S_IDLE; ret *)
      step. step. step. step.
      apply evt_done. unfold QQ. do 16 eexists. split; [reflexivity|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      lazymatch goal with H : rw_cells rsegs ?mm W_BASE_PLAIN _ |- rw_cells rsegs ?mm W_BASE_PLAIN _ => exact H end.
    + (* OW.n < TRANS_MAX: OW.t[OW.n] = {S_IDLE, old state, why} (:200-203) *)
      replace (n <? TRANS_MAX) with true in HM by (symmetry; apply Z.ltb_lt; unfold TRANS_MAX; lia).
      (* OW.n < 0: OW.t[OW.n] is out of bounds (:201) and the binary would store below OW.t; the model is None
         there, so the premise HM excludes it *)
      destruct (Z_lt_le_dec n 0) as [Ln|Ln].
      { replace (n <? 0) with true in HM by (symmetry; apply Z.ltb_lt; lia). cbv beta iota in HM. discriminate HM. }
      replace (n <? 0) with false in HM by (symmetry; apply Z.ltb_ge; lia).
      replace (n =? INT_MAX) with false in HM by (symmetry; apply Z.eqb_neq; unfold INT_MAX; lia).
      cbv beta iota in HM. injection HM as HB'. subst B'.
      replace (15 <? n) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
      (* 0x158d8 slli, slli, sub, add: a5 = &g_fail_next + 12 * OW.n *)
      step. step. step. step.
      lazymatch goal with |- context [Z_to_bv 64 (271704 + ?X)] =>
        replace (Z_to_bv 64 (271704 + X)) with (Z_to_bv 64 (271704 + 12 * n))
          by (f_equal; rewrite (unsigned_lit n) by lia; rewrite !Z.shiftl_mul_pow2 by lia;
              change (2 ^ 4) with 16; change (2 ^ 2) with 4; rewrite !unsigned_lit by lia; lia)
      end.
      (* 0x158e8 sw OW.t[n].state = S_IDLE; sw OW.t[n].old = M.state; sw OW.t[n].reason = why *)
      m_lost_pre_store (65316 + 12 * n). step.
      m_lost_pre_store (65320 + 12 * n). step.
      m_lost_pre_store (65324 + 12 * n). step.
      (* the three offsets are the model's A_OW_t_state / _old / _reason n *)
      lazymatch goal with H : rw_cells rsegs _ W_BASE_PLAIN _ |- _ =>
        replace (65316 + 12 * n) with (A_OW_t_state n) in H by (unfold A_OW_t_state, OFF_OW; lia);
        replace (65320 + 12 * n) with (A_OW_t_old n) in H by (unfold A_OW_t_old, OFF_OW; lia);
        replace (65324 + 12 * n) with (A_OW_t_reason n) in H by (unfold A_OW_t_reason, OFF_OW; lia)
      end.
      (* 0x158f4 addi a4 = OW.n + 1; sw OW.n; sw M.state = S_IDLE; ret *)
      step. step. step. step.
      apply evt_done. unfold QQ. do 16 eexists. split; [reflexivity|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      lazymatch goal with H : rw_cells rsegs ?mm W_BASE_PLAIN _ |- rw_cells rsegs ?mm W_BASE_PLAIN _ => exact H end.
Qed.
