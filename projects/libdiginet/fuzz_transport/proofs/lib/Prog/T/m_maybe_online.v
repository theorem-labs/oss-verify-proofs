(* The walk of m_maybe_online in the plain image, against m_maybe_online_c.v. *)
(* m_maybe_online, entry 0x15904 (fuzz/fuzz_transport.c:237-243), a leaf with no prologue: m_set is inlined, so
   this walk assumes no callee contract. The function reads M.state, M.e2_acked and M.e1_us; unless all three say
   WAKING with both flags set it returns at once (0x15988) and the world is unchanged. Otherwise it stores
   M.next_ka = g_cfg.keepalive_ms * 1000 + M.last_rx (0x1594c), and then m_set's body: when OW.n <= 15 (the signed
   blt at 0x15950) the three words of OW.t[OW.n] (0x1596c-0x15974), then OW.n + 1 and M.state = S_ONLINE.
   The model forces OW.n >= 0 in that arm (m_set_m is None for a negative index), which keeps the indexed stores
   inside the world. The store hooks below are those of the ubsan m_set walk (U/Prog/T/m_set.v,
   lines 13-96) with the plain base W_BASE_PLAIN. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TImg TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract m_maybe_online_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- bridges: a register holding a 32-bit value, and the model's Z tests ---- *)

Lemma signed_int : forall x, -2^31 <= x < 2^31 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. rewrite zb_signed, unsigned_lit_wrap.
  destruct (Z_le_gt_dec 0 x) as [N|N].
  - rewrite (Z.mod_small x (2^64)) by lia.
    rewrite (proj2 (Z.ltb_lt x (2^63))) by lia. reflexivity.
  - assert (Hm : x mod 2^64 = x + 2^64).
    { rewrite <- (Z.mod_add x 1 (2^64)) by lia. rewrite Z.mod_small by lia. ring. }
    rewrite Hm. rewrite (proj2 (Z.ltb_ge (x + 2^64) (2^63))) by lia. cbv iota. lia.
Qed.

Lemma br_eqb : forall x y, -2^31 <= x < 2^31 -> -2^31 <= y < 2^31 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb.
  destruct (Z.eqb_spec (bv_unsigned (Z_to_bv 64 x)) (bv_unsigned (Z_to_bv 64 y))) as [E|E];
  destruct (Z.eqb_spec x y) as [Ex|Ex]; try reflexivity.
  - exfalso. apply Ex.
    pose proof (signed_int x Hx) as Sx. pose proof (signed_int y Hy) as Sy.
    rewrite zb_signed, E in Sx. rewrite zb_signed in Sy. congruence.
  - exfalso. apply E. rewrite Ex. reflexivity.
Qed.

Lemma br_slt : forall x y, -2^31 <= x < 2^31 -> -2^31 <= y < 2^31 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_lts. rewrite !signed_int by assumption. reflexivity. Qed.

(* ---- the bytes the machine writes at M.next_ka are the model's u64 sum ---- *)

Lemma mo_put8_ka : forall k l, put 8 (k * 1000 + l) = put 8 (u64 (l + h_ms_m k)).
Proof.
  intros k l. unfold h_ms_m, u64.
  rewrite <- (put_mod64 8 (k * 1000 + l)) by lia. f_equal.
  rewrite Z.add_mod_idemp_r by lia. f_equal. lia.
Qed.

(* ---- the next_ka store (8 bytes at offset 48) leaves M.state and OW.n alone ---- *)

Lemma mo_state_ka : forall (B0 : list byte) v, Z.of_nat (length B0) = 65616 ->
  M_state (set_M_next_ka B0 v) = M_state B0.
Proof.
  intros B0 v L. unfold M_state, set_M_next_ka, A_M_state, A_M_next_ka, OFF_M.
  rewrite s32_at_upd_out; [reflexivity | lia | lia | rewrite length_put; lia | rewrite length_put; lia].
Qed.

Lemma mo_n_ka : forall (B0 : list byte) v, Z.of_nat (length B0) = 65616 ->
  OW_n (set_M_next_ka B0 v) = OW_n B0.
Proof.
  intros B0 v L. unfold OW_n, set_M_next_ka, A_OW_n, A_M_next_ka, OFF_OW, OFF_M.
  rewrite s32_at_upd_out; [reflexivity | lia | lia | rewrite length_put; lia | rewrite length_put; lia].
Qed.

(* ---- world stores (U/Prog/T/m_set.v:44-96, base W_BASE_PLAIN) ----
   The indexed OW.t stores form the address as (struct_base + 12*n) + field_off: two literals with the symbolic
   index between them, which the world store hook's wk_offset cannot read. Fold the literals into the world
   offset and keep the base the NAME W_BASE_PLAIN, so wk_offset reads [W_BASE_PLAIN + k] directly and the cell
   machinery's literal [address - base] path stays off. *)
Ltac mset_fold_in E :=
  lazymatch E with
  | ?c1 + ?X + ?c2 =>
      is_Zlit_zb c1; is_Zlit_zb c2;
      let d := eval vm_compute in (Z.add c1 c2 - W_BASE_PLAIN)%Z in
      replace (c1 + X + c2) with (W_BASE_PLAIN + (d + X)) by (unfold W_BASE_PLAIN; lia)
  end.
Ltac mset_norm_addr :=
  try (lazymatch goal with
  | |- context [store_ok _ _ (Z_to_bv 64 ?E) _] => mset_fold_in E
  | |- context [write_to_mem _ (Z_to_bv 64 ?E) _] => mset_fold_in E
  | |- context [write_to_mem _ (wa ?E) _] => mset_fold_in E
  end).
Ltac solve_store ::= mset_norm_addr; wk_solve_store_world.
(* Side goals by lia only. The kit's wk_side / wk_len_side fall through to wk_vm_close, which [vm_compute]s a goal
   still holding the open [Z_to_bv 64 _] of the stored bytes: the runaway TWorldMem.v warns about. Rewrite
   [length] first and never [vm_compute]. *)
Ltac msafe := first [ lia | (unfold W_LEN, W_BASE_PLAIN in *; lia) ].
Ltac mlen := rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1; msafe.
(* Transport the world fact and the footprint across each world store with the kit's own lemmas (the kit's
   store_done takes the same runaway path on an indexed address). *)
Ltac mset_after :=
  try fix_lit_store; mset_norm_addr;
  lazymatch goal with
  | |- evt rsegs _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs) _) =>
      let E := addr_expr a in
      lazymatch goal with
      | WM : rw_cells rsegs m W_BASE_PLAIN [CB (Z.to_nat W_LEN) ?B] |- _ =>
          let k := wk_offset W_BASE_PLAIN a in
          assert (HS : store_ok rsegs m a (length bs) = true)
            by (apply (wm_store_ok rsegs W_BASE_PLAIN m B k (length bs) a WM); [ msafe | mlen | wk_addr_eq ]);
          let WMn := fresh "WMn" in
          assert (WMn : rw_cells rsegs (write_to_mem m a bs) W_BASE_PLAIN [CB (Z.to_nat W_LEN) (upd B k bs)])
            by (apply (wm_write_at rsegs W_BASE_PLAIN m B k bs E);
                [ exact WM | msafe | mlen | first [ reflexivity | (unfold W_BASE_PLAIN; lia) ] ]);
          match goal with MU : munch ?W ?m0 m |- _ =>
            apply (munch_write W m0 m E bs) in MU;
              [ change (wa E) with a in MU
              | msafe | mlen | (cbn [inside]; right; left; rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1; split; msafe) ] end;
          match goal with WMo : wmono _ ?m0 m |- _ => apply (wmono_write rsegs m0 m a bs) in WMo end;
          match goal with MI : mem_inv rsegs m |- _ => apply (mem_inv_store rsegs m a bs) in MI; [ | exact HS ] end;
          match goal with ST : stk rsegs m ?lo ?hi |- _ =>
            apply (stk_write rsegs m lo hi E bs) in ST; [ change (wa E) with a in ST | msafe | mlen ] end;
          clear WM HS; rename WMn into WM;
          let mN := fresh "m" in set (mN := write_to_mem m a bs) in *; clearbody mN
      end
  | _ => idtac
  end.
Ltac mem_after_store_opt ::= mset_after.

Theorem m_maybe_online_holds : m_maybe_online_contract.
Proof.
  unfold m_maybe_online_contract, m_maybe_online_ENTRY, m_maybe_online_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo B B' Hsp ST LO WOFF MI WM MODEL.
  assert (RST : -2^31 <= M_state B < 2^31) by apply (s32_range B A_M_state).
  assert (RE2 : -2^31 <= M_e2_acked B < 2^31) by apply (s32_range B A_M_e2_acked).
  assert (RE1 : -2^31 <= M_e1_us B < 2^31) by apply (s32_range B A_M_e1_us).
  assert (RN : -2^31 <= OW_n B < 2^31) by apply (s32_range B A_OW_n).
  assert (LB : Z.of_nat (length B) = 65616)
    by (rewrite (wm_len rsegs W_BASE_PLAIN m B WM); vm_compute; reflexivity).
  assert (RKA : 0 <= Cfg_keepalive_ms B < 2^32)
    by (pose proof (u_at_range B A_Cfg_keepalive_ms 4) as HR;
        change (8 * Z.of_nat 4)%Z with 32%Z in HR; exact HR).
  pose proof (munch_refl [(bv_unsigned sp - 0, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WO.
  wk_facts.
  unfold m_maybe_online_m, S_WAKING, S_ONLINE, R_ONLINE, truth in MODEL.
  step.                                   (* 0x15904 auipc a0, 0x1d *)
  step.                                   (* 0x15908 addi a0,a0,-372: a0 = W_BASE_PLAIN *)
  step.                                   (* 0x1590c lw a1,12(a0): M.state *)
  change (s32_at B 12) with (M_state B).
  step.                                   (* 0x15910 li a2,1 *)
  step.                                   (* 0x15914 bne a1,a2,0x15988 *)
  rewrite (br_eqb (M_state B) 1) by lia.
  destruct (Z.eqb_spec (M_state B) 1) as [EST|EST]; cbn [negb andb] in MODEL |- *; cbv iota.
  2: { assert (EB : B' = B) by congruence; subst B'.
       step.                              (* 0x15988 ret *)
       apply evt_done. hnf. do 16 eexists. split; [reflexivity|].
       split; [exact MU|]. split; [exact WO|]. split; [exact MI|]. split; [exact ST|exact WM]. }
  step.                                   (* 0x15918 lw a1,16(a0): M.e2_acked *)
  change (s32_at B 16) with (M_e2_acked B).
  step.                                   (* 0x1591c beqz a1,0x15988 *)
  rewrite (br_eqb (M_e2_acked B) 0) by lia.
  destruct (Z.eqb_spec (M_e2_acked B) 0) as [EE2|EE2]; cbn [negb andb] in MODEL |- *; cbv iota.
  1: { assert (EB : B' = B) by congruence; subst B'.
       step.                              (* 0x15988 ret *)
       apply evt_done. hnf. do 16 eexists. split; [reflexivity|].
       split; [exact MU|]. split; [exact WO|]. split; [exact MI|]. split; [exact ST|exact WM]. }
  step.                                   (* 0x15920 lw a1,20(a0): M.e1_us *)
  change (s32_at B 20) with (M_e1_us B).
  step.                                   (* 0x15924 beqz a1,0x15988 *)
  rewrite (br_eqb (M_e1_us B) 0) by lia.
  destruct (Z.eqb_spec (M_e1_us B) 0) as [EE1|EE1]; cbn [negb andb] in MODEL |- *; cbv iota.
  1: { assert (EB : B' = B) by congruence; subst B'.
       step.                              (* 0x15988 ret *)
       apply evt_done. hnf. do 16 eexists. split; [reflexivity|].
       split; [exact MU|]. split; [exact WO|]. split; [exact MI|]. split; [exact ST|exact WM]. }
  (* the taken branch: MODEL is now m_set_m (set_M_next_ka B KA) S_ONLINE R_ONLINE = Some (B', tt). The next_ka
     store touches neither M.state nor OW.n, so m_set's test M.state == S_ONLINE is false, and OW.n is
     incremented only below INT_MAX. *)
  unfold m_set_m, TRANS_MAX, int_inc, INT_MAX in MODEL.
  rewrite (mo_state_ka B _ LB) in MODEL.
  rewrite (mo_n_ka B _ LB) in MODEL.
  rewrite EST in MODEL.
  change ((1 =? 2)%Z) with false in MODEL.
  cbv beta iota zeta in MODEL.
  destruct (Z.eqb_spec (OW_n B) (2 ^ 31 - 1)) as [EINC|EINC];
    [ exfalso; cbv beta iota in MODEL;
      destruct (OW_n B <? 16); [destruct (OW_n B <? 0)|]; discriminate MODEL | ].
  cbv beta iota in MODEL.
  step.                                   (* 0x15928 auipc a1, 0x2d *)
  step.                                   (* 0x1592c addi a1,a1,-976: a1 = &g_fail_next *)
  step.                                   (* 0x15930 lwu a3,80(a1): g_cfg.keepalive_ms *)
  change (u_at B 65048 4) with (Cfg_keepalive_ms B).
  step.                                   (* 0x15934 ld a4,32(a0): M.last_rx *)
  change (u_at B 32 8) with (M_last_rx B).
  step.                                   (* 0x15938 li a5,1000 *)
  step.                                   (* 0x1593c lw a2,344(a1): OW.n *)
  change (s32_at B 65312) with (OW_n B).
  step.                                   (* 0x15940 mul a3,a3,a5 *)
  rewrite (unsigned_lit (Cfg_keepalive_ms B)) by lia.
  step.                                   (* 0x15944 add a3,a3,a4 *)
  step.                                   (* 0x15948 li a4,15 *)
  step.                                   (* 0x1594c sd a3,48(a0): M.next_ka *)
  step.                                   (* 0x15950 blt a4,a2,0x15978 *)
  rewrite (br_slt 15 (OW_n B)) by lia.
  destruct (Z.ltb_spec 15 (OW_n B)) as [HN|HN]; cbv iota.
  - (* OW.n >= 16: no transition slot is written *)
    replace (OW_n B <? 16) with false in MODEL by (symmetry; apply Z.ltb_ge; lia).
    cbv beta iota in MODEL. injection MODEL as HB. subst B'.
    step.                                 (* 0x15978 addi a2,a2,1 *)
    step.                                 (* 0x1597c sw a2,344(a1): OW.n *)
    step.                                 (* 0x15980 li a1,2 *)
    step.                                 (* 0x15984 sw a1,12(a0): M.state *)
    step.                                 (* 0x15988 ret *)
    unfold set_M_state, set_OW_n, set_M_next_ka.
    rewrite ?le8_put, ?le4_put in WM.
    rewrite <- (mo_put8_ka (Cfg_keepalive_ms B) (M_last_rx B)).
    apply evt_done. hnf. do 16 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WO|]. split; [exact MI|]. split; [exact ST|exact WM].
  - (* OW.n <= 15: the model forbids a negative index, and OW.t[OW.n] is written *)
    replace (OW_n B <? 16) with true in MODEL by (symmetry; apply Z.ltb_lt; lia).
    cbv beta iota in MODEL.
    assert (HN0 : 0 <= OW_n B).
    { destruct (Z_lt_le_dec (OW_n B) 0) as [L|L]; [exfalso|exact L].
      replace (OW_n B <? 0) with true in MODEL by (symmetry; apply Z.ltb_lt; lia).
      cbv beta iota in MODEL. discriminate MODEL. }
    replace (OW_n B <? 0) with false in MODEL by (symmetry; apply Z.ltb_ge; lia).
    cbv beta iota in MODEL. injection MODEL as HB. subst B'.
    step.                                 (* 0x15954 slli a3,a2,2 *)
    step.                                 (* 0x15958 slli a4,a2,4 *)
    step.                                 (* 0x1595c li a5,2 *)
    step.                                 (* 0x15960 sub a4,a4,a3 *)
    step.                                 (* 0x15964 li a3,1 *)
    step.                                 (* 0x15968 add a4,a1,a4: a4 = &g_fail_next + 12 * OW.n *)
    assert (Ha6 : bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (OW_n B))) 4)) -
                  bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (OW_n B))) 2)) = 12 * OW_n B).
    { rewrite (unsigned_lit (OW_n B)) by lia.
      rewrite !Z.shiftl_mul_pow2 by lia.
      rewrite (unsigned_lit (OW_n B * 2^4)) by (change (2^4) with 16; lia).
      rewrite (unsigned_lit (OW_n B * 2^2)) by (change (2^2) with 4; lia).
      change (2^4) with 16. change (2^2) with 4. lia. }
    rewrite Ha6.
    step.                                 (* 0x1596c sw a5,348(a4): OW.t[n].state *)
    step.                                 (* 0x15970 sw a3,352(a4): OW.t[n].old *)
    step.                                 (* 0x15974 sw a5,356(a4): OW.t[n].reason *)
    step.                                 (* 0x15978 addi a2,a2,1 *)
    step.                                 (* 0x1597c sw a2,344(a1): OW.n *)
    step.                                 (* 0x15980 li a1,2 *)
    step.                                 (* 0x15984 sw a1,12(a0): M.state *)
    step.                                 (* 0x15988 ret *)
    unfold set_M_state, set_OW_n, set_OW_t_reason, set_OW_t_old, set_OW_t_state, set_M_next_ka.
    replace (A_OW_t_state (OW_n B)) with (65316 + 12 * OW_n B) by (unfold A_OW_t_state, OFF_OW; lia).
    replace (A_OW_t_old (OW_n B)) with (65320 + 12 * OW_n B) by (unfold A_OW_t_old, OFF_OW; lia).
    replace (A_OW_t_reason (OW_n B)) with (65324 + 12 * OW_n B) by (unfold A_OW_t_reason, OFF_OW; lia).
    rewrite ?le8_put, ?le4_put in WM.
    rewrite <- (mo_put8_ka (Cfg_keepalive_ms B) (M_last_rx B)).
    apply evt_done. hnf. do 16 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WO|]. split; [exact MI|]. split; [exact ST|exact WM].
Qed.
