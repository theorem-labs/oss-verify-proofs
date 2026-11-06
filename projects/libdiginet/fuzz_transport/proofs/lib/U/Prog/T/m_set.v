(* The walk of m_set in the ubsan image, against m_set_c.v. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TImg TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract m_set_c.
Import ListNotations.
Open Scope Z_scope.

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

Lemma br_ltu : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

(* The indexed OW.t stores form the address as (struct_base + 12*n) + field_off: two literals with
   the symbolic index between them, which the world store hook's wk_offset cannot read.  Fold the
   literals into the world offset and keep the base the NAME W_BASE_UBSAN, so wk_offset reads
   [W_BASE_UBSAN + k] directly and the cell machinery's literal [address - base] path stays off. *)
Ltac mset_fold_in E :=
  lazymatch E with
  | ?c1 + ?X + ?c2 =>
      is_Zlit_zb c1; is_Zlit_zb c2;
      let d := eval vm_compute in (Z.add c1 c2 - W_BASE_UBSAN)%Z in
      replace (c1 + X + c2) with (W_BASE_UBSAN + (d + X)) by (unfold W_BASE_UBSAN; lia)
  end.
Ltac mset_norm_addr :=
  try (lazymatch goal with
  | |- context [store_ok _ _ (Z_to_bv 64 ?E) _] => mset_fold_in E
  | |- context [write_to_mem _ (Z_to_bv 64 ?E) _] => mset_fold_in E
  | |- context [write_to_mem _ (wa ?E) _] => mset_fold_in E
  end).
Ltac solve_store ::= mset_norm_addr; wk_solve_store_world.
(* Side goals by lia only.  The kit's wk_side / wk_len_side fall through to wk_vm_close, which
   [vm_compute]s a goal still holding the open [Z_to_bv 64 st] of the stored bytes: the runaway
   TWorldMem.v warns about.  Rewrite [length] first and never [vm_compute]. *)
Ltac msafe := first [ lia | (unfold W_LEN, W_BASE_UBSAN in *; lia) ].
Ltac mlen := rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1; msafe.
(* Transport the world fact and the footprint across each world store with the kit's own lemmas
   (the kit's store_done takes the same runaway path on an indexed address). *)
Ltac mset_after :=
  try fix_lit_store; mset_norm_addr;
  lazymatch goal with
  | |- evt rsegs _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs) _) =>
      let E := addr_expr a in
      lazymatch goal with
      | WM : rw_cells rsegs m W_BASE_UBSAN [CB (Z.to_nat W_LEN) ?B] |- _ =>
          let k := wk_offset W_BASE_UBSAN a in
          assert (HS : store_ok rsegs m a (length bs) = true)
            by (apply (wm_store_ok rsegs W_BASE_UBSAN m B k (length bs) a WM); [ msafe | mlen | wk_addr_eq ]);
          let WMn := fresh "WMn" in
          assert (WMn : rw_cells rsegs (write_to_mem m a bs) W_BASE_UBSAN [CB (Z.to_nat W_LEN) (upd B k bs)])
            by (apply (wm_write_at rsegs W_BASE_UBSAN m B k bs E);
                [ exact WM | msafe | mlen | first [ reflexivity | (unfold W_BASE_UBSAN; lia) ] ]);
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

Theorem m_set_holds : m_set_contract.
Proof.
  unfold m_set_contract, m_set_ENTRY, m_set_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo B B' st why Ha0 Ha1 Hst Hwhy Hmod16 ST LO WOFF MI WM MODEL.
  subst a0 a1.
  pose proof (munch_refl [(bv_unsigned sp - 0, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  pose proof (s32_range B 12) as HM.
  wk_facts.
  step. step.
  change (s32_at B 12) with (M_state B) in *.
  step.
  rewrite (br_eqb (M_state B) st HM Hst).
  destruct (M_state B =? st) eqn:E.
  - (* M.state == st: no change, B' = B *)
    cbv iota.
    unfold m_set_m in MODEL. rewrite E in MODEL. injection MODEL as HB. subst B'.
    step.
    finish.
  - (* M.state <> st *)
    cbv iota.
    pose proof (s32_range B 65312) as HN.
    step. step. step.
    change (s32_at B 65312) with (OW_n B) in *.
    unfold m_set_m in MODEL. rewrite E in MODEL.
    step. step.
    rewrite (br_slt 15 (OW_n B) ltac:(lia) HN).
    destruct (15 <? OW_n B) eqn:Hblt; cycle 1.
    assert (Hle : OW_n B <= 15) by (apply Z.ltb_ge in Hblt; lia).
    replace (OW_n B <? TRANS_MAX) with true in MODEL
      by (symmetry; apply Z.ltb_lt; unfold TRANS_MAX; lia).
    assert (Hpos : 0 <= OW_n B).
    { destruct (Z_lt_le_dec (OW_n B) 0) as [Hlt|Hge]; [|lia].
      exfalso. replace (OW_n B <? 0) with true in MODEL by (symmetry; apply Z.ltb_lt; lia).
      cbn in MODEL. discriminate MODEL. }
    step. step.
    rewrite (br_ltu (OW_n B) 16 ltac:(lia) ltac:(lia)).
    replace (OW_n B <? 16) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn [negb]. cbv iota.
    do 3 step.
    assert (Ha6 : bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (OW_n B)) ≪ 4)) -
                  bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (OW_n B)) ≪ 2)) = 12 * OW_n B).
    { rewrite (unsigned_lit (OW_n B)) by lia.
      rewrite !Z.shiftl_mul_pow2 by lia.
      rewrite (unsigned_lit (OW_n B * 2^4)) by (change (2^4) with 16; lia).
      rewrite (unsigned_lit (OW_n B * 2^2)) by (change (2^2) with 4; lia).
      change (2^4) with 16. change (2^2) with 4. lia. }
    rewrite Ha6.
    do 2 step.
    step.
    rewrite (br_ltu 18446744073709276635 (12 * OW_n B) ltac:(lia) ltac:(lia)).
    replace (18446744073709276635 <? 12 * OW_n B) with false by (symmetry; apply Z.ltb_ge; lia).
    cbv iota.
    do 4 step.
    step. step.
    assert (Ha1 : bv_swrap 32 (bv_unsigned (Z_to_bv 64 (OW_n B)) + 1) = OW_n B + 1).
    { rewrite (unsigned_lit (OW_n B)) by lia. apply bv_swrap_small.
      change (bv_half_modulus 32) with (2^31). lia. }
    rewrite Ha1.
    rewrite (br_slt (OW_n B + 1) (OW_n B) ltac:(lia) HN).
    replace (OW_n B + 1 <? OW_n B) with false by (symmetry; apply Z.ltb_ge; lia).
    cbv iota.
    step. step. step.
    (* the model: B' is the five-field update *)
    replace (OW_n B <? 0) with false in MODEL by (symmetry; apply Z.ltb_ge; lia).
    replace (int_inc (OW_n B)) with (Some (OW_n B + 1)) in MODEL
      by (unfold int_inc; replace (OW_n B =? INT_MAX) with false
            by (symmetry; apply Z.eqb_neq; unfold INT_MAX; lia); reflexivity).
    cbv iota in MODEL. injection MODEL as HB. subst B'.
    unfold set_M_state, set_OW_n, set_OW_t_reason, set_OW_t_old, set_OW_t_state.
    replace (A_OW_t_state (OW_n B)) with (65316 + 12 * OW_n B) by (unfold A_OW_t_state, OFF_OW; lia).
    replace (A_OW_t_old (OW_n B)) with (65320 + 12 * OW_n B) by (unfold A_OW_t_old, OFF_OW; lia).
    replace (A_OW_t_reason (OW_n B)) with (65324 + 12 * OW_n B) by (unfold A_OW_t_reason, OFF_OW; lia).
    replace A_OW_n with 65312 by (unfold A_OW_n, OFF_OW; lia).
    replace A_M_state with 12 by (unfold A_M_state, OFF_M; lia).
    rewrite ?le4_put in WM.
    finish.
    (* OW_n B >= 16: the OW.t store is skipped (blt at 0x15e58 taken to 0x15e8c) *)
    assert (Hge : 16 <= OW_n B) by (apply Z.ltb_lt in Hblt; lia).
    replace (OW_n B <? TRANS_MAX) with false in MODEL
      by (symmetry; apply Z.ltb_ge; unfold TRANS_MAX; lia).
    assert (HnMax : OW_n B <> INT_MAX).
    { intro Heq. unfold int_inc in MODEL. rewrite Heq, Z.eqb_refl in MODEL.
      cbv iota in MODEL. discriminate MODEL. }
    step. step.
    assert (Ha1 : bv_swrap 32 (bv_unsigned (Z_to_bv 64 (OW_n B)) + 1) = OW_n B + 1).
    { rewrite (unsigned_lit (OW_n B)) by lia. apply bv_swrap_small.
      change (bv_half_modulus 32) with (2^31). unfold INT_MAX in HnMax. lia. }
    rewrite Ha1.
    rewrite (br_slt (OW_n B + 1) (OW_n B) ltac:(unfold INT_MAX in HnMax; lia) HN).
    replace (OW_n B + 1 <? OW_n B) with false by (symmetry; apply Z.ltb_ge; lia).
    cbv iota.
    step. step. step.
    replace (int_inc (OW_n B)) with (Some (OW_n B + 1)) in MODEL
      by (unfold int_inc; replace (OW_n B =? INT_MAX) with false
            by (symmetry; apply Z.eqb_neq; exact HnMax); reflexivity).
    cbv iota in MODEL. injection MODEL as HB. subst B'.
    unfold set_M_state, set_OW_n.
    replace A_OW_n with 65312 by (unfold A_OW_n, OFF_OW; lia).
    replace A_M_state with 12 by (unfold A_M_state, OFF_M; lia).
    rewrite ?le4_put in WM.
    finish.
Qed.
