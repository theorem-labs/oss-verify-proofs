(* The walk of m_maybe_online in the ubsan image, against m_maybe_online_c.v. *)
(* m_maybe_online, entry 0x15dec (fuzz/fuzz_transport.c:237-243), no prologue. It reads M.state, M.e2_acked and
   M.e1_us; unless all three say WAKING with both flags set it returns at once (0x15e38) and the world is
   unchanged. Otherwise it stores M.next_ka = g_cfg.keepalive_ms * 1000 + M.last_rx (0x15e30) and tail-jumps to
   m_set (j 0x15e3c at 0x15e34) with a0 = S_ONLINE, a1 = R_ONLINE and the entry sp and ra: m_set's contract is
   the hypothesis of the theorem, and its post is the post here once the footprints are composed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TImg TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract m_maybe_online_c m_set_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- bridges: a register holding a 32-bit value, and the model's Z tests (U/Prog/T/m_set.v:13-34) ---- *)

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

(* ---- the bytes the machine writes at M.next_ka are the model's u64 sum ---- *)

Lemma mo_put8_ka : forall k l, put 8 (k * 1000 + l) = put 8 (u64 (l + h_ms_m k)).
Proof.
  intros k l. unfold h_ms_m, u64.
  rewrite <- (put_mod64 8 (k * 1000 + l)) by lia. f_equal.
  rewrite Z.add_mod_idemp_r by lia. f_equal. lia.
Qed.

(* ---- the world store (U/Prog/T/m_set.v:62-96; the one store here has a literal address) ----
   Side goals by lia only: the kit's wk_side / wk_len_side fall through to wk_vm_close, which [vm_compute]s a goal
   still holding the open [Z_to_bv 64 _] of the stored bytes. *)
Ltac msafe := first [ lia | (unfold W_LEN, W_BASE_UBSAN in *; lia) ].
Ltac mlen := rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1; msafe.
Ltac mset_after :=
  try fix_lit_store;
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

Theorem m_maybe_online_holds : m_set_contract -> m_maybe_online_contract.
Proof.
  intros MSET.
  unfold m_maybe_online_contract, m_maybe_online_ENTRY, m_maybe_online_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo B B' Hsp ST LO WOFF MI WM MODEL.
  assert (RST : -2^31 <= M_state B < 2^31) by apply (s32_range B A_M_state).
  assert (RE2 : -2^31 <= M_e2_acked B < 2^31) by apply (s32_range B A_M_e2_acked).
  assert (RE1 : -2^31 <= M_e1_us B < 2^31) by apply (s32_range B A_M_e1_us).
  assert (RKA : 0 <= Cfg_keepalive_ms B < 2^32)
    by (pose proof (u_at_range B A_Cfg_keepalive_ms 4) as HR;
        change (8 * Z.of_nat 4)%Z with 32%Z in HR; exact HR).
  pose proof (munch_refl [(bv_unsigned sp - 0, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WO.
  wk_facts.
  unfold m_maybe_online_m, S_WAKING, S_ONLINE, R_ONLINE, truth in MODEL.
  step.                                   (* 0x15dec auipc a0, 0x1d *)
  step.                                   (* 0x15df0 addi a2,a0,1300: a2 = W_BASE_UBSAN *)
  step.                                   (* 0x15df4 lw a0,12(a2): M.state *)
  change (s32_at B 12) with (M_state B).
  step.                                   (* 0x15df8 li a1,1 *)
  step.                                   (* 0x15dfc bne a0,a1,0x15e38 *)
  rewrite (br_eqb (M_state B) 1) by lia.
  destruct (Z.eqb_spec (M_state B) 1) as [EST|EST]; cbn [negb andb] in MODEL |- *; cbv iota.
  2: { assert (EB : B' = B) by congruence; subst B'.
       step.                              (* 0x15e38 ret *)
       apply evt_done. hnf. do 16 eexists. split; [reflexivity|].
       split; [exact MU|]. split; [exact WO|]. split; [exact MI|]. split; [exact ST|exact WM]. }
  step.                                   (* 0x15e00 lw a0,16(a2): M.e2_acked *)
  change (s32_at B 16) with (M_e2_acked B).
  step.                                   (* 0x15e04 beqz a0,0x15e38 *)
  rewrite (br_eqb (M_e2_acked B) 0) by lia.
  destruct (Z.eqb_spec (M_e2_acked B) 0) as [EE2|EE2]; cbn [negb andb] in MODEL |- *; cbv iota.
  1: { assert (EB : B' = B) by congruence; subst B'.
       step.                              (* 0x15e38 ret *)
       apply evt_done. hnf. do 16 eexists. split; [reflexivity|].
       split; [exact MU|]. split; [exact WO|]. split; [exact MI|]. split; [exact ST|exact WM]. }
  step.                                   (* 0x15e08 lw a0,20(a2): M.e1_us *)
  change (s32_at B 20) with (M_e1_us B).
  step.                                   (* 0x15e0c beqz a0,0x15e38 *)
  rewrite (br_eqb (M_e1_us B) 0) by lia.
  destruct (Z.eqb_spec (M_e1_us B) 0) as [EE1|EE1]; cbn [negb andb] in MODEL |- *; cbv iota.
  1: { assert (EB : B' = B) by congruence; subst B'.
       step.                              (* 0x15e38 ret *)
       apply evt_done. hnf. do 16 eexists. split; [reflexivity|].
       split; [exact MU|]. split; [exact WO|]. split; [exact MI|]. split; [exact ST|exact WM]. }
  (* the taken branch: MODEL is m_set_m (set_M_next_ka B KA) S_ONLINE R_ONLINE = Some (B', tt), m_set's premise *)
  step.                                   (* 0x15e10 auipc a0, 0x2d *)
  step.                                   (* 0x15e14 lwu a0,776(a0): g_cfg.keepalive_ms *)
  change (u_at B 65048 4) with (Cfg_keepalive_ms B).
  step.                                   (* 0x15e18 ld a1,32(a2): M.last_rx *)
  change (u_at B 32 8) with (M_last_rx B).
  step.                                   (* 0x15e1c li a3,1000 *)
  step.                                   (* 0x15e20 mul a3,a0,a3 *)
  rewrite (unsigned_lit (Cfg_keepalive_ms B)) by lia.
  step.                                   (* 0x15e24 li a0,2 *)
  step.                                   (* 0x15e28 add a3,a3,a1 *)
  step.                                   (* 0x15e2c li a1,2 *)
  step.                                   (* 0x15e30 sd a3,48(a2): M.next_ka *)
  rewrite le8_put, (mo_put8_ka (Cfg_keepalive_ms B) (M_last_rx B)) in WM.
  step.                                   (* 0x15e34 j 0x15e3c <m_set> *)
  eapply evt_mono.
  { eapply MSET;
      [ reflexivity | reflexivity | lia | lia | exact Hsp | exact ST | exact LO | exact WOFF | exact MI
      | exact WM | exact MODEL ]. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              -> & MUc & WOc & MIc & STc & WMc).
  cbv beta. do 16 eexists. split; [reflexivity|].
  split; [eapply munch_trans; [exact MU | exact MUc]|].
  split; [eapply wmono_trans; [exact WO | exact WOc]|].
  split; [exact MIc|]. split; [exact STc|exact WMc].
Qed.
