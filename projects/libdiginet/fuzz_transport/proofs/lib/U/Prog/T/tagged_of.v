(* The walk of tagged_of in the ubsan image, against tagged_of_c.v. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem tagged_of_c.
Import ListNotations.
Open Scope Z_scope.

(* tagged_of (0x155f4-0x15664), a leaf: no stack, no store. The walk follows the C (fuzz_transport.c:609-615):
     0x155f8 bltu n, 3        -> 0x1565c (return NULL)
     0x155fc beqz b           -> 0x15664 (UBSan trap: NULL b; closed by 0 < p)
     0x15608 bne b[0], 0xa0   -> 0x1565c
     0x15614 bgeu 1, b + 2    -> trap (pointer overflow; closed by the bound of b)
     0x15630 bgeu serial, g_ncmd (lw at 0x430d8 = W_BASE_UBSAN + OFF_g_ncmd, sign-extended) -> 0x1565c
     0x15638 bgeu serial, 1025 -> trap (g_cmd[serial] out of bounds; closed by the model's Some)
     0x15650 bltu ~&g_cmd, 40 * serial -> trap (pointer overflow; closed by serial < 1024)
     0x15654 a0 = &g_cmd[serial] = 0x380c8 + 40 * serial *)

(* lw sign-extends the 32-bit g_ncmd and bgeu compares unsigned: for serial < 2^31 this is serial < g_ncmd. *)
Lemma tg_ncmd_lt : forall s B, 0 <= s < 2^31 ->
  (s < s32_at B 64984 mod 18446744073709551616 <-> s < g_ncmd B).
Proof.
  intros s B Hs. unfold s32_at, g_ncmd, OFF_g_ncmd.
  pose proof (u_at_range B 64984 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  set (g := u_at B 64984 4) in *.
  assert (E : bv_swrap 32 g = (g + 2^31) mod 2^32 - 2^31) by reflexivity.
  rewrite E.
  destruct (Z_lt_le_dec g (2^31)) as [L|L].
  - rewrite (Z.mod_small (g + 2^31) (2^32)) by lia.
    replace (g + 2^31 - 2^31) with g by lia.
    rewrite (Z.mod_small g) by lia. split; intro; lia.
  - replace (g + 2^31) with ((g - 2^31) + 1 * 2^32) by lia.
    rewrite Z.mod_add by lia. rewrite (Z.mod_small (g - 2^31) (2^32)) by lia.
    replace (g - 2^31 - 2^31) with ((g - 2^32 + 18446744073709551616) + (-1) * 18446744073709551616) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. split; intro; lia.
Qed.

(* a branch condition after zify_cond: drop the 64-bit wrap of a value known to be in range *)
Ltac tg_norm H x :=
  rewrite ?(unsigned_lit x) in H by (lia);
  rewrite ?(Z.mod_small x 18446744073709551616) in H by (lia).

Theorem tagged_of_holds : tagged_of_contract.
Proof.
  unfold tagged_of_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo B B' p n b t -> -> Hn Hp HB S16 ST LO WOS MI WM HM.
  pose proof (munch_refl [(bv_unsigned sp - tagged_of_FRAME, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMO.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  (* 0x1565c: li a0, 0; ret *)
  assert (RET0 : forall a0v a1v a2v : word, B' = B -> t = None ->
    evt rsegs QQ (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0v a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1565c) fc None m (seg_rom rsegs))).
  { intros a0v a1v a2v EB Et.
    step. step.
    apply evt_done. unfold QQ. clear QQ. subst B' t.
    do 15 eexists. split; [reflexivity|].
    exact (conj MU (conj WMO (conj MI (conj ST (conj eq_refl WM))))). }
  unfold tagged_of_m in HM.
  unfold tagged_of_ENTRY.
  step.                                              (* li a2, 3 *)
  step.                                              (* bltu a1, a2: n < 3 *)
  if_cases H1; zify_cond H1; tg_norm H1 n.
  { rewrite (proj2 (Z.ltb_lt n 3) ltac:(lia)) in HM. injection HM as EB Et. apply RET0; congruence. }
  rewrite (proj2 (Z.ltb_ge n 3) ltac:(lia)) in HM.
  destruct b as [|b0 r0].
  { cbn [length Nat.ltb Nat.leb] in HM. discriminate HM. }
  pose proof (bytes_at_bound rsegs m p _ HB) as BB. cbn [length] in BB.
  assert (U0 : 0 <= bv_unsigned b0 < 256)
    by (pose proof (bv_unsigned_in_range 8 b0) as X; unfold bv_modulus in X; exact X).
  step.                                              (* beqz a0: the UBSan trap on NULL b *)
  if_cases H2; zify_cond H2; tg_norm H2 p.
  { exfalso. lia. }
  pose proof (u8ro_read rsegs m p (b0 :: r0) 0 b0 (Z_to_bv 64 (p + 0)) HB eq_refl ltac:(lia) eq_refl) as R0.
  step.                                              (* lbu a1, 0(a0) *)
  step. step.                                        (* li a2, 160; bne a1, a2 *)
  cbn [length Nat.ltb Nat.leb] in HM.
  change (at8 (b0 :: r0) 0) with (bv_unsigned b0) in HM. change TAG with 160 in HM.
  if_cases H3; zify_cond H3; tg_norm H3 (bv_unsigned b0).
  { rewrite (proj2 (Z.eqb_neq (bv_unsigned b0) 160) H3) in HM. cbn [negb] in HM.
    injection HM as EB Et. apply RET0; congruence. }
  rewrite (proj2 (Z.eqb_eq (bv_unsigned b0) 160) H3) in HM. cbn [negb] in HM.
  destruct r0 as [|b1 [|b2 r]].
  1-2: (cbn [length Nat.ltb Nat.leb] in HM; discriminate HM).
  cbn [length Nat.ltb Nat.leb] in HM. cbn [length] in BB.
  change (at8 (b0 :: b1 :: b2 :: r) 1) with (bv_unsigned b1) in HM.
  change (at8 (b0 :: b1 :: b2 :: r) 2) with (bv_unsigned b2) in HM.
  assert (U1 : 0 <= bv_unsigned b1 < 256)
    by (pose proof (bv_unsigned_in_range 8 b1) as X; unfold bv_modulus in X; exact X).
  assert (U2 : 0 <= bv_unsigned b2 < 256)
    by (pose proof (bv_unsigned_in_range 8 b2) as X; unfold bv_modulus in X; exact X).
  step. step. step.                                  (* addi a1, a0, 2; li a2, 1; bgeu a2, a1: b + 2 wraps *)
  if_cases H4; zify_cond H4; tg_norm H4 (p + 2).
  { exfalso. lia. }
  pose proof (u8ro_read rsegs m p (b0 :: b1 :: b2 :: r) 1 b1 (Z_to_bv 64 (p + 1)) HB eq_refl ltac:(lia) eq_refl)
    as R1.
  pose proof (u8ro_read rsegs m p (b0 :: b1 :: b2 :: r) 2 b2 (Z_to_bv 64 (p + 2)) HB eq_refl ltac:(lia) eq_refl)
    as R2.
  step. step.                                        (* lbu a1, 1(a0); lbu a0, 2(a0) *)
  step. step.                                        (* auipc a2; lw a2, g_ncmd: the world hook reads s32_at B 64984 *)
  step. step.                                        (* slli a0, a0, 7; or a0, a0, a1: serial *)
  unfold zxb.
  rewrite (unsigned_lit (bv_unsigned b2)) by lia.
  rewrite (unsigned_lit (bv_unsigned b1)) by lia.
  rewrite (unsigned_lit (Z.shiftl (bv_unsigned b2) 7)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  assert (SR : 0 <= Z.lor (Z.shiftl (bv_unsigned b2) 7) (bv_unsigned b1) < 2^15).
  { apply lor_lt_pow2; [rewrite Z.shiftl_mul_pow2 by lia; lia | lia]. }
  rewrite (Z.lor_comm (bv_unsigned b1)) in HM.
  remember (Z.lor (Z.shiftl (bv_unsigned b2) 7) (bv_unsigned b1)) as ser eqn:ES.
  step.                                              (* bgeu a0, a2: serial >= g_ncmd *)
  if_cases H5; zify_cond H5; tg_norm H5 ser.
  { assert (G : ~ ser < g_ncmd B) by (intro X; apply (proj2 (tg_ncmd_lt ser B ltac:(lia))) in X; lia).
    rewrite (proj2 (Z.ltb_ge ser (g_ncmd B)) ltac:(lia)) in HM. cbv iota in HM.
    injection HM as EB Et. apply RET0; congruence. }
  apply (proj1 (tg_ncmd_lt ser B ltac:(lia))) in H5.
  rewrite (proj2 (Z.ltb_lt ser (g_ncmd B)) H5) in HM. cbv iota in HM.
  destruct (Z_lt_le_dec ser CMDS_MAX) as [CM|CM].
  2: { rewrite (proj2 (Z.leb_le CMDS_MAX ser) CM) in HM. cbv iota in HM. discriminate HM. }
  rewrite (proj2 (Z.leb_gt CMDS_MAX ser) CM) in HM. cbv iota in HM.
  injection HM as EB Et.
  unfold CMDS_MAX in CM.
  step. step.                                        (* li a1, 1025; bgeu a0, a1: g_cmd[serial] out of bounds *)
  if_cases H6; zify_cond H6; tg_norm H6 ser.
  { exfalso. lia. }
  step. step. step. step. step.                      (* li a1, 40; auipc a2; mul a0; addi a1 (&g_cmd); not a2 *)
  rewrite ?(unsigned_lit ser) by lia.
  step.                                              (* bltu a2, a0: &g_cmd + 40 * serial wraps *)
  if_cases H7; zify_cond H7; tg_norm H7 (ser * 40).
  { exfalso. lia. }
  step.                                              (* add a0, a1, a0 *)
  step.                                              (* ret *)
  rewrite ?(unsigned_lit ser) by lia.
  lazymatch goal with |- context [Z_to_bv 64 (229576 + ?e)] =>
    replace (Z_to_bv 64 (229576 + e)) with (Z_to_bv 64 (tagged_of_ret (Some ser)))
      by (f_equal; rewrite ?(unsigned_lit ser) by lia;
          change (tagged_of_ret (Some ser)) with (W_BASE_UBSAN + A_Cmd_st ser);
          unfold W_BASE_UBSAN, A_Cmd_st, OFF_g_cmd; lia)
  end.
  apply evt_done. unfold QQ. clear RET0 QQ. subst B' t.
  do 15 eexists. split; [reflexivity|].
  exact (conj MU (conj WMO (conj MI (conj ST (conj eq_refl WM))))).
Qed.
