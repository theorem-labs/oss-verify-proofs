(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpTac.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.A0.ICP Require Import IcptKit IcptKit2 F_rip F_irt I_printf_lib I_sscanf.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition imemset32_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (D : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(D, D + 32)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' D [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].
Lemma imemset32_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (D : Z) (junk : list byte),
  mem_inv asegs m -> rw_cells asegs m D [CB 32 junk] -> 0 <= D -> D + 32 < 2^64 -> D mod 16 = 0 ->
  evt asegs (imemset32_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 D m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz D) (wz 0) (wz 32) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x699b0) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros MI DC D0 DB AL.
  pose proof (munch_refl [(D, D + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep.
  assert (E0 : Z.land (Z.lor 32 D) 15 = 0).
  { rewrite Z.land_lor_distr_l. change 15 with (Z.ones 4). rewrite !Z.land_ones by lia. change (2^4) with 16. rewrite AL. reflexivity. }
  rewrite E0. zstep. lit_branch. zstep. lit_branch.
  do 7 zstep.
  zstep. zstep. fix_lit_store. zstep. fix_lit_store. zstep. zstep.
  if_cases K1; zify_cond K1. 2:{ exfalso. lia. }
  zstep. fix_lit_store. zstep. fix_lit_store. zstep. zstep.
  if_cases K2; zify_cond K2. { exfalso. lia. }
  zstep.
  unfold imemset32_post. finish.
Qed.

Section Blocks.
  Variables (F : bvmap 5 word) (fc : bv 32) (mc : mem) (P n : Z).
  Hypothesis MI : mem_inv asegs mc.
  Hypothesis ES : env_shadow mc.
  Hypothesis ACC : accessible mc P n.
  Hypothesis RD : sh_readable mc P n.
  Hypothesis WIN : cwin P n.
  Hypothesis W2 : P + n < 2^47.
  Hypothesis NS : 1 <= n <= 64.

  Definition blk_post (pcK : Z) (x1 x2 gp tp x5 x6 x7 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) : machine_state -> Prop :=
    fun ms' => exists a0 a1 a2 a3 a4,
      ms' = MS (mkR x1 x2 gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pcK) fc None mc (seg_rom asegs).

  #[using="WIN W2"] Lemma BLK : 0 <= P /\ P + n < 2^47.
  Proof. destruct WIN as [Hn W]. lia. Qed.

  Notation APOSTa x1 x2 gp tp x5 x6 x7 s0 s1 a5 a6 a7 s2 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6 :=
    (blk_post 0x481bc x1 x2 gp tp x5 x6 x7 s0 s1 a5 a6 a7 s2 s3 s4 s5 (wz P) (wz n) s8 s9 s10 s11 t3 t4 t5 t6) (only parsing).
  #[using="Type"] Lemma land_m64_small : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
  Proof. intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
  #[using="ACC WIN W2 NS"] Lemma LWLa : forall (j : nat) (cur : Z) x1 x2 gp tp x5 x6 x7 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6,
    Z.to_nat (sh (P + n - 1) - cur) = j -> sh P <= cur < sh (P + n - 1) ->
    evt asegs (APOSTa x1 x2 gp tp x5 x6 x7 s0 s1 a5 a6 a7 s2 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6)
      (MS (mkR x1 x2 gp tp x5 x6 x7 s0 s1 (wz cur) (wz (2147450880 + Z.shiftr (P + n + -1) 3)) (wz 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 (wz P) (wz n) s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x4833c) fc None mc (seg_rom asegs)).
  Proof.
    intros j. induction j as [|j IH]; intros until t6; intros Hk Hc; [exfalso; lia|]. pose proof BLK as BL0.
    assert (SL : sh (P + n - 1) = 2147450880 + Z.shiftr (P + n + -1) 3) by (unfold sh, SHADOW_OFF; rewrite shiftr3_div; replace (P + n + -1) with (P + n - 1) by lia; lia).
    pose proof (sh_div8 (P + n - 1)) as D1.
    pose proof (ov_read1_mrd mc cur _ ltac:(unfold sh, SHADOW_OFF in *; lia) ltac:(unfold sh, SHADOW_OFF in *; lia)
                  (acc_full_zero mc P n cur ACC ltac:(lia) ltac:(lia))) as RDc.
    assert (SHB : 0 <= Z.shiftr (P + n + -1) 3 < 2^44) by (rewrite shiftr3_div; Z.div_mod_to_equations; lia).
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K; rewrite ?land_m64_small in K by (unfold sh, SHADOW_OFF in *; lia).
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      apply evt_done. unfold blk_post. do 5 eexists. reflexivity.
  Qed.
  #[using="ACC WIN W2 NS"] Lemma LWSa : forall x1 x2 gp tp x5 x6 x7 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6,
    evt asegs (APOSTa x1 x2 gp tp x5 x6 x7 s0 s1 a5 a6 a7 s2 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6)
      (MS (mkR x1 x2 gp tp x5 x6 x7 s0 s1 (wz (2147450880 + Z.shiftr P 3)) (wz (2147450880 + Z.shiftr (P + n + -1) 3)) (wz (P + n + -1)) a3 a4 a5 a6 a7 s2 s3 s4 s5 (wz P) (wz n) s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x48320) fc None mc (seg_rom asegs)).
  Proof.
    intros. pose proof BLK as BL0.
    destruct (acc_byte_rd mc P n (P + n + -1) ACC ltac:(lia) ltac:(lia) ltac:(lia)) as (kk & RDk & CKk).
    unfold sh, SHADOW_OFF in RDk. rewrite <- shiftr3_div in RDk.
    zstep. rewrite (sxb_small kk) by lia. do 5 zstep.
    rewrite land7_mod8. rewrite (aip_zero ((P + n + -1) mod 8) kk) by (pose proof (Z.mod_pos_bound (P + n + -1) 8 ltac:(lia)); lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      apply evt_done. unfold blk_post. do 5 eexists. reflexivity.
    - eapply LWLa; [reflexivity |].
      rewrite !shiftr3_div in *. replace (P + n - 1) with (P + n + -1) by lia. unfold sh, SHADOW_OFF.
      assert (0 <= P / 8 < 2^44 /\ 0 <= (P + n + -1) / 8 < 2^44) as [B1 B2] by (split; Z.div_mod_to_equations; lia).
      rewrite ?land_m64_small in K6 by lia. rewrite ?Z.mod_small in K6 by lia. lia.
  Qed.

  #[using="ES ACC RD WIN W2 NS"] Lemma arg_block : forall x1 x2 gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6,
    evt asegs (APOSTa x1 x2 gp tp x5 x6 x7 s0 s1 a5 a6 a7 s2 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6)
      (MS (mkR x1 x2 gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (wz P) (wz n) s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x48180) fc None mc (seg_rom asegs)).
  Proof.
    intros. pose proof BLK as BL0. destruct ES as [GOT1 SHB1].
    do 11 zstep.
    probe8_regx 13%Z RD P w1 P1. probe8_regx 14%Z RD (P + n + -1) w2 P2.
    do 4 zstep. if_cases K5; zify_cond K5.
    - eapply LWSa.
    - apply evt_done. unfold blk_post. do 5 eexists. reflexivity.
  Qed.
End Blocks.

Section FBlock.
  Variables (F : bvmap 5 word) (fc : bv 32) (mc : mem) (P k : Z).
  Hypothesis MI : mem_inv asegs mc.
  Hypothesis ES : env_shadow mc.
  Hypothesis ACC : accessible mc P (k + 1).
  Hypothesis RD : sh_readable mc P (k + 1).
  Hypothesis WIN : cwin P (k + 1).
  Hypothesis W2 : P + (k + 1) < 2^47.
  Hypothesis NS : 0 <= k < 64.

  #[using="WIN W2 NS"] Lemma BLKf : 0 <= P /\ P + (k + 1) < 2^47.
  Proof. destruct WIN as [Hn W]. lia. Qed.

  Notation APOSTf x1 x2 gp tp x5 x6 x7 s0 s1 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 :=
    (blk_post F fc mc 0x47d24 x1 x2 gp tp x5 x6 x7 s0 s1 a5 a6 a7 s2 s3 (wz P) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) (only parsing).
  #[using="ACC WIN W2 NS"] Lemma LWLf : forall (j : nat) (cur : Z) x1 x2 gp tp x5 x6 x7 s0 s1 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6,
    Z.to_nat (sh (P + (k + 1) - 1) - cur) = j -> sh P <= cur < sh (P + (k + 1) - 1) ->
    evt asegs (APOSTf x1 x2 gp tp x5 x6 x7 s0 s1 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      (MS (mkR x1 x2 gp tp x5 x6 x7 s0 s1 (wz cur) (wz (2147450880 + Z.shiftr (k + P) 3)) (wz 0) a3 a4 a5 a6 a7 s2 s3 (wz P) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x486f4) fc None mc (seg_rom asegs)).
  Proof.
    intros j. induction j as [|j IH]; intros until t6; intros Hk Hc; [exfalso; lia|]. pose proof BLKf as BL0.
    assert (SL : sh (P + (k + 1) - 1) = 2147450880 + Z.shiftr (k + P) 3) by (unfold sh, SHADOW_OFF; rewrite shiftr3_div; replace (P + (k + 1) - 1) with (k + P) by lia; lia).
    pose proof (sh_div8 (P + (k + 1) - 1)) as D1.
    pose proof (ov_read1_mrd mc cur _ ltac:(unfold sh, SHADOW_OFF in *; lia) ltac:(unfold sh, SHADOW_OFF in *; lia)
                  (acc_full_zero mc P (k + 1) cur ACC ltac:(lia) ltac:(lia))) as RDc.
    assert (SHB : 0 <= Z.shiftr (k + P) 3 < 2^44) by (rewrite shiftr3_div; Z.div_mod_to_equations; lia).
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K; rewrite ?land_m64_small in K by (unfold sh, SHADOW_OFF in *; lia).
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      apply evt_done. unfold blk_post. do 5 eexists. reflexivity.
  Qed.

  #[using="ACC WIN W2 NS"] Lemma LWSf : forall x1 x2 gp tp x5 x6 x7 s0 s1 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6,
    evt asegs (APOSTf x1 x2 gp tp x5 x6 x7 s0 s1 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      (MS (mkR x1 x2 gp tp x5 x6 x7 s0 s1 (wz (2147450880 + Z.shiftr P 3)) (wz (2147450880 + Z.shiftr (k + P) 3)) (wz (k + P)) a3 a4 a5 a6 a7 s2 s3 (wz P) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x486d8) fc None mc (seg_rom asegs)).
  Proof.
    intros. pose proof BLKf as BL0.
    destruct (acc_byte_rd mc P (k + 1) (k + P) ACC ltac:(lia) ltac:(lia) ltac:(lia)) as (kk & RDk & CKk).
    unfold sh, SHADOW_OFF in RDk. rewrite <- shiftr3_div in RDk.
    zstep. rewrite (sxb_small kk) by lia. do 5 zstep.
    rewrite land7_mod8. rewrite (aip_zero ((k + P) mod 8) kk) by (pose proof (Z.mod_pos_bound (k + P) 8 ltac:(lia)); lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      apply evt_done. unfold blk_post. do 5 eexists. reflexivity.
    - eapply LWLf; [reflexivity |].
      rewrite !shiftr3_div in *. replace (P + (k + 1) - 1) with (k + P) by lia. unfold sh, SHADOW_OFF.
      assert (0 <= P / 8 < 2^44 /\ 0 <= (k + P) / 8 < 2^44) as [B1 B2] by (split; Z.div_mod_to_equations; lia).
      rewrite ?land_m64_small in K6 by lia. rewrite ?Z.mod_small in K6 by lia. lia.
  Qed.

  #[using="ES ACC RD WIN W2 NS"] Lemma fmt_block : forall x1 x2 gp tp x5 x6 x7 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6,
    evt asegs (APOSTf x1 x2 gp tp x5 x6 x7 s0 s1 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      (MS (mkR x1 x2 gp tp x5 x6 x7 s0 s1 (wz k) a1 a2 a3 a4 a5 a6 a7 s2 s3 (wz P) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x47cec) fc None mc (seg_rom asegs)).
  Proof.
    intros. pose proof BLKf as BL0. destruct ES as [GOT1 SHB1].
    do 10 zstep.
    probe8_regx 13%Z RD P w1 P1. probe8_regx 14%Z RD (k + P) w2 P2.
    do 4 zstep. if_cases K5; zify_cond K5.
    - eapply LWSf.
    - apply evt_done. unfold blk_post. do 5 eexists. reflexivity.
  Qed.
End FBlock.

Definition FSTR : list byte := [Z_to_bv 8 37; Z_to_bv 8 100; Z_to_bv 8 32; Z_to_bv 8 46; Z_to_bv 8 32; Z_to_bv 8 37; Z_to_bv 8 100; Z_to_bv 8 32; Z_to_bv 8 37; Z_to_bv 8 100].
Lemma fstr_at : forall m, mem_inv asegs m -> bytes_at asegs m A0_FMT (FSTR ++ Z_to_bv 8 0 :: []).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold A0_FMT; lia| unfold A0_FMT, FSTR; cbn [length app]; lia|].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
Lemma fstr_noz : Forall (fun b : byte => bv_unsigned b <> 0) FSTR. Proof. noz_tac. Qed.
Lemma fmt_rd : forall m (i : Z) b, mem_inv asegs m -> nth_error (FSTR ++ [Z_to_bv 8 0]) (Z.to_nat i) = Some b -> 0 <= i ->
  ov_read_bytes asegs m (wa (A0_FMT + i)) 1 = Some [b].
Proof. intros m i b MI Hn Hi. eapply u8ro_read; [apply fstr_at; exact MI | exact Hn | exact Hi | reflexivity]. Qed.
Lemma pat_rd : forall m, mem_inv asegs m -> ov_read_bytes asegs m (wa 0x103f8) 8 = Some (le8 (wz 0xaaaaaaaaaaaaaaaa)).
Proof.
  intros m MI.
  assert (B : bytes_at asegs m 0x103f8 (le8 (wz 0xaaaaaaaaaaaaaaaa))).
  { apply ro_bytes_at; [exact MI| lia| vm_compute; discriminate|]. apply ro_bytes_b_sound. vm_compute. reflexivity. }
  exact (ov_read_of_bytes_at m 0x103f8 _ B).
Qed.
Definition S_CCSSB : Z := 0x17b12.  Definition B_CCSSB : list byte := [Z_to_bv 8 99; Z_to_bv 8 67; Z_to_bv 8 115; Z_to_bv 8 83; Z_to_bv 8 91].
Lemma ccssb_bytes : forall m, mem_inv asegs m -> bytes_at asegs m S_CCSSB (B_CCSSB ++ Z_to_bv 8 0 :: []). Proof. img_str S_CCSSB B_CCSSB. Qed.
Lemma ccssb_noz : Forall (fun b : byte => bv_unsigned b <> 0%Z) B_CCSSB. Proof. noz_tac. Qed.

Ltac frd i :=
  lazymatch goal with MIc : mem_inv asegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let H := fresh "RDf" in
    pose proof (fmt_rd mm i _ MIc eq_refl ltac:(lia)) as H; unfold A0_FMT in H;
    let a := eval vm_compute in (137376 + i) in change (137376 + i) with a in H end.
Ltac frd_clear := repeat match goal with H : ov_read_bytes asegs _ (wa _) 1 = Some _ |- _ => clear H end.
Ltac fixq := repeat match goal with |- context [(?x - 4096)%Z] => replace (x - 4096) with (x + -4096) by lia end.
Ltac zl i := frd i; zstep; frd_clear; cbv beta; rewrite ?unsigned_lit8 by lia.
Ltac zz := zstep; fix_lit_store; try (timeout 5 lit_branch); fixq.   (* timeout-ok: on expiry try skips lit_branch and zz goes on; without this limit the build exceeds 250 GiB *)

Ltac strchr_res := repeat match goal with |- context [ifind_byte ?c ?B] => let t := eval vm_compute in (ifind_byte c B) in change (ifind_byte c B) with t end; cbv iota; rewrite ?unsigned_lit by lia.

Ltac strchr_call BYTES NOZ :=
  lazymatch goal with MIc : mem_inv asegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply istrchr_spec; [ exact MIc | rewrite unsigned_lit by (vm_compute; split; congruence); apply BYTES; exact MIc | exact NOZ | reflexivity | lia ]
    | post_call asegs mm ] end;
  unfold istrchr_res; strchr_res.

Ltac zto n := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) => tryif constr_eq p n then fail else zz end).

Ltac argblk IE HO A R W Pa :=
  lazymatch goal with MIc : mem_inv asegs ?mm, MUc : munch [(?lo, ?q)] ?m ?mm, WMc : wmono asegs ?m ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply arg_block with (P := Pa) (n := 4);
      first [ exact (ie_shadow _ (icpt_env_stack lo q m mm IE MUc WMc ltac:(lia)))
            | eapply accessible_munch; [exact A| exact MUc| exact W| intros s Hs; apply HO; lia]
            | eapply sh_readable_munch; [exact R| exact MUc| exact W| exact HO] | exact W | lia ]
    | let ms' := fresh "ms'" in intros ms' (?b0 & ?b1 & ?b2 & ?b3 & ?b4 & ->) ] end.
Ltac dirset qv Q16h :=
  lazymatch goal with DIRh : rw_cells asegs ?mm (qv + -2208) _, MIc : mem_inv asegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let dj := fresh "dj" in let DJ := fresh "DJ" in
    destruct (rw_cells_forget _ _ _ _ DIRh) as [dj DJ]; cbn [cells_size csize Nat.add] in DJ; clear DIRh;
    eapply evt_cut;
    [ eapply imemset32_spec with (D := (qv + -2208)%Z) (junk := dj); [ exact MIc | exact DJ | lia | lia | clear - Q16h; Z.div_mod_to_equations; lia ]
    | unfold imemset32_post; post_call asegs mm ] end;
  lazymatch goal with H : rw_cells asegs _ (qv + -2208) [C8 _; C8 _; C8 _; C8 _] |- _ =>
    apply (rw_cells_reshape asegs _ _ _ [C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 2 [Z_to_bv 8 0; Z_to_bv 8 0]]) in H;
    [ | cbn; repeat split; reflexivity | vm_compute; reflexivity | reflexivity ] end.
Ltac dirforget qv :=
  lazymatch goal with DIRh : rw_cells asegs _ (qv + -2208) _ |- _ =>
    let dj := fresh "dj" in let DJ := fresh "DJ" in
    destruct (rw_cells_forget _ _ _ _ DIRh) as [dj DJ]; cbn [cells_size csize Nat.add] in DJ; clear DIRh end.
Ltac fgvs_call qv lov :=
  lazymatch goal with D : rw_cells asegs ?mm (qv + -2208) [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10], MIc : mem_inv asegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let LMC := fresh "LMC" in
    pose proof (rw_cells_pick asegs mm (qv + -2208) [c0; c1; c2; c3; c4; c5] c6 [c7; c8; c9; c10] (qv + -2182) D ltac:(cbn [cells_size csize Nat.add]; lia)) as LMC;
    eapply evt_cut;
    [ eapply fgvs_specq with (lo := lov) (c := 100) (idx := 0%nat) (LM := (qv + -2182)%Z);
      [ exact MIc | eassumption | lia | lia | vm_compute; reflexivity | lia | exact LMC | lia | lia ]
    | post_call asegs mm ]; clear LMC end.
Ltac sc_exit qv :=
  do 16 zz;
  lazymatch goal with L : rw_cells asegs ?mm (qv + -2240) _, D : rw_cells asegs ?mm (qv + -2208) _, T : rw_cells asegs ?mm (qv + -2176) _, S : stk asegs ?mm _ (qv + -2240) |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    release_frame L S (qv + -2208)%Z; release_frame D S (qv + -2176)%Z; release_frame T S qv end;
  unfold sc_post; finish.

Ltac dir_head qv lov Q16h :=
  dirforget qv; zto 432560; dirset qv Q16h; zto 432740;
  strchr_call jzt_bytes jzt_noz; zto 432740;
  strchr_call ccssb_bytes ccssb_noz; zto 313960;
  fgvs_call qv lov;
  do 7 zz; change (Z.b2z (0 <? 18446744073709551606)) with 1.

Ltac arg_part Pv :=
  zto 295296;
  change (Z.land (Z.land (bv_swrap 32 (Z.b2z (6 <? 1) + -1)) 18446744073709551615) 4) with 4;
  rewrite ?(land_m64_small Pv) by lia; rewrite zb_lxor_ones by lia;
  let KO := fresh "KO" in if_cases KO; zify_cond KO; [ exfalso; lia | ];
  zto 295296.

Lemma scanf_common_spec : scanf_common_stmt.
Proof.
  unfold scanf_common_stmt, scanf_common_gen. intros until w3.
  intros MI IE ST KLO LO Q64 Q16 RR APC HW3E QAP APH AF RF A1 R1 W1 H1 A2 R2 W2 H2 A3 R3 W3 H3.
  rewrite (HW3E eq_refl) in APC. clear HW3E.
  unfold A0_scanf_common, SC_DEPTH, A0_FMT in *.
  pose proof (munch_refl [(lo, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (Q0 : 0 <= lo) by lia.
  carve_frame 2176%nat ST. rename FR into FRT. carve_frame 32%nat ST. rename FR into DIR. carve_frame 32%nat ST. rename FR into LOC.
  do 23 zstep.
  zstep.
  lazymatch goal with MIc : mem_inv asegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply istrlen_spec with (str := FSTR) (rest := []);
      [ exact MIc | rewrite unsigned_lit by lia; apply fstr_at; exact MIc | exact fstr_noz ]
    | post_call asegs mm ] end.
  change (Z.of_nat (length FSTR)) with 10.
  do 2 zstep.
  zstep. lit_branch. zstep. zstep. lit_branch.
  lazymatch goal with MIc : mem_inv asegs ?mm, MUc : munch [(lo, q)] m ?mm, WMc : wmono asegs m ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HO : forall s, 0x7fff7000 <= s < 0x10007fff8000 -> outside [(lo, q)] s) by (intros s Hs; cbn [outside]; lia);
    assert (CF : cwin 137376 11) by (unfold cwin; lia);
    assert (IEc : icpt_env mm) by (eapply icpt_env_stack; [exact IE| exact MUc| exact WMc| lia]);
    assert (AFc : accessible mm 137376 (10 + 1)) by (eapply accessible_munch; [exact AF| exact MUc| exact CF| intros s Hs; apply HO; lia]);
    assert (RFc : sh_readable mm 137376 (10 + 1)) by (eapply sh_readable_munch; [exact RF| exact MUc| exact CF| exact HO]);
    eapply evt_cut;
    [ eapply fmt_block with (P := 137376) (k := 10); first [ exact (ie_shadow _ IEc) | exact AFc | exact RFc | exact CF | lia ]
    | intros ms' (b0 & b1 & b2 & b3 & b4 & ->) ] end.
  clear AFc RFc IEc.
  zz. zz. zz. zl 0. zz.
  do 8 zz.
  lazymatch goal with MIc : mem_inv asegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (pat_rd mm MIc) as RDp end.
  zz. clear RDp.
  do 6 zz.
  assert (PB : 0 <= P1 /\ 0 <= P2 /\ 0 <= P3) by (destruct W1 as [_ ?]; destruct W2 as [_ ?]; destruct W3 as [_ ?]; lia).

  dir_head q lo Q16.
  rewrite (SFW1_lemmas.swrap32_small (r - 1)) by lia. zstep.
  assert (BL : bv_lts (Z_to_bv 64 (r - 1)) (Z_to_bv 64 0) = false) by (unfold bv_lts; rewrite !SFModel.signed_of_Z by lia; apply Z.ltb_ge; lia).
  rewrite BL. clear BL.
  arg_part P1. argblk IE HO A1 R1 W1 P1. zto 294260.

  dir_head q lo Q16.
  rewrite (SFW1_lemmas.swrap32_small (r - 1 - 1)) by lia. zstep.
  assert (BL : bv_lts (Z_to_bv 64 (r - 1 - 1)) (Z_to_bv 64 0) = (r - 1 - 1 <? 0)) by (unfold bv_lts; rewrite !SFModel.signed_of_Z by lia; reflexivity).
  rewrite BL. clear BL. destruct (Z.ltb_spec (r - 1 - 1) 0) as [RK|RK].
  {   sc_exit q. }
  arg_part P2. argblk IE HO A2 R2 W2 P2. zto 294260.

  dir_head q lo Q16.
  rewrite (SFW1_lemmas.swrap32_small (r - 1 - 1 - 1)) by lia. zstep.
  assert (BL : bv_lts (Z_to_bv 64 (r - 1 - 1 - 1)) (Z_to_bv 64 0) = (r - 1 - 1 - 1 <? 0)) by (unfold bv_lts; rewrite !SFModel.signed_of_Z by lia; reflexivity).
  rewrite BL. clear BL. destruct (Z.ltb_spec (r - 1 - 1 - 1) 0) as [RK2|RK2].
  {   sc_exit q. }
  arg_part P3. argblk IE HO A3 R3 W3 P3.

  zto 296476.
  sc_exit q.
Qed.

Definition FSTR2 : list byte := [Z_to_bv 8 37; Z_to_bv 8 100; Z_to_bv 8 32; Z_to_bv 8 46; Z_to_bv 8 32; Z_to_bv 8 37; Z_to_bv 8 100].
Lemma fstr2_at : forall m, mem_inv asegs m -> bytes_at asegs m A0_FMT2 (FSTR2 ++ Z_to_bv 8 0 :: []).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold A0_FMT2; lia| unfold A0_FMT2, FSTR2; cbn [length app]; lia|].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
Lemma fstr2_noz : Forall (fun b : byte => bv_unsigned b <> 0) FSTR2. Proof. noz_tac. Qed.
Lemma scanf_common2_spec : scanf_common2_stmt.
Proof.
  unfold scanf_common2_stmt, scanf_common_gen. intros until w3.
  intros MI IE ST KLO LO Q64 Q16 RR APC HW3E QAP APH AF RF A1 R1 W1 H1 A2 R2 W2 H2 A3 R3 W3 H3.
  clear HW3E.
  unfold A0_scanf_common, SC_DEPTH, A0_FMT2 in *.
  pose proof (munch_refl [(lo, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (Q0 : 0 <= lo) by lia.
  carve_frame 2176%nat ST. rename FR into FRT. carve_frame 32%nat ST. rename FR into DIR. carve_frame 32%nat ST. rename FR into LOC.
  do 23 zstep.
  zstep.
  lazymatch goal with MIc : mem_inv asegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply istrlen_spec with (str := FSTR2) (rest := []);
      [ exact MIc | rewrite unsigned_lit by lia; apply fstr2_at; exact MIc | exact fstr2_noz ]
    | post_call asegs mm ] end.
  change (Z.of_nat (length FSTR2)) with 7.
  do 2 zstep.
  zstep. lit_branch. zstep. zstep. lit_branch.
  lazymatch goal with MIc : mem_inv asegs ?mm, MUc : munch [(lo, q)] m ?mm, WMc : wmono asegs m ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HO : forall s, 0x7fff7000 <= s < 0x10007fff8000 -> outside [(lo, q)] s) by (intros s Hs; cbn [outside]; lia);
    assert (CF : cwin 137952 8) by (unfold cwin; lia);
    assert (IEc : icpt_env mm) by (eapply icpt_env_stack; [exact IE| exact MUc| exact WMc| lia]);
    assert (AFc : accessible mm 137952 (7 + 1)) by (eapply accessible_munch; [exact AF| exact MUc| exact CF| intros s Hs; apply HO; lia]);
    assert (RFc : sh_readable mm 137952 (7 + 1)) by (eapply sh_readable_munch; [exact RF| exact MUc| exact CF| exact HO]);
    eapply evt_cut;
    [ eapply fmt_block with (P := 137952) (k := 7); first [ exact (ie_shadow _ IEc) | exact AFc | exact RFc | exact CF | lia ]
    | intros ms' (b0 & b1 & b2 & b3 & b4 & ->) ] end.
  clear AFc RFc IEc.
  zz. zz. zz. zz. zz.
  do 8 zz.
  lazymatch goal with MIc : mem_inv asegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (pat_rd mm MIc) as RDp end.
  zz. clear RDp.
  do 6 zz.
  assert (PB : 0 <= P1 /\ 0 <= P2 /\ 0 <= P3) by (destruct W1 as [_ ?]; destruct W2 as [_ ?]; destruct W3 as [_ ?]; lia).

  dir_head q lo Q16.
  rewrite (SFW1_lemmas.swrap32_small (r - 1)) by lia. zstep.
  assert (BL : bv_lts (Z_to_bv 64 (r - 1)) (Z_to_bv 64 0) = false) by (unfold bv_lts; rewrite !SFModel.signed_of_Z by lia; apply Z.ltb_ge; lia).
  rewrite BL. clear BL.
  arg_part P1. argblk IE HO A1 R1 W1 P1. zto 294260.

  dir_head q lo Q16.
  rewrite (SFW1_lemmas.swrap32_small (r - 1 - 1)) by lia. zstep.
  assert (BL : bv_lts (Z_to_bv 64 (r - 1 - 1)) (Z_to_bv 64 0) = (r - 1 - 1 <? 0)) by (unfold bv_lts; rewrite !SFModel.signed_of_Z by lia; reflexivity).
  rewrite BL. clear BL. destruct (Z.ltb_spec (r - 1 - 1) 0) as [RK|RK].
  {   sc_exit q. }
  arg_part P2. argblk IE HO A2 R2 W2 P2.

  zto 296476.
  sc_exit q.
Qed.
