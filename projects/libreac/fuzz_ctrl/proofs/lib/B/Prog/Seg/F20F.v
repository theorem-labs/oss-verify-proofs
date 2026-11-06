(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths, addresses and numbers changed; 555 of its 598 lines of code are new or changed and 353 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F20.v, with its module paths and module names changed; 135 of its 190 lines of code are new or changed and 543 lines of the source are left out. *)
(* rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source run: lib/B/Prog/Seg/F20.v lu_evt (:64) and seg_F20's own inline stretch 0x82668 -> 0x82728
     (:538-616) at a working branch 3803efccea0 (blob 9f1728fca2579f33a183d2fb3bd071b4db7471d9);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: lu_evt is the UL bridge that carries the reac_ctrl_checksum_verify contract into seg_F20's UL run;
     an _F stretch never runs a callee, so the bridge has no footprint twin.  The stretch is split at the call
     instead: seg_F20_pre_F re-runs F20.v:549-590 / 600-607 (0x82668 -> the callee entry 0x83b94,
     ra = 0x82728) and seg_F20_post_F re-runs F20.v:594-599 (the return pc 0x82728 -> the stretch's end, no
     step), with the callee post facts as premises. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ctrl_checksum_verify_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require F20.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module CKV := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_checksum_verify_c.
(* The short name PropExec resolves to the UL engine's copy here (the Seg chain loads it last), but StepF steps
   the lib.Lib engine: name its value functions explicitly. *)
Module LPE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.

Local Ltac acc_hint ::=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      match goal with
      | H : rng RNG E _ |- _ =>
          eapply rng_acc_litZ; [exact H | reflexivity | lia | split; lia]
      end
  end.

(* ---- The read facts and value normalisations of F20's run, over the lib.Lib engine (F20's own copies speak
   the UL engine's Mem / PropExec). ---- *)
Lemma f20_rd1_lib : forall m a b, bytes_at rsegs m a [b] -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof.
  intros m a b H.
  pose proof (bytes_at_ov_read rsegs m a [b] 0 1 H ltac:(cbn; lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r in HH. cbn [firstn skipn] in HH. exact HH.
Qed.
Lemma f20_rd2_lib : forall m a bs, bytes_at rsegs m a bs -> length bs = 2%nat ->
  ov_read_bytes rsegs m (wa a) 2 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (bytes_at_ov_read rsegs m a bs 0 2 H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by lia. exact HH.
Qed.
Lemma f20_rd8_lib : forall m a v, q64 m a v -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 (Z_to_bv 64 v)).
Proof.
  intros m a v H. unfold q64 in H.
  pose proof (bytes_at_ov_read rsegs m a _ 0 8 H ltac:(rewrite length_le8; lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH.
  rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by (rewrite length_le8; lia).
  exact HH.
Qed.
Lemma f20_ubv8_lib : forall v, 0 <= v < 256 -> bv_unsigned (zxb (Z_to_bv 8 v)) = v.
Proof.
  intros v Hv. unfold zxb. rewrite (unsigned_lit (bv_unsigned (Z_to_bv 8 v))).
  - rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia.
  - rewrite Z_to_bv_unsigned, (bv_wrap_small 8 v) by (unfold bv_modulus; cbn; lia). lia.
Qed.
Lemma f20_zxb8_lib : forall v, 0 <= v < 256 -> zxb (Z_to_bv 8 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold bv_modulus; cbn; lia.
Qed.
Lemma f20_seqz_v17_lib : forall v17, 0 <= v17 < 256 ->
  LPE.v_sltiu (zxb (Z_to_bv 8 v17)) 1 = Z_to_bv 64 (if v17 =? 0 then 1 else 0).
Proof.
  intros v17 Hv. unfold LPE.v_sltiu. rewrite f20_ubv8_lib by lia. change (bv_wrap 64 1) with 1%Z.
  replace (v17 <? 1) with (v17 =? 0) by
    (destruct (Z.eqb_spec v17 0); destruct (Z.ltb_spec v17 1); lia).
  destruct (v17 =? 0); reflexivity.
Qed.
Lemma f20_seqz_vs8_lib : forall vs8, 0 <= vs8 < 2 ^ 64 ->
  LPE.v_sltiu (Z_to_bv 64 (vs8 + -1)) 1 = Z_to_bv 64 (if vs8 =? 1 then 1 else 0).
Proof.
  intros vs8 Hv. unfold LPE.v_sltiu. rewrite unsigned_lit_wrap. change (bv_wrap 64 1) with 1%Z.
  destruct (Z.eq_dec vs8 0) as [->|H0].
  - change ((0 + -1) mod 2 ^ 64 <? 1) with false. reflexivity.
  - rewrite (Z.mod_small (vs8 + -1) (2 ^ 64)) by lia.
    replace (vs8 + -1 <? 1) with (vs8 =? 1) by
      (destruct (Z.eqb_spec vs8 1); destruct (Z.ltb_spec (vs8 + -1) 1); lia).
    destruct (vs8 =? 1); reflexivity.
Qed.
Lemma f20_cmp16_eq_lib : forall v14 v15 field16, 0 <= v14 < 256 -> 0 <= v15 < 256 -> field16 = v14 + 256 * v15 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb (Z_to_bv 8 v15))) 8)))
                    (bv_unsigned (zxb (Z_to_bv 8 v14))))
  = zx16 (Z_to_bv 64 field16).
Proof.
  intros v14 v15 field16 H14 H15 Hf.
  rewrite (f20_ubv8_lib v15), (f20_ubv8_lib v14) by lia.
  rewrite (unsigned_lit (Z.shiftl v15 8)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite Z.lor_comm, lor_shiftl8_add by lia.
  unfold zx16. rewrite (unsigned_lit field16) by lia.
  rewrite Z.mod_small by lia. subst field16. reflexivity.
Qed.

Ltac f20_ush := match goal with
  | |- context [Z.shiftr (bv_unsigned (Z_to_bv 64 ?X)) 3] => rewrite (unsigned_lit X) by lia
  end.

(* The footprint twin of seg_F20's inline stretch, up to the checksum callee's entry 0x83b94 (ra = 0x82728):
   the four one-byte instrumented checks on the record bytes Phi + 14 .. Phi + 17, the two record comparisons
   (the halfword at fr + 196 read through the spill [A + 280] = fr + 176), and `mv a0,s2 ; jal`.  It writes no
   memory. *)
Lemma seg_F20_pre_F : forall (RNG : footprint) (Q : _ -> Prop)
  (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8v s9 s10v s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
  (A fr phi k v14 v15 v16 v17 field16 : Z),
  a0v = Z_to_bv 64 0 -> s1v = Z_to_bv 64 A -> s2v = Z_to_bv 64 phi ->
  s8v = Z_to_bv 64 k -> s10v = Z_to_bv 64 ASAN_K ->
  0 < phi -> phi + 50 <= 2 ^ 64 -> 0 <= k < 2 ^ 64 ->
  0 <= v14 < 256 -> 0 <= v15 < 256 -> 0 <= v16 < 256 -> 0 <= v17 < 256 ->
  0 <= field16 < 2 ^ 16 ->
  q64 m (A + 280) (fr + 176) -> u16 m (fr + 196) field16 ->
  b8 m (phi + 14) v14 -> b8 m (phi + 15) v15 -> b8 m (phi + 16) v16 -> b8 m (phi + 17) v17 ->
  b8 m (Z.shiftr (phi + 14) 3 + ASAN_K) 0 -> b8 m (Z.shiftr (phi + 15) 3 + ASAN_K) 0 ->
  b8 m (Z.shiftr (phi + 16) 3 + ASAN_K) 0 -> b8 m (Z.shiftr (phi + 17) 3 + ASAN_K) 0 ->
  field16 = v14 + 256 * v15 ->
  (if v16 =? 0 then (if v17 =? 0 then 1 else 0) else 0) = (if k =? 1 then 1 else 0) ->
  rng RNG (A + 280) 8 -> rng RNG (fr + 196) 2 ->
  rng RNG (phi + 14) 1 -> rng RNG (phi + 15) 1 -> rng RNG (phi + 16) 1 -> rng RNG (phi + 17) 1 ->
  rng RNG (Z.shiftr (phi + 14) 3 + ASAN_K) 1 -> rng RNG (Z.shiftr (phi + 15) 3 + ASAN_K) 1 ->
  rng RNG (Z.shiftr (phi + 16) 3 + ASAN_K) 1 -> rng RNG (Z.shiftr (phi + 17) 3 + ASAN_K) 1 ->
  (forall a1' a2' a3' : word,
     Q (MS (mkR (Z_to_bv 64 0x82728) sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 phi) a1' a2' a3' a4 a5 a6 a7
            s2v s3 s4 s5 s6 s7 s8v s9 s10v s11 t3 t4 t5 t6)
         F (Z_to_bv 64 CKV.REAC_CTRL_CHECKSUM_VERIFY) fc None m (seg_rom rsegs))) ->
  evtF rsegs RNG Q
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8v s9 s10v s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x82668) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8v s9 s10v s11 t3 t4 t5 t6
    F fc m A fr phi k v14 v15 v16 v17 field16 -> -> -> -> ->
    Hphi0 Hphi50 Rtk Rv14 Rv15 Rv16 Rv17 Rf16 H280 Hfield Hb14 Hb15 Hb16 Hb17
    Hsh14 Hsh15 Hsh16 Hsh17 Heq1 Heq2
    R280 Rfield RB14 RB15 RB16 RB17 RS14 RS15 RS16 RS17 HQ.
  pose proof (f20_rd1_lib m _ _ Hsh14) as RD14. pose proof (f20_rd1_lib m _ _ Hsh15) as RD15.
  pose proof (f20_rd1_lib m _ _ Hsh16) as RD16. pose proof (f20_rd1_lib m _ _ Hsh17) as RD17.
  pose proof (f20_rd1_lib m _ _ Hb14) as RDb14. pose proof (f20_rd1_lib m _ _ Hb15) as RDb15.
  pose proof (f20_rd1_lib m _ _ Hb16) as RDb16. pose proof (f20_rd1_lib m _ _ Hb17) as RDb17.
  pose proof (f20_rd2_lib m _ _ Hfield ltac:(apply length_le2)) as RDfield.
  pose proof (f20_rd8_lib m _ _ H280) as RD280.
  assert (Ephi : bv_unsigned (Z_to_bv 64 phi) = phi) by (apply unsigned_lit; lia).
  (* 0x82668 bnez a0 : a0 = 0, not taken *)
  step. if_false.
  (* 0x8266c beqz s2 : the branch to 0x82fa0 is not taken because 0 < Phi *)
  step. if_false.
  (* 0x82670 li a0,-15 ; 0x82674 bltu a0,s2 : not taken *)
  step. step. if_false.
  (* 0x82678 li a0,-16 ; 0x8267c bltu a0,s2 : not taken *)
  step. step. if_false.
  (* 0x82680 addi ; srli ; add ; lb a1 = the shadow byte of Phi + 14, which is 0 *)
  step. step. step. rewrite (unsigned_lit (phi + 14)) by lia.
  step.
  (* 0x82690 ld a2,280(s1) = fr + 176 ; 0x82694 lhu a2,20(a2) = field16 ; 0x82698 bnez a1 (= 0) not taken *)
  step. step. step. if_false.
  (* 0x8269c addi ; srli ; add ; lb a3 = the shadow byte of Phi + 15 (0) *)
  step. step. step. rewrite (unsigned_lit (phi + 15)) by lia.
  step.
  (* 0x826ac lbu a0 = v14 ; 0x826b0 bnez a3 (= 0) not taken ; 0x826b4 lbu a1 = v15 ; slli ; or *)
  step. step. if_false. step. step. step.
  (* 0x826c0 bne a0,a2 : (v15 << 8) | v14 = field16, not taken *)
  step. rewrite (f20_cmp16_eq_lib v14 v15 field16 Rv14 Rv15 Heq1), bv_eqb_refl; cbn [negb]; cbv iota.
  (* 0x826c4 li a0,-17 ; 0x826c8 bltu a0,s2 : not taken *)
  step. step. if_false.
  (* 0x826cc addi ; srli ; add ; lb a1 = the shadow byte of Phi + 16 (0) *)
  step. step. step. rewrite (unsigned_lit (phi + 16)) by lia.
  step.
  (* 0x826dc bnez a1 (= 0) not taken ; 0x826e0 lbu a0 = v16 ; 0x826e4 beqz a0 *)
  step. if_false. step. step. rewrite (f20_zxb8_lib v16) by lia.
  destruct (Z.eq_dec v16 0) as [Hv16|Hv16].
  - (* v16 = 0 : beqz taken to 0x826f0 *)
    subst v16. rewrite bv_eqb_refl. cbv iota.
    (* 0x826f0 li a0,-18 ; 0x826f4 bltu a0,s2 : not taken *)
    step. step. if_false.
    (* 0x826f8 addi ; srli ; add ; lb a1 = the shadow byte of Phi + 17 (0) *)
    step. step. step. rewrite (unsigned_lit (phi + 17)) by lia.
    step.
    (* bnez a1 (= 0) ; lbu a0 = v17 ; seqz a0 ; addi a1,s8,-1 ; seqz a1 ; bne (the carried equality) *)
    step. if_false. step. step. step. step. step.
    rewrite (f20_seqz_v17_lib v17 Rv17), (f20_seqz_vs8_lib k Rtk).
    replace (0 =? 0) with true in Heq2 by reflexivity. cbv iota in Heq2.
    rewrite Heq2, bv_eqb_refl; cbn [negb]; cbv iota.
    (* 0x82720 mv a0,s2 ; 0x82724 jal reac_ctrl_checksum_verify *)
    step. step.
    apply evtF_done. apply HQ.
  - (* v16 <> 0 : beqz not taken, fall to 0x826e8 *)
    rewrite (F20.eqb0_false v16) by lia. cbv iota.
    (* 0x826e8 li a0,0 ; 0x826ec j 82714 ; 0x82714 addi a1,s8,-1 ; 0x82718 seqz a1 ; 0x8271c bne *)
    step. step. step. step. step.
    rewrite (f20_seqz_vs8_lib k Rtk).
    replace (v16 =? 0) with false in Heq2 by (symmetry; apply Z.eqb_neq; exact Hv16). cbv iota in Heq2.
    rewrite <- Heq2, bv_eqb_refl; cbn [negb]; cbv iota.
    step. step.
    apply evtF_done. apply HQ.
Qed.

(* The post half (F20.v:594-599): from the return pc 0x82728 there is no further instruction before the
   stretch's exit cut, so the post is the callee post facts themselves. *)
Lemma seg_F20_post_F : forall (RNG : footprint)
  (ra' sp gp tp t0' t1 t2 s0 s1v a1' a2' a3' a4' a5' a6' a7' s2v s3 s4 s5 s6 s7 s8v s9 s10v s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m m' : word -> option byte) (lo res : Z),
  munch [(bv_unsigned sp - CKV.REAC_CTRL_CHECKSUM_VERIFY_FRAME, bv_unsigned sp)] m m' ->
  wmono rsegs m m' -> stk rsegs m' lo (bv_unsigned sp) ->
  evtF rsegs RNG
    (fun ms'' => exists (ra'' t0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' : word) (m'' : word -> option byte),
       ms'' = MS (mkR ra'' sp gp tp t0'' t1 t2 s0 s1v (Z_to_bv 64 res) a1'' a2'' a3'' a4'' a5'' a6'' a7''
                      s2v s3 s4 s5 s6 s7 s8v s9 s10v s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x82728) fc None m'' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - CKV.REAC_CTRL_CHECKSUM_VERIFY_FRAME, bv_unsigned sp)] m m''
       /\ wmono rsegs m m'' /\ stk rsegs m'' lo (bv_unsigned sp))
    (MS (mkR ra' sp gp tp t0' t1 t2 s0 s1v (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7'
             s2v s3 s4 s5 s6 s7 s8v s9 s10v s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x82728) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG ra' sp gp tp t0' t1 t2 s0 s1v a1' a2' a3' a4' a5' a6' a7' s2v s3 s4 s5 s6 s7 s8v s9 s10v s11
    t3 t4 t5 t6 F fc m m' lo res MU WM ST.
  apply evtF_done.
  exists ra', t0', a1', a2', a3', a4', a5', a6', a7', m'.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM | exact ST].
Qed.
