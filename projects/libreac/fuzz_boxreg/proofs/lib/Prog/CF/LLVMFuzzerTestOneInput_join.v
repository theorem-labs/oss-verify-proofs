(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/ZBridge.v; 281 of its 298 lines of code are new or changed and 392 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Prog/CF/LLVMFuzzerTestOneInput_seg.v; 393 of its 444 lines of code are new or changed and 247 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Contract Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import Boxreg BoxregRd.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import check_c bcmp_c strncmp_c reac_boxreg_find.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog.CF Require Import
LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog.CF Require Import SRCF.
Import ListNotations.
Open Scope Z_scope.

Lemma jn_m56 : forall z, 0 <= z < 2 ^ 32 ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 z)) 6)) -
              bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 z)) 3))) = Z_to_bv 64 (56 * z).
Proof.
  intros z Hz. rewrite (unsigned_lit z) by lia. rewrite !Z.shiftl_mul_pow2 by lia.
  change (2 ^ 6) with 64. change (2 ^ 3) with 8. rewrite !unsigned_lit by lia. f_equal. lia.
Qed.

Lemma jn_rd8 : forall m a v, bytes_at rsegs m a (le8 v) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 v).
Proof.
  intros m a v H. rewrite <- (Z.add_0_r a) at 1.
  rewrite (bytes_at_read rsegs m a _ 0 8 H) by (rewrite ?length_le8; lia).
  first [ reflexivity | f_equal; apply firstn_all2; rewrite length_le8; lia ].
Qed.

Lemma jn_strncmp_walk : forall l k, (k < length l)%nat -> strncmp_walk l l k = Some 0.
Proof.
  induction l as [|a l IH]; intros k H; cbn [length] in H; [lia|].
  cbn [strncmp_walk]. rewrite Z.eqb_refl, Z.sub_diag.
  match goal with |- (if ?c then _ else _) = _ => destruct c end; [reflexivity|].
  destruct k as [|k]; [reflexivity|]. apply IH. lia.
Qed.

Lemma jn_strncmp : forall l, length l = 32%nat -> strncmp_model l l 32 = Some 0.
Proof.
  intros l H. unfold strncmp_model. change (32 =? 0) with false. cbv iota.
  change (Z.to_nat (32 - 1)) with 31%nat. apply jn_strncmp_walk. lia.
Qed.

Lemma jn_mem_inv : forall lo hi m m', mem_inv rsegs m -> munch [(lo, hi)] m m' -> LF_RES_TOP <= lo ->
  mem_inv rsegs m'.
Proof.
  intros lo hi m m' MI MU HL a b E.
  destruct (Z_le_dec lo (bv_unsigned a)) as [H1|H1]; [destruct (Z_lt_dec (bv_unsigned a) hi) as [H2|H2]|].
  - unfold ro_addr. destruct (find_segment rsegs (bv_unsigned a) 1) as [seg|] eqn:Fs; [|reflexivity].
    pose proof (lf_find_top _ _ _ Fs). lia.
  - rewrite (MU a) in E by (cbn [outside]; split; [lia | exact I]). exact (MI a b E).
  - rewrite (MU a) in E by (cbn [outside]; split; [lia | exact I]). exact (MI a b E).
Qed.

Lemma jn_cell_bytes : forall m A pre c post, rw_cells rsegs m A (pre ++ c :: post) ->
  bytes_at rsegs m (A + Z.of_nat (cells_size pre)) (cbytes c).
Proof.
  intros m A pre c post [[Hwf Hb] _]. apply cells_wf_app in Hwf. destruct Hwf as [Hw1 _].
  rewrite cells_bytes_app in Hb. cbn [cells_bytes] in Hb.
  apply (proj1 (bytes_at_app rsegs _ _ _ _)) in Hb. destruct Hb as [_ Hb].
  rewrite cells_bytes_length in Hb by exact Hw1.
  apply (proj1 (bytes_at_app rsegs _ _ _ _)) in Hb. destruct Hb as [Hb _]. exact Hb.
Qed.

Lemma jn_munch : forall W m mm m2, munch W m mm -> munch [] mm m2 -> munch W m m2.
Proof.
  intros W m mm m2 H1 H2. eapply munch_trans; [exact H1|]. eapply munch_weaken; [|exact H2].
  unfold sub_fp. intros; exact I.
Qed.

Lemma jn_zero : forall m, mem_inv rsegs m -> bytes_at rsegs m ZERO_ADDR zero6.
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | unfold ZERO_ADDR; lia | cbn [length zero6 repeat]; unfold ZERO_ADDR; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Ltac jn_eq := first [ fnd_eq | apply jn_m56; lia ].

Definition jn_Q (sp gp tp s0 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (i inn : Z) : machine_state -> Prop :=
  fun ms' => exists (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31
                     pc : word) (m' : word -> option byte),
    ms' = MS (mkR x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 s9 s10 s11
                  x28 x29 x30 x31) F pc fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
    ((pc = Z_to_bv 64 0x12d30 /\ i <= 62 /\ inn <> 0 /\ x21 = Z_to_bv 64 inn /\ x24 = Z_to_bv 64 (i + 1)) \/
     pc = Z_to_bv 64 0x13408).

Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis CHECK : check_contract.
Hypothesis BCMP : bcmp_contract.
Hypothesis STRNCMP : strncmp_contract.

Lemma jn_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo r fab rr ren i inn : Z) (bs bs' : list byte),
    s0 = Z_to_bv 64 r -> s3 = Z_to_bv 64 rr -> s8 = Z_to_bv 64 i -> s10 = Z_to_bv 64 (bv_unsigned sp + 32) ->
    s11 = Z_to_bv 64 fab ->
    bytes_at rsegs m (bv_unsigned sp + 32) bs -> bytes_at rsegs m r bs' ->
    bytes_at rsegs m (bv_unsigned sp + 336) (le8 (Z_to_bv 64 inn)) ->
    length bs = 288%nat -> boxreg_B1 bs -> boxreg_B16 bs' -> bx_fabric bs' = fab -> llvm_kept bs bs' ren ->
    0 <= rr < 2 ^ 32 -> (rr = ren \/ ren = -1) -> 0 <= i <= 63 -> 0 <= inn < 2 ^ 64 ->
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> LF_RES_TOP <= lo -> lo + 112 <= bv_unsigned sp ->
    bv_unsigned sp + 448 <= 2 ^ 64 -> 0 <= r -> r + 288 <= lo ->
    evt rsegs (jn_Q sp gp tp s0 s9 s10 s11 F fc m i inn)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13314) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo r fab rr ren i inn bs bs' -> -> -> -> -> HP HR HN Lbs B1 B16 Hfab KEPT Rrr Hrr Hi Hinn MI ST Hlo Hlo2 Hsp Hr0 Hr.
  pose proof CHECK as CK. unfold check_contract, check_c.CHECK, CHECK_FRAME in CK.
  pose proof BCMP as BC. unfold bcmp_contract, bcmp_c.BCMP in BC.
  pose proof STRNCMP as SC. unfold strncmp_contract, strncmp_c.STRNCMP in SC.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  pose proof B16 as (Lbs' & B1' & B2' & B3' & B4' & B5' & B6').
  unfold boxreg_B1 in B1.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  assert (EPI : forall (mm : word -> option byte)
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word),
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m mm -> wmono rsegs m mm ->
    bytes_at rsegs mm (bv_unsigned sp + 336) (le8 (Z_to_bv 64 inn)) ->
    evt rsegs QQ (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 r) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                          x22 x23 (Z_to_bv 64 i) s9 (Z_to_bv 64 (bv_unsigned sp + 32)) (Z_to_bv 64 fab)
                          x28 x29 x30 x31)
                     F (Z_to_bv 64 0x133bc) fc None mm (seg_rom rsegs))).
  { intros mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 MU0 WM0 HN0.
    step. step. if_cases HC; zify_cond HC; rewrite ?unsigned_lit in HC by lia.
    - apply evt_done. unfold QQ, jn_Q. do 25 eexists. exists mm.
      split; [reflexivity|]. split; [exact MU0|]. split; [exact WM0|]. right. reflexivity.
    - pose proof (jn_rd8 _ _ _ HN0) as RD.
      step. step. rewrite ?fnd_addiw by lia. step.
      if_cases HZ; zify_cond HZ; rewrite ?unsigned_lit in HZ by lia.
      + apply evt_done. unfold QQ, jn_Q. do 25 eexists. exists mm.
        split; [reflexivity|]. split; [exact MU0|]. split; [exact WM0|].
        left. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [reflexivity | fnd_eq].
      + step. apply evt_done. unfold QQ, jn_Q. do 25 eexists. exists mm.
        split; [reflexivity|]. split; [exact MU0|]. split; [exact WM0|]. right. reflexivity. }
  assert (LOOP : forall (k : nat) (j : Z) (mm : word -> option byte)
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 : word),
    k = Z.to_nat (bx_n bs - j) -> 0 <= j < bx_n bs ->
    x9 = Z_to_bv 64 (56 * j) -> x20 = Z_to_bv 64 (56 * bx_n bs) -> x21 = Z_to_bv 64 (56 * rr) ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m mm -> wmono rsegs m mm -> mem_inv rsegs mm ->
    bytes_at rsegs mm (bv_unsigned sp + 32) bs -> bytes_at rsegs mm r bs' ->
    bytes_at rsegs mm (bv_unsigned sp + 336) (le8 (Z_to_bv 64 inn)) ->
    evt rsegs QQ (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 r) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                          s6 s7 (Z_to_bv 64 i) s9 (Z_to_bv 64 (bv_unsigned sp + 32)) (Z_to_bv 64 fab)
                          x28 x29 x30 x31)
                     F (Z_to_bv 64 0x13344) fc None mm (seg_rom rsegs))).
  { induction k as [|k IH];
      intros j mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31
        Hk Hj E9 E20 E21 MU0 WM0 MI0 HP0 HR0 HN0; [lia|].
    subst x9 x20 x21.
    destruct (KEPT j Hj) as (Kb & Kn & Kp & Km & Kname).
    assert (BOT : forall (m4 : word -> option byte)
        (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y28 y29 y30 y31 : word),
      y9 = Z_to_bv 64 (56 * j) -> y20 = Z_to_bv 64 (56 * bx_n bs) -> y21 = Z_to_bv 64 (56 * rr) ->
      munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m4 -> wmono rsegs m m4 -> mem_inv rsegs m4 ->
      bytes_at rsegs m4 (bv_unsigned sp + 32) bs -> bytes_at rsegs m4 r bs' ->
      bytes_at rsegs m4 (bv_unsigned sp + 336) (le8 (Z_to_bv 64 inn)) ->
      evt rsegs QQ (MS (mkR y1 sp gp tp y5 y6 y7 (Z_to_bv 64 r) y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21
                            s6 s7 (Z_to_bv 64 i) s9 (Z_to_bv 64 (bv_unsigned sp + 32)) (Z_to_bv 64 fab)
                            y28 y29 y30 y31)
                       F (Z_to_bv 64 0x133b4) fc None m4 (seg_rom rsegs))).
    { intros m4 y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y28 y29 y30 y31
        E9 E20 E21 MU4 WM4 MI4 HP4 HR4 HN4. subst y9 y20 y21.
      step. step. if_cases HC; zify_cond HC; rewrite ?unsigned_lit_wrap in HC.
      - eapply (IH (j + 1) m4); [lia | clear - HC Hj B1; Z.div_mod_to_equations; lia | fnd_eq | reflexivity
                                | reflexivity | exact MU4 | exact WM4 | exact MI4 | exact HP4 | exact HR4 | exact HN4].
      - eapply EPI; [exact MU4 | exact WM4 | exact HN4]. }
    assert (NAMEP : forall (m3 : word -> option byte)
        (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y28 y29 y30 y31 : word),
      y9 = Z_to_bv 64 (56 * j) -> y18 = Z_to_bv 64 (bv_unsigned sp + 32 + 56 * j) -> y19 = Z_to_bv 64 (r + 56 * j) ->
      y20 = Z_to_bv 64 (56 * bx_n bs) -> y21 = Z_to_bv 64 (56 * rr) ->
      munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m3 -> wmono rsegs m m3 -> mem_inv rsegs m3 ->
      bytes_at rsegs m3 (bv_unsigned sp + 32) bs -> bytes_at rsegs m3 r bs' ->
      bytes_at rsegs m3 (bv_unsigned sp + 336) (le8 (Z_to_bv 64 inn)) ->
      evt rsegs QQ (MS (mkR y1 sp gp tp y5 y6 y7 (Z_to_bv 64 r) y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21
                            s6 s7 (Z_to_bv 64 i) s9 (Z_to_bv 64 (bv_unsigned sp + 32)) (Z_to_bv 64 fab)
                            y28 y29 y30 y31)
                       F (Z_to_bv 64 0x1339c) fc None m3 (seg_rom rsegs))).
    { intros m3 y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y28 y29 y30 y31
        E9 E18 E19 E20 E21 MU3 WM3 MI3 HP3 HR3 HN3. subst y9 y18 y19 y20 y21.
      step. if_cases HC.
      - eapply BOT; [reflexivity | reflexivity | reflexivity | exact MU3 | exact WM3 | exact MI3
                    | exact HP3 | exact HR3 | exact HN3].
      - zify_cond HC. rewrite ?unsigned_lit in HC by lia.
        assert (Nj : j <> ren) by (destruct Hrr as [Er|Er]; lia).
        destruct Kname as [Kn' | En]; [lia|].
        assert (Ln : length (bx_name bs j) = 32%nat) by (unfold bx_name; apply bsub_length; lia).
        pose proof (bytes_at_bsub m3 (bv_unsigned sp + 32) bs (56 * j + 24) 32 HP3 ltac:(lia) ltac:(lia)
          ltac:(rewrite Lbs; lia)) as HA.
        pose proof (bytes_at_bsub m3 r bs' (56 * j + 24) 32 HR3 ltac:(lia) ltac:(lia)
          ltac:(rewrite Lbs'; lia)) as HB.
        do 4 step.
        eapply evt_cut.
        { eapply SC with (ls := bx_name bs j) (rs := bx_name bs' j) (v := 0);
            [ eapply fnd_bv; [exact HA | lia | lia] | eapply fnd_bv; [exact HB | lia | lia]
            | rewrite En; first [ apply jn_strncmp; exact Ln | rewrite unsigned_lit by lia; apply jn_strncmp; exact Ln ]
            | exact MI3 ]. }
        intros ms' PO. unfold strncmp_post in PO.
        destruct PO as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m5
          & E & MUc & WMc & MIc & _ & _).
        subst ms'.
        lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
          replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
        end.
        step. if_cases HZ; [exfalso; zify_cond HZ; first [ discriminate HZ | lia ] |].
        eapply BOT; [reflexivity | reflexivity | reflexivity | exact (jn_munch _ _ _ _ MU3 MUc)
                    | exact (wmono_trans _ _ _ _ WM3 WMc) | exact MIc
                    | exact (bytes_at_transport rsegs [] m3 m5 _ _ HP3 MUc I)
                    | exact (bytes_at_transport rsegs [] m3 m5 _ _ HR3 MUc I)
                    | exact (bytes_at_transport rsegs [] m3 m5 _ _ HN3 MUc I)]. }
    assert (Lm : length (bx_mac bs j) = 6%nat) by (unfold bx_mac; apply bsub_length; lia).
    assert (Lm' : length (bx_mac bs' j) = 6%nat) by (unfold bx_mac; apply bsub_length; lia).
    destruct (memcmp_model_total (bx_mac bs j) zero6 6 ltac:(lia) ltac:(unfold zero6; rewrite repeat_length; lia))
      as [v1 Hv1].
    destruct (fnd_memcmp 6 (bx_mac bs j) zero6 v1 Lm eq_refl Hv1) as [Rv1 Iv1].
    pose proof (rd4_bytes_at mm r bs' (56 * j + 8) HR0 ltac:(lia) ltac:(rewrite Lbs'; lia)) as F1.
    pose proof (rd4_bytes_at mm (bv_unsigned sp + 32) bs (56 * j + 8) HP0 ltac:(lia) ltac:(rewrite Lbs; lia)) as F2.
    pose proof (rd4_bytes_at mm r bs' (56 * j + 12) HR0 ltac:(lia) ltac:(rewrite Lbs'; lia)) as F3.
    pose proof (rd4_bytes_at mm (bv_unsigned sp + 32) bs (56 * j + 12) HP0 ltac:(lia) ltac:(rewrite Lbs; lia)) as F4.
    pose proof (rd4_bytes_at mm r bs' (56 * j + 20) HR0 ltac:(lia) ltac:(rewrite Lbs'; lia)) as F5.
    pose proof (rd4_bytes_at mm (bv_unsigned sp + 32) bs (56 * j + 20) HP0 ltac:(lia) ltac:(rewrite Lbs; lia)) as F6.
    change (rd4 bs' (56 * j + 8)) with (bx_base bs' j) in F1. rewrite Kb in F1.
    change (rd4 bs (56 * j + 8)) with (bx_base bs j) in F2.
    change (rd4 bs' (56 * j + 12)) with (bx_nch bs' j) in F3. rewrite Kn in F3.
    change (rd4 bs (56 * j + 12)) with (bx_nch bs j) in F4.
    change (rd4 bs' (56 * j + 20)) with (bx_pinned bs' j) in F5. rewrite Kp in F5.
    change (rd4 bs (56 * j + 20)) with (bx_pinned bs j) in F6.
    apply fnd_rd4 in F1. apply fnd_rd4 in F2. apply fnd_rd4 in F3.
    apply fnd_rd4 in F4. apply fnd_rd4 in F5. apply fnd_rd4 in F6.
    pose proof (rd4_range bs (56 * j + 8)) as R1. change (rd4 bs (56 * j + 8)) with (bx_base bs j) in R1.
    pose proof (rd4_range bs (56 * j + 12)) as R2. change (rd4 bs (56 * j + 12)) with (bx_nch bs j) in R2.
    pose proof (rd4_range bs (56 * j + 20)) as R3. change (rd4 bs (56 * j + 20)) with (bx_pinned bs j) in R3.
    pose proof (bytes_at_bsub mm (bv_unsigned sp + 32) bs (56 * j) 6 HP0 ltac:(lia) ltac:(lia)
      ltac:(rewrite Lbs; lia)) as HM1.
    pose proof (jn_zero mm MI0) as HZ0.
    step. step. step. rewrite ?fnd_sx32 by lia. step. rewrite ?fnd_sx32 by lia.
    step. if_cases HC; [exfalso; zify_cond HC; first [ exact (HC eq_refl) | lia ] |].
    clear F1 F2.
    step. rewrite ?fnd_sx32 by lia. step. rewrite ?fnd_sx32 by lia.
    step. if_cases HC'; [exfalso; zify_cond HC'; first [ exact (HC' eq_refl) | lia ] |].
    clear F3 F4.
    step. rewrite ?fnd_sx32 by lia. step. rewrite ?fnd_sx32 by lia.
    step. if_cases HC''; [exfalso; zify_cond HC''; first [ exact (HC'' eq_refl) | lia ] |].
    clear F5 F6.
    do 5 step.
    eapply evt_cut.
    { eapply BC with (ls := bx_mac bs j) (rs := zero6) (v := v1);
        [ eapply fnd_bv; [exact HM1 | lia | lia] | eapply fnd_bv; [exact HZ0 | unfold ZERO_ADDR; lia | lia]
        | exact Hv1 | exact MI0 ]. }
    intros ms' PO. unfold memcmp_post in PO.
    destruct PO as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m2
      & E & MUc & WMc & MIc & _ & _).
    subst ms'.
    lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
    end.
    pose proof (bytes_at_transport rsegs [] mm m2 _ _ HP0 MUc I) as HP2.
    pose proof (bytes_at_transport rsegs [] mm m2 _ _ HR0 MUc I) as HR2.
    pose proof (bytes_at_transport rsegs [] mm m2 _ _ HN0 MUc I) as HN2.
    pose proof (jn_munch _ _ _ _ MU0 MUc) as MU2.
    pose proof (wmono_trans _ _ _ _ WM0 WMc) as WM2.
    step. if_cases HC0; zify_cond HC0; rewrite ?unsigned_lit_wrap in HC0.
    - eapply NAMEP; [fnd_eq | fnd_eq | fnd_eq | reflexivity | reflexivity | exact MU2 | exact WM2 | exact MIc
                    | exact HP2 | exact HR2 | exact HN2].
    - assert (V1 : v1 <> 0) by (clear - HC0 Rv1; Z.div_mod_to_equations; lia).
      assert (NZ : bx_mac bs j <> zero6) by (intros Ez; apply Iv1 in Ez; lia).
      destruct Km as [Kz | Km']; [contradiction|].
      destruct (memcmp_model_total (bx_mac bs j) (bx_mac bs' j) 6 ltac:(lia) ltac:(lia)) as [v2 Hv2].
      destruct (fnd_memcmp 6 _ _ v2 Lm Lm' Hv2) as [Rv2 Iv2].
      assert (V2 : v2 = 0) by (apply Iv2; symmetry; exact Km').
      subst v2.
      pose proof (bytes_at_bsub m2 (bv_unsigned sp + 32) bs (56 * j) 6 HP2 ltac:(lia) ltac:(lia)
        ltac:(rewrite Lbs; lia)) as HMa.
      pose proof (bytes_at_bsub m2 r bs' (56 * j) 6 HR2 ltac:(lia) ltac:(lia)
        ltac:(rewrite Lbs'; lia)) as HMb.
      do 4 step.
      eapply evt_cut.
      { eapply BC with (ls := bx_mac bs j) (rs := bx_mac bs' j) (v := 0);
          [ eapply fnd_bv; [exact HMa | lia | lia] | eapply fnd_bv; [exact HMb | lia | lia]
          | exact Hv2 | exact MIc ]. }
      intros ms' PO. unfold memcmp_post in PO.
      destruct PO as (w5 & w6 & w7 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m3
        & E & MUd & WMd & MId & _ & _).
      subst ms'.
      lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
      end.
      step. if_cases HZ; [exfalso; zify_cond HZ; first [ discriminate HZ | lia ] |].
      eapply NAMEP; [fnd_eq | fnd_eq | fnd_eq | reflexivity | reflexivity | exact (jn_munch _ _ _ _ MU2 MUd)
                    | exact (wmono_trans _ _ _ _ WM2 WMd) | exact MId
                    | exact (bytes_at_transport rsegs [] m2 m3 _ _ HP2 MUd I)
                    | exact (bytes_at_transport rsegs [] m2 m3 _ _ HR2 MUd I)
                    | exact (bytes_at_transport rsegs [] m2 m3 _ _ HN2 MUd I)]. }
  step. step. step.
  eapply evt_cut.
  { eapply CK with (r := r) (fabric := fab) (bs := bs') (lo := lo);
      [ fnd_eq | fnd_eq | exact HR | exact B16 | exact Hfab | exact MI | exact ST | lia | left; lia ]. }
  intros ms' PO.
  destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & E & MU1 & WM1 & ST1 & _).
  subst ms'.
  lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  pose proof (jn_mem_inv _ _ m m1 MI MU1 ltac:(lia)) as MI1.
  pose proof (bytes_at_transport rsegs _ m m1 _ _ HP MU1 ltac:(cbn [disjoint_from]; split; [lia | exact I])) as HP1.
  pose proof (bytes_at_transport rsegs _ m m1 _ _ HR MU1
    ltac:(cbn [disjoint_from]; rewrite Lbs'; split; [lia | exact I])) as HR1.
  pose proof (bytes_at_transport rsegs _ m m1 _ _ HN MU1 ltac:(cbn [disjoint_from]; split; [lia | exact I])) as HN1.
  pose proof (rd4_bytes_at m1 (bv_unsigned sp + 32) bs 280 HP1 ltac:(lia) ltac:(rewrite Lbs; lia)) as FN.
  change (rd4 bs 280) with (bx_n bs) in FN.
  replace (bv_unsigned sp + 32 + 280) with (bv_unsigned sp + 312) in FN by lia.
  apply fnd_rd4 in FN.
  step. rewrite ?fnd_sx32 by lia.
  step. if_cases HC.
  - eapply EPI; [exact MU1 | exact WM1 | exact HN1].
  - zify_cond HC.
    assert (Hn0 : 0 < bx_n bs) by lia.
    do 7 step.
    eapply (LOOP (Z.to_nat (bx_n bs)) 0 m1); [lia | lia | jn_eq | jn_eq | jn_eq | exact MU1 | exact WM1 | exact MI1
                                           | exact HP1 | exact HR1 | exact HN1].
Qed.

Theorem llvm_join_holds : llvm_join_ok B API.
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n b i k c HCX HKX.
  destruct HCX as (BI & Hk0 & Hra & Hpre & Hsn & H47 & Hres0 & Hroom & Hro0 & Hgi & Hfrm0 & Hn26).
  pose proof BI as (SEGS & _ & _ & HGG & _ & AX).
  destruct HKX as (fx' & regs & mem & md & L & A & r & fab & ip & inn & bs & bs' & ren & j0 & j1 & jm & Ec & Hfrm
    & RB & E19 & FRC & Hi & Hinn & Hip & Hipn & Hren & INV & Hfab & RWR & INV' & Hfab' & KEPT & AL & Hk).
  destruct RB as (E2 & E3 & E4 & E8 & E24 & E25 & E26 & E27).
  destruct AL as (FR & MINE & RES).
  subst c.
  unfold LLVM_K, LLVM_FRAME in Hk0.
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra1 & Hal & Hceil & H63 & Hstw0 & Htp & Herr0 & Hp & Hn1 & Hpl & Hrod).
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & Hro).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt.
  destruct INV as ((Lbs & B1 & _) & _). unfold boxreg_B1 in B1.
  destruct (lf_mine_bytes B API AX L0 A0 L A mem md r 288 r HM MINE ltac:(lia)) as (_ & _ & Hr1 & _).
  destruct (lf_mine_bytes B API AX L0 A0 L A mem md r 288 (r + 287) HM MINE ltac:(lia)) as (_ & _ & Hr2 & _).
  assert (G2 : reg_get regs 2 = Z_to_bv 64 (spZ regs0 - 448)) by exact E2.
  assert (Esp : bv_unsigned (reg_get regs 2) = spZ regs0 - 448) by (rewrite G2; apply unsigned_lit; lia).
  pose proof (jn_cell_bytes mem (spZ regs0 - 448) [CB 8 j0; C8 (Z_to_bv 64 fab); CB 16 j1] (CB 288 bs)
    (CB 8 jm :: C8 (Z_to_bv 64 ip) :: C8 (Z_to_bv 64 inn) :: llvm_saved_cells regs0) FRC) as HP.
  change (Z.of_nat (cells_size [CB 8 j0; C8 (Z_to_bv 64 fab); CB 16 j1])) with 32 in HP.
  change (cbytes (CB 288 bs)) with bs in HP.
  pose proof (jn_cell_bytes mem (spZ regs0 - 448)
    [CB 8 j0; C8 (Z_to_bv 64 fab); CB 16 j1; CB 288 bs; CB 8 jm; C8 (Z_to_bv 64 ip)] (C8 (Z_to_bv 64 inn))
    (llvm_saved_cells regs0) FRC) as HN.
  change (Z.of_nat (cells_size [CB 8 j0; C8 (Z_to_bv 64 fab); CB 16 j1; CB 288 bs; CB 8 jm; C8 (Z_to_bv 64 ip)]))
    with 336 in HN.
  change (cbytes (C8 (Z_to_bv 64 inn))) with (le8 (Z_to_bv 64 inn)) in HN.
  pose proof (jn_cell_bytes mem r [] (CB 288 bs') [] RWR) as HR.
  change (Z.of_nat (cells_size [])) with 0 in HR. rewrite Z.add_0_r in HR.
  change (cbytes (CB 288 bs')) with bs' in HR.
  pose proof (bytes_at_normalize rsegs mem _ _ Hro HP) as HPn.
  pose proof (bytes_at_normalize rsegs mem _ _ Hro HN) as HNn.
  pose proof (bytes_at_normalize rsegs mem _ _ Hro HR) as HRn.
  assert (STn : Frame.stk rsegs (normalize rsegs mem) (spZ regs0 - stk) (spZ regs0 - 448)).
  { apply lf_stk; [lia | lia |]. intros a Ha. unfold YP09.writable_at.
    assert (Hni : ~ in_img B a) by (intros Hi'; pose proof (lf_in_img_top B a SEGS Hi'); lia).
    rewrite (wview_rel_rw rsegs mem (normalize rsegs mem) _ (mem_rel_normalize rsegs mem Hro)
               (lf_ro_addr_out B a SEGS Hni ltac:(lia))).
    rewrite <- SEGS. exact (Hstw a ltac:(lia)). }
  assert (Hrr : ren mod 2 ^ 32 = ren \/ ren = -1).
  { destruct (Z.eq_dec ren (-1)) as [E|E]; [right; exact E | left; apply Z.mod_small; lia]. }
  rewrite SEGS.
  eapply (llvm_run_norm fx' regs (Z_to_bv 64 LLVM_JOIN) mem md); [exact Hh | exact Hl | exact Hro | | |].
  - unfold Regs6ss.mkR_of, LLVM_JOIN.
    eapply jn_evt with (lo := spZ regs0 - stk) (r := r) (fab := fab) (rr := ren mod 2 ^ 32) (ren := ren) (i := i)
      (inn := inn) (bs := bs) (bs' := bs');
      [ exact E8 | exact E19 | exact E24 | rewrite Esp; exact E26 | exact E27
      | rewrite Esp; exact HPn | exact HRn | rewrite Esp; exact HNn
      | exact Lbs | exact B1 | exact (proj1 INV') | exact Hfab' | exact KEPT
      | apply Z.mod_pos_bound; lia | exact Hrr | exact Hi | lia
      | exact (mem_inv_normalize rsegs mem) | rewrite Esp; exact STn | lia | rewrite Esp; lia | rewrite Esp; lia
      | lia | lia ].
  - intros ms HQ. unfold jn_Q in HQ.
    destruct HQ as (x1 & x5 & x6 & x7 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21
      & x22 & x23 & x24 & x28 & x29 & x30 & x31 & pc & m'' & -> & _).
    do 5 eexists. reflexivity.
  - intros R F pc' fc m0' HQ regs' m' Hx Hrel Hsame. unfold jn_Q in HQ.
    destruct HQ as (x1 & x5 & x6 & x7 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21
      & x22 & x23 & x24 & x28 & x29 & x30 & x31 & pc & m'' & HE & MU & WM & Hpc).
    injection HE as ER EF EP EC EM. subst R F pc' fc m0'.
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) m' m'' (mem_rel_normalize rsegs mem Hro) Hrel Hsame MU)
      as MU'.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) m' m'' (mem_rel_normalize rsegs mem Hro) Hrel Hsame WM)
      as WM'.
    pose proof (ro_agree_same rsegs mem m' Hro Hsame) as Hro'.
    rewrite Esp in MU'.
    assert (FR1 : lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L A m' md).
    { eapply (lf_fr_evt B API SEGS AX HGG); [exact FR | lia | lia | exact MU' | exact WM' | exact Hro' |].
      intros x Hx0 NO. left.
      destruct (Z_le_dec (spZ regs0 - 448 - 112) x); destruct (Z_lt_dec x (spZ regs0 - 448)); try lia;
        exfalso; apply NO; cbn [Frame.outside]; (split; [lia | exact I]). }
    pose proof (rw_cells_transport rsegs _ mem m' _ _ FRC MU' WM' ltac:(cbn [disjoint_from]; split; [lia | exact I]))
      as FRC'.
    pose proof (rw_cells_transport rsegs _ mem m' _ _ RWR MU' WM'
      ltac:(cbn [disjoint_from]; change (Z.of_nat (cells_size [CB 288 bs'])) with 288; split; [lia | exact I]))
      as RWR'.
    assert (R2 : YK11.getr regs' 2 = Z_to_bv 64 (spZ regs0 - 448)) by (rewrite (lf_getr_eqv _ _ _ Hx); exact E2).
    assert (R3 : YK11.getr regs' 3 = YK11.getr regs0 3) by (rewrite (lf_getr_eqv _ _ _ Hx); exact E3).
    assert (R4 : YK11.getr regs' 4 = YK11.getr regs0 4) by (rewrite (lf_getr_eqv _ _ _ Hx); exact E4).
    assert (R8 : YK11.getr regs' 8 = Z_to_bv 64 r) by (rewrite (lf_getr_eqv _ _ _ Hx); exact E8).
    apply SR_ret.
    destruct Hpc as [(Epc & Hi62 & Hinn0 & E21' & E24') | Epc]; subst pc.
    + left. unfold llvm_J.
      exists (mkFP (@fp_regs fx') (@fp_csr fx')), regs', m', md, L, A, r, fab, ip, inn, bs', j0,
        (cells_bytes [CB 16 j1; CB 288 bs; CB 8 jm]), (cells_bytes [C8 (Z_to_bv 64 inn)]).
      split; [rewrite SEGS; reflexivity|].
      split; [exact Hfrm|].
      split.
      { unfold llvm_regs_base. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|].
        split; [rewrite (lf_getr_eqv _ _ _ Hx); exact E24'|].
        split; [rewrite (lf_getr_eqv _ _ _ Hx); exact E25|].
        split; [rewrite (lf_getr_eqv _ _ _ Hx); exact E26 | rewrite (lf_getr_eqv _ _ _ Hx); exact E27]. }
      split; [rewrite (lf_getr_eqv _ _ _ Hx); exact E21'|].
      split.
      { pose proof (rw_cells_merge rsegs m' (spZ regs0 - 448) [CB 8 j0; C8 (Z_to_bv 64 fab)]
          [CB 16 j1; CB 288 bs; CB 8 jm] (C8 (Z_to_bv 64 ip) :: C8 (Z_to_bv 64 inn) :: llvm_saved_cells regs0) FRC')
          as M1.
        exact (rw_cells_merge rsegs m' (spZ regs0 - 448)
          [CB 8 j0; C8 (Z_to_bv 64 fab); CB (cells_size [CB 16 j1; CB 288 bs; CB 8 jm])
             (cells_bytes [CB 16 j1; CB 288 bs; CB 8 jm]); C8 (Z_to_bv 64 ip)]
          [C8 (Z_to_bv 64 inn)] (llvm_saved_cells regs0) M1). }
      split; [lia|]. split; [lia|]. split; [exact Hip|]. split; [exact Hipn|].
      split; [exact RWR'|]. split; [exact INV'|]. split; [exact Hfab'|].
      split; [split; [exact FR1 | split; [exact MINE | exact RES]] | lia].
    + right. unfold llvm_X.
      exists (mkFP (@fp_regs fx') (@fp_csr fx')), regs', m', md, L, A, r,
        (cells_bytes [CB 8 j0; C8 (Z_to_bv 64 fab); CB 16 j1; CB 288 bs; CB 8 jm; C8 (Z_to_bv 64 ip);
                      C8 (Z_to_bv 64 inn)]).
      split; [rewrite SEGS; reflexivity|].
      split; [exact Hfrm|].
      split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|].
      split.
      { exact (rw_cells_merge rsegs m' (spZ regs0 - 448) []
          [CB 8 j0; C8 (Z_to_bv 64 fab); CB 16 j1; CB 288 bs; CB 8 jm; C8 (Z_to_bv 64 ip); C8 (Z_to_bv 64 inn)]
          (llvm_saved_cells regs0) FRC'). }
      split; [split; [exact FR1 | split; [exact MINE | exact RES]] | lia].
Qed.

End S.
