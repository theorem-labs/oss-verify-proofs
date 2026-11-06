(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1050 of its 1065 lines of code are new or changed and 32 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import TxCalls.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require RegisterBridge Regs6ss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import memcpy_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import tx_put_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 (Z_to_bv 64 0) => constr:(C1 (Z_to_bv 8 0))
  end.

Lemma bytes_at_munch : forall W m m' a bs,
  bytes_at rsegs m a bs -> munch W m m' -> (bs = [] \/ disjoint_from W a (Z.of_nat (length bs))) ->
  bytes_at rsegs m' a bs.
Proof.
  intros W m m' a bs H MU [E|D].
  - subst bs. pose proof (bytes_at_bound _ _ _ _ H) as HB. cbn [length Z.of_nat] in HB. apply bytes_at_nil. lia.
  - eapply bytes_at_transport; eassumption.
Qed.

Ltac src_after MU SRC SL :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of SRC with True /\ bytes_at _ _ ?s ?src =>
    lazymatch type of SL with length _ = Z.to_nat ?n =>
      assert (SRC' : bytes_at rsegs mm s src)
        by (eapply bytes_at_munch; [exact (proj2 SRC) | exact MU |];
            destruct (Z.eq_dec n 0);
            [ left; destruct src; [reflexivity | cbn [length] in SL; lia]
            | right; cbn [disjoint_from]; rewrite SL; lia ])
    end end
  end.

Ltac br_lits := unfold_cond; rewrite ?unsigned_lit by lia.

Lemma sltu_pos : forall b, (0 < b < 2 ^ 64)%Z -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 b) = Z_to_bv 64 1.
Proof.
  intros b Hb. unfold v_sltu, c_ltu. try unfold bv_ltu. rewrite !unsigned_lit by lia.
  destruct (Z.ltb_spec 0 b); [reflexivity | lia].
Qed.

Lemma sltiu_pos : forall d, (1 <= d < 2 ^ 64)%Z -> v_sltiu (Z_to_bv 64 d) 1 = Z_to_bv 64 0.
Proof.
  intros d Hd. unfold v_sltiu. rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1%Z.
  destruct (Z.ltb_spec d 1); [lia | reflexivity].
Qed.

Ltac xor_lit :=
  change (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 1)) (bv_unsigned (Z_to_bv 64 0)))) with (Z_to_bv 64 1).

Section KA.
Hypothesis MC : memcpy_contract.

Definition tail_post (rav f0 gp tp s0v s1v s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (W : list ivl) (t b len n cap d s : Z) (src : list byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR rav f0 gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom rsegs) /\
    munch W m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
    rw_cells rsegs m' t [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 (len + n)); C8 (Z_to_bv 64 cap)] /\
    bytes_at rsegs m' d (src ++ [Z_to_bv 8 0]).

Lemma tx_tail : forall ra gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (rav s0v s1v s2v : word)
    (f t s n b len cap d e : Z) (src junk : list byte) (z : byte),
  d = (b + len)%Z -> e = (d + n)%Z ->
  (0 < b)%Z -> (0 <= len)%Z -> (0 <= n)%Z -> (e + 1 <= 2 ^ 64)%Z -> (0 <= cap < 2 ^ 64)%Z ->
  (0 <= s < 2 ^ 64)%Z -> (s + n <= 2 ^ 64)%Z -> (0 <= t)%Z -> (t + 24 <= 2 ^ 64)%Z -> (0 <= f)%Z -> (f + 32 <= 2 ^ 64)%Z ->
  rw_cells rsegs m f [C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rw_cells rsegs m t [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 cap)] ->
  rw_cells rsegs m d [CB (Z.to_nat n) junk] ->
  rw_cells rsegs m e [C1 z] ->
  bytes_at rsegs m s src -> length src = Z.to_nat n ->
  (n = 0 \/ s + n <= d \/ e + 1 <= s)%Z -> (t + 24 <= d \/ e + 1 <= t)%Z ->
  (f + 32 <= t \/ t + 24 <= f)%Z -> (f + 32 <= d \/ e + 1 <= f)%Z ->
  munch [(f, f + 32); (t, t + 24); (d, e + 1)]%Z m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  evt rsegs (tail_post rav (Z_to_bv 64 (f + 32)) gp tp s0v s1v s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0
               [(f, f + 32); (t, t + 24); (d, e + 1)]%Z t b len n cap d s src)
    (MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 n) (Z_to_bv 64 b) (Z_to_bv 64 len) a2
             a3 a4 a5 a6 a7 (Z_to_bv 64 s) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15524) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m rav s0v s1v s2v
    f t s n b len cap d e src junk z Hd He Hb Hl Hn He1 Hc Hs Hs1 Ht Ht1 Hf Hf1 FR REC DST ZB SRC SL DS DT FT FD MU WM MI.
  step. replace (len + b)%Z with d by lia.
  step. br_lits. if_false.
  step. step. step.
  rewrite (sltu_pos b) by lia. rewrite (sltiu_pos d) by lia. xor_lit.
  step. br_lits. if_false.
  step. step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (MC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ src junk);
      rewrite ?unsigned_lit by lia; first [eassumption | lia]
    | let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO; unfold memcpy_post in PO; rewrite ?unsigned_lit in PO by lia; revert ms' PO;
      post_call rsegs mm ]
  end.
  cbv delta [mkR].
  step. step. step.
  step. first [ replace (b + (len + n))%Z with e by lia | replace (len + n + b)%Z with e by lia ].
  step.
  step. br_lits. if_false.
  step. step. step.
  rewrite (sltu_pos b) by lia. rewrite (sltiu_pos e) by lia. xor_lit.
  step. br_lits. if_false.
  step. br_lits. if_false.
  step.
  step. step. step. step. step. step.
  finish.
  apply bytes_at_app. split.
  - match goal with H : rw_cells _ _ d [CB _ src] |- _ =>
      destruct H as [[_ H] _]; cbn [cells_bytes cbytes] in H; rewrite app_nil_r in H; exact H end.
  - rewrite SL. replace (d + Z.of_nat (Z.to_nat n))%Z with e by lia.
    match goal with H : rw_cells _ _ e [C1 _] |- _ =>
      destruct H as [[_ H] _]; cbn [cells_bytes cbytes app] in H; exact H end.
Qed.

Definition grow_post (ra0 gp tp s0v s1v s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (f t b len cap c n s : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1,
    ms' = MS (mkR (Z_to_bv 64 0x15508) (Z_to_bv 64 f) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 n) (Z_to_bv 64 b)
                  (Z_to_bv 64 c) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 s) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19bfc) fc None m1 (seg_rom rsegs) /\
    munch [(f, f + 32); (t, t + 24)]%Z m0 m1 /\ wmono rsegs m0 m1 /\ mem_inv rsegs m1 /\
    rw_cells rsegs m1 f [C8 s2v; C8 s1v; C8 s0v; C8 ra0] /\
    rw_cells rsegs m1 t [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 cap)].

Lemma land7 : forall t, (0 <= t)%Z -> (t mod 8 = 0)%Z -> Z.land t 7 = 0%Z.
Proof.
  intros t Ht Hm. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. exact Hm.
Qed.

(* The `failed` field of the record at t + 24 (int, read by `lw a0, 24(s0)` at 0x154d8) is 0: tx_put goes on. *)
Lemma tx_head_grow : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (t s n b len cap c : Z) (j : list byte),
  c = (2 * (len + n + 1))%Z ->
  (0 <= b < 2 ^ 64)%Z -> (0 <= len)%Z -> (0 <= n)%Z -> (0 <= cap < 2 ^ 64)%Z -> (len + n + 1 <= 2 ^ 28)%Z ->
  (cap < len + n + 1)%Z ->
  (0 <= s < 2 ^ 64)%Z -> (0 <= t)%Z -> (t + 24 <= 2 ^ 64)%Z -> (t mod 8 = 0)%Z ->
  rw_cells rsegs m (bv_unsigned sp + -32) [CB 32 j] ->
  rw_cells rsegs m t [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 cap)] ->
  ro_cells rsegs m (t + 24) [C4 (Z_to_bv 64 0)] ->
  (bv_unsigned sp <= t)%Z -> mem_inv rsegs m ->
  evt rsegs (grow_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (bv_unsigned sp + -32) t b len cap c n s)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 t) (Z_to_bv 64 s) (Z_to_bv 64 n) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x154b8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    t s n b len cap c j Hc Hb Hl Hn Hcap Hneed Hgrow Hs Ht Ht1 Tal FRJ REC FL Hst MI.
  pose proof (rw_cells_bound _ _ _ _ FRJ) as FB. cbn [cells_size csize] in FB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp + -32 + 32); (t, t + 24)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat j [] [8; 8; 8; 8]%nat) in FRJ; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FRJ.
  do 7 step.
  rewrite (unsigned_lit t) by lia. rewrite (land7 t) by lia.
  step. br_lits. if_false.
  step.
  step. br_lits. if_false.
  do 7 step.
  step. br_lits. if_false.
  step.
  replace (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (n + len + 1))) 1)) with (Z_to_bv 64 c)
    by (f_equal; rewrite unsigned_lit by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
  step.
  finish.
Qed.

Lemma tx_head_nogrow : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (t s n b len cap d e : Z) (src junk j : list byte) (z : byte),
  d = (b + len)%Z -> e = (d + n)%Z ->
  (0 < b < 2 ^ 64)%Z -> (0 <= len)%Z -> (0 <= n)%Z -> (0 <= cap < 2 ^ 64)%Z -> (len + n + 1 <= cap)%Z ->
  (e + 1 <= 2 ^ 64)%Z -> (0 <= s < 2 ^ 64)%Z -> (s + n <= 2 ^ 64)%Z -> (0 <= t)%Z -> (t + 24 <= 2 ^ 64)%Z ->
  (t mod 8 = 0)%Z ->
  rw_cells rsegs m (bv_unsigned sp + -32) [CB 32 j] ->
  rw_cells rsegs m t [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 cap)] ->
  ro_cells rsegs m (t + 24) [C4 (Z_to_bv 64 0)] ->
  rw_cells rsegs m d [CB (Z.to_nat n) junk] ->
  rw_cells rsegs m e [C1 z] ->
  bytes_at rsegs m s src -> length src = Z.to_nat n ->
  (n = 0 \/ s + n <= d \/ e + 1 <= s)%Z -> (t + 24 <= d \/ e + 1 <= t)%Z -> (n = 0 \/ s + n <= t \/ t + 24 <= s)%Z ->
  (bv_unsigned sp <= t)%Z -> (bv_unsigned sp <= d \/ e + 1 <= bv_unsigned sp + -32)%Z ->
  (n = 0 \/ bv_unsigned sp <= s \/ s + n <= bv_unsigned sp + -32)%Z ->
  mem_inv rsegs m ->
  evt rsegs (tail_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m
               [(bv_unsigned sp + -32, bv_unsigned sp + -32 + 32); (t, t + 24); (d, e + 1)]%Z t b len n cap d s src)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 t) (Z_to_bv 64 s) (Z_to_bv 64 n) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x154b8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    t s n b len cap d e src junk j z Hd He Hb Hl Hn Hcap Hfit He1 Hs Hs1 Ht Ht1 Tal FRJ REC FL DST ZB SRC SL DS DT ST Hst FD FS MI.
  pose proof (rw_cells_bound _ _ _ _ FRJ) as FB. cbn [cells_size csize] in FB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp + -32 + 32); (t, t + 24); (d, e + 1)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (SRCH : True /\ bytes_at rsegs m s src) by (split; [exact I | exact SRC]). clear SRC.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat j [] [8; 8; 8; 8]%nat) in FRJ; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FRJ.
  do 7 step.
  rewrite (unsigned_lit t) by lia. rewrite (land7 t) by lia.
  step. br_lits. if_false.
  step.
  step. br_lits. if_false.
  do 7 step.
  step. br_lits. if_true.
  assert (ESP : Z_to_bv 64 (bv_unsigned sp + -32 + 32) = sp)
    by (replace (bv_unsigned sp + -32 + 32)%Z with (bv_unsigned sp) by lia; apply Z_to_bv_bv_unsigned).
  src_after MU SRCH SL.
  eapply evt_mono; [eapply tx_tail with (cap := cap); try eassumption; try reflexivity; lia | intros ms' HP; rewrite ESP in HP;
     replace (bv_unsigned sp + 0)%Z with (bv_unsigned sp + -32 + 32)%Z by lia; exact HP].
Qed.

Lemma tx_after : forall ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (rav s0v s1v s2v : word)
    (f t s n q b0 len cap c d e : Z) (src junk : list byte) (z : byte),
  c = (2 * (len + n + 1))%Z -> d = (q + len)%Z -> e = (d + n)%Z ->
  (0 < q < 2 ^ 64)%Z -> (0 <= b0 < 2 ^ 64)%Z -> (0 <= len)%Z -> (0 <= n)%Z -> (e + 1 <= 2 ^ 64)%Z -> (0 <= cap < 2 ^ 64)%Z ->
  (c < 2 ^ 64)%Z ->
  (0 <= s < 2 ^ 64)%Z -> (s + n <= 2 ^ 64)%Z -> (0 <= t)%Z -> (t + 24 <= 2 ^ 64)%Z -> (0 <= f)%Z -> (f + 32 <= 2 ^ 64)%Z ->
  rw_cells rsegs m f [C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rw_cells rsegs m t [C8 (Z_to_bv 64 b0); C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 cap)] ->
  rw_cells rsegs m d [CB (Z.to_nat n) junk] ->
  rw_cells rsegs m e [C1 z] ->
  bytes_at rsegs m s src -> length src = Z.to_nat n ->
  (n = 0 \/ s + n <= d \/ e + 1 <= s)%Z -> (t + 24 <= d \/ e + 1 <= t)%Z -> (n = 0 \/ s + n <= t \/ t + 24 <= s)%Z ->
  (f + 32 <= t \/ t + 24 <= f)%Z -> (f + 32 <= d \/ e + 1 <= f)%Z -> (n = 0 \/ f + 32 <= s \/ s + n <= f)%Z ->
  mem_inv rsegs m ->
  evt rsegs (tail_post rav (Z_to_bv 64 (f + 32)) gp tp s0v s1v s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m
               [(f, f + 32); (t, t + 24); (d, e + 1)]%Z t q len n c d s src)
    (MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 n) (Z_to_bv 64 q) a1 a2
             a3 a4 a5 a6 a7 (Z_to_bv 64 s) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15508) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m rav s0v s1v s2v
    f t s n q b0 len cap c d e src junk z Hc Hd He Hq Hb0 Hl Hn He1 Hcap Hc1 Hs Hs1 Ht Ht1 Hf Hf1 FR REC DST ZB SRC SL DS DT ST
    FT FD FS MI.
  pose proof (munch_refl [(f, f + 32); (t, t + 24); (d, e + 1)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (SRCH : True /\ bytes_at rsegs m s src) by (split; [exact I | exact SRC]). clear SRC.
  step. br_lits. if_false.
  step. step. step. step.
  replace (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (len + n))) 1 + 2)) with (Z_to_bv 64 c)
    by (f_equal; rewrite unsigned_lit by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
  step. step.
  src_after MU SRCH SL.
  eapply tx_tail with (cap := c); try eassumption; try reflexivity; lia.
Qed.

End KA.

Lemma find_segment_some : forall segs a k seg, find_segment segs a k = Some seg ->
  In seg segs /\ (Z.of_N (seg_base seg) <= a /\ a + k <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z.
Proof.
  induction segs as [|sg segs IH]; intros a k seg H; cbn in H; [discriminate|].
  match type of H with context [if ?c then _ else _] => destruct c eqn:E end.
  - inversion H; subst. apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1, E2.
    split; [left; reflexivity | lia].
  - destruct (IH _ _ _ H) as (H1 & H2). split; [right; exact H1 | exact H2].
Qed.

Lemma rsegs_low : forall seg, In seg rsegs -> (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= 2 ^ 40)%Z.
Proof.
  intros seg H.
  assert (E : forallb (fun sg => Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? 2 ^ 40)%Z rsegs = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in E. specialize (E seg H). apply Z.leb_le in E. exact E.
Qed.

Lemma reserve_cover : forall seg a,
  (Z.of_N (seg_base seg) <= a < Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z ->
  (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= 2 ^ 40)%Z ->
  (bv_unsigned (fst (segment_reservation seg)) <= a <
   bv_unsigned (fst (segment_reservation seg)) + bv_unsigned (snd (segment_reservation seg)))%Z.
Proof.
  intros seg a Ha Hs. unfold segment_reservation. cbn [fst snd].
  unfold page_round_down_Z, page_round_up_Z, page_size.
  set (b := Z.of_N (seg_base seg)) in *. set (z := Z.of_N (seg_size seg)) in *.
  assert (Hb : (0 <= b)%Z) by (subst b; lia). assert (Hz : (0 <= z)%Z) by (subst z; lia).
  assert (L1 : (0 <= b / 4096 * 4096 <= b)%Z) by (Z.div_mod_to_equations; lia).
  assert (L2 : (b + z <= (b + z + 4096 - 1) / 4096 * 4096 <= b + z + 4095)%Z)
    by (Z.div_mod_to_equations; lia).
  rewrite !unsigned_lit by lia. lia.
Qed.

Lemma pairwise_in : forall {T : Type} (R : T -> T -> Prop) (l : list T) x y,
  pairwise R l -> In x l -> In y l -> x <> y -> R x y \/ R y x.
Proof.
  intros T R l. induction l as [|h l IH]; intros x y Hp Hx Hy Hne; cbn in *; [contradiction|].
  destruct Hp as [H1 H2].
  destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - contradiction.
  - left. apply H1. exact Hy.
  - right. apply H1. exact Hx.
  - apply IH; assumption.
Qed.

Lemma ivl_disj : forall s n lo hi, (lo < hi)%Z ->
  (forall i, (0 <= i < n)%Z -> ~ (lo <= s + i < hi)%Z) -> (n = 0 \/ s + n <= lo \/ hi <= s)%Z \/ (n < 0)%Z.
Proof.
  intros s n lo hi Hle H.
  destruct (Z_lt_ge_dec n 0); [right; lia|]. left.
  destruct (Z.eq_dec n 0); [left; exact e|]. right.
  destruct (Z_le_gt_dec (s + n) lo); [left; lia|].
  destruct (Z_le_gt_dec hi s); [right; lia|].
  exfalso. destruct (Z_le_gt_dec s lo).
  - apply (H (lo - s)%Z); lia.
  - apply (H 0%Z); lia.
Qed.

Lemma outside_dec : forall W x, {outside W x} + {~ outside W x}.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn; [left; exact I|].
  destruct (IH x) as [H|H].
  - destruct (Z_le_gt_dec lo x); destruct (Z_lt_ge_dec x hi).
    + right. intros [H1 _]. lia.
    + left. split; [lia | exact H].
    + left. split; [lia | exact H].
    + left. split; [lia | exact H].
  - right. intros [_ H2]. exact (H H2).
Qed.

Lemma vm_id : forall md, md = with_vmmaps (m_vmmaps md) md.
Proof. intros [fd v io fs pr lim tm]. destruct v. reflexivity. Qed.

Lemma eqv_final `{fx : FPState} : forall R F pc fc m ro ms',
  Regs6ss.ms_eqv (MS R F pc fc None m ro) ms' -> F = fp_regs -> fc = fp_csr ->
  ms' = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst (ms_regs ms') pc m ro /\
  (forall r : reg, is_x0 r = false -> reg_get (ms_regs ms') r = reg_get R r).
Proof.
  intros R F pc fc m ro [r' fr pcv svc rv fcs mm rom] (HR & HF & HP & HS & HV & HC & HM & HRo) EF EC.
  cbn in *. subst. split; [reflexivity|]. intros r Hr. symmetry. apply HR. exact Hr.
Qed.

Section KB.
Context {fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RFm : ResForm.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRB : errno_addr B + 4 <= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling.
(* Cut-free twin only: malloc's entry, for the ra <> ms_malloc premise of the cut-free NULL realloc. *)
Hypothesis MALLOC_AT : ms_malloc B = 0x18390%Z.
Local Open Scope Z_scope.

Lemma find_img : forall a seg, (0 <= a)%Z -> find_segment rsegs a 1 = Some seg -> in_img B a.
Proof.
  intros a seg Ha F. destruct (find_segment_some _ _ _ _ F) as (Hin & H1 & H2). pose proof (rsegs_low _ Hin).
  split. { rewrite SEGS. intros E. rewrite E in Hin. destruct Hin. }
  exists (segment_reservation seg). split.
  - rewrite SEGS. unfold segments_reserved. apply in_map. exact Hin.
  - apply reserve_cover; lia.
Qed.

Lemma present_of_writable : forall m a, (0 <= a < 2 ^ 64)%Z ->
  (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling <= a \/ ~ in_img B a)%Z -> writable_at (ms_segs B) m a -> present m a.
Proof.
  intros m a Ha Hc W. unfold writable_at, wview in W. unfold present.
  destruct (m (Z_to_bv 64 a)) as [x|] eqn:E; [exists x; reflexivity|]. exfalso.
  rewrite SEGS in W. rewrite unsigned_lit in W by lia.
  destruct (find_segment rsegs a 1) as [seg|] eqn:F; [|apply W; reflexivity].
  destruct Hc as [Hc|Hc].
  - destruct (find_segment_some _ _ _ _ F) as (Hin & _ & H2). pose proof (rsegs_low _ Hin).
    pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value. lia.
  - apply Hc. eapply find_img; [lia | exact F].
Qed.

Lemma writable_of_present : forall m a, present m a -> writable_at (ms_segs B) m a.
Proof. intros m a [x Hx]. unfold writable_at, wview. rewrite Hx. discriminate. Qed.

Lemma rw_of_present : forall m lo k, (0 <= lo)%Z -> (lo + k <= 2 ^ 64)%Z -> (0 <= k)%Z ->
  (forall i, (0 <= i < k)%Z -> present m (lo + i)) -> exists junk, rw_cells rsegs m lo [CB (Z.to_nat k) junk].
Proof.
  intros m lo k Hlo Hhi Hk HP.
  assert (ST : stk rsegs m lo (lo + k)).
  { split; [lia|]. split; [lia|]. intros a Ha. destruct (HP (a - lo)%Z) as [x Hx]; [lia|].
    replace (lo + (a - lo))%Z with a in Hx by lia. unfold wa. split.
    - unfold wview. rewrite Hx. discriminate.
    - exists x. unfold mrd. rewrite Hx. reflexivity. }
  destruct (stk_carve rsegs m lo (lo + k) (Z.to_nat k) ST ltac:(lia)) as [_ [junk H]].
  exists junk. replace (lo + k - Z.of_nat (Z.to_nat k))%Z with lo in H by lia. exact H.
Qed.

Lemma rw_cells_CB1 : forall m a bs, rw_cells rsegs m a [CB 1 bs] -> exists z, rw_cells rsegs m a [C1 z].
Proof.
  intros m a bs [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [Hl _].
  destruct bs as [|z [|]]; cbn in Hl; try lia. exists z.
  split; [split; [cbn; tauto | exact Hb] | exact Hw].
Qed.

Lemma mbytes_bytes_at : forall m a bs, (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  mbytes B m a bs -> bytes_at rsegs m a bs.
Proof.
  intros m a bs Ha Hl H. unfold mbytes in H. rewrite SEGS in H. split; [lia|]. split; [lia|].
  intros i Hi. specialize (H (Z.of_nat i) ltac:(lia)). rewrite Nat2Z.id in H. exact H.
Qed.

Lemma bytes_at_mbytes : forall m a bs, bytes_at rsegs m a bs -> mbytes B m a bs.
Proof.
  intros m a bs (Ha & Hl & H). unfold mbytes. rewrite SEGS. intros i Hi.
  specialize (H (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in H by lia. exact H.
Qed.

Lemma rw_rec : forall m t b len cap, (0 <= t)%Z -> (t + 24 <= 2 ^ 64)%Z -> text_rec B m t b len cap ->
  (forall i, (0 <= i < 24)%Z -> writable_at (ms_segs B) m (t + i)) ->
  rw_cells rsegs m t [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 cap)].
Proof.
  intros m t b len cap Ht Ht1 [R _] W. split.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    apply mbytes_bytes_at; [lia | rewrite !length_app, !length_le8; cbn; lia | exact R].
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi. rewrite SEGS in W. apply W. lia.
Qed.

(* The `failed` field (offset 24) of the record, as the cell the walk's `lw` at 0x154d8 reads. *)
Lemma ro_fail : forall m t b len cap, (0 <= t)%Z -> text_rec B m t b len cap ->
  ro_cells rsegs m (t + 24) [C4 (Z_to_bv 64 0)].
Proof.
  intros m t b len cap Ht (_ & T28 & R). split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
  apply mbytes_bytes_at; [lia | rewrite length_le4; cbn; lia | exact R].
Qed.

Lemma rec_of_rw : forall m t b len cap,
  rw_cells rsegs m t [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 cap)] ->
  (t + 28 <= 2 ^ 64)%Z -> mbytes B m (t + 24) (le4 (Z_to_bv 64 0)) ->
  text_rec B m t b len cap /\ (forall i, (0 <= i < 24)%Z -> writable_at (ms_segs B) m (t + i)).
Proof.
  intros m t b len cap [[_ Hb] (_ & _ & Hw)] T28 FL. split.
  - split; [|split; [exact T28 | exact FL]].
    apply bytes_at_mbytes. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
  - intros i Hi. rewrite SEGS. apply Hw. cbn. lia.
Qed.

Lemma rw_cells_same : forall m m' A cs, rw_cells rsegs m A cs ->
  (forall a, (A <= a < A + Z.of_nat (cells_size cs))%Z ->
     mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a -> writable_at rsegs m' a)) ->
  rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs [[Hwf (Ha & Hl & Hb)] (_ & _ & Hw)] H.
  pose proof (cells_bytes_length cs Hwf) as CL.
  split; [split; [exact Hwf|]|].
  - split; [lia|]. split; [lia|]. intros i Hi.
    destruct (H (A + Z.of_nat i)%Z) as [E _]; [lia|].
    change (mrd rsegs m' (wa (A + Z.of_nat i))) with (mbyte rsegs m' (A + Z.of_nat i)).
    rewrite E. apply Hb. exact Hi.
  - split; [lia|]. split; [lia|]. intros i Hi.
    destruct (H (A + i)%Z) as [_ W]; [lia|]. apply W. apply Hw. exact Hi.
Qed.

Lemma ro_mbyte : forall m a, mem_inv rsegs m -> ro_addr rsegs (Z_to_bv 64 a) = true ->
  mbyte rsegs m a = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom rsegs (Z_to_bv 64 a).
Proof.
  intros m a MI R. unfold mbyte. destruct (m (Z_to_bv 64 a)) eqn:E; [|reflexivity].
  pose proof (MI _ _ E). congruence.
Qed.

Lemma present_not_ro : forall m a, mem_inv rsegs m -> present m a -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof. intros m a MI [x Hx]. exact (MI _ _ Hx). Qed.

Lemma in_blocks : forall L A a k, In (a, k) (blocks L A) -> exists p, In (p, k) (user_blocks A) /\ ptr_addr L p = a.
Proof.
  intros L A a k H. unfold blocks in H. apply in_map_iff in H. destruct H as ([p k'] & E & Hin).
  cbn in E. inversion E; subst. exists p. split; [exact Hin | reflexivity].
Qed.

Lemma block_facts : forall L A mem md a k i, aa_MR API L A mem md -> In (a, k) (blocks L A) -> (0 <= i < k)%Z ->
  present mem (a + i) /\ (4096 <= a)%Z /\ (a + k <= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling)%Z /\ ~ owned B L A (a + i).
Proof.
  intros L A mem md a k i MR H Hi. destruct (in_blocks _ _ _ _ H) as (p & Hp & <-).
  exact (mr_blocks _ _ (aa_laws API) _ _ _ _ _ _ _ MR Hp Hi).
Qed.

Lemma mr_store : forall L A m m' md W, aa_MR API L A m md -> munch W m m' -> wmono rsegs m m' ->
  (forall a, ~ outside W a -> (0 <= a < 2 ^ 64)%Z /\ (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling <= a \/ ~ in_img B a)%Z) ->
  (forall a, owned B L A a -> outside W a) ->
  aa_MR API L A m' md.
Proof.
  intros L A m m' md W MR MU WM HW HO. pose proof (aa_laws API) as LAWS. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as ACV.
  destruct (mr_model _ _ LAWS _ _ _ _ MR) as (Hh & Hl & Hm).
  eapply (mr_frame _ _ LAWS); try eassumption; try reflexivity.
  - intros a Ho. pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ MR Ho). unfold mbyte.
    rewrite (MU (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit by lia. apply HO. exact Ho.
  - intros a Ho [x Hx]. pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ MR Ho). exists x.
    rewrite (MU (Z_to_bv 64 a)); [exact Hx|]. rewrite unsigned_lit by lia. apply HO. exact Ho.
  - intros p k i Hin Hi. destruct (mr_blocks _ _ LAWS _ _ _ _ _ _ _ MR Hin Hi) as (Hp & H4 & Hc & _).
    destruct (outside_dec W (ptr_addr L p + i)) as [Ho|Ho].
    + destruct Hp as [x Hx]. exists x. rewrite (MU (Z_to_bv 64 _)); [exact Hx|]. rewrite unsigned_lit by lia. exact Ho.
    + destruct (HW _ Ho) as [Hr Hc'].
      apply present_of_writable; [exact Hr | exact Hc' |].
      pose proof (writable_of_present _ _ Hp) as Wp. unfold writable_at in *. rewrite SEGS in *. apply WM. exact Wp.
Qed.


Lemma in_img_range : forall a, in_img B a -> (0 <= a < 2 ^ 40)%Z.
Proof.
  intros a [_ (r & Hr & H1)]. rewrite SEGS in Hr.
  assert (E : forallb (fun r => bv_unsigned (fst r) + bv_unsigned (snd r) <=? 2 ^ 40)%Z (segments_reserved rsegs) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in E. specialize (E r Hr). apply Z.leb_le in E.
  pose proof (bv_unsigned_in_range _ (fst r)). lia.
Qed.

Lemma munch_byte : forall W m m' a, munch W m m' -> (0 <= a < 2 ^ 64)%Z -> outside W a ->
  mbyte (ms_segs B) m' a = mbyte (ms_segs B) m a /\ (writable_at (ms_segs B) m a <-> writable_at (ms_segs B) m' a).
Proof.
  intros W m m' a MU Ha Ho.
  assert (E : m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) by (apply MU; rewrite unsigned_lit by lia; exact Ho).
  unfold mbyte, writable_at, wview. rewrite E. tauto.
Qed.

Lemma mbytes_app : forall m a x y, mbytes B m a (x ++ y) <-> mbytes B m a x /\ mbytes B m (a + Z.of_nat (length x)) y.
Proof.
  intros m a x y. unfold mbytes. rewrite length_app. split.
  - intros H. split.
    + intros i Hi. rewrite H by lia. rewrite nth_error_app1 by lia. reflexivity.
    + intros i Hi. replace (a + Z.of_nat (length x) + i)%Z with (a + (Z.of_nat (length x) + i))%Z by lia.
      rewrite H by lia. rewrite nth_error_app2 by lia. f_equal. lia.
  - intros [H1 H2] i Hi. destruct (Z_lt_ge_dec i (Z.of_nat (length x))).
    + rewrite H1 by lia. rewrite nth_error_app1 by lia. reflexivity.
    + replace (a + i)%Z with (a + Z.of_nat (length x) + (i - Z.of_nat (length x)))%Z by lia.
      rewrite H2 by lia. rewrite nth_error_app2 by lia. f_equal. lia.
Qed.

Lemma mbytes_same : forall m m' a bs,
  mbytes B m a bs -> (forall i, (0 <= i < Z.of_nat (length bs))%Z -> mbyte (ms_segs B) m' (a + i) = mbyte (ms_segs B) m (a + i)) ->
  mbytes B m' a bs.
Proof. intros m m' a bs H E i Hi. rewrite E by exact Hi. apply H. exact Hi. Qed.

Lemma ret_ok_pc : forall k, OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok k -> ret_pc k = k.
Proof.
  intros k H. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok in H.
  assert (E : (bv_unsigned k mod 2 = 0)%Z).
  { rewrite <- H. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK14.v_jalr. rewrite Z_to_bv_unsigned. unfold bv_wrap. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.jalr_tgtZ.
    set (x := Z.land (bv_unsigned k + 0) (-2)).
    assert (X : (x mod 2 = 0)%Z).
    { replace 2%Z with (2 ^ 1)%Z by reflexivity. rewrite <- Z.land_ones by lia. subst x.
      rewrite <- Z.land_assoc. change (Z.land (-2) (Z.ones 1)) with 0%Z. apply Z.land_0_r. }
    change (bv_modulus 64) with (2 * 2 ^ 63)%Z. rewrite (Z.mod_eq x (2 * 2 ^ 63)) by lia.
    replace (x - 2 * 2 ^ 63 * (x / (2 * 2 ^ 63)))%Z with (x + (- (2 ^ 63 * (x / (2 * 2 ^ 63)))) * 2)%Z by ring.
    rewrite Z_mod_plus_full. exact X. }
  rewrite <- (Z_to_bv_bv_unsigned k). apply ret_pc_even; [| exact E].
  pose proof (bv_unsigned_in_range 64 k) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

Lemma sr_evt : forall regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  evt rsegs Q (MS (mkR (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 5) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 6) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 7)
          (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 8) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 9) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 10) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 11) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 12) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 13) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 14)
          (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 15) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 16) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 17) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 18) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 19) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 20) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 21)
          (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 22) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 23) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 24) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 25) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 26) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 27) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 28)
          (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 29) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 30) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 31)) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall ms', (exists can, Q can /\ Regs6ss.ms_eqv can ms') -> SR (ms_segs B) (mkCfg ms' md) P) ->
  SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs pc mem (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros regs pc mem md Q P Hh Hl HE K. rewrite SEGS in K |- *.
  apply (evt_SR_canon rsegs _ Q md P); [exact HE | exact Hh | exact Hl | exact K].
Qed.

Ltac getr_val HR :=
  lazymatch goal with
  | |- context [OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr ?X ?k] =>
      change (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr X k) with (reg_get X k); rewrite HR by reflexivity
  end.

Ltac regs_pres HR :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; unfold callee_saved in Hr;
  assert (Hc : (r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)%Z) by lia;
  repeat destruct Hc as [Hc|Hc]; subst r;
  lazymatch goal with |- OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr ?X ?k = _ => change (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr X k) with (reg_get X k) end;
  rewrite HR by reflexivity; simp_regs; reflexivity.

Lemma ro_false : forall a, (0 <= a < 2 ^ 64)%Z -> (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling <= a \/ ~ in_img B a)%Z ->
  ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha Hc. unfold ro_addr. rewrite unsigned_lit by lia. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value.
  destruct (find_segment rsegs a 1) as [seg|] eqn:F; [|reflexivity]. exfalso.
  destruct Hc as [Hc|Hc].
  - destruct (find_segment_some _ _ _ _ F) as (Hin & _ & H2). pose proof (rsegs_low _ Hin). lia.
  - apply Hc. eapply find_img; [lia | exact F].
Qed.

Lemma rw_cells_norm : forall m A cs, ro_agree rsegs m -> rw_cells rsegs m A cs ->
  (forall i, (0 <= i < Z.of_nat (cells_size cs))%Z -> ro_addr rsegs (wa (A + i)) = false) ->
  rw_cells rsegs (normalize rsegs m) A cs.
Proof.
  intros m A cs RA [[Hwf Hb] Hw] Hro. split; [split; [exact Hwf | apply bytes_at_normalize; assumption] |].
  apply (wr_at_norm rsegs m (normalize rsegs m)); [apply mem_rel_normalize; exact RA | exact Hw | exact Hro].
Qed.

Lemma rw_cells_rel : forall m m0 A cs, mem_rel rsegs m m0 -> rw_cells rsegs m0 A cs -> rw_cells rsegs m A cs.
Proof.
  intros m m0 A cs HR [[Hwf Hb] Hw]. split; [split; [exact Hwf|] |].
  - apply (proj2 (bytes_at_rel rsegs m m0 A _ HR)). exact Hb.
  - apply (wr_at_rel rsegs m m0 A _ HR). exact Hw.
Qed.

Lemma final_n : forall R F pc fc m0 ro can ms',
  ms_rel rsegs can (MS R F pc fc None m0 ro) -> Regs6ss.ms_eqv can ms' -> F = fp_regs -> fc = fp_csr ->
  ms' = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst (ms_regs ms') pc (ms_mem ms') ro /\
  (forall r : reg, is_x0 r = false -> reg_get (ms_regs ms') r = reg_get R r) /\
  mem_rel rsegs (ms_mem ms') m0 /\ ms_mem ms' = ms_mem can.
Proof.
  intros R F pc fc m0 ro [r1 f1 p1 v1 s1 c1 m1 o1] [r2 f2 p2 v2 s2 c2 m2 o2]
    (HR & HF & HP & HS & HV & HC & HO & HM) (ER & EF & EP & ES & EV & EC & EM & EO) E1 E2.
  cbn in *. subst. split; [reflexivity|]. split; [|split; [exact HM | reflexivity]].
  intros r Hr. symmetry. apply ER. exact Hr.
Qed.

Lemma wmono_writable : forall m m' a, wmono rsegs m m' -> writable_at (ms_segs B) m a -> writable_at (ms_segs B) m' a.
Proof. intros m m' a WM H. unfold writable_at in *. rewrite SEGS in *. apply WM. exact H. Qed.

Lemma ro_agree_mbyte : forall m a, ro_agree rsegs m -> ro_addr rsegs (Z_to_bv 64 a) = true ->
  mbyte rsegs m a = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom rsegs (Z_to_bv 64 a).
Proof. intros m a RA H. exact (RA _ H). Qed.

Lemma sr_evt_n : forall regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree rsegs mem ->
  evt rsegs Q (MS (mkR (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 5)
          (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 6) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 7) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 8) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 9) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 10)
          (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 11) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 12) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 13) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 14) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 15)
          (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 16) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 17) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 18) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 19) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 20)
          (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 21) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 22) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 23) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 24) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 25)
          (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 26) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 27) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 28) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 29) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 30)
          (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 31)) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms', (exists can s0, Q s0 /\ ms_rel rsegs can s0 /\ ro_same rsegs mem (ms_mem can) /\ Regs6ss.ms_eqv can ms') ->
     SR (ms_segs B) (mkCfg ms' md) P) ->
  SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs pc mem (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros regs pc mem md Q P Hh Hl RA HE K.
  apply (sr_evt regs pc mem md (fun s => exists s0, Q s0 /\ ms_rel rsegs s s0 /\ ro_same rsegs mem (ms_mem s)) P Hh Hl).
  - apply evt_normalize; [vm_compute; reflexivity | exact RA | exact HE].
  - intros ms' (can & (s0 & HQ & HR & HO) & EQV). apply K. exists can, s0. auto.
Qed.

Lemma pairwise_mid : forall {T : Type} (R : T -> T -> Prop) l1 x l2 y,
  pairwise R (l1 ++ x :: l2) -> In y (l1 ++ l2) -> R y x \/ R x y.
Proof.
  intros T R l1. induction l1 as [|h l1 IH]; cbn; intros x l2 y Hp Hy.
  - destruct Hp as [H1 _]. right. apply H1. exact Hy.
  - destruct Hp as [H1 H2]. destruct Hy as [<-|Hy].
    + left. apply H1. apply in_or_app. right. left. reflexivity.
    + eapply IH; eassumption.
Qed.

Lemma call_post_k_mono : forall stk L A regs mem md (E1 E2 : Z -> Prop) L' A' regs' mem' md',
  call_post_k B (aa_MR API) stk L A regs mem md E1 L' A' regs' mem' md' -> (forall a, E1 a -> E2 a) ->
  call_post_k B (aa_MR API) stk L A regs mem md E2 L' A' regs' mem' md'.
Proof.
  intros stk L A regs mem md E1 E2 L' A' regs' mem' md'
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) HE.
  repeat (split; [eassumption|]). split; [|split; [exact H9 | exact H10]].
  intros a Ha Ho1 Ho2 Hs He. apply H8; auto.
Qed.

Lemma blocks_kept_mono : forall L A mem mem' (g1 g2 : Z -> Prop),
  blocks_kept B L A mem mem' g1 -> (forall a, g1 a -> g2 a) -> blocks_kept B L A mem mem' g2.
Proof.
  unfold blocks_kept. intros L A mem mem' g1 g2 H G a k i Hin Hg Hi.
  apply (H a k i Hin); [intros Hx; apply Hg; apply G; exact Hx | exact Hi].
Qed.

Lemma in_other : forall (bl : list (Z * Z)) bl1 bl2 b0 cap0 a k,
  In (a, k) bl -> a <> b0 ->
  ((cap0 = 0 /\ bl = bl1 ++ bl2) \/ (cap0 <> 0 /\ bl = bl1 ++ (b0, cap0) :: bl2)) -> In (a, k) (bl1 ++ bl2).
Proof.
  intros bl bl1 bl2 b0 cap0 a k Hin Hne [[_ E]|[_ E]]; subst bl; [exact Hin|].
  apply in_app_or in Hin. apply in_or_app. destruct Hin as [H|[H|H]]; [left; exact H | | right; exact H].
  inversion H. congruence.
Qed.

Ltac gval HR :=
  lazymatch goal with |- OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr ?X ?k = _ => change (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr X k) with (reg_get X k) end;
  rewrite HR by reflexivity; simp_regs; reflexivity.

Theorem tx_put_holds : realloc_contract_r B API RFm TX_REALLOC -> realloc_null_contract_r B API RFm TX_REALLOC ->
  memcpy_contract -> tx_put_contract B API RFm.
Proof.
  intros RC RNC MC. unfold tx_put_contract.
  intros L A regs mem md t s n b0 len0 cap0 txt src bnd PRE INIT RA0 R10 R11 R12 Tlo Thi Tal TW Rb Rl Rc REC INV
    Sr Sn Shi SRCB SRCL SP NEED RES ROOM.
  pose proof (aa_laws API) as LAWS. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as ACV.
  pose proof PRE as (MR0 & WF0 & BD0 & RET & SPal & SPlo & SPhi & WIN & TP & ERRW & AUX).
  destruct (mr_model _ _ LAWS _ _ _ _ MR0) as (Hh & Hlz & Hmat).
  unfold TX_STACK, REALLOC_STACK, ALLOC_STACK in *.
  pose proof (bv_unsigned_in_range 64 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold spZ in *.
  rewrite SEGS in RA0. rename RA0 into RA.
  pose proof (rw_rec mem t b0 len0 cap0 ltac:(lia) Thi REC TW) as RECW.
  pose proof (proj1 (proj2 REC)) as T28. pose proof (proj2 (proj2 REC)) as FL0.
  assert (FLN : ro_cells rsegs (normalize rsegs mem) (t + 24) [C4 (Z_to_bv 64 0)]).
  { destruct (ro_fail mem t b0 len0 cap0 ltac:(lia) REC) as [FW FB]. split; [exact FW|].
    apply bytes_at_normalize; assumption. }
  assert (SRC : bytes_at rsegs mem s src) by (apply mbytes_bytes_at; [lia | lia | exact SRCB]).
  assert (FRP : forall i, (0 <= i < 32)%Z -> present mem (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32 + i)).
  { intros i Hi. apply present_of_writable; [lia | left; lia | apply WIN; lia]. }
  edestruct (rw_of_present mem (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32) 32) as [j FRJ]; [lia | lia | lia | exact FRP |].
  change (Z.to_nat 32) with 32%nat in FRJ.
  assert (RECN : rw_cells rsegs (normalize rsegs mem) t [C8 (Z_to_bv 64 b0); C8 (Z_to_bv 64 len0); C8 (Z_to_bv 64 cap0)]).
  { apply rw_cells_norm; [exact RA | exact RECW |]. intros i Hi. cbn in Hi. apply ro_false; lia. }
  assert (FRN : rw_cells rsegs (normalize rsegs mem) (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32) [CB 32 j]).
  { apply rw_cells_norm; [exact RA | exact FRJ |]. intros i Hi. cbn in Hi. apply ro_false; lia. }
  assert (SRCN : bytes_at rsegs (normalize rsegs mem) s src) by (apply bytes_at_normalize; assumption).
  pose proof (mem_inv_normalize rsegs mem) as MIN.
  destruct (Z_le_gt_dec (len0 + n + 1) cap0) as [FIT|GROW].
  - destruct INV as (TL & [(C0 & B0 & L0) | (Cpos & BIN & LC & TXT & NOIMG)]); [lia|].
    assert (BF : forall i, (0 <= i < cap0)%Z -> present mem (b0 + i) /\ (4096 <= b0)%Z /\ (b0 + cap0 <= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling)%Z /\ ~ owned B L A (b0 + i))
      by (intros i Hi; exact (block_facts _ _ _ _ _ _ i MR0 BIN Hi)).
    destruct (BF 0%Z ltac:(lia)) as (_ & B4 & BC & _).
    edestruct (rw_of_present mem (b0 + len0) n) as [junk DST]; [lia | lia | lia | |].
    { intros i Hi. replace (b0 + len0 + i)%Z with (b0 + (len0 + i))%Z by lia. apply BF. lia. }
    edestruct (rw_of_present mem (b0 + len0 + n) 1) as [jz ZB0]; [lia | lia | lia | |].
    { intros i Hi. replace (b0 + len0 + n + i)%Z with (b0 + (len0 + n + i))%Z by lia. apply BF. lia. }
    destruct (rw_cells_CB1 _ _ _ ZB0) as [z ZB]. clear ZB0.
    assert (DSTN : rw_cells rsegs (normalize rsegs mem) (b0 + len0) [CB (Z.to_nat n) junk]).
    { apply rw_cells_norm; [exact RA | exact DST |]. intros i Hi. cbn in Hi. apply ro_false; [lia | right].
      replace (b0 + len0 + i)%Z with (b0 + (len0 + i))%Z by lia. apply NOIMG. lia. }
    assert (ZBN : rw_cells rsegs (normalize rsegs mem) (b0 + len0 + n) [C1 z]).
    { apply rw_cells_norm; [exact RA | exact ZB |]. intros i Hi. cbn in Hi. apply ro_false; [lia | right].
      replace (b0 + len0 + n + i)%Z with (b0 + (len0 + n + i))%Z by lia. apply NOIMG. lia. }
    assert (DSj : (n = 0 \/ s + n <= b0 + len0 \/ b0 + len0 + n + 1 <= s)%Z).
    { edestruct (ivl_disj s n b0 (b0 + cap0)) as [[H|[H|H]]|H]; [lia | intros i Hi; apply (SP i Hi) | lia..]. }
    assert (STj : (n = 0 \/ s + n <= t \/ t + 24 <= s)%Z).
    { edestruct (ivl_disj s n t (t + 24)) as [[H|[H|H]]|H]; [lia | intros i Hi; apply (SP i Hi) | lia..]. }
    assert (FSj : (n = 0 \/ bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) <= s \/ s + n <= bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32)%Z).
    { edestruct (ivl_disj s n (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) - (8192 + 64 + 32)) (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2)))
        as [[H|[H|H]]|H]; [lia | intros i Hi; apply (SP i Hi) | lia..]. }
    eapply (sr_evt_n regs _ mem md); [exact Hh | exact Hlz | exact RA | |].
    + rewrite R10, R11, R12.
      apply (tx_head_nogrow MC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fp_regs fp_csr (normalize rsegs mem)
               t s n b0 len0 cap0 (b0 + len0) (b0 + len0 + n) src junk j z);
        try reflexivity; try eassumption; lia.
    + intros ms' (can & s0 & HQ & HREL & RS & EQV).
      destruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                      -> & MU & WM & MI2 & REC2 & DB2).
      destruct (final_n _ _ _ _ _ _ _ _ HREL EQV eq_refl eq_refl) as (EMS & HR & MRL & EM).
      rewrite <- EM in RS.
      pose proof (munch_rel rsegs _ mem (normalize rsegs mem) (ms_mem ms') m0' (mem_rel_normalize rsegs mem RA) MRL RS MU) as MU'.
      pose proof (wmono_rel rsegs mem (normalize rsegs mem) (ms_mem ms') m0' (mem_rel_normalize rsegs mem RA) MRL RS WM) as WM'.
      pose proof (ro_agree_same rsegs mem (ms_mem ms') RA RS) as RA'.
      pose proof (rw_cells_rel _ _ _ _ MRL REC2) as REC2'.
      pose proof (proj2 (bytes_at_rel rsegs _ _ _ _ MRL) DB2) as DB2'.
      clear MU WM REC2 DB2 MI2.
      assert (OUTW : forall a, (0 <= a < 2 ^ 64)%Z ->
                ~ (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32 <= a < bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2))%Z ->
                ~ (t <= a < t + 24)%Z -> ~ (b0 + len0 <= a < b0 + len0 + n + 1)%Z ->
                mbyte (ms_segs B) (ms_mem ms') a = mbyte (ms_segs B) mem a /\
                (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) (ms_mem ms') a)).
      { intros a Ha H1 H2 H3. apply (munch_byte _ _ _ _ MU' Ha). cbn [outside]. repeat split; lia. }
      assert (MR' : aa_MR API L A (ms_mem ms') md).
      { apply (mr_store L A mem (ms_mem ms') md _ MR0 MU' WM').
        - intros a Ho.
          assert (Hc : (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32 <= a < bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32 + 32 \/
                        t <= a < t + 24 \/ b0 + len0 <= a < b0 + len0 + n + 1)%Z) by (cbn [outside] in Ho; lia).
          destruct Hc as [Hc|[Hc|Hc]]; [split; [lia | left; lia] | split; [lia | left; lia] |].
          split; [lia | right]. replace a with (b0 + (a - b0))%Z by lia. apply NOIMG. lia.
        - intros a Ho. pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ MR0 Ho). cbn [outside].
          split; [lia|]. split; [lia|]. split; [|exact I]. intros Hd.
          apply (proj2 (proj2 (proj2 (BF (a - b0)%Z ltac:(lia))))). replace (b0 + (a - b0))%Z with a by lia. exact Ho. }
      rewrite EMS. apply SR_ret.
      exists L, A, (ms_regs ms'), (ms_mem ms'), md, b0, cap0, bnd.
      split. { f_equal. rewrite ret_ok_pc by exact RET. rewrite SEGS. reflexivity. }
      split.
      { unfold tx_frame. split; [exact MR'|]. split; [exact WF0|]. split; [exact BD0|]. split; [apply layout_le_refl|].
        split; [intros; reflexivity|]. split; [exists (m_vmmaps md); apply vm_id|].
        split.
        { intros a Ha Ho1 Ho2 Hsc HE.
          assert (Hr : (0 <= a < 2 ^ 64)%Z) by (destruct Ha as [Ha|Ha]; [lia | apply in_img_range in Ha; lia]).
          unfold scratch_k, spZ, tx_writes in Hsc, HE. apply OUTW; [exact Hr | lia | lia | lia]. }
        split.
        { intros p k i Hin1 Hin2 Hi HE. destruct (mr_blocks _ _ LAWS _ _ _ _ _ _ _ MR0 Hin1 Hi) as (_ & H4 & Hc & _).
          unfold tx_writes in HE. refine (proj1 (OUTW _ _ _ _ _)); lia. }
        { intros a Hsc. unfold scratch_k, spZ in Hsc. apply (wmono_writable mem); [exact WM'|].
          destruct Hsc as [Hsc|Hsc]; [apply WIN | apply ERRW]; lia. } }
      split. { regs_pres HR. }
      split.
      { unfold blocks_kept. intros a k i Hin Hne Hi.
        destruct (block_facts _ _ _ _ _ _ i MR0 Hin Hi) as (_ & H4 & Hc & _).
        destruct (pairwise_in _ _ _ _ (mr_blocks_disjoint _ _ LAWS _ _ _ _ MR0) Hin BIN
                    ltac:(intros E; inversion E; congruence)) as [D|D];
          unfold ranges_disjoint in D; cbn [fst snd] in D; refine (proj1 (OUTW _ _ _ _ _)); lia. }
      assert (FL2 : mbytes B (ms_mem ms') (t + 24) (le4 (Z_to_bv 64 0))).
      { apply (mbytes_same mem); [exact FL0|]. intros i Hi. rewrite length_le4 in Hi. cbn in Hi.
        refine (proj1 (OUTW _ _ _ _ _)); lia. }
      destruct (rec_of_rw _ _ _ _ _ REC2' T28 FL2) as [TR2 TW2].
      split. { exact TR2. }
      split. { exact TW2. }
      split.
      { unfold tx_inv. split; [rewrite length_app; lia|]. right. split; [lia|]. split; [exact BIN|]. split; [lia|].
        split; [|exact NOIMG].
        rewrite <- app_assoc. apply mbytes_app. split.
        - apply mbytes_app in TXT. destruct TXT as [TXT0 _]. apply (mbytes_same mem); [exact TXT0|].
          intros i Hi. refine (proj1 (OUTW _ _ _ _ _)); lia.
        - rewrite TL. apply bytes_at_mbytes. exact DB2'. }
      split.
      { apply (mbytes_same mem); [exact SRCB|]. intros i Hi. destruct (SP i ltac:(lia)) as (S1 & S2 & S3 & _).
        refine (proj1 (OUTW _ _ _ _ _)); lia. }
      split. { rewrite SEGS. exact RA'. }
      split.
      { unfold guard_kept. intros i Hi.
        assert (HO : owned B L A (ms_got_guard B + i)) by (right; unfold static_owned; do 4 right; left; lia).
        pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ MR0 HO).
        refine (proj1 (OUTW _ _ _ _ _)); try lia. intros Hd.
        apply (proj2 (proj2 (proj2 (BF (ms_got_guard B + i - b0)%Z ltac:(lia))))).
        replace (b0 + (ms_got_guard B + i - b0))%Z with (ms_got_guard B + i)%Z by lia. exact HO. }
      split. { exact INIT. }
      split. { lia. }
      split. { exact RES. }
      left. split; [lia | repeat split].
  - pose proof (fun i Hi => SP i Hi) as SP'.
    eapply (sr_evt_n regs _ mem md); [exact Hh | exact Hlz | exact RA | |].
    + rewrite R10, R11, R12.
      apply (tx_head_grow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fp_regs fp_csr (normalize rsegs mem)
               t s n b0 len0 cap0 (2 * (len0 + n + 1)) j); try reflexivity; try eassumption; lia.
    + intros ms1 (can1 & s01 & HQ1 & HREL1 & RS1 & EQV1).
      destruct HQ1 as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m01 &
                       -> & MU1 & WM1 & MI1 & FR1 & REC1).
      destruct (final_n _ _ _ _ _ _ _ _ HREL1 EQV1 eq_refl eq_refl) as (EMS1 & HR1 & MRL1 & EM1).
      rewrite <- EM1 in RS1.
      pose proof (munch_rel rsegs _ mem (normalize rsegs mem) (ms_mem ms1) m01 (mem_rel_normalize rsegs mem RA) MRL1 RS1 MU1) as MU1'.
      pose proof (wmono_rel rsegs mem (normalize rsegs mem) (ms_mem ms1) m01 (mem_rel_normalize rsegs mem RA) MRL1 RS1 WM1) as WM1'.
      pose proof (ro_agree_same rsegs mem (ms_mem ms1) RA RS1) as RA1.
      pose proof (rw_cells_rel _ _ _ _ MRL1 FR1) as FR1'.
      pose proof (rw_cells_rel _ _ _ _ MRL1 REC1) as REC1'.
      clear MU1 WM1 FR1 REC1 MI1.
      assert (G1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr (ms_regs ms1) 1 = Z_to_bv 64 0x15508) by gval HR1.
      assert (G2 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr (ms_regs ms1) 2 = Z_to_bv 64 (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32)) by gval HR1.
      assert (G4 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr (ms_regs ms1) 4 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4) by gval HR1.
      assert (G8 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr (ms_regs ms1) 8 = Z_to_bv 64 t) by gval HR1.
      assert (G9 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr (ms_regs ms1) 9 = Z_to_bv 64 n) by gval HR1.
      assert (G10 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr (ms_regs ms1) 10 = Z_to_bv 64 b0) by gval HR1.
      assert (G11 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr (ms_regs ms1) 11 = Z_to_bv 64 (2 * (len0 + n + 1))) by gval HR1.
      assert (G18 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr (ms_regs ms1) 18 = Z_to_bv 64 s) by gval HR1.
      assert (SP1 : spZ (ms_regs ms1) = bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32).
      { unfold spZ. change (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr (ms_regs ms1) 2) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr (ms_regs ms1) 2). rewrite G2. apply unsigned_lit. lia. }
      assert (MR1 : aa_MR API L A (ms_mem ms1) md).
      { apply (mr_store L A mem (ms_mem ms1) md _ MR0 MU1' WM1').
        - intros a Ho. assert (Hc : (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32 <= a < bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32 + 32 \/
                        t <= a < t + 24)%Z) by (cbn [outside] in Ho; lia).
          split; [lia | left; lia].
        - intros a Ho. pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ MR0 Ho). cbn [outside]. repeat split; lia. }
      assert (PRE1 : call_pre_k B (aa_MR API) (8192 + 64) L A (ms_regs ms1) (ms_mem ms1) md).
      { unfold call_pre_k. split; [exact MR1|]. split; [exact WF0|]. split; [exact BD0|].
        split; [rewrite G1; apply OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok_even; vm_compute; reflexivity|].
        rewrite SP1. split; [lia|]. split; [lia|]. split; [lia|].
        split; [intros a Ha; apply (wmono_writable mem); [exact WM1' | apply WIN; lia]|].
        split; [rewrite G4; exact TP|].
        split; [intros a Ha; apply (wmono_writable mem); [exact WM1' | apply ERRW; lia]|].
        intros HI. congruence. }
      rewrite EMS1.
      set (c := (2 * (len0 + n + 1))%Z) in *.
      set (f := (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + -32)%Z) in *.
      set (m1 := ms_mem ms1) in *. set (regs1 := ms_regs ms1) in *.
      assert (RA1' : ro_agree (ms_segs B) m1) by (rewrite SEGS; exact RA1).
      assert (Rn : SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs1 (Z_to_bv 64 0x19bfc) m1 (seg_rom rsegs)) md)
        (fun c' => exists L' A' regs2 m2 md2 q,
           c' = mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs2 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1 1) m2 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md2 /\
           call_post_k B (aa_MR API) (8192 + 64) L A regs1 m1 md (fun a => b0 <= a < b0 + cap0)%Z L' A' regs2 m2 md2 /\
           OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 10 = Z_to_bv 64 q /\ q <> 0 /\ (q mod 16 = 0)%Z /\ fresh_block B q c /\
           (exists bl1 bl2 bm1 bm2, blocks L' A' = bm1 ++ (q, c) :: bm2 /\ bm1 ++ bm2 = bl1 ++ bl2 /\
              ((cap0 = 0 /\ blocks L A = bl1 ++ bl2) \/ (cap0 <> 0 /\ blocks L A = bl1 ++ (b0, cap0) :: bl2))) /\
           blocks_kept B L A m1 m2 (fun a => a = b0) /\
           ro_agree (ms_segs B) m2 /\ guard_kept B m1 m2 /\
           (forall i, (0 <= i < Z.min cap0 c)%Z -> mbyte (ms_segs B) m2 (q + i) = mbyte (ms_segs B) m1 (b0 + i)) /\
           st_init_done A' = true /\ (length (st_regions A) <= length (st_regions A'))%nat /\
           rf_ok RFm A' (tx_step RFm bnd cap0 c))).
      { replace (seg_rom rsegs) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B)) by (rewrite SEGS; reflexivity).
        destruct INV as (TL & [(C0 & B0 & L0) | (Cpos & BIN & LC & TXT & NOIMG)]).
        - subst cap0 b0.
          eapply SR_mono; [apply (RNC L A regs1 m1 md c bnd PRE1 RA1'); [rewrite G10; reflexivity | exact G11 | rewrite G1, MALLOC_AT; intros E; apply (f_equal (@bv_unsigned 64)) in E; vm_compute in E; discriminate E | exact RES | exact (ROOM ltac:(lia))] |].
          intros c' (L' & A' & regs' & mem' & md' & res & -> & CP & R10' & Rnz & Ral & FRS & (b1 & b2 & E1 & E2) & BK &
                     ROA & GK & KEEPU & INIT' & LEN & RES').
          exists L', A', regs', mem', md', res. split; [reflexivity|].
          split; [eapply call_post_k_mono; [exact CP | intros a []]|].
          split; [exact R10'|]. split; [exact Rnz|]. split; [exact Ral|]. split; [exact FRS|].
          split; [exists b1, b2, b1, b2; split; [exact E1|]; split; [reflexivity | left; split; [reflexivity | exact E2]]|].
          split; [eapply blocks_kept_mono; [exact BK | intros a []]|].
          split; [exact ROA|]. split; [exact GK|]. split; [intros i Hi; lia|]. split; [exact INIT' | split; [exact LEN | exact RES']].
        - destruct (in_blocks _ _ _ _ BIN) as (p & Hp & Ep).
          destruct (block_facts _ _ _ _ _ _ 0 MR1 BIN ltac:(lia)) as (_ & B4 & BC & _).
          edestruct (rw_of_present m1 b0 cap0) as [old OLD]; [lia | lia | lia | |].
          { intros i Hi. exact (proj1 (block_facts _ _ _ _ _ _ i MR1 BIN Hi)). }
          destruct OLD as [[OWF OB] _]. cbn [cells_bytes cbytes cells_wf cell_wf] in OWF, OB. rewrite app_nil_r in OB.
          destruct OWF as [OL _].
          eapply SR_mono; [apply (RC L A regs1 m1 md p cap0 c old bnd PRE1 RA1' Hp); [rewrite G10, Ep; reflexivity | exact G11 | | | exact RES | exact (ROOM ltac:(lia))] |].
          + intros i Hi. rewrite Ep. pose proof (bytes_at_mbytes _ _ _ OB) as OM. unfold mbytes in OM.
            rewrite OL in OM. apply OM. lia.
          + rewrite OL. lia.
          + intros c' (L' & A' & regs' & mem' & md' & res & -> & CP & R10' & Rnz & Ral & FRS & (b1 & b2 & c1 & c2 & E1 & E2 & E3) &
                       BK & ROA & GK & KEEPU & PFX & INIT' & LEN & RES').
            rewrite Ep in CP, E1, BK.
            exists L', A', regs', mem', md', res. split; [reflexivity|].
            split; [exact CP|]. split; [exact R10'|]. split; [exact Rnz|]. split; [exact Ral|]. split; [exact FRS|].
            split; [exists b1, b2, c1, c2; split; [exact E2|]; split; [exact E3 | right; split; [lia | exact E1]]|].
            split; [exact BK|]. split; [exact ROA|]. split; [exact GK|].
            split; [|split; [exact INIT' | split; [exact LEN |
              unfold tx_step; rewrite (proj2 (Z.eqb_neq cap0 0)) by lia; exact RES']]].
            intros i Hi. rewrite PFX by lia. pose proof (bytes_at_mbytes _ _ _ OB) as OM. unfold mbytes in OM.
            rewrite OL in OM. symmetry. apply OM. lia. }
      eapply SR_bind; [exact Rn|].
      intros c2 (L' & A' & regs2 & m2 & md2 & q & -> & CP & R10q & Qnz & Qal & FRESH & BLS & BK & ROA2 & GK & PFX & INIT' & LEN2 & RES').
      destruct CP as (MR2 & WF2 & BD2 & LLE & PTR & REGP & (vm' & Emd) & FRM & BLK & SCR).
      destruct (mr_model _ _ LAWS _ _ _ _ MR2) as (Hh2 & Hlz2 & Hmat2).
      assert (RA2 : ro_agree rsegs m2) by (rewrite <- SEGS; exact ROA2).
      assert (QIN : In (q, c) (blocks L' A')).
      { destruct BLS as (bl1 & bl2 & bm1 & bm2 & E1 & _). rewrite E1. apply in_or_app. right. left. reflexivity. }
      destruct FRESH as (Q4 & QC & QNI).
      assert (QF : forall i, (0 <= i < c)%Z -> present m2 (q + i) /\ ~ owned B L' A' (q + i)).
      { intros i Hi. destruct (block_facts _ _ _ _ _ _ i MR2 QIN Hi) as (P & _ & _ & O). split; assumption. }
      assert (BLK0 : cap0 = 0 \/ (4096 <= b0 /\ b0 + cap0 <= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling)%Z).
      { destruct INV as (_ & [(C0 & _ & _) | (Cpos & BIN & _ & _ & _)]); [left; exact C0|].
        right. destruct (block_facts _ _ _ _ _ _ 0 MR0 BIN ltac:(lia)) as (_ & H1 & H2 & _). lia. }
      assert (HI12 : forall a, (f <= a < 2 ^ 64)%Z -> ~ (b0 <= a < b0 + cap0)%Z ->
                 mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
                 (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
      { intros a Ha Hb. apply FRM.
        - left. lia.
        - intros Ho. pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ MR1 Ho). lia.
        - intros Ho. pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ MR2 Ho). lia.
        - unfold scratch_k. rewrite SP1. lia.
        - exact Hb. }
      assert (HI12r : forall a, (f <= a < 2 ^ 64)%Z ->
                 mbyte rsegs m2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a -> writable_at rsegs m2 a)).
      { intros a Ha. rewrite <- SEGS. destruct (HI12 a Ha) as [E W]; [lia|]. split; [exact E | apply W]. }
      apply (rw_cells_same _ m2) in FR1'; [| intros a Ha; cbn in Ha; apply HI12r; lia].
      apply (rw_cells_same _ m2) in REC1'; [| intros a Ha; cbn in Ha; apply HI12r; lia].
      rename FR1' into FR2. rename REC1' into REC2.
      edestruct (rw_of_present m2 (q + len0) n) as [junk2 DST2]; [lia | lia | lia | |].
      { intros i Hi. replace (q + len0 + i)%Z with (q + (len0 + i))%Z by lia. apply QF. lia. }
      edestruct (rw_of_present m2 (q + len0 + n) 1) as [jz2 ZB20]; [lia | lia | lia | |].
      { intros i Hi. replace (q + len0 + n + i)%Z with (q + (len0 + n + i))%Z by lia. apply QF. lia. }
      destruct (rw_cells_CB1 _ _ _ ZB20) as [z2 ZB2]. clear ZB20.
      assert (FR2N := rw_cells_norm _ _ _ RA2 FR2). specialize (FR2N ltac:(intros i Hi; cbn in Hi; apply ro_false; lia)).
      assert (REC2N := rw_cells_norm _ _ _ RA2 REC2). specialize (REC2N ltac:(intros i Hi; cbn in Hi; apply ro_false; lia)).
      assert (DST2N : rw_cells rsegs (normalize rsegs m2) (q + len0) [CB (Z.to_nat n) junk2]).
      { apply rw_cells_norm; [exact RA2 | exact DST2 |]. intros i Hi. cbn in Hi. apply ro_false; [lia | right].
        replace (q + len0 + i)%Z with (q + (len0 + i))%Z by lia. apply QNI. lia. }
      assert (ZB2N : rw_cells rsegs (normalize rsegs m2) (q + len0 + n) [C1 z2]).
      { apply rw_cells_norm; [exact RA2 | exact ZB2 |]. intros i Hi. cbn in Hi. apply ro_false; [lia | right].
        replace (q + len0 + n + i)%Z with (q + (len0 + n + i))%Z by lia. apply QNI. lia. }
      pose proof (mem_inv_normalize rsegs m2) as MIN2.
      assert (SB2 : forall i, (0 <= i < n)%Z ->
                mbyte (ms_segs B) m2 (s + i) = mbyte (ms_segs B) mem (s + i) /\ ~ (q <= s + i < q + c)%Z).
      { intros i Hi. destruct (SP i Hi) as (S1 & S2 & S3 & S4).
        assert (E01 : mbyte (ms_segs B) m1 (s + i) = mbyte (ms_segs B) mem (s + i)).
        { apply (munch_byte _ _ _ _ MU1'); [lia|]. cbn [outside]. repeat split; lia. }
        destruct S4 as [S4|[S4|[S4|(a & k & Hin & Hne & Hr)]]].
        - lia.
        - split; [rewrite (proj1 (HI12 (s + i)%Z ltac:(lia) S3)); exact E01 | lia].
        - split.
          + rewrite SEGS in S4 |- *. rewrite (ro_agree_mbyte m2 _ RA2 S4). rewrite (ro_agree_mbyte mem _ RA S4). reflexivity.
          + intros Hq. assert (RF : ro_addr rsegs (Z_to_bv 64 (s + i)) = false).
            { apply ro_false; [lia | right]. replace (s + i)%Z with (q + (s + i - q))%Z by lia. apply QNI. lia. }
            rewrite SEGS in S4. congruence.
        - split.
          + unfold blocks_kept in BK. replace (s + i)%Z with (a + (s + i - a))%Z by lia.
            rewrite (BK a k (s + i - a)%Z Hin Hne) by lia. replace (a + (s + i - a))%Z with (s + i)%Z by lia. exact E01.
          + destruct BLS as (bl1 & bl2 & bm1 & bm2 & E1 & E2 & E3).
            pose proof (in_other _ _ _ _ _ _ _ Hin Hne E3) as Hin'. rewrite <- E2 in Hin'.
            pose proof (mr_blocks_disjoint _ _ LAWS _ _ _ _ MR2) as PW. rewrite E1 in PW.
            destruct (pairwise_mid _ _ _ _ _ PW Hin') as [D|D]; unfold ranges_disjoint in D; cbn [fst snd] in D; lia. }
      assert (SRC2 : bytes_at rsegs m2 s src).
      { apply mbytes_bytes_at; [lia | lia |]. apply (mbytes_same mem); [exact SRCB|]. intros i Hi. apply SB2. lia. }
      pose proof (bytes_at_normalize rsegs m2 s src RA2 SRC2) as SRC2N.
      assert (DS2 : (n = 0 \/ s + n <= q + len0 \/ q + len0 + n + 1 <= s)%Z).
      { edestruct (ivl_disj s n q (q + c)) as [[H|[H|H]]|H]; [lia | intros i Hi; apply (SB2 i Hi) | lia..]. }
      assert (ST2 : (n = 0 \/ s + n <= t \/ t + 24 <= s)%Z).
      { edestruct (ivl_disj s n t (t + 24)) as [[H|[H|H]]|H]; [lia | intros i Hi; apply (SP i Hi) | lia..]. }
      assert (FS2 : (n = 0 \/ f + 32 <= s \/ s + n <= f)%Z).
      { edestruct (ivl_disj s n (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) - (8192 + 64 + 32)) (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2)))
          as [[H|[H|H]]|H]; [lia | intros i Hi; apply (SP i Hi) | lia..]. }
      assert (H2' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 2 = Z_to_bv 64 f)
        by (transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1 2); [apply (REGP 2%Z); unfold callee_saved; lia | exact G2]).
      assert (H8' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 8 = Z_to_bv 64 t)
        by (transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1 8); [apply (REGP 8%Z); unfold callee_saved; lia | exact G8]).
      assert (H9' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 9 = Z_to_bv 64 n)
        by (transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1 9); [apply (REGP 9%Z); unfold callee_saved; lia | exact G9]).
      assert (H18' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 18 = Z_to_bv 64 s)
        by (transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1 18); [apply (REGP 18%Z); unfold callee_saved; lia | exact G18]).
      rewrite G1.
      eapply (sr_evt_n regs2 _ m2 md2); [exact Hh2 | exact Hlz2 | exact RA2 | |].
      * rewrite H2', H8', H9', R10q, H18'.
        eapply (tx_after MC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fp_regs fp_csr (normalize rsegs m2)
                 _ _ _ _ f t s n q b0 len0 cap0 c (q + len0) (q + len0 + n) src junk2 z2);
          try reflexivity; try eassumption; lia.
      * intros ms3 (can3 & s03 & HQ3 & HREL3 & RS3 & EQV3).
        destruct HQ3 as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' &
                         m03 & -> & MU3 & WM3 & MI3 & REC3 & DB3).
        destruct (final_n _ _ _ _ _ _ _ _ HREL3 EQV3 eq_refl eq_refl) as (EMS3 & HR3 & MRL3 & EM3).
        rewrite <- EM3 in RS3.
        pose proof (munch_rel rsegs _ m2 (normalize rsegs m2) (ms_mem ms3) m03 (mem_rel_normalize rsegs m2 RA2) MRL3 RS3 MU3) as MU3'.
        pose proof (wmono_rel rsegs m2 (normalize rsegs m2) (ms_mem ms3) m03 (mem_rel_normalize rsegs m2 RA2) MRL3 RS3 WM3) as WM3'.
        pose proof (ro_agree_same rsegs m2 (ms_mem ms3) RA2 RS3) as RA3.
        pose proof (rw_cells_rel _ _ _ _ MRL3 REC3) as REC3'.
        pose proof (proj2 (bytes_at_rel rsegs _ _ _ _ MRL3) DB3) as DB3'.
        clear MU3 WM3 REC3 DB3 MI3.
        set (m3 := ms_mem ms3) in *.
        pose proof (proj1 INV) as TL.
        assert (OUT3 : forall a, (0 <= a < 2 ^ 64)%Z -> ~ (f <= a < f + 32)%Z -> ~ (t <= a < t + 24)%Z ->
                  ~ (q + len0 <= a < q + len0 + n + 1)%Z ->
                  mbyte (ms_segs B) m3 a = mbyte (ms_segs B) m2 a /\
                  (writable_at (ms_segs B) m2 a <-> writable_at (ms_segs B) m3 a)).
        { intros a Ha H1 H2 H3. apply (munch_byte _ _ _ _ MU3' Ha). cbn [outside]. repeat split; lia. }
        assert (OUT1 : forall a, (0 <= a < 2 ^ 64)%Z -> ~ (f <= a < f + 32)%Z -> ~ (t <= a < t + 24)%Z ->
                  mbyte (ms_segs B) m1 a = mbyte (ms_segs B) mem a /\
                  (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) m1 a)).
        { intros a Ha H1 H2. apply (munch_byte _ _ _ _ MU1' Ha). cbn [outside]. repeat split; lia. }
        assert (MR3 : aa_MR API L' A' m3 md2).
        { apply (mr_store L' A' m2 m3 md2 _ MR2 MU3' WM3').
          - intros a Ho.
            assert (Hc : (f <= a < f + 32 \/ t <= a < t + 24 \/ q + len0 <= a < q + len0 + n + 1)%Z)
              by (cbn [outside] in Ho; lia).
            destruct Hc as [Hc|[Hc|Hc]]; [split; [lia | left; lia] | split; [lia | left; lia] |].
            split; [lia | right]. replace a with (q + (a - q))%Z by lia. apply QNI. lia.
          - intros a Ho. pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ MR2 Ho). cbn [outside].
            split; [lia|]. split; [lia|]. split; [|exact I]. intros Hd.
            apply (proj2 (QF (a - q)%Z ltac:(lia))). replace (q + (a - q))%Z with a by lia. exact Ho. }
        rewrite EMS3. apply SR_ret.
        exists L', A', (ms_regs ms3), m3, md2, q, c, (tx_step RFm bnd cap0 c).
        split. { f_equal. rewrite ret_ok_pc by exact RET. rewrite SEGS. reflexivity. }
        split.
        { unfold tx_frame. split; [exact MR3|]. split; [exact WF2|]. split; [exact BD2|]. split; [exact LLE|].
          split; [exact PTR|]. split; [exists vm'; exact Emd|].
          split.
          { intros a Ha Ho1 Ho2 Hsc HE.
            assert (Hr : (0 <= a < 2 ^ 64)%Z) by (destruct Ha as [Ha|Ha]; [lia | apply in_img_range in Ha; lia]).
            unfold scratch_k, spZ, tx_writes in Hsc, HE.
            edestruct (OUT3 a) as [E3 W3]; [exact Hr | lia | lia | lia |].
            edestruct (FRM a Ha Ho1 Ho2) as [E2 W2]; [unfold scratch_k; rewrite SP1; lia | lia |].
            edestruct (OUT1 a) as [E1 W1]; [exact Hr | lia | lia |].
            split; [rewrite E3, E2, E1; reflexivity | tauto]. }
          split.
          { intros p k i Hin1 Hin2 Hi HE. destruct (mr_blocks _ _ LAWS _ _ _ _ _ _ _ MR0 Hin1 Hi) as (_ & H4 & Hc & _).
            unfold tx_writes in HE.
            edestruct (OUT3 (ptr_addr L p + i)%Z) as [E3 _]; [lia | lia | lia | lia |].
            edestruct (OUT1 (ptr_addr L p + i)%Z) as [E1 _]; [lia | lia | lia |].
            rewrite E3, (BLK p k i Hin1 Hin2 Hi), E1. reflexivity. }
          { intros a Hsc. unfold scratch_k, spZ in Hsc.
            assert (W1 : writable_at (ms_segs B) m1 a).
            { apply (wmono_writable mem); [exact WM1'|]. destruct Hsc as [Hsc|Hsc]; [apply WIN | apply ERRW]; lia. }
            assert (W2 : writable_at (ms_segs B) m2 a).
            { destruct (Z_lt_ge_dec a f).
              - apply SCR. unfold scratch_k. rewrite SP1. lia.
              - apply (proj2 (HI12 a ltac:(lia) ltac:(lia))). exact W1. }
            apply (wmono_writable m2); [exact WM3' | exact W2]. } }
        split.
        { intros r Hr. unfold callee_saved in Hr.
          assert (Hc : (r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                        r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)%Z) by lia.
          repeat destruct Hc as [Hc|Hc]; subst r;
          lazymatch goal with |- OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr ?X ?k = _ => change (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr X k) with (reg_get X k) end;
          rewrite HR3 by reflexivity; simp_regs;
          first [ reflexivity
                | transitivity (Z_to_bv 64 (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2))); [f_equal; unfold f; lia | apply Z_to_bv_bv_unsigned]
                | lazymatch goal with |- _ = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs (Z_to_bv 5 ?k) =>
                    transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1 (Z_to_bv 5 k)); [apply (REGP k); unfold callee_saved; lia | gval HR1]
                  end ]. }
        split.
        { unfold blocks_kept. intros a k i Hin Hne Hi.
          destruct (block_facts _ _ _ _ _ _ i MR0 Hin Hi) as (_ & H4 & Hc & _).
          assert (D : (a + k <= q \/ q + c <= a)%Z).
          { destruct BLS as (bl1 & bl2 & bm1 & bm2 & E1 & E2 & E3).
            pose proof (in_other _ _ _ _ _ _ _ Hin Hne E3) as Hin'. rewrite <- E2 in Hin'.
            pose proof (mr_blocks_disjoint _ _ LAWS _ _ _ _ MR2) as PW. rewrite E1 in PW.
            destruct (pairwise_mid _ _ _ _ _ PW Hin') as [D|D]; unfold ranges_disjoint in D; cbn [fst snd] in D; lia. }
          edestruct (OUT3 (a + i)%Z) as [E3 _]; [lia | lia | lia | lia |].
          edestruct (OUT1 (a + i)%Z) as [E1 _]; [lia | lia | lia |].
          unfold blocks_kept in BK. rewrite E3, (BK a k i Hin Hne Hi), E1. reflexivity. }
        assert (FL3 : mbytes B m3 (t + 24) (le4 (Z_to_bv 64 0))).
        { apply (mbytes_same mem); [exact FL0|]. intros i Hi. rewrite length_le4 in Hi. cbn in Hi.
          edestruct (OUT3 (t + 24 + i)%Z) as [E3 _]; [lia | lia | lia | lia |].
          edestruct (HI12 (t + 24 + i)%Z) as [E2 _]; [lia | lia |].
          edestruct (OUT1 (t + 24 + i)%Z) as [E1 _]; [lia | lia | lia |].
          rewrite E3, E2, E1. reflexivity. }
        destruct (rec_of_rw _ _ _ _ _ REC3' T28 FL3) as [TR3 TW3].
        split. { exact TR3. }
        split. { exact TW3. }
        split.
        { unfold tx_inv. split; [rewrite length_app; lia|]. right. split; [lia|]. split; [exact QIN|]. split; [lia|].
          split; [|exact QNI].
          rewrite <- app_assoc. apply mbytes_app. split.
          - destruct INV as (_ & [(C0 & B0 & L0) | (Cpos & BIN & LC & TXT & NOIMG)]).
            + destruct txt; [intros i Hi; cbn in Hi; lia | cbn [length] in TL; lia].
            + intros i Hi. unfold mbytes in TXT.
              edestruct (OUT3 (q + i)%Z) as [E3 _]; [lia | lia | lia | lia |].
              edestruct (OUT1 (b0 + i)%Z) as [E1 _]; [lia | lia | lia |].
              rewrite E3, PFX by lia. rewrite E1, TXT by (rewrite length_app; cbn; lia).
              rewrite nth_error_app1 by lia. reflexivity.
          - rewrite TL. apply bytes_at_mbytes. exact DB3'. }
        split.
        { apply (mbytes_same mem); [exact SRCB|]. intros i Hi. destruct (SP i ltac:(lia)) as (S1 & S2 & S3 & _).
          destruct (SB2 i ltac:(lia)) as [Es Nq].
          edestruct (OUT3 (s + i)%Z) as [E3 _]; [lia | lia | lia | lia |].
          rewrite E3. exact Es. }
        split. { rewrite SEGS. exact RA3. }
        split.
        { unfold guard_kept. intros i Hi.
          assert (HS : static_owned B (ms_got_guard B + i)) by (unfold static_owned; do 4 right; left; lia).
          pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ MR0 (or_intror HS)).
          edestruct (OUT3 (ms_got_guard B + i)%Z) as [E3 _]; [lia | lia | lia | |].
          { intros Hd. apply (proj2 (QF (ms_got_guard B + i - q)%Z ltac:(lia))).
            replace (q + (ms_got_guard B + i - q))%Z with (ms_got_guard B + i)%Z by lia. right. exact HS. }
          edestruct (OUT1 (ms_got_guard B + i)%Z) as [E1 _]; [lia | lia | lia |].
          unfold guard_kept in GK. rewrite E3, (GK i Hi), E1. reflexivity. }
        split. { exact INIT'. }
        split. { exact LEN2. }
        split. { exact RES'. }
        right. split; [lia|]. split; [reflexivity|]. split; [exact Qal|]. split; [reflexivity|]. exact BLS.
Qed.
End KB.
