From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import Tac.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterSpec.
Import ListNotations.
Open Scope Z_scope.

Definition ENC_FRAME : Z := 32.
Definition ENC_KMAGIC : Z := 0x10420.
Definition ENC_MAGIC : Z := 12297829382473034411.
Definition ENC_TABLE : Z := 0x104a4.
Definition enc_M (len : Z) : Z := (len + 2) / 3 * 4 + 1.

Lemma land_m4 : forall z, 0 <= z < 2^64 -> Z.land z 18446744073709551612 = z / 4 * 4.
Proof.
  intros z Hz.
  replace 18446744073709551612 with (Z.land (Z.ones 64) (Z.lnot (Z.ones 2))) by (vm_compute; reflexivity).
  rewrite Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma enc_mulhu : forall x, 0 <= x <= 2^62 + 2 -> Z.shiftr (x * 12297829382473034411) 64 = 2 * x / 3.
Proof.
  intros x Hx. rewrite Z.shiftr_div_pow2 by lia.
  assert (H3 : x = 3 * (x / 3) + x mod 3) by (apply Z.div_mod; lia).
  assert (Hr : 0 <= x mod 3 < 3) by (apply Z.mod_pos_bound; lia).
  remember (x / 3) as t eqn:Et. remember (x mod 3) as r eqn:Er. clear Et Er.
  subst x.
  replace ((3 * t + r) * 12297829382473034411) with ((2 * t) * 2^64 + (t + r * 12297829382473034411)) by ring.
  replace (2 * (3 * t + r)) with ((2 * t) * 3 + 2 * r) by ring.
  rewrite !Z.div_add_l by lia.
  assert (r = 0 \/ r = 1 \/ r = 2) as [-> | [-> | ->]] by lia; Z.div_mod_to_equations; lia.
Qed.

Lemma enc_M_machine : forall len, 0 <= len <= 2^62 ->
  Z.land (Z.shiftl (Z.shiftr ((len + 2) * 12297829382473034411) 64 mod 18446744073709551616) 1
            mod 18446744073709551616) 18446744073709551612 + 1 = enc_M len.
Proof.
  intros len HL. rewrite enc_mulhu by lia.
  assert (Hy : 0 <= 2 * (len + 2) / 3 < 2^62) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (Z.mod_small (2 * (len + 2) / 3)) by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.mod_small by lia.
  rewrite land_m4 by lia.
  unfold enc_M. f_equal. Z.div_mod_to_equations. lia.
Qed.

Theorem enc_prologue : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (lo data len : Z) (m : word -> option byte),
  0 <= len <= 2^62 ->
  bytes_at rsegs m ENC_KMAGIC (le8 (Z_to_bv 64 ENC_MAGIC)) ->
  stk rsegs m lo (bv_unsigned sp) -> lo + ENC_FRAME <= bv_unsigned sp ->
  (ENC_KMAGIC + 8 <= bv_unsigned sp - ENC_FRAME \/ bv_unsigned sp <= ENC_KMAGIC) ->
  evt rsegs (fun ms' => exists junk m',
      ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - ENC_FRAME)) gp tp t0 t1 t2 (Z_to_bv 64 len) (Z_to_bv 64 data)
                 (Z_to_bv 64 (enc_M len)) (Z_to_bv 64 (len + 2)) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x14d44) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp - ENC_FRAME, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
      stk rsegs m' lo (bv_unsigned sp - ENC_FRAME) /\
      rw_cells rsegs m' (bv_unsigned sp - ENC_FRAME) [CB 8 junk; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 data) (Z_to_bv 64 len) a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14d10) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo data len m
    HL KM ST LO DK.
  unfold ENC_FRAME, ENC_KMAGIC, ENC_MAGIC in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  carve_frame 32%nat ST.
  zstep. zstep. zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  assert (RD : ov_read_bytes rsegs mm (wa 66592) 8 = Some (le8 (Z_to_bv 64 12297829382473034411)));
  [ replace (wa 66592) with (wa (66592 + 0)) by reflexivity;
    rewrite (bytes_at_read rsegs mm 66592 _ 0 8 KM ltac:(lia)) by (rewrite length_le8; lia);
    reflexivity | ] end.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  rewrite (enc_M_machine len HL).
  apply evt_done. eexists _, _. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact ST|exact FR].
Qed.

Theorem enc_call : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (lo data len : Z) (m : word -> option byte),
  0 <= len <= 2^62 ->
  bytes_at rsegs m ENC_KMAGIC (le8 (Z_to_bv 64 ENC_MAGIC)) ->
  stk rsegs m lo (bv_unsigned sp) -> lo + ENC_FRAME <= bv_unsigned sp ->
  (ENC_KMAGIC + 8 <= bv_unsigned sp - ENC_FRAME \/ bv_unsigned sp <= ENC_KMAGIC) ->
  evt rsegs (fun ms' => exists junk m',
      ms' = MS (mkR (Z_to_bv 64 0x14d48) (Z_to_bv 64 (bv_unsigned sp - ENC_FRAME)) gp tp t0 t1 t2
                 (Z_to_bv 64 len) (Z_to_bv 64 data) (Z_to_bv 64 (enc_M len)) (Z_to_bv 64 (len + 2)) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x13ed8) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp - ENC_FRAME, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
      stk rsegs m' lo (bv_unsigned sp - ENC_FRAME) /\
      rw_cells rsegs m' (bv_unsigned sp - ENC_FRAME) [CB 8 junk; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 data) (Z_to_bv 64 len) a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14d10) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo data len m
    HL KM ST LO DK.
  eapply evt_cut; [eapply enc_prologue; eassumption |].
  intros ms' (junk & m' & -> & MU & WM & ST' & FR).
  zstep. apply evt_done. exists junk, m'. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact ST'|exact FR].
Qed.

Definition enc_ret (W : list ivl) (r : word) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
  (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte) (R : (word -> option byte) -> Prop)
  : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch W m m' /\ wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp) /\ R m'.

Lemma enc_epilogue : forall (W : list ivl) (R : (word -> option byte) -> Prop)
  (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 g1 g8 g9 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (lo : Z) (junk : list byte) (m0 m : word -> option byte),
  rw_cells rsegs m (bv_unsigned sp - 32) [CB 8 junk; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (bv_unsigned sp - 32) -> lo + 32 <= bv_unsigned sp ->
  munch W m0 m -> wmono rsegs m0 m -> R m ->
  evt rsegs (enc_ret W a0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m0 R)
    (MS (mkR g1 (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 g8 g9 a0 a1 a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14e7c) fc None m (seg_rom rsegs)).
Proof.
  intros W R ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 g1 g8 g9 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    F fc lo junk m0 m FR ST LO MU WM HR.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  zstep. zstep. zstep. zstep.
  replace (bv_unsigned sp - 32 + 32) with (bv_unsigned sp) by lia.
  rewrite Z_to_bv_bv_unsigned.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  apply evt_done. unfold enc_ret. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact ST|exact HR].
Qed.

Theorem enc_body_null : forall (ra sp gp tp s0 s1 g1 g8 g9 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (lo : Z) (junk : list byte) (m : word -> option byte),
  rw_cells rsegs m (bv_unsigned sp - ENC_FRAME) [CB 8 junk; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (bv_unsigned sp - ENC_FRAME) -> lo + ENC_FRAME <= bv_unsigned sp ->
  evt rsegs (enc_ret [(bv_unsigned sp - ENC_FRAME, bv_unsigned sp)] (Z_to_bv 64 0)
               ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m (fun _ => True))
    (MS (mkR g1 (Z_to_bv 64 (bv_unsigned sp - ENC_FRAME)) gp tp t0 t1 t2 g8 g9 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14d48) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 g1 g8 g9 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc lo junk m FR ST LO.
  unfold ENC_FRAME in *.
  zstep. if_true.
  eapply enc_epilogue; [exact FR | exact ST | exact LO | apply munch_refl | apply wmono_refl | exact I].
Qed.

Lemma u8 : forall x, 0 <= x < 256 -> bv_unsigned (Z_to_bv 8 x) = x.
Proof. intros x Hx. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Lemma firstn1_skipn : forall {A} (l : list A) n d, (n < length l)%nat -> firstn 1 (skipn n l) = [nth n l d].
Proof. induction l as [|a l IH]; intros [|n] d H; cbn in *; try lia; [reflexivity|]. apply IH. lia. Qed.

Lemma rd_byte : forall m A xs i x, bytes_at rsegs m A (map (Z_to_bv 8) xs) -> 0 <= i < Z.of_nat (length xs) ->
  nth (Z.to_nat i) xs 0 = x -> ov_read_bytes rsegs m (wa (A + i)) 1 = Some [Z_to_bv 8 x].
Proof.
  intros m A xs i x H Hi Hx.
  rewrite (bytes_at_read rsegs m A _ i 1 H) by (try rewrite length_map; lia).
  rewrite (firstn1_skipn _ _ (Z_to_bv 8 0)) by (try rewrite length_map; lia).
  rewrite map_nth, Hx. reflexivity.
Qed.

Lemma byte_nth : forall l n, bytes_ok l -> 0 <= nth n l 0 < 256.
Proof.
  induction l as [|a l IH]; intros [|n] H; cbn; try lia; inversion H; subst; [assumption|]. apply IH. assumption.
Qed.

Lemma tab_nth : forall v, 0 <= v < 64 -> nth (Z.to_nat v) b64_table 0 = b64c v.
Proof.
  intros v Hv.
  assert (C : forallb (fun n => Z.eqb (nth n b64_table 0) (b64c (Z.of_nat n))) (seq 0 64) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C (Z.to_nat v) ltac:(apply in_seq; lia)).
  apply Z.eqb_eq in C. rewrite C, Z2Nat.id by lia. reflexivity.
Qed.

Lemma tab_len : length b64_table = 65%nat.
Proof. reflexivity. Qed.

Lemma firstn_snoc : forall (l : list Z) n, (n < length l)%nat -> firstn (S n) l = firstn n l ++ [nth n l 0].
Proof. induction l as [|a l IH]; intros [|n] H; cbn in *; try lia; [reflexivity|]. rewrite IH by lia. reflexivity. Qed.

Lemma b64_enc_app : forall n l1 l2, length l1 = (3 * n)%nat -> b64_enc (l1 ++ l2) = b64_enc l1 ++ b64_enc l2.
Proof.
  induction n as [|n IH]; intros l1 l2 H.
  - destruct l1; [reflexivity|cbn in H; lia].
  - destruct l1 as [|x0 [|x1 [|x2 l1]]]; cbn in H; try lia.
    cbn [app b64_enc]. rewrite (IH l1 l2) by lia. reflexivity.
Qed.

Lemma b64_enc_len : forall l, Z.of_nat (length (b64_enc l)) = 4 * ((Z.of_nat (length l) + 2) / 3).
Proof.
  assert (G : forall n l, (length l <= n)%nat -> Z.of_nat (length (b64_enc l)) = 4 * ((Z.of_nat (length l) + 2) / 3)).
  { induction n as [|n IH]; intros l H.
    - destruct l; [reflexivity|cbn in H; lia].
    - destruct l as [|x0 [|x1 [|x2 l]]]; try reflexivity.
      cbn [b64_enc length]. specialize (IH l ltac:(cbn in H; lia)).
      rewrite !Nat2Z.inj_succ, IH. Z.div_mod_to_equations. lia. }
  intros l. apply (G (length l)). lia.
Qed.

Lemma prefix_store : forall m q pre a bs,
  bytes_at rsegs m q pre -> a = q + Z.of_nat (length pre) -> a + Z.of_nat (length bs) <= 2^64 ->
  bytes_at rsegs (write_to_mem m (wa a) bs) q (pre ++ bs).
Proof.
  intros m q pre a bs H Ha Hb. pose proof (bytes_at_bound _ _ _ _ H) as Hq.
  apply bytes_at_app. split.
  - apply bytes_at_write_other; [exact H | lia | lia | left; lia].
  - subst a. apply bytes_at_write_same; lia.
Qed.

Lemma brute2_lemma : forall (f g : Z -> Z -> Z),
  forallb (fun x => forallb (fun y => f x y =? g x y) (map Z.of_nat (seq 0 256))) (map Z.of_nat (seq 0 256)) = true ->
  forall x y, 0 <= x < 256 -> 0 <= y < 256 -> f x y = g x y.
Proof.
  intros f g H x y Hx Hy. rewrite forallb_forall in H.
  assert (Ix : In x (map Z.of_nat (seq 0 256))) by (apply in_map_iff; exists (Z.to_nat x); split; [lia | apply in_seq; lia]).
  assert (Iy : In y (map Z.of_nat (seq 0 256))) by (apply in_map_iff; exists (Z.to_nat y); split; [lia | apply in_seq; lia]).
  specialize (H x Ix). rewrite forallb_forall in H. specialize (H y Iy). apply Z.eqb_eq. exact H.
Qed.

Ltac brute2 x y :=
  lazymatch goal with |- ?L = ?R =>
    let f := eval pattern x, y in L in
    let g := eval pattern x, y in R in
    lazymatch f with ?F _ _ => lazymatch g with ?G _ _ =>
      change (F x y = G x y); apply (brute2_lemma F G); [vm_compute; reflexivity | lia | lia]
    end end
  end.

Lemma ix_lor1 : forall b1 b2, 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  Z.lor (Z.shiftl b1 8 mod 18446744073709551616) b2 = b1 * 256 + b2.
Proof. intros b1 b2 H1 H2. brute2 b1 b2. Qed.

Lemma ix_lor2 : forall b0 b1, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  Z.lor (Z.shiftl b1 8 mod 18446744073709551616) (Z.shiftl b0 16 mod 18446744073709551616) = b0 * 65536 + b1 * 256.
Proof. intros b0 b1 H0 H1. brute2 b0 b1. Qed.

Lemma ix1 : forall b0 b1, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  Z.shiftr (Z.shiftl (b0 * 65536 + b1 * 256) 46 mod 18446744073709551616) 58 = (b0 mod 4) * 16 + b1 / 16.
Proof.
  intros b0 b1 H0 H1. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2 ^ 46) with 70368744177664. change (2 ^ 58) with 288230376151711744.
  Z.div_mod_to_equations. lia.
Qed.

Lemma ix2 : forall b1 b2, 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  Z.shiftr (Z.shiftl (b1 * 256 + b2) 52 mod 18446744073709551616) 58 = (b1 mod 16) * 4 + b2 / 64.
Proof.
  intros b1 b2 H1 H2. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2 ^ 52) with 4503599627370496. change (2 ^ 58) with 288230376151711744.
  Z.div_mod_to_equations. lia.
Qed.

Lemma ix3 : forall b2, 0 <= b2 -> Z.land b2 63 = b2 mod 64.
Proof. intros b2 H. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma le1_byte : forall b : byte, le1 (Z_to_bv 64 (bv_unsigned b)) = [b].
Proof. intros b. exact (le1_zxb b). Qed.

Lemma le1_lit : forall z, 0 <= z < 256 -> le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof. intros z Hz. unfold le1. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma shr18 : forall b0, 0 <= b0 < 256 -> Z.shiftr (b0 * 65536) 18 = b0 / 4.
Proof. intros b0 H. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 18) with 262144. Z.div_mod_to_equations. lia. Qed.

Lemma ix1t : forall b0, 0 <= b0 < 256 ->
  Z.shiftr (Z.shiftl (b0 * 65536) 46 mod 18446744073709551616) 58 = b0 mod 4 * 16.
Proof.
  intros b0 H0. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2 ^ 46) with 70368744177664. change (2 ^ 58) with 288230376151711744.
  Z.div_mod_to_equations. lia.
Qed.

Lemma ix1u : forall b0 b1, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  Z.shiftr (Z.shiftl (b1 * 256 + b0 * 65536) 46 mod 18446744073709551616) 58 = b0 mod 4 * 16 + b1 / 16.
Proof.
  intros b0 b1 H0 H1. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2 ^ 46) with 70368744177664. change (2 ^ 58) with 288230376151711744.
  Z.div_mod_to_equations. lia.
Qed.

Lemma lor16 : forall x y, 0 <= x < 65536 -> 0 <= y -> Z.lor x (y * 65536) = x + y * 65536.
Proof.
  intros x y Hx Hy.
  assert (D : Z.land x (y * 65536) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    change 65536 with (2 ^ 16). rewrite <- Z.shiftl_mul_pow2 by lia.
    destruct (Z.ltb_spec i 16).
    - rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
    - rewrite <- (Z.mod_small x (2 ^ 16)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D. reflexivity.
Qed.

Lemma shr6 : forall b1, 0 <= b1 < 256 -> Z.shiftr (b1 * 256) 6 = b1 * 4.
Proof. intros b1 H. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 6) with 64. Z.div_mod_to_equations. lia. Qed.

Lemma land60 : forall b1, 0 <= b1 < 256 -> Z.land (b1 * 4) 60 = b1 mod 16 * 4.
Proof.
  intros b1 H.
  assert (C : forallb (fun n => Z.eqb (Z.land (Z.of_nat n * 4) 60) (Z.of_nat n mod 16 * 4)) (seq 0 256) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C (Z.to_nat b1) ltac:(apply in_seq; lia)).
  apply Z.eqb_eq in C. rewrite Z2Nat.id in C by lia. exact C.
Qed.

Ltac out_store PRE :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m ?a ?bs) ?ro) =>
    let E := addr_expr a in
    (lazymatch a with
     | wa _ => idtac
     | Z_to_bv 64 _ => change (write_to_mem m a bs) with (write_to_mem m (wa E) bs)
     end);
    lazymatch type of PRE with bytes_at _ _ ?qq ?pre =>
      let S1 := fresh "S" in let S2 := fresh "S" in let P' := fresh "P" in
      assert (S1 : E = qq + Z.of_nat (length pre)) by (rewrite ?length_app, ?length_le1; lia);
      assert (S2 : E + Z.of_nat (length bs) <= 2^64) by (rewrite ?length_le1; lia);
      pose proof (prefix_store m qq pre E bs PRE S1 S2) as P';
      clear PRE S1 S2; rename P' into PRE
    end;
    store_done
  end.

Section EncBody.
  Variables (ra sp gp tp s0v s1v s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 g1 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo data len q : Z) (junk : list byte) (bs : list Z)
    (m0 : word -> option byte).
  Hypothesis HB : bytes_ok bs.
  Hypothesis HN : Z.of_nat (length bs) = len.
  Hypothesis HL : len <= 2^62.
  Hypothesis HQ : q <> 0.
  Hypothesis DATA0 : bytes_at rsegs m0 data (map (Z_to_bv 8) bs).
  Hypothesis TAB0 : bytes_at rsegs m0 66724 (map (Z_to_bv 8) b64_table).
  Hypothesis WR0 : wr_at rsegs m0 q (enc_M len).
  Hypothesis FR0 : rw_cells rsegs m0 (bv_unsigned sp - 32) [CB 8 junk; C8 s1v; C8 s0v; C8 ra].
  Hypothesis ST0 : stk rsegs m0 lo (bv_unsigned sp - 32).
  Hypothesis LO : lo + 32 <= bv_unsigned sp.
  Hypothesis DQD : len = 0 \/ q + enc_M len <= data \/ data + len <= q.
  Hypothesis DQT : q + enc_M len <= 66724 \/ 66724 + 65 <= q.
  Hypothesis DQF : q + enc_M len <= bv_unsigned sp - 32 \/ bv_unsigned sp <= q.

  Definition enc_facts (m : word -> option byte) (k : Z) : Prop :=
    munch [(q, q + enc_M len)] m0 m /\ wmono rsegs m0 m /\ stk rsegs m lo (bv_unsigned sp - 32) /\
    bytes_at rsegs m q (map (Z_to_bv 8) (b64_enc (firstn (Z.to_nat (3 * k)) bs))).

  Abbreviation BS pc x5 x6 x7 x12 x13 x14 x15 x16 x17 m :=
    (MS (mkR g1 (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp x5 x6 x7 (Z_to_bv 64 len) (Z_to_bv 64 data)
       (Z_to_bv 64 q) (Z_to_bv 64 66724) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  Lemma enc_prefix_len : forall k, 0 <= k -> 3 * k <= len ->
    Z.of_nat (length (map (Z_to_bv 8) (b64_enc (firstn (Z.to_nat (3 * k)) bs)))) = 4 * k.
  Proof.
    intros k Hk Hk3. rewrite length_map, b64_enc_len, firstn_length_le by lia.
    rewrite Z2Nat.id by lia. Z.div_mod_to_equations. lia.
  Qed.

  Lemma enc_prefix_step : forall k, 0 <= k -> 3 * k + 3 <= len ->
    map (Z_to_bv 8) (b64_enc (firstn (Z.to_nat (3 * (k + 1))) bs)) =
    map (Z_to_bv 8) (b64_enc (firstn (Z.to_nat (3 * k)) bs)) ++
    map (Z_to_bv 8) (b64_enc [nth (Z.to_nat (3 * k)) bs 0; nth (Z.to_nat (3 * k + 1)) bs 0;
                              nth (Z.to_nat (3 * k + 2)) bs 0]).
  Proof.
    intros k Hk Hk3.
    replace (Z.to_nat (3 * (k + 1))) with (S (S (S (Z.to_nat (3 * k))))) by lia.
    replace (Z.to_nat (3 * k + 1)) with (S (Z.to_nat (3 * k))) by lia.
    replace (Z.to_nat (3 * k + 2)) with (S (S (Z.to_nat (3 * k)))) by lia.
    rewrite !firstn_snoc by lia.
    rewrite <- !app_assoc. cbn [app].
    rewrite (b64_enc_app (Z.to_nat k)) by (rewrite firstn_length_le; lia).
    rewrite map_app. reflexivity.
  Qed.

  Ltac rd_tab TAB v :=
    let H := fresh "RT" in
    pose proof (rd_byte _ _ _ v (b64c v) TAB ltac:(rewrite tab_len; Z.div_mod_to_equations; lia)
                  (tab_nth v ltac:(Z.div_mod_to_equations; lia))) as H.

  Ltac hs_out WR j :=
    let H := fresh "HS" in
    pose proof (wr_at_store_ok rsegs _ q (enc_M len) j 1 WR ltac:(lia) ltac:(lia)) as H.

  Lemma enc_iter : forall (Q : machine_state -> Prop) (k : Z) (m : word -> option byte) (x5 x6 x7 x16 x17 : word),
    0 <= k -> 3 * k + 3 <= len -> enc_facts m k ->
    (forall (m' : word -> option byte) (y5 y6 y7 y16 : word), enc_facts m' (k + 1) ->
       evt rsegs Q (BS 0x14de8 y5 y6 y7 (Z_to_bv 64 (q + 4 * k + 4)) (Z_to_bv 64 (data + 2)) (Z_to_bv 64 (data + 1))
                      (Z_to_bv 64 (3 * k + 3)) y16 (Z_to_bv 64 (3 * k + 5)) m')) ->
    evt rsegs Q (BS 0x14d6c x5 x6 x7 (Z_to_bv 64 (q + 4 * k)) (Z_to_bv 64 (data + 2)) (Z_to_bv 64 (data + 1))
                   (Z_to_bv 64 (3 * k)) x16 x17 m).
  Proof.
    intros Q k m x5 x6 x7 x16 x17 Hk Hk3 (MU & WM & ST & PRE) CONT.
    pose proof (bytes_at_bound _ _ _ _ DATA0) as BD. rewrite length_map, HN in BD.
    pose proof (proj1 WR0) as Hq0. pose proof (proj1 (proj2 WR0)) as HqM.
    assert (HM : 4 * k + 4 < enc_M len) by (unfold enc_M; Z.div_mod_to_equations; lia).
    assert (DATA : bytes_at rsegs m data (map (Z_to_bv 8) bs)).
    { eapply bytes_at_transport; [exact DATA0 | exact MU |]. cbn [disjoint_from]. rewrite length_map, HN. lia. }
    assert (TAB : bytes_at rsegs m 66724 (map (Z_to_bv 8) b64_table)).
    { eapply bytes_at_transport; [exact TAB0 | exact MU |]. cbn [disjoint_from]. rewrite length_map, tab_len. lia. }
    pose proof (wr_at_transport rsegs m0 m q (enc_M len) WR0 WM) as WR.
    assert (LD : Z.of_nat (length (map (Z_to_bv 8) bs)) = len) by (rewrite length_map; exact HN).
    assert (LT : Z.of_nat (length (map (Z_to_bv 8) b64_table)) = 65) by (rewrite length_map, tab_len; reflexivity).
    pose proof (enc_prefix_len k Hk ltac:(lia)) as LP.
    remember (nth (Z.to_nat (3 * k)) bs 0) as b0 eqn:E0.
    remember (nth (Z.to_nat (3 * k + 1)) bs 0) as b1 eqn:E1.
    remember (nth (Z.to_nat (3 * k + 2)) bs 0) as b2 eqn:E2.
    assert (R0 : 0 <= b0 < 256) by (subst b0; apply byte_nth; exact HB).
    assert (R1 : 0 <= b1 < 256) by (subst b1; apply byte_nth; exact HB).
    assert (R2 : 0 <= b2 < 256) by (subst b2; apply byte_nth; exact HB).
    pose proof (rd_byte _ _ _ (3 * k) b0 DATA ltac:(lia) (eq_sym E0)) as RD0.
    pose proof (rd_byte _ _ _ (3 * k + 1) b1 DATA ltac:(lia) (eq_sym E1)) as RD1.
    pose proof (rd_byte _ _ _ (3 * k + 2) b2 DATA ltac:(lia) (eq_sym E2)) as RD2.
    zstep. zstep. zstep. cbv beta. rewrite (u8 b0 R0).
    zstep. cbv beta. rewrite (u8 b1 R1).
    zstep. zstep. cbv beta. rewrite (u8 b2 R2).
    clear RD0 RD1 RD2.
    zstep. zstep. zstep. zstep. zstep.
    rewrite (ix_lor1 b1 b2 R1 R2), (ix_lor2 b0 b1 R0 R1).
    zstep.
    rewrite (Z.shiftr_div_pow2 b0 2) by lia. change (2 ^ 2) with 4.
    rd_tab TAB (b0 / 4).
    zstep. cbv beta. clear RT.
    zstep. zstep. rewrite (ix1 b0 b1 R0 R1).
    zstep.
    hs_out WR (4 * k).
    zstep. clear HS.
    out_store PRE.
    rd_tab TAB (b0 mod 4 * 16 + b1 / 16).
    zstep. cbv beta. clear RT.
    zstep. zstep. rewrite (ix2 b1 b2 R1 R2).
    zstep.
    hs_out WR (4 * k + 1).
    zstep. clear HS.
    out_store PRE.
    rd_tab TAB (b1 mod 16 * 4 + b2 / 64).
    zstep. cbv beta. clear RT.
    zstep. rewrite (ix3 b2 ltac:(lia)).
    zstep.
    hs_out WR (4 * k + 2).
    zstep. clear HS.
    out_store PRE.
    rd_tab TAB (b2 mod 64).
    zstep. cbv beta. clear RT.
    zstep.
    hs_out WR (4 * k + 3).
    zstep. clear HS.
    out_store PRE.
    zstep. zstep.
    eapply CONT.
    split; [exact MU|]. split; [exact WM|]. split; [exact ST|].
    eapply bytes_at_ext; [exact PRE|].
    rewrite (enc_prefix_step k Hk Hk3), <- E0, <- E1, <- E2, !le1_byte, <- !app_assoc.
    reflexivity.
  Qed.

  Definition enc_loop_exit (ms : machine_state) : Prop :=
    exists (k p i : Z) (m : word -> option byte) (y5 y6 y7 y16 y17 : word),
      0 <= k /\ 3 * k <= len < 3 * k + 3 /\ p = q + 4 * k /\ i = 3 * k /\ enc_facts m k /\
      ms = BS 0x14dec y5 y6 y7 (Z_to_bv 64 p) (Z_to_bv 64 (data + 2)) (Z_to_bv 64 (data + 1)) (Z_to_bv 64 i) y16 y17 m.

  Lemma enc_loop : forall (n : nat) (k p i : Z) (m : word -> option byte) (x5 x6 x7 x16 x17 : word),
    Z.to_nat (len - 3 * k) = n -> 0 <= k -> 3 * k + 3 <= len -> p = q + 4 * k -> i = 3 * k -> enc_facts m k ->
    evt rsegs enc_loop_exit
      (BS 0x14d6c x5 x6 x7 (Z_to_bv 64 p) (Z_to_bv 64 (data + 2)) (Z_to_bv 64 (data + 1)) (Z_to_bv 64 i) x16 x17 m).
  Proof.
    induction n as [n IH] using lt_wf_ind.
    intros k p i m x5 x6 x7 x16 x17 En Hk Hk3 Ep Ei FA. subst p i.
    apply (enc_iter _ k m x5 x6 x7 x16 x17 Hk Hk3 FA).
    intros m' y5 y6 y7 y16 FA'.
    zstep. if_cases BR; zify_cond BR.
    - eapply (IH (Z.to_nat (len - 3 * (k + 1))) ltac:(lia) (k + 1)); [reflexivity | lia | lia | ring | ring | exact FA'].
    - apply evt_done. exists (k + 1), (q + 4 * k + 4), (3 * k + 3), m', y5, y6, y7, y16, (Z_to_bv 64 (3 * k + 5)).
      split; [lia|]. split; [lia|]. split; [ring|]. split; [ring|]. split; [exact FA'|]. reflexivity.
  Qed.

  Lemma enc_finish : forall (p : Z) (m : word -> option byte) (x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 : word),
    p = q + (enc_M len - 1) ->
    munch [(q, q + enc_M len)] m0 m -> wmono rsegs m0 m -> stk rsegs m lo (bv_unsigned sp - 32) ->
    bytes_at rsegs m q (map (Z_to_bv 8) (b64_enc bs)) ->
    evt rsegs (enc_ret [(q, q + enc_M len); (bv_unsigned sp - 32, bv_unsigned sp)] (Z_to_bv 64 q)
                 ra sp gp tp s0v s1v s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m0
                 (fun m' => bytes_at rsegs m' q (map (Z_to_bv 8) (b64_enc bs ++ [0]))))
      (MS (mkR g1 (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 q) x11 (Z_to_bv 64 p)
             x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14e78) fc None m (seg_rom rsegs)).
  Proof.
    intros p m x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 Ep MU WM ST PRE. subst p.
    pose proof (proj1 WR0) as Hq0. pose proof (proj1 (proj2 WR0)) as HqM.
    assert (HM1 : 1 <= enc_M len) by (unfold enc_M; Z.div_mod_to_equations; lia).
    pose proof (wr_at_transport rsegs m0 m q (enc_M len) WR0 WM) as WR.
    assert (LP : Z.of_nat (length (map (Z_to_bv 8) (b64_enc bs))) = enc_M len - 1)
      by (rewrite length_map, b64_enc_len, HN; unfold enc_M; lia).
    hs_out WR (enc_M len - 1).
    zstep. clear HS.
    out_store PRE.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FR : rw_cells rsegs mm (bv_unsigned sp - 32) [CB 8 junk; C8 s1v; C8 s0v; C8 ra])
        by (eapply rw_cells_transport; [exact FR0 | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia])
    end.
    eapply enc_epilogue; [exact FR | exact ST | exact LO | | exact WM | ].
    - eapply munch_weaken; [|exact MU]. unfold sub_fp. cbn [outside]. tauto.
    - cbv beta. eapply bytes_at_ext; [exact PRE|]. rewrite map_app, le1_lit by lia. reflexivity.
  Qed.

  Lemma enc_tail_list1 : forall k, 0 <= k -> len = 3 * k + 1 ->
    map (Z_to_bv 8) (b64_enc bs) =
    map (Z_to_bv 8) (b64_enc (firstn (Z.to_nat (3 * k)) bs)) ++
    map (Z_to_bv 8) (b64_enc [nth (Z.to_nat (3 * k)) bs 0]).
  Proof.
    intros k Hk EL.
    assert (E : bs = firstn (S (Z.to_nat (3 * k))) bs) by (rewrite firstn_all2 by lia; reflexivity).
    rewrite E at 1. rewrite firstn_snoc by lia.
    rewrite (b64_enc_app (Z.to_nat k)) by (rewrite firstn_length_le; lia).
    apply map_app.
  Qed.

  Lemma enc_tail_list2 : forall k, 0 <= k -> len = 3 * k + 2 ->
    map (Z_to_bv 8) (b64_enc bs) =
    map (Z_to_bv 8) (b64_enc (firstn (Z.to_nat (3 * k)) bs)) ++
    map (Z_to_bv 8) (b64_enc [nth (Z.to_nat (3 * k)) bs 0; nth (Z.to_nat (3 * k + 1)) bs 0]).
  Proof.
    intros k Hk EL.
    assert (E : bs = firstn (S (S (Z.to_nat (3 * k)))) bs) by (rewrite firstn_all2 by lia; reflexivity).
    replace (Z.to_nat (3 * k + 1)) with (S (Z.to_nat (3 * k))) by lia.
    rewrite E at 1. rewrite !firstn_snoc by lia.
    rewrite <- app_assoc. cbn [app].
    rewrite (b64_enc_app (Z.to_nat k)) by (rewrite firstn_length_le; lia).
    apply map_app.
  Qed.

  Lemma enc_tail : forall (k p i : Z) (m : word -> option byte) (x5 x6 x7 x13 x14 x16 x17 : word),
    0 <= k -> 3 * k < len < 3 * k + 3 -> p = q + 4 * k -> i = 3 * k -> enc_facts m k ->
    evt rsegs (enc_ret [(q, q + enc_M len); (bv_unsigned sp - 32, bv_unsigned sp)] (Z_to_bv 64 q)
                 ra sp gp tp s0v s1v s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m0
                 (fun m' => bytes_at rsegs m' q (map (Z_to_bv 8) (b64_enc bs ++ [0]))))
      (BS 0x14dfc x5 x6 x7 (Z_to_bv 64 p) x13 x14 (Z_to_bv 64 i) x16 x17 m).
  Proof.
    intros k p i m x5 x6 x7 x13 x14 x16 x17 Hk Hlen Ep Ei (MU & WM & ST & PRE). subst p i.
    pose proof (bytes_at_bound _ _ _ _ DATA0) as BD. rewrite length_map, HN in BD.
    pose proof (proj1 WR0) as Hq0. pose proof (proj1 (proj2 WR0)) as HqM.
    assert (HM : enc_M len = 4 * k + 5) by (unfold enc_M; Z.div_mod_to_equations; lia).
    assert (DATA : bytes_at rsegs m data (map (Z_to_bv 8) bs)).
    { eapply bytes_at_transport; [exact DATA0 | exact MU |]. cbn [disjoint_from]. rewrite length_map, HN. lia. }
    assert (TAB : bytes_at rsegs m 66724 (map (Z_to_bv 8) b64_table)).
    { eapply bytes_at_transport; [exact TAB0 | exact MU |]. cbn [disjoint_from]. rewrite length_map, tab_len. lia. }
    pose proof (wr_at_transport rsegs m0 m q (enc_M len) WR0 WM) as WR.
    assert (LD : Z.of_nat (length (map (Z_to_bv 8) bs)) = len) by (rewrite length_map; exact HN).
    assert (LT : Z.of_nat (length (map (Z_to_bv 8) b64_table)) = 65) by (rewrite length_map, tab_len; reflexivity).
    pose proof (enc_prefix_len k Hk ltac:(lia)) as LP.
    remember (nth (Z.to_nat (3 * k)) bs 0) as b0 eqn:E0.
    assert (R0 : 0 <= b0 < 256) by (subst b0; apply byte_nth; exact HB).
    pose proof (rd_byte _ _ _ (3 * k) b0 DATA ltac:(lia) (eq_sym E0)) as RD0.
    zstep. zstep. cbv beta. rewrite (u8 b0 R0). clear RD0.
    zstep. zstep. rewrite (Z.shiftl_mul_pow2 b0 16) by lia. change (2 ^ 16) with 65536.
    zstep. if_cases BR; zify_cond BR.
    - assert (EL : len = 3 * k + 1) by lia.
      zstep. zstep. rewrite Z.lor_0_l.
      zstep. rewrite (shr18 b0 R0).
      zstep. rd_tab TAB (b0 / 4). zstep. cbv beta. clear RT.
      zstep. zstep. rewrite (ix1t b0 R0).
      zstep. hs_out WR (4 * k). zstep. clear HS. out_store PRE.
      rd_tab TAB (b0 mod 4 * 16). zstep. cbv beta. clear RT.
      zstep. hs_out WR (4 * k + 1). zstep. clear HS. out_store PRE.
      zstep. zstep. if_cases BR2; zify_cond BR2; [| exfalso; lia].
      zstep. hs_out WR (4 * k + 2). zstep. clear HS. out_store PRE.
      hs_out WR (4 * k + 3). zstep. clear HS. out_store PRE.
      zstep.
      eapply enc_finish; [ | exact MU | exact WM | exact ST | ].
      + lia.
      + eapply bytes_at_ext; [exact PRE|].
        rewrite (enc_tail_list1 k Hk EL), <- E0. cbn [b64_enc map].
        rewrite !le1_byte, !le1_lit by lia. rewrite <- !app_assoc. reflexivity.
    - assert (EL : len = 3 * k + 2) by lia.
      remember (nth (Z.to_nat (3 * k + 1)) bs 0) as b1 eqn:E1.
      assert (R1 : 0 <= b1 < 256) by (subst b1; apply byte_nth; exact HB).
      pose proof (rd_byte _ _ _ (3 * k + 1) b1 DATA ltac:(lia) (eq_sym E1)) as RD1.
      zstep. zstep. cbv beta. rewrite (u8 b1 R1). clear RD1.
      zstep. rewrite (Z.shiftl_mul_pow2 b1 8) by lia. change (2 ^ 8) with 256.
      zstep.
      zstep. rewrite (lor16 (b1 * 256) b0) by lia.
      zstep. rewrite (shr18 b0 R0).
      zstep. rd_tab TAB (b0 / 4). zstep. cbv beta. clear RT.
      zstep. zstep. rewrite (ix1u b0 b1 R0 R1).
      zstep. hs_out WR (4 * k). zstep. clear HS. out_store PRE.
      rd_tab TAB (b0 mod 4 * 16 + b1 / 16). zstep. cbv beta. clear RT.
      zstep. hs_out WR (4 * k + 1). zstep. clear HS. out_store PRE.
      zstep. zstep. if_cases BR2; zify_cond BR2; [exfalso; lia |].
      zstep. rewrite (shr6 b1 R1).
      zstep. rewrite (land60 b1 R1).
      zstep. rd_tab TAB (b1 mod 16 * 4). zstep. cbv beta. clear RT.
      zstep. hs_out WR (4 * k + 2). zstep. clear HS. out_store PRE.
      hs_out WR (4 * k + 3). zstep. clear HS. out_store PRE.
      zstep.
      eapply enc_finish; [ | exact MU | exact WM | exact ST | ].
      + lia.
      + eapply bytes_at_ext; [exact PRE|].
        rewrite (enc_tail_list2 k Hk EL), <- E0, <- E1. cbn [b64_enc map].
        rewrite !le1_byte, !le1_lit by lia. rewrite <- !app_assoc. reflexivity.
  Qed.

  Lemma enc_body_sec : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 : word),
    evt rsegs (enc_ret [(q, q + enc_M len); (bv_unsigned sp - 32, bv_unsigned sp)] (Z_to_bv 64 q)
                 ra sp gp tp s0v s1v s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m0
                 (fun m' => bytes_at rsegs m' q (map (Z_to_bv 8) (b64_enc bs ++ [0]))))
      (MS (mkR g1 (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp x5 x6 x7 (Z_to_bv 64 len) (Z_to_bv 64 data)
             (Z_to_bv 64 q) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14d48) fc None m0 (seg_rom rsegs)).
  Proof.
    intros x5 x6 x7 x11 x12 x13 x14 x15 x16 x17.
    pose proof (proj1 WR0) as Hq0. pose proof (proj1 (proj2 WR0)) as HqM.
    assert (HM1 : 1 <= enc_M len) by (unfold enc_M; Z.div_mod_to_equations; lia).
    assert (Hq : 0 < q < 2^64) by lia.
    zstep. if_cases BZ; zify_cond BZ; [exfalso; lia |].
    zstep. zstep. zstep. zstep.
    zstep. if_cases B3; zify_cond B3.
    - zstep.
      zstep. if_cases B0; zify_cond B0.
      + assert (EL : len = 0) by lia.
        assert (EB : bs = []) by (destruct bs; [reflexivity | cbn in HN; lia]).
        eapply enc_finish; [ | apply munch_refl | apply wmono_refl | exact ST0 | ].
        * unfold enc_M. rewrite EL. Z.div_mod_to_equations. lia.
        * rewrite EB. apply bytes_at_nil. lia.
      + eapply (enc_tail 0 q 0); [lia | lia | ring | reflexivity | ].
        split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact ST0|].
        change (map (Z_to_bv 8) (b64_enc (firstn (Z.to_nat (3 * 0)) bs))) with (@nil byte).
        apply bytes_at_nil. lia.
    - zstep. zstep. zstep.
      eapply evt_cut.
      { eapply (enc_loop (Z.to_nat (len - 3 * 0)) 0 q 0); [reflexivity | lia | lia | ring | reflexivity | ].
        split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact ST0|].
        change (map (Z_to_bv 8) (b64_enc (firstn (Z.to_nat (3 * 0)) bs))) with (@nil byte).
        apply bytes_at_nil. lia. }
      intros ms' (k & p & i & m & y5 & y6 & y7 & y16 & y17 & Hk & Hlen & Ep & Ei & FA & ->).
      zstep. if_cases BT; zify_cond BT.
      + eapply (enc_tail k p i); [lia | lia | exact Ep | exact Ei | exact FA].
      + zstep.
        destruct FA as (MU & WM & ST & PRE).
        eapply enc_finish; [ | exact MU | exact WM | exact ST | ].
        * subst p. unfold enc_M. Z.div_mod_to_equations. lia.
        * eapply bytes_at_ext; [exact PRE|]. rewrite firstn_all2 by lia. reflexivity.
  Qed.
End EncBody.

Theorem enc_body : forall (ra sp gp tp s0 s1 g1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (lo data len q : Z) (junk : list byte) (bs : list Z) (m : word -> option byte),
  bytes_ok bs -> Z.of_nat (length bs) = len -> len <= 2^62 -> q <> 0 ->
  bytes_at rsegs m data (map (Z_to_bv 8) bs) ->
  bytes_at rsegs m ENC_TABLE (map (Z_to_bv 8) b64_table) ->
  wr_at rsegs m q (enc_M len) ->
  rw_cells rsegs m (bv_unsigned sp - ENC_FRAME) [CB 8 junk; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (bv_unsigned sp - ENC_FRAME) -> lo + ENC_FRAME <= bv_unsigned sp ->
  (len = 0 \/ q + enc_M len <= data \/ data + len <= q) ->
  (q + enc_M len <= ENC_TABLE \/ ENC_TABLE + 65 <= q) ->
  (q + enc_M len <= bv_unsigned sp - ENC_FRAME \/ bv_unsigned sp <= q) ->
  evt rsegs (enc_ret [(q, q + enc_M len); (bv_unsigned sp - ENC_FRAME, bv_unsigned sp)] (Z_to_bv 64 q)
               ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m
               (fun m' => bytes_at rsegs m' q (map (Z_to_bv 8) (b64_enc bs ++ [0]))))
    (MS (mkR g1 (Z_to_bv 64 (bv_unsigned sp - ENC_FRAME)) gp tp t0 t1 t2 (Z_to_bv 64 len) (Z_to_bv 64 data)
           (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14d48) fc None m (seg_rom rsegs)).
Proof.
  intros. unfold ENC_FRAME, ENC_TABLE in *.
  eapply enc_body_sec; eassumption.
Qed.

Lemma enc_table_image : forall m, mem_inv rsegs m -> bytes_at rsegs m ENC_TABLE (map (Z_to_bv 8) b64_table).
Proof.
  intros m MI. unfold ENC_TABLE.
  apply ro_bytes_at; [exact MI | lia | rewrite length_map, tab_len; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma enc_magic_image : forall m, mem_inv rsegs m -> bytes_at rsegs m ENC_KMAGIC (le8 (Z_to_bv 64 ENC_MAGIC)).
Proof.
  intros m MI. unfold ENC_KMAGIC.
  apply ro_bytes_at; [exact MI | lia | rewrite length_le8; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
