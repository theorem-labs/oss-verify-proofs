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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Regs6ss RegisterBridge FP.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import Boxreg BoxregRd BoxregUpd BoxregStep lowest_free_base_c
  range_free_c lowest_free_c printf_facts_c snprintf_c reac_boxreg_set_name_c reac_boxreg_declare_c reac_boxreg_declare_inv
  bcmp_c strncmp_c read_name_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require range_free lowest_free lowest_free_base memset bcmp strncmp
  reac_boxreg_declare.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr
  LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_exit LLVMFuzzerTestOneInput_res LLVMFuzzerTestOneInput_rn.
Import ListNotations.
Open Scope Z_scope.

Definition c0_nch (pl : list byte) : Z := match pl with [] => 0 | x :: _ => bv_unsigned x end.
Definition c0_base (pl : list byte) : Z := match pl with _ :: y :: _ => bv_signed y | _ => 0 end.
Definition c0_used (pl : list byte) : Z := Z.min (Z.of_nat (length pl)) 2.

Ltac show := match goal with |- ?G => idtac "GOAL:" G end.

Lemma c0_rd1 : forall m a b l, bytes_at rsegs m a (b :: l) -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof.
  intros m a b l H. pose proof (bytes_at_read rsegs m a (b :: l) 0 1 H ltac:(lia) ltac:(cbn; lia)) as E.
  rewrite Z.add_0_r in E. exact E.
Qed.

Lemma c0_ne0 : forall z, 0 < z < 2 ^ 64 -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 0) = false.
Proof. intros z Hz. rewrite eqb_lit by lia. apply Z.eqb_neq. lia. Qed.

Lemma c0_byte_signed : forall b : byte,
  (bv_signed b = bv_unsigned b /\ bv_unsigned b < 128) \/ (bv_signed b = bv_unsigned b - 256 /\ 128 <= bv_unsigned b).
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  change (256 / 2) with 128.
  destruct (Z.ltb_spec (bv_unsigned b) 128); [left | right]; (split; [|lia]); Z.div_mod_to_equations; lia.
Qed.

Lemma c0_sl : forall b : byte, Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b)) 56) = Z_to_bv 64 (bv_signed b * 2 ^ 56).
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  unfold zxb. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. apply Z_to_bv_eqm.
  change (2 ^ 56) with 72057594037927936. change (2 ^ 64) with 18446744073709551616.
  destruct (c0_byte_signed b) as [[-> _] | [-> _]]; [reflexivity|].
  Z.div_mod_to_equations. lia.
Qed.

Lemma c0_sr : forall b : byte,
  Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b)) 56))) 56) = Z_to_bv 64 (bv_signed b).
Proof.
  intros b. rewrite c0_sl. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  assert (Hs : -128 <= bv_signed b < 128) by (destruct (c0_byte_signed b) as [[E H] | [E H]]; rewrite E; lia).
  rewrite signed_lit by (change (2 ^ 56) with 72057594037927936; change (2 ^ 63) with 9223372036854775808; lia).
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

Lemma c0_rw2 : forall m A x y x' y', rw_cells rsegs m A [C8 x; C8 y] -> x = x' -> y = y' ->
  rw_cells rsegs m A [C8 x'; C8 y'].
Proof. intros m A x y x' y' H -> ->. exact H. Qed.

Lemma llvm_c0_evt1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ip : Z) (pl : list byte),
    0 <= ip -> ip + 1 + Z.of_nat (length pl) <= bv_unsigned sp -> bv_unsigned sp + 344 <= 2 ^ 64 ->
    bytes_at rsegs m (ip + 1) pl ->
    rw_cells rsegs m (bv_unsigned sp + 328) [C8 (Z_to_bv 64 (ip + 1)); C8 (Z_to_bv 64 (Z.of_nat (length pl)))] ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a1' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x12ea4) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (c0_base pl * 2 ^ 56))
                       (Z_to_bv 64 (bv_unsigned sp + 328)) a1' a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 (Z.of_nat (length pl))) s3 (Z_to_bv 64 (c0_nch pl)) (Z_to_bv 64 (c0_base pl))
                       s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x135cc) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp + 328, bv_unsigned sp + 344)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         rw_cells rsegs m' (bv_unsigned sp + 328)
           [C8 (Z_to_bv 64 (ip + 1 + c0_used pl)); C8 (Z_to_bv 64 (Z.of_nat (length (skipn 2 pl))))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 ip) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (Z.of_nat (length pl))) s3 s4 (Z_to_bv 64 (1 + Z.of_nat (length pl)))
               s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12d6c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ip pl Hip Hsp Htop HB CW MI.
  pose proof (munch_refl [(bv_unsigned sp + 328, bv_unsigned sp + 344)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  destruct pl as [|v1 [|v2 rest]].
  - change (Z.of_nat (length [])) with 0 in *. change (c0_used []) with 0.
    change (Z.of_nat (length (skipn 2 []))) with 0. cbn [c0_base c0_nch] in *. rewrite Z.add_0_r.
    step. if_true. do 6 step.
    finish.
  - change (Z.of_nat (length [v1])) with 1 in *. change (c0_used [v1]) with 1.
    change (Z.of_nat (length (skipn 2 [v1]))) with 0. cbn [c0_base c0_nch] in *.
    replace (ip + 1 + 1) with (ip + 2) by lia.
    pose proof (c0_rd1 _ _ _ _ HB) as R1.
    step. if_false. do 6 step.
    if_true. do 4 step.
    finish.
  - cbn [c0_base c0_nch skipn] in *.
    replace (c0_used (v1 :: v2 :: rest)) with 2 by (unfold c0_used; cbn [length]; lia).
    replace (ip + 1 + 2) with (ip + 3) by lia.
    pose proof (c0_rd1 _ _ _ _ HB) as R1.
    apply (proj1 (bytes_at_app rsegs m (ip + 1) [v1] (v2 :: rest))) in HB. destruct HB as [_ HB2].
    cbn [length] in HB2. change (Z.of_nat 1) with 1 in HB2.
    replace (Z.of_nat (length (v1 :: v2 :: rest))) with (2 + Z.of_nat (length rest)) in * by (cbn [length]; lia).
    replace (Z.of_nat (length (v2 :: rest))) with (1 + Z.of_nat (length rest)) in * by (cbn [length]; lia).
    step. rewrite c0_ne0 by lia. cbv iota. do 6 step. rewrite c0_ne0 by lia. cbv iota.
    step. clear R1.
    pose proof (c0_rd1 _ _ _ _ HB2) as R2.
    do 9 step.
    rewrite c0_sr, c0_sl. change (skipn 0 rest) with rest.
    finish.
    eapply c0_rw2; [exact CW | word_eq_tac | word_eq_tac].
Qed.

Lemma c0_op8 : forall op, Z.land op 8 = 0 \/ Z.land op 8 = 8.
Proof.
  intros op. destruct (Z.testbit op 3) eqn:T; [right | left]; apply Z.bits_inj'; intros i Hi;
    rewrite Z.land_spec; change 8 with (2 ^ 3); destruct (Z.eq_dec i 3) as [->|N].
  - rewrite T, Z.pow2_bits_true by lia. reflexivity.
  - rewrite !Z.pow2_bits_false by lia. apply andb_false_r.
  - rewrite T. rewrite Z.bits_0. reflexivity.
  - rewrite Z.pow2_bits_false by lia. rewrite Z.bits_0. apply andb_false_r.
Qed.

Lemma c0_given : forall op nm, 0 <= op < 256 -> 0 <= nm < 2 ^ 64 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64
    (Z.land (bv_unsigned (Z_to_bv 64 op)) 8))) 3 + -1))) (bv_unsigned (Z_to_bv 64 nm))) =
  Z_to_bv 64 (if Z.land op 8 =? 0 then nm else 0).
Proof.
  intros op nm Hop Hnm. rewrite (unsigned_lit op) by lia. rewrite (unsigned_lit nm) by lia.
  destruct (c0_op8 op) as [E|E]; rewrite E.
  - change (Z.shiftr (bv_unsigned (Z_to_bv 64 0)) 3 + -1) with (-1).
    change (bv_unsigned (Z_to_bv 64 (-1))) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
    rewrite Z.mod_small by lia. reflexivity.
  - reflexivity.
Qed.

Lemma c0_rfo_ok : forall bs k b, range_free_ok bs b k (bx_fabric bs) -> range_ok bs k b.
Proof.
  intros bs k b [H1 H2]. split; [lia|]. split; [lia|]. intros (i & Hi & Hm). exact (H2 i Hi Hm).
Qed.

Lemma c0_ok_rfo : forall bs k b, range_ok bs k b -> range_free_ok bs b k (bx_fabric bs).
Proof.
  intros bs k b (H1 & H2 & H3). split; [lia|]. intros i Hi Hm. apply H3. exists i. split; [exact Hi | exact Hm].
Qed.

Definition c0_want (bs : list byte) (nch base want : Z) : Prop :=
  (~ (box_width_ok nch (bx_fabric bs) /\ bx_n bs < 5) /\ want = -1) \/
  (box_width_ok nch (bx_fabric bs) /\ bx_n bs < 5 /\ 0 <= base /\
     ((range_free_ok bs base nch (bx_fabric bs) /\ want = base) \/
      (~ range_free_ok bs base nch (bx_fabric bs) /\ want = -1))) \/
  (box_width_ok nch (bx_fabric bs) /\ bx_n bs < 5 /\ base < 0 /\ lowest_free_res bs nch (bx_fabric bs) want).

Lemma c0_link_refused : forall bs nch base want,
  c0_want bs nch base want -> declare_refused bs nch base -> want = -1.
Proof.
  intros bs nch base want HW HR.
  destruct HW as [(_ & E) | [(Hw & Hn & Hb & [(Hf & E) | (_ & E)]) | (Hw & Hn & Hb & Hl)]]; try exact E.
  - exfalso. destruct HR as [HR | [HR | [(_ & HR) | (HR & _)]]]; [tauto | lia | | lia].
    exact (HR (c0_rfo_ok bs nch base Hf)).
  - destruct HR as [HR | [HR | [(HR & _) | (_ & HR)]]]; [tauto | lia | lia |].
    destruct Hl as [(E & _) | (H1 & H2 & _)]; [exact E|].
    exfalso. destruct HR as [(_ & HR) | (HR & _)]; [|lia].
    destruct (c0_rfo_ok bs nch want H2) as (_ & _ & HF). apply HF. apply HR; [lia|]. destruct H2; lia.
Qed.

Lemma c0_link_placed : forall bs nch base want b p,
  c0_want bs nch base want -> declare_placed bs nch base b p -> want = b.
Proof.
  intros bs nch base want b p HW (Hw & Hn & HP).
  destruct HW as [(HN & _) | [(_ & _ & Hb & [(Hf & E) | (Hf & E)]) | (_ & _ & Hb & Hl)]].
  - exfalso. tauto.
  - destruct HP as [(_ & -> & _) | (HP & _)]; [exact E | lia].
  - exfalso. destruct HP as [(_ & -> & _ & Hr) | (HP & _)]; [| lia]. exact (Hf (c0_ok_rfo bs nch base Hr)).
  - destruct HP as [(HP & _) | (_ & _ & Hb0 & HL)]; [lia|].
    destruct HL as [(E & _) | (L1 & L2 & L3 & L4)]; [lia|].
    destruct Hl as [(E & H) | (H1 & H2 & H3)].
    + exfalso. apply (H b); [lia|]. apply c0_ok_rfo. split; [lia|]. split; [lia | exact L3].
    + destruct (Z.lt_trichotomy want b) as [Lt | [Eq | Gt]]; [| exact Eq |].
      * exfalso. destruct (c0_rfo_ok bs nch want H2) as (_ & _ & HF). apply HF. apply L4. lia.
      * exfalso. apply (H3 b); [lia|]. apply c0_ok_rfo. split; [lia|]. split; [lia | exact L3].
Qed.


Lemma c0_kept_placed : forall bs b k p s, boxreg_inv bs -> bx_n bs < 5 -> llvm_kept bs (decl_bytes bs b k p s) (-1).
Proof.
  intros bs b k p s [[HL [H1 _]] _] Hn5 j Hj. unfold boxreg_B1 in H1.
  pose proof (decl_row_length b k p s) as HR.
  replace (decl_bytes bs b k p s) with (new_row_bytes bs (decl_row b k p s)) by reflexivity.
  assert (Hn : 0 <= bx_n bs <= 4) by lia.
  unfold bx_base, bx_nch, bx_pinned, bx_mac, bx_name, rd4.
  rewrite !(new_row_old bs (decl_row b k p s) HL Hn HR j) by lia.
  replace (56 * j) with (56 * j + 0) by lia.
  rewrite !(new_row_old bs (decl_row b k p s) HL Hn HR j) by lia.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [right; reflexivity | right; reflexivity].
Qed.


Lemma c0_zero_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10392 zero6.
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn [length zero6 repeat]; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma c0_empty_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x102cd [Z_to_bv 8 0].
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn [length]; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma c0_lor1 : forall x : word, Z.lor 18446744073709551615 (bv_unsigned x) = 18446744073709551615.
Proof.
  intros x. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2 ^ 64) in R.
  change 18446744073709551615 with (Z.ones 64).
  apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
  destruct (Z.lt_ge_cases i 64) as [L|L].
  - rewrite Z.ones_spec_low by lia. reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite <- (Z.mod_small (bv_unsigned x) (2 ^ 64)) by lia.
    rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma c0_kept_refl : forall bs, llvm_kept bs bs (-1).
Proof. intros bs j Hj. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; right; reflexivity. Qed.

Lemma c0_row_bsub : forall bs b k p s o w, length bs = 288%nat -> 0 <= bx_n bs <= 4 -> 0 <= o -> 0 <= w -> o + w <= 56 ->
  bsub (decl_bytes bs b k p s) (56 * bx_n bs + o) w = bsub (decl_row b k p s) o w.
Proof.
  intros bs b k p s o w HL Hn Ho Hw Hl.
  change (decl_bytes bs b k p s) with (new_row_bytes bs (decl_row b k p s)).
  rewrite new_row_new by first [exact HL | lia | apply decl_row_length]. reflexivity.
Qed.

Lemma c0_decl_length : forall bs b k p s, length bs = 288%nat -> 0 <= bx_n bs <= 4 ->
  length (decl_bytes bs b k p s) = 288%nat.
Proof.
  intros bs b k p s HL Hn. change (decl_bytes bs b k p s) with (new_row_bytes bs (decl_row b k p s)).
  rewrite new_row_length by first [exact HL | lia | apply decl_row_length]. reflexivity.
Qed.

Lemma c0_row_rd : forall m r bs b k p s o v, bytes_at rsegs m r (decl_bytes bs b k p s) -> length bs = 288%nat ->
  0 <= bx_n bs <= 4 -> 0 <= o -> o + 4 <= 56 -> bsub (decl_row b k p s) o 4 = le4 (Z_to_bv 64 v) ->
  -2^31 <= v < 2^31 ->
  ov_read_bytes rsegs m (wa (r + (56 * bx_n bs + o))) 4 = Some (le4 (Z_to_bv 64 v)).
Proof.
  intros m r bs b k p s o v HB HL Hn Ho Hl Hr Hv.
  assert (E : bsub (decl_bytes bs b k p s) (56 * bx_n bs + o) 4 = le4 (Z_to_bv 64 v))
    by (rewrite c0_row_bsub by lia; exact Hr).
  pose proof (rd4_le4 _ _ v Hv E) as Er.
  apply bx_ov4. rewrite <- Er. apply rd4_bytes_at; [exact HB | lia |].
  rewrite c0_decl_length by assumption. lia.
Qed.

Lemma c0_decl_n : forall bs b k p s, length bs = 288%nat -> 0 <= bx_n bs <= 4 ->
  bx_n (decl_bytes bs b k p s) = bx_n bs + 1.
Proof.
  intros bs b k p s HL Hn. change (decl_bytes bs b k p s) with (new_row_bytes bs (decl_row b k p s)).
  rewrite new_row_n by first [exact HL | lia | apply decl_row_length]. reflexivity.
Qed.

Lemma c0_decl_fabric : forall bs b k p s, length bs = 288%nat -> 0 <= bx_n bs <= 4 ->
  bx_fabric (decl_bytes bs b k p s) = bx_fabric bs.
Proof.
  intros bs b k p s HL Hn. change (decl_bytes bs b k p s) with (new_row_bytes bs (decl_row b k p s)).
  rewrite new_row_fabric by first [exact HL | lia | apply decl_row_length]. reflexivity.
Qed.

Lemma c0_pin_val : forall z, -2^63 <= z < 2^63 ->
  Z_to_bv 64 (Z.lxor (bv_unsigned (v_slti (Z_to_bv 64 z) 0)) 1) = Z_to_bv 64 (if z <? 0 then 0 else 1).
Proof. intros z Hz. unfold v_slti, zsig. rewrite bx_signed by lia. destruct (z <? 0); reflexivity. Qed.

Lemma c0_lts56 : forall z, -128 <= z < 128 -> bv_lts (Z_to_bv 64 (z * 2 ^ 56)) (Z_to_bv 64 0) = (z <? 0).
Proof.
  intros z Hz.
  rewrite bx_lts by (change (2 ^ 56) with 72057594037927936; change (2 ^ 63) with 9223372036854775808; lia).
  destruct (Z.ltb_spec z 0); [apply Z.ltb_lt | apply Z.ltb_ge]; change (2 ^ 56) with 72057594037927936; lia.
Qed.

Lemma c0_swrap_small : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648.
  change (bv_modulus 32) with 4294967296. change (2^31) with 2147483648 in Hz. Z.div_mod_to_equations. lia.
Qed.

Lemma c0_srai : forall z, 0 <= z < 2^31 ->
  Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_swrap 32 (bv_unsigned (Z_to_bv 64 z))) 31)) = Z_to_bv 64 0.
Proof.
  intros z Hz. rewrite unsigned_lit by lia. rewrite (c0_swrap_small z) by lia.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Definition c0_q2 (sp gp tp s0 s8 s9 s10 s11 : word) (lo r fab nm : Z) (j0 bs : list byte)
    (m0 : word -> option byte) (ms' : machine_state) : Prop :=
  exists (t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
         (m' : word -> option byte) (bs' j1' : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x1330c) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 nm) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (Z_to_bv 64 0x14648) fc' None m' (seg_rom rsegs) /\
    FP.frm0 fc' /\
    munch [(lo, bv_unsigned sp + 32); (r, r + 288)] m0 m' /\ wmono rsegs m0 m' /\
    bytes_at rsegs m' r bs' /\ wr_at rsegs m' r 288 /\
    rw_cells rsegs m' (bv_unsigned sp) [CB 8 j0; C8 (Z_to_bv 64 fab); CB 16 j1'] /\
    boxreg_inv bs' /\ bx_fabric bs' = fab /\ llvm_kept bs bs' (-1).

Lemma llvm_c0_k13200 :
  forall (ra sp gp tp t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s3 s8 s9 s10 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
         (lo r nch base op nm want nl : Z) (j0 j1 bs NB slack : list byte) (s : list Z) (canary : word),
    reac_boxreg_declare_contract -> bcmp_contract -> strncmp_contract ->
    0 <= nch < 256 -> -128 <= base < 128 -> 0 <= op < 256 ->
    boxreg_inv bs -> length bs = 288%nat -> r mod 8 = 0 -> pf_img_free r 288 -> c0_want bs nch base want ->
    bytes_at rsegs m r bs -> wr_at rsegs m r 288 ->
    rw_cells rsegs m (bv_unsigned sp) [CB 8 j0; C8 (Z_to_bv 64 (bx_fabric bs)); CB 16 j1] ->
    stk rsegs m lo (bv_unsigned sp) -> 0x50000 <= lo -> lo + 6000 <= bv_unsigned sp -> bv_unsigned sp + 448 <= 2 ^ 47 ->
    4096 <= r -> r + 288 <= lo ->
    0 < nm -> Forall (fun c => 0 < c < 256) s -> Z.of_nat (length s) < 2 ^ 31 - 1 ->
    bytes_at rsegs m nm NB -> NB = pf_bytes (s ++ [0]) ++ slack -> Z.of_nat (length NB) = nl ->
    (- (nm + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack) ->
    nm + nl <= lo -> (nm + nl <= r \/ r + 288 <= nm) ->
    mem_inv rsegs m -> MemNorm.task_mem rsegs m0 -> FP.frm0 fc ->
    bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
    munch [(lo, bv_unsigned sp + 32); (r, r + 288)] m0 m -> wmono rsegs m0 m ->
    evt rsegs (c0_q2 sp gp tp (Z_to_bv 64 r) s8 s9 s10 (Z_to_bv 64 (bx_fabric bs)) lo r (bx_fabric bs) nm j0 bs m0)
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 r) (Z_to_bv 64 (base * 2 ^ 56)) a0 a1 (Z_to_bv 64 want) a3 a4 a5 a6 a7
               (Z_to_bv 64 nm) s3 (Z_to_bv 64 nch) (Z_to_bv 64 base) (Z_to_bv 64 op) (Z_to_bv 64 (bx_n bs))
               s8 s9 s10 (Z_to_bv 64 (bx_fabric bs)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x13200) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s3 s8 s9 s10 t3 t4 t5 t6 F fc m0 m lo r nch base op nm want nl
    j0 j1 bs NB slack s canary DC BC SC Hnch Hbase Hop INV HL Hr8 HIF HWANT HB HWR CW ST Hlo HLO HSP Hr4 HRL Hnm
    Hsok Hslen HNB HNBe HNBl Hmod Hnlo Hnr MI TM Hfc HG1 HG2 MU WM.
  unfold reac_boxreg_declare_contract in DC. unfold GOT_GUARD, GUARD in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof (nm_len s slack) as HNL. rewrite <- HNBe, HNBl in HNL.
  step. do 8 step.
  rewrite c0_given by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HNA : name_ok mm (bv_unsigned sp) lo r (if Z.land op 8 =? 0 then nm else 0)
                    (if Z.land op 8 =? 0 then s else []))
      by (destruct (Z.land op 8 =? 0);
          [ right; split; [lia|]; split; [exact Hsok|]; split; [exact Hslen|]; exists slack; rewrite <- HNBe;
            split; [assumption|]; split; [exact Hmod|]; split; lia
          | left; split; reflexivity ]);
    assert (TMm : MemNorm.task_mem rsegs mm)
      by (apply (nm_task_munch [(lo, bv_unsigned sp + 32); (r, r + 288)] m0 mm TM);
          [ assumption | intros x Hx; unfold TASK_SIZE; cbn [outside] in Hx; lia ])
  end.
  eapply evt_cut.
  { eapply DC with (r := r) (k := nch) (nm := if Z.land op 8 =? 0 then nm else 0) (b0 := base) (lo := lo) (bs := bs)
      (canary := canary) (s := if Z.land op 8 =? 0 then s else []);
      first [ reflexivity | exact HNA | exact TMm | assumption | unfold DECLARE_K; lia | unfold IMG_END; lia
            | destruct (Z.land op 8 =? 0); lia ]. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & m2
    & E & FK & Hfc' & MUc & WMc & MI2 & TM2 & ST2 & RES).
  subst ms'.
  lazymatch type of MUc with munch _ ?mm ?mm' => transport_after_call rsegs mm mm' MUc WMc end.
  clear MUc WMc.
  replace (ret_pc (Z_to_bv 64 78372)) with (Z_to_bv 64 78372) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct RES as [(HR & -> & HB2) | (b & p & HP & -> & HB2)].
  - pose proof (c0_link_refused bs nch base want HWANT HR) as ->.
    assert (R280 : ov_read_bytes rsegs m2 (wa (r + 280)) 4 = Some (le4 (Z_to_bv 64 (bx_n bs))))
      by (apply bx_ov4; exact (rd4_bytes_at m2 r bs 280 HB2 ltac:(lia) ltac:(rewrite HL; lia))).
    pose proof (rd4_range bs 280) as Rn. change (rd4 bs 280) with (bx_n bs) in Rn.
    step. step. step. if_true.
    step. rewrite ?bx_sx32 by lia.
    step. if_true.
    step. step. if_false.
    step. step. step. step.
    rewrite c0_lor1. if_false.
    step. step.
    lazymatch goal with H : rw_cells _ ?mm (bv_unsigned sp) (CB 8 j0 :: C8 ?f :: C8 ?w :: CB _ ?x :: []) |- _ =>
      pose proof (rw_cells_merge rsegs mm (bv_unsigned sp) [CB 8 j0; C8 f] [C8 w; CB 8 x] [] H) as CWm;
      cbn [app] in CWm end.
    finish.
    all: first [exact HB2 | exact INV | exact CWm | reflexivity | apply c0_kept_refl].
  - pose proof (c0_link_placed bs nch base want b p HWANT HP) as ->.
    pose proof HP as (Hwd & Hn5 & HPC).
    assert (Hn : 0 <= bx_n bs <= 4) by (pose proof INV as ((_ & H1 & _) & _); unfold boxreg_B1 in H1; lia).
    assert (Hfb : 1 <= bx_fabric bs <= 40) by (pose proof INV as ((_ & _ & H2 & _) & _); unfold boxreg_B2 in H2; lia).
    assert (Hbr : 0 <= b <= 40 /\ (p = 0 \/ p = 1)).
    { destruct HPC as [(_ & -> & -> & H1 & H2 & _) | (_ & -> & H0 & [(E & _) | (H1 & H2 & _)])]; lia. }
    assert (Hp : p = if base <? 0 then 0 else 1).
    { destruct HPC as [(H0 & _ & -> & _) | (H0 & -> & _)];
        [rewrite (proj2 (Z.ltb_ge base 0) H0) | rewrite (proj2 (Z.ltb_lt base 0) H0)]; reflexivity. }
    assert (Hbb : 0 <= base -> b = base) by (destruct HPC as [(_ & E & _) | (H0 & _)]; [intros; exact E | lia]).
    set (s' := if Z.land op 8 =? 0 then s else []) in HB2, HNA.
    assert (R280 : ov_read_bytes rsegs m2 (wa (r + 280)) 4 = Some (le4 (Z_to_bv 64 (bx_n bs + 1)))).
    { apply bx_ov4. rewrite <- (c0_decl_n bs b nch p s' HL Hn).
      exact (rd4_bytes_at m2 r _ 280 HB2 ltac:(lia) ltac:(rewrite c0_decl_length by assumption; lia)). }
    pose proof (c0_row_rd m2 r bs b nch p _ 12 nch HB2 HL Hn ltac:(lia) ltac:(lia) (decl_row_nch b nch p _)
      ltac:(lia)) as R12.
    step. step. step. rewrite bx_eqb by lia. if_false.
    step. rewrite bx_eqb by lia. if_false.
    step. rewrite ?bx_sx32 by lia.
    step. rewrite bx_lts by lia. if_false.
    step. rewrite swrap_addi by lia.
    step. rewrite bx_eqb by lia. if_false.
    do 6 step. rewrite bx_off56 by lia.
    step. rewrite ?bx_sx32 by lia.
    step. rewrite bx_eqb by lia. if_false.
    do 5 step.
    assert (HZ1 : bytes_at rsegs m2 (bv_unsigned (Z_to_bv 64 (r + 56 * bx_n bs))) zero6).
    { rewrite unsigned_lit by lia. replace (r + 56 * bx_n bs) with (r + (56 * bx_n bs + 0)) by lia.
      rewrite <- (decl_row_mac b nch p s'), <- (c0_row_bsub bs b nch p s' 0 6 HL Hn) by lia.
      apply bytes_at_bsub; [exact HB2 | lia | lia | rewrite c0_decl_length by assumption; lia]. }
    eapply evt_cut.
    { unfold bcmp_contract in BC. eapply BC with (ls := zero6) (rs := zero6) (v := 0).
      - exact HZ1.
      - rewrite unsigned_lit by lia. exact (c0_zero_at _ MI2).
      - reflexivity.
      - exact MI2. }
    post_call rsegs m2.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (c0_row_rd mm r bs b nch p _ 20 p HB2 HL Hn ltac:(lia) ltac:(lia) (decl_row_pin b nch p _)
        ltac:(lia)) as R20 end.
    step. if_false.
    step. rewrite ?bx_sx32 by lia.
    step. step. rewrite c0_pin_val by lia. rewrite <- Hp.
    step. rewrite bx_eqb by lia. if_false.
    step. rewrite c0_lts56 by lia.
    destruct (Z_lt_le_dec base 0) as [Hneg|Hpos];
      [ if_true
      | if_false;
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (c0_row_rd mm r bs b nch p _ 8 b HB2 HL Hn ltac:(lia) ltac:(lia) (decl_row_base b nch p _)
            ltac:(lia)) as R8 end;
        step; rewrite ?bx_sx32 by lia; step; rewrite bx_eqb by lia; pose proof (Hbb Hpos) as Ebb; if_false ].
    all: step; step; rewrite (unsigned_lit op) by lia.
    all: subst s'; destruct (c0_op8 op) as [E8|E8]; rewrite E8 in HB2, HNA |- *; cbn [Z.eqb] in HB2, HNA |- *.
    all: first [if_true | if_false; step; step].
    all: do 4 step; rewrite bx_off56 by lia; step; step; step.
    all: lazymatch goal with HB2 : bytes_at _ ?mm _ (decl_bytes _ _ _ _ ?sx) |- _ =>
      assert (HNF : bytes_at rsegs mm (r + (56 * bx_n bs + 24)) (name_field sx))
        by (rewrite <- (decl_row_name b nch p sx), <- (c0_row_bsub bs b nch p sx 24 32 HL Hn) by lia;
            apply bytes_at_bsub; [exact HB2 | lia | lia | rewrite c0_decl_length by assumption; lia]) end.
    all: unfold strncmp_contract in SC.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply SC with (v := 0);
        [ match goal with |- bytes_at _ _ ?a _ =>
            replace a with (r + (56 * bx_n bs + 24)) by (rewrite unsigned_lit by lia; lia) end; exact HNF
        | match goal with |- bytes_at _ _ ?a _ =>
            first [ replace a with nm by (rewrite unsigned_lit by lia; lia); exact HNB
                  | replace a with 66253 by (rewrite unsigned_lit by lia; lia); exact (c0_empty_at _ ltac:(eassumption)) ]
          end
        | first [rewrite HNBe; exact (nm_strncmp_field s slack Hsok) | exact (nm_strncmp_field [] [] (Forall_nil _))]
        | assumption ]
      | post_call rsegs mm ] end.
    all: step; if_false.
    all: step; step; rewrite c0_srai by lia.
    all: step; rewrite Z.lor_0_l, Z_to_bv_bv_unsigned.
    all: step; step; rewrite bx_eqb by lia; if_false.
    all: step.
    all: lazymatch goal with HB2 : bytes_at _ ?mm _ (decl_bytes _ _ _ _ ?sx) |- _ =>
      pose proof (c0_row_rd mm r bs b nch p sx 8 b HB2 HL Hn ltac:(lia) ltac:(lia) (decl_row_base b nch p sx)
        ltac:(lia)) as R8' end.
    all: step; rewrite ?bx_sx32 by lia; step; rewrite bx_eqb by lia; if_false.
    all: step; step; step.
    all: lazymatch goal with H : rw_cells _ ?mm (bv_unsigned _) (CB 8 _ :: C8 ?f :: C8 ?w :: CB _ ?x :: []) |- _ =>
      pose proof (rw_cells_merge rsegs mm (bv_unsigned sp) [CB 8 j0; C8 f] [C8 w; CB 8 x] [] H) as CWm;
      cbn [app] in CWm end.
    all: finish.
    all: first [ exact HB2 | exact CWm | reflexivity | apply c0_kept_placed; assumption
               | apply c0_decl_fabric; assumption
               | eapply reac_boxreg_declare_keeps_inv_holds; [exact INV | exact HP] ].
Qed.

Lemma c0_even : forall k, k mod 2 = 0 -> Z.even k = true.
Proof. intros k H. rewrite (Z.div_mod k 2) by lia. rewrite H, Z.add_0_r, Z.even_mul. reflexivity. Qed.

Lemma c0_even_mod : forall k, Z.even k = true -> k mod 2 = 0.
Proof. intros k H. rewrite Zmod_even, H. reflexivity. Qed.

Lemma c0_wtest : forall k, 0 <= k < 256 ->
  bv_ltu (Z_to_bv 64 38) (Z_to_bv 64 (k + -2)) = negb ((2 <=? k) && (k <=? 40)).
Proof.
  intros k Hk. unfold bv_ltu. rewrite !unsigned_lit_wrap. change (2 ^ 64) with 18446744073709551616.
  destruct (Z.leb_spec 2 k), (Z.leb_spec k 40); cbn [andb negb];
    first [apply Z.ltb_ge | apply Z.ltb_lt]; Z.div_mod_to_equations; lia.
Qed.

Lemma c0_mem_inv_hi : forall W m m', mem_inv rsegs m -> munch W m m' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> LF_RES_TOP <= x) -> mem_inv rsegs m'.
Proof.
  intros W m m' MI MU HW a b E.
  pose proof (bv_unsigned_in_range 64 a) as Ra. unfold bv_modulus in Ra. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra.
  destruct (lf_outside_dec W (bv_unsigned a)) as [O|NO].
  - rewrite (MU a O) in E. exact (MI a b E).
  - pose proof (HW _ Ra NO) as Ht. unfold Mem.ro_addr.
    destruct (find_segment rsegs (bv_unsigned a) 1) as [seg|] eqn:Ef; [|reflexivity].
    pose proof (lf_find_top _ _ _ Ef). unfold LF_RES_TOP in *. lia.
Qed.

Ltac c0_c2 w := eapply llvm_c0_k13200 with (want := w); try eassumption; try lia.
Ltac c0_br := first [if_true | if_false | idtac].

Lemma c0_rf_one : forall z : Z,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 1)) + -1))))
    (bv_unsigned (Z_to_bv 64 z))) = Z_to_bv 64 z.
Proof.
  intros z.
  replace (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 1)) + -1)))) with 0
    by (vm_compute; reflexivity).
  rewrite Z.lor_0_l. apply Z_to_bv_bv_unsigned.
Qed.

Lemma c0_rf_zero : forall z : Z,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 0)) + -1))))
    (bv_unsigned (Z_to_bv 64 z))) = Z_to_bv 64 (-1).
Proof.
  intros z.
  replace (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 0)) + -1))))
    with 18446744073709551615 by (vm_compute; reflexivity).
  rewrite c0_lor1. apply Z_to_bv_eqm. reflexivity.
Qed.

Lemma llvm_c0_k12ea4 :
  forall (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
         (lo r nch base op nm nl : Z) (j0 j1 bs NB slack : list byte) (s : list Z) (canary : word),
    range_free_contract -> lowest_free_contract ->
    reac_boxreg_declare_contract -> bcmp_contract -> strncmp_contract ->
    0 <= nch < 256 -> -128 <= base < 128 -> 0 <= op < 256 ->
    boxreg_inv bs -> length bs = 288%nat -> r mod 8 = 0 -> pf_img_free r 288 ->
    bytes_at rsegs m r bs -> wr_at rsegs m r 288 ->
    rw_cells rsegs m (bv_unsigned sp) [CB 8 j0; C8 (Z_to_bv 64 (bx_fabric bs)); CB 16 j1] ->
    bytes_at rsegs m (bv_unsigned sp + 32) bs ->
    stk rsegs m lo (bv_unsigned sp) -> 0x50000 <= lo -> lo + 6000 <= bv_unsigned sp -> bv_unsigned sp + 448 <= 2 ^ 47 ->
    4096 <= r -> r + 288 <= lo ->
    0 < nm -> Forall (fun c => 0 < c < 256) s -> Z.of_nat (length s) < 2 ^ 31 - 1 ->
    bytes_at rsegs m nm NB -> NB = pf_bytes (s ++ [0]) ++ slack -> Z.of_nat (length NB) = nl ->
    (- (nm + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack) ->
    nm + nl <= lo -> (nm + nl <= r \/ r + 288 <= nm) ->
    mem_inv rsegs m -> MemNorm.task_mem rsegs m0 -> FP.frm0 fc ->
    bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
    munch [(lo, bv_unsigned sp + 32); (r, r + 288)] m0 m -> wmono rsegs m0 m ->
    evt rsegs (c0_q2 sp gp tp (Z_to_bv 64 r) s8 s9 s10 (Z_to_bv 64 (bx_fabric bs)) lo r (bx_fabric bs) nm j0 bs m0)
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 r) (Z_to_bv 64 (base * 2 ^ 56)) (Z_to_bv 64 nm) a1 a2 a3 a4 a5 a6 a7
               s2 s3 (Z_to_bv 64 nch) (Z_to_bv 64 base) (Z_to_bv 64 op) (Z_to_bv 64 (bx_n bs))
               s8 s9 s10 (Z_to_bv 64 (bx_fabric bs)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x12ea4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 t3 t4 t5 t6 F fc m0 m lo r nch base op nm nl
    j0 j1 bs NB slack s canary RF LF DC BC SC Hnch Hbase Hop INV HL Hr8 HIF HB HWR CW HP ST Hlo HLO HSP Hr4 HRL Hnm
    Hsok Hslen HNB HNBe HNBl Hmod Hnlo Hnr MI TM Hfc HG1 HG2 MU WM.
  pose proof INV as ((_ & HB1 & HB2 & HB3 & _) & _).
  assert (Hn : 0 <= bx_n bs <= 5) by exact HB1.
  assert (Hfb : 1 <= bx_fabric bs <= 40) by exact HB2.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  unfold GOT_GUARD, GUARD in HG1, HG2.
  pose proof (nm_len s slack) as HNL. rewrite <- HNBe, HNBl in HNL.
  step. step.
  step. rewrite bx_lts by lia.
  destruct (Z_lt_le_dec (bx_fabric bs) nch) as [T1|T1]; c0_br.
  { c0_c2 (-1). left. split; [intros ((_ & _ & Hle) & _); lia | reflexivity]. }
  step. step.
  step. rewrite c0_wtest by lia.
  destruct (Z.leb_spec 2 nch) as [W1|W1]; destruct (Z.leb_spec nch 40) as [W2|W2]; cbn [andb negb]; c0_br;
    try solve [c0_c2 (-1); left; split; [intros ((_ & Hr & _) & _); lia | reflexivity]].
  all: try solve [c0_c2 (-1)].
  step. rewrite bx_land1 by lia.
  step. rewrite bx_eqb by (pose proof (Z.mod_pos_bound nch 2); lia).
  destruct (Z.eqb_spec (nch mod 2) 0) as [E2|E2]; cbn [negb]; c0_br;
    [| c0_c2 (-1); left; split; [intros ((He & _) & _); apply c0_even_mod in He; lia | reflexivity]].
  assert (Hw : box_width_ok nch (bx_fabric bs)) by (split; [apply c0_even; exact E2 | lia]).
  step.
  step. rewrite bx_lts by lia.
  destruct (Z.ltb_spec 4 (bx_n bs)) as [N4|N4]; c0_br.
  { c0_c2 (-1). left. split; [intros (_ & Hn5); lia | reflexivity]. }
  step.
  step. rewrite c0_lts56 by lia.
  destruct (Z.ltb_spec base 0) as [Hneg|Hpos]; c0_br.
  - step. step. step.
    eapply evt_cut.
    { unfold lowest_free_contract in LF.
      eapply LF with (lo := lo) (t := bv_unsigned sp + 32) (nch := nch) (fabric := bx_fabric bs) (bs := bs);
        first [reflexivity | assumption | unfold LOWEST_FREE_FRAME; lia | lia]. }
    intros ms' (t0' & t1' & t2' & rr & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'
      & E & MUc & WMc & ST' & z & -> & HLF).
    subst ms'.
    assert (MI' : mem_inv rsegs m').
    { apply (c0_mem_inv_hi _ m m' MI MUc). intros x Hx NO. apply Z.nlt_ge. intros Hlt. apply NO.
      cbn [outside]. unfold LOWEST_FREE_FRAME, LF_RES_TOP in *. split; [lia | exact I]. }
    unfold LOWEST_FREE_FRAME in MUc. transport_after_call rsegs m m' MUc WMc. clear MUc WMc MI.
    replace (ret_pc (Z_to_bv 64 0x131fc)) with (Z_to_bv 64 0x131fc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    step.
    c0_c2 z. right. right. split; [exact Hw|]. split; [lia|]. split; [lia | exact HLF].
  - do 4 step.
    eapply evt_cut.
    { unfold range_free_contract in RF.
      eapply RF with (t := bv_unsigned sp + 32) (base := base) (nch := nch) (fabric := bx_fabric bs) (bs := bs);
        first [reflexivity | assumption | lia]. }
    intros ms' (t0' & t1' & t2' & rr & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & E & HRF).
    subst ms'.
    replace (ret_pc (Z_to_bv 64 0x12ee4)) with (Z_to_bv 64 0x12ee4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    destruct HRF as [(-> & Hok) | (-> & Hnok)].
    + step. step. step. rewrite c0_rf_one. step.
      c0_c2 base. right. left. split; [exact Hw|]. split; [lia|]. split; [lia|]. left. split; [exact Hok | reflexivity].
    + step. step. step. rewrite c0_rf_zero. step.
      c0_c2 (-1). right. left. split; [exact Hw|]. split; [lia|]. split; [lia|]. right. split; [exact Hnok | reflexivity].
Qed.

Lemma c0_nch_range : forall pl, 0 <= c0_nch pl < 256.
Proof.
  intros [|x pl]; cbn [c0_nch]; [lia|]. pose proof (bv_unsigned_in_range 8 x) as R. change (bv_modulus 8) with 256 in R.
  lia.
Qed.

Lemma c0_base_range : forall pl, -128 <= c0_base pl < 128.
Proof.
  intros [|x [|y pl]]; cbn [c0_base]; try lia.
  pose proof (bv_unsigned_in_range 8 y) as R. change (bv_modulus 8) with 256 in R.
  destruct (c0_byte_signed y) as [[E H]|[E H]]; rewrite E; lia.
Qed.

Lemma c0_used_split : forall pl, Z.of_nat (length (firstn 2 pl)) = c0_used pl.
Proof. intros pl. rewrite length_firstn. unfold c0_used. lia. Qed.

Lemma c0_skip_len : forall pl, Z.of_nat (length (skipn 2 pl)) = Z.of_nat (length pl) - c0_used pl /\
  0 <= c0_used pl <= Z.of_nat (length pl).
Proof. intros pl. rewrite length_skipn. unfold c0_used. lia. Qed.

Section C0.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis MALLOC : forall fx' : YK11.FPState, @malloc_contract fx' rc B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= YM05.alloc_ceiling.
Hypothesis SLACK : block_slack_present B API.
Hypothesis SNPRINTF : snprintf_contract.

Theorem llvm_case0_ok : llvm_case_ok B API 0.
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n b i k c CTX HT HPC.
  match goal with |- SR _ _ ?Q => set (Pk := Q) end.
  destruct HT as (fx' & regs & mem & md & L & A & r & fab & ip & inn & bs & op & j0 & j1 & jm & Ec & Hfrm & RB & E9 & E18
    & E19 & E21 & E22 & E23 & FRC & Hi & Hinn & Hpip & Hipn & Hop & RWR & INV & Hfab & AL & Hk).
  assert (Epc : Z_to_bv 64 (llvm_case_pc (Z.land op 3)) = Z_to_bv 64 0x12d6c).
  { destruct HPC as (ms & md1 & Ec' & Ep). rewrite Ec in Ec'. injection Ec' as Ems Emd. rewrite <- Ems in Ep. exact Ep. }
  subst c. rewrite Epc. clear HPC Epc.
  pose proof CTX as ((SEGS & HMAL & HFRE & HGG & HG & AX) & Hstk & Hra & Hpre & Hsn & Hsp47 & Hres0 & Hroom & Hro0
    & Hrelro & Hfrm0 & Hn26).
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra0 & Hal & Hceil & H63 & Hstw0 & Htp & Herr0 & Hp & Hn1 & Hpl & Hrod).
  unfold LLVM_K, LLVM_FRAME in Hstk.
  subst fab.
  pose proof RB as BASE0.
  destruct AL as (FR & MINE & RES).
  destruct RB as (E2 & E3 & E4 & E8 & E24 & E25 & E26 & E27).
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & Hro).
  destruct (llvm_md_ok B API _ _ _ _ _ _ _ _ _ _ FR) as [Hh Hl].
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt. pose proof YM05.alloc_ceiling_lt as Hlt.
  assert (Hn0 : 0 < n) by lia.
  destruct (llvm_payload_bound B API stk empty L0 A0 regs0 mem0 md0 ra p n b CTX Hn0) as [Hp4 Hpn].
  pose proof INV as ((HL & HB1 & HB2' & _) & _). unfold boxreg_B1 in HB1. unfold boxreg_B2 in HB2'.
  pose proof MINE as (Hrin & Hr0 & Hrd).
  destruct (lf_mine_bytes B API AX L0 A0 L A mem md r 288 r HM MINE ltac:(lia)) as (_ & _ & Hr1 & _).
  destruct (lf_mine_bytes B API AX L0 A0 L A mem md r 288 (r + 287) HM MINE ltac:(lia)) as (_ & _ & Hr2 & _).
  assert (Hr16 : r mod 16 = 0).
  { pose proof Hrin as Hq. apply blocks_In in Hq as (q & Hq & Hqin). rewrite <- Hq.
    exact (mr_blocks_aligned B _ (aa_laws API) L A mem md q 288 HM Hqin). }
  assert (Hr8 : r mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (HIF : pf_img_free r 288).
  { intros j Hj sg Hsg. destruct (lf_mine_bytes B API AX L0 A0 L A mem md r 288 (r + j) HM MINE ltac:(lia))
      as (_ & Hn' & _). exact (lf_not_img_res B (r + j) SEGS Hn' sg Hsg). }
  set (S := spZ regs0) in *.
  assert (G2 : reg_get regs 2 = Z_to_bv 64 (S - 448)) by exact E2.
  assert (Esp : bv_unsigned (reg_get regs 2) = S - 448) by (rewrite G2; apply unsigned_lit; lia).
  assert (PR : forall j, 0 <= j < Z.of_nat (Z.to_nat (inn - 1)) -> exists v, mrd rsegs mem (wa (ip + 1 + j)) = Some v).
  { intros j Hj. exact (llvm_payload_mrd B API stk empty L0 A0 regs0 mem0 md0 ra p n b L A mem md (ip + 1 + j) CTX FR
      ltac:(lia)). }
  destruct (nm_collect mem (ip + 1) (Z.to_nat (inn - 1)) ltac:(lia) ltac:(lia) PR) as (pl & HPL & Lpl).
  assert (Hlen : Z.of_nat (length pl) = inn - 1) by (rewrite Lpl; lia).
  pose proof (proj1 (lf_cells_split mem (S - 448) regs0 j0 (bx_fabric bs) j1 bs jm (ip + 1) (inn - 1)) FRC)
    as (CF1 & CF2 & CF3 & CF4).
  assert (HPLn : bytes_at rsegs (normalize rsegs mem) (ip + 1) pl) by exact (bytes_at_normalize rsegs mem _ _ Hro HPL).
  assert (CF3n : rw_cells rsegs (normalize rsegs mem) (S - 448 + 328)
                   [C8 (Z_to_bv 64 (ip + 1)); C8 (Z_to_bv 64 (Z.of_nat (length pl)))]).
  { rewrite Hlen. apply (lf_rw_cells_norm B); [exact SEGS | exact Hro | | exact CF3].
    intros x Hx Hix. pose proof (lf_in_img_top B _ SEGS Hix). change (Z.of_nat (cells_size _)) with 16 in Hx. lia. }
  rewrite SEGS.
  eapply (llvm_run_norm fx' regs (Z_to_bv 64 0x12d6c) mem md); [exact Hh | exact Hl | exact Hro | | |].
  { unfold Regs6ss.mkR_of.
    assert (R9 : reg_get regs 9 = Z_to_bv 64 ip) by exact E9.
    assert (R18 : reg_get regs 18 = Z_to_bv 64 (Z.of_nat (length pl))) by (rewrite Hlen; exact E18).
    assert (R21 : reg_get regs 21 = Z_to_bv 64 (1 + Z.of_nat (length pl)))
      by (rewrite Hlen; replace (1 + (inn - 1)) with inn by lia; exact E21).
    rewrite R9, R18, R21.
    eapply llvm_c0_evt1 with (s1 := Z_to_bv 64 0) (s2 := Z_to_bv 64 0) (s5 := Z_to_bv 64 0).
    - lia.
    - rewrite Esp. lia.
    - rewrite Esp. lia.
    - exact HPLn.
    - rewrite Esp. exact CF3n.
    - exact (mem_inv_normalize rsegs mem). }
  { intros ms (a1' & m'' & -> & _). do 5 eexists. reflexivity. }
  intros R F pc' fc m0' (a1' & m'' & HE & MU & WM & MI' & CW') regs1 m1 Hx Hrel Hsame.
  injection HE as ER EF EP EC EM. subst R F pc' fc m0'.
  assert (MU' : munch [(S - 448 + 328, S - 448 + 344)] mem m1).
  { pose proof (munch_rel rsegs _ mem (normalize rsegs mem) m1 m'' (mem_rel_normalize rsegs mem Hro) Hrel Hsame MU) as M.
    rewrite Esp in M. exact M. }
  assert (WM' : wmono rsegs mem m1)
    by exact (wmono_rel rsegs mem (normalize rsegs mem) m1 m'' (mem_rel_normalize rsegs mem Hro) Hrel Hsame WM).
  assert (Hro1 : ro_agree rsegs m1) by exact (ro_agree_same rsegs mem m1 Hro Hsame).
  assert (FR1 : lf_fr B API stk S L0 A0 mem0 md0 L A m1 md).
  { eapply (lf_fr_evt B API SEGS AX HGG); [exact FR | lia | lia | exact MU' | exact WM' | exact Hro1 |].
    intros x Hx0 NO. left. destruct (Z_le_dec (S - 448 + 328) x); destruct (Z_lt_dec x (S - 448 + 344)); try lia;
      exfalso; apply NO; cbn [Frame.outside]; (split; [lia | exact I]). }
  assert (CF1' : rw_cells rsegs m1 (S - 448) [CB 8 j0; C8 (Z_to_bv 64 (bx_fabric bs)); CB 16 j1]).
  { apply (rw_cells_transport rsegs _ mem m1 _ _ CF1 MU' WM'). change (Z.of_nat (cells_size _)) with 32.
    cbn [disjoint_from]. split; [lia | exact I]. }
  assert (CF2' : rw_cells rsegs m1 (S - 448 + 32) [CB 288 bs; CB 8 jm]).
  { apply (rw_cells_transport rsegs _ mem m1 _ _ CF2 MU' WM'). change (Z.of_nat (cells_size _)) with 296.
    cbn [disjoint_from]. split; [lia | exact I]. }
  assert (CF4' : rw_cells rsegs m1 (S - 448 + 344) (llvm_saved_cells regs0)).
  { apply (rw_cells_transport rsegs _ mem m1 _ _ CF4 MU' WM').
    change (Z.of_nat (cells_size (llvm_saved_cells regs0))) with 104. cbn [disjoint_from]. split; [lia | exact I]. }
  assert (CF3' : rw_cells rsegs m1 (S - 448 + 328)
    [C8 (Z_to_bv 64 (ip + 1 + c0_used pl)); C8 (Z_to_bv 64 (Z.of_nat (length (skipn 2 pl))))]).
  { pose proof (lf_rw_cells_rel m1 m'' _ _ Hrel CW') as H. rewrite Esp in H. exact H. }
  assert (RWR1 : rw_cells rsegs m1 r [CB 288 bs]).
  { apply (rw_cells_transport rsegs _ mem m1 _ _ RWR MU' WM'). change (Z.of_nat (cells_size _)) with 288.
    cbn [disjoint_from]. split; [lia | exact I]. }
  assert (HPL1 : bytes_at rsegs m1 (ip + 1 + c0_used pl) (skipn 2 pl)).
  { pose proof (bytes_at_transport rsegs _ mem m1 _ _ HPL MU' ltac:(cbn [disjoint_from]; split; [lia | exact I])) as H.
    rewrite <- (firstn_skipn 2 pl) in H. apply (proj1 (bytes_at_app rsegs m1 _ _ _)) in H. destruct H as [_ H].
    rewrite c0_used_split in H. exact H. }
  assert (G1' : YK11.getr regs1 1 = Z_to_bv 64 0x12ea4) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
  assert (G2' : YK11.getr regs1 2 = Z_to_bv 64 (S - 448)) by (rewrite (lf_getr_eqv _ _ _ Hx); exact E2).
  assert (G4' : YK11.getr regs1 4 = YK11.getr regs0 4) by (rewrite (lf_getr_eqv _ _ _ Hx); exact E4).
  assert (G10' : YK11.getr regs1 10 = Z_to_bv 64 (S - 448 + 328)).
  { rewrite (lf_getr_eqv _ _ _ Hx).
    change (Z_to_bv 64 (bv_unsigned (reg_get regs 2) + 328) = Z_to_bv 64 (S - 448 + 328)). rewrite Esp. reflexivity. }
  assert (BASE1 : llvm_regs_base regs0 regs1 r (bx_fabric bs) i)
    by (unfold llvm_regs_base; rewrite !(lf_getr_eqv _ _ _ Hx); exact BASE0).
  pose proof (rn_k_range (skipn 2 pl)) as Hkr.
  assert (ROOM : room_slots (sb_malloc b LLVM_REQ) (rn_k (skipn 2 pl) + 1)).
  { exact (llvm_name_room B API stk empty L0 A0 regs0 mem0 md0 ra p n b (rn_k (skipn 2 pl) + 1) CTX
      ltac:(unfold LLVM_REQ; lia)). }
  refine (llvm_rn_glue B API MALLOC ERRNO_LOW stk empty L0 A0 regs0 mem0 md0 ra p n b CTX _ regs1 m1 md L A r bs
    (sb_malloc b LLVM_REQ) 0x12ea4 j0 (bx_fabric bs) j1 bs jm (ip + 1 + c0_used pl) (skipn 2 pl) Pk Hn0 FR1 MINE RES ROOM G1'
    _ G2' G4' G10' _ RWR1 HPL1 _ _ _).
  { apply ret_ok_even. reflexivity. }
  { apply (proj2 (lf_cells_split m1 (S - 448) regs0 j0 (bx_fabric bs) j1 bs jm _ _)). auto. }
  { pose proof (c0_used_split pl). unfold c0_used in *. lia. }
  { rewrite length_skipn. pose proof (c0_used_split pl). unfold c0_used in *. lia. }
  intros L' A' regs' mem' md' s FR2 MINE2 MINEs Hsr RES2 Hrp G10s HBs CF2x CR2.
  set (ip2 := ip + 1 + c0_used pl + Z.min (Z.of_nat (length (skipn 2 pl))) 1 + rn_k (skipn 2 pl)) in *.
  set (ln2 := Z.of_nat (length (skipn 2 pl)) - Z.min (Z.of_nat (length (skipn 2 pl))) 1 - rn_k (skipn 2 pl)) in *.
  assert (Hip2 : ip2 + ln2 = p + n /\ 0 <= ln2 /\ p <= ip2).
  { unfold ip2, ln2. pose proof (c0_skip_len pl). lia. }
  pose proof FR2 as (HM2 & HW2 & HB2 & HID2 & Hmd2 & Hhigh2 & Himg2 & Hblk2 & Hbyt2 & Hstw2 & Herr2 & Hgd2 & Hro2).
  destruct (llvm_md_ok B API _ _ _ _ _ _ _ _ _ _ FR2) as [Hh2 Hl2].
  pose proof MINEs as (Hsin & Hs0' & Hsd).
  destruct (lf_mine_bytes B API AX L0 A0 L' A' mem' md' s (rn_k (skipn 2 pl) + 1) s HM2 MINEs ltac:(lia)) as (_ & _ & Hs1 & _).
  destruct (lf_mine_bytes B API AX L0 A0 L' A' mem' md' s (rn_k (skipn 2 pl) + 1) (s + rn_k (skipn 2 pl)) HM2 MINEs ltac:(lia))
    as (_ & _ & Hs2 & _).
  destruct (llvm_name_parts B API SLACK L' A' mem' md' s (rn_k (skipn 2 pl)) (bsub (skipn 2 pl) 1 (rn_k (skipn 2 pl))) HM2 Hsin ltac:(lia)
    ltac:(lia) ltac:(lia) HBs (rn_name_len (skipn 2 pl))) as (slack & HNB & Hstrl & Hmod & Hnl).
  set (nmstr := nm_str (bsub (skipn 2 pl) 1 (rn_k (skipn 2 pl)) ++ [Z_to_bv 8 0])) in *.
  destruct (llvm_guards B API stk empty L0 A0 regs0 mem0 md0 ra p n b L' A' mem' md' CTX HM2) as (HG1 & cn & HG2).
  pose proof (nm_len nmstr slack) as HNL.
  assert (HE8 : 8 * ((s + rn_k (skipn 2 pl) + 1 + 7) / 8) <= YM05.alloc_ceiling)
    by (apply nm_up8; [lia | Z.div_mod_to_equations; lia]).
  assert (Hnr' : s + Z.of_nat (length (pf_bytes (nmstr ++ [0]) ++ slack)) <= r \/
                 r + 288 <= s).
  { destruct Hsr as [Hsr|Hsr]; [left | right; lia].
    pose proof (nm_up8 (s + rn_k (skipn 2 pl) + 1) r ltac:(lia) ltac:(Z.div_mod_to_equations; lia)). lia. }
  assert (BASE' : llvm_regs_base regs0 regs' r (bx_fabric bs) i) by exact (lf_base_pres _ _ _ _ _ _ BASE1 Hrp).
  pose proof BASE' as (F2 & F3 & F4 & F8 & F24 & F25 & F26 & F27).
  assert (Esp' : bv_unsigned (reg_get regs' 2) = S - 448) by (change (bv_unsigned (YK11.getr regs' 2) = S - 448);
    rewrite F2; apply unsigned_lit; lia).
  assert (R9 : reg_get regs' 9 = Z_to_bv 64 (c0_base pl * 2 ^ 56)).
  { change (YK11.getr regs' (Z_to_bv 5 9) = Z_to_bv 64 (c0_base pl * 2 ^ 56)).
    rewrite (Hrp 9 ltac:(unfold callee_saved; lia)), (lf_getr_eqv _ _ _ Hx). reflexivity. }
  assert (R20 : reg_get regs' 20 = Z_to_bv 64 (c0_nch pl)).
  { change (YK11.getr regs' (Z_to_bv 5 20) = Z_to_bv 64 (c0_nch pl)).
    rewrite (Hrp 20 ltac:(unfold callee_saved; lia)), (lf_getr_eqv _ _ _ Hx). reflexivity. }
  assert (R21 : reg_get regs' 21 = Z_to_bv 64 (c0_base pl)).
  { change (YK11.getr regs' (Z_to_bv 5 21) = Z_to_bv 64 (c0_base pl)).
    rewrite (Hrp 21 ltac:(unfold callee_saved; lia)), (lf_getr_eqv _ _ _ Hx). reflexivity. }
  assert (R22 : reg_get regs' 22 = Z_to_bv 64 op).
  { change (YK11.getr regs' (Z_to_bv 5 22) = Z_to_bv 64 op).
    rewrite (Hrp 22 ltac:(unfold callee_saved; lia)), (lf_getr_eqv _ _ _ Hx). exact E22. }
  assert (R23 : reg_get regs' 23 = Z_to_bv 64 (bx_n bs)).
  { change (YK11.getr regs' (Z_to_bv 5 23) = Z_to_bv 64 (bx_n bs)).
    rewrite (Hrp 23 ltac:(unfold callee_saved; lia)), (lf_getr_eqv _ _ _ Hx). exact E23. }
  assert (R8 : reg_get regs' 8 = Z_to_bv 64 r) by exact F8.
  assert (R10 : reg_get regs' 10 = Z_to_bv 64 s) by exact G10s.
  assert (R27 : reg_get regs' 27 = Z_to_bv 64 (bx_fabric bs)) by exact F27.
  pose proof (proj1 (lf_cells_split mem' (S - 448) regs0 j0 (bx_fabric bs) j1 bs jm ip2 ln2) CF2x)
    as (D1 & D2 & D3 & D4).
  assert (NOIMG : forall a x, LF_RES_TOP <= a -> 0 <= x -> ~ in_img B (a + x))
    by (intros a x Ha Hxw Hix; pose proof (lf_in_img_top B _ SEGS Hix); lia).
  set (M := MemNorm.normalize_cj rsegs mem').
  assert (CWM : rw_cells rsegs M (bv_unsigned (reg_get regs' 2)) [CB 8 j0; C8 (Z_to_bv 64 (bx_fabric bs)); CB 16 j1]).
  { rewrite Esp'. apply (nm_rw_cj B); [exact SEGS | exact Hro2 | exact D1 | intros x Hxw; apply NOIMG; lia |].
    change (Z.of_nat (cells_size _)) with 32. unfold TASK_SIZE. lia. }
  assert (HPM : bytes_at rsegs M (bv_unsigned (reg_get regs' 2) + 32) bs).
  { rewrite Esp'. apply nm_bytes_cj; [exact Hro2 | | rewrite HL; unfold TASK_SIZE; lia].
    destruct D2 as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. apply (proj1 (bytes_at_app rsegs _ _ _ _)) in Hb.
    exact (proj1 Hb). }
  assert (CRM : rw_cells rsegs M r [CB 288 bs]).
  { apply (nm_rw_cj B); [exact SEGS | exact Hro2 | exact CR2 | |].
    - intros x Hxw. change (Z.of_nat (cells_size _)) with 288 in Hxw.
      destruct (lf_mine_bytes B API AX L0 A0 L' A' mem' md' r 288 (r + x) HM2 MINE2 ltac:(lia)) as (_ & N & _).
      exact N.
    - change (Z.of_nat (cells_size _)) with 288. unfold TASK_SIZE. lia. }
  assert (HrM : bytes_at rsegs M r bs).
  { destruct CRM as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (HwM : wr_at rsegs M r 288) by (destruct CRM as [_ Hw]; exact Hw).
  assert (STM : Frame.stk rsegs M (S - stk) (bv_unsigned (reg_get regs' 2))).
  { rewrite Esp'. apply (nm_stk_cj B); [exact SEGS | exact Hro2 | lia | unfold TASK_SIZE; lia |].
    intros a Ha. rewrite <- SEGS. apply Hstw2. lia. }
  assert (HNBM : bytes_at rsegs M s (pf_bytes (nmstr ++ [0]) ++ slack)).
  { apply nm_bytes_cj; [exact Hro2 | exact HNB | rewrite HNL; unfold TASK_SIZE; lia]. }
  assert (HG1M : bytes_at rsegs M GOT_GUARD (le8 (Z_to_bv 64 GUARD)))
    by (apply nm_bytes_cj; [exact Hro2 | exact HG1 | rewrite length_le8; unfold GOT_GUARD, TASK_SIZE; lia]).
  assert (HG2M : bytes_at rsegs M GUARD (le8 cn))
    by (apply nm_bytes_cj; [exact Hro2 | exact HG2 | rewrite length_le8; unfold GUARD, TASK_SIZE; lia]).
  assert (MIM : mem_inv rsegs M)
    by exact (MemNorm.mem_inv_cj_inv rsegs _ (MemNorm.mem_inv_cj_normalize rsegs mem')).
  assert (TMM : MemNorm.task_mem rsegs M)
    by exact (MemNorm.mem_inv_cj_task rsegs _ (MemNorm.mem_inv_cj_normalize rsegs mem')).
  assert (Hnlo' : s + Z.of_nat (length (pf_bytes (nmstr ++ [0]) ++ slack)) <= S - stk) by lia.
  eapply (llvm_run_norm_cj (mkFP (@fp_regs fx') (@fp_csr fx')) regs' (Z_to_bv 64 0x12ea4) mem' md');
    [exact Hh2 | exact Hl2 | exact Hro2 | | |].
  { unfold Regs6ss.mkR_of. rewrite R8, R9, R10, R20, R21, R22, R23, R27. fold M.
    eapply llvm_c0_k12ea4 with (lo := S - stk) (r := r) (nch := c0_nch pl) (base := c0_base pl) (op := op) (nm := s)
      (j0 := j0) (j1 := j1) (bs := bs) (NB := pf_bytes (nmstr ++ [0]) ++ slack) (slack := slack) (s := nmstr)
      (canary := cn) (nl := Z.of_nat (length (pf_bytes (nmstr ++ [0]) ++ slack))) (m0 := M);
      first [ exact range_free.range_free_holds | exact (lowest_free.lowest_free_holds range_free.range_free_holds)
            | exact (reac_boxreg_declare.reac_boxreg_declare_holds lowest_free_base.lowest_free_base_holds
                       memset.memset_holds SNPRINTF)
            | exact bcmp.bcmp_holds | exact strncmp.strncmp_holds | apply c0_nch_range | apply c0_base_range
            | apply nm_str_ok | apply munch_refl | apply wmono_refl | exact Hfrm | assumption | reflexivity | lia ]. }
  { intros ms HQ.
    destruct HQ as (t0q & t1q & t2q & s1q & a1q & a2q & a3q & a4q & a5q & a6q & a7q & s2q & s3q & s4q & s5q & s6q & s7q
      & t3q & t4q & t5q & t6q & Fq & fcq & mq & bsq & j1q & -> & _).
    do 5 eexists. reflexivity. }
  intros R F pc' fc m0' HQ regs2 m2 Hx2 Hrel2 Hsame2.
  destruct HQ as (t0q & t1q & t2q & s1q & a1q & a2q & a3q & a4q & a5q & a6q & a7q & s2q & s3q & s4q & s5q & s6q & s7q
    & t3q & t4q & t5q & t6q & Fq & fcq & mq & bs' & j1' & HE & Hfc' & MU2 & WM2 & HBr & HWr & CW2 & INV' & Hfab' & KEPT).
  injection HE as ER EF EP EC EM. subst R F pc' fc m0'.
  pose proof (MemNorm.mem_rel_cj_normalize rsegs mem' Hro2) as HRn.
  assert (MU2' : munch [(S - stk, S - 448 + 32); (r, r + 288)] mem' m2).
  { pose proof (MemNorm.munch_rel_cj rsegs _ mem' _ m2 mq HRn Hrel2 Hsame2 MU2) as Mx. rewrite Esp' in Mx. exact Mx. }
  assert (WM2' : wmono rsegs mem' m2) by exact (MemNorm.wmono_rel_cj rsegs mem' _ m2 mq HRn Hrel2 Hsame2 WM2).
  assert (Hro3 : ro_agree rsegs m2) by exact (MemNorm.ro_agree_same_cj rsegs mem' m2 Hro2 Hsame2).
  assert (FR3 : lf_fr B API stk S L0 A0 mem0 md0 L' A' m2 md').
  { eapply (lf_fr_evt B API SEGS AX HGG); [exact FR2 | lia | lia | exact MU2' | exact WM2' | exact Hro3 |].
    intros x Hx0 NO.
    destruct (Z_le_dec (S - stk) x); destruct (Z_lt_dec x S); try (left; lia).
    all: right; exists r, 288; split; [exact MINE2|];
      destruct (Z_le_dec r x); destruct (Z_lt_dec x (r + 288)); try lia;
      exfalso; apply NO; cbn [Frame.outside]; repeat split; lia. }
  assert (CFm : rw_cells rsegs m2 (S - 448) (lf_cells regs0 j0 (bx_fabric bs) j1' bs jm ip2 ln2)).
  { apply (proj2 (lf_cells_split m2 (S - 448) regs0 j0 (bx_fabric bs) j1' bs jm ip2 ln2)).
    split; [pose proof (nm_rw_rel_cj m2 mq _ _ Hrel2 CW2) as H; rewrite Esp' in H; exact H|].
    split; [apply (rw_cells_transport rsegs _ mem' m2 _ _ D2 MU2' WM2'); change (Z.of_nat (cells_size _)) with 296;
      cbn [disjoint_from]; repeat split; lia|].
    split; [apply (rw_cells_transport rsegs _ mem' m2 _ _ D3 MU2' WM2'); change (Z.of_nat (cells_size _)) with 16;
      cbn [disjoint_from]; repeat split; lia|].
    apply (rw_cells_transport rsegs _ mem' m2 _ _ D4 MU2' WM2').
    change (Z.of_nat (cells_size (llvm_saved_cells regs0))) with 104. cbn [disjoint_from]. repeat split; lia. }
  assert (CRm : rw_cells rsegs m2 r [CB 288 bs']).
  { pose proof INV' as ((HL' & _) & _).
    split; [split; [cbn; split; [exact HL' | exact I] |] |].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact (MemNorm.bytes_at_rel_cj rsegs m2 mq r bs' Hrel2 HBr).
    - change (Z.of_nat (cells_size _)) with 288. exact (MemNorm.wr_at_rel_cj rsegs m2 mq r 288 Hrel2 HWr). }
  assert (BASE2 : llvm_regs_base regs0 regs2 r (bx_fabric bs) i).
  { unfold llvm_regs_base. rewrite !(lf_getr_eqv _ _ _ Hx2).
    split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [reflexivity|].
    split; [exact F24|]. split; [exact F25|]. split; [exact F26 | reflexivity]. }
  pose proof BASE2 as (H2 & H3 & H4 & _).
  assert (G10'' : YK11.getr regs2 10 = Z_to_bv 64 s) by (rewrite (lf_getr_eqv _ _ _ Hx2); reflexivity).
  assert (G1'' : YK11.getr regs2 1 = Z_to_bv 64 0x1330c) by (rewrite (lf_getr_eqv _ _ _ Hx2); reflexivity).
  refine (llvm_free_glue B API FREE ERRNO_LOW stk empty L0 A0 regs0 mem0 md0 ra p n b CTX _ regs2 m2 md' L' A' r bs' s
    (rn_k (skipn 2 pl) + 1) (sb_malloc (sb_malloc b LLVM_REQ) (rn_k (skipn 2 pl) + 1)) 0x1330c
    (lf_cells regs0 j0 (bx_fabric bs) j1' bs jm ip2 ln2) Pk FR3 MINE2 MINEs ltac:(lia) RES2 G1'' _ H2 H4 G10'' CFm eq_refl
    CRm _).
  { apply ret_ok_even. reflexivity. }
  intros L3 A3 regs3 mem3 md3 FR4 MINE3 RES3 Hrp3 CF3x CR3.
  destruct (llvm_md_ok B API _ _ _ _ _ _ _ _ _ _ FR4) as [Hh3 Hl3].
  assert (BASE3 : llvm_regs_base regs0 regs3 r (bx_fabric bs) i) by exact (lf_base_pres _ _ _ _ _ _ BASE2 Hrp3).
  apply (llvm_run (mkFP Fq fcq) regs3 (Z_to_bv 64 0x1330c) mem3 md3
    (fun ms => exists R, ms = MS R Fq (Z_to_bv 64 0x13314) fcq None mem3 (YK11.seg_rom rsegs) /\
       reg_get R 19 = Z_to_bv 64 ((-1) mod 2 ^ 32) /\
       forall x, x = 2 \/ x = 3 \/ x = 4 \/ x = 8 \/ 24 <= x <= 27 -> reg_get R (Z_to_bv 5 x) = reg_get regs3 (Z_to_bv 5 x)));
    [exact Hh3 | exact Hl3 | | |].
  { unfold Regs6ss.mkR_of. step. step.
    apply evt_done. eexists. split; [reflexivity|]. split; [reflexivity|].
    intros x Hxc. destruct Hxc as [->|[->|[->|[->|Hxc]]]]; try reflexivity.
    assert (Hc : x = 24 \/ x = 25 \/ x = 26 \/ x = 27) by lia.
    destruct Hc as [->|[->|[->| ->]]]; reflexivity. }
  { intros ms (R & -> & _). do 5 eexists. reflexivity. }
  intros R F pc' fc m' (R' & HE & H19 & Hcs) regs4 Hx4.
  injection HE as ER EF EP EC EM. subst R F pc' fc m'.
  apply SR_ret. unfold Pk. exists (Datatypes.S k).
  exists (mkFP Fq fcq), regs4, mem3, md3, L3, A3, r, (bx_fabric bs), ip2, ln2, bs, bs', (-1), j0, j1', jm.
  split; [rewrite SEGS; reflexivity|].
  split; [exact Hfc'|].
  split; [exact (lf_base_eqv _ _ _ _ _ _ _ BASE3 Hcs Hx4)|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx4); exact H19|].
  split; [exact CF3x|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact INV|]. split; [reflexivity|].
  split; [exact CR3|]. split; [exact INV'|]. split; [exact Hfab'|]. split; [exact KEPT|].
  split; [split; [exact FR4 | split; [exact MINE3 | exact (llvm_name_back A3 b (rn_k (skipn 2 pl) + 1) RES3)]] | lia].
Qed.

End C0.
