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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import Boxreg BoxregRd BoxregUpd BoxregStep printf_facts_c snprintf_c reac_boxreg_set_name_c strncmp_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog.CF Require Import read_name_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require reac_boxreg_set_name strncmp.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog.CF Require Import LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_exit LLVMFuzzerTestOneInput_res LLVMFuzzerTestOneInput_rn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog.CF Require LLVMFuzzerTestOneInput_entry LLVMFuzzerTestOneInput_case0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog.CF Require Import SRCF.
Import ListNotations.
Open Scope Z_scope.

Lemma llvm_c3_evt1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ip : Z) (pl : list byte),
    0 <= ip -> ip + 1 + Z.of_nat (length pl) <= bv_unsigned sp -> bv_unsigned sp + 344 <= 2 ^ 64 ->
    bytes_at rsegs m (ip + 1) pl ->
    rw_cells rsegs m (bv_unsigned sp + 328) [C8 (Z_to_bv 64 (ip + 1)); C8 (Z_to_bv 64 (Z.of_nat (length pl)))] ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (s1' s5' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x12f00) sp gp tp t0 t1 t2 s0 s1' (Z_to_bv 64 (bv_unsigned sp + 328))
                       a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat (length pl)))
                       (Z_to_bv 64 (CF.LLVMFuzzerTestOneInput_case0.c0_nch pl)) s4 s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x135cc) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp + 328, bv_unsigned sp + 344)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         rw_cells rsegs m' (bv_unsigned sp + 328)
           [C8 (Z_to_bv 64 (ip + 1 + Z.min (Z.of_nat (length pl)) 1));
            C8 (Z_to_bv 64 (Z.of_nat (length pl) - Z.min (Z.of_nat (length pl)) 1))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 ip) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (Z.of_nat (length pl))) s3 s4 (Z_to_bv 64 (1 + Z.of_nat (length pl)))
               s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12e08) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ip pl Hip Hsp Htop HB CW MI.
  pose proof (munch_refl [(bv_unsigned sp + 328, bv_unsigned sp + 344)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  destruct pl as [|v1 rest].
  - change (Z.of_nat (length [])) with 0 in *. change (Z.min 0 1) with 0. change (0 - 0) with 0.
    cbn [CF.LLVMFuzzerTestOneInput_case0.c0_nch] in *. rewrite Z.add_0_r.
    step. if_true. do 3 step.
    finish.
  - replace (Z.of_nat (length (v1 :: rest))) with (1 + Z.of_nat (length rest)) in * by (cbn [length]; lia).
    replace (Z.min (1 + Z.of_nat (length rest)) 1) with 1 by lia.
    replace (1 + Z.of_nat (length rest) - 1) with (Z.of_nat (length rest)) by lia.
    cbn [CF.LLVMFuzzerTestOneInput_case0.c0_nch].
    replace (ip + 1 + 1) with (ip + 2) by lia.
    pose proof (CF.LLVMFuzzerTestOneInput_case0.c0_rd1 _ _ _ _ HB) as R1.
    step. rewrite CF.LLVMFuzzerTestOneInput_case0.c0_ne0 by lia. cbv iota.
    do 6 step. do 2 step.
    finish.
    all: eapply CF.LLVMFuzzerTestOneInput_case0.c0_rw2; [exact CW | word_eq_tac | word_eq_tac].
Qed.

Definition c3_ren (x n : Z) : Z := if (0 <=? x) && (x <? n) then x else -1.

Lemma c3_ren_val : forall x n, -128 <= x < 128 -> 0 <= n <= 5 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned
    (v_slti (Z_to_bv 64 x) 0)) 18446744073709551615))) (bv_unsigned (v_slt (Z_to_bv 64 x) (Z_to_bv 64 n))) + -1)))
    (bv_unsigned (Z_to_bv 64 x))) = Z_to_bv 64 (c3_ren x n).
Proof.
  intros x n Hx Hn. unfold v_slti, v_slt, zsig, c3_ren. rewrite ?bx_signed by lia.
  try unfold c_lts. rewrite ?bx_lts by lia. unfold zsig. rewrite ?bx_signed by lia.
  destruct (Z.ltb_spec x 0) as [H0|H0]; destruct (Z.ltb_spec x n) as [H1|H1]; destruct (Z.leb_spec 0 x) as [H2|H2];
    try lia; cbn [andb].
  - replace (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 1))
      18446744073709551615))) (bv_unsigned (Z_to_bv 64 1)) + -1))) with 18446744073709551615 by reflexivity.
    rewrite CF.LLVMFuzzerTestOneInput_case0.c0_lor1. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
  - replace (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 0))
      18446744073709551615))) (bv_unsigned (Z_to_bv 64 1)) + -1))) with 0 by reflexivity.
    rewrite Z.lor_0_l. apply Z_to_bv_bv_unsigned.
  - replace (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 0))
      18446744073709551615))) (bv_unsigned (Z_to_bv 64 0)) + -1))) with 18446744073709551615 by reflexivity.
    rewrite CF.LLVMFuzzerTestOneInput_case0.c0_lor1. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
Qed.

Lemma c3_mod32 : forall z, (z mod (2 ^ 32 * 2 ^ 32)) mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
  intros z. rewrite Z.rem_mul_r by lia.
  rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.

Lemma c3_low32 : forall z : Z,
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 z)) 32))) 32) =
  Z_to_bv 64 (z mod 2 ^ 32).
Proof.
  intros z. f_equal. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 32 * 2 ^ 32).
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  set (u := z mod (2 ^ 32 * 2 ^ 32)).
  assert (Hu : 0 <= u < 2 ^ 32 * 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  rewrite (Z.div_mod u (2 ^ 32)) at 1 by lia.
  replace ((2 ^ 32 * (u / 2 ^ 32) + u mod 2 ^ 32) * 2 ^ 32)
    with (u mod 2 ^ 32 * 2 ^ 32 + (u / 2 ^ 32) * (2 ^ 32 * 2 ^ 32)) by ring.
  rewrite Z.mod_add by lia.
  rewrite Z.mod_small by (pose proof (Z.mod_pos_bound u (2 ^ 32) ltac:(lia)); nia).
  rewrite Z.div_mul by lia. unfold u. apply c3_mod32.
Qed.

Lemma c3_used_split : forall pl : list byte, Z.of_nat (length (firstn 1 pl)) = Z.min (Z.of_nat (length pl)) 1.
Proof. intros pl. rewrite length_firstn. lia. Qed.

Lemma c3_skip_len : forall pl : list byte,
  Z.of_nat (length (skipn 1 pl)) = Z.of_nat (length pl) - Z.min (Z.of_nat (length pl)) 1.
Proof. intros pl. rewrite length_skipn. lia. Qed.

Lemma nu_len : forall bs X idx, length bs = 288%nat -> length X = 32%nat -> 0 <= idx <= 4 ->
  length (upd_bytes bs (Z.to_nat (56 * idx + 24)) X) = 288%nat.
Proof. intros bs X idx HL HX Hi. rewrite upd_bytes_length; [exact HL | lia]. Qed.

Lemma nu_bsub : forall bs X idx a w, length bs = 288%nat -> length X = 32%nat -> 0 <= idx <= 4 ->
  0 <= a -> 0 <= w -> a + w <= 288 -> (a + w <= 56 * idx + 24 \/ 56 * idx + 56 <= a) ->
  bsub (upd_bytes bs (Z.to_nat (56 * idx + 24)) X) a w = bsub bs a w.
Proof. intros bs X idx a w HL HX Hi Ha Hw Haw Hd. apply bsub_upd_out; rewrite ?HL, ?HX; lia. Qed.

Lemma nu_rd4 : forall bs X idx a, length bs = 288%nat -> length X = 32%nat -> 0 <= idx <= 4 ->
  0 <= a -> a + 4 <= 288 -> (a + 4 <= 56 * idx + 24 \/ 56 * idx + 56 <= a) ->
  rd4 (upd_bytes bs (Z.to_nat (56 * idx + 24)) X) a = rd4 bs a.
Proof. intros bs X idx a HL HX Hi Ha Haw Hd. unfold rd4. rewrite nu_bsub by (assumption || lia). reflexivity. Qed.

Lemma nu_name : forall bs X idx, length bs = 288%nat -> length X = 32%nat -> 0 <= idx <= 4 ->
  bsub (upd_bytes bs (Z.to_nat (56 * idx + 24)) X) (56 * idx + 24) 32 = X.
Proof.
  intros bs X idx HL HX Hi.
  pose proof (bsub_upd_in bs (Z.to_nat (56 * idx + 24)) X 0 32 ltac:(lia) ltac:(lia) ltac:(rewrite HL, HX; lia)
    ltac:(rewrite HX; lia)) as E.
  rewrite Z2Nat.id, Z.add_0_r in E by lia. rewrite E. unfold bsub. change (Z.to_nat 0) with 0%nat.
  rewrite skipn_O. apply firstn_all2. rewrite HX. lia.
Qed.

Lemma nu_inv : forall bs X idx, boxreg_inv bs -> 0 <= idx < bx_n bs -> length X = 32%nat -> In (Z_to_bv 8 0) X ->
  boxreg_inv (upd_bytes bs (Z.to_nat (56 * idx + 24)) X) /\
  bx_fabric (upd_bytes bs (Z.to_nat (56 * idx + 24)) X) = bx_fabric bs /\
  llvm_kept bs (upd_bytes bs (Z.to_nat (56 * idx + 24)) X) idx.
Proof.
  intros bs X idx [[HL [H1 [H2 [H3 [H4 [H5 H6]]]]]] H7] Hi HX H0. unfold boxreg_B1 in H1.
  assert (Hi4 : 0 <= idx <= 4) by lia.
  set (bs' := upd_bytes bs (Z.to_nat (56 * idx + 24)) X).
  assert (En : bx_n bs' = bx_n bs) by (unfold bx_n, bs'; apply nu_rd4; lia).
  assert (Ef : bx_fabric bs' = bx_fabric bs) by (unfold bx_fabric, bs'; apply nu_rd4; lia).
  assert (Erow : forall j o, 0 <= j < 5 -> 0 <= o -> o + 4 <= 24 -> rd4 bs' (56 * j + o) = rd4 bs (56 * j + o))
    by (intros j o Hj Ho Hoo; unfold bs'; apply nu_rd4; lia).
  assert (Emac : forall j, 0 <= j < 5 -> bx_mac bs' j = bx_mac bs j)
    by (intros j Hj; unfold bx_mac, bs'; apply nu_bsub; lia).
  assert (Ename : forall j, 0 <= j < 5 -> j <> idx -> bx_name bs' j = bx_name bs j)
    by (intros j Hj Hne; unfold bx_name, bs'; apply nu_bsub; lia).
  split; [|split; [exact Ef|]].
  - split; [split; [unfold bs'; apply nu_len; lia|] |].
    + split; [unfold boxreg_B1; rewrite En; lia|].
      split; [unfold boxreg_B2 in *; rewrite Ef; exact H2|].
      split; [intros j Hj; rewrite En in Hj; unfold bx_nch, bx_base; rewrite !Erow by lia; rewrite Ef; exact (H3 j Hj)|].
      split; [intros j1 j2 Hj1 Hj Hj2; rewrite En in Hj2; unfold bx_base, bx_nch; rewrite !Erow by lia;
              exact (H4 j1 j2 Hj1 Hj Hj2)|].
      split; [intros j1 j2 Hj1 Hj Hj2; rewrite En in Hj2; rewrite !Emac by lia; exact (H5 j1 j2 Hj1 Hj Hj2)|].
      intros j Hj. rewrite En in Hj. destruct (Z.eq_dec j idx) as [->|Hne].
      * unfold bx_name, bs'. rewrite nu_name by lia. exact H0.
      * rewrite Ename by lia. exact (H6 j Hj).
    + intros j Hj. rewrite En in Hj. unfold bx_pinned, bx_established. rewrite !Erow by lia. exact (H7 j Hj).
  - intros j Hj. unfold bx_base, bx_nch, bx_pinned. rewrite !Erow by lia.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [right; apply Emac; lia|].
    destruct (Z.eq_dec j idx) as [->|Hne]; [left; reflexivity | right; apply Ename; lia].
Qed.

Lemma nu_mem : forall m m' r bs X idx lo hi, bytes_at rsegs m r bs -> length bs = 288%nat -> length X = 32%nat ->
  0 <= idx <= 4 -> munch [(lo, hi); (r + 56 * idx + 24, r + 56 * idx + 56)] m m' -> (r + 288 <= lo \/ hi <= r) ->
  bytes_at rsegs m' (r + 56 * idx + 24) X -> bytes_at rsegs m' r (upd_bytes bs (Z.to_nat (56 * idx + 24)) X).
Proof.
  intros m m' r bs X idx lo hi (H0 & H1 & HB) HL HX Hi MU Hd (G0 & G1 & GB).
  rewrite HL in H1. rewrite HX in G1.
  split; [lia|]. rewrite nu_len by assumption. split; [lia|].
  intros i Hi'. rewrite upd_bytes_nth by (rewrite ?HL, ?HX; lia). rewrite HX.
  destruct (Nat.leb_spec (Z.to_nat (56 * idx + 24)) i) as [Ha|Ha];
    destruct (Nat.ltb_spec i (Z.to_nat (56 * idx + 24) + 32)) as [Hb|Hb]; cbn [andb].
  - replace (r + Z.of_nat i) with (r + 56 * idx + 24 + Z.of_nat (i - Z.to_nat (56 * idx + 24))) by lia.
    apply GB. lia.
  - rewrite <- (HB i ltac:(lia)). unfold mrd. rewrite (MU (wa (r + Z.of_nat i))); [reflexivity|].
    cbn [outside]. rewrite wa_unsigned by lia. lia.
  - rewrite <- (HB i ltac:(lia)). unfold mrd. rewrite (MU (wa (r + Z.of_nat i))); [reflexivity|].
    cbn [outside]. rewrite wa_unsigned by lia. lia.
  - rewrite <- (HB i ltac:(lia)). unfold mrd. rewrite (MU (wa (r + Z.of_nat i))); [reflexivity|].
    cbn [outside]. rewrite wa_unsigned by lia. lia.
Qed.

Lemma nu_last : forall l : list Z,
  (0 < length (pf_bytes (l ++ [0%Z])))%nat /\
  nth_error (pf_bytes (l ++ [0])) (length (pf_bytes (l ++ [0])) - 1) = Some (Z_to_bv 8 0).
Proof.
  intros l. unfold pf_bytes. rewrite map_app, length_app. cbn [map length].
  split; [lia|]. rewrite nth_error_app2 by lia. replace (length (map (Z_to_bv 8) l) + 1 - 1 - length (map (Z_to_bv 8) l))%nat
    with 0%nat by lia. reflexivity.
Qed.

Lemma nu_window : forall m D P, (forall i, 0 <= i < 32 -> exists v, mrd rsegs m (wa (D + i)) = Some v) ->
  0 <= D -> D + 32 <= 2 ^ 64 -> bytes_at rsegs m D P -> (0 < length P <= 32)%nat ->
  nth_error P (length P - 1) = Some (Z_to_bv 8 0) ->
  exists X, bytes_at rsegs m D X /\ length X = 32%nat /\ In (Z_to_bv 8 0) X.
Proof.
  intros m D P HR HD HD2 HP HLP Hlast.
  destruct (nm_collect m D 32 HD ltac:(lia) HR) as (X & HX & LX).
  exists X. split; [exact HX|]. split; [exact LX|].
  destruct HX as (_ & _ & GX). destruct HP as (_ & _ & GP).
  pose proof (GX (length P - 1)%nat ltac:(lia)) as E1. pose proof (GP (length P - 1)%nat ltac:(lia)) as E2.
  rewrite E2, Hlast in E1. symmetry in E1. exact (nth_error_In _ _ E1).
Qed.

Lemma nu_rd : forall m A n, (forall i, 0 <= i < n -> find_segment rsegs (A + i) 1 = None) -> wr_at rsegs m A n ->
  forall i, 0 <= i < n -> exists v, mrd rsegs m (wa (A + i)) = Some v.
Proof.
  intros m A n HN (H0 & H1 & HW) i Hi. pose proof (HW i Hi) as W. unfold wview in W.
  destruct (m (wa (A + i))) as [v|] eqn:E; [exists v; unfold mrd; rewrite E; reflexivity|].
  exfalso. apply W. rewrite wa_unsigned by lia. rewrite (HN i Hi). reflexivity.
Qed.

Definition c3_q2 (sp gp tp s0 s8 s9 s10 s11 : word) (lo r fab nm : Z) (bs : list byte)
    (m0 : word -> option byte) (ms' : machine_state) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
         (m' : word -> option byte) (bs' : list byte) (ren : Z),
    ms' = MS (mkR (Z_to_bv 64 0x12f7c) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 ren) (Z_to_bv 64 nm) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (Z_to_bv 64 0x14648) fc' None m' (seg_rom rsegs) /\
    FP.frm0 fc' /\
    munch [(lo, bv_unsigned sp); (r, r + 288)] m0 m' /\ wmono rsegs m0 m' /\
    bytes_at rsegs m' r bs' /\ wr_at rsegs m' r 288 /\
    boxreg_inv bs' /\ bx_fabric bs' = fab /\ llvm_kept bs bs' ren /\ -1 <= ren < bx_n bs.

Lemma llvm_c3_k12f00 :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s8 s9 s10 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (lo r ix op nm nl : Z) (bs NB slack : list byte) (s : list Z) (canary : word),
    reac_boxreg_set_name_contract -> strncmp_contract ->
    0 <= ix < 256 -> 0 <= op < 256 ->
    boxreg_inv bs -> pf_img_free r 288 -> (forall i, 0 <= i < 288 -> find_segment rsegs (r + i) 1 = None) ->
    rw_cells rsegs m r [CB 288 bs] ->
    stk rsegs m lo (bv_unsigned sp) -> 0x50000 <= lo -> lo + 6000 <= bv_unsigned sp -> bv_unsigned sp + 448 <= 2 ^ 47 ->
    4096 <= r -> r + 288 <= lo ->
    0 < nm -> Forall (fun c => 0 < c < 256) s -> Z.of_nat (length s) < 2 ^ 31 - 1 ->
    bytes_at rsegs m nm NB -> NB = pf_bytes (s ++ [0]) ++ slack -> Z.of_nat (length NB) = nl ->
    (- (nm + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack) ->
    nm + nl <= lo -> (nm + nl <= r \/ r + 288 <= nm) ->
    mem_inv rsegs m -> MemNorm.task_mem rsegs m -> FP.frm0 fc ->
    bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
    evt rsegs (c3_q2 sp gp tp (Z_to_bv 64 r) s8 s9 s10 (Z_to_bv 64 (bx_fabric bs)) lo r (bx_fabric bs) nm bs m)
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 r) s1 (Z_to_bv 64 nm) a1 a2 a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 ix) s4 s5 (Z_to_bv 64 op) (Z_to_bv 64 (bx_n bs))
               s8 s9 s10 (Z_to_bv 64 (bx_fabric bs)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x12f00) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s8 s9 s10 t3 t4 t5 t6 F fc m lo r ix op nm nl
    bs NB slack s canary SNC SC Hix Hop INV HIF HNS CR ST Hlo HLO HSP Hr4 HRL Hnm Hsok Hslen HNB HNBe HNBl Hmod Hnlo
    Hnr MI TM Hfc HG1 HG2.
  unfold reac_boxreg_set_name_contract in SNC. unfold GOT_GUARD, GUARD in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof (nm_len s slack) as HNL. rewrite <- HNBe, HNBl in HNL.
  pose proof INV as ((HL & HB1 & HB2 & _) & _).
  pose proof CR as [[_ HBr0] HWR0]. cbn [cells_bytes cbytes] in HBr0. rewrite app_nil_r in HBr0.
  change (Z.of_nat (cells_size _)) with 288 in HWR0.
  pose proof (munch_refl [(lo, bv_unsigned sp); (r, r + 288)] m) as MU0. pose proof (wmono_refl rsegs m) as WM0.
  do 10 step. rewrite CF.LLVMFuzzerTestOneInput_case0.c0_given by lia. rewrite CF.LLVMFuzzerTestOneInput_entry.en_sext by lia.
  assert (HNA : name_ok m (bv_unsigned sp) lo r (if Z.land op 8 =? 0 then nm else 0)
                  (if Z.land op 8 =? 0 then s else []))
    by (destruct (Z.land op 8 =? 0);
        [ right; split; [lia|]; split; [exact Hsok|]; split; [exact Hslen|]; exists slack; rewrite <- HNBe;
          split; [exact HNB|]; split; [exact Hmod|]; split; lia
        | left; split; reflexivity ]).
  eapply evt_cut.
  { eapply SNC with (lo := lo) (r := r) (idx := CF.LLVMFuzzerTestOneInput_entry.en_sx ix)
      (q := if Z.land op 8 =? 0 then nm else 0) (bs := bs) (canary := canary) (s := if Z.land op 8 =? 0 then s else []);
      first [ reflexivity | exact HNA | exact HB1 | assumption | unfold SNPRINTF_K; lia | unfold IMG_END; lia
            | unfold CF.LLVMFuzzerTestOneInput_entry.en_sx; destruct (ix <? 128); lia
            | destruct (Z.land op 8 =? 0); lia ]. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m'
    & E & MUc & WMc & MI2 & TM2 & Hfc' & FK & ST2 & RES).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x12f28)) with (Z_to_bv 64 0x12f28) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof INV as ((_ & HB1u & _) & _). unfold boxreg_B1 in HB1u.
  rewrite (unsigned_lit op) by lia.
  destruct (CF.LLVMFuzzerTestOneInput_case0.c0_op8 op) as [E8|E8]; rewrite E8 in RES |- *; cbn [Z.eqb] in RES |- *.
  all: set (idx := CF.LLVMFuzzerTestOneInput_entry.en_sx ix) in *.
  all: assert (Hidxr : -128 <= idx < 128)
         by (unfold idx, CF.LLVMFuzzerTestOneInput_entry.en_sx; destruct (Z.ltb_spec ix 128); lia).
  all: case_eq ((idx <? 0) || (bx_n bs <=? idx)); intros Ev; rewrite Ev in RES.
  1: (destruct RES as (-> & -> & ->); clear MUc WMc; do 6 step; rewrite c3_ren_val by lia;
        replace (c3_ren idx (bx_n bs)) with (-1)
          by (unfold c3_ren; apply orb_true_iff in Ev; destruct Ev as [Ev|Ev];
              [apply Z.ltb_lt in Ev | apply Z.leb_le in Ev];
              destruct ((0 <=? idx) && (idx <? bx_n bs)) eqn:E2; try reflexivity;
              apply andb_true_iff in E2; destruct E2 as [E2a E2b]; apply Z.leb_le in E2a; apply Z.ltb_lt in E2b;
              lia);
        step; if_true; step; step; finish;
        try solve [ eassumption | apply CF.LLVMFuzzerTestOneInput_case0.c0_kept_refl | reflexivity | lia ]).
  2: (destruct RES as (-> & -> & ->); clear MUc WMc; do 6 step; rewrite c3_ren_val by lia;
        replace (c3_ren idx (bx_n bs)) with (-1)
          by (unfold c3_ren; apply orb_true_iff in Ev; destruct Ev as [Ev|Ev];
              [apply Z.ltb_lt in Ev | apply Z.leb_le in Ev];
              destruct ((0 <=? idx) && (idx <? bx_n bs)) eqn:E2; try reflexivity;
              apply andb_true_iff in E2; destruct E2 as [E2a E2b]; apply Z.leb_le in E2a; apply Z.ltb_lt in E2b;
              lia);
        step; if_true; step; step; finish;
        try solve [ eassumption | apply CF.LLVMFuzzerTestOneInput_case0.c0_kept_refl | reflexivity | lia ]).
  all: destruct (proj1 (orb_false_iff _ _) Ev) as [Ev1 Ev2]; apply Z.ltb_ge in Ev1; apply Z.leb_gt in Ev2.
  all: pose proof (wr_at_transport rsegs m m' r 288 HWR0 WMc) as HWR'.
  all: assert (HRD : forall i, 0 <= i < 32 -> exists v, mrd rsegs m' (wa (r + 56 * idx + 24 + i)) = Some v)
         by (intros i Hi; pose proof (nu_rd m' r 288 HNS HWR' (56 * idx + 24 + i) ltac:(lia)) as H;
             replace (r + (56 * idx + 24 + i)) with (r + 56 * idx + 24 + i) in H by lia; exact H).
  all: lazymatch type of RES with bytes_at _ _ _ (pf_bytes (firstn 31 ?sx ++ [0])) =>
         pose proof (nu_last (firstn 31 sx)) as [HLP1 HLP2];
         assert (HLP3 : (length (pf_bytes (firstn 31 sx ++ [0%Z])) <= 32)%nat)
           by (unfold pf_bytes; rewrite length_map, length_app, length_firstn; cbn [length]; lia) end.
  all: destruct (nu_window m' (r + 56 * idx + 24) _ HRD ltac:(lia) ltac:(lia) RES ltac:(lia) HLP2) as (X & HX & LX & HX0).
  all: pose proof (nu_mem m m' r bs X idx lo (bv_unsigned sp) HBr0 HL LX ltac:(lia) MUc ltac:(lia) HX) as HBr'.
  all: destruct (nu_inv bs X idx INV ltac:(lia) LX HX0) as (INV' & Hfab' & KEPT').
  all: lazymatch type of MUc with munch _ ?mm ?mm' => transport_after_call rsegs mm mm' MUc WMc end.
  all: clear MUc WMc.
  all: do 6 step; rewrite c3_ren_val by lia.
  all: replace (c3_ren idx (bx_n bs)) with idx
         by (unfold c3_ren; replace ((0 <=? idx) && (idx <? bx_n bs)) with true
               by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia); reflexivity).
  all: step; rewrite bx_lts by lia; replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia); cbv iota.
  all: step; step.
  all: first [if_true | if_false; step; step].
  all: do 3 step; rewrite bx_off56 by lia; do 4 step.
  all: unfold strncmp_contract in SC.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply SC with (v := 0);
      [ match goal with |- bytes_at _ _ ?a _ =>
          replace a with (r + 56 * idx + 24) by (rewrite ?unsigned_lit by lia; lia) end; exact RES
      | match goal with |- bytes_at _ _ ?a _ =>
          first [ replace a with nm by (rewrite ?unsigned_lit by lia; lia); exact HNB
                | replace a with 66253 by (rewrite ?unsigned_lit by lia; lia);
                  exact (CF.LLVMFuzzerTestOneInput_case0.c0_empty_at _ ltac:(eassumption)) ]
        end
      | first [rewrite HNBe; exact (nm_strncmp_set s slack Hsok) | exact (nm_strncmp_set [] [] (Forall_nil _))]
      | assumption ]
    | post_call rsegs mm ] end.
  all: step; if_false; step; step.
  all: finish.
  all: first [ eassumption | exact INV' | exact Hfab' | exact KEPT' | lia ].
Qed.

Section C3.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis MALLOC : forall fx' : YK11.FPState, @malloc_contract fx' rc B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= YM05.alloc_ceiling.
Hypothesis SLACK : block_slack_present B API.
Hypothesis SNPRINTF : snprintf_contract.

Theorem llvm_case3_ok : llvm_case_ok B API 3.
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n b i k c CTX HT HPC.
  match goal with |- SR _ _ ?Q => set (Pk := Q) end.
  destruct HT as (fx' & regs & mem & md & L & A & r & fab & ip & inn & bs & op & j0 & j1 & jm & Ec & Hfrm & RB & E9 & E18
    & E19 & E21 & E22 & E23 & FRC & Hi & Hinn & Hpip & Hipn & Hop & RWR & INV & Hfab & AL & Hk).
  assert (Epc : Z_to_bv 64 (llvm_case_pc (Z.land op 3)) = Z_to_bv 64 0x12e08).
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
  assert (HIF : pf_img_free r 288).
  { intros j Hj sg Hsg. destruct (lf_mine_bytes B API AX L0 A0 L A mem md r 288 (r + j) HM MINE ltac:(lia))
      as (_ & Hn' & _). exact (lf_not_img_res B (r + j) SEGS Hn' sg Hsg). }
  assert (HNS : forall j, 0 <= j < 288 -> find_segment rsegs (r + j) 1 = None).
  { intros j Hj. destruct (lf_mine_bytes B API AX L0 A0 L A mem md r 288 (r + j) HM MINE ltac:(lia)) as (_ & Hn' & _).
    destruct (find_segment rsegs (r + j) 1) as [sg|] eqn:F; [|reflexivity].
    exfalso. exact (Hn' (lf_find_img B (r + j) sg SEGS F)). }
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
  eapply (llvm_run_norm fx' regs (Z_to_bv 64 0x12e08) mem md); [exact Hh | exact Hl | exact Hro | | |].
  { unfold Regs6ss.mkR_of.
    assert (R9 : reg_get regs 9 = Z_to_bv 64 ip) by exact E9.
    assert (R18 : reg_get regs 18 = Z_to_bv 64 (Z.of_nat (length pl))) by (rewrite Hlen; exact E18).
    assert (R21 : reg_get regs 21 = Z_to_bv 64 (1 + Z.of_nat (length pl)))
      by (rewrite Hlen; replace (1 + (inn - 1)) with inn by lia; exact E21).
    rewrite R9, R18, R21.
    eapply llvm_c3_evt1 with (s1 := Z_to_bv 64 0) (s2 := Z_to_bv 64 0) (s5 := Z_to_bv 64 0).
    - lia.
    - rewrite Esp. lia.
    - rewrite Esp. lia.
    - exact HPLn.
    - rewrite Esp. exact CF3n.
    - exact (mem_inv_normalize rsegs mem). }
  { intros ms (s1' & s5' & m'' & -> & _). do 5 eexists. reflexivity. }
  intros R F pc' fc m0' (s1' & s5' & m'' & HE & MU & WM & MI' & CW') regs1 m1 Hx Hrel Hsame.
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
    [C8 (Z_to_bv 64 (ip + 1 + Z.min (Z.of_nat (length pl)) 1)); C8 (Z_to_bv 64 (Z.of_nat (length (skipn 1 pl))))]).
  { pose proof (lf_rw_cells_rel m1 m'' _ _ Hrel CW') as H. rewrite Esp, <- c3_skip_len in H. exact H. }
  assert (RWR1 : rw_cells rsegs m1 r [CB 288 bs]).
  { apply (rw_cells_transport rsegs _ mem m1 _ _ RWR MU' WM'). change (Z.of_nat (cells_size _)) with 288.
    cbn [disjoint_from]. split; [lia | exact I]. }
  assert (HPL1 : bytes_at rsegs m1 (ip + 1 + Z.min (Z.of_nat (length pl)) 1) (skipn 1 pl)).
  { pose proof (bytes_at_transport rsegs _ mem m1 _ _ HPL MU' ltac:(cbn [disjoint_from]; split; [lia | exact I])) as H.
    rewrite <- (firstn_skipn 1 pl) in H. apply (proj1 (bytes_at_app rsegs m1 _ _ _)) in H. destruct H as [_ H].
    rewrite c3_used_split in H. exact H. }
  assert (G1' : YK11.getr regs1 1 = Z_to_bv 64 0x12f00) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
  assert (G2' : YK11.getr regs1 2 = Z_to_bv 64 (S - 448)) by (rewrite (lf_getr_eqv _ _ _ Hx); exact E2).
  assert (G4' : YK11.getr regs1 4 = YK11.getr regs0 4) by (rewrite (lf_getr_eqv _ _ _ Hx); exact E4).
  assert (G10' : YK11.getr regs1 10 = Z_to_bv 64 (S - 448 + 328)).
  { rewrite (lf_getr_eqv _ _ _ Hx).
    change (Z_to_bv 64 (bv_unsigned (reg_get regs 2) + 328) = Z_to_bv 64 (S - 448 + 328)). rewrite Esp. reflexivity. }
  assert (BASE1 : llvm_regs_base regs0 regs1 r (bx_fabric bs) i)
    by (unfold llvm_regs_base; rewrite !(lf_getr_eqv _ _ _ Hx); exact BASE0).
  pose proof (rn_k_range (skipn 1 pl)) as Hkr.
  pose proof (c3_skip_len pl) as Hsk.
  assert (ROOM : room_ag (sb_malloc b LLVM_REQ) (rn_k (skipn 1 pl) + 1)).
  { exact (llvm_name_room B API stk empty L0 A0 regs0 mem0 md0 ra p n b (rn_k (skipn 1 pl) + 1) CTX
      ltac:(unfold LLVM_REQ; lia)). }
  refine (llvm_rn_glue B API MALLOC ERRNO_LOW stk empty L0 A0 regs0 mem0 md0 ra p n b CTX _ regs1 m1 md L A r bs
    (sb_malloc b LLVM_REQ) 0x12f00 j0 (bx_fabric bs) j1 bs jm (ip + 1 + Z.min (Z.of_nat (length pl)) 1) (skipn 1 pl) Pk
    Hn0 FR1 MINE RES ROOM G1' _ G2' G4' G10' _ RWR1 HPL1 _ _ _).
  { apply ret_ok_even. reflexivity. }
  { apply (proj2 (lf_cells_split m1 (S - 448) regs0 j0 (bx_fabric bs) j1 bs jm _ _)). auto. }
  { lia. }
  { lia. }
  intros L' A' regs' mem' md' s FR2 MINE2 MINEs Hsr RES2 Hrp G10s HBs CF2x CR2.
  set (ip2 := ip + 1 + Z.min (Z.of_nat (length pl)) 1 + Z.min (Z.of_nat (length (skipn 1 pl))) 1 + rn_k (skipn 1 pl))
    in *.
  set (ln2 := Z.of_nat (length (skipn 1 pl)) - Z.min (Z.of_nat (length (skipn 1 pl))) 1 - rn_k (skipn 1 pl)) in *.
  assert (Hip2 : ip2 + ln2 = p + n /\ 0 <= ln2 /\ p <= ip2) by (unfold ip2, ln2; lia).
  pose proof FR2 as (HM2 & HW2 & HB2 & HID2 & Hmd2 & Hhigh2 & Himg2 & Hblk2 & Hbyt2 & Hstw2 & Herr2 & Hgd2 & Hro2).
  destruct (llvm_md_ok B API _ _ _ _ _ _ _ _ _ _ FR2) as [Hh2 Hl2].
  pose proof MINEs as (Hsin & Hs0' & Hsd).
  destruct (lf_mine_bytes B API AX L0 A0 L' A' mem' md' s (rn_k (skipn 1 pl) + 1) s HM2 MINEs ltac:(lia))
    as (_ & _ & Hs1 & _).
  destruct (lf_mine_bytes B API AX L0 A0 L' A' mem' md' s (rn_k (skipn 1 pl) + 1) (s + rn_k (skipn 1 pl)) HM2 MINEs
    ltac:(lia)) as (_ & _ & Hs2 & _).
  destruct (llvm_name_parts B API SLACK L' A' mem' md' s (rn_k (skipn 1 pl)) (bsub (skipn 1 pl) 1 (rn_k (skipn 1 pl)))
    HM2 Hsin ltac:(lia) ltac:(lia) ltac:(lia) HBs (rn_name_len (skipn 1 pl))) as (slack & HNB & Hstrl & Hmod & Hnl).
  set (nmstr := nm_str (bsub (skipn 1 pl) 1 (rn_k (skipn 1 pl)) ++ [Z_to_bv 8 0])) in *.
  destruct (llvm_guards B API stk empty L0 A0 regs0 mem0 md0 ra p n b L' A' mem' md' CTX HM2) as (HG1 & cn & HG2).
  pose proof (nm_len nmstr slack) as HNL.
  assert (HE8 : 8 * ((s + rn_k (skipn 1 pl) + 1 + 7) / 8) <= YM05.alloc_ceiling)
    by (apply nm_up8; [lia | Z.div_mod_to_equations; lia]).
  assert (Hnr' : s + Z.of_nat (length (pf_bytes (nmstr ++ [0]) ++ slack)) <= r \/ r + 288 <= s).
  { destruct Hsr as [Hsr|Hsr]; [left | right; lia].
    assert (Hr16 : r mod 16 = 0).
    { pose proof Hrin as Hq. apply blocks_In in Hq as (q & Hq & Hqin). rewrite <- Hq.
      exact (mr_blocks_aligned B _ (aa_laws API) L A mem md q 288 HM Hqin). }
    pose proof (nm_up8 (s + rn_k (skipn 1 pl) + 1) r ltac:(lia) ltac:(Z.div_mod_to_equations; lia)). lia. }
  assert (BASE' : llvm_regs_base regs0 regs' r (bx_fabric bs) i) by exact (lf_base_pres _ _ _ _ _ _ BASE1 Hrp).
  pose proof BASE' as (F2 & F3 & F4 & F8 & F24 & F25 & F26 & F27).
  assert (Esp' : bv_unsigned (reg_get regs' 2) = S - 448) by (change (bv_unsigned (YK11.getr regs' 2) = S - 448);
    rewrite F2; apply unsigned_lit; lia).
  assert (R19 : reg_get regs' 19 = Z_to_bv 64 (CF.LLVMFuzzerTestOneInput_case0.c0_nch pl)).
  { change (YK11.getr regs' (Z_to_bv 5 19) = Z_to_bv 64 (CF.LLVMFuzzerTestOneInput_case0.c0_nch pl)).
    rewrite (Hrp 19 ltac:(unfold callee_saved; lia)), (lf_getr_eqv _ _ _ Hx). reflexivity. }
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
  set (M := MemNorm.normalize_cj rsegs mem').
  assert (CRM : rw_cells rsegs M r [CB 288 bs]).
  { apply (nm_rw_cj B); [exact SEGS | exact Hro2 | exact CR2 | |].
    - intros x Hxw. change (Z.of_nat (cells_size _)) with 288 in Hxw.
      destruct (lf_mine_bytes B API AX L0 A0 L' A' mem' md' r 288 (r + x) HM2 MINE2 ltac:(lia)) as (_ & N & _).
      exact N.
    - change (Z.of_nat (cells_size _)) with 288. unfold TASK_SIZE. lia. }
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
  eapply (llvm_run_norm_cj (mkFP (@fp_regs fx') (@fp_csr fx')) regs' (Z_to_bv 64 0x12f00) mem' md');
    [exact Hh2 | exact Hl2 | exact Hro2 | | |].
  { unfold Regs6ss.mkR_of. rewrite R8, R10, R19, R22, R23, R27. fold M.
    eapply llvm_c3_k12f00 with (lo := S - stk) (r := r) (ix := CF.LLVMFuzzerTestOneInput_case0.c0_nch pl) (op := op)
      (nm := s) (bs := bs) (NB := pf_bytes (nmstr ++ [0]) ++ slack) (slack := slack) (s := nmstr) (canary := cn)
      (nl := Z.of_nat (length (pf_bytes (nmstr ++ [0]) ++ slack)));
      first [ exact (reac_boxreg_set_name.reac_boxreg_set_name_holds SNPRINTF) | exact strncmp.strncmp_holds
            | apply CF.LLVMFuzzerTestOneInput_case0.c0_nch_range | apply nm_str_ok | exact Hfrm | assumption
            | reflexivity | lia ]. }
  { intros ms HQ.
    destruct HQ as (t0q & t1q & t2q & a1q & a2q & a3q & a4q & a5q & a6q & a7q & s2q & s3q & s4q & s5q & s6q & s7q
      & t3q & t4q & t5q & t6q & Fq & fcq & mq & bsq & renq & -> & _).
    do 5 eexists. reflexivity. }
  intros R F pc' fc m0' HQ regs2 m2 Hx2 Hrel2 Hsame2.
  destruct HQ as (t0q & t1q & t2q & a1q & a2q & a3q & a4q & a5q & a6q & a7q & s2q & s3q & s4q & s5q & s6q & s7q
    & t3q & t4q & t5q & t6q & Fq & fcq & mq & bs' & ren & HE & Hfc' & MU2 & WM2 & HBr & HWr & INV' & Hfab' & KEPT & Hren).
  injection HE as ER EF EP EC EM. subst R F pc' fc m0'.
  pose proof (MemNorm.mem_rel_cj_normalize rsegs mem' Hro2) as HRn.
  assert (MU2' : munch [(S - stk, S - 448); (r, r + 288)] mem' m2).
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
  assert (CFm : rw_cells rsegs m2 (S - 448) (lf_cells regs0 j0 (bx_fabric bs) j1 bs jm ip2 ln2)).
  { apply (rw_cells_transport rsegs _ mem' m2 _ _ CF2x MU2' WM2').
    change (Z.of_nat (cells_size (lf_cells regs0 j0 (bx_fabric bs) j1 bs jm ip2 ln2))) with 448.
    cbn [disjoint_from]. repeat split; lia. }
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
  assert (G1'' : YK11.getr regs2 1 = Z_to_bv 64 0x12f7c) by (rewrite (lf_getr_eqv _ _ _ Hx2); reflexivity).
  refine (llvm_free_glue B API FREE ERRNO_LOW stk empty L0 A0 regs0 mem0 md0 ra p n b CTX _ regs2 m2 md' L' A' r bs' s
    (rn_k (skipn 1 pl) + 1) (sb_malloc (sb_malloc b LLVM_REQ) (rn_k (skipn 1 pl) + 1)) 0x12f7c
    (lf_cells regs0 j0 (bx_fabric bs) j1 bs jm ip2 ln2) Pk FR3 MINE2 MINEs ltac:(lia) RES2 G1'' _ H2 H4 G10'' CFm eq_refl
    CRm _).
  { apply ret_ok_even. reflexivity. }
  intros L3 A3 regs3 mem3 md3 FR4 MINE3 RES3 Hrp3 CF3x CR3.
  destruct (llvm_md_ok B API _ _ _ _ _ _ _ _ _ _ FR4) as [Hh3 Hl3].
  assert (BASE3 : llvm_regs_base regs0 regs3 r (bx_fabric bs) i) by exact (lf_base_pres _ _ _ _ _ _ BASE2 Hrp3).
  assert (R9' : reg_get regs3 9 = Z_to_bv 64 ren).
  { change (YK11.getr regs3 (Z_to_bv 5 9) = Z_to_bv 64 ren).
    rewrite (Hrp3 9 ltac:(unfold callee_saved; lia)), (lf_getr_eqv _ _ _ Hx2). reflexivity. }
  apply (llvm_run (mkFP Fq fcq) regs3 (Z_to_bv 64 0x12f7c) mem3 md3
    (fun ms => exists R, ms = MS R Fq (Z_to_bv 64 0x13314) fcq None mem3 (YK11.seg_rom rsegs) /\
       reg_get R 19 = Z_to_bv 64 (ren mod 2 ^ 32) /\
       forall x, x = 2 \/ x = 3 \/ x = 4 \/ x = 8 \/ 24 <= x <= 27 -> reg_get R (Z_to_bv 5 x) = reg_get regs3 (Z_to_bv 5 x)));
    [exact Hh3 | exact Hl3 | | |].
  { unfold Regs6ss.mkR_of. rewrite R9'. step. step. step.
    apply evt_done. eexists. split; [reflexivity|]. split; [apply c3_low32|].
    intros x Hxc. destruct Hxc as [->|[->|[->|[->|Hxc]]]]; try reflexivity.
    assert (Hc : x = 24 \/ x = 25 \/ x = 26 \/ x = 27) by lia.
    destruct Hc as [->|[->|[->| ->]]]; reflexivity. }
  { intros ms (R & -> & _). do 5 eexists. reflexivity. }
  intros R F pc' fc m' (R' & HE & H19 & Hcs) regs4 Hx4.
  injection HE as ER EF EP EC EM. subst R F pc' fc m'.
  apply SR_ret. unfold Pk. exists (Datatypes.S k).
  exists (mkFP Fq fcq), regs4, mem3, md3, L3, A3, r, (bx_fabric bs), ip2, ln2, bs, bs', ren, j0, j1, jm.
  split; [rewrite SEGS; reflexivity|].
  split; [exact Hfc'|].
  split; [exact (lf_base_eqv _ _ _ _ _ _ _ BASE3 Hcs Hx4)|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx4); exact H19|].
  split; [exact CF3x|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact INV|]. split; [reflexivity|].
  split; [exact CR3|]. split; [exact INV'|]. split; [exact Hfab'|]. split; [exact KEPT|].
  split; [split; [exact FR4 | split; [exact MINE3 | exact (llvm_name_back A3 b (rn_k (skipn 1 pl) + 1) RES3)]] | lia].
Qed.

End C3.
