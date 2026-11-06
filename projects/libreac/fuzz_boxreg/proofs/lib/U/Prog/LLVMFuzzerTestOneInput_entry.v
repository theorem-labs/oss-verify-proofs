From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import Boxreg BoxregInit reac_boxreg_init_c check_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import reac_boxreg_find.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import
LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_inv
LLVMFuzzerTestOneInput_exit LLVMFuzzerTestOneInput_top LLVMFuzzerTestOneInput_join.
Import ListNotations.
Open Scope Z_scope.

Lemma en_cond : forall u, 0 <= u < 2 ^ 26 ->
  negb (bv_eqb (Z_to_bv 64 (Z.shiftr u 26)) (Z_to_bv 64 0)) = false.
Proof.
  intros u Hu. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Definition en_sx (fb : Z) : Z := if fb <? 128 then fb else fb - 256.

Lemma en_signed_hi : forall x, 2 ^ 63 <= x < 2 ^ 64 -> bv_signed (Z_to_bv 64 x) = x - 2 ^ 64.
Proof.
  intros x Hx. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 / 2) with (2 ^ 63). Z.div_mod_to_equations. lia.
Qed.

Lemma en_sext : forall fb, 0 <= fb < 256 ->
  Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 fb)) 56))) 56) =
  Z_to_bv 64 (en_sx fb).
Proof.
  intros fb Hfb. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. unfold en_sx.
  destruct (Z.ltb_spec fb 128) as [H|H].
  - rewrite signed_lit by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. reflexivity.
  - rewrite en_signed_hi by lia. rewrite Z.shiftr_div_pow2 by lia.
    replace (fb * 2 ^ 56 - 2 ^ 64) with ((fb - 256) * 2 ^ 56) by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma en_swrap : forall fb, 0 <= fb < 256 -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 (en_sx fb))) = en_sx fb.
Proof.
  intros fb Hfb. unfold en_sx. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  destruct (Z.ltb_spec fb 128); Z.div_mod_to_equations; lia.
Qed.

Lemma en_clamp_in : forall fb, 1 <= fb <= 40 -> clamp40 (en_sx fb) = fb.
Proof.
  intros fb Hfb. unfold en_sx. rewrite (proj2 (Z.ltb_lt fb 128)) by lia. apply clamp40_in. exact Hfb.
Qed.

Lemma en_clamp_out : forall fb, 0 <= fb < 256 -> ~ (1 <= fb <= 40) -> clamp40 (en_sx fb) = 40.
Proof.
  intros fb Hfb Hout. unfold en_sx. destruct (Z.ltb_spec fb 128); apply clamp40_out; lia.
Qed.

Lemma en_ltu : forall fb, 0 <= fb < 256 ->
  bv_ltu (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (fb + -1))) (bv_wrap 64 255))) (Z_to_bv 64 40) =
  (1 <=? fb) && (fb <=? 40).
Proof.
  intros fb Hfb. unfold bv_ltu. change (bv_wrap 64 255) with 255.
  destruct (Z.eq_dec fb 0) as [->|Hnz]; [vm_compute; reflexivity|].
  rewrite (unsigned_lit (fb + -1)) by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  rewrite (Z.mod_small (fb + -1)) by lia. rewrite !unsigned_lit by lia.
  destruct (Z.ltb_spec (fb + -1) 40), (Z.leb_spec 1 fb), (Z.leb_spec fb 40); cbn [andb];
    first [ reflexivity | exfalso; lia ].
Qed.

Lemma en_ltu_t : forall fb, 1 <= fb <= 40 ->
  bv_ltu (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (fb + -1))) (bv_wrap 64 255))) (Z_to_bv 64 40) = true.
Proof.
  intros fb H. rewrite en_ltu by lia. rewrite (proj2 (Z.leb_le 1 fb)) by lia.
  rewrite (proj2 (Z.leb_le fb 40)) by lia. reflexivity.
Qed.

Lemma en_ltu_f : forall fb, 0 <= fb < 256 -> ~ (1 <= fb <= 40) ->
  bv_ltu (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (fb + -1))) (bv_wrap 64 255))) (Z_to_bv 64 40) = false.
Proof.
  intros fb Hfb H. rewrite en_ltu by lia.
  destruct (Z.leb_spec 1 fb), (Z.leb_spec fb 40); cbn [andb]; first [ reflexivity | exfalso; lia ].
Qed.

Lemma en_not : forall x, 0 <= x < 2 ^ 64 -> Z_to_bv 64 (18446744073709551615 - x) = Z_to_bv 64 (-1 - x).
Proof.
  intros x Hx. apply bv_eq. rewrite !unsigned_lit_wrap. change (2 ^ 64) with 18446744073709551616.
  replace (18446744073709551615 - x) with ((-1 - x) + 1 * 18446744073709551616) by lia.
  apply Z.mod_add. lia.
Qed.

Lemma en_r4 : forall r, r mod 16 = 0 -> r mod 4 = 0.
Proof. intros r H. Z.div_mod_to_equations. lia. Qed.

Lemma en_rw_cb : forall m0 m A n bs0 bs,
  rw_cells rsegs m0 A [CB n bs0] -> wmono rsegs m0 m -> length bs = n -> bytes_at rsegs m A bs ->
  rw_cells rsegs m A [CB n bs].
Proof.
  intros m0 m A n bs0 bs [_ HW] WM HL HB. split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact HL | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - exact (wr_at_transport rsegs m0 m A _ HW WM).
Qed.

Lemma en_munch : forall W W' m1 m2 m3, munch W m1 m2 -> munch W' m2 m3 -> sub_fp W' W -> munch W m1 m3.
Proof. intros W W' m1 m2 m3 H1 H2 Hs. exact (munch_trans W m1 m2 m3 H1 (munch_weaken W' W m2 m3 Hs H2)). Qed.

Lemma en_stk_out : forall B m lo hi, ms_segs B = rsegs -> 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> ~ in_img B a /\ writable_at rsegs m a) -> Frame.stk rsegs m lo hi.
Proof.
  intros B m lo hi HS Hlo Hhi H. split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as [Hn W]. unfold writable_at in W. rewrite (lf_wview_out B m a HS Hn ltac:(lia)) in W.
  unfold Mem.wa. split.
  - rewrite (lf_wview_out B m a HS Hn ltac:(lia)). exact W.
  - unfold Mem.mrd. destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | contradiction].
Qed.

Lemma en_pro_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 464 <= bv_unsigned sp -> mem_inv rsegs m ->
    bv_unsigned a1 < 2 ^ 26 ->
    evt rsegs
      (fun ms' => exists (a1' : word) (j1 : list byte) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x12d1c) (Z_to_bv 64 (bv_unsigned sp - 464)) gp tp t0 t1 t2 s0 a0
                       (Z_to_bv 64 288) a1' a2 a3 a4 a5 a6 a7 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x14b88) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 464, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp - 464) /\
         rw_cells rsegs m' (bv_unsigned sp - 464)
           [CB 344 j1; C8 a0; C8 a1; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2;
            C8 s1; C8 s0; C8 ra])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12cc4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO MI H26.
  pose proof (munch_refl [(bv_unsigned sp - 464, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra1.
  carve_frame 464%nat ST.
  do 17 step.
  if_false_by (en_cond (bv_unsigned a1) ltac:(lia)).
  do 5 step.
  apply evt_done. do 3 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  split; [exact ST | exact FR].
Qed.

Definition en_Q (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (spv r p n lo hi : Z) (ws : list cell) : machine_state -> Prop :=
  fun ms' => exists (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                     x28 x29 x30 x31 pc : word) (m' : word -> option byte) (fab ip inn : Z) (bs j0 j1 : list byte),
    ms' = MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 r) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                  x24 x25 x26 x27 x28 x29 x30 x31) F pc fc None m' (seg_rom rsegs) /\
    munch [(lo, hi); (r, r + 288)] m m' /\ wmono rsegs m m' /\
    rw_cells rsegs m' r [CB 288 bs] /\ boxreg_inv bs /\ bx_fabric bs = fab /\ p <= ip /\ ip + inn = p + n /\
    ((pc = Z_to_bv 64 0x12da8 /\ 1 <= inn /\ x10 = Z_to_bv 64 0 /\ x18 = Z_to_bv 64 inn /\ x22 = Z_to_bv 64 1 /\
      x23 = Z_to_bv 64 fab /\ x24 = Z_to_bv 64 (-1 - (spv + 48)) /\ x25 = Z_to_bv 64 (-1 - r) /\
      x26 = Z_to_bv 64 (spv + 48) /\ x27 = Z_to_bv 64 336 /\
      rw_cells rsegs m' spv (CB 8 j0 :: C8 (Z_to_bv 64 0) :: C8 (Z_to_bv 64 fab) :: CB 320 j1 :: C8 (Z_to_bv 64 ip) ::
        C8 (Z_to_bv 64 inn) :: ws)) \/
     (pc = Z_to_bv 64 0x13528 /\
      rw_cells rsegs m' spv (CB 344 j1 :: C8 (Z_to_bv 64 ip) :: C8 (Z_to_bv 64 inn) :: ws))).

Section V.
Hypothesis INIT : reac_boxreg_init_contract.
Hypothesis CHECK : check_contract.

Lemma en_chk_evt :
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
          gp tp : word)
         (F : bvmap 5 word) (fc : bv 32) (m m1 : word -> option byte) (spv r p n lo hi fab ip inn : Z)
         (bs j1 : list byte) (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word),
    x23 = Z_to_bv 64 fab ->
    munch [(lo, hi); (r, r + 288)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 -> stk rsegs m1 lo spv ->
    rw_cells rsegs m1 r [CB 288 bs] -> boxreg_inv bs -> bx_fabric bs = fab ->
    rw_cells rsegs m1 spv [CB 344 j1; C8 (Z_to_bv 64 ip); C8 (Z_to_bv 64 inn); C8 w1; C8 w2; C8 w3; C8 w4; C8 w5;
      C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13] ->
    LF_RES_TOP <= lo -> lo + 144 <= spv -> spv + 464 <= hi -> hi <= 2 ^ 64 -> 0 <= r -> r + 288 <= lo ->
    r mod 16 = 0 -> p <= ip -> ip + inn = p + n -> 0 <= inn < 2 ^ 64 ->
    evt rsegs (en_Q (Z_to_bv 64 spv) gp tp F fc m spv r p n lo hi
                 [C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13])
      (MS (mkR x1 (Z_to_bv 64 spv) gp tp x5 x6 x7 (Z_to_bv 64 r) x9 x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 inn) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x12d74) fc None m1 (seg_rom rsegs)).
Proof.
  intros x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 gp tp
    F fc m m1 spv r p n lo hi fab ip inn bs j1 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
    -> MU WM MI ST HR INV HFB HF Hlo Hlo2 Hhi Hhi2 Hr0 Hr Hr16 Hip Hipn Hinn.
  assert (Hspv : 0 <= spv < 2 ^ 64) by (unfold LF_RES_TOP in Hlo; lia).
  pose proof CHECK as CK. unfold check_contract, check_c.CHECK, CHECK_FRAME in CK.
  pose proof (top_rw_bytes m1 r 288 bs HR) as HB.
  pose proof INV as (B16 & B7).
  step. step. step.
  eapply evt_cut.
  { eapply CK with (r := r) (fabric := fab) (bs := bs) (lo := lo);
      [ fnd_eq | fnd_eq | exact (en_r4 r Hr16) | exact HB | exact B16 | exact HFB | exact MI
      | rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia
      | left; rewrite unsigned_lit by lia; lia ]. }
  intros ms' PO.
  destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & E & MU2 & WM2 & ST2 & _).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x12d80)) with (Z_to_bv 64 0x12d80)
    by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  rewrite unsigned_lit in MU2, ST2 by lia.
  pose proof (jn_mem_inv _ _ m1 m2 MI MU2 ltac:(lia)) as MI2.
  pose proof (rw_cells_transport rsegs _ m1 m2 _ _ HR MU2 WM2
    ltac:(cbn [disjoint_from]; change (Z.of_nat (cells_size [CB 288 bs])) with 288; split; [lia | exact I])) as HR2.
  pose proof (rw_cells_transport rsegs _ m1 m2 _ _ HF MU2 WM2
    ltac:(cbn [disjoint_from]; split; [lia | exact I])) as HF2.
  pose proof (en_munch _ _ m m1 m2 MU MU2 ltac:(unfold sub_fp; cbn [outside]; intros x Hx; repeat split; lia)) as MU3.
  pose proof (wmono_trans rsegs m m1 m2 WM WM2) as WM3.
  clear MU MU2 WM WM2 HR HF HB ST MI.
  pose proof MU3 as MU. pose proof WM3 as WM. pose proof MI2 as MI.
  step. if_cases HC; zify_cond HC.
  - apply evt_done. unfold en_Q. do 29 eexists. exists fab, ip, inn, bs, (@nil byte), j1.
    split; [reflexivity|]. split; [exact MU3|]. split; [exact WM3|]. split; [exact HR2|].
    split; [exact INV|]. split; [exact HFB|]. split; [exact Hip|]. split; [exact Hipn|].
    right. split; [reflexivity | exact HF2].
  - step. step.
    rewrite ?(unsigned_lit r) by lia. rewrite ?(fnd_land3 r (en_r4 r Hr16)).
    step. step. rewrite ?(unsigned_lit r) by lia. rewrite (fnd_lxor r) by lia. rewrite (en_not r) by lia.
    step. step. step. step. rewrite (unsigned_lit (spv + 48)) by lia. rewrite (fnd_lxor (spv + 48)) by lia.
    rewrite (en_not (spv + 48)) by lia.
    step.
    apply evt_done. unfold en_Q. do 35 eexists.
    split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [exact HR2|].
    split; [exact INV|]. split; [exact HFB|]. split; [exact Hip|]. split; [exact Hipn|].
    left. split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [fnd_eq|]. split; [reflexivity|]. eassumption.
Qed.

Lemma en_mid_evt :
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
          gp tp : word)
         (F : bvmap 5 word) (fc : bv 32) (m mm : word -> option byte) (spv r p n lo hi fb ip inn : Z)
         (junk j1 : list byte) (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word),
    x9 = Z_to_bv 64 fb -> x18 = Z_to_bv 64 inn -> 0 <= fb < 256 ->
    munch [(lo, hi); (r, r + 288)] m mm -> wmono rsegs m mm -> mem_inv rsegs mm -> stk rsegs mm lo spv ->
    rw_cells rsegs mm r [CB 288 junk] ->
    rw_cells rsegs mm spv [CB 344 j1; C8 (Z_to_bv 64 ip); C8 (Z_to_bv 64 inn); C8 w1; C8 w2; C8 w3; C8 w4; C8 w5;
      C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13] ->
    LF_RES_TOP <= lo -> lo + 144 <= spv -> spv + 464 <= hi -> hi <= 2 ^ 64 -> 0 < r -> r mod 16 = 0 ->
    r + 288 <= lo -> p <= ip -> ip + inn = p + n -> 0 <= inn < 2 ^ 64 ->
    evt rsegs (en_Q (Z_to_bv 64 spv) gp tp F fc m spv r p n lo hi
                 [C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13])
      (MS (mkR x1 (Z_to_bv 64 spv) gp tp x5 x6 x7 (Z_to_bv 64 r) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
               x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x12d4c) fc None mm (seg_rom rsegs)).
Proof.
  intros x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 gp tp
    F fc m mm spv r p n lo hi fb ip inn junk j1 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
    -> -> Hfb MU WM MI ST HR HF Hlo Hlo2 Hhi Hhi2 Hr0 Hr16 Hr Hip Hipn Hinn.
  assert (Hspv : 0 <= spv < 2 ^ 64) by (unfold LF_RES_TOP in Hlo; lia).
  pose proof INIT as IN. unfold reac_boxreg_init_contract, REAC_BOXREG_INIT, REAC_BOXREG_INIT_FRAME in IN.
  step. step. step. step. step.
  rewrite (en_sext fb Hfb).
  eapply evt_cut.
  { eapply IN with (r := r) (lo := lo) (junk := junk);
      [ reflexivity | exact HR | lia | exact (en_r4 r Hr16)
      | rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia
      | left; rewrite unsigned_lit by lia; lia | exact MI ]. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1
    & E & MU1 & WM1 & MI1 & ST1 & HB1 & INV1 & HN1 & HFB1).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x12d60)) with (Z_to_bv 64 0x12d60)
    by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  rewrite unsigned_lit in MU1, ST1 by lia.
  rewrite (en_swrap fb Hfb) in HB1, INV1, HFB1.
  pose proof (en_rw_cb mm m1 r 288 junk _ HR WM1 (init_bytes_length _) HB1) as HR1.
  pose proof (rw_cells_transport rsegs _ mm m1 _ _ HF MU1 WM1
    ltac:(cbn [disjoint_from]; split; [lia | split; [lia | exact I]])) as HF1.
  pose proof (en_munch _ _ m mm m1 MU MU1 ltac:(unfold sub_fp; cbn [outside]; intros x Hx; repeat split; lia)) as MU2.
  pose proof (wmono_trans rsegs m mm m1 WM WM1) as WM2.
  clear MU MU1 WM WM1 HR HF HB1 ST MI.
  step. step. step. step.
  assert (Hd : (1 <= fb <= 40) \/ ~ (1 <= fb <= 40)) by lia.
  destruct Hd as [Hin|Hout].
  - if_true_by (en_ltu_t fb Hin).
    eapply en_chk_evt with (m := m) (spv := spv) (r := r) (p := p) (n := n) (lo := lo) (hi := hi)
      (fab := clamp40 (en_sx fb)) (ip := ip) (inn := inn) (bs := init_bytes (clamp40 (en_sx fb))) (j1 := j1);
      try eassumption; try lia.
    rewrite (en_clamp_in fb Hin). unfold en_sx. rewrite (proj2 (Z.ltb_lt fb 128)) by lia. reflexivity.
  - if_false_by (en_ltu_f fb Hfb Hout).
    step.
    eapply en_chk_evt with (m := m) (spv := spv) (r := r) (p := p) (n := n) (lo := lo) (hi := hi)
      (fab := clamp40 (en_sx fb)) (ip := ip) (inn := inn) (bs := init_bytes (clamp40 (en_sx fb))) (j1 := j1);
      try eassumption; try lia.
    rewrite (en_clamp_out fb Hfb Hout). reflexivity.
Qed.

Lemma en_body_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv r p n lo hi : Z)
         (j1 junk : list byte) (vb : byte) (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 r -> s1 = Z_to_bv 64 p -> s2 = Z_to_bv 64 n ->
    rw_cells rsegs m spv [CB 344 j1; C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 n); C8 w1; C8 w2; C8 w3; C8 w4; C8 w5;
      C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13] ->
    rw_cells rsegs m r [CB 288 junk] ->
    (n = 0 \/ (1 <= n /\ ov_read_bytes rsegs m (Z_to_bv 64 p) 1 = Some [vb] /\ 1 <= p /\ p + 1 <= lo /\
               (p + 1 <= r \/ r + 288 <= p))) ->
    mem_inv rsegs m -> stk rsegs m lo spv -> LF_RES_TOP <= lo -> lo + 144 <= spv -> spv + 464 <= hi ->
    hi <= 2 ^ 64 -> 0 < r -> r mod 16 = 0 -> r + 288 <= lo -> 0 <= n < 2 ^ 64 ->
    evt rsegs (en_Q sp gp tp F fc m spv r p n lo hi
                 [C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12d1c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv r p n lo hi j1 junk vb w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
    -> -> -> -> HF HR HP MI ST Hlo Hlo2 Hhi Hhi2 Hr0 Hr16 Hr Hn.
  assert (Hspv : 0 <= spv < 2 ^ 64) by (unfold LF_RES_TOP in Hlo; lia).
  pose proof (munch_refl [(lo, hi); (r, r + 288)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. if_cases HC; zify_cond HC; [exfalso; lia|].
  step. step. if_cases HC1; zify_cond HC1.
  - assert (En : n = 0) by lia. subst n.
    step.
    eapply en_mid_evt with (m := m) (spv := spv) (r := r) (p := p) (n := 0) (lo := lo) (hi := hi) (fb := 0)
      (ip := p) (inn := 0) (junk := junk) (j1 := j1);
      try eassumption; try reflexivity; try lia.
  - destruct HP as [Hn0 | (Hn1 & HP & Hp1 & Hp2 & Hp3)]; [exfalso; lia|].
    pose proof (bv_unsigned_in_range 8 vb) as R8. change (bv_modulus 8) with 256 in R8.
    step. step. step. step.
    step. if_cases HC2; [ exfalso; zify_cond HC2; rewrite ?unsigned_lit_wrap in HC2; Z.div_mod_to_equations; lia | ].
    clear HC2.
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (HP0 : ov_read_bytes rsegs mm (Z_to_bv 64 p) 1 = Some [vb])
          by (rewrite (top_ovr_munch [(lo, hi); (r, r + 288)] m mm p MU ltac:(lia)
                ltac:(cbn [Frame.outside]; split; [lia | split; [lia | exact I]])); exact HP)
    end.
    step. step. step.
    eapply en_mid_evt with (m := m) (spv := spv) (r := r) (p := p) (n := n) (lo := lo) (hi := hi)
      (fb := bv_unsigned vb) (ip := p + 1) (inn := n - 1) (junk := junk) (j1 := j1);
      try eassumption; try reflexivity; try lia.
Qed.

End V.

Section E.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis MALLOC : forall fx' : YK11.FPState, @malloc_contract fx' rc B API.
Hypothesis INIT : reac_boxreg_init_contract.
Hypothesis CHECK : check_contract.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= YM05.alloc_ceiling.

Theorem llvm_entry_holds : forall stk empty L0 A0 regs0 mem0 md0 ra p n b,
    llvm_ctx B API stk empty L0 A0 regs0 mem0 md0 ra p n b ->
    SR (ms_segs B) (mkCfg (YK11.mkst regs0 (Z_to_bv 64 LLVM_ENTRY) mem0 (YK11.seg_rom (ms_segs B))) md0)
      (fun c => llvm_J B API stk L0 A0 regs0 mem0 md0 p n b 0 1 c \/ llvm_X B API stk L0 A0 regs0 mem0 md0 b 1 c).
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n b CTX.
  pose proof CTX as ((SEGS & HMAL & HFRE & HGG & HG & AX) & Hk & Hra & Hpre & Hsn & Hsp47 & Hres & Hroom & Hro
    & Hrelro & Hfrm & Hn26).
  pose proof Hpre as (HM & HW & HB & HID & Hra1 & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hn1 & Hpl & Hrod).
  pose proof (lf_fr_init B API stk empty L0 A0 regs0 mem0 md0 ra p n Hpre Hro) as FR0.
  unfold LLVM_K, LLVM_FRAME in Hk.
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt.
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  assert (Hn0 : 0 <= n) by (destruct Hpl as [[-> _] | [H _]]; lia).
  assert (E11 : bv_unsigned (reg_get regs0 11) = n).
  { change (reg_get regs0 11) with (YK11.getr regs0 11). rewrite Hn1. apply unsigned_lit. lia. }
  set (S := spZ regs0) in *.
  assert (ES : bv_unsigned (reg_get regs0 2) = S) by reflexivity.
  rewrite SEGS.
  eapply (llvm_run_norm fx regs0 (Z_to_bv 64 LLVM_ENTRY) mem0 md0); [exact Hh | exact Hl | exact Hro | | |].
  - unfold Regs6ss.mkR_of, LLVM_ENTRY.
    apply en_pro_evt with (lo := S - stk).
    + rewrite ES. apply lf_stk; [lia | lia |].
      intros a Ha. unfold writable_at.
      assert (Hni : ~ in_img B a) by (intros Hi; pose proof (lf_in_img_top B a SEGS Hi); lia).
      rewrite (wview_rel_rw rsegs mem0 (normalize rsegs mem0) _ (mem_rel_normalize rsegs mem0 Hro)
                 (lf_ro_addr_out B a SEGS Hni ltac:(lia))).
      rewrite <- SEGS. exact (Hstw a Ha).
    + rewrite ES. lia.
    + exact (mem_inv_normalize rsegs mem0).
    + rewrite E11. lia.
  - intros ms (a1' & j1 & m'' & -> & _). do 5 eexists. reflexivity.
  - intros R F pc' fc m0' (a1' & j1 & m'' & HE & MU & WM & MI' & ST' & CF) regs1 m1 Hx Hrel Hsame.
    injection HE as ER EF EP EC EM. subst R F pc' fc m0'.
    assert (MU' : munch [(S - 464, S)] mem0 m1)
      by exact (munch_rel rsegs _ mem0 (normalize rsegs mem0) m1 m'' (mem_rel_normalize rsegs mem0 Hro) Hrel Hsame MU).
    assert (WM' : wmono rsegs mem0 m1)
      by exact (wmono_rel rsegs mem0 (normalize rsegs mem0) m1 m'' (mem_rel_normalize rsegs mem0 Hro) Hrel Hsame WM).
    assert (Hro1 : ro_agree rsegs m1) by exact (ro_agree_same rsegs mem0 m1 Hro Hsame).
    assert (FR1 : lf_fr B API stk S L0 A0 mem0 md0 L0 A0 m1 md0).
    { eapply (lf_fr_evt B API SEGS AX HGG); [exact FR0 | lia | lia | exact MU' | exact WM' | exact Hro1 |].
      intros x Hx0 NO. left.
      destruct (Z_le_dec (S - 464) x); destruct (Z_lt_dec x S); try lia;
        exfalso; apply NO; cbn [Frame.outside]; (split; [lia | exact I]). }
    pose proof (lf_rw_cells_rel m1 m'' _ _ Hrel CF) as CF1.
    clear MU WM CF.
    assert (G1 : YK11.getr regs1 1 = Z_to_bv 64 0x12d1c) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
    assert (G2 : YK11.getr regs1 2 = Z_to_bv 64 (S - 464)) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
    assert (G3 : YK11.getr regs1 3 = YK11.getr regs0 3) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
    assert (G4 : YK11.getr regs1 4 = YK11.getr regs0 4) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
    assert (G9 : YK11.getr regs1 9 = Z_to_bv 64 p) by (rewrite (lf_getr_eqv _ _ _ Hx); exact Hp).
    assert (G10 : YK11.getr regs1 10 = Z_to_bv 64 288) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
    assert (G18 : YK11.getr regs1 18 = Z_to_bv 64 n) by (rewrite (lf_getr_eqv _ _ _ Hx); exact Hn1).
    assert (Hsp1 : spZ regs1 = S - 464) by (unfold spZ; rewrite G2; apply unsigned_lit; lia).
    pose proof FR1 as (HM1 & HW1 & HB1 & HID1 & Hmd1 & Hhigh1 & Himg1 & Hblk1 & Hbyt1 & Hstw1 & Herr1 & Hgd1 & MI1).
    rewrite <- SEGS.
    eapply SR_bind.
    { replace (Z_to_bv 64 0x14b88) with (Z_to_bv 64 (ms_malloc B)) by (rewrite HMAL; reflexivity).
      apply (MALLOC (mkFP (@fp_regs fx) (@fp_csr fx)) L0 A0 regs1 m1 md0 288 b).
      - split; [exact HM1|]. split; [exact HW1|]. split; [exact HB1|].
        split; [rewrite G1; apply ret_ok_even; reflexivity|].
        split; [rewrite Hsp1; replace (S - 464) with (S + (-29) * 16) by lia; rewrite Z.mod_add by lia; exact Hal|].
        split; [rewrite Hsp1; unfold ALLOC_STACK; lia|]. split; [rewrite Hsp1; lia|].
        split; [intros a Ha; apply Hstw1; rewrite Hsp1 in Ha; unfold ALLOC_STACK in Ha; lia|].
        split; [rewrite G4; exact Htp|]. split; [exact Herr1|].
        intros E. rewrite HID in E. discriminate.
      - rewrite SEGS. exact Hro1.
      - exact G10.
      - exact Hres.
      - exact (lf_room0 A0 b 288 Hres Hroom ltac:(unfold LLVM_REQ; lia)). }
    intros c2 (L2 & A2 & regs2 & mem2 & md2 & res & -> & Hpost & G10' & Hres0 & Hal16 & (Hf1 & Hf2 & Hf3)
      & (b1 & b2 & Eb1 & Eb2) & Hkept & Hro2 & Hgk & Hub & Hidt & Hlen & Hres2).
    pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hrp & (vm2 & Hvm2) & Hfr2 & Hkeep2 & Hscr2).
    destruct (mr_model B _ (aa_laws API) _ _ _ _ HM2) as (Hh2 & Hl2 & _).
    rewrite SEGS in Hro2.
    assert (FR2 : lf_fr B API stk S L0 A0 mem0 md0 L2 A2 mem2 md2).
    { eapply (lf_fr_call B API SEGS AX ERRNO_LOW); [exact FR1 | lia | lia | exact Hpost
        | rewrite Hsp1; unfold ALLOC_STACK; lia | rewrite Hsp1; lia | | | | | | exact Hidt | | ].
      - intros a Ha. exfalso. exact Ha.
      - intros a Ha. right. intros Hf. exact Hf.
      - intros a Hf Ha. exfalso. exact Hf.
      - intros a0 k0 Hin. rewrite Eb2 in Hin. rewrite Eb1.
        apply in_app_or in Hin. apply in_or_app. destruct Hin as [Hin|Hin]; [left; exact Hin | right; right; exact Hin].
      - intros a0 k0 i Hin Hi. exact (Hkept a0 k0 i Hin (fun H => H) Hi).
      - exact Hro2.
      - exact Hgk. }
    assert (MINE : lf_mine L0 A0 L2 A2 res 288).
    { split; [rewrite Eb1; apply in_or_app; right; left; reflexivity|]. split; [lia|].
      intros a j Hin. rewrite Eb2 in Hin.
      pose proof (mr_blocks_disjoint B (aa_MR API) (aa_laws API) L2 A2 mem2 md2 HM2) as HP. rewrite Eb1 in HP.
      destruct (pairwise_app_mid _ b1 (res, 288) b2 (a, j) HP Hin) as [H|H];
        unfold ranges_disjoint in H; cbn [fst snd] in H; lia. }
    assert (CF2 : rw_cells rsegs mem2 (S - 464)
      [CB 344 j1; C8 (reg_get regs0 10); C8 (reg_get regs0 11); C8 (reg_get regs0 27); C8 (reg_get regs0 26);
       C8 (reg_get regs0 25); C8 (reg_get regs0 24); C8 (reg_get regs0 23); C8 (reg_get regs0 22);
       C8 (reg_get regs0 21); C8 (reg_get regs0 20); C8 (reg_get regs0 19); C8 (reg_get regs0 18);
       C8 (reg_get regs0 9); C8 (reg_get regs0 8); C8 (reg_get regs0 1)]).
    { apply (lf_rw_cells_frame m1); [exact CF1|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
      rewrite <- SEGS. apply Hfr2.
      - left. lia.
      - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ a HM1 Ho). lia.
      - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ a HM2 Ho). lia.
      - unfold scratch_k. rewrite Hsp1. unfold ALLOC_STACK.
        intros [Hs|Hs]; [lia | pose proof (lf_errno_low B ERRNO_LOW a Hs); lia].
      - intros Hf. exact Hf. }
    change (reg_get regs0 10) with (YK11.getr regs0 10) in CF2. rewrite Hp in CF2.
    change (reg_get regs0 11) with (YK11.getr regs0 11) in CF2. rewrite Hn1 in CF2.
    pose proof FR2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hstw2 & _).
    assert (CFn : rw_cells rsegs (normalize rsegs mem2) (S - 464)
      [CB 344 j1; C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 n); C8 (reg_get regs0 27); C8 (reg_get regs0 26);
       C8 (reg_get regs0 25); C8 (reg_get regs0 24); C8 (reg_get regs0 23); C8 (reg_get regs0 22);
       C8 (reg_get regs0 21); C8 (reg_get regs0 20); C8 (reg_get regs0 19); C8 (reg_get regs0 18);
       C8 (reg_get regs0 9); C8 (reg_get regs0 8); C8 (reg_get regs0 1)]).
    { apply (lf_rw_cells_norm B); [exact SEGS | exact Hro2 | | exact CF2].
      intros x Hx' Himg. pose proof (lf_in_img_top B _ SEGS Himg). lia. }
    assert (STn : Frame.stk rsegs (normalize rsegs mem2) (S - stk) (S - 464)).
    { apply lf_stk; [lia | lia |]. intros a Ha. unfold YP09.writable_at.
      assert (Hni : ~ in_img B a) by (intros Hi'; pose proof (lf_in_img_top B a SEGS Hi'); lia).
      rewrite (wview_rel_rw rsegs mem2 (normalize rsegs mem2) _ (mem_rel_normalize rsegs mem2 Hro2)
                 (lf_ro_addr_out B a SEGS Hni ltac:(lia))).
      rewrite <- SEGS. exact (Hstw2 a ltac:(lia)). }
    assert (STr : Frame.stk rsegs (normalize rsegs mem2) res (res + 288)).
    { apply (en_stk_out B); [exact SEGS | lia | lia |]. intros a Ha.
      destruct (lf_mine_bytes B API AX L0 A0 L2 A2 mem2 md2 res 288 a HM2 MINE Ha) as (N1 & N2 & N3 & N4 & N5).
      split; [exact N2|]. unfold YP09.writable_at.
      rewrite (wview_rel_rw rsegs mem2 (normalize rsegs mem2) _ (mem_rel_normalize rsegs mem2 Hro2)
                 (lf_ro_addr_out B a SEGS N2 ltac:(lia))).
      apply YL01.present_writable. exact N4. }
    destruct (stk_carve rsegs _ res (res + 288) 288 STr ltac:(lia)) as [_ [junk HRj]].
    change (Z.of_nat 288) with 288 in HRj. replace (res + 288 - 288) with res in HRj by lia.
    assert (HPAY : exists vb, n = 0 \/
      (1 <= n /\ ov_read_bytes rsegs (normalize rsegs mem2) (Z_to_bv 64 p) 1 = Some [vb] /\ 1 <= p /\
       p + 1 <= S - stk /\ (p + 1 <= res \/ res + 288 <= p))).
    { destruct (Z.eq_dec n 0) as [E0|E0]; [exists (Z_to_bv 8 0); left; exact E0|].
      destruct (llvm_payload_read B API stk empty L0 A0 regs0 mem0 md0 ra p n b L2 A2 mem2 md2 p CTX FR2
        ltac:(lia)) as [v Hv].
      destruct Hpl as [[E0' _] | [_ (q & Hq & Hqp)]]; [lia|].
      destruct (mr_blocks B _ (aa_laws API) L0 A0 mem0 md0 q n 0 HM Hq ltac:(lia)) as (_ & Hq1 & Hq2 & _).
      rewrite Hqp in Hq1, Hq2.
      assert (Hpb : In (p, n) (blocks L0 A0)) by (apply blocks_In; exists q; auto).
      pose proof MINE as (_ & _ & Hdis). specialize (Hdis p n Hpb).
      exists v. right. split; [lia|]. split.
      { rewrite <- (ov_read_rel rsegs mem2 (normalize rsegs mem2) _ _ (mem_rel_normalize rsegs mem2 Hro2)). exact Hv. }
      split; [lia|]. split; [lia|]. lia. }
    destruct HPAY as [vb HPAY].
    assert (G2' : YK11.getr regs2 (Z_to_bv 5 2) = Z_to_bv 64 (S - 464))
      by (rewrite (Hrp 2 ltac:(unfold callee_saved; lia)); exact G2).
    assert (G3' : YK11.getr regs2 (Z_to_bv 5 3) = YK11.getr regs0 3)
      by (rewrite (Hrp 3 ltac:(unfold callee_saved; lia)); exact G3).
    assert (G4' : YK11.getr regs2 (Z_to_bv 5 4) = YK11.getr regs0 4)
      by (rewrite (Hrp 4 ltac:(unfold callee_saved; lia)); exact G4).
    assert (G9' : YK11.getr regs2 (Z_to_bv 5 9) = Z_to_bv 64 p)
      by (rewrite (Hrp 9 ltac:(unfold callee_saved; lia)); exact G9).
    assert (G18' : YK11.getr regs2 (Z_to_bv 5 18) = Z_to_bv 64 n)
      by (rewrite (Hrp 18 ltac:(unfold callee_saved; lia)); exact G18).
    rewrite G1, SEGS.
    eapply (llvm_run_norm (mkFP (@fp_regs fx) (@fp_csr fx)) regs2 (Z_to_bv 64 0x12d1c) mem2 md2);
      [exact Hh2 | exact Hl2 | exact Hro2 | | |].
    + unfold Regs6ss.mkR_of.
      eapply (en_body_evt INIT CHECK) with (spv := S - 464) (r := res) (p := p) (n := n) (lo := S - stk) (hi := S)
        (junk := junk) (vb := vb);
        [ exact G2' | exact G10' | exact G9' | exact G18' | exact CFn | exact HRj | exact HPAY
        | exact (mem_inv_normalize rsegs mem2) | exact STn | lia | lia | lia | lia | lia | exact Hal16 | lia | lia ].
    + intros ms HQ. unfold en_Q in HQ.
      destruct HQ as (x1 & x5 & x6 & x7 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20
        & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & pc & mq & fab & ip & inn & bs
        & j0 & j1' & -> & _).
      do 5 eexists. reflexivity.
    + intros R F pc' fc m0' HQ regs3 m3 Hx3 Hrel3 Hsame3. unfold en_Q in HQ.
      destruct HQ as (x1 & x5 & x6 & x7 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20
        & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & pc & mq & fab & ip & inn & bs
        & j0 & j1' & HE & MU3 & WM3 & HR3 & INV3 & HFB3 & Hip & Hipn & HJX).
      injection HE as ER EF EP EC EM. subst R F pc' fc m0'.
      assert (MU3' : munch [(S - stk, S); (res, res + 288)] mem2 m3)
        by exact (munch_rel rsegs _ mem2 (normalize rsegs mem2) m3 mq (mem_rel_normalize rsegs mem2 Hro2)
                    Hrel3 Hsame3 MU3).
      assert (WM3' : wmono rsegs mem2 m3)
        by exact (wmono_rel rsegs mem2 (normalize rsegs mem2) m3 mq (mem_rel_normalize rsegs mem2 Hro2)
                    Hrel3 Hsame3 WM3).
      assert (Hro3 : ro_agree rsegs m3) by exact (ro_agree_same rsegs mem2 m3 Hro2 Hsame3).
      assert (FR3 : lf_fr B API stk S L0 A0 mem0 md0 L2 A2 m3 md2).
      { eapply (lf_fr_evt B API SEGS AX HGG); [exact FR2 | lia | lia | exact MU3' | exact WM3' | exact Hro3 |].
        intros x Hx0 NO.
        destruct (Z_le_dec (S - stk) x); destruct (Z_lt_dec x S); try (left; lia).
        all: right; exists res, 288; split; [exact MINE|];
          destruct (Z_le_dec res x); destruct (Z_lt_dec x (res + 288)); try lia;
          exfalso; apply NO; cbn [Frame.outside]; repeat split; lia. }
      pose proof (lf_rw_cells_rel m3 mq _ _ Hrel3 HR3) as HR4.
      apply SR_ret.
      destruct HJX as [(Epc & Hinn & E10 & E18 & E22 & E23 & E24 & E25 & E26 & E27 & HF3) | (Epc & HF3)]; subst pc;
        pose proof (lf_rw_cells_rel m3 mq _ _ Hrel3 HF3) as HF4.
      * left. eexists. exists regs3, m3, md2, L2, A2, res, fab, ip, inn, bs, j0, j1',
          (cells_bytes [C8 (Z_to_bv 64 inn)]).
        split; [rewrite SEGS; reflexivity|].
        split; [exact Hfrm|].
        split.
        { unfold llvm_regs_base. rewrite !(lf_getr_eqv _ _ _ Hx3).
          split; [exact G2'|]. split; [exact G3'|]. split; [exact G4'|]. split; [reflexivity|].
          split; [exact E22|]. split; [exact E23|]. split; [exact E24|]. split; [exact E25|].
          split; [exact E26 | exact E27]. }
        split; [rewrite (lf_getr_eqv _ _ _ Hx3); exact E10|].
        split; [rewrite (lf_getr_eqv _ _ _ Hx3); exact E18|].
        split; [exact (rw_cells_merge rsegs m3 (S - 464)
          [CB 8 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 fab); CB 320 j1'; C8 (Z_to_bv 64 ip)]
          [C8 (Z_to_bv 64 inn)] _ HF4)|].
        split; [lia|]. split; [lia|]. split; [exact Hip|]. split; [exact Hipn|].
        split; [exact HR4|]. split; [exact INV3|]. split; [exact HFB3|].
        split; [split; [exact FR3 | split; [exact MINE | exact Hres2]] | cbn; lia].
      * right. eexists. exists regs3, m3, md2, L2, A2, res,
          (cells_bytes [CB 344 j1'; C8 (Z_to_bv 64 ip); C8 (Z_to_bv 64 inn)]).
        split; [rewrite SEGS; reflexivity|].
        split; [exact Hfrm|].
        rewrite !(lf_getr_eqv _ _ _ Hx3).
        split; [exact G2'|]. split; [exact G3'|]. split; [exact G4'|]. split; [reflexivity|].
        split; [exact (rw_cells_merge rsegs m3 (S - 464) [] [CB 344 j1'; C8 (Z_to_bv 64 ip); C8 (Z_to_bv 64 inn)] _ HF4)|].
        split; [split; [exact FR3 | split; [exact MINE | exact Hres2]] | lia].
Qed.

End E.
