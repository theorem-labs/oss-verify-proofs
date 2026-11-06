From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree codec_cells codec_img
  codec_main_inv LLVMFuzzerTestOneInput_c codec_main_owe_lib.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** owe()'s BUTTON case (fuzz_codec.c:151-155). *)
Lemma owe1_spec_ok : forall od a b c delta bytes n, 0 <= a <= 0x7f -> 0 <= b <= 0x3f ->
  owe_spec 1 od a b c delta bytes n =
  (0, ([0x90; u8 a; u8 (Z.lor (bit_or_0 (negb (c =? 0)) 0x40) b)], KEY 2 (Z.lor ((a * 256) mod 2 ^ 32) b), 0)).
Proof.
  intros od a b c delta bytes n Ha Hb. unfold owe_spec. destruct od; cbv beta iota zeta;
    (destruct (Z.ltb_spec 0x7f a); [lia|]); (destruct (Z.ltb_spec 0x3f b); [lia|]); reflexivity.
Qed.

Lemma owe1_spec_rng : forall od a b c delta bytes n, 0x7f < a \/ 0x3f < b ->
  fst (owe_spec 1 od a b c delta bytes n) = E_RANGE.
Proof.
  intros od a b c delta bytes n H. unfold owe_spec. destruct od; cbv beta iota zeta;
    destruct (Z.ltb_spec 0x7f a); destruct (Z.ltb_spec 0x3f b); try reflexivity; lia.
Qed.

Lemma key1 : forall a b, 0 <= a <= 127 -> 0 <= b <= 63 ->
  Z.lor (Z.shiftl a 8 mod 2 ^ 64) (Z.lor b 131072) = KEY 2 (Z.lor ((a * 256) mod 2 ^ 32) b).
Proof.
  intros a b Ha Hb. unfold KEY. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (Z.mod_small (a * 2 ^ 8)) by lia. rewrite (Z.mod_small (a * 256)) by lia.
  change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia.
  assert (L := lor_lt_pow2 (a * 256) b 16 ltac:(lia) ltac:(lia)).
  rewrite (Z.mod_small (Z.lor (a * 256) b)) by lia.
  replace (a * 2 ^ 8) with (a * 256) by lia.
  rewrite Z.lor_assoc, Z.lor_comm. reflexivity.
Qed.

Lemma snez_sx : forall c, 0 <= c < 2 ^ 32 -> (0 <? bv_unsigned (sx32 (Z_to_bv 64 c))) = negb (c =? 0).
Proof.
  intros c Hc. destruct (Z.eqb_spec c 0) as [E|E].
  - subst c. vm_compute. reflexivity.
  - cbn [negb]. apply Z.ltb_lt. destruct (sx32_u32 c Hc) as [[_ H]|[_ H]]; rewrite H; lia.
Qed.

Ltac byte_tac2 := first [ byte_tac | (rewrite Z.lor_comm; byte_tac) ].

(** CHK with the want fields of the frame. *)
Ltac chk_go FR CH :=
  try replace (Z_to_bv 64 18446744073709551605) with (Z_to_bv 64 (-11)) in FR by (apply bv_eq; reflexivity);
  to_body FR;
  unfold chk_ok, st, body_regs in CH;
  lazymatch type of FR with rw_cells _ _ _ (body_cells _ ?K' ?c ?rem ?tl) =>
    eapply CH with (k := K') (c := c) (rem := rem) (tl := tl) end;
  [ eassumption | eassumption | eassumption | | eassumption | exact FR
  | refine (conj _ (conj _ (conj _ (conj _ _)))); eassumption ].

(** 0x14584 lw a0, a; bltu 0x7f, a0 -> E_RANGE; lw a1, b; bltu 0x3f, a1 -> E_RANGE; lw a2, c;
    key = a<<8 | b | 0x20000; want = 90 a (c?0x40:0)|b; j 0x14888: want_len = 3, want_key; j CHK. *)
Lemma codec_main_owe1 : S_owe1.
Proof.
  unfold S_owe1. intros e fuel HE CH.
  unfold owe_ok, st, body_regs.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s8' t3' t4' t5' t6' ops k od c rem tl m1
         HF HREC HK1 HND HRC W0 W1 W2 W3 HC FR HFR.
  replace (owe_pc 1) with 0x14584 by reflexivity.
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof HE as (_ & _ & _ & HLO & _).
  pose proof HREC as (Hk & Hpd & Hr & _ & _).
  unfold rdr_k, reader_ok in Hr. destruct Hr as (Ha & Hb & Hc & Hdl & _ & _ & Hn & _).
  pose proof (sx32_u32 (k_a k) Ha) as SXA. pose proof (sx32_u32 (k_b k) Hb) as SXB.
  pose proof (snez_sx (k_c k) Hc) as SN.
  destruct HFR as (SV & ST & MU & WM & HMI).
  unfold LLVM_CODEC_STACK in HLO, MU.
  pose proof ST as [Hlo0 _].
  unfold body_cells in FR. cbn [kcall_cells app] in FR.
  zstep. zstep. zstep.
  if_cases E1.
  - (* a > 0x7f *)
    zify_cond E1.
    do 2 zstep. chk_go FR CH.
    apply owe_want_range; [ | reflexivity | exact W1 | exact W2 | exact W3 ].
    unfold owe_k. cbn [k_kind k_a k_b k_c k_delta k_bytes k_n]. rewrite HK1. apply owe1_spec_rng. lia.
  - zify_cond E1.
    assert (Ha' : k_a k <= 0x7f) by lia.
    rewrite (sx32_lit (k_a k)) by lia.
    zstep. zstep. zstep.
    if_cases E2.
    + (* b > 0x3f *)
      zify_cond E2.
      do 2 zstep. chk_go FR CH.
      apply owe_want_range; [ | reflexivity | exact W1 | exact W2 | exact W3 ].
      unfold owe_k. cbn [k_kind k_a k_b k_c k_delta k_bytes k_n]. rewrite HK1. apply owe1_spec_rng. lia.
    + zify_cond E2.
      assert (Hb' : k_b k <= 0x3f) by lia.
      rewrite (sx32_lit (k_b k)) by lia.
      destruct (Z.eqb_spec (k_c k) 0) as [Hc0 | Hc0];
        [ assert (Hceq : (k_c k =? 0) = true) by (apply Z.eqb_eq; exact Hc0)
        | assert (Hceq : (k_c k =? 0) = false) by (apply Z.eqb_neq; exact Hc0) ];
        try rewrite Hceq in SN; cbn [negb] in SN.
      all: do 6 zstep; rewrite SN; cbn [Z.b2z]; do 11 zstep.
      all: chk_go FR CH.
      all: apply (owe_want_succ _ _ [0x90; u8 (k_a k); u8 (Z.lor (bit_or_0 (negb (k_c k =? 0)) 0x40) (k_b k))]
                             (KEY 2 (Z.lor ((k_a k * 256) mod 2 ^ 32) (k_b k))) 0);
        [ unfold owe_k; cbn [k_kind k_a k_b k_c k_delta k_bytes k_n]; rewrite HK1; apply owe1_spec_ok; lia
        | exact W0
        | reflexivity
        |
        | cbn [k_want_key]; apply key1; lia
        | exact W3 ].
      all: rewrite Hceq; cbn [negb bit_or_0].
      all: cbn [k_want cells_bytes cbytes app firstn length bz map].
      all: repeat (apply f_equal2; [ byte_tac2 | ]); reflexivity.
Qed.
