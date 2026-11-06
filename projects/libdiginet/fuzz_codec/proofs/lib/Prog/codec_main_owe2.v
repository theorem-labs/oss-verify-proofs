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

(** owe()'s TOUCH case (fuzz_codec.c:158-161). *)
Lemma owe2_spec_ok : forall d a b c delta bytes n, a < d_strips d ->
  owe_spec 2 (Some d) a b c delta bytes n =
  (0, ([0x90; 0x09; u8 (Z.lor (bit_or_0 (negb (c =? 0)) 0x40) a)], KEY 8 0, 0)).
Proof.
  intros d a b c delta bytes n Ha. unfold owe_spec. cbv beta iota zeta.
  destruct (Z.leb_spec (d_strips d) a); [lia|]. reflexivity.
Qed.

Lemma owe2_spec_rng : forall d a b c delta bytes n, d_strips d <= a ->
  fst (owe_spec 2 (Some d) a b c delta bytes n) = E_RANGE.
Proof.
  intros d a b c delta bytes n H. unfold owe_spec. cbv beta iota zeta.
  destruct (Z.leb_spec (d_strips d) a); [reflexivity | lia].
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

(** 0x144fc lw a0, a; lbu a1, strips; bgeu -> E_RANGE; lw a1, c; a0 = (c?0x40:0)|a; a1 = 0x990;
    0x14520 sh a1, want[0..1] (90 09); sb a0, want[2]; want_len = 3; want_key = 0x80000; j CHK. *)
Lemma codec_main_owe2 : S_owe2.
Proof.
  unfold S_owe2. intros e fuel HE CH.
  unfold owe_ok, st, body_regs.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s8' t3' t4' t5' t6' ops k od c rem tl m1
         HF HREC HK2 HND HRC W0 W1 W2 W3 HC FR HFR.
  replace (owe_pc 2) with 0x144fc by reflexivity.
  destruct od as [d|]; [ | exfalso; destruct (HND eq_refl) as [H|[H|H]]; lia ].
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof HE as (_ & _ & _ & HLO & _).
  pose proof HREC as (Hk & Hpd & Hr & _ & _).
  pose proof (pd_range _ _ _ Hpd) as [Hp Hd].
  pose proof (desk_rng _ _ _ Hpd) as (Rdev & Rstr & Rch & Rcnt).
  pose proof (desk_strips_rd e m1 _ _ d HE HFR Hpd) as RD9.
  assert (BS : bv_unsigned (b8 (d_strips d)) = d_strips d) by (apply b8_small; lia).
  assert (UD : bv_unsigned (Z_to_bv 64 (k_desk k)) = k_desk k) by (apply unsigned_lit; lia).
  unfold rdr_k, reader_ok in Hr. destruct Hr as (Ha & Hb & Hc & Hdl & _ & _ & Hn & _).
  pose proof (sx32_u32 (k_a k) Ha) as SXA.
  pose proof (snez_sx (k_c k) Hc) as SN.
  destruct HFR as (SV & ST & MU & WM & HMI).
  unfold LLVM_CODEC_STACK in HLO, MU.
  pose proof ST as [Hlo0 _].
  unfold body_cells in FR. cbn [kcall_cells app] in FR.
  zstep. zstep.
  rewrite ?BS.
  zstep.
  if_cases E1.
  - (* a >= strips *)
    zify_cond E1.
    do 2 zstep. chk_go FR CH.
    apply owe_want_range; [ | reflexivity | exact W1 | exact W2 | exact W3 ].
    unfold owe_k. cbn [k_kind k_a k_b k_c k_delta k_bytes k_n]. rewrite HK2. apply owe2_spec_rng. lia.
  - zify_cond E1.
    assert (Ha' : k_a k < d_strips d) by lia.
    rewrite (sx32_lit (k_a k)) by lia.
    destruct (Z.eqb_spec (k_c k) 0) as [Hc0 | Hc0];
      [ assert (Hceq : (k_c k =? 0) = true) by (apply Z.eqb_eq; exact Hc0)
      | assert (Hceq : (k_c k =? 0) = false) by (apply Z.eqb_neq; exact Hc0) ];
      try rewrite Hceq in SN; cbn [negb] in SN.
    all: do 2 zstep; rewrite SN; cbn [Z.b2z]; do 11 zstep.
    all: chk_go FR CH.
    all: apply (owe_want_succ _ _ [0x90; 0x09; u8 (Z.lor (bit_or_0 (negb (k_c k =? 0)) 0x40) (k_a k))]
                           (KEY 8 0) 0);
      [ unfold owe_k; cbn [k_kind k_a k_b k_c k_delta k_bytes k_n]; rewrite HK2; apply owe2_spec_ok; lia
      | exact W0
      | reflexivity
      |
      | reflexivity
      | exact W3 ].
    all: rewrite Hceq; cbn [negb bit_or_0].
    all: cbn [k_want cells_bytes cbytes app firstn length bz map le2 Z_to_le_bytes].
    all: repeat (apply f_equal2; [ byte_tac2 | ]); reflexivity.
Qed.
