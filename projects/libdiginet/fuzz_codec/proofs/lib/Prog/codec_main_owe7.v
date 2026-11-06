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

(** owe()'s STRIP_LEDS case (fuzz_codec.c:202-207, owe_sysex with function 0x20). *)
Lemma owe7_spec_ok : forall d a b c delta bytes n, a < d_strips d -> b <= 0x7f ->
  owe_spec 7 (Some d) a b c delta bytes n =
  (0, ([0xf0; 0x13; u8 (d_dev d); u8 0x20; u8 a; u8 b; 0xf7], KEY 5 a, 0)).
Proof.
  intros d a b c delta bytes n Ha Hb. unfold owe_spec. cbv beta iota zeta.
  destruct (Z.leb_spec (d_strips d) a); [lia|]. destruct (Z.ltb_spec 0x7f b); [lia|]. reflexivity.
Qed.

Lemma owe7_spec_rng : forall d a b c delta bytes n, d_strips d <= a \/ 0x7f < b ->
  fst (owe_spec 7 (Some d) a b c delta bytes n) = E_RANGE.
Proof.
  intros d a b c delta bytes n H. unfold owe_spec. cbv beta iota zeta.
  destruct (Z.leb_spec (d_strips d) a); destruct (Z.ltb_spec 0x7f b); try reflexivity; lia.
Qed.

Lemma key5 : forall a, 0 <= a < 65536 -> Z.lor a 327680 = KEY 5 a.
Proof.
  intros a Ha. unfold KEY. change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia.
  rewrite (Z.mod_small a) by lia. rewrite Z.lor_comm. reflexivity.
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

(** 0x14574 lw a0, a; lbu a1, strips; bltu a0, a1 -> 0x147f4, else j E_RANGE; 0x147f4 lw a1, b;
    bgeu 0x7f, a1 -> 0x14850, else E_RANGE; 0x14850 lbu a2, dev; want_display = 0; key = 0x50000|a;
    want = F0 13 dev 20 a b F7; want_len = 7; want_key; j CHK. *)
Lemma codec_main_owe7 : S_owe7.
Proof.
  unfold S_owe7. intros e fuel HE CH.
  unfold owe_ok, st, body_regs.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s8' t3' t4' t5' t6' ops k od c rem tl m1
         HF HREC HK7 HND HRC W0 W1 W2 W3 HC FR HFR.
  replace (owe_pc 7) with 0x14574 by reflexivity.
  destruct od as [d|]; [ | exfalso; destruct (HND eq_refl) as [H|[H|H]]; lia ].
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof HE as (_ & _ & _ & HLO & _).
  pose proof HREC as (Hk & Hpd & Hr & _ & _).
  pose proof (pd_range _ _ _ Hpd) as [Hp Hd].
  pose proof (desk_rng _ _ _ Hpd) as (Rdev & Rstr & Rch & Rcnt).
  pose proof (desk_strips_rd e m1 _ _ d HE HFR Hpd) as RD9.
  pose proof (desk_dev_rd e m1 _ _ d HE HFR Hpd) as RD8.
  assert (BS : bv_unsigned (b8 (d_strips d)) = d_strips d) by (apply b8_small; lia).
  assert (BD : bv_unsigned (b8 (d_dev d)) = d_dev d) by (apply b8_small; lia).
  assert (UD : bv_unsigned (Z_to_bv 64 (k_desk k)) = k_desk k) by (apply unsigned_lit; lia).
  unfold rdr_k, reader_ok in Hr. destruct Hr as (Ha & Hb & Hc & Hdl & _ & _ & Hn & _).
  pose proof (sx32_u32 (k_a k) Ha) as SXA. pose proof (sx32_u32 (k_b k) Hb) as SXB.
  destruct HFR as (SV & ST & MU & WM & HMI).
  unfold LLVM_CODEC_STACK in HLO, MU.
  pose proof ST as [Hlo0 _].
  unfold body_cells in FR. cbn [kcall_cells app] in FR.
  zstep. zstep.
  rewrite ?BS.
  zstep.
  if_cases E1.
  2: { (* a >= strips: j E_RANGE *)
    zify_cond E1.
    do 3 zstep. chk_go FR CH.
    apply owe_want_range; [ | reflexivity | exact W1 | exact W2 | exact W3 ].
    unfold owe_k. cbn [k_kind k_a k_b k_c k_delta k_bytes k_n]. rewrite HK7. apply owe7_spec_rng. lia. }
  zify_cond E1.
  assert (Ha' : k_a k < d_strips d) by lia.
  rewrite (sx32_lit (k_a k)) by lia.
  zstep. zstep. zstep.
  if_cases E2.
  2: { (* b > 0x7f *)
    zify_cond E2.
    do 2 zstep. chk_go FR CH.
    apply owe_want_range; [ | reflexivity | exact W1 | exact W2 | exact W3 ].
    unfold owe_k. cbn [k_kind k_a k_b k_c k_delta k_bytes k_n]. rewrite HK7. apply owe7_spec_rng. lia. }
  zify_cond E2.
  assert (Hb' : k_b k <= 0x7f) by lia.
  rewrite (sx32_lit (k_b k)) by lia.
  zstep.
  rewrite ?BD.
  do 16 zstep.
  chk_go FR CH.
  apply (owe_want_succ _ _ [0xf0; 0x13; u8 (d_dev d); u8 0x20; u8 (k_a k); u8 (k_b k); 0xf7] (KEY 5 (k_a k)) 0);
    [ unfold owe_k; cbn [k_kind k_a k_b k_c k_delta k_bytes k_n]; rewrite HK7; apply owe7_spec_ok; lia
    | exact W0
    | reflexivity
    |
    | cbn [k_want_key]; apply key5; lia
    | reflexivity ].
  cbn [k_want cells_bytes cbytes app firstn length bz map le2 Z_to_le_bytes].
  repeat (apply f_equal2; [ byte_tac2 | ]); reflexivity.
Qed.
