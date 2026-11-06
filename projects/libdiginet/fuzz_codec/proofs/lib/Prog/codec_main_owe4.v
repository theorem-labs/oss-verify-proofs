From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree codec_cells codec_img
  codec_main_inv LLVMFuzzerTestOneInput_c codec_main_owe_lib codec_main_owe34_lib.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** CHK with the want fields of the frame. *)
Ltac chk_go FR CH :=
  try replace (Z_to_bv 64 18446744073709551605) with (Z_to_bv 64 (-11)) in FR by (apply bv_eq; reflexivity);
  to_body FR;
  unfold chk_ok, st, body_regs in CH;
  lazymatch type of FR with rw_cells _ _ _ (body_cells _ ?K' ?c ?rem ?tl) =>
    eapply CH with (k := K') (c := c) (rem := rem) (tl := tl) end;
  [ eassumption | eassumption | eassumption | | eassumption | exact FR
  | refine (conj _ (conj _ (conj _ (conj _ _)))); eassumption ].

(** 0x14420 lw a0, delta; addiw a1, a0, -0x40; bltu a1, -0x80 -> E_RANGE; a0 = delta+0x40; ld a1, FP+0 (B0 5C);
    0x14520 sh a1, want[0..2); sb a0, want[2]; 0x14528 want_len = 3, want_key = 0x80000; j CHK. *)
Lemma codec_main_owe4 : S_owe4.
Proof.
  unfold S_owe4. intros e fuel HE CH.
  unfold owe_ok, st, body_regs.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s8' t3' t4' t5' t6' ops k od c rem tl m1
         HF HREC HK0 HND HRC W0 W1 W2 W3 HC FR HFR.
  replace (owe_pc 4) with 0x14420 by reflexivity.
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof HE as (_ & _ & _ & HLO & _).
  pose proof HREC as (Hk & Hpd & Hr & _ & _).
  unfold rdr_k, reader_ok in Hr. destruct Hr as (Ha & Hb & Hc & Hdl & _ & _ & Hn & _).
  destruct HFR as (SV & ST & MU & WM & HMI).
  unfold LLVM_CODEC_STACK in HLO, MU.
  pose proof ST as [Hlo0 _].
  unfold body_cells in FR. cbn [kcall_cells app] in FR.
  zstep. rewrite (sx32_lit (k_delta k)) by lia.
  zstep. zstep. zstep.
  if_cases E2.
  - (* delta outside [-64, 63] *)
    zify_cond E2. apply delta_out in E2; [ | lia ].
    do 2 zstep. chk_go FR CH.
    apply owe_want_range; [ | reflexivity | exact W1 | exact W2 | exact W3 ].
    unfold owe_k. cbn [k_kind k_a k_b k_c k_delta k_bytes k_n]. rewrite HK0. apply owe4_spec_rng. lia.
  - zify_cond E2. apply delta_in in E2; [ | lia ].
    do 10 zstep.
    chk_go FR CH.
    apply (owe_want_succ _ _ [0xb0; 0x5c; u8 (k_delta k + 64)] (KEY 8 0) 0).
    + unfold owe_k. cbn [k_kind k_a k_b k_c k_delta k_bytes k_n]. rewrite HK0. apply owe4_spec_ok; lia.
    + exact W0.
    + reflexivity.
    + cbn [k_want cells_bytes cbytes app]. rewrite le2_b05c.
      cbn [app firstn length bz map].
      repeat (apply f_equal2; [ first [ reflexivity | byte_tac ] | ]). reflexivity.
    + cbn [k_want_key]. rewrite key8. reflexivity.
    + exact W3.
Qed.
