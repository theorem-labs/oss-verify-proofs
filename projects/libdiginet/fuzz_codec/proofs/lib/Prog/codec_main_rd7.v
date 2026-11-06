From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_main_inv
  diginet_strip_leds_encode_c LLVMFuzzerTestOneInput_c codec_main_rda_lib.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Section RD7.
Variable e : env.
Variable fuel : nat.
Hypothesis HE : env_ok e.
Hypothesis JN : join_ok e fuel.
Hypothesis SLEDS : diginet_strip_leds_encode_contract.

(** 0x13eb4-0x13edc: b = lo | hi << 16 stored, a and b reloaded, diginet_strip_leds_encode(k.p, a, b, &k.out), to JOIN. *)
Lemma rd7_fin : forall (ra' t0' t1' t2' a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops : word)
    (x1 x2 x3 x4 va pv dv : Z) (od : option desk) (cur rem : Z) (tl : list byte) (m : word -> option byte),
  rw_cells rsegs m (bv_unsigned (e_sp e) + -400) (rd_cells 7 pv dv va 0 0 0 cur rem tl) ->
  fuel_ok ops (S fuel) -> pd_ok pv dv od -> 0 <= va < 2 ^ 32 ->
  0 <= x1 < 2 ^ 16 -> 0 <= x2 < 2 ^ 16 -> 0 <= x3 < 2 ^ 16 -> 0 <= x4 < 2 ^ 16 ->
  bv_unsigned (e_p e) <= cur -> 0 <= rem -> cur - bv_unsigned (e_p e) + rem = Z.of_nat (length (e_data e)) ->
  fr_ok e m ->
  evt rsegs (Qk e)
    (st e (body_regs e ra' t0' t1' t2' (Z_to_bv 64 x4) (Z_to_bv 64 x1) (Z_to_bv 64 x2) (Z_to_bv 64 x3) a4' a5' a6' a7'
                     (Z_to_bv 64 pv) ops s8' s10' t3' t4' t5' t6') 0x13eb4 m).
Proof.
  intros ra' t0' t1' t2' a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops x1 x2 x3 x4 va pv dv od cur rem tl m
    FR HF HPD Hva H1 H2 H3 H4 Hc0 Hr0 Hcr HFR.
  unfold st, body_regs. rd_setup HE HFR. unfold rd_cells in FR.
  do 5 zstep.
  match type of FR with context [C4 (Z_to_bv 64 (Z.lor ?X ?Y))] => set (vb := Z.lor X Y) in * end.
  assert (Hvb : 0 <= vb < 2 ^ 32) by (unfold vb; apply cmp_range; assumption).
  clearbody vb.
  do 4 zstep.
  lazymatch goal with FR : rw_cells _ ?mm _ _ |- _ =>
    pose proof (rd_cells_body e mm _ 7 pv dv va vb 0 0 cur rem tl FR) as FB end.
  clear FR.
  zstep.
  destruct (body_out_split _ _ _ _ _ _ _ FB) as (P1 & PO & P2). clear FB.
  unfold k_enc in PO, P1. unfold body_pre in P1.
  cbn [k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before k_out] in PO, P1.
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -276)) = bv_unsigned (e_sp e) + -276)
    by (apply unsigned_lit; lia).
  pose proof SLEDS as C. unfold diginet_strip_leds_encode_contract, DIGINET_STRIP_LEDS_ENCODE in C.
  call C.
  { unfold diginet_strip_leds_encode_pre. rewrite USP.
    split; [ apply (pers_arg_of_pd _ pv dv od); [ exact (relro_of_munch e _ HE MU) | exact HPD ] | ].
    split; [ apply arg_u32_sx; exact Hva | ].
    split; [ apply arg_u32_sx; exact Hvb | ].
    split; [ lia | ].
    split; [ replace (bv_unsigned (e_sp e) + -276) with (bv_unsigned (e_sp e) + -400 + 124) by lia; exact PO
           | assumption ]. }
  match goal with H : mem_inv rsegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into HMI end.
  match goal with H : context [strip_leds_spec] |- _ => revert H end.
  destruct (strip_leds_spec od va vb) as [rc o] eqn:EF. intros HP. destruct HP as [Ea0 HO].
  match type of Ea0 with ?v = _ => subst v end.
  rewrite USP in HO.
  zstep.
  set (K := set_out (k_enc 7 pv dv va vb 0 0) (cmd_out (fa5 32) o)).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (FJ : rw_cells rsegs mm (bv_unsigned (e_sp e) + -400) (body_cells e K (cur - bv_unsigned (e_p e)) rem tl))
  end.
  { apply body_out_join; [ exact P1 | | exact P2 ].
    replace (bv_unsigned (e_sp e) + -400 + 124) with (bv_unsigned (e_sp e) + -276) by lia. exact HO. }
  assert (EK : enc_k K od = strip_leds_spec od va vb) by reflexivity.
  replace (Z_to_bv 64 rc) with (Z_to_bv 64 (fst (enc_k K od))) by (rewrite EK, EF; reflexivity).
  pose proof JN as J. unfold join_ok, st, body_regs in J.
  eapply J; [ exact HF | | | exact FJ | exact (conj SV (conj ST (conj MU (conj WM HMI)))) ].
  - unfold rec_ok, rdr_k. rewrite EK, EF. cbn [snd]. unfold K.
    cbn [set_out k_enc k_kind k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_before k_out].
    split; [lia|]. split; [exact HPD|]. split; [apply rdr_zero; lia|]. split; reflexivity.
  - unfold cur_ok. lia.
Qed.

(** 0x13e18-0x13e2c: a = lo | hi << 16 stored; 0x13e2c: the read of b (in.n = rem bytes left), to 0x13eb4. *)
Lemma rd7_mid : forall (ra' t0' t1' t2' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops : word)
    (x1 x2 x3 x4 pv dv : Z) (od : option desk) (cur rem : Z) (tl : list byte) (m : word -> option byte),
  rw_cells rsegs m (bv_unsigned (e_sp e) + -400) (rd_cells 7 pv dv 0 0 0 0 cur rem tl) ->
  fuel_ok ops (S fuel) -> pd_ok pv dv od ->
  0 <= x1 < 2 ^ 16 -> 0 <= x2 < 2 ^ 16 -> 0 <= x3 < 2 ^ 16 -> 0 <= x4 < 2 ^ 16 ->
  bv_unsigned (e_p e) <= cur -> 0 <= rem -> cur - bv_unsigned (e_p e) + rem = Z.of_nat (length (e_data e)) ->
  fr_ok e m ->
  evt rsegs (Qk e)
    (st e (body_regs e ra' t0' t1' t2' (Z_to_bv 64 rem) (Z_to_bv 64 x1) (Z_to_bv 64 x2) (Z_to_bv 64 x3) (Z_to_bv 64 x4)
                     a5' a6' a7' (Z_to_bv 64 pv) ops s8' s10' t3' t4' t5' t6') 0x13e18 m).
Proof.
  intros ra' t0' t1' t2' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops x1 x2 x3 x4 pv dv od cur rem tl m
    FR HF HPD H1 H2 H3 H4 Hc0 Hr0 Hcr HFR.
  unfold st, body_regs. rd_setup HE HFR. unfold rd_cells in FR.
  do 5 zstep.
  match type of FR with context [C4 (Z_to_bv 64 (Z.lor ?X ?Y))] => set (va := Z.lor X Y) in * end.
  assert (Hva : 0 <= va < 2 ^ 32) by (unfold va; apply cmp_range; assumption).
  clearbody va.
  destruct (rem_cases rem Hr0) as [R | [R | [R | [R | R]]]]; try subst rem.
  all: drive 0x13eb4.
  all: eapply rd7_fin; [ exact FR | rd_side .. ].
Qed.

(** 0x136d4: the read of a, to 0x13e18. *)
Lemma rd7_rd : rd_ok e 7 fuel.
Proof.
  unfold rd_ok, st, body_regs.
  intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops pv dv od c rem tl m1
    HF HPD HC FR HFR.
  change (rd_pc 7) with 0x136d4.
  rd_setup HE HFR. destruct HC as (Hc0 & Hr0 & Hcr).
  unfold body_cells, k_rd in FR.
  cbn [kcall_cells app k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before k_out k_want_rc k_want
       k_want_len k_want_key k_want_display] in FR.
  destruct (rem_cases rem Hr0) as [R | [R | [R | [R | R]]]]; try subst rem.
  all: drive 0x13e18.
  all: eapply rd7_mid; [ exact FR | rd_side .. ].
Qed.

End RD7.

Lemma codec_main_rd7 : S_rd7.
Proof. unfold S_rd7. intros SLEDS e fuel HE JN. eapply rd7_rd; eassumption. Qed.
