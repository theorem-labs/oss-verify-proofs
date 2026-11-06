From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_main_inv
  diginet_vpot_encode_c LLVMFuzzerTestOneInput_c codec_main_rda_lib.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** The delta field holds the u32 the reader composed; as the int (int) d its 4 bytes are the same. *)
Lemma body_pre_s32 : forall m A kind pv dv a b c d, 0 <= d < 2 ^ 32 ->
  rw_cells rsegs m A (body_pre (k_enc kind pv dv a b c d)) ->
  rw_cells rsegs m A (body_pre (k_enc kind pv dv a b c (s32 d))).
Proof.
  intros m A kind pv dv a b c d Hd H. eapply rw_cells_same; [ | | | exact H ].
  - unfold body_pre, k_enc. cbn. repeat split.
  - unfold body_pre, k_enc.
    cbn [k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before cells_bytes cbytes].
    rewrite le4_s32 by exact Hd. reflexivity.
  - reflexivity.
Qed.

Section RD3.
Variable e : env.
Variable fuel : nat.
Hypothesis HE : env_ok e.
Hypothesis JN : join_ok e fuel.
Hypothesis VPOT : diginet_vpot_encode_contract.

(** 0x13de0-0x13e08: delta = lo | hi << 16 stored, a and delta reloaded, diginet_vpot_encode(k.p, a, delta, &k.out), to JOIN. *)
Lemma rd3_fin : forall (ra' t0' t1' t2' a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops : word)
    (x1 x2 x3 x4 va pv dv : Z) (od : option desk) (cur rem : Z) (tl : list byte) (m : word -> option byte),
  rw_cells rsegs m (bv_unsigned (e_sp e) + -400) (rd_cells 3 pv dv va 0 0 0 cur rem tl) ->
  fuel_ok ops (S fuel) -> pd_ok pv dv od -> 0 <= va < 2 ^ 32 ->
  0 <= x1 < 2 ^ 16 -> 0 <= x2 < 2 ^ 16 -> 0 <= x3 < 2 ^ 16 -> 0 <= x4 < 2 ^ 16 ->
  bv_unsigned (e_p e) <= cur -> 0 <= rem -> cur - bv_unsigned (e_p e) + rem = Z.of_nat (length (e_data e)) ->
  fr_ok e m ->
  evt rsegs (Qk e)
    (st e (body_regs e ra' t0' t1' t2' (Z_to_bv 64 x4) (Z_to_bv 64 x1) (Z_to_bv 64 x2) (Z_to_bv 64 x3) a4' a5' a6' a7'
                     (Z_to_bv 64 pv) ops s8' s10' t3' t4' t5' t6') 0x13de0 m).
Proof.
  intros ra' t0' t1' t2' a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops x1 x2 x3 x4 va pv dv od cur rem tl m
    FR HF HPD Hva H1 H2 H3 H4 Hc0 Hr0 Hcr HFR.
  unfold st, body_regs. rd_setup HE HFR. unfold rd_cells in FR.
  do 5 zstep.
  match type of FR with context [C4 (Z_to_bv 64 (Z.lor ?X ?Y))] => set (vd := Z.lor X Y) in * end.
  assert (Hvd : 0 <= vd < 2 ^ 32) by (unfold vd; apply cmp_range; assumption).
  clearbody vd.
  do 4 zstep.
  lazymatch goal with FR : rw_cells _ ?mm _ _ |- _ =>
    pose proof (rd_cells_body e mm _ 3 pv dv va 0 0 vd cur rem tl FR) as FB end.
  clear FR.
  zstep.
  destruct (body_out_split _ _ _ _ _ _ _ FB) as (P1 & PO & P2). clear FB.
  unfold k_enc in PO, P1. unfold body_pre in P1.
  cbn [k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before k_out] in PO, P1.
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -276)) = bv_unsigned (e_sp e) + -276)
    by (apply unsigned_lit; lia).
  pose proof VPOT as C. unfold diginet_vpot_encode_contract, DIGINET_VPOT_ENCODE in C.
  call C.
  { unfold diginet_vpot_encode_pre. rewrite USP.
    split; [ apply (pers_arg_of_pd _ pv dv od); [ exact (relro_of_munch e _ HE MU) | exact HPD ] | ].
    split; [ apply arg_u32_sx; exact Hva | ].
    split; [ apply arg_s32_sx; exact Hvd | ].
    split; [ lia | ].
    split; [ replace (bv_unsigned (e_sp e) + -276) with (bv_unsigned (e_sp e) + -400 + 124) by lia; exact PO
           | assumption ]. }
  match goal with H : mem_inv rsegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into HMI end.
  match goal with H : context [vpot_spec] |- _ => revert H end.
  destruct (vpot_spec od va (s32 vd)) as [rc o] eqn:EF. intros HP. destruct HP as [Ea0 HO].
  match type of Ea0 with ?v = _ => subst v end.
  rewrite USP in HO.
  zstep.
  pose proof (body_pre_s32 _ _ 3 pv dv va 0 0 vd Hvd P1) as P1'. clear P1.
  set (K := set_out (k_enc 3 pv dv va 0 0 (s32 vd)) (cmd_out (fa5 32) o)).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (FJ : rw_cells rsegs mm (bv_unsigned (e_sp e) + -400) (body_cells e K (cur - bv_unsigned (e_p e)) rem tl))
  end.
  { apply body_out_join; [ exact P1' | | exact P2 ].
    replace (bv_unsigned (e_sp e) + -400 + 124) with (bv_unsigned (e_sp e) + -276) by lia. exact HO. }
  assert (EK : enc_k K od = vpot_spec od va (s32 vd)) by reflexivity.
  replace (Z_to_bv 64 rc) with (Z_to_bv 64 (fst (enc_k K od))) by (rewrite EK, EF; reflexivity).
  pose proof JN as J. unfold join_ok, st, body_regs in J.
  eapply J; [ exact HF | | | exact FJ | exact (conj SV (conj ST (conj MU (conj WM HMI)))) ].
  - unfold rec_ok, rdr_k. rewrite EK, EF. cbn [snd]. unfold K.
    cbn [set_out k_enc k_kind k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_before k_out].
    split; [lia|]. split; [exact HPD|]. split; [apply rdr_zero; first [lia | apply s32_range; lia] |].
    split; reflexivity.
  - unfold cur_ok. lia.
Qed.

(** 0x13d44-0x13d58: a = lo | hi << 16 stored; 0x13d58: the read of delta (in.n = rem bytes left), to 0x13de0. *)
Lemma rd3_mid : forall (ra' t0' t1' t2' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops : word)
    (x1 x2 x3 x4 pv dv : Z) (od : option desk) (cur rem : Z) (tl : list byte) (m : word -> option byte),
  rw_cells rsegs m (bv_unsigned (e_sp e) + -400) (rd_cells 3 pv dv 0 0 0 0 cur rem tl) ->
  fuel_ok ops (S fuel) -> pd_ok pv dv od ->
  0 <= x1 < 2 ^ 16 -> 0 <= x2 < 2 ^ 16 -> 0 <= x3 < 2 ^ 16 -> 0 <= x4 < 2 ^ 16 ->
  bv_unsigned (e_p e) <= cur -> 0 <= rem -> cur - bv_unsigned (e_p e) + rem = Z.of_nat (length (e_data e)) ->
  fr_ok e m ->
  evt rsegs (Qk e)
    (st e (body_regs e ra' t0' t1' t2' (Z_to_bv 64 rem) (Z_to_bv 64 x1) (Z_to_bv 64 x2) (Z_to_bv 64 x3) (Z_to_bv 64 x4)
                     a5' a6' a7' (Z_to_bv 64 pv) ops s8' s10' t3' t4' t5' t6') 0x13d44 m).
Proof.
  intros ra' t0' t1' t2' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops x1 x2 x3 x4 pv dv od cur rem tl m
    FR HF HPD H1 H2 H3 H4 Hc0 Hr0 Hcr HFR.
  unfold st, body_regs. rd_setup HE HFR. unfold rd_cells in FR.
  do 5 zstep.
  match type of FR with context [C4 (Z_to_bv 64 (Z.lor ?X ?Y))] => set (va := Z.lor X Y) in * end.
  assert (Hva : 0 <= va < 2 ^ 32) by (unfold va; apply cmp_range; assumption).
  clearbody va.
  destruct (rem_cases rem Hr0) as [R | [R | [R | [R | R]]]]; try subst rem.
  all: drive 0x13de0.
  all: eapply rd3_fin; [ exact FR | rd_side .. ].
Qed.

(** 0x13660: the read of a, to 0x13d44. *)
Lemma rd3_rd : rd_ok e 3 fuel.
Proof.
  unfold rd_ok, st, body_regs.
  intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops pv dv od c rem tl m1
    HF HPD HC FR HFR.
  change (rd_pc 3) with 0x13660.
  rd_setup HE HFR. destruct HC as (Hc0 & Hr0 & Hcr).
  unfold body_cells, k_rd in FR.
  cbn [kcall_cells app k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before k_out k_want_rc k_want
       k_want_len k_want_key k_want_display] in FR.
  destruct (rem_cases rem Hr0) as [R | [R | [R | [R | R]]]]; try subst rem.
  all: drive 0x13d44.
  all: eapply rd3_mid; [ exact FR | rd_side .. ].
Qed.

End RD3.

Lemma codec_main_rd3 : S_rd3.
Proof. unfold S_rd3. intros VPOT e fuel HE JN. eapply rd3_rd; eassumption. Qed.
