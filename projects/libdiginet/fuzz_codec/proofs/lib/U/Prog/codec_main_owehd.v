From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells codec_img
  codec_main_inv codec_main_lib.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** The call record with want_key and want_display (both 0) as one 8-byte cell: owe()'s prologue
    clears them with one doubleword store. *)
Definition kc8 (k : kcall) : list cell :=
  [C4 (Z_to_bv 64 (k_kind k)); CB 4 (k_pad k); C8 (Z_to_bv 64 (k_p k)); C8 (Z_to_bv 64 (k_desk k));
   C4 (Z_to_bv 64 (k_a k)); C4 (Z_to_bv 64 (k_b k)); C4 (Z_to_bv 64 (k_c k)); C4 (Z_to_bv 64 (k_delta k));
   CB 24 (k_bytes k); C8 (Z_to_bv 64 (k_n k)); C4 (Z_to_bv 64 (k_rc k));
   CB 32 (k_before k); CB 32 (k_out k);
   C4 (Z_to_bv 64 (k_want_rc k)); CB 24 (k_want k); C8 (Z_to_bv 64 (k_want_len k));
   C8 (Z_to_bv 64 0)].

Lemma kc8_of : forall m A k, k_want_key k = 0 -> k_want_display k = 0 ->
  rw_cells rsegs m A (kcall_cells k) -> rw_cells rsegs m A (kc8 k).
Proof.
  intros m A k H1 H2 H. pose proof H as [[W _] _].
  apply (rw_cells_same_bytes m A (kcall_cells k) (kc8 k)); [ | | reflexivity | exact H].
  - unfold kcall_cells, kc8 in *. cbn [cells_wf cell_wf] in *. tauto.
  - unfold kcall_cells, kc8. rewrite H1, H2. reflexivity.
Qed.

Lemma kc8_to : forall m A k, k_want_key k = 0 -> k_want_display k = 0 ->
  rw_cells rsegs m A (kc8 k) -> rw_cells rsegs m A (kcall_cells k).
Proof.
  intros m A k H1 H2 H. pose proof H as [[W _] _].
  apply (rw_cells_same_bytes m A (kc8 k) (kcall_cells k)); [ | | reflexivity | exact H].
  - unfold kcall_cells, kc8 in *. cbn [cells_wf cell_wf] in *. tauto.
  - unfold kcall_cells, kc8. rewrite H1, H2. reflexivity.
Qed.

(** The record owe() hands its cases: k.rc holds the encoder's code, owe()'s fields are 0. *)
Lemma frk_run : forall m A k,
  k_want_rc k = 0 -> k_want_len k = 0 -> k_want_key k = 0 -> k_want_display k = 0 ->
  rw_cells rsegs m A
    [C4 (Z_to_bv 64 (k_kind k)); CB 4 (k_pad k); C8 (Z_to_bv 64 (k_p k)); C8 (Z_to_bv 64 (k_desk k));
     C4 (Z_to_bv 64 (k_a k)); C4 (Z_to_bv 64 (k_b k)); C4 (Z_to_bv 64 (k_c k)); C4 (Z_to_bv 64 (k_delta k));
     CB 24 (k_bytes k); C8 (Z_to_bv 64 (k_n k)); C4 (Z_to_bv 64 (fst (enc_k k)));
     CB 32 (k_before k); CB 32 (cmd_out (k_before k) (snd (enc_k k)));
     C4 (Z_to_bv 64 0); CB 24 (k_want k); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells rsegs m A (kcall_cells (k_run k)).
Proof.
  intros m A k H1 H2 H3 H4 H. apply kc8_to; [exact H3 | exact H4 |].
  unfold kc8, k_run, with_rc, with_out. cbn [k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc
    k_before k_out k_want_rc k_want k_want_len k_want_key k_want_display].
  rewrite H1, H2. exact H.
Qed.

(** The record of the return of fuzz_codec.c:132-133: want_rc = SPEC_E_ARG. *)
Lemma frk_earg : forall m A k,
  k_want_len k = 0 -> k_want_key k = 0 -> k_want_display k = 0 ->
  rw_cells rsegs m A
    [C4 (Z_to_bv 64 (k_kind k)); CB 4 (k_pad k); C8 (Z_to_bv 64 (k_p k)); C8 (Z_to_bv 64 (k_desk k));
     C4 (Z_to_bv 64 (k_a k)); C4 (Z_to_bv 64 (k_b k)); C4 (Z_to_bv 64 (k_c k)); C4 (Z_to_bv 64 (k_delta k));
     CB 24 (k_bytes k); C8 (Z_to_bv 64 (k_n k)); C4 (Z_to_bv 64 (fst (enc_k k)));
     CB 32 (k_before k); CB 32 (cmd_out (k_before k) (snd (enc_k k)));
     C4 (Z_to_bv 64 (-1)); CB 24 (k_want k); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells rsegs m A (kcall_cells (with_want_rc (k_run k) (-1))).
Proof.
  intros m A k H2 H3 H4 H. apply kc8_to; [exact H3 | exact H4 |].
  unfold kc8, with_want_rc, k_run, with_rc, with_out. cbn [k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes
    k_n k_rc k_before k_out k_want_rc k_want k_want_len k_want_key k_want_display].
  rewrite H2. exact H.
Qed.

Lemma needs_desk_true : forall kind, needs_desk kind = true -> kind <> 1 /\ kind <> 4 /\ kind <> 11.
Proof.
  intros kind H. unfold needs_desk in H.
  destruct (Z.eqb_spec kind 1); destruct (Z.eqb_spec kind 4); destruct (Z.eqb_spec kind 11);
    cbn in H; try discriminate H; lia.
Qed.

Lemma needs_desk_false : forall kind, needs_desk kind = false -> kind = 1 \/ kind = 4 \/ kind = 11.
Proof.
  intros kind H. unfold needs_desk in H.
  destruct (Z.eqb_spec kind 1); destruct (Z.eqb_spec kind 4); destruct (Z.eqb_spec kind 11);
    cbn in H; try discriminate H; lia.
Qed.

(** 0x144e4-0x144f4: the bit [kind] of 0x812 (BUTTON, JOG, SYSEX) is 0 exactly when the kind needs a desk. *)
Lemma bit812 : forall kind, 0 <= kind <= 11 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr 2066 (bv_unsigned (Z_to_bv 64 kind) mod 64)))) 1))
         (Z_to_bv 64 0) = needs_desk kind.
Proof.
  intros kind H.
  assert (E : kind = 0 \/ kind = 1 \/ kind = 2 \/ kind = 3 \/ kind = 4 \/ kind = 5 \/ kind = 6 \/
              kind = 7 \/ kind = 8 \/ kind = 9 \/ kind = 10 \/ kind = 11) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]; vm_compute; reflexivity.
Qed.

Lemma od_ok_of : forall k, desk_at k -> od_ok (od_of k).
Proof.
  unfold desk_at, od_of, od_ok, SDESK_C24, SDESK_PC.
  intros k [[_ E]|[[_ E]|[_ E]]]; rewrite E; cbn.
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. reflexivity.
Qed.

(** owe() on a record that needs a desk and has none: SPEC_E_ARG (fuzz_codec.c:132-133). *)
Lemma owe_k_none : forall k, k_desk k = 0 -> needs_desk (k_kind k) = true -> fst (owe_k k) = E_ARG.
Proof.
  intros k H1 H2. unfold owe_k, owe_spec, od_of. rewrite H1. unfold needs_desk in H2. rewrite H2.
  reflexivity.
Qed.

(** ... and the library agrees: its encoder returned E_ARG too. *)
Lemma enc_k_none : forall k, 0 <= k_kind k <= 11 -> desk_at k ->
  reader_ok (k_kind k) (k_a k) (k_b k) (k_c k) (k_delta k) (zb (k_bytes k)) (k_n k) ->
  k_desk k = 0 -> needs_desk (k_kind k) = true -> fst (enc_k k) = E_ARG.
Proof.
  intros k HK HD HR H1 H2.
  pose proof (agree_all (k_kind k) (od_of k) (k_a k) (k_b k) (k_c k) (k_delta k) (zb (k_bytes k)) (k_n k)
                HK (od_ok_of k HD) HR) as A.
  pose proof (owe_k_none k H1 H2) as O. unfold owe_k in O.
  unfold agrees in A. unfold enc_k.
  destruct (enc_of_call (k_kind k) (od_of k) (k_a k) (k_b k) (k_c k) (k_delta k) (zb (k_bytes k)) (k_n k))
    as [rc o].
  destruct A as [A _]. cbn [fst]. congruence.
Qed.

Lemma enc_k_wrc : forall k w, enc_k (with_want_rc (k_run k) w) = enc_k k.
Proof. reflexivity. Qed.

Lemma owe_k_wrc : forall k w, owe_k (with_want_rc (k_run k) w) = owe_k k.
Proof. reflexivity. Qed.

(** The record of the E_ARG return satisfies what the checks need. *)
Lemma chk_wf_earg : forall k, rec_wf k -> k_desk k = 0 -> needs_desk (k_kind k) = true ->
  chk_wf (with_want_rc (k_run k) (-1)).
Proof.
  intros k WF HD0 ND.
  pose proof WF as (HK & HDK & HBF & HOUT & HRC & HWRC & HWL & HWK & HWD & HRD).
  pose proof (enc_k_none k HK HDK HRD HD0 ND) as ERC.
  pose proof (owe_k_none k HD0 ND) as ORC.
  assert (HP0 : k_p k = 0).
  { destruct HDK as [[H _]|[[_ H]|[_ H]]]; [exact H | | ]; rewrite HD0 in H;
      unfold SDESK_C24, SDESK_PC in H; discriminate H. }
  unfold chk_wf. rewrite enc_k_wrc, owe_k_wrc.
  refine (conj HK (conj HDK (conj _ (conj HBF (conj HRD (conj eq_refl (conj eq_refl (conj _ _)))))))).
  - unfold kcall_wf, with_want_rc, k_run, with_rc, with_out.
    cbn [k_kind k_p k_desk k_a k_b k_c k_delta k_n k_rc k_want_rc k_want_len k_want_key k_want_display].
    rewrite ERC, HP0, HD0, HWL, HWK, HWD. unfold E_ARG.
    destruct HRD as (Ha & Hb & Hc & Hd & _ & _ & Hn & _). lia.
  - rewrite ORC. reflexivity.
  - rewrite ORC. unfold E_ARG. intro H. discriminate H.
Qed.

(** The pc of a jump into owe()'s switch, as the case's cut state names it. *)
Ltac pc_to_owe k EK :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?L) _ _ _ _) =>
      replace (Z_to_bv 64 L) with (Z_to_bv 64 (pc_owe (k_kind k))) by (rewrite EK; reflexivity)
  end.

Lemma codec_main_owehd : seg_owehd_stmt.
Proof.
  unfold seg_owehd_stmt.
  intros [ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p F fc m lo data] n ENV CHK OWE k WF.
  unfold join_ok.
  intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' cur rem u0 pj tj plj c ops m1
         _ HOPS HOPS2 HCUR HC0 HCN FR ST MU WM HMI.
  pose proof (OWE k WF) as OW. clear OWE.
  unfold owe_ok, fr in OW. unfold chk_ok, fr in CHK.
  unfold env_ok in ENV. unfold fr in FR.
  cenv_cbn.
  destruct ENV as (BY & HMI0 & ST0 & LO & SPA & DJ & HPB & HPNZ & RI & DJR).
  pose proof WF as (HK & HDK & HBF & HOUT & HRC & HWRC & HWL & HWK & HWD & HRD).
  destruct FR as (HS & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST0 as (Hlo0 & Hhi0 & _).
  apply kc8_of in FK; [ | exact HWK | exact HWD ].
  unfold kc8 in FK. cbn [with_out k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before
    k_out k_want_rc k_want k_want_len k_want_key k_want_display] in FK.
  rewrite HRC, HWRC, HWL in FK.
  (* 0x144cc-0x144e0: kind, desk, k.rc, the pl[] base; kind > 11 is dead *)
  step.
  rewrite (sx32_small (k_kind k)) by lia.
  do 5 step.
  if_cases T1; [ refute_trap T1 | clear T1 ].
  (* 0x144e4-0x144f4: the 0x812 bit test *)
  do 5 step.
  if_cases T2; rewrite (bit812 (k_kind k) HK) in T2.
  - (* needs_desk: 0x14588-0x14594 *)
    pose proof (needs_desk_true _ T2) as (N1 & N4 & N11).
    do 4 step.
    if_cases T3.
    + (* !d: want_rc = SPEC_E_ARG at 0x14a30, then the checks *)
      assert (HD0 : k_desk k = 0).
      { destruct HDK as [[_ H]|[[_ H]|[_ H]]]; [exact H | | ]; rewrite H in T3; vm_compute in T3; discriminate T3. }
      do 3 step.
      pose proof (frk_earg _ _ k HWL HWK HWD FK) as FRK.
      eapply (CHK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (with_want_rc (k_run k) (-1))); try eassumption.
      * apply chk_wf_earg; assumption.
      * exact (conj (kcall_cells_size _) (conj F0 (conj F8 (conj FRK (conj FIN (conj FPD (conj FTX (conj FPL FSV)))))))).
    + (* d != 0: a0 = 1 and the switch; its fall-through to 0x145a0 is dead *)
      assert (HDNZ : k_desk k <> 0) by (intro E0; rewrite E0 in T3; vm_compute in T3; discriminate T3).
      pose proof (frk_run _ _ k HWRC HWL HWK HWD FK) as FRK.
      do 2 step.
      if_cases T4; [ | refute_trap T4 ].
      assert (KC : k_kind k = 0 \/ k_kind k = 2 \/ k_kind k = 3 \/ k_kind k = 5 \/ k_kind k = 6 \/
                   k_kind k = 7 \/ k_kind k = 8 \/ k_kind k = 9 \/ k_kind k = 10) by lia.
      destruct KC as [EK|[EK|[EK|[EK|[EK|[EK|[EK|[EK|EK]]]]]]]].
      all: rewrite EK; do 7 step; pc_to_owe k EK.
      all: eapply OW; try eassumption;
        [ intros _; split; [reflexivity | exact HDNZ]
        | exact (conj (kcall_cells_size _) (conj F0 (conj F8 (conj FRK (conj FIN (conj FPD (conj FTX (conj FPL FSV))))))))].
  - (* no desk needed: 0x144f8-0x14508 *)
    pose proof (needs_desk_false _ T2) as KN.
    do 5 step.
    pose proof (frk_run _ _ k HWRC HWL HWK HWD FK) as FRK.
    if_cases T5.
    + (* SYSEX, the switch's default 0x145a0 *)
      assert (EK : k_kind k = 11) by (zify_cond T5; repeat (rewrite Z.mod_small in T5 by lia); lia).
      pc_to_owe k EK.
      eapply OW; try eassumption;
        [ intros E0; rewrite T2 in E0; discriminate E0
        | exact (conj (kcall_cells_size _) (conj F0 (conj F8 (conj FRK (conj FIN (conj FPD (conj FTX (conj FPL FSV))))))))].
    + assert (KC : k_kind k = 1 \/ k_kind k = 4) by (zify_cond T5; repeat (rewrite Z.mod_small in T5 by lia); lia).
      destruct KC as [EK|EK].
      all: rewrite EK; do 7 step; pc_to_owe k EK.
      all: eapply OW; try eassumption;
        [ intros E0; rewrite T2 in E0; discriminate E0
        | exact (conj (kcall_cells_size _) (conj F0 (conj F8 (conj FRK (conj FIN (conj FPD (conj FTX (conj FPL FSV))))))))].
Qed.
