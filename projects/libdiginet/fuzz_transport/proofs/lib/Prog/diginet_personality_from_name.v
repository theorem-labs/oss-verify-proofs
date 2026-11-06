(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_codec proofs/libdiginet/fuzz_codec/lib/Prog/diginet_personality_from_name.v at d8e4e696562a3ec070d61f99e264ce9d80f5a5bd to fuzz_transport's images *)
(** diginet_personality_from_name (diginet_codec.c:17-25; 34 instructions at 0x17bb0, frame 0x30). a0 is not
    NULL, so 0x17bb0 `beqz` falls through; the prologue saves ra, s0-s3 and sets s2 = &personalities[0]. Each of
    the two turns loads the announce_name pointer at s3 + 8 (s3 = s2 + 24 i, in the RELRO tables) and calls
    strcmp with the argument string; a 0 result returns s3 (snez / addi -1 / and), two misses return 0. The
    argument string is the bytes of tb up to its first 0; the names are the .rodata strings "CNTRL|24" and
    "MAINUNIT". The frame stores miss tb (premise) and the RELRO tables (the stack window is disjoint from
    them), so the loads read the image. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import codec_cells codec_img strcmp_c
  diginet_personality_from_name_c.
Import ListNotations.
Open Scope Z_scope.

#[local] Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                                    | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** ---- the C string argument ---- *)

(* a byte list holding a 0 is the bytes before its first 0, that 0, and the rest *)
Lemma pfn_split : forall tb : list byte, In (b8 0) tb ->
  exists sx rest, tb = sx ++ b8 0 :: rest /\ ~ In (b8 0) sx.
Proof.
  induction tb as [|b tb IH]; intros H; [destruct H|].
  destruct (Z.eq_dec (bv_unsigned b) 0) as [E|E].
  - exists [], tb. split; [|intros []]. cbn [app]. f_equal. apply bv_eq. rewrite E. reflexivity.
  - destruct H as [H|H]; [subst b; exfalso; apply E; reflexivity|].
    destruct (IH H) as (sx & rest & -> & N). exists (b :: sx), rest. split; [reflexivity|].
    intros [H'|H']; [subst b; apply E; reflexivity | exact (N H')].
Qed.

Lemma pfn_cstring : forall sx rest, ~ In (b8 0) sx -> cstring (zb (sx ++ b8 0 :: rest)) = zb sx.
Proof.
  induction sx as [|b sx IH]; intros rest N.
  - reflexivity.
  - unfold zb in *. cbn [app map cstring].
    destruct (Z.eqb_spec (bv_unsigned b) 0) as [E|E].
    + exfalso. apply N. left. apply bv_eq. rewrite E. reflexivity.
    + f_equal. apply IH. intros H. apply N. right. exact H.
Qed.

Lemma pfn_zb_inj : forall xs ys : list byte, zb xs = zb ys -> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] H; unfold zb in H; cbn [map] in H; try discriminate H;
    [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Lemma pfn_res_c24 : forall rest, from_name_res (codec_str_c24 ++ b8 0 :: rest) = PERS.
Proof.
  intros rest. unfold from_name_res. rewrite (pfn_cstring _ rest codec_str_c24_nz).
  vm_compute. reflexivity.
Qed.

Lemma pfn_res_pc : forall rest, from_name_res (codec_str_pc ++ b8 0 :: rest) = PERS + 24.
Proof.
  intros rest. unfold from_name_res. rewrite (pfn_cstring _ rest codec_str_pc_nz).
  vm_compute. reflexivity.
Qed.

Lemma pfn_res_none : forall sx rest, ~ In (b8 0) sx -> sx <> codec_str_c24 -> sx <> codec_str_pc ->
  from_name_res (sx ++ b8 0 :: rest) = 0.
Proof.
  intros sx rest N N1 N2. unfold from_name_res. rewrite (pfn_cstring _ rest N).
  destruct (list_eq_dec Z.eq_dec (zb sx) NAME_C24) as [E1|E1].
  - exfalso. apply N1. apply pfn_zb_inj. rewrite E1. vm_compute. reflexivity.
  - destruct (list_eq_dec Z.eq_dec (zb sx) NAME_PC) as [E2|E2]; [|reflexivity].
    exfalso. apply N2. apply pfn_zb_inj. rewrite E2. vm_compute. reflexivity.
Qed.

(** ---- the walk ---- *)

Ltac pfn_ret :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.

Theorem diginet_personality_from_name_holds : strcmp_contract -> diginet_personality_from_name_contract.
Proof.
  intros SC. unfold strcmp_contract, STRCMP in SC.
  unfold diginet_personality_from_name_contract, diginet_personality_from_name_pre,
    DIGINET_PERSONALITY_FROM_NAME, DIGINET_PERSONALITY_FROM_NAME_DEPTH.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo tb [HA0 [[HTB HIN] [HTD [HR [DJ [HMI [ST LO]]]]]]].
  destruct (pfn_split tb HIN) as (sx & rest & -> & NZ). clear HIN.
  replace (sx ++ b8 0 :: rest) with ((sx ++ [b8 0]) ++ rest) in HTB by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in HTB. destruct HTB as [HS _].
  assert (HD : bv_unsigned a0 + Z.of_nat (length sx) + 1 <= lo \/ bv_unsigned sp <= bv_unsigned a0)
    by (rewrite length_app in HTD; cbn [length] in HTD; lia).
  clear HTD.
  pose proof (codec_pers_at m HR) as HP. unfold codec_pers_cells in HP. clear HR.
  unfold disj, RELRO_BASE, RELRO_LEN in DJ.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  replace (bv_modulus 64) with 18446744073709551616 in Rsp by reflexivity.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  (* beqz a0 *)
  step. if_false.
  (* prologue: frame, five saves, s0 = a0, s1 = 0, a1 = 0, s2 = &personalities[0] *)
  do 11 zstep.
  (* turn 0: s3 = s2, a1 = personalities[0].announce_name, strcmp(a0, a1) *)
  do 7 zstep.
  eapply evt_cut.
  { eapply SC with (sx := sx) (sy := codec_str_c24).
    - exact HS.
    - exact NZ.
    - rewrite unsigned_lit by lia. exact (codec_str_c24_at _ HMI).
    - exact codec_str_c24_nz. }
  intros ms' (r & x11 & x12 & x13 & E & HR1). subst ms'.
  pfn_ret.
  (* beqz a0 *)
  step.
  if_cases K1; zify_cond K1.
  - (* strcmp = 0: "CNTRL|24" *)
    assert (Er : r = Z_to_bv 64 0) by (apply bv_eq; rewrite K1; reflexivity).
    subst r. assert (Es : sx = codec_str_c24) by (apply HR1; reflexivity). subst sx.
    do 8 zstep.
    release_frame FR ST (bv_unsigned sp).
    do 2 zstep.
    rewrite pfn_res_c24.
    finish.
  - (* turn 1 *)
    assert (Nr : r <> Z_to_bv 64 0) by (intro C; apply K1; rewrite C; reflexivity).
    assert (N1 : sx <> codec_str_c24) by (intro C; apply Nr; apply HR1; exact C).
    clear HR1 Nr K1.
    do 4 zstep. if_true.
    do 7 zstep.
    eapply evt_cut.
    { eapply SC with (sx := sx) (sy := codec_str_pc).
      - exact HS.
      - exact NZ.
      - rewrite unsigned_lit by lia. exact (codec_str_pc_at _ HMI).
      - exact codec_str_pc_nz. }
    intros ms' (r2 & y11 & y12 & y13 & E & HR2). subst ms'.
    pfn_ret.
    step.
    if_cases K2; zify_cond K2.
    + (* strcmp = 0: "MAINUNIT" *)
      assert (Er : r2 = Z_to_bv 64 0) by (apply bv_eq; rewrite K2; reflexivity).
      subst r2. assert (Es : sx = codec_str_pc) by (apply HR2; reflexivity). subst sx.
      do 8 zstep.
      release_frame FR ST (bv_unsigned sp).
      do 2 zstep.
      rewrite pfn_res_pc.
      finish.
    + (* two misses *)
      assert (Nr : r2 <> Z_to_bv 64 0) by (intro C; apply K2; rewrite C; reflexivity).
      assert (N2 : sx <> codec_str_pc) by (intro C; apply Nr; apply HR2; exact C).
      assert (HL : (0 <? bv_unsigned r2) = true).
      { apply Z.ltb_lt. pose proof (bv_unsigned_in_range 64 r2). lia. }
      clear HR2 Nr.
      do 4 zstep. if_false.
      zstep. rewrite HL.
      do 7 zstep.
      release_frame FR ST (bv_unsigned sp).
      do 2 zstep.
      rewrite (pfn_res_none sx rest NZ N1 N2).
      finish.
Qed.
