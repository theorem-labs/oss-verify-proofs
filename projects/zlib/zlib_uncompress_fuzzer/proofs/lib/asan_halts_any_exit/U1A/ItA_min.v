(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* inflate_state arrays at their 1.4 offsets (lens 168, work 808, codes 1384, sane 7160; 1.3.1: 152, 792, 1368, 7144) *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AArr U2AKit ItAKit ItAPure.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U1A Require Import ItA_base.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_base | solve_load_sh0 | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.

Section CANSEC1. Context {rc : runConstT}.
Section P.
  Variables (RNG : footprint) (FR : bvmap 5 word) (fc : bv 32) (gp tp : word).
  Variables (SP SPA S F PB top : Z) (m1 : amem).
  Variables (lf wf cf : Z -> Z) (lo codes bits : Z).
  Hypothesis CX : itb_ctx RNG SP SPA S F PB top m1.
  Hypothesis Hcodes : 0 <= codes <= 288.
  Hypothesis Hbits : 1 <= bits <= 15.

  Notation LP := (S + 168 + 2 * lo).
  Notation ST := (bst SP SPA S F PB LP gp tp FR fc).
  Notation cA := (arr_get (cntA lf lo codes)).
  Notation mx := (mxA lf lo codes).
  Notation mn := (mnA lf lo codes).
  Notation rt := (rootA lf lo codes bits).
  Notation SHPB := (Z_to_bv 64 (Z.shiftr PB 3 + 2147450880)).

  Lemma cA_range' : forall j, 0 <= cA j <= codes.
  Proof. intros j. rewrite cntA_eq. apply cntK_le; lia. Qed.

  Lemma mxmn_facts : 1 <= mx -> 1 <= mn <= mx /\ mx <= 15 /\ 1 <= rt <= 15 /\ mn <= rt /\
    rt = (let r := (if bits <? mx then bits else mx) in if mn <? r then r else mn).
  Proof.
    intros H1. pose proof (mx_range (cntA lf lo codes)) as MR.
    pose proof (mn_range (cntA lf lo codes) mx ltac:(unfold mxA in *; lia)) as NR.
    unfold rootA, itm_root. unfold mnA in *. unfold mxA in *.
    set (mxv := itm_max (cntA lf lo codes)) in *. set (mnv := itm_min (cntA lf lo codes) mxv) in *.
    destruct (Z.ltb_spec mxv bits); destruct (Z.ltb_spec bits mxv); try lia;
      destruct (Z.ltb_spec mxv mnv); destruct (Z.ltb_spec bits mnv); destruct (Z.ltb_spec mnv mxv); destruct (Z.ltb_spec mnv bits); cbv zeta; lia.
  Qed.

  Definition left_pre (m : amem) (x1 x5 x6 x7 x17 x24 x25 x28 x29 x30 x31 : word) : machine_state -> Prop :=
    fun ms' => exists (q10 q16 : word),
      ms' = ST x1 x5 x6 x7 q10 (Z_to_bv 64 (if mx =? 1 then 1 else 0)) SHPB (Z_to_bv 64 rt) (Z_to_bv 64 mx) (Z_to_bv 64 mn)
               q16 x17 x24 x25 x28 x29 x30 x31 0x95bb0 m
      /\ 1 <= mx.

  Lemma it_min_loop : forall (k : nat) (i r7 : Z) (m : amem)
      (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 : word) (offs : Z -> Z) (next bitsw : word)
      (x1 x5 x6 x7 x16 x17 x24 x25 x28 x29 x30 x31 : word),
    Z.of_nat k = mx - i -> 1 <= i < mx -> 2 <= mx <= 15 -> r7 = (if bits <? mx then bits else mx) ->
    (forall j, 1 <= j < i -> cA j = 0) ->
    itb_inv SPA S F PB m1 m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 cA offs lf wf cf next bitsw ->
    evtF asegs RNG (left_pre m x1 x5 x6 x7 x17 x24 x25 x28 x29 x30 x31)
      (ST x1 x5 x6 x7 (Z_to_bv 64 (F + 32 + 2 * i)) (Z_to_bv 64 (mx - i)) SHPB (Z_to_bv 64 r7) (Z_to_bv 64 mx) (Z_to_bv 64 i)
          x16 x17 x24 x25 x28 x29 x30 x31 0x95b80 m).
  Proof using All.
    induction k as [|k IH]; intros i r7 m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 offs next bitsw
      x1 x5 x6 x7 x16 x17 x24 x25 x28 x29 x30 x31 Hk Hi Hmx Hr7 HZ INV; [lia|].
    pose proof INV as INV0. open_ctx CX. open_inv INV. unfold bst.
    pose proof (cA_range' i) as RCI.
    pose proof (mxmn_facts ltac:(lia)) as (MN1 & MX15 & RT & MNRT & RTEQ). cbv zeta in RTEQ.
    assert (R7 : 1 <= r7 <= 15 /\ r7 <= mx) by (subst r7; destruct (Z.ltb_spec bits mx); lia).
    pose proof (f16arr_read asegs m (F + 32) 16 _ i _ CNT ltac:(lia) eq_refl) as RD.
    zs. rewrite (zx16_small (cA i)) by lia. clear RD.
    zs. zbr0 K.
    -
      assert (MNI : mn = i) by (unfold mnA; apply mn_found; [lia | lia | exact HZ | exact K]).
      zs. zs. zbr0 K2.
      + apply evtF_done. unfold left_pre. do 2 eexists. split; [|lia].
        replace (mx =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
        replace rt with r7 by (rewrite RTEQ, <- Hr7, MNI; destruct (Z.ltb_spec i r7); lia).
        rewrite MNI. reflexivity.
      + zs. apply evtF_done. unfold left_pre. do 2 eexists. split; [|lia].
        replace (mx =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
        replace rt with i by (rewrite RTEQ, <- Hr7, MNI; destruct (Z.ltb_spec i r7); lia).
        rewrite MNI. reflexivity.
    -
      zs. setreg 15 (Z_to_bv 64 (i + 1)) ltac:(rewrite swrap32_small by lia; reflexivity).
      zs. zs. zs. zbr0 K2.
      +
        setreg 10 (Z_to_bv 64 (F + 32 + 2 * (i + 1))) ltac:(f_equal; lia).
        setreg 11 (Z_to_bv 64 (mx - (i + 1))) ltac:(f_equal; lia).
        eapply (IH (i + 1) r7); [lia | lia | lia | exact Hr7 | | exact INV0].
        intros j Hj. destruct (Z.eq_dec j i) as [->|]; [exact K | apply HZ; lia].
      +
        assert (MNI : mn = mx).
        { unfold mnA. apply mn_all; [lia|]. intros j Hj. destruct (Z.eq_dec j i) as [->|]; [exact K | apply HZ; lia]. }
        zs. zs. zbr K3.
        * zs. apply evtF_done. unfold left_pre. do 2 eexists. split; [|lia].
          replace (mx =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
          replace rt with mx by (rewrite RTEQ, <- Hr7, MNI; destruct (Z.ltb_spec mx r7); lia).
          rewrite MNI. replace (mx - i + -1) with 0 by lia. reflexivity.
  Qed.

  Lemma it_rootmin : forall (m : amem)
      (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 : word) (offs : Z -> Z) (next bitsw : word)
      (x1 x5 x6 x7 x10 x11 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word),
    2 <= mx ->
    itb_inv SPA S F PB m1 m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 cA offs lf wf cf next bitsw ->
    evtF asegs RNG (left_pre m x1 x5 x6 x7 x17 x24 x25 x28 x29 x30 x31)
      (ST x1 x5 x6 x7 x10 x11 SHPB (Z_to_bv 64 bits) (Z_to_bv 64 mx) x15 x16 x17 x24 x25 x28 x29 x30 x31 0x95b6c m).
  Proof using All.
    intros until x31. intros Hmx INV.
    pose proof (mxmn_facts ltac:(lia)) as (MN1 & MX15 & RT & MNRT & RTEQ).
    unfold bst. zs. zbr0 K.
    -
      zs. zs. zs.
      pose proof (it_min_loop (Z.to_nat (mx - 1)) 1 bits m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 offs next bitsw
                    x1 x5 x6 x7 x16 x17 x24 x25 x28 x29 x30 x31 ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(destruct (Z.ltb_spec bits mx); lia) ltac:(intros; lia) INV) as HL.
      replace (F + 32 + 2 * 1) with (F + 34) in HL by lia.
      replace (mx - 1) with (mx + -1) in HL by lia. exact HL.
    - zs. zs. zs. zs.
      pose proof (it_min_loop (Z.to_nat (mx - 1)) 1 mx m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 offs next bitsw
                    x1 x5 x6 x7 x16 x17 x24 x25 x28 x29 x30 x31 ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(destruct (Z.ltb_spec bits mx); lia) ltac:(intros; lia) INV) as HL.
      replace (F + 32 + 2 * 1) with (F + 34) in HL by lia.
      replace (mx - 1) with (mx + -1) in HL by lia. exact HL.
  Qed.

  Definition low_post (m : amem) (x1 x5 x6 x7 x11 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word) : machine_state -> Prop :=
    fun ms' => left_pre m x1 x5 x6 x7 x17 x24 x25 x28 x29 x30 x31 ms'
      \/ (exists q10 : word, ms' = ST x1 x5 x6 x7 q10 x11 SHPB (Z_to_bv 64 bits) x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 0x964e8 m /\ mx = 0).

  Lemma it_low : forall (m : amem)
      (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 : word) (offs : Z -> Z) (next bitsw : word)
      (x1 x5 x6 x7 x10 x11 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word),
    (forall j, 2 <= j <= 15 -> cA j = 0) ->
    itb_inv SPA S F PB m1 m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 cA offs lf wf cf next bitsw ->
    evtF asegs RNG (low_post m x1 x5 x6 x7 x11 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31)
      (ST x1 x5 x6 x7 x10 x11 SHPB (Z_to_bv 64 bits) x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 0x964b4 m).
  Proof using All.
    intros until x31. intros HZ INV. open_ctx CX. open_inv INV. unfold bst.
    pose proof (cA_range' 1) as R1.
    pose proof (f16arr_read asegs m (F + 32) 16 _ 1 _ CNT ltac:(lia) eq_refl) as RD.
    zs. rewrite (zx16_small (cA 1)) by lia. clear RD.
    zs. zbr0 K.
    -
      apply evtF_done. unfold low_post. right. eexists. split; [reflexivity|].
      unfold mxA. apply mx_zero. intros j Hj. destruct (Z.eq_dec j 1) as [->|]; [exact K | apply HZ; lia].
    -
      assert (MX1 : mx = 1) by (unfold mxA; apply (mx_found _ 1); [lia | intros j Hj; apply HZ; lia | exact K]).
      pose proof (mxmn_facts ltac:(lia)) as (MN1 & MX15 & RT & MNRT & RTEQ). cbv zeta in RTEQ.
      zs. setreg 13 (Z_to_bv 64 1) ltac:(replace (0 <? bits) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
      zs. zs. zs. zs. zs.
      apply evtF_done. unfold low_post. left. unfold left_pre. do 2 eexists. split; [|lia].
      assert (MN : mn = 1) by lia.
      replace rt with 1 by (rewrite RTEQ, MX1, MN; destruct (Z.ltb_spec bits 1); destruct (Z.ltb_spec 1 bits); try lia; destruct (Z.ltb_spec 1 1); lia).
      rewrite MX1, MN. reflexivity.
  Qed.
End P.
End CANSEC1.
