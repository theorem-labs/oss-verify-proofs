(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths changed; 166 of its 215 lines of code are new or changed and 3804 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/joined_byte.v; 58 of its 188 lines of code are new or changed and 85 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/joined_byteF.v, with its numbers changed; 406 of its 444 lines of code are new or changed and 150 lines of the source are left out. *)
(* The footprint twin of name_field.v (image B): the same run as an ExecF.evtF under a footprint RNG
   (name_field_contract_F), a mechanical re-run of the plain proof name_field.v@53dc00d331f over StepF's step
   (route 2): the same script, step for step, with evtF for evt and each access side goal closed from one rng premise:
   the frame stores and loads (the window), the two loads of the shadow base (the image), the 8-byte load at m + 280
   and its shadow byte, the 1-byte loads of the name bytes and their shadow bytes (inside the byte-exact shadow span
   of the name), and the 1-byte stores at N + i and their shadow bytes (inside the shadow word cover of [N, N + 16)).
   The one callee, __asan_memset, is taken in its owner's footprint form: a Theorem Labs lane's asan_memset_contract_F
   (lib/B/Prog/asan_memset_cF.v, merged from a working branch 9869f1d1f86), in the place where
   name_field.v takes asan_memset_contract. name_field.v and its theorem are unchanged. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes
  ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib RcAsan
  RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT asan_memset_c asan_memset_cF name_field_c
  name_field.
(* Last: StepF's step / if_false (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* A shadow address is [x / 8 + off]: its access side goal needs the Euclidean equations of the division, which
   StepF's [alia] does not add, so the shadow loads go through StepF's acc_hint hook (reac_ports_parseF.v's hint). *)
Ltac has_div E := lazymatch E with context [Z.div _ _] => idtac end.

Ltac solve_acc_div_with H E :=
  lazymatch goal with
  | |- acc_in ?RNG (_, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with
      | rng _ ?lo ?len =>
          apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true));
          split; Z.div_mod_to_equations; lia
      end
  end.

Ltac acc_hintF :=
  lazymatch goal with
  | |- acc_in ?RNG (?a, _) =>
      let E := addr_expr a in
      has_div E;
      match goal with
      | H : rng RNG ?lo _ |- _ => has_div lo; solve_acc_div_with H E
      end
  end.

Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= acc_hintF.

(* The shadow byte of x in [a, a + n) inside the byte-exact shadow span of [a, a + n). *)
Lemma nfF_sh_exact : forall RNG a n x,
  rng RNG (shadow_addr a) (shadow_addr (a + n - 1) - shadow_addr a + 1) -> 0 <= a -> a <= x < a + n ->
  rng RNG (x / 8 + 2147450880) 1.
Proof.
  intros RNG a n x H Ha Hx. unfold shadow_addr, ASAN_K in H.
  eapply rng_sub; [exact H | clear H | clear H].
  - pose proof (Z.div_le_mono a x 8 ltac:(lia) ltac:(lia)). lia.
  - pose proof (Z.div_le_mono x (a + n - 1) 8 ltac:(lia) ltac:(lia)). lia.
Qed.

(* The shadow byte of x in [a, a + n) inside the 8-aligned shadow word cover of [a, a + n). *)
Lemma nfF_sh_cover : forall RNG a n x,
  rng RNG (shadow_addr a / 8 * 8) (shadow_addr (a + n - 1) / 8 * 8 + 8 - shadow_addr a / 8 * 8) ->
  0 <= a -> a <= x < a + n ->
  rng RNG (x / 8 + 2147450880) 1.
Proof.
  intros RNG a n x H Ha Hx. unfold shadow_addr, ASAN_K in H.
  eapply rng_sub; [exact H | clear H | clear H]; Z.div_mod_to_equations; lia.
Qed.

(* A branch whose condition is a closed term that computes to false (name.v's nf_pc_false_vm on evtF goals). *)
Ltac nfF_pc_false_vm :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false by (vm_compute; reflexivity); cbv iota
  end.

Section NFF.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (wm wn name : word) (nb : list byte) (RNG : footprint).
  Hypothesis Rsp : 2240 <= bv_unsigned sp < 2^64.
  Hypothesis Hm288 : bv_unsigned wm + 288 <= 2^64.
  Hypothesis Hm8 : bv_unsigned wm mod 8 = 0.
  Hypothesis HN16 : bv_unsigned wn + 16 <= 2^64.
  Hypothesis Hname : bv_unsigned name <> 0 -> name_ok nb /\ bv_unsigned name + Z.of_nat (length nb) <= 2^64.
  Hypothesis Dfm : bv_unsigned sp <= bv_unsigned wm + 280 \/ bv_unsigned wm + 288 <= bv_unsigned sp - 2240.
  Hypothesis Dfn : bv_unsigned sp <= bv_unsigned name \/
                   bv_unsigned name + Z.of_nat (length nb) <= bv_unsigned sp - 2240.
  Hypothesis DfN : bv_unsigned sp <= bv_unsigned wn \/ bv_unsigned wn + 16 <= bv_unsigned sp - 2240.
  Hypothesis DNm : bv_unsigned wn + 16 <= bv_unsigned wm + 280 \/ bv_unsigned wm + 288 <= bv_unsigned wn.
  Hypothesis DNn : bv_unsigned wn + 16 <= bv_unsigned name \/ bv_unsigned name + Z.of_nat (length nb) <= bv_unsigned wn.
  Hypothesis HC : asan_cells m.
  Hypothesis HSW : shadow_rw m.
  Hypothesis HHM : HIGHMEM_BEG <= bv_unsigned sp - 2240.
  Hypothesis HAE : bv_unsigned sp <= APPMEM_END.
  Hypothesis ADm : addressable m (bv_unsigned wm + 280) 8.
  Hypothesis ADn : addressable m (bv_unsigned name) (Z.of_nat (length nb)).
  Hypothesis ADN : addressable m (bv_unsigned wn) 16.
  Hypothesis HRT : bv_unsigned wn + 16 <= RT_LO \/ RT_HI <= bv_unsigned wn.
  (* The footprint premises the loop and the epilogue use, in name_field_contract_F's form (the shadow byte of
     m + 280 with shadow_addr unfolded). *)
  Hypothesis RWIN : rng RNG (bv_unsigned sp - 2240) 2240.
  Hypothesis RM8 : rng RNG (bv_unsigned wm + 280) 8.
  Hypothesis RMS : rng RNG ((bv_unsigned wm + 280) / 8 + 2147450880) 1.
  Hypothesis RNB : bv_unsigned name <> 0 -> rng RNG (bv_unsigned name) (Z.of_nat (length nb)).
  Hypothesis RNBS : bv_unsigned name <> 0 ->
    rng RNG (shadow_addr (bv_unsigned name))
      (shadow_addr (bv_unsigned name + Z.of_nat (length nb) - 1) - shadow_addr (bv_unsigned name) + 1).
  Hypothesis RN16 : rng RNG (bv_unsigned wn) 16.
  Hypothesis RN16S : rng RNG (shadow_addr (bv_unsigned wn) / 8 * 8)
    (shadow_addr (bv_unsigned wn + 16 - 1) / 8 * 8 + 8 - shadow_addr (bv_unsigned wn) / 8 * 8).

  Local Abbreviation W0 := [(bv_unsigned sp - 2240, bv_unsigned sp); (bv_unsigned wn, bv_unsigned wn + 16)].
  Local Abbreviation SPm := (Z_to_bv 64 (bv_unsigned sp + -32)).
  Local Abbreviation A0w := (Z_to_bv 64 (bv_unsigned wm + 280)).
  Local Abbreviation SAw := (Z_to_bv 64 ((bv_unsigned wm + 280) / 8 + 2147450880)).
  Local Abbreviation SKw := (Z_to_bv 64 2147450880).
  Local Abbreviation PFX i := (firstn i nb ++ repeat (Z_to_bv 8 0) (16 - i)).

  Definition QnF : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ bytes_at rsegs m' (bv_unsigned wn) (nmf nb)
      /\ munch W0 m m'
      /\ wmono rsegs m m'
      /\ mem_inv rsegs m'
      /\ stk rsegs m' (bv_unsigned sp - 2240) (bv_unsigned sp)
      /\ asan_cells m' /\ shadow_rw m'.

  (* The loop invariant (name_field.v's ninv). *)
  Definition ninvF (m' : word -> option byte) (cur : list byte) : Prop :=
    wr_at rsegs m' (bv_unsigned wn) 16 /\ length cur = 16%nat /\ bytes_at rsegs m' (bv_unsigned wn) cur /\
    rw_cells rsegs m' (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] /\
    bytes_at rsegs m' (bv_unsigned wm + 280) (le8 name) /\ bytes_at rsegs m' (bv_unsigned name) nb /\
    munch W0 m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    stk rsegs m' (bv_unsigned sp - 2240) (bv_unsigned sp + -32).

  Lemma AW0F : all_app W0.
  Proof. exact (nf_aw m (bv_unsigned sp) (bv_unsigned wn) HHM HAE ADN). Qed.

  Lemma DRT0F : disjoint_from W0 RT_LO (RT_HI - RT_LO).
  Proof. exact (nf_drt (bv_unsigned sp) (bv_unsigned wn) HHM HRT). Qed.

  Lemma nfF_mk : forall m', munch W0 m m' -> meta_kept m m'.
  Proof. intros m' MU. exact (munch_meta _ m m' MU AW0F). Qed.

  Lemma nfF_adm : forall m', munch W0 m m' -> addressable m' (bv_unsigned wm + 280) 8.
  Proof. intros m' MU. exact (addressable_kept m m' _ _ ADm (nfF_mk m' MU)). Qed.

  Lemma nfF_adn : forall m', munch W0 m m' -> addressable m' (bv_unsigned name) (Z.of_nat (length nb)).
  Proof. intros m' MU. exact (addressable_kept m m' _ _ ADn (nfF_mk m' MU)). Qed.

  Lemma nfF_adN : forall m', munch W0 m m' -> addressable m' (bv_unsigned wn) 16.
  Proof. intros m' MU. exact (addressable_kept m m' _ _ ADN (nfF_mk m' MU)). Qed.

  Lemma nfF_cells : forall m', munch W0 m m' -> wmono rsegs m m' -> asan_cells m' /\ shadow_rw m'.
  Proof.
    intros m' MU WM. split; [exact (asan_cells_kept _ m m' HC MU DRT0F)|].
    exact (shadow_rw_kept m m' HSW (nfF_mk m' MU) WM).
  Qed.

  (* The epilogue (0x87ad0 .. 0x87ae4): the four restores (window), addi sp,sp,32 and ret. *)
  Lemma epiF : forall (x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 u3 u4 u5 u6 : word) m',
    ninvF m' (nmf nb) ->
    evtF rsegs RNG QnF
      (MS (mkR x1 SPm gp tp u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18
               s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x87ad0) fc None m' (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 u3 u4 u5 u6 m'
      (HW & _ & HB & FR & HM & HNm & MU & WM & MI & ST).
    destruct (nfF_cells m' MU WM) as [HC' HSW'].
    step. step. step. step. step. step.
    apply evtF_done. unfold QnF. do 15 eexists. exists m'.
    split; [reflexivity|].
    split; [exact HB|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [|split; [exact HC' | exact HSW']].
    release_frame FR ST (bv_unsigned sp). exact ST.
  Qed.

  Lemma ninvF_store : forall m' cur i (c : byte), ninvF m' cur -> (i < 16)%nat ->
    ninvF (write_to_mem m' (wa (bv_unsigned wn + Z.of_nat i)) [c]) (upd_bytes cur i [c]).
  Proof.
    intros m' cur i c (HW & Hlen & HB & FR & HM & HNm & MU & WM & MI & ST) Hi.
    pose proof (bytes_at_bound rsegs m' _ _ HB) as BB.
    pose proof (bytes_at_bound rsegs m' _ _ HNm) as BN.
    pose proof (wr_at_store_ok rsegs m' (bv_unsigned wn) 16 (Z.of_nat i) 1 HW ltac:(lia) ltac:(lia)) as HS.
    split; [apply wr_at_write; exact HW|].
    split; [rewrite upd_bytes_length by (cbn [length]; lia); exact Hlen|].
    split.
    { pose proof (bytes_at_write_inside rsegs m' (bv_unsigned wn) cur (Z.of_nat i) [c] HB ltac:(lia)
                    ltac:(rewrite Nat2Z.id; cbn [length]; lia)) as H.
      rewrite Nat2Z.id in H. exact H. }
    split.
    { apply rw_cells_frame; [exact FR | lia | cbn [length]; lia |].
      cbn [cells_size csize Nat.add length]. lia. }
    split; [apply bytes_at_write_other; [exact HM | lia | cbn [length]; lia | rewrite length_le8; cbn [length]; lia]|].
    split; [apply bytes_at_write_other; [exact HNm | lia | cbn [length]; lia | cbn [length]; lia]|].
    split; [apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length]; right; left; split; lia]|].
    split; [apply wmono_write; exact WM|].
    split; [apply mem_inv_store; [exact MI | exact HS]|].
    apply stk_write; [exact ST | lia | cbn [length]; lia].
  Qed.

  (* The state at the loop head 0x87a4c for step i. *)
  Definition head_okF (i : nat) : Prop :=
    forall (x1 u0 u1 u2 x11 x14 x16 x17 u3 u4 u5 u6 : word) (m' : word -> option byte),
      bv_unsigned x14 = 18446744073709551615 - bv_unsigned wn ->
      (forall j, (j < i)%nat -> bv_unsigned (nth j nb (Z_to_bv 8 0)) <> 0) ->
      ninvF m' (PFX i) ->
      evtF rsegs RNG QnF
        (MS (mkR x1 SPm gp tp u0 u1 u2 wn wm A0w x11 SAw (Z_to_bv 64 (Z.of_nat i)) x14 (Z_to_bv 64 16) x16 x17
                 SKw s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            F (Z_to_bv 64 0x87a4c) fc None m' (seg_rom rsegs)).

  (* 0x87aa4 .. : the store of the byte at N + i (RN16), the loop test, and the next step or the epilogue. *)
  Lemma l_storeF : forall i, (i < 16)%nat -> (i < length nb)%nat -> bv_unsigned name <> 0 ->
    (S i < 16 -> head_okF (S i))%nat ->
    (forall j, (j <= i)%nat -> bv_unsigned (nth j nb (Z_to_bv 8 0)) <> 0) ->
    forall (x1 u0 u1 u2 x14 x17 u3 u4 u5 u6 : word) (m' : word -> option byte),
      bv_unsigned x14 = 18446744073709551615 - bv_unsigned wn ->
      ninvF m' (PFX i) ->
      evtF rsegs RNG QnF
        (MS (mkR x1 SPm gp tp u0 u1 u2 wn wm A0w (Z_to_bv 64 (bv_unsigned wn + Z.of_nat i)) SAw
                 (Z_to_bv 64 (Z.of_nat i)) x14 (Z_to_bv 64 16) (zxb (nth i nb (Z_to_bv 8 0))) x17
                 SKw s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            F (Z_to_bv 64 0x87aa4) fc None m' (seg_rom rsegs)).
  Proof.
    intros i Hi16 Hi NZ HNX Hnz x1 u0 u1 u2 x14 x17 u3 u4 u5 u6 m' H14 NI.
    destruct (Hname NZ) as (OK & Lnb).
    pose proof NI as (HW & Hlen & HB & FR & HM & HNm & MU & WM & MI & ST).
    pose proof (zr_word wn) as RN. unfold inr64 in RN.
    pose proof (wr_at_store_ok rsegs m' (bv_unsigned wn) 16 (Z.of_nat i) 1 HW ltac:(lia) ltac:(lia)) as HS.
    step. step.
    rewrite le1_zxb.
    pose proof (ninvF_store m' _ i (nth i nb (Z_to_bv 8 0)) NI ltac:(lia)) as NI'.
    rewrite upd_prefix in NI' by lia.
    step.
    rewrite (rc_eqb_lit (Z.of_nat i + 1) 16) by lia.
    destruct (Nat.lt_ge_cases (S i) 16) as [Hlt | Hge].
    - replace (Z.of_nat i + 1 =? 16) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia.
      pose proof (HNX Hlt) as HH. unfold head_okF in HH.
      apply HH; [exact H14 | | exact NI'].
      intros j' Hj'. apply Hnz. lia.
    - replace (Z.of_nat i + 1 =? 16) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. cbv iota.
      step.
      assert (L16 : length nb = 16%nat) by (destruct OK as (OKl & _ & _); lia).
      replace (S i) with 16%nat in NI' by lia.
      rewrite <- (nmf_full nb L16) in NI'.
      2:{ intros j' Hj'. apply Hnz. lia. }
      apply epiF. exact NI'.
  Qed.

  (* 0x87a84 .. : the byte nb[i] (RNB), the stop on 0, the bound check of N + i, the instrumented check of the store
     at N + i (its shadow byte inside RN16S; fast path, or the slow path at 0x87ac0 with (N + i) mod 8 < k), then
     l_storeF. *)
  Lemma l_byteF : forall i, (i < 16)%nat -> (i < length nb)%nat -> bv_unsigned name <> 0 ->
    (S i < 16 -> head_okF (S i))%nat ->
    (forall j, (j < i)%nat -> bv_unsigned (nth j nb (Z_to_bv 8 0)) <> 0) ->
    forall (x1 u0 u1 u2 x14 x16 x17 u3 u4 u5 u6 : word) (m' : word -> option byte),
      bv_unsigned x14 = 18446744073709551615 - bv_unsigned wn ->
      ninvF m' (PFX i) ->
      evtF rsegs RNG QnF
        (MS (mkR x1 SPm gp tp u0 u1 u2 wn wm A0w (Z_to_bv 64 (bv_unsigned name + Z.of_nat i)) SAw
                 (Z_to_bv 64 (Z.of_nat i)) x14 (Z_to_bv 64 16) x16 x17
                 SKw s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            F (Z_to_bv 64 0x87a84) fc None m' (seg_rom rsegs)).
  Proof.
    intros i Hi16 Hi NZ HNX Hnz x1 u0 u1 u2 x14 x16 x17 u3 u4 u5 u6 m' H14 NI.
    destruct (Hname NZ) as (OK & Lnb).
    pose proof (RNB NZ) as RNB'.
    pose proof NI as (HW & Hlen & HB & FR & HM & HNm & MU & WM & MI & ST).
    pose proof (zr_word wn) as RN. unfold inr64 in RN.
    assert (RSN : rng RNG ((bv_unsigned wn + Z.of_nat i) / 8 + 2147450880) 1)
      by (apply (nfF_sh_cover RNG (bv_unsigned wn) 16 _ RN16S); lia).
    pose proof (rd_byte rsegs m' (bv_unsigned name) nb i HNm Hi) as RD.
    step. step.
    rewrite rc_zxb_eqb0.
    destruct (Z.eqb_spec (bv_unsigned (nth i nb (Z_to_bv 8 0))) 0) as [C0 | CNZ].
    - cbv iota.
      rewrite <- (nmf_stop nb i Hi ltac:(lia) Hnz C0) in NI.
      apply epiF. exact NI.
    - cbv iota.
      clear RD.
      step.
      rewrite (rc_ltu_ge (Z_to_bv 64 (Z.of_nat i)) x14) by (rewrite unsigned_lit by lia; lia).
      cbv iota.
      step. step.
      rewrite (unsigned_lit (bv_unsigned wn + Z.of_nat i)) by lia. rewrite rc_shr3.
      step.
      destruct (nf_sh m' (bv_unsigned wn) 16 (bv_unsigned wn + Z.of_nat i) (Z.of_nat i) (nfF_adN m' MU)
                  ltac:(lia) eq_refl) as (k & RK & OKk & KR).
      step.
      clear RK.
      step.
      unfold sxb. rewrite (rc_eqb0_signed (bv_signed k)) by lia.
      assert (Hnz' : forall j, (j <= i)%nat -> bv_unsigned (nth j nb (Z_to_bv 8 0)) <> 0).
      { intros j Hj. destruct (Nat.eq_dec j i) as [->|Ne]; [exact CNZ | apply Hnz; lia]. }
      destruct (Z.eqb_spec (bv_signed k) 0) as [K0 | K0]; cbn [negb]; cbv iota.
      + apply l_storeF; assumption.
      + step.
        rewrite (unsigned_lit (bv_unsigned wn + Z.of_nat i)) by lia. rewrite rc_land7.
        step.
        rewrite (rc_lts_signed ((bv_unsigned wn + Z.of_nat i) mod 8) (bv_signed k))
          by (pose proof (Z.mod_pos_bound (bv_unsigned wn + Z.of_nat i) 8 ltac:(lia)); lia).
        replace ((bv_unsigned wn + Z.of_nat i) mod 8 <? bv_signed k) with true
          by (symmetry; apply Z.ltb_lt; lia).
        cbv iota.
        apply l_storeF; assumption.
  Qed.

  (* 0x87a4c .. : the instrumented check of the 8-byte load at m + 280 (RMS, RM8), the load of name, the checks of
     name + i (no unsigned wrap, no wrap to 0, name <> 0), the instrumented check of the 1-byte load at name + i (its
     shadow byte inside RNBS; fast path, or the slow path at 0x87ab4 with (name + i) mod 8 < k), then l_byteF. *)
  Lemma l_headF : forall i, (i < 16)%nat -> bv_unsigned name <> 0 -> (S i < 16 -> head_okF (S i))%nat -> head_okF i.
  Proof.
    intros i Hi16 NZ HNX. unfold head_okF.
    intros x1 u0 u1 u2 x11 x14 x16 x17 u3 u4 u5 u6 m' H14 Hnz NI.
    destruct (Hname NZ) as (OK & Lnb).
    pose proof (name_ok_lt nb i OK Hi16 Hnz) as Hi.
    pose proof NI as (HW & Hlen & HB & FR & HM & HNm & MU & WM & MI & ST).
    pose proof (zr_word name) as Rn. unfold inr64 in Rn.
    assert (RSn : rng RNG ((bv_unsigned name + Z.of_nat i) / 8 + 2147450880) 1)
      by (apply (nfF_sh_exact RNG (bv_unsigned name) (Z.of_nat (length nb)) _ (RNBS NZ)); lia).
    pose proof (nf_sh8 m' (bv_unsigned wm + 280) (nfF_adm m' MU) (nf_mod280 _ Hm8)) as RS8.
    pose proof (rd_le8 rsegs m' _ name HM) as HR.
    step. step.
    nfF_pc_false_vm.
    step. step. step.
    rewrite (rc_ltu_ge name (Z_to_bv 64 (bv_unsigned name + Z.of_nat i))) by (rewrite unsigned_lit by lia; lia).
    cbv iota.
    step. step. step. step.
    rewrite (rc_ubchk name (Z_to_bv 64 (bv_unsigned name + Z.of_nat i))) by (try rewrite unsigned_lit by lia; lia).
    cbv iota.
    step.
    rewrite (rc_neq0w name NZ). cbv iota.
    clear RS8 HR.
    step.
    rewrite (unsigned_lit (bv_unsigned name + Z.of_nat i)) by lia. rewrite rc_shr3.
    step.
    destruct (nf_sh m' (bv_unsigned name) (Z.of_nat (length nb)) (bv_unsigned name + Z.of_nat i) (Z.of_nat i)
                (nfF_adn m' MU) ltac:(lia) eq_refl) as (k & RK & OKk & KR).
    step.
    clear RK.
    step.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed k)) by lia.
    destruct (Z.eqb_spec (bv_signed k) 0) as [K0 | K0]; cbn [negb]; cbv iota.
    - eapply l_byteF; eassumption.
    - step.
      rewrite (unsigned_lit (bv_unsigned name + Z.of_nat i)) by lia. rewrite rc_land7.
      step.
      rewrite (rc_lts_signed ((bv_unsigned name + Z.of_nat i) mod 8) (bv_signed k))
        by (pose proof (Z.mod_pos_bound (bv_unsigned name + Z.of_nat i) 8 ltac:(lia)); lia).
      replace ((bv_unsigned name + Z.of_nat i) mod 8 <? bv_signed k) with true
        by (symmetry; apply Z.ltb_lt; lia).
      cbn [negb]. cbv iota.
      step.
      eapply l_byteF; eassumption.
  Qed.

  Lemma loopF : forall k i, (i + k = 16)%nat -> (0 < k)%nat -> bv_unsigned name <> 0 -> head_okF i.
  Proof.
    induction k as [|k IH]; intros i Hik Hk NZ; [lia|].
    apply l_headF; [lia | exact NZ |].
    intros Hlt. apply IH; [lia | lia | exact NZ].
  Qed.
End NFF.

Theorem name_field_holds_F : asan_memset_contract_F -> name_field_contract_F.
Proof.
  intros AMS. unfold asan_memset_contract_F, ASAN_MEMSET_K in AMS. cbv zeta in AMS.
  unfold name_field_contract_F, NAME_FIELD, NAME_FIELD_K.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    name nb junk ST Hm0 Hm8 Hm288 HNW HN16 HN HNB Dfm Dfn DfN DNm DNn MI HC HSW HHM HAE ADm ADn ADN HAN HRT
    RB RIMG RWIN RWS RM8 RMS RNB RNBS RN16 RN16S.
  unfold shadow_addr, ASAN_K in RMS.
  (* the two loads of the shadow base read the GOT cell and the cell of the shadow offset, inside the image *)
  assert (RG8 : rng RNG 657648 8)
    by (apply (rng_sub RNG IMG_LO (IMG_HI - IMG_LO)); [exact RIMG | unfold IMG_LO; lia | unfold IMG_LO, IMG_HI; lia]).
  assert (RC8 : rng RNG 693944 8)
    by (apply (rng_sub RNG IMG_LO (IMG_HI - IMG_LO)); [exact RIMG | unfold IMG_LO; lia | unfold IMG_LO, IMG_HI; lia]).
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
  pose proof (zr_word a1) as Ra1. unfold inr64 in Ra1.
  pose proof (zr_word name) as Rnm. unfold inr64 in Rnm.
  pose proof ST as (Rlo & _ & _).
  assert (HBn : bytes_at rsegs m (bv_unsigned name) nb /\
                (bv_unsigned name <> 0 -> name_ok nb /\ bv_unsigned name + Z.of_nat (length nb) <= 2^64) /\
                (bv_unsigned name = 0 -> nb = [])).
  { destruct HNB as [(E & ->) | (E & OK & L & B)].
    - split; [apply bytes_at_nil; pose proof (zr_word name) as R; unfold inr64 in R; lia|]. split; [tauto|]. auto.
    - split; [exact B|]. split; [auto|]. intros; contradiction. }
  clear HNB. destruct HBn as (HBn & Hname & Hnil).
  pose proof (nf_aw m (bv_unsigned sp) (bv_unsigned a1) HHM HAE ADN) as AW.
  pose proof (nf_drt (bv_unsigned sp) (bv_unsigned a1) HHM HRT) as DRT.
  pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 16)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* addi sp,sp,-32 ; the four saves (window) *)
  step.
  carve_frame 32%nat ST.
  step. step. step. step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mA end.
  pose proof (asan_cells_kept _ m mA HC MU DRT) as HCA.
  pose proof (shadow_rw_kept m mA HSW (munch_meta _ m mA MU AW) WM) as HSWA.
  pose proof (addressable_kept m mA _ _ ADN (munch_meta _ m mA MU AW)) as ADNA.
  pose proof HCA as (Hk & Hg & _).
  pose proof (rd_le8 rsegs mA _ _ Hg) as RG. pose proof (rd_le8 rsegs mA _ _ Hk) as RC.
  unfold GOT_CELL_K, CELL_K, ASAN_K in RG, RC.
  clear Hk Hg.
  (* mv s0,a1 ; auipc ; ld a1 (GOT cell, RG8) ; ld s2 (shadow base, RC8) *)
  step. step. step. step.
  clear RG RC.
  (* mv s1,a0 ; li a2,16 ; mv a0,s0 ; li a1,0 ; jal __asan_memset *)
  step. step. step. step. step.
  assert (EU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  pose proof ADNA as (_ & _ & _ & HA7).
  pose proof (proj1 (HA7 7 ltac:(lia))) as A7.
  eapply evtF_cut.
  { eapply AMS with (junk := junk) (lo := bv_unsigned sp - 2240).
    all: rewrite ?EU; try change (bv_unsigned (Z_to_bv 64 16)) with 16.
    - exact HN.
    - lia.
    - exact ADNA.
    - unfold end_in_app. right. exact HAN.
    - right. exact A7.
    - exact HRT.
    - lia.
    - exact ST.
    - lia.
    - exact HHM.
    - lia.
    - exact HCA.
    - exact HSWA.
    - exact MI.
    - exact RB.
    - exact RIMG.
    - (* the callee's window [sp - 32 - 2208, sp - 32) inside the window K *)
      eapply rng_sub; [exact RWIN | lia | lia].
    - exact RN16.
    - unfold sh_word_rng, sh_al8_lo, sh_al8_hi. right. exact RN16S.
    - (* the shadow word cover of the callee's window [sp - 2240, sp - 32) *)
      unfold sh_word_rng, sh_al8_lo, sh_al8_hi. right.
      replace (bv_unsigned sp + -32 - 2208) with (bv_unsigned sp - 2240) by lia.
      replace (bv_unsigned sp - 2240 + 2208 - 1) with (bv_unsigned sp - 32 - 1) by lia.
      exact RWS. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
              -> & MU2 & WM2 & MI2 & ST2 & RW2 & HC2 & HSW2).
  unfold ASAN_MEMSET_K in MU2.
  rewrite !unsigned_lit in MU2 by lia.
  rewrite unsigned_lit in ST2 by lia.
  rewrite !unsigned_lit in RW2 by lia.
  change (Z.to_nat 16) with 16%nat in RW2.
  change (0 mod 256) with 0 in RW2.
  transport_after_call rsegs mA m2 MU2 WM2.
  clear MU2 WM2.
  replace (ret_pc (Z_to_bv 64 555548)) with (Z_to_bv 64 555548) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct RW2 as [[_ HB1] HW1]. cbn [cells_bytes cbytes cells_size csize Nat.add] in HB1, HW1.
  rewrite app_nil_r in HB1.
  pose proof (nf_sh8 m2 (bv_unsigned a0 + 280) (addressable_kept m m2 _ _ ADm (munch_meta _ m m2 MU AW))
                (nf_mod280 _ Hm8)) as RS8.
  pose proof (rd_le8 rsegs m2 _ name HNW) as HR.
  (* andi a0,s1,7 ; bnez a0 (not taken: m mod 8 = 0) *)
  step. step.
  replace (Z.land (bv_unsigned a0) 7) with 0
    by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; rewrite Hm8; reflexivity).
  if_false.
  (* addi a0,s1,280 ; srli ; add s2 ; lbu (shadow byte 0, RMS) ; bnez (not taken) *)
  step. step.
  rewrite (unsigned_lit (bv_unsigned a0 + 280)) by lia. rewrite rc_shr3.
  step. step. step.
  nfF_pc_false_vm.
  (* ld a1,0(a0) (RM8) ; beqz a1 *)
  step. step.
  destruct (Z.eq_dec (bv_unsigned name) 0) as [Z0 | NZ].
  - rewrite (rc_eq0w name Z0). cbv iota.
    assert (EN : nmf nb = repeat (Z_to_bv 8 0) 16) by (rewrite (Hnil Z0); reflexivity).
    eapply epiF with (wm := a0) (wn := a1) (name := name) (nb := nb).
    all: try eassumption.
    all: try lia.
    all: try (unfold ninvF; rewrite EN;
              split; [exact HW1|]; split; [reflexivity|]; split; [exact HB1|]; split; [exact FR|];
              split; [exact HNW|]; split; [exact HBn|]; split; [exact MU|]; split; [exact WM|];
              split; [exact MI2 | exact ST2]).
  - rewrite (rc_neq0w name NZ). cbv iota.
    (* li a3,0 ; not a4,s0 ; li a5,16 *)
    step. step. step.
    pose proof loopF as HL. unfold head_okF in HL.
    eapply HL with (k := 16%nat) (i := 0%nat) (wm := a0) (wn := a1) (name := name) (nb := nb).
    all: try eassumption.
    all: try lia.
    all: try (intros; lia).
    all: try (rewrite (zb_lxor_ones (bv_unsigned a1)) by lia; rewrite unsigned_lit by lia; reflexivity).
    all: try (unfold ninvF; change (firstn 0 nb ++ repeat (Z_to_bv 8 0) (16 - 0)) with (repeat (Z_to_bv 8 0) 16);
              split; [exact HW1|]; split; [reflexivity|]; split; [exact HB1|]; split; [exact FR|];
              split; [exact HNW|]; split; [exact HBn|]; split; [exact MU|]; split; [exact WM|];
              split; [exact MI2 | exact ST2]).
Qed.

(* The plain theorem's statement, back from the footprint form at ExecF.RNG_all, from the same callee contract (in
   footprint form). *)
Theorem name_field_holds_of_F : asan_memset_contract_F -> name_field_contract.
Proof. intros AMS. exact (name_field_contract_of_F (name_field_holds_F AMS)). Qed.
