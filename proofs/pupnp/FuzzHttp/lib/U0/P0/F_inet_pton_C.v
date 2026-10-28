(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes STRW_tac.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_syscalls F_memmove F_inet_pton_A F_inet_pton_B.
Import ListNotations.
Open Scope bv_scope.
Local Ltac flia ::= flia_cheap.

Notation w z := (Z_to_bv 64 z) (only parsing).
Ltac zs := zstep; fix_lit_store.

Lemma u8arr_of_cells : forall m A cs, rw_cells rsegs m A cs -> u8arr rsegs m A (cells_bytes cs) /\ length (cells_bytes cs) = cells_size cs.
Proof.
  intros m A cs [[Hwf Hb] Hw]. pose proof (cells_bytes_length cs Hwf) as L.
  split; [split; [exact Hb| rewrite L; exact Hw] | exact L].
Qed.

Lemma swrap32_small : forall x, (-2^31 <= x < 2^31)%Z -> bv_swrap 32 x = x.
Proof. intros x Hx. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. cbn. cbn in Hx. lia. Qed.

Lemma mm_result_length : forall us a b c, (b + c <= length us)%nat -> (a + c <= length us)%nat ->
  length (mm_result us a b c) = length us.
Proof. intros. unfold mm_result, slice. rewrite upd_bytes_length; [reflexivity|]. rewrite firstn_length, skipn_length. lia. Qed.

Lemma signed_lit : forall v, (-2^63 <= v < 2^63)%Z -> bv_signed (Z_to_bv 64 v) = v.
Proof.
  intros v Hv. rewrite zb_signed, unsigned_lit_wrap.
  destruct (Z.lt_ge_cases v 0).
  - rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia.
    destruct (Z.ltb_spec0 (v + 1 * 2^64) (2^63)); lia.
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec0 v (2^63)); lia.
Qed.

Lemma land7_range : forall i, (0 <= i)%Z -> (0 <= Z.land i 7 <= 7)%Z.
Proof.
  intros i Hi.
  replace (Z.land i 7) with (i mod 8)%Z by (change 7%Z with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
  pose proof (Z.mod_pos_bound i 8%Z ltac:(lia)). lia.
Qed.

Section IP.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
            (S : Z) (str : list byte) (A : Z) (N : nat) (canary : word) (lo : Z).
  Hypothesis LO : (lo <= bv_unsigned sp - 80)%Z.
  Hypothesis BND : (0 <= S /\ S + Z.of_nat (length str) + 1 <= 2^64 /\ 0 <= A /\ A + Z.of_nat N <= 2^64 /\ 0 <= lo /\ bv_unsigned sp < 2^64)%Z.
  Hypothesis SEPS : (S + Z.of_nat (length str) + 1 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= S)%Z.
  Hypothesis SEPA : (A + Z.of_nat N <= bv_unsigned sp - 80 \/ bv_unsigned sp <= A)%Z.
  Hypothesis SEPAS : (A + Z.of_nat N <= S \/ S + Z.of_nat (length str) + 1 <= A)%Z.
  Hypothesis SEPG : (got_ssp + 8 <= bv_unsigned sp - 80)%Z.
  Hypothesis SEPC : (ssp_guard + 8 <= bv_unsigned sp - 80)%Z.
  Hypothesis SEPAG : (A + Z.of_nat N <= got_ssp \/ got_ssp + 8 <= A)%Z.
  Hypothesis SEPAC : (A + Z.of_nat N <= ssp_guard \/ ssp_guard + 8 <= A)%Z.

  Notation len := (Z.of_nat (length str)).
  Notation full := (str ++ [Z_to_bv 8 0]).
  Notation SP := (bv_unsigned sp).
  Notation W := [(bv_unsigned sp - 80, bv_unsigned sp); (A, A + Z.of_nat N)]%Z.
  Notation POST := (inet_pton_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str A N canary lo m).

  Notation INV' := (INV ra sp s0 s1 s2 s3 s4 s5 m S str A N canary lo).
  Notation VR' := (VR sp gp tp s6 s7 s8 s9 s10 s11).
  Notation CONTv' := (CONTv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m S str A N canary lo).
  Notation str_read' := (str_read ra sp s0 s1 s2 s3 s4 s5 m S str A N canary lo SEPS SEPA SEPAS SEPG SEPC).
  Notation out_store' := (out_store ra sp s0 s1 s2 s3 s4 s5 m S str A N canary lo LO BND SEPS SEPA SEPAS SEPG SEPC SEPAG SEPAC).
  Notation ip_exit' := (ip_exit ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m S str A N canary lo LO BND).
  Notation ip_ret0' := (ip_ret0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m S str A N canary lo LO BND).

  Notation ip_store' := (ip_store ra sp s0 s1 s2 s3 s4 s5 m S str A N canary lo LO BND SEPS SEPA SEPAS SEPG SEPC SEPAG SEPAC).
  Notation v4b_loop' := (v4b_loop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m S str A N canary lo LO BND SEPS SEPA SEPAS SEPG SEPC SEPAG SEPAC).

  Ltac st_name :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs0) _) =>
      repeat match goal with
      | H : store_ok _ m1 _ _ = true |- _ => clear H
      | H : ov_read_bytes _ m1 _ _ = Some _ |- _ => clear H
      | H : INV' m1 |- _ => clear H
      end;
      let m' := fresh "m" in remember (write_to_mem m1 a bs0) as m' eqn:E; clear E; try clear m1
    end.
  Ltac open_inv I := destruct I as (STR & MI & MU & WM & STK & GOT & GUARD & FR & (ips & IPS & LIP) & (outs & OUT & LOUT)); unfold FRC in FR.

  Notation v4a_loop' := (v4a_loop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m S str A N canary lo LO BND SEPS SEPA SEPAS SEPG SEPC SEPAG SEPAC).

  #[using="S str A N lo BND SEPS SEPA SEPAS SEPG SEPC"] Lemma frame_split : forall m1 j16 cs, rw_cells rsegs m1 (SP + -80) (CB 16 j16 :: cs) ->
    u8arr rsegs m1 (SP + -80) j16 /\ length j16 = 16%nat /\ rw_cells rsegs m1 (SP + -64) cs.
  Proof.
    intros m1 j16 cs [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [L Hwf].
    cbn [cells_bytes cbytes] in Hb. apply bytes_at_app in Hb. destruct Hb as [Hb1 Hb2]. rewrite L in Hb2.
    cbn [cells_size csize] in Hw.
    assert (W1 : wr_at rsegs m1 (SP + -80) 16 /\ wr_at rsegs m1 (SP + -64) (Z.of_nat (cells_size cs))).
    { destruct Hw as (H1 & H2 & H3). split; (split; [lia|]; split; [lia|]); intros i Hi.
      - apply H3. lia.
      - replace (SP + -64 + i)%Z with (SP + -80 + (16 + i))%Z by lia. apply H3. lia. }
    destruct W1 as [W1 W2].
    split; [split; [exact Hb1| rewrite L; exact W1] |]. split; [exact L|].
    split; [split; [exact Hwf|] | exact W2]. replace (SP + -64)%Z with (SP + -80 + Z.of_nat 16)%Z by lia. exact Hb2.
  Qed.

  Ltac ip_bundle :=
    lazymatch goal with FR0 : rw_cells rsegs ?mm (SP + -80) (CB 16 ?j :: _) |- _ =>
      destruct (frame_split _ _ _ FR0) as (IPS0 & LIP0 & FRC0); clear FR0;
      let I := fresh "I" in
      assert (I : INV' mm); [ split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
                              split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [exact FRC0|];
                              split; [ exists j; split; [exact IPS0 | exact LIP0] | eexists; split; eassumption ] | ] end.

  #[using="LO BND SEPS SEPA SEPAS SEPG SEPC SEPAG SEPAC"] Lemma ip_entry_v4 : forall (ojunk : list byte) t0 t1 t2 (xa0 xa1 xa2 : word) a3 a4 a5 a6 a7 t3 t4 t5 t6,
    rw_cells rsegs m A [CB N ojunk] -> bytes_at rsegs m S full ->
    rw_cells rsegs m got_ssp [C8 (w ssp_guard)] -> rw_cells rsegs m ssp_guard [C8 canary] ->
    stk rsegs m lo SP -> mem_inv rsegs m -> (4 <= Z.of_nat N)%Z -> xa0 = w 2 -> xa1 = w S -> xa2 = w A ->
    evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 xa0 xa1 xa2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (w 0x1a008) fc None m (seg_rom rsegs)).
  Proof.
    intros until t6. intros OUTC STR0 GOT0 GUARD0 STK0 MI0 HN4 -> -> ->.
    pose proof BND as BD; unfold got_ssp, ssp_guard in *.
    pose proof (munch_refl W m) as MU0; pose proof (wmono_refl rsegs m) as WM0.
    pose proof (u8arr_of_rw_cells rsegs _ _ _ _ OUTC) as OUT0. pose proof (rw_cells_CB_length rsegs _ _ _ _ OUTC) as LOUT0. clear OUTC.
    carve_frame 80%nat STK0.
    do 13 zs. zs. if_false. zs. zs. if_false. do 7 zs.
    ip_bundle.
    lazymatch goal with I : INV' ?mm |- _ =>
      eapply (v4a_loop' 4 mm A 0 0); [exact I | lia | lia | lia | lia | lia | word_eq_tac | reflexivity] end.
  Qed.

  Hypothesis N16 : N = 16%nat.

  Definition V6 (x1 xt0 xt1 xt2 : word) (i : Z) (xa0 xa1 xa3 : word) (xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6 : word) :=
    mkR x1 (w (SP + -80)) gp tp xt0 xt1 xt2 (w ssp_guard) (w i) xa0 xa1 (w A) xa3 (w (SP + -80)) (w 7) (w 10) (w 5)
        xs2 xs3 xs4 xs5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6.

  Definition V6x (x1 xt0 xt1 xt2 : word) (i : Z) (xa0 xa1 xa3 xa4 xa5 xa6 xa7 : word) (xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6 : word) :=
    mkR x1 (w (SP + -80)) gp tp xt0 xt1 xt2 (w ssp_guard) (w i) xa0 xa1 (w A) xa3 xa4 xa5 xa6 xa7
        xs2 xs3 xs4 xs5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6.

  Ltac rebuild_inv :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let I := fresh "I" in
      assert (I : INV' mm); [ split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
                              split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
                              split; [ eexists; split; [eassumption | first [eassumption | reflexivity] ]
                                    | eexists; split; [eassumption | first [eassumption | reflexivity] ] ] | ] end.

  Ltac out_st o :=
    let SOK := fresh "SOK" in
    lazymatch goal with I : INV' ?m1 |- _ =>
      pose proof (proj1 (out_store' m1 o (w (A + o)) [Z_to_bv 8 0] I ltac:(lia) ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia) eq_refl)) as SOK end;
    zs;
    lazymatch goal with I : INV' ?m1 |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs0) _) =>
      let I2 := fresh "I" in
      pose proof (proj2 (out_store' m1 o a bs0 I ltac:(lia) ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia) ltac:(first [reflexivity | apply length_le1]))) as I2;
      clear I end;
    st_name.

  #[using="LO BND SEPS SEPA SEPAS SEPG SEPC SEPAG SEPAC N16"] Lemma v6_out : forall m1 (i k fl : Z) x1 xt0 xt1 xt2 (xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs2 : word) xs3 xs4 xs5 xt3 xt4 xt5 xt6,
    INV' m1 -> (0 <= k <= len)%Z -> (fl = 0 \/ fl = 1)%Z -> xa1 = w (S + k) -> xs2 = w fl ->
    evt rsegs POST (MS (V6x x1 xt0 xt1 xt2 i xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6) F (w 0x1a2f4) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until xt6. intros I Hk Hfl -> ->. pose proof I as I0; open_inv I. pose proof BND as BD. unfold V6x. unfold got_ssp, ssp_guard in *.
    pose proof (rw_cells_of_u8arr rsegs _ _ _ IPS) as IPC. rewrite LIP in IPC.
    do 13 zs.
    clear IPC STR MI MU WM STK GOT GUARD FR IPS OUT.
    out_st 0%Z. out_st 1%Z. out_st 2%Z. out_st 3%Z. zs.
    out_st 4%Z. out_st 5%Z. out_st 6%Z. out_st 7%Z. zs.
    out_st 8%Z. out_st 9%Z. out_st 10%Z. out_st 11%Z. zs.
    out_st 12%Z. out_st 13%Z. out_st 14%Z. out_st 15%Z.
    zs. if_cases Kf; zify_cond Kf.
    -   do 8 zs.
      lazymatch goal with I : INV' ?mm |- _ =>
        eapply (v4b_loop' 4 mm (A + 12) k 0); [exact I | lia | lia | lia | lia | lia | word_eq_tac | word_eq_tac] end.
    - zs. zs. lazymatch goal with I : INV' ?mm |- _ => apply ip_exit'; [exact I | right; reflexivity] end.
  Qed.

  Ltac ip_st o :=
    let SOK := fresh "SOK" in
    lazymatch goal with I : INV' ?m1 |- _ =>
      pose proof (proj1 (ip_store' m1 o (w (SP + -80 + o)) [Z_to_bv 8 0; Z_to_bv 8 0] I ltac:(lia) ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia) eq_refl)) as SOK end;
    zs;
    lazymatch goal with I : INV' ?m1 |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs0) _) =>
      let I2 := fresh "I" in
      pose proof (proj2 (ip_store' m1 o a bs0 I ltac:(lia) ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia) ltac:(first [reflexivity | apply length_le2]))) as I2;
      clear I end;
    st_name.

  #[using="LO BND SEPS SEPA SEPAS SEPG SEPC SEPAG SEPAC N16"] Lemma v6_zfill : forall (n : nat) m1 (q e i k fl : Z) x1 xt0 xt1 xt2 (xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs2 : word) xs3 xs4 xs5 xt3 xt4 xt5 xt6,
    INV' m1 -> (Z.to_nat (e - q) = n) -> (0 <= q < e)%Z -> (e <= 8)%Z -> (0 <= k <= len)%Z -> (fl = 0 \/ fl = 1)%Z ->
    xa1 = w (S + k) -> xs2 = w fl -> xa0 = w (SP + -80 + 2 * q) -> xa3 = w (SP + -80 + 2 * e) ->
    evt rsegs POST (MS (V6x x1 xt0 xt1 xt2 i xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6) F (w 0x1a2e8) fc None m1 (seg_rom rsegs)).
  Proof.
    induction n as [|n IH]; [lia|].
    intros until xt6. intros I Hn Hq He Hk Hfl -> -> -> ->. pose proof BND as BD. unfold V6x. unfold got_ssp, ssp_guard in *.
    ip_st (2 * q)%Z.
    zs. zs. if_cases K; zify_cond K.
    - lazymatch goal with I : INV' ?mm |- _ =>
        eapply (IH mm (q + 1)%Z e i k fl); [exact I | lia | lia | lia | lia | exact Hfl | reflexivity | reflexivity | word_eq_tac | reflexivity] end.
    - lazymatch goal with I : INV' ?mm |- _ =>
        eapply (v6_out mm i k fl); [exact I | lia | exact Hfl | reflexivity | reflexivity] end.
  Qed.

  #[using="LO BND SEPS SEPA SEPAS SEPG SEPC SEPAG SEPAC N16"] Lemma v6_tail : forall m1 (brk i k fl : Z) x1 xt0 xt1 xt2 (xa0 xa1 xa3 xs2 : word) xs3 xs4 xs5 xt3 xt4 xt5 xt6,
    INV' m1 -> (-1 <= brk <= i)%Z -> (0 <= i <= 7)%Z -> (0 <= k <= len)%Z -> (fl = 0 \/ fl = 1)%Z ->
    xa0 = w brk -> xa1 = w (S + k) -> xs2 = w fl ->
    evt rsegs POST (MS (V6 x1 xt0 xt1 xt2 i xa0 xa1 xa3 xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6) F (w 0x1a278) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until xt6. intros I Hb Hi Hk Hfl -> -> ->. pose proof BND as BD. unfold V6. unfold got_ssp, ssp_guard in *.
    zs. if_cases Kb; zify_cond Kb.
    {   eapply (v6_out m1 i k fl); [exact I | lia | exact Hfl | reflexivity | reflexivity]. }
    assert (Hb0 : (0 <= brk)%Z).
    { destruct (Z.eq_dec brk (-1)) as [->|]; [| lia]. exfalso.
      change ((-1) mod 18446744073709551616)%Z with 18446744073709551615%Z in Kb. lia. }
    clear Kb.
    pose proof I as I0; open_inv I. unfold got_ssp, ssp_guard in *.
    do 13 zs.
    rewrite !(swrap32_small (i - brk)) by lia.
    rewrite !(Z.mod_small (i - brk) 18446744073709551616) by lia.
    rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 1)%Z with 2%Z.
    rewrite !(Z.mod_small ((i - brk) * 2) 18446744073709551616) by lia.
    rewrite !(swrap32_small ((i - brk) * 2 + 2)) by lia.
    rewrite !(Z.mod_small (SP + -80 + brk * 2) 18446744073709551616) by lia.
    rewrite !(Z.mod_small (i * 2) 18446744073709551616) by lia.
    zs. eapply evt_cut.
    { eapply memmove_spec; [ exact IPS | lia | | | | exact MI ]; rewrite ?unsigned_lit by lia; rewrite ?LIP; lia. }

    intros ms' PO. destruct_exs PO. destruct PO as [E [MUc [WMc [MIc PO]]]]. subst ms'.
    rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in PO by lia.
    lazymatch type of MUc with munch _ _ ?m' => transport_after_call rsegs m1 m' MUc WMc end.
    clear MUc WMc MI. try clear m1.
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with H : u8arr rsegs ?mm (SP + -80) ?xs |- _ =>
      assert (length xs = 16%nat) by (rewrite <- LIP; apply mm_result_length; rewrite LIP; lia) end.
    rebuild_inv. clear I0.
    do 4 zs. if_cases K6; zify_cond K6.
    {   lazymatch goal with I : INV' ?mm |- _ =>
        eapply (v6_out mm i k fl); [exact I | lia | exact Hfl | reflexivity | reflexivity] end. }
    rewrite signed_lit in K6 by lia.
    zs. zs. zs. if_cases K7; [clear K7 | clear K7; zs].
    all: do 5 zs.
    - rewrite (swrap32_small (7 - i)) by lia. rewrite (Z.mod_small (7 - i) 18446744073709551616) by lia.
      rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1)%Z with 2%Z.
      lazymatch goal with I : INV' ?mm |- _ =>
        eapply (v6_zfill (Z.to_nat (7 - i)) mm brk (brk + (7 - i))%Z i k fl);
          [exact I | lia | lia | lia | lia | exact Hfl | reflexivity | reflexivity | word_eq_tac | word_eq_tac] end.
    - lazymatch goal with I : INV' ?mm |- _ =>
        eapply (v6_zfill 1 mm brk (brk + 1)%Z i k fl);
          [exact I | lia | lia | lia | lia | exact Hfl | reflexivity | reflexivity | word_eq_tac | word_eq_tac] end.
  Qed.

  Definition CONT6 (i : Z) : Prop :=
    forall m2 (k brk : Z) (b : byte) x1 (xt0 : word) xt1 xt2 (xa0 xa1 : word) xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6,
      INV' m2 -> (0 <= k <= len)%Z -> nth_error full (Z.to_nat k) = Some b -> (-1 <= brk <= i)%Z ->
      xt0 = w (bv_unsigned b) -> xa1 = w (S + k) -> xa0 = w brk ->
      evt rsegs POST (MS (V6 x1 xt0 xt1 xt2 i xa0 xa1 (w 58) xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6) F (w 0x1a120) fc None m2 (seg_rom rsegs)).

  #[using="SEPS SEPA SEPAS SEPG SEPC N16"] Lemma str_read2 : forall m1 p a, INV' m1 -> (0 <= p <= len)%Z -> a = w (S + p) ->
    exists b, ov_read_bytes rsegs m1 a 1 = Some [b] /\ nth_error full (Z.to_nat p) = Some b /\
              (0 <= bv_unsigned b < 256)%Z /\ (bv_unsigned b <> 0%Z -> p < len)%Z.
  Proof.
    intros m1 p a I Hp Ha. pose proof I as I'; open_inv I.
    destruct (nth_error full (Z.to_nat p)) as [b|] eqn:E.
    2:{ apply nth_error_None in E. rewrite length_app in E. cbn in E. lia. }
    destruct (str_read' m1 p a I' Hp Ha) as (b' & RD & R & Hb).
    assert (b' = b). { pose proof (u8ro_read rsegs m1 S full p b a STR E ltac:(lia) ltac:(subst a; reflexivity)) as RD2. rewrite RD in RD2. congruence. }
    subst b'. exists b. auto.
  Qed.

  #[using="LO BND SEPS SEPA SEPAS SEPG SEPC SEPAG SEPAC N16"] Lemma v6_store : forall m1 (i k j brk : Z) x1 xt0 (xt1 : word) xt2 (xa0 xa1 : word) xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6,
    INV' m1 -> (i < 7 -> CONT6 i)%Z -> (0 <= i <= 7)%Z -> (1 <= j <= 4)%Z -> (0 <= k)%Z -> (k + j <= len)%Z -> (-1 <= brk <= i - 1)%Z ->
    xt1 = w j -> xa1 = w (S + k) -> xa0 = w brk ->
    evt rsegs POST (MS (V6 x1 xt0 xt1 xt2 i xa0 xa1 (w 58) xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6) F (w 0x1a1f8) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until xt6. intros I CO Hi Hj Hk Hkj Hb -> -> ->. pose proof BND as BD. unfold V6. unfold got_ssp, ssp_guard in *.
    pose proof (land7_range i ltac:(lia)) as L7.
    destruct (str_read2 m1 (k + j) (w (S + (k + j))) I ltac:(lia) ltac:(f_equal; lia)) as (bj & RDj & Hnj & Rj & Hbj).
    zs. zs. zs. zs. zs.
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1)%Z with 2%Z.
    ip_st (Z.land i 7 * 2)%Z.
    zs. if_cases Kz; zify_cond Kz.
    -   zs. zs. if_cases Kb; [clear Kb|].
      + lazymatch goal with I : INV' ?mm |- _ =>
          eapply (v6_tail mm brk i k 1); [exact I | lia | lia | lia | lia | reflexivity | reflexivity | reflexivity] end.
      + zs. zs. if_cases K7; zify_cond K7.
        * lazymatch goal with I : INV' ?mm |- _ =>
            eapply (v6_tail mm brk i k 1); [exact I | lia | lia | lia | lia | reflexivity | reflexivity | reflexivity] end.
        * lazymatch goal with I : INV' ?mm |- _ => apply ip_ret0'; exact I end.
    - assert (Hkj2 : (k + j < len)%Z) by (apply Hbj; exact Kz).
      zs. if_cases K7; zify_cond K7. { lazymatch goal with I : INV' ?mm |- _ => apply ip_ret0'; exact I end. }
      zs. if_cases Kc; zify_cond Kc.
      +
        zs. zs. if_cases Kd; zify_cond Kd. { lazymatch goal with I : INV' ?mm |- _ => apply ip_ret0'; exact I end. }
        zs. zs. if_cases K5; [clear K5 | clear K5; zs; if_cases Kn; [ lazymatch goal with I : INV' ?mm |- _ => apply ip_ret0'; exact I end | clear Kn ] ].
        all: zs; zs; rewrite (swrap32_small (i + 1)) by lia.
        all: pose proof (land7_range (i + 1) ltac:(lia)) as L8.
        all: zs; zs; zs; zs; rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 1)%Z with 2%Z.
        all: ip_st (Z.land (i + 1) 7 * 2)%Z.
        all: zs; lazymatch goal with I : INV' ?mm |- _ =>
          eapply (v6_tail mm brk (i + 1)%Z k 0); [exact I | lia | lia | lia | lia | reflexivity | reflexivity | reflexivity] end.
      +
        lazymatch goal with I : INV' ?mm |- _ =>
          destruct (str_read2 mm (k + j + 1) (w (S + (k + j + 1))) I ltac:(lia) ltac:(f_equal; lia)) as (bn & RDn & Hnn & Rn & Hbn) end.
        zs. zs. zs. specialize (CO ltac:(lia)). unfold CONTv in CO.
        lazymatch goal with I : INV' ?mm |- _ =>
          eapply (CO mm (k + j + 1)%Z brk bn); [exact I | lia | exact Hnn | lia | reflexivity | word_eq_tac | reflexivity] end.
  Qed.

  Ltac nz_from K Hb :=
    apply Hb; let E := fresh "E" in intros E; rewrite E in K; revert K; clear; intros K; cbv in K;
    first [ discriminate | lia | exfalso; apply K; reflexivity | easy ].

  Ltac use_store iv kv jv bv :=
    lazymatch goal with I : INV' ?mm, CO : (_ -> CONT6 _)%Z |- _ =>
      eapply (v6_store mm iv kv jv bv); [exact I | exact CO | lia | lia | lia | lia | lia | reflexivity | reflexivity | reflexivity] end.
  Ltac use_ret0 := lazymatch goal with I : INV' ?mm |- _ => apply ip_ret0'; exact I end.

  #[using="LO BND SEPS SEPA SEPAS SEPG SEPC SEPAG SEPAC N16"] Lemma v6_g3 : forall m1 (i k brk : Z) x1 (xt0 xt1 xt2 xa0 xa1 : word) xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6,
    INV' m1 -> (i < 7 -> CONT6 i)%Z -> (0 <= i <= 7)%Z -> (0 <= k)%Z -> (k + 3 <= len)%Z -> (-1 <= brk <= i - 1)%Z ->
    xa1 = w (S + k) -> xa0 = w brk ->
    evt rsegs POST (MS (V6 x1 xt0 xt1 xt2 i xa0 xa1 (w 58) xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6) F (w 0x1a1b0) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until xt6. intros I CO Hi Hk Hk3 Hb -> ->. pose proof BND as BD. unfold V6. unfold got_ssp, ssp_guard in *.
    destruct (str_read2 m1 (k + 3) (w (S + (k + 3))) I ltac:(lia) ltac:(f_equal; lia)) as (b3 & RD3 & Hn3 & R3 & Hb3).
    do 5 zs. if_cases Kd; zify_cond Kd.
    - assert (Hk4 : (k + 3 < len)%Z) by nz_from Kd Hb3. do 4 zs. use_store i k 4%Z brk.
    - do 3 zs. if_cases Kl; zify_cond Kl.
      + zs. use_store i k 3%Z brk.
      + assert (Hk4 : (k + 3 < len)%Z) by nz_from Kl Hb3. do 5 zs. use_store i k 4%Z brk.
  Qed.

  #[using="LO BND SEPS SEPA SEPAS SEPG SEPC SEPAG SEPAC N16"] Lemma v6_g2 : forall m1 (i k brk : Z) x1 (xt0 xt1 xt2 xa0 xa1 : word) xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6,
    INV' m1 -> (i < 7 -> CONT6 i)%Z -> (0 <= i <= 7)%Z -> (0 <= k)%Z -> (k + 2 <= len)%Z -> (-1 <= brk <= i - 1)%Z ->
    xa1 = w (S + k) -> xa0 = w brk ->
    evt rsegs POST (MS (V6 x1 xt0 xt1 xt2 i xa0 xa1 (w 58) xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6) F (w 0x1a18c) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until xt6. intros I CO Hi Hk Hk2 Hb -> ->. pose proof BND as BD. unfold V6. unfold got_ssp, ssp_guard in *.
    destruct (str_read2 m1 (k + 2) (w (S + (k + 2))) I ltac:(lia) ltac:(f_equal; lia)) as (b2 & RD2 & Hn2 & R2 & Hb2).
    do 5 zs. if_cases Kd; zify_cond Kd.
    - assert (Hk3 : (k + 2 < len)%Z) by nz_from Kd Hb2.
      eapply (v6_g3 m1 i k brk); [exact I | exact CO | lia | lia | lia | lia | reflexivity | reflexivity].
    - do 3 zs. if_cases Kl; zify_cond Kl.
      + zs. zs. use_store i k 2%Z brk.
      + assert (Hk3 : (k + 2 < len)%Z) by nz_from Kl Hb2. zs.
        eapply (v6_g3 m1 i k brk); [exact I | exact CO | lia | lia | lia | lia | reflexivity | reflexivity].
  Qed.

  #[using="LO BND SEPS SEPA SEPAS SEPG SEPC SEPAG SEPAC N16"] Lemma v6_g1 : forall m1 (i k brk : Z) x1 (xt0 xt1 xt2 xa0 xa1 : word) xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6,
    INV' m1 -> (i < 7 -> CONT6 i)%Z -> (0 <= i <= 7)%Z -> (0 <= k)%Z -> (k + 1 <= len)%Z -> (-1 <= brk <= i - 1)%Z ->
    xa1 = w (S + k) -> xa0 = w brk ->
    evt rsegs POST (MS (V6 x1 xt0 xt1 xt2 i xa0 xa1 (w 58) xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6) F (w 0x1a170) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until xt6. intros I CO Hi Hk Hk1 Hb -> ->. pose proof BND as BD. unfold V6. unfold got_ssp, ssp_guard in *.
    destruct (str_read2 m1 (k + 1) (w (S + (k + 1))) I ltac:(lia) ltac:(f_equal; lia)) as (b1 & RD1 & Hn1 & R1 & Hb1).
    do 3 zs. if_cases Kd; zify_cond Kd.
    - assert (Hk2 : (k + 1 < len)%Z) by nz_from Kd Hb1.
      eapply (v6_g2 m1 i k brk); [exact I | exact CO | lia | lia | lia | lia | reflexivity | reflexivity].
    - do 3 zs. if_cases Kl; zify_cond Kl.
      + zs. zs. use_store i k 1%Z brk.
      + assert (Hk2 : (k + 1 < len)%Z) by nz_from Kl Hb1. zs.
        eapply (v6_g2 m1 i k brk); [exact I | exact CO | lia | lia | lia | lia | reflexivity | reflexivity].
  Qed.

  #[using="LO BND SEPS SEPA SEPAS SEPG SEPC SEPAG SEPAC N16"] Lemma v6_grp : forall m1 (i k brk : Z) (b0 : byte) x1 (xt0 xt1 xt2 xa0 xa1 : word) xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6,
    INV' m1 -> (i < 7 -> CONT6 i)%Z -> (0 <= i <= 7)%Z -> (0 <= k <= len)%Z -> nth_error full (Z.to_nat k) = Some b0 -> (-1 <= brk <= i - 1)%Z ->
    xt0 = w (bv_unsigned b0) -> xa1 = w (S + k) -> xa0 = w brk ->
    evt rsegs POST (MS (V6 x1 xt0 xt1 xt2 i xa0 xa1 (w 58) xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6) F (w 0x1a154) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until xt6. intros I CO Hi Hk Hn0 Hb -> -> ->. pose proof BND as BD. unfold V6. unfold got_ssp, ssp_guard in *.
    destruct (str_read2 m1 k (w (S + k)) I ltac:(lia) ltac:(f_equal; lia)) as (b0' & RD0 & Hn0' & R0 & Hb0).
    rewrite Hn0 in Hn0'. injection Hn0' as <-.
    zs. replace (Z.land (bv_unsigned b0) 255) with (bv_unsigned b0).
    2:{ change 255%Z with (2^8 - 1)%Z. rewrite zb_land_mask, Z.mod_small by lia. reflexivity. }
    zs. zs. if_cases Kd; zify_cond Kd.
    - assert (Hk1 : (k < len)%Z) by nz_from Kd Hb0.
      eapply (v6_g1 m1 i k brk); [exact I | exact CO | lia | lia | lia | lia | reflexivity | reflexivity].
    - do 3 zs. if_cases Kl; zify_cond Kl.
      + use_ret0.
      + assert (Hk1 : (k < len)%Z) by nz_from Kl Hb0. zs.
        eapply (v6_g1 m1 i k brk); [exact I | exact CO | lia | lia | lia | lia | reflexivity | reflexivity].
  Qed.

  #[using="LO BND SEPS SEPA SEPAS SEPG SEPC SEPAG SEPAC N16"] Lemma v6_head : forall (fuel : nat) m1 (i k brk : Z) (b0 : byte) x1 (xt0 xt1 xt2 xa0 xa1 : word) xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6,
    INV' m1 -> (Z.to_nat (7 - i) < fuel)%nat -> (0 <= i <= 7)%Z -> (0 <= k <= len)%Z -> nth_error full (Z.to_nat k) = Some b0 ->
    (-1 <= brk <= i - 1)%Z ->
    xt0 = w (bv_unsigned b0) -> xa1 = w (S + k) -> xa0 = w brk ->
    evt rsegs POST (MS (V6 x1 xt0 xt1 xt2 i xa0 xa1 (w 58) xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6) F (w 0x1a124) fc None m1 (seg_rom rsegs)).
  Proof.
    induction fuel as [|fuel IH]; [lia|].
    intros until xt6. intros I Hf Hi Hk Hn0 Hb -> -> ->. pose proof BND as BD. unfold V6. unfold got_ssp, ssp_guard in *.
    assert (CO : (i < 7 -> CONT6 i)%Z).
    { intros Hi7. unfold CONT6. intros m2 k' brk' b' x1' xt0' xt1' xt2' xa0' xa1' xs2' xs3' xs4' xs5' xt3' xt4' xt5' xt6' I' Hk' Hn' Hb' -> -> ->.
      unfold V6. zs. try rewrite (swrap32_small (i + 1)) by lia.
      eapply (IH m2 (i + 1)%Z k' brk' b'); [exact I' | lia | lia | lia | exact Hn' | lia | reflexivity | reflexivity | reflexivity]. }
    destruct (str_read2 m1 k (w (S + k)) I ltac:(lia) ltac:(f_equal; lia)) as (b0' & RD0 & Hn0' & R0 & Hb0).
    rewrite Hn0 in Hn0'. injection Hn0' as <-.
    zs. if_cases Kc; zify_cond Kc.
    { eapply (v6_grp m1 i k brk b0); [exact I | exact CO | lia | lia | exact Hn0 | lia | reflexivity | reflexivity | reflexivity]. }
    zs. if_cases Kb; [clear Kb|].
    { eapply (v6_grp m1 i k brk b0); [exact I | exact CO | lia | lia | exact Hn0 | lia | reflexivity | reflexivity | reflexivity]. }
    assert (Hk1 : (k < len)%Z) by (apply Hb0; lia).
    pose proof (land7_range i ltac:(lia)) as L7.
    destruct (str_read2 m1 (k + 1) (w (S + (k + 1))) I ltac:(lia) ltac:(f_equal; lia)) as (b1 & RD1 & Hn1 & R1 & Hb1).
    zs. zs. zs. zs. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1)%Z with 2%Z.
    ip_st (Z.land i 7 * 2)%Z.
    zs. zs. if_cases Kz; zify_cond Kz.
    -   zs. zs.
      lazymatch goal with I : INV' ?mm |- _ =>
        eapply (v6_tail mm i i (k + 1) 1); [exact I | lia | lia | lia | lia | reflexivity | word_eq_tac | reflexivity] end.
    - zs. zs. if_cases K7; zify_cond K7.
      + specialize (CO ltac:(lia)). unfold CONT6 in CO.
        lazymatch goal with I : INV' ?mm |- _ =>
          eapply (CO mm (k + 1)%Z i b1); [exact I | lia | exact Hn1 | lia | reflexivity | word_eq_tac | reflexivity] end.
      + zs. use_ret0.
  Qed.

  #[using="LO BND SEPS SEPA SEPAS SEPG SEPC SEPAG SEPAC N16"] Lemma ip_entry_v6 : forall (ojunk : list byte) t0 t1 t2 (xa0 xa1 xa2 : word) a3 a4 a5 a6 a7 t3 t4 t5 t6,
    rw_cells rsegs m A [CB N ojunk] -> bytes_at rsegs m S full ->
    rw_cells rsegs m got_ssp [C8 (w ssp_guard)] -> rw_cells rsegs m ssp_guard [C8 canary] ->
    stk rsegs m lo SP -> mem_inv rsegs m -> xa0 = w 10 -> xa1 = w S -> xa2 = w A ->
    evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 xa0 xa1 xa2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (w 0x1a008) fc None m (seg_rom rsegs)).
  Proof.
    intros until t6. intros OUTC STR0 GOT0 GUARD0 STK0 MI0 -> -> ->.
    pose proof BND as BD; unfold got_ssp, ssp_guard in *.
    pose proof (munch_refl W m) as MU0; pose proof (wmono_refl rsegs m) as WM0.
    pose proof (u8arr_of_rw_cells rsegs _ _ _ _ OUTC) as OUT0. pose proof (rw_cells_CB_length rsegs _ _ _ _ OUTC) as LOUT0. clear OUTC.
    carve_frame 80%nat STK0.
    do 13 zs. zs. if_true.
    ip_bundle.
    lazymatch goal with I : INV' ?mm |- _ =>
      destruct (str_read2 mm 0 (w S) I ltac:(lia) ltac:(f_equal; lia)) as (b0 & RD0 & Hn0 & R0 & Hb0) end.
    zs. zs. zs. if_cases Kc; zify_cond Kc.
    -   do 7 zs.
      lazymatch goal with I : INV' ?mm |- _ =>
        eapply (v6_head 8 mm 0 0 (-1) b0); [exact I | lia | lia | lia | exact Hn0 | lia | reflexivity | word_eq_tac | reflexivity] end.
    - assert (Hk0 : (0 < len)%Z) by (apply Hb0; lia).
      lazymatch goal with I : INV' ?mm |- _ =>
        destruct (str_read2 mm 1 (w (S + 1)) I ltac:(lia) ltac:(f_equal; lia)) as (b1 & RD1 & Hn1 & R1 & Hb1) end.
      zs. zs. if_cases Kc2; zify_cond Kc2. { use_ret0. }
      zs. do 7 zs.
      lazymatch goal with I : INV' ?mm |- _ =>
        eapply (v6_head 8 mm 0 1 (-1) b1); [exact I | lia | lia | lia | exact Hn1 | lia | word_eq_tac | word_eq_tac | reflexivity] end.
  Qed.
End IP.

Theorem inet_pton_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str ojunk : list byte) (N : nat) (canary : word) (lo : Z),
  bytes_at rsegs m (bv_unsigned a1) (str ++ [Z_to_bv 8 0]) ->
  rw_cells rsegs m (bv_unsigned a2) [CB N ojunk] ->
  ((bv_unsigned a0 = 2 /\ 4 <= Z.of_nat N) \/ (bv_unsigned a0 = 10 /\ N = 16%nat))%Z ->
  rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m ssp_guard [C8 canary] ->
  stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 80)%Z ->
  (bv_unsigned a1 + Z.of_nat (length str) + 1 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  (bv_unsigned a2 + Z.of_nat N <= bv_unsigned sp - 80 \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
  (bv_unsigned a2 + Z.of_nat N <= bv_unsigned a1 \/ bv_unsigned a1 + Z.of_nat (length str) + 1 <= bv_unsigned a2)%Z ->
  (got_ssp + 8 <= bv_unsigned sp - 80)%Z -> (ssp_guard + 8 <= bv_unsigned sp - 80)%Z ->
  (bv_unsigned a2 + Z.of_nat N <= got_ssp \/ got_ssp + 8 <= bv_unsigned a2)%Z ->
  (bv_unsigned a2 + Z.of_nat N <= ssp_guard \/ ssp_guard + 8 <= bv_unsigned a2)%Z ->
  mem_inv rsegs m ->
  evt rsegs (inet_pton_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) str (bv_unsigned a2) N canary lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1a008) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros STR OUTC AF GOT GUARD STK LO SEPS SEPA SEPAS SEPG SEPC SEPAG SEPAC MI.
  pose proof (bytes_at_bound _ _ _ _ STR) as B. rewrite length_app in B. cbn [length] in B.
  pose proof (rw_cells_bound rsegs _ _ _ OUTC) as BA. cbn [cells_size csize Nat.add] in BA.
  pose proof STK as STK'. destruct STK' as [LO0 _]. pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R; cbn in R.
  assert (E1 : a1 = Z_to_bv 64 (bv_unsigned a1)) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (E2 : a2 = Z_to_bv 64 (bv_unsigned a2)) by (symmetry; apply Z_to_bv_bv_unsigned).
  destruct AF as [[AF HN]|[AF HN]].
  - assert (E0 : a0 = Z_to_bv 64 2) by (rewrite <- AF; symmetry; apply Z_to_bv_bv_unsigned).
    eapply ip_entry_v4; eauto; lia.
  - assert (E0 : a0 = Z_to_bv 64 10) by (rewrite <- AF; symmetry; apply Z_to_bv_bv_unsigned).
    eapply ip_entry_v6; eauto; lia.
Qed.
