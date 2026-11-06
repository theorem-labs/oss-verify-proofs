(* talk, PLAIN build: the two inlined copies of take_text (fuzz_link.c:318-328), the fragments
   F_take_al (0x1593c .. 0x15998, ends at 0x15a54) and F_take_kd (0x159e4 .. 0x15a3c, falls into
   0x15a40) of lib/Prog/talk_defs.v.

   Each copy: the strnlen loop over the payload pay = slice ck (a + 4) (l - 4) leaves s2 = nul_at pay;
   the cap test makes it k = min (nul_at pay) (cap - 1) (cut_text); memcpy copies k payload bytes
   into the buffer; `sb zero` puts the NUL at buffer + k. The memory steps after the memcpy do not
   name a register (tt_after_call, tt_after_store); the two walks differ only in their registers,
   their spill offset (0 for the alias cap, 0x18 for the kind cap) and their pcs. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import memcpy_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem talk_defs talk_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac.
Import ListNotations.
Local Open Scope Z_scope.

(* a fact `lia` must not case-split on *)
Definition tt_hold (P : Prop) : Prop := P.

(* --------------------------------------------------------------------------
   1. the payload and its first NUL
   -------------------------------------------------------------------------- *)

Lemma tt_nul_step : forall (pay : list byte) (i : nat) b,
  (i <= nul_at pay)%nat -> nth_error pay i = Some b ->
  (bz b = 0 -> nul_at pay = i) /\ (bz b <> 0 -> (S i <= nul_at pay)%nat).
Proof.
  induction pay as [|x pay IH]; intros i b Hi Hn; [destruct i; discriminate|].
  destruct i as [|i]; cbn [nul_at nth_error] in Hi, Hn |- *.
  - injection Hn as ->. destruct (Z.eqb_spec (bz b) 0) as [E|E]; cbv beta iota in *; split; intros H; lia.
  - destruct (Z.eqb_spec (bz x) 0) as [E|E]; cbv beta iota in *; [lia|].
    destruct (IH i b ltac:(lia) Hn) as [H1 H2]. split; intros H.
    + rewrite (H1 H). reflexivity.
    + specialize (H2 H). lia.
Qed.

Lemma tt_pay_len : forall ck a l, 0 <= a -> 4 <= l -> a + l <= Z.of_nat (length ck) ->
  length (slice ck (a + RTA_HDR) (l - RTA_HDR)) = Z.to_nat (l - 4).
Proof. intros ck a l H1 H2 H3. unfold RTA_HDR. apply tk_slice_length; lia. Qed.

Lemma tt_pay_nth : forall ck a l i, 0 <= a -> 4 <= l -> a + l <= Z.of_nat (length ck) -> 0 <= i < l - 4 ->
  nth_error (slice ck (a + RTA_HDR) (l - RTA_HDR)) (Z.to_nat i) = nth_error ck (Z.to_nat (a + 4 + i)).
Proof. intros ck a l i H1 H2 H3 H4. unfold RTA_HDR. apply tk_nth_slice; lia. Qed.

Lemma tt_cut_len : forall pay cap, 1 <= cap ->
  Z.of_nat (length (cut_text pay cap)) = Z.min (Z.of_nat (nul_at pay)) (cap - 1).
Proof.
  intros pay cap Hc. unfold cut_text. rewrite length_firstn. pose proof (nul_at_le pay). lia.
Qed.

Lemma tt_u_zxb : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. intros b. unfold zxb. apply unsigned_lit. pose proof (tk_byte_range b). lia. Qed.

(* --------------------------------------------------------------------------
   2. memory
   -------------------------------------------------------------------------- *)

Lemma tt_bytes_at_addr : forall m x y (bs : list byte), bytes_at rsegs m x bs -> x = y -> bytes_at rsegs m y bs.
Proof. intros m x y bs H ->. exact H. Qed.

Lemma tt_prefix : forall m A (bs : list byte) n, bytes_at rsegs m A bs -> bytes_at rsegs m A (firstn n bs).
Proof.
  intros m A bs n H. rewrite <- (firstn_skipn n bs) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

(* the memcpy source: the first bytes of the payload, which sits at B + 4 + a *)
Lemma tt_src : forall m B ck a l cap, bytes_at rsegs m B ck -> 0 <= a -> 4 <= l -> a + l <= Z.of_nat (length ck) ->
  bytes_at rsegs m (B + 4 + a) (cut_text (slice ck (a + RTA_HDR) (l - RTA_HDR)) cap).
Proof.
  intros m B ck a l cap HB H1 H2 H3. unfold cut_text. apply tt_prefix.
  replace (B + 4 + a) with (B + (a + RTA_HDR)) by (unfold RTA_HDR; lia).
  apply tk_bytes_slice; [exact HB | unfold RTA_HDR; lia ..].
Qed.

Lemma tt_merge : forall m A A' k l (x y : list byte),
  rw_cells rsegs m A [CB k x] -> rw_cells rsegs m A' [CB l y] -> A' = A + Z.of_nat k ->
  rw_cells rsegs m A [CB (k + l) (x ++ y)].
Proof. intros m A A' k l x y H1 H2 ->. exact (tk_rw_merge m A k l x y H1 H2). Qed.

(* one byte stored over a one-byte cell *)
Lemma tt_store1 : forall m A (x : list byte) (b : byte), rw_cells rsegs m A [CB 1 x] ->
  rw_cells rsegs (write_to_mem m (wa A) [b]) A [CB 1 [b]].
Proof.
  intros m A x b H.
  pose proof (rw_cells_write rsegs m A [CB 1 x] 0 (CB 1 x) (CB 1 [b]) H eq_refl eq_refl eq_refl) as W.
  cbn [cell_upd cbytes Nat.eqb] in W. change (Z.of_nat 0) with 0 in W. rewrite Z.add_0_r in W. exact W.
Qed.

(* across the memcpy of k bytes into BUF: the bytes BUF + k and after are untouched *)
Lemma tt_after_call : forall m m1 BUF CAP k (jk : list byte),
  0 <= k -> k + 1 <= CAP ->
  rw_cells rsegs m BUF [CB (Z.to_nat CAP) jk] ->
  munch [(BUF, BUF + k)] m m1 -> wmono rsegs m m1 ->
  munch [(BUF, BUF + CAP)] m m1 /\
  rw_cells rsegs m1 (BUF + k) [CB 1 (firstn 1 (skipn (Z.to_nat k) jk))] /\
  rw_cells rsegs m1 (BUF + k + 1) [CB (Z.to_nat CAP - Z.to_nat k - 1) (skipn 1 (skipn (Z.to_nat k) jk))].
Proof.
  intros m m1 BUF CAP k jk Hk HkC HJ MU WM.
  destruct (tk_rw_split m BUF (Z.to_nat CAP) (Z.to_nat k) jk ltac:(lia) HJ) as [_ J2].
  destruct (tk_rw_split m (BUF + Z.of_nat (Z.to_nat k)) (Z.to_nat CAP - Z.to_nat k) 1
              (skipn (Z.to_nat k) jk) ltac:(lia) J2) as [J3 J4].
  rewrite Z2Nat.id in J3, J4 by lia.
  replace (BUF + k + Z.of_nat 1) with (BUF + k + 1) in J4 by lia.
  split; [|split].
  - eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in Hx |- *.
    destruct Hx as [Hx _]. split; [lia | exact I].
  - eapply rw_cells_transport; [exact J3 | exact MU | exact WM |].
    cbn [disjoint_from cells_size csize]. split; [lia | exact I].
  - eapply rw_cells_transport; [exact J4 | exact MU | exact WM |].
    cbn [disjoint_from cells_size csize]. split; [lia | exact I].
Qed.

(* the NUL at BUF + k after the k text bytes: the C string, and the whole buffer still rw_cells *)
Lemma tt_after_store : forall m m1 BUF CAP k (src x y : list byte),
  0 <= BUF -> BUF + CAP <= 2 ^ 64 -> 0 <= k -> k + 1 <= CAP ->
  (forall b, In b src -> bz b <> 0) ->
  munch [(BUF, BUF + CAP)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  rw_cells rsegs m1 BUF [CB (Z.to_nat k) src] ->
  rw_cells rsegs m1 (BUF + k) [CB 1 x] ->
  rw_cells rsegs m1 (BUF + k + 1) [CB (Z.to_nat CAP - Z.to_nat k - 1) y] ->
  munch [(BUF, BUF + CAP)] m (write_to_mem m1 (wa (BUF + k)) [zb 0]) /\
  wmono rsegs m (write_to_mem m1 (wa (BUF + k)) [zb 0]) /\
  mem_inv rsegs (write_to_mem m1 (wa (BUF + k)) [zb 0]) /\
  cstr_at (write_to_mem m1 (wa (BUF + k)) [zb 0]) BUF src /\
  (exists j, rw_cells rsegs (write_to_mem m1 (wa (BUF + k)) [zb 0]) BUF [CB (Z.to_nat CAP) j]).
Proof.
  intros m m1 BUF CAP k src x y H0 H1 Hk HkC Hnz MU WM MI R1 R2 R3.
  pose proof (rw_cells_store_ok rsegs m1 (BUF + k) [CB 1 x] 0 (CB 1 x) 1 R2 eq_refl eq_refl) as SOK.
  change (Z.of_nat 0) with 0 in SOK. rewrite Z.add_0_r in SOK.
  pose proof (tt_store1 m1 (BUF + k) x (zb 0) R2) as R2'.
  assert (R1' : rw_cells rsegs (write_to_mem m1 (wa (BUF + k)) [zb 0]) BUF [CB (Z.to_nat k) src]).
  { apply rw_cells_frame; [exact R1 | lia | cbn [length]; lia | cbn [cells_size csize length]; lia]. }
  assert (R3' : rw_cells rsegs (write_to_mem m1 (wa (BUF + k)) [zb 0]) (BUF + k + 1)
                  [CB (Z.to_nat CAP - Z.to_nat k - 1) y]).
  { apply rw_cells_frame; [exact R3 | lia | cbn [length]; lia | cbn [cells_size csize length]; lia]. }
  pose proof (tt_merge _ _ _ _ _ _ _ R1' R2' ltac:(lia)) as M1.
  pose proof (tt_merge _ _ _ _ _ _ _ M1 R3' ltac:(lia)) as M2.
  split; [|split; [|split; [|split]]].
  - apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length]; left; lia].
  - apply wmono_write. exact WM.
  - apply mem_inv_store; [exact MI | exact SOK].
  - split; [exact (tk_rw_bytes _ _ _ _ M1) |].
    intros Hin. apply (Hnz _ Hin). first [reflexivity | unfold bz, zb; rewrite Z_to_bv_unsigned; reflexivity].
  - exists ((src ++ [zb 0]) ++ y).
    replace (Z.to_nat CAP) with (Z.to_nat k + 1 + (Z.to_nat CAP - Z.to_nat k - 1))%nat by lia.
    exact M2.
Qed.

(* ==========================================================================
   3. F_take_al: s4 = l, s11 = a, s0 = AD, cap AN - 1 at 0(sp)
   ========================================================================== *)
Section Alias.
  Variables (Q : machine_state -> Prop) (gp tp s1 s3 s6 s7 s8 s9 s10 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
            (B : Z) (ck : list byte) (a l SP KD KN AD AN : Z) (jk : list byte).
  Hypothesis MC : memcpy_contract.
  Hypothesis HSP : 144 <= SP <= 2 ^ 63.
  Hypothesis HFR : rw_cells rsegs m (SP + -144) (spill_cells AN B KN AD KD).
  Hypothesis HB : bytes_at rsegs m B ck.
  Hypothesis HLk : Z.of_nat (length ck) <= 4096.
  Hypothesis HB0 : 0 <= B.
  Hypothesis HB1 : B + 4096 <= 2 ^ 63.
  Hypothesis Ha : 0 <= a.
  Hypothesis Hl : 4 <= l.
  Hypothesis Hal : a + l <= Z.of_nat (length ck).
  Hypothesis HAD : 1 <= AD.
  Hypothesis HAN : 1 <= AN.
  Hypothesis HADN : AD + AN <= 2 ^ 64.
  Hypothesis HJ : rw_cells rsegs m AD [CB (Z.to_nat AN) jk].
  Hypothesis HSEP : tt_hold (B + 4 + a + (l - 4) <= AD \/ AD + AN <= B + 4 + a).
  Hypothesis MI : mem_inv rsegs m.

  Notation pay := (slice ck (a + RTA_HDR) (l - RTA_HDR)).
  Notation ST pc mm ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 :=
    (MS (mkR ra (Z_to_bv 64 (SP + -144)) gp tp t0 t1 t2 (Z_to_bv 64 AD) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 l) (Z_to_bv 64 (B + 4)) s6 s7 s8 s9 s10 (Z_to_bv 64 a) t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

  Hypothesis HK : forall m',
    munch [(AD, AD + AN)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    cstr_at m' AD (cut_text pay AN) ->
    (exists j, rw_cells rsegs m' AD [CB (Z.to_nat AN) j]) ->
    forall ra' t0' t1' t2' a0' a1' a2' a3' a7' s2' t3' t4' t5' t6',
    evt rsegs Q (ST 0x15a54 m' ra' t0' t1' t2' a0' a1' a2' a3' (Z_to_bv 64 4) (Z_to_bv 64 1) (Z_to_bv 64 3)
                    a7' s2' t3' t4' t5' t6').

  (* 0x15984: s2 = s0 + s2; sb zero, 0(s2); a4 = 4, a5 = 1, a6 = 3; j 0x15a54 *)
  Lemma al_tail : forall m1 k ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs2 t3 t4 t5 t6 (x y : list byte),
    xs2 = Z_to_bv 64 k -> 0 <= k -> k + 1 <= AN ->
    munch [(AD, AD + AN)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
    rw_cells rsegs m1 AD [CB (Z.to_nat k) (cut_text pay AN)] ->
    rw_cells rsegs m1 (AD + k) [CB 1 x] ->
    rw_cells rsegs m1 (AD + k + 1) [CB (Z.to_nat AN - Z.to_nat k - 1) y] ->
    evt rsegs Q (ST 0x15984 m1 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs2 t3 t4 t5 t6).
  Proof.
    intros m1 k ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs2 t3 t4 t5 t6 x y -> Hk HkA MU WM MI1 R1 R2 R3.
    destruct (tt_after_store m m1 AD AN k (cut_text pay AN) x y ltac:(lia) HADN Hk HkA
                (cut_text_nonul pay AN) MU WM MI1 R1 R2 R3) as (MU2 & WM2 & MI2 & CS2 & RW2).
    pose proof (rw_cells_store_ok rsegs m1 (AD + k) [CB 1 x] 0 (CB 1 x) 1 R2 eq_refl eq_refl) as SOK.
    change (Z.of_nat 0) with 0 in SOK. rewrite Z.add_0_r in SOK.
    clear R1 R2 R3 MU WM.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?ad ?bs) _) =>
      replace (write_to_mem m1 ad bs) with (write_to_mem m1 (wa (AD + k)) [zb 0])
        by (f_equal; try reflexivity; unfold wa; word_eq_tac) end.
    zstep. zstep. zstep. zstep.
    eapply HK; [exact MU2 | exact WM2 | exact MI2 | exact CS2 | exact RW2].
  Qed.

  (* 0x15970: a1 = ld 0x10(sp) + s11; a0 = s0; a2 = s2; jal memcpy *)
  Lemma al_call : forall k ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs2 t3 t4 t5 t6,
    xs2 = Z_to_bv 64 k -> k = Z.min (Z.of_nat (nul_at pay)) (AN - 1) ->
    evt rsegs Q (ST 0x15970 m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs2 t3 t4 t5 t6).
  Proof.
    intros k ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs2 t3 t4 t5 t6 -> Hk.
    pose proof HFR as FR. unfold spill_cells in FR.
    pose proof (tt_pay_len ck a l Ha Hl Hal) as PL. pose proof (nul_at_le pay) as NL.
    pose proof (tt_cut_len pay AN HAN) as CL.
    assert (K0 : 0 <= k <= l - 4) by lia. assert (K1 : k + 1 <= AN) by lia.
    pose proof (tt_src m B ck a l AN HB Ha Hl Hal) as SRC.
    destruct (tk_rw_split m AD (Z.to_nat AN) (Z.to_nat k) jk ltac:(lia) HJ) as [J1 _].
    pose proof MC as MC0. unfold memcpy_contract in MC0.
    zstep. zstep. zstep. zstep. zstep.
    eapply evt_cut.
    { eapply MC0 with (src := cut_text pay AN) (junk := firstn (Z.to_nat k) jk).
      - rewrite ?unsigned_lit by lia. eapply tt_bytes_at_addr; [exact SRC | lia].
      - rewrite ?unsigned_lit by lia. lia.
      - rewrite ?unsigned_lit by lia. exact J1.
      - rewrite ?unsigned_lit by lia. unfold tt_hold in HSEP. lia.
      - exact MI. }
    intros ms' PO. unfold memcpy_post in PO. cbv beta in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1
                    & E & MU & WM & MI1 & RW & _).
    subst ms'.
    rewrite ?unsigned_lit in MU by lia. rewrite ?unsigned_lit in RW by lia.
    destruct (tt_after_call m m1 AD AN k jk ltac:(lia) K1 HJ MU WM) as (MU' & R2 & R3).
    lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.
    eapply al_tail with (k := k);
      [word_eq_tac | lia | lia | exact MU' | exact WM | exact MI1 | exact RW | exact R2 | exact R3].
  Qed.

  (* 0x15964: a0 = ld 0(sp) (AN - 1); bltu s2, a0 -> 0x15970, else s2 = ld 0(sp) *)
  Lemma al_cap : forall k0 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs2 t3 t4 t5 t6,
    xs2 = Z_to_bv 64 k0 -> k0 = Z.of_nat (nul_at pay) ->
    evt rsegs Q (ST 0x15964 m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs2 t3 t4 t5 t6).
  Proof.
    intros k0 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs2 t3 t4 t5 t6 -> Hk0.
    pose proof HFR as FR. unfold spill_cells in FR.
    pose proof (tt_pay_len ck a l Ha Hl Hal) as PL. pose proof (nul_at_le pay) as NL.
    assert (K0 : 0 <= k0 <= l - 4) by lia.
    zstep. zstep. if_cases K; zify_cond K.
    all: first
      [ eapply al_call with (k := k0); [word_eq_tac | lia]
      | zstep; eapply al_call with (k := AN - 1); [word_eq_tac | lia] ].
  Qed.

  (* the strnlen loop head 0x1594c: a2 = a1 + s2; lbu; beqz -> 0x15964; s2++; bne a0, s2 -> loop;
     s2 = a0 *)
  Lemma al_loop : forall (fu : nat) (i : Z) ra t0 t1 t2 xa0 xa1 a2 a3 a4 a5 a6 a7 xs2 t3 t4 t5 t6,
    Z.to_nat (l - 4 - i) = fu ->
    xa0 = Z_to_bv 64 (l - 4) -> xa1 = Z_to_bv 64 (B + 4 + a) -> xs2 = Z_to_bv 64 i ->
    0 <= i < l - 4 -> (Z.to_nat i <= nul_at pay)%nat ->
    evt rsegs Q (ST 0x1594c m ra t0 t1 t2 xa0 xa1 a2 a3 a4 a5 a6 a7 xs2 t3 t4 t5 t6).
  Proof.
    induction fu as [|fu IH];
      intros i ra t0 t1 t2 xa0 xa1 a2 a3 a4 a5 a6 a7 xs2 t3 t4 t5 t6 Hfu -> -> -> Hi Hn; [lia|].
    pose proof (tt_pay_len ck a l Ha Hl Hal) as PL. pose proof (nul_at_le pay) as NL.
    destruct (tk_nth_some pay (Z.to_nat i) ltac:(lia)) as [b Eb].
    pose proof Eb as Eb'. rewrite (tt_pay_nth ck a l i Ha Hl Hal Hi) in Eb'.
    pose proof (tk_read1 m B ck (a + 4 + i) b HB ltac:(lia) Eb') as RD.
    destruct (tt_nul_step pay (Z.to_nat i) b Hn Eb) as [N0 N1].
    unfold bz in N0, N1.
    zstep. zstep. zstep. if_cases K; zify_cond K; rewrite ?tt_u_zxb in K.
    - eapply al_cap with (k0 := i); [word_eq_tac |]. specialize (N0 K). lia.
    - zstep. zstep. if_cases K2; zify_cond K2.
      all: first
        [ eapply (IH (i + 1)); [lia | word_eq_tac | word_eq_tac | word_eq_tac | lia | specialize (N1 K); lia]
        | zstep; eapply al_cap with (k0 := l - 4); [word_eq_tac | specialize (N1 K); lia] ].
  Qed.

  (* 0x1593c: s2 = 0; a0 = s4 - 4; beqz a0 -> 0x15964; a1 = s5 + s11 *)
  Lemma al_entry : forall ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6,
    evt rsegs Q (ST 0x1593c m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6).
  Proof.
    intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6.
    pose proof (tt_pay_len ck a l Ha Hl Hal) as PL. pose proof (nul_at_le pay) as NL.
    zstep. zstep. zstep. if_cases K; zify_cond K.
    all: first
      [ eapply al_cap with (k0 := 0); [word_eq_tac | lia]
      | zstep; eapply (al_loop (Z.to_nat (l - 4 - 0)) 0);
        [reflexivity | word_eq_tac | word_eq_tac | word_eq_tac | lia | lia] ].
  Qed.
End Alias.

Lemma F_take_al_ok : memcpy_contract -> F_take_al_spec.
Proof.
  intros MC. unfold F_take_al_spec.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m B ck a l SP KD KN AD AN jk -> -> -> -> -> HSP HFR HB HLk HB0 HB1 Ha Hl Hal HAD HAN HJ HAP1 HAP2 MI HK.
  pose proof (rw_cells_bound rsegs m AD [CB (Z.to_nat AN) jk] HJ) as HJB. cbn [cells_size csize] in HJB.
  assert (HAD1 : 1 <= AD) by lia.
  assert (HADN : AD + AN <= 2 ^ 64) by lia.
  assert (HLk' : Z.of_nat (length ck) <= 4096) by lia.
  assert (HSEP : tt_hold (B + 4 + a + (l - 4) <= AD \/ AD + AN <= B + 4 + a)).
  { unfold tt_hold, apart in *. lia. }
  clear HAP1 HAP2 HJB.
  eapply al_entry; eassumption.
Qed.

(* ==========================================================================
   4. F_take_kd: s10 = ln (li), s8 = o (i), s1 = KD, cap KN - 1 at 0x18(sp)
   ========================================================================== *)
Section Kind.
  Variables (Q : machine_state -> Prop) (gp tp s0 s3 s4 s6 s7 s9 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
            (B : Z) (ck : list byte) (o ln SP KD KN AD AN : Z) (jk : list byte).
  Hypothesis MC : memcpy_contract.
  Hypothesis HSP : 144 <= SP <= 2 ^ 63.
  Hypothesis HFR : rw_cells rsegs m (SP + -144) (spill_cells AN B KN AD KD).
  Hypothesis HB : bytes_at rsegs m B ck.
  Hypothesis HLk : Z.of_nat (length ck) <= 4096.
  Hypothesis HB0 : 0 <= B.
  Hypothesis HB1 : B + 4096 <= 2 ^ 63.
  Hypothesis Ho : 0 <= o.
  Hypothesis Hln : 4 <= ln.
  Hypothesis Hol : o + ln <= Z.of_nat (length ck).
  Hypothesis HKD : 1 <= KD.
  Hypothesis HKN : 1 <= KN.
  Hypothesis HKDN : KD + KN <= 2 ^ 64.
  Hypothesis HJ : rw_cells rsegs m KD [CB (Z.to_nat KN) jk].
  Hypothesis HSEP : tt_hold (B + 4 + o + (ln - 4) <= KD \/ KD + KN <= B + 4 + o).
  Hypothesis MI : mem_inv rsegs m.

  Notation pay := (slice ck (o + RTA_HDR) (ln - RTA_HDR)).
  Notation ST pc mm ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 :=
    (MS (mkR ra (Z_to_bv 64 (SP + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 KD) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 (Z_to_bv 64 (B + 4)) s6 s7 (Z_to_bv 64 o) s9 (Z_to_bv 64 ln) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

  Hypothesis HK : forall m',
    munch [(KD, KD + KN)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    cstr_at m' KD (cut_text pay KN) ->
    (exists j, rw_cells rsegs m' KD [CB (Z.to_nat KN) j]) ->
    forall ra' t0' t1' t2' a0' a1' a2' a3' a7' s2' t3' t4' t5' t6',
    evt rsegs Q (ST 0x15a40 m' ra' t0' t1' t2' a0' a1' a2' a3' (Z_to_bv 64 4) (Z_to_bv 64 1) (Z_to_bv 64 3)
                    a7' s2' t3' t4' t5' t6').

  (* 0x15a2c: s2 = s1 + s2; sb zero, 0(s2); a4 = 4, a5 = 1, a6 = 3; falls into 0x15a40 *)
  Lemma kd_tail : forall m1 k ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs2 t3 t4 t5 t6 (x y : list byte),
    xs2 = Z_to_bv 64 k -> 0 <= k -> k + 1 <= KN ->
    munch [(KD, KD + KN)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
    rw_cells rsegs m1 KD [CB (Z.to_nat k) (cut_text pay KN)] ->
    rw_cells rsegs m1 (KD + k) [CB 1 x] ->
    rw_cells rsegs m1 (KD + k + 1) [CB (Z.to_nat KN - Z.to_nat k - 1) y] ->
    evt rsegs Q (ST 0x15a2c m1 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs2 t3 t4 t5 t6).
  Proof.
    intros m1 k ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs2 t3 t4 t5 t6 x y -> Hk HkA MU WM MI1 R1 R2 R3.
    destruct (tt_after_store m m1 KD KN k (cut_text pay KN) x y ltac:(lia) HKDN Hk HkA
                (cut_text_nonul pay KN) MU WM MI1 R1 R2 R3) as (MU2 & WM2 & MI2 & CS2 & RW2).
    pose proof (rw_cells_store_ok rsegs m1 (KD + k) [CB 1 x] 0 (CB 1 x) 1 R2 eq_refl eq_refl) as SOK.
    change (Z.of_nat 0) with 0 in SOK. rewrite Z.add_0_r in SOK.
    clear R1 R2 R3 MU WM.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?ad ?bs) _) =>
      replace (write_to_mem m1 ad bs) with (write_to_mem m1 (wa (KD + k)) [zb 0])
        by (f_equal; try reflexivity; unfold wa; word_eq_tac) end.
    zstep. zstep. zstep.
    eapply HK; [exact MU2 | exact WM2 | exact MI2 | exact CS2 | exact RW2].
  Qed.

  (* 0x15a18: a1 = ld 0x10(sp) + s8; a0 = s1; a2 = s2; jal memcpy *)
  Lemma kd_call : forall k ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs2 t3 t4 t5 t6,
    xs2 = Z_to_bv 64 k -> k = Z.min (Z.of_nat (nul_at pay)) (KN - 1) ->
    evt rsegs Q (ST 0x15a18 m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs2 t3 t4 t5 t6).
  Proof.
    intros k ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs2 t3 t4 t5 t6 -> Hk.
    pose proof HFR as FR. unfold spill_cells in FR.
    pose proof (tt_pay_len ck o ln Ho Hln Hol) as PL. pose proof (nul_at_le pay) as NL.
    pose proof (tt_cut_len pay KN HKN) as CL.
    assert (K0 : 0 <= k <= ln - 4) by lia. assert (K1 : k + 1 <= KN) by lia.
    pose proof (tt_src m B ck o ln KN HB Ho Hln Hol) as SRC.
    destruct (tk_rw_split m KD (Z.to_nat KN) (Z.to_nat k) jk ltac:(lia) HJ) as [J1 _].
    pose proof MC as MC0. unfold memcpy_contract in MC0.
    zstep. zstep. zstep. zstep. zstep.
    eapply evt_cut.
    { eapply MC0 with (src := cut_text pay KN) (junk := firstn (Z.to_nat k) jk).
      - rewrite ?unsigned_lit by lia. eapply tt_bytes_at_addr; [exact SRC | lia].
      - rewrite ?unsigned_lit by lia. lia.
      - rewrite ?unsigned_lit by lia. exact J1.
      - rewrite ?unsigned_lit by lia. unfold tt_hold in HSEP. lia.
      - exact MI. }
    intros ms' PO. unfold memcpy_post in PO. cbv beta in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1
                    & E & MU & WM & MI1 & RW & _).
    subst ms'.
    rewrite ?unsigned_lit in MU by lia. rewrite ?unsigned_lit in RW by lia.
    destruct (tt_after_call m m1 KD KN k jk ltac:(lia) K1 HJ MU WM) as (MU' & R2 & R3).
    lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.
    eapply kd_tail with (k := k);
      [word_eq_tac | lia | lia | exact MU' | exact WM | exact MI1 | exact RW | exact R2 | exact R3].
  Qed.

  (* 0x15a0c: a0 = ld 0x18(sp) (KN - 1); bltu s2, a0 -> 0x15a18, else s2 = ld 0x18(sp) *)
  Lemma kd_cap : forall k0 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs2 t3 t4 t5 t6,
    xs2 = Z_to_bv 64 k0 -> k0 = Z.of_nat (nul_at pay) ->
    evt rsegs Q (ST 0x15a0c m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs2 t3 t4 t5 t6).
  Proof.
    intros k0 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs2 t3 t4 t5 t6 -> Hk0.
    pose proof HFR as FR. unfold spill_cells in FR.
    pose proof (tt_pay_len ck o ln Ho Hln Hol) as PL. pose proof (nul_at_le pay) as NL.
    assert (K0 : 0 <= k0 <= ln - 4) by lia.
    zstep. zstep. if_cases K; zify_cond K.
    all: first
      [ eapply kd_call with (k := k0); [word_eq_tac | lia]
      | zstep; eapply kd_call with (k := KN - 1); [word_eq_tac | lia] ].
  Qed.

  (* the strnlen loop head 0x159f4 *)
  Lemma kd_loop : forall (fu : nat) (i : Z) ra t0 t1 t2 xa0 xa1 a2 a3 a4 a5 a6 a7 xs2 t3 t4 t5 t6,
    Z.to_nat (ln - 4 - i) = fu ->
    xa0 = Z_to_bv 64 (ln - 4) -> xa1 = Z_to_bv 64 (B + 4 + o) -> xs2 = Z_to_bv 64 i ->
    0 <= i < ln - 4 -> (Z.to_nat i <= nul_at pay)%nat ->
    evt rsegs Q (ST 0x159f4 m ra t0 t1 t2 xa0 xa1 a2 a3 a4 a5 a6 a7 xs2 t3 t4 t5 t6).
  Proof.
    induction fu as [|fu IH];
      intros i ra t0 t1 t2 xa0 xa1 a2 a3 a4 a5 a6 a7 xs2 t3 t4 t5 t6 Hfu -> -> -> Hi Hn; [lia|].
    pose proof (tt_pay_len ck o ln Ho Hln Hol) as PL. pose proof (nul_at_le pay) as NL.
    destruct (tk_nth_some pay (Z.to_nat i) ltac:(lia)) as [b Eb].
    pose proof Eb as Eb'. rewrite (tt_pay_nth ck o ln i Ho Hln Hol Hi) in Eb'.
    pose proof (tk_read1 m B ck (o + 4 + i) b HB ltac:(lia) Eb') as RD.
    destruct (tt_nul_step pay (Z.to_nat i) b Hn Eb) as [N0 N1].
    unfold bz in N0, N1.
    zstep. zstep. zstep. if_cases K; zify_cond K; rewrite ?tt_u_zxb in K.
    - eapply kd_cap with (k0 := i); [word_eq_tac |]. specialize (N0 K). lia.
    - zstep. zstep. if_cases K2; zify_cond K2.
      all: first
        [ eapply (IH (i + 1)); [lia | word_eq_tac | word_eq_tac | word_eq_tac | lia | specialize (N1 K); lia]
        | zstep; eapply kd_cap with (k0 := ln - 4); [word_eq_tac | specialize (N1 K); lia] ].
  Qed.

  (* 0x159e4: s2 = 0; a0 = s10 - 4; beqz a0 -> 0x15a0c; a1 = s5 + s8 *)
  Lemma kd_entry : forall ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6,
    evt rsegs Q (ST 0x159e4 m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6).
  Proof.
    intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6.
    pose proof (tt_pay_len ck o ln Ho Hln Hol) as PL. pose proof (nul_at_le pay) as NL.
    zstep. zstep. zstep. if_cases K; zify_cond K.
    all: first
      [ eapply kd_cap with (k0 := 0); [word_eq_tac | lia]
      | zstep; eapply (kd_loop (Z.to_nat (ln - 4 - 0)) 0);
        [reflexivity | word_eq_tac | word_eq_tac | word_eq_tac | lia | lia] ].
  Qed.
End Kind.

Lemma F_take_kd_ok : memcpy_contract -> F_take_kd_spec.
Proof.
  intros MC. unfold F_take_kd_spec.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m B ck i li SP KD KN AD AN jk -> -> -> -> -> HSP HFR HB HLk HB0 HB1 Hi Hli Hil HKD HKN HJ HAP1 HAP2 MI HK.
  pose proof (rw_cells_bound rsegs m KD [CB (Z.to_nat KN) jk] HJ) as HJB. cbn [cells_size csize] in HJB.
  assert (HKD1 : 1 <= KD) by lia.
  assert (HKDN : KD + KN <= 2 ^ 64) by lia.
  assert (HLk' : Z.of_nat (length ck) <= 4096) by lia.
  assert (HSEP : tt_hold (B + 4 + i + (li - 4) <= KD \/ KD + KN <= B + 4 + i)).
  { unfold tt_hold, apart in *. lia. }
  clear HAP1 HAP2 HJB.
  eapply kd_entry; eassumption.
Qed.

Print Assumptions F_take_al_ok.
Print Assumptions F_take_kd_ok.
