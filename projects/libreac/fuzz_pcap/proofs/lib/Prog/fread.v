(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 314 of its 342 lines of code are new or changed and 294 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel memcpy_c __toread_c mread_c fread_c fread_lemmas.
Import ListNotations.
Open Scope Z_scope.

Ltac post_call_r segs m :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let A0 := fresh "A0E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in
  let MIc := fresh "MIc" in
  destruct PO as [E [A0 [MUc [WMc [MIc PO]]]]];
  subst ms';
  lazymatch type of MUc with
  | munch _ m ?m' =>
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Ltac disc := first [ assumption | reflexivity | lia
  | (rewrite ?Z.add_0_r, ?Z.sub_0_r; first [ assumption | symmetry; apply Z_to_bv_lit_self ])
  | (cbn [Z.to_nat firstn]; apply bytes_at_nil; lia)
  | (rewrite unsigned_lit by lia; lia)
  | (f_equal; lia) ].

Definition sf (sp d k h : word) (b : Z) (Fc : list byte) (lo p : Z) : Prop :=
  1 <= bv_unsigned k /\
  (bv_unsigned d + bv_unsigned k <= bv_unsigned h \/ bv_unsigned h + 1304 <= bv_unsigned d) /\
  (bv_unsigned d + bv_unsigned k <= b \/ b + Z.of_nat (length Fc) <= bv_unsigned d) /\
  (bv_unsigned d + bv_unsigned k <= lo \/ bv_unsigned sp <= bv_unsigned d) /\
  0 <= lo /\ lo + 112 <= bv_unsigned sp /\ bv_unsigned sp <= 2^64 /\
  bv_unsigned h + 1304 <= lo /\ b + Z.of_nat (length Fc) <= lo /\
  bv_unsigned d + bv_unsigned k <= 2^64 /\ 0 <= p.

Section Fread.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
          (d k h : word) (b : Z) (Fc : list byte) (p : Z) (pv nx : word) (lo : Z) (m0 : word -> option byte).
Hypothesis HMC : memcpy_contract.
Hypothesis HTR : __toread_contract.
Hypothesis HMR : mread_contract.

Local Notation ZS := (bv_unsigned sp).
Local Notation ZD := (bv_unsigned d).
Local Notation ZK := (bv_unsigned k).
Local Notation ZH := (bv_unsigned h).
Local Notation ZN := (Z.of_nat (length Fc)).
Local Notation FPOST := (fread_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d k h b Fc p pv nx lo m0).
Local Notation SFF := (sf sp d k h b Fc lo p).
Local Notation FRM m := (rw_cells rsegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
Local Notation MUN m := (munch [(bv_unsigned sp - 112, bv_unsigned sp);
  (bv_unsigned d, bv_unsigned d + fread_j (bv_unsigned k) (Z.of_nat (length Fc)) p);
  (bv_unsigned h, bv_unsigned h + 1304)] m0 m).
Local Notation STT pc m x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 :=
  (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
      x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Ltac open_sf SF0 :=
  let SF1 := fresh "SF1" in pose proof SF0 as SF1;
  destruct SF1 as (HK & DH & DB & DS & L0 & LO & SPB & HL & BL & DE & P0);
  pose proof (zr_word sp) as Rsp; unfold inr64 in Rsp;
  pose proof (zr_word d) as Rd; unfold inr64 in Rd;
  pose proof (zr_word k) as Rk; unfold inr64 in Rk;
  pose proof (zr_word h) as Rh; unfold inr64 in Rh.

Lemma fr_exit : forall m x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
  SFF -> FRM m -> stk rsegs m lo (ZS + -64) -> MUN m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  x10 = Z_to_bv 64 (fread_j ZK ZN p) ->
  bytes_at rsegs m ZD (firstn (Z.to_nat (fread_j ZK ZN p)) (skipn (Z.to_nat p) Fc)) ->
  mstl m ZH b Fc (p + fread_j ZK ZN p) pv nx ->
  evt rsegs FPOST (STT (symaddr (Symbols.Plain.s_fread_unlocked + 0x108)%Z) m x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31).
Proof.
  intros m x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31
    SF0 FR ST MU WM MI -> OUT MS'.
  open_sf SF0.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  apply evt_done. unfold fread_post, FREAD_K.
  do 16 eexists. split; [reflexivity|].
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))); first [ reflexivity | eassumption ].
Qed.

Lemma fr_ret_k : forall m x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
  SFF -> FRM m -> stk rsegs m lo (ZS + -64) -> MUN m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  fread_j ZK ZN p = ZK ->
  bytes_at rsegs m ZD (firstn (Z.to_nat ZK) (skipn (Z.to_nat p) Fc)) ->
  mstl m ZH b Fc (p + ZK) pv nx ->
  x9 = Z_to_bv 64 1 -> x18 = k -> x21 = Z_to_bv 64 1 ->
  evt rsegs FPOST (STT (symaddr (Symbols.Plain.s_fread_unlocked + 0xd0)%Z) m x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31).
Proof.
  intros m x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31
    SF0 FR ST MU WM MI JK OUT MS' -> -> ->.
  open_sf SF0.
  zstep. zstep. zstep. zstep. if_true.
  rewrite land_ones_k by lia.
  eapply fr_exit; [ exact SF0 | exact FR | exact ST | exact MU | exact WM | exact MI
                  | rewrite JK; reflexivity | rewrite JK; exact OUT | rewrite JK; exact MS' ].
Qed.

Lemma fr_ret_c : forall m (c : Z) x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
  SFF -> FRM m -> stk rsegs m lo (ZS + -64) -> MUN m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  0 <= c <= ZK -> fread_j ZK ZN p = c ->
  bytes_at rsegs m ZD (firstn (Z.to_nat c) (skipn (Z.to_nat p) Fc)) ->
  mstl m ZH b Fc (p + c) pv nx ->
  x9 = Z_to_bv 64 1 -> x20 = Z_to_bv 64 (ZK - c) -> x21 = Z_to_bv 64 1 -> x22 = k ->
  evt rsegs FPOST (STT (symaddr (Symbols.Plain.s_fread_unlocked + 0xf4)%Z) m x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31).
Proof.
  intros m c x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31
    SF0 FR ST MU WM MI C0 JC OUT MS' -> -> -> ->.
  open_sf SF0.
  zstep. if_true. zstep. zstep.
  rewrite divu_one.
  eapply fr_exit; [ exact SF0 | exact FR | exact ST | exact MU | exact WM | exact MI
                  | rewrite JC; f_equal; lia | rewrite JC; exact OUT | rewrite JC; exact MS' ].
Qed.

Lemma fr_eof : forall m (c q : Z) (rb : option (Z * Z))
    x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31,
  SFF -> FRM m -> stk rsegs m lo (ZS + -64) -> MUN m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  mfile m ZH b Fc (wz 24) (wz 4294967295) q rb pv nx -> rlen rb = 0 ->
  0 <= c <= ZK -> q = p + c -> q = ZN ->
  bytes_at rsegs m ZD (firstn (Z.to_nat c) (skipn (Z.to_nat p) Fc)) ->
  x9 = Z_to_bv 64 1 -> x20 = Z_to_bv 64 (ZK - c) -> x21 = Z_to_bv 64 1 -> x22 = k ->
  evt rsegs FPOST (STT (symaddr (Symbols.Plain.s_fread_unlocked + 0xa0)%Z) m x1 x5 x6 x7 h x9 x10 x11 x12 x13 x14 x15 x16 x17 k x19 x20 x21 x22 x28 x29 x30 x31).
Proof.
  intros m c q rb x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31
    SF0 FR ST MU WM MI MF R0 C0 QC QN OUT -> -> -> ->.
  open_sf SF0. unfold fread_j in MU.
  assert (U : bv_unsigned (Z_to_bv 64 (ZS + -64)) = ZS + -64) by (apply unsigned_lit; lia).
  assert (LOUT : Z.of_nat (length (firstn (Z.to_nat c) (skipn (Z.to_nat p) Fc))) = c) by (apply len_take; lia).
  zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply HTR with (lo := lo) (b := b) (Fc := Fc) (fl := wz 24) (md := wz 4294967295) (q := q) (rb := rb)
        (pv := pv) (nx := nx);
      [ exact MF | exact R0 | right; reflexivity | right; reflexivity | exact MI | rewrite U; exact ST
      | rewrite U; unfold TOREAD_K; lia | lia | lia ]
    | clear MF; unfold __toread_post, TOREAD_K; post_call_r rsegs mm ] end.
  match goal with A : ?v = (if bv_eqb (wz 24) (wz 24) then _ else _) |- _ =>
    change (bv_eqb (wz 24) (wz 24)) with true in A; cbv iota in A; subst v end.
  match goal with Hs : stk _ _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite U in Hs end.
  unfold wz.
  zstep. if_true.
  eapply fr_ret_c with (c := c); try eassumption; try reflexivity.
  - unfold fread_j; lia.
  - eapply mstl_of; [ eassumption | right; reflexivity | right; reflexivity | cbn [rlen]; lia | intros _; lia ].
Qed.

Lemma fr_loop : forall m (c q : Z) (rb : option (Z * Z)) (junk : list byte)
    x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31,
  SFF -> FRM m -> stk rsegs m lo (ZS + -64) -> MUN m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  mfile m ZH b Fc (wz 8) (wz 4294967295) q rb pv nx -> rlen rb = 0 ->
  0 <= c < ZK -> q = p + c ->
  bytes_at rsegs m ZD (firstn (Z.to_nat c) (skipn (Z.to_nat p) Fc)) ->
  rw_cells rsegs m (ZD + c) [CB (Z.to_nat (ZK - c)) junk] ->
  x9 = Z_to_bv 64 1 -> x19 = Z_to_bv 64 (ZD + c) -> x20 = Z_to_bv 64 (ZK - c) -> x21 = Z_to_bv 64 1 -> x22 = k ->
  evt rsegs FPOST (STT (symaddr (Symbols.Plain.s_fread_unlocked + 0xa0)%Z) m x1 x5 x6 x7 h x9 x10 x11 x12 x13 x14 x15 x16 x17 k x19 x20 x21 x22 x28 x29 x30 x31).
Proof.
  intros m c q rb junk x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31
    SF0 FR ST MU WM MI MF R0 C0 -> OUT DST2 -> -> -> -> ->.
  open_sf SF0. unfold fread_j in MU.
  assert (Q0 : 0 <= p + c <= ZN) by (clear - MF; destruct MF as (? & _ & ? & _); lia).
  assert (U : bv_unsigned (Z_to_bv 64 (ZS + -64)) = ZS + -64) by (apply unsigned_lit; lia).
  assert (U19 : bv_unsigned (Z_to_bv 64 (ZD + c)) = ZD + c) by (apply unsigned_lit; lia).
  assert (U20 : bv_unsigned (Z_to_bv 64 (ZK - c)) = ZK - c) by (apply unsigned_lit; lia).
  assert (LOUT : Z.of_nat (length (firstn (Z.to_nat c) (skipn (Z.to_nat p) Fc))) = c) by (apply len_take; lia).
  zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply HTR with (lo := lo) (b := b) (Fc := Fc) (fl := wz 8) (md := wz 4294967295) (q := p + c) (rb := rb)
        (pv := pv) (nx := nx);
      [ exact MF | exact R0 | left; reflexivity | right; reflexivity | exact MI | rewrite U; exact ST
      | rewrite U; unfold TOREAD_K; lia | lia | lia ]
    | clear MF; unfold __toread_post, TOREAD_K; post_call_r rsegs mm ] end.
  match goal with A : ?v = (if bv_eqb (wz 8) (wz 24) then _ else _) |- _ =>
    change (bv_eqb (wz 8) (wz 24)) with false in A; cbv iota in A; subst v end.
  match goal with Hs : stk _ _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite U in Hs end.
  match goal with Hm : mfile _ _ _ _ _ _ _ _ _ _ |- _ => rename Hm into MF end.
  unfold wz.
  zstep. if_false.
  pose proof MF as MF2. destruct MF2 as (buf2 & (pad0 & pad1 & pad2 & ung & CELLS & _) & _).
  unfold mfile_cells, wz, A_MCLOSE, A_MREAD, A_MWRITE, A_MSEEK in CELLS.
  zstep. clear CELLS.
  zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply HMR with (lo := lo) (b := b) (Fc := Fc) (md := wz 4294967295) (q := p + c) (rb := Some (1024, 1024))
        (pv := pv) (nx := nx) (junk := junk);
      [ exact MF | reflexivity | rewrite U19, U20; exact DST2 | rewrite U20; lia | rewrite U19, U20; lia
      | rewrite U19, U20; lia | rewrite U19, U20, U; lia | eassumption | rewrite U; eassumption
      | rewrite U; unfold MREAD_K; lia | lia | lia ]
    | clear MF; unfold mread_post, MREAD_K, mread_rem2, mread_t; post_call_r rsegs mm ] end.
  rewrite ?U19, ?U20 in *.
  set (t := Z.min (ZK - c) (ZN - (p + c))) in *.
  assert (Et : t = Z.min (ZK - c) (ZN - (p + c))) by reflexivity. clearbody t.
  match goal with A : ?v = wz t |- _ => subst v end.
  match goal with Hs : stk _ _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite U in Hs end.
  match goal with Hm : mfile _ _ _ _ _ _ _ _ _ _ |- _ => rename Hm into MF end.
  match goal with Hb : bytes_at _ _ (ZD + c) _ |- _ => rename Hb into OUT2 end.
  assert (UT : bv_unsigned (Z_to_bv 64 t) = t) by (apply unsigned_lit; lia).
  unfold wz.
  zstep.
  destruct (Z.eq_dec t 0) as [T0 | T0].
  - if_true.
    replace (ZK - c >? ZN - (p + c)) with true in MF by (symmetry; apply Z.gtb_lt; lia).
    cbv iota in MF.
    eapply fr_ret_c with (c := c); try eassumption; try reflexivity.
    all: first [ (unfold fread_j; lia) | lia
               | eapply mstl_of; [ exact MF | right; reflexivity | right; reflexivity | cbn [rlen]; lia | intros _; lia ] ].
  - if_false.
    zstep. zstep.
    assert (U4 : bv_unsigned (Z_to_bv 64 (ZK - c - t)) = ZK - c - t) by (apply unsigned_lit; lia).
    zstep.
    destruct (Z.eq_dec (ZK - c - t) 0) as [T1 | T1].
    + if_false.
      replace (ZK - c >? ZN - (p + c)) with false in MF by (rewrite Z.gtb_ltb; symmetry; apply Z.ltb_ge; lia).
      cbv iota in MF.
      eapply fr_ret_k; try eassumption; try reflexivity.
      all: first [ (unfold fread_j; lia) | lia
                 | (replace ZK with (c + t) by lia; apply bytes_at_join; try lia; eassumption)
                 | eapply mstl_of; [ exact MF | left; reflexivity | right; reflexivity | cbn [rlen]; lia
                                   | intros W; exfalso; exact (wz_8_24 W) ] ].
    + if_true.
      replace (ZK - c >? ZN - (p + c)) with true in MF by (symmetry; apply Z.gtb_lt; lia).
      cbv iota in MF.
      eapply fr_eof with (c := c + t); try eassumption; try reflexivity.
      all: first [ (cbn [rlen]; lia) | lia | (apply bytes_at_join; try lia; eassumption) | (f_equal; lia) ].
Qed.

Lemma fr_copy : forall m (i e q c : Z) (junk : list byte)
    x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31,
  SFF -> FRM m -> stk rsegs m lo (ZS + -64) -> MUN m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  mfile m ZH b Fc (wz 8) (wz 4294967295) q (Some (i, e)) pv nx ->
  i < e -> p = q - (e - i) -> c = Z.min (e - i) ZK ->
  rw_cells rsegs m ZD [CB (Z.to_nat ZK) junk] ->
  x9 = Z_to_bv 64 1 -> bv_unsigned x11 = ZH + 280 + i -> x19 = d -> bv_unsigned x20 = c ->
  x21 = Z_to_bv 64 1 -> x22 = k ->
  evt rsegs FPOST (STT (symaddr (Symbols.Plain.s_fread_unlocked + 0x7c)%Z) m x1 x5 x6 x7 h x9 x10 x11 x12 x13 x14 x15 x16 x17 k x19 x20 x21 x22 x28 x29 x30 x31).
Proof.
  intros m i e q c junk x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31
    SF0 FR ST MU WM MI MF IE PE CE DST -> U11 -> U20 -> ->.
  open_sf SF0. unfold fread_j in MU.
  destruct MF as (buf & (pad0 & pad1 & pad2 & ung & CELLS & LU & LB & H0 & H16) & Q0 & (I0 & E1 & EQ & BUFEQ)
    & BF & B0 & HB).
  pose proof CELLS as BUF. apply mfile_buf in BUF.
  pose proof (bytes_at_sub _ _ _ (Z.to_nat i) (Z.to_nat c) BUF ltac:(rewrite LB; lia)) as SRC. clear BUF.
  rewrite Z2Nat.id in SRC by lia.
  assert (LSRC : length (firstn (Z.to_nat c) (skipn (Z.to_nat i) buf)) = Z.to_nat c)
    by (rewrite firstn_length_le; [lia | rewrite length_skipn; lia]).
  assert (LOUT : Z.of_nat (length (firstn (Z.to_nat c) (skipn (Z.to_nat p) Fc))) = c) by (apply len_take; lia).
  cbn [rpos_of rend_of] in CELLS.
  unfold mfile_cells, wz, A_MCLOSE, A_MREAD, A_MWRITE, A_MSEEK in CELLS.
  replace (Z.to_nat ZK) with (Z.to_nat c + Z.to_nat (ZK - c))%nat in DST by lia.
  destruct (rw_cells_cb_split2 _ _ _ _ _ DST) as [DST1 DST2]. clear DST.
  rewrite Z2Nat.id in DST2 by lia.
  zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply HMC with (src := firstn (Z.to_nat c) (skipn (Z.to_nat i) buf)) (junk := firstn (Z.to_nat c) junk);
      [ rewrite U11; exact SRC | rewrite U20; exact LSRC | rewrite U20; exact DST1 | rewrite U11, U20; lia
      | exact MI ]
    | post_call rsegs mm ] end.
  match goal with Hd : rw_cells _ _ (bv_unsigned d) [CB _ _] |- _ => apply rw_cells_CB_bytes in Hd; rename Hd into OUT end.
  rewrite (buf_take buf Fc i e q c ltac:(lia) BUFEQ) in OUT. rewrite <- PE in OUT.
  zstep. zstep. zstep. zstep. zstep.
  assert (U4 : bv_unsigned (Z_to_bv 64 (ZK - bv_unsigned x20)) = ZK - c) by (rewrite U20; apply unsigned_lit; lia).
  zstep.
  replace (Z_to_bv 64 (ZH + 280 + i + bv_unsigned x20)) with (Z_to_bv 64 (ZH + 280 + (i + c))) in CELLS
    by (f_equal; lia).
  lazymatch type of CELLS with rw_cells _ ?mm _ _ =>
    assert (MF : mfile mm ZH b Fc (wz 8) (wz 4294967295) q (Some (i + c, e)) pv nx) end.
  { apply (mfile_pack _ _ _ _ _ pad0 pad1 pad2 ung buf);
      [ exact CELLS | assumption | assumption | assumption | assumption | assumption | | assumption | assumption
      | assumption ].
    cbv beta iota. refine (conj _ (conj _ (conj _ _))); [lia | lia | lia | apply buf_drop; [lia | lia | lia | exact BUFEQ]]. }
  destruct (Z.eq_dec c ZK) as [CK | CK].
  - if_true.
    eapply fr_ret_k; try eassumption; try reflexivity.
    all: first [ (unfold fread_j; lia) | lia | (rewrite <- CK; exact OUT)
               | eapply mstl_of; [ exact MF | left; reflexivity | right; reflexivity | cbn [rlen]; lia
                                 | intros W; exfalso; exact (wz_8_24 W) ] ].
  - if_false.
    eapply fr_loop with (c := c) (q := q) (rb := Some (i + c, e)) (junk := skipn (Z.to_nat c) junk);
      try eassumption; try reflexivity.
    all: first [ (cbn [rlen]; lia) | lia | (f_equal; lia) ].
Qed.

End Fread.

Theorem fread_holds : memcpy_contract -> __toread_contract -> mread_contract -> fread_contract.
Proof.
  intros HMC HTR HMR. unfold fread_contract, FREAD.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo b Fc p pv nx junk MS0 A1 K1 DST DH DB DS MI ST LO HL BL.
  subst a1. unfold wz. unfold FREAD_K in LO.
  destruct MS0 as (fl & md & q & rb & MF & FL & MD & PQ & P24).
  destruct MF as (buf & (pad0 & pad1 & pad2 & ung & CELLS & LU & LB & H0 & H16) & Q0 & RBF & BF & B0 & HB).
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
  pose proof (zr_word a2) as Ra2. unfold inr64 in Ra2.
  pose proof (zr_word a3) as Ra3. unfold inr64 in Ra3.
  pose proof (rw_cells_bound _ _ _ _ DST) as DSTB. cbn [cells_size csize] in DSTB.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  assert (SPB : bv_unsigned sp <= 2^64) by (destruct ST as [_ [? _]]; lia).
  assert (RB : 0 <= rlen rb <= q)
    by (destruct rb as [[i e]|]; cbn [rlen]; [destruct RBF as (? & ? & ? & _); lia | lia]).
  assert (P0 : 0 <= p) by lia.
  assert (SF : sf sp a0 a2 a3 b Fc lo p) by (unfold sf; lia).
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp);
    (bv_unsigned a0, bv_unsigned a0 + fread_j (bv_unsigned a2) (Z.of_nat (length Fc)) p);
    (bv_unsigned a3, bv_unsigned a3 + 1304)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold mfile_cells, wz, A_MCLOSE, A_MREAD, A_MWRITE, A_MSEEK in CELLS.
  carve_frame 64%nat ST.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  zstep. zstep. zstep. zstep. zstep.
  zstep. if_true.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  eapply mfile_cells_md in CELLS; [ | clear - MD; apply le4_eq; destruct MD as [-> | ->]; vm_compute; reflexivity ].
  pose proof (mfile_pack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CELLS LU LB H0 H16 Q0 RBF BF B0 HB) as MF.
  clear CELLS.
  zstep.
  replace (Z_to_bv 64 (bv_unsigned a2 * 1)) with a2 by (rewrite Z.mul_1_r; symmetry; apply Z_to_bv_lit_self).
  zstep.
  if_cases E.
  - assert (R0 : rlen rb = 0) by (apply (rlen_zero (bv_unsigned a3) q Fc buf rb); [lia | lia | exact RBF | exact E]).
    zstep. zstep. if_true.
    destruct FL as [-> | ->].
    + eapply fr_loop with (c := 0) (q := q) (rb := rb) (junk := junk); disc.
    + specialize (P24 eq_refl).
      eapply fr_eof with (c := 0) (q := q) (rb := rb); disc.
  - destruct rb as [[i e]|].
    2: { exfalso. cbn [rpos_of rend_of] in E. unfold bv_eqb in E. rewrite Z.eqb_refl in E. discriminate. }
    cbn [rlen] in PQ, RB.
    destruct RBF as (I0 & E1 & EQ & BUFEQ).
    assert (NE : i <> e).
    { intros Hie. subst e. cbn [rpos_of rend_of] in E. unfold bv_eqb in E. rewrite Z.eqb_refl in E. discriminate. }
    destruct FL as [-> | ->]; [ | exfalso; specialize (P24 eq_refl); lia ].
    cbn [rpos_of rend_of]. unfold wz.
    zstep. zstep. if_cases BL2.
    + zify_cond BL2.
      eapply fr_copy with (i := i) (e := e) (q := q) (c := e - i) (junk := junk); disc.
    + zify_cond BL2. zstep.
      eapply fr_copy with (i := i) (e := e) (q := q) (c := bv_unsigned a2) (junk := junk); disc.
Qed.
