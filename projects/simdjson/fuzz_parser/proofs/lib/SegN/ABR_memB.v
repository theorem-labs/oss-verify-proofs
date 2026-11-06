(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require PropExec StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec FP Image RunConst.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import AsanEmbed AsanCtrl.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg ABase RtCells AMalloc_iface AU_iface I_asan_memset AU_rt.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs PIosKitA PIosKit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegCall SegProg SegLib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA Require Import SegLibBr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AHMB AMEMHB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3.AX2. Import AxSymExec3Sound.AX2S. Import AxSymRun3. Import ST.
Open Scope Z_scope.
Local Notation u := bv_unsigned.

Module ABRB.

(* [comment removed for export] *)
Lemma modr : forall x lo hi, 0 <= lo -> hi - 2^64 < x < 2^64 -> lo <= x mod 2^64 <= hi -> lo <= x <= hi.
Proof.
  intros x lo hi H0 H1 H2. destruct (Z.lt_ge_cases x 0) as [Hn|Hp].
  - rewrite Zmod_eq_full in H2 by lia.
    assert (Hq : x / 2^64 = -1) by (symmetry; apply Z.div_unique with (2^64 + x); [left|]; lia).
    rewrite Hq in H2. lia.
  - rewrite Z.mod_small in H2 by lia. exact H2.
Qed.

Lemma ur : forall x : word, 0 <= u x < 2^64.
Proof. exact SLB.urange. Qed.

Lemma sval_small : forall k, 0 <= k <= 7 -> sval (Z_to_bv 8 k) = k.
Proof.
  intros k Hk. assert (E : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma unpoisoned_of_zero : forall m lo hi sb,
  0 <= lo -> lo < hi -> hi <= 2^64 -> sb = ASHOFF + lo / 8 ->
  (forall i, 0 <= i < (hi + 7) / 8 - lo / 8 -> m (wa (sb + i)) = Some (Z_to_bv 8 0)) ->
  unpoisoned m lo hi.
Proof.
  intros m lo hi sb H0 H1 H2 Hsb HZ. split; [lia|]. split; [lia|]. intros G _ HG1 HG2.
  exists (Z_to_bv 8 0). split.
  - replace (ASHOFF + G) with (sb + (G - lo / 8)) by lia. apply HZ. Z.div_mod_to_equations. lia.
  - left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma kin : forall segs E M kn K, know_ok segs E M kn -> In K kn -> kentry_ok segs E M K.
Proof. intros segs E M kn K H Hin. exact (proj1 (Forall_forall _ _) H K Hin). Qed.

Ltac zden H := repeat (first [rewrite u_add64 in H | rewrite u_sub64 in H | rewrite u_mul64 in H | rewrite u_lit64a in H]).
Ltac kget HK K := pose proof (kin _ _ _ _ K HK ltac:(cbn [app AMHB.opnd2 AMHB.opnd2p AMHB.opnd AMHB.stk2]; repeat (first [left; reflexivity | right]))).

Section Br.
Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma opnd2_ok : forall E M p n p8 g h he,
  know_ok bsegs E M (AMHB.opnd2 p n p8 g h he) -> u (edenot E n) <= 2^40 ->
  app_blk (u (edenot E p)) (u (edenot E p) + u (edenot E n))
  /\ unpoisoned M (u (edenot E p)) (u (edenot E p) + u (edenot E n))
  /\ 64 * u (edenot E h) <= u (edenot E p) /\ u (edenot E p) + u (edenot E n) <= 64 * u (edenot E he)
  /\ 0 <= 64 * u (edenot E h) /\ 64 * u (edenot E he) <= KEND
  /\ (64 * u (edenot E h)) mod 64 = 0 /\ (64 * u (edenot E he)) mod 64 = 0
  /\ wr_at bsegs M (shad (64 * u (edenot E h))) (shad (64 * u (edenot E he)) - shad (64 * u (edenot E h)))
  /\ u (edenot E (AMHB.mul 8 h)) + AMHB.SH = shad (64 * u (edenot E h))
  /\ u (edenot E (AMHB.mul 8 (AMHB.sub he h))) = shad (64 * u (edenot E he)) - shad (64 * u (edenot E h))
  /\ u (edenot E p) + u (edenot E n) <= 0x7fffff800000 /\ 0x671000 <= u (edenot E p).
Proof.
  intros E M p n p8 g h he HK HN.
  set (P := u (edenot E p)). set (N := u (edenot E n)). set (P8 := u (edenot E p8)). set (G := u (edenot E g)).
  set (H := u (edenot E h)). set (HE := u (edenot E he)).
  assert (RP := ur (edenot E p)). assert (RN := ur (edenot E n)). assert (RP8 := ur (edenot E p8)).
  assert (RG := ur (edenot E g)). assert (RH := ur (edenot E h)). assert (RHE := ur (edenot E he)).
  fold P N P8 G H HE in RP, RN, RP8, RG, RH, RHE.
  kget HK (KRange p8 0 0x200000000000). kget HK (KRange h 0 0x200000000000). kget HK (KRange he 0 0x200000000000).
  kget HK (KRange p 0x671000 0x7fffff800000). kget HK (KRange (AMHB.add p n) 0x671000 0x7fffff800000).
  kget HK (KRange (AMHB.sub p (AMHB.mul 8 p8)) 0 7). kget HK (KRange g 0 0x2000000000).
  kget HK (KRange (AMHB.sub (AMHB.mul 8 g) (AMHB.sub (AMHB.add p n) (AMHB.mul 8 p8))) 0 7).
  kget HK (KZero (SA p8 AMHB.SH) g).
  kget HK (KRange (AMHB.sub p (AMHB.mul 64 h)) 0 1048576). kget HK (KRange (AMHB.sub (AMHB.mul 64 he) (AMHB.add p n)) 0 1048576).
  kget HK (KWr (SA (AMHB.mul 8 h) AMHB.SH) (AMHB.mul 8 (AMHB.sub he h))).
  kget HK (KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA p 0) n).
  match goal with
  | H1 : kentry_ok _ _ _ (KRange p8 _ _), H2 : kentry_ok _ _ _ (KRange h _ _), H3 : kentry_ok _ _ _ (KRange he _ _),
    H4 : kentry_ok _ _ _ (KRange p _ _), H5 : kentry_ok _ _ _ (KRange (AMHB.add p n) _ _),
    H6 : kentry_ok _ _ _ (KRange (AMHB.sub p (AMHB.mul 8 p8)) _ _), H7 : kentry_ok _ _ _ (KRange g _ _),
    H8 : kentry_ok _ _ _ (KRange (AMHB.sub (AMHB.mul 8 g) _) _ _), H9 : kentry_ok _ _ _ (KZero _ _),
    H10 : kentry_ok _ _ _ (KRange (AMHB.sub p (AMHB.mul 64 h)) _ _), H11 : kentry_ok _ _ _ (KRange (AMHB.sub (AMHB.mul 64 he) _) _ _),
    H12 : kentry_ok _ _ _ (KWr _ _), H13 : kentry_ok _ _ _ (KDisj _ _ _ _) |- _ =>
    rename H1 into F11; rename H2 into F12; rename H3 into F13; rename H4 into F8; rename H5 into F9; rename H6 into F1;
    rename H7 into F2; rename H8 into F3; rename H9 into F4; rename H10 into F5; rename H11 into F6; rename H12 into F7;
    rename H13 into F10
  end.
  cbn [kentry_ok] in F11, F12, F13, F8, F2. fold P8 H HE P G in F11, F12, F13, F8, F2.
  cbn [kentry_ok AMHB.add AMHB.sub AMHB.mul edenot] in F9, F1, F3, F5, F6.
  zden F9. zden F1. zden F3. zden F5. zden F6.
  fold P N P8 G H HE in F9, F1, F3, F5, F6.
  change (8 mod 2^64) with 8 in F1, F3. change (64 mod 2^64) with 64 in F5, F6.
  rewrite (Z.mod_small (8 * P8)) in F1 by lia. rewrite (Z.mod_small (8 * P8)) in F3 by lia. rewrite (Z.mod_small (8 * G)) in F3 by lia.
  rewrite (Z.mod_small (64 * H)) in F5 by lia. rewrite (Z.mod_small (64 * HE)) in F6 by lia.
  rewrite (Z.mod_small (P + N)) in F9 by lia. rewrite (Z.mod_small (P + N)) in F3 by lia. rewrite (Z.mod_small (P + N)) in F6 by lia.
  assert (A1 : 0 <= P - 8 * P8 <= 7) by (apply modr; lia).
  assert (A3 : 0 <= 8 * G - (P + N - 8 * P8) <= 7).
  { rewrite (Z.mod_small (P + N - 8 * P8)) in F3 by lia. apply modr; lia. }
  assert (A5 : 0 <= P - 64 * H <= 1048576) by (apply modr; lia).
  assert (A6 : 0 <= 64 * HE - (P + N) <= 1048576) by (apply modr; lia).
  assert (HSH : forall x, 0 <= x -> shad (64 * x) = 8 * x + ASHOFF).
  { intros x Hx. rewrite shad_div. replace (64 * x) with ((8 * x) * 8) by lia. rewrite Z.div_mul by lia. lia. }
  split.
  { (* [comment removed for export] *)
    cbn [kentry_ok] in F10. unfold estart, elenZ in F10. cbn [a_base a_off edenot] in F10. fold P N in F10. zden F10.
    rewrite ?(Z.mod_small 0 (2^64)), ?(Z.mod_small 0x100000001000 (2^64)) in F10 by lia.
    unfold app_blk, KLOW, KHIGH, KEND. lia. }
  split.
  { (* [comment removed for export] *)
    destruct (Z.eq_dec N 0) as [N0|N0].
    - rewrite N0, Z.add_0_r. apply unpoisoned_nil. lia.
    - apply (unpoisoned_of_zero M P (P + N) (ASHOFF + P8)); [lia | lia | lia | |].
      + f_equal. Z.div_mod_to_equations. lia.
      + intros i Hi. destruct F4 as [_ Z4]. unfold elenZ, estart in Z4. cbn [a_base a_off] in Z4. fold P8 G in Z4.
        unfold wa. replace (ASHOFF + P8 + i) with (P8 + AMHB.SH + i) by (unfold ASHOFF, AMHB.SH; lia). apply Z4.
        split; [lia|]. Z.div_mod_to_equations. lia. }
  split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold KEND; lia|].
  split; [rewrite Z.mul_comm; apply Z_mod_mult|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
  assert (E1 : u (edenot E (AMHB.mul 8 h)) = 8 * H).
  { cbn [AMHB.mul edenot]. rewrite u_mul64, u_lit64a. fold H. rewrite (Z.mod_small 8) by lia. apply Z.mod_small. lia. }
  assert (E2 : u (edenot E (AMHB.mul 8 (AMHB.sub he h))) = 8 * (HE - H)).
  { cbn [AMHB.mul AMHB.sub edenot]. rewrite u_mul64, u_sub64, u_lit64a. fold H HE. rewrite (Z.mod_small 8) by lia.
    rewrite (Z.mod_small (HE - H)) by lia. apply Z.mod_small. lia. }
  split.
  { pose proof (SLB.kn_wr_at bsegs E M _ _ _ F7) as W. rewrite E1, E2 in W. rewrite !HSH by lia.
    replace (8 * HE + ASHOFF - (8 * H + ASHOFF)) with (8 * (HE - H)) by lia. unfold ASHOFF, AMHB.SH in *.
    replace (8 * H + 2147450880) with (8 * H + 2147450880) by lia. exact W. }
  split; [rewrite E1, HSH by lia; unfold ASHOFF, AMHB.SH; lia|].
  split; [rewrite E2, !HSH by lia; lia|].
  lia.
Qed.

(* [comment removed for export] *)
Lemma kword1_overlay : forall E M a v, kentry_ok bsegs E M (KWord a 1 v) -> 0x671000 <= estart E a ->
  M (Z_to_bv 64 (estart E a)) = Some (Z_to_bv 8 (u (edenot E v))).
Proof.
  intros E M a v (_ & Hf & Hr) Hlo.
  assert (EA : adenot E a = Z_to_bv 64 (estart E a)).
  { apply bv_eq. rewrite (flat_u E a _ Hf). destruct Hf as (F1 & F2 & _). rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|].
    unfold bv_modulus. cbn. lia. }
  rewrite EA in Hr. cbn [AS.PropExec.rdn] in Hr.
  destruct (M (Z_to_bv 64 (estart E a))) as [b|] eqn:Hm.
  - cbn in Hr. injection Hr as Hb. rewrite Hb. reflexivity.
  - unfold AS.PropExec.seg_rom in Hr. rewrite ref_memory_read_none in Hr; [discriminate | lia |]. destruct Hf as (F1 & F2 & _).
    rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma opnd2p_ok : forall E M p n p8 g h he z,
  know_ok bsegs E M (AMHB.opnd2p p n p8 g h he z) -> u (edenot E n) <= 2^40 ->
  app_blk (u (edenot E p)) (u (edenot E p) + u (edenot E n))
  /\ unpoisoned M (u (edenot E p)) (u (edenot E p) + u (edenot E n))
  /\ 64 * u (edenot E h) <= u (edenot E p) /\ u (edenot E p) + u (edenot E n) <= 64 * u (edenot E he)
  /\ 0 <= 64 * u (edenot E h) /\ 64 * u (edenot E he) <= KEND
  /\ (64 * u (edenot E h)) mod 64 = 0 /\ (64 * u (edenot E he)) mod 64 = 0
  /\ wr_at bsegs M (shad (64 * u (edenot E h))) (shad (64 * u (edenot E he)) - shad (64 * u (edenot E h)))
  /\ u (edenot E (AMHB.mul 8 h)) + AMHB.SH = shad (64 * u (edenot E h))
  /\ u (edenot E (AMHB.mul 8 (AMHB.sub he h))) = shad (64 * u (edenot E he)) - shad (64 * u (edenot E h))
  /\ u (edenot E p) + u (edenot E n) <= 0x7fffff800000 /\ 0x671000 <= u (edenot E p).
Proof.
  intros E M p n p8 g h he z HK HN.
  set (P := u (edenot E p)). set (N := u (edenot E n)). set (P8 := u (edenot E p8)). set (G := u (edenot E g)).
  set (H := u (edenot E h)). set (HE := u (edenot E he)). set (Zz := u (edenot E z)).
  assert (RP := ur (edenot E p)). assert (RN := ur (edenot E n)). assert (RP8 := ur (edenot E p8)).
  assert (RG := ur (edenot E g)). assert (RH := ur (edenot E h)). assert (RHE := ur (edenot E he)). assert (RZ := ur (edenot E z)).
  fold P N P8 G H HE Zz in RP, RN, RP8, RG, RH, RHE, RZ.
  kget HK (KRange p8 0 0x200000000000). kget HK (KRange h 0 0x200000000000). kget HK (KRange he 0 0x200000000000).
  kget HK (KRange p 0x671000 0x7fffff800000). kget HK (KRange (AMHB.add p n) 0x671000 0x7fffff800000).
  kget HK (KRange (AMHB.sub p (AMHB.mul 8 p8)) 0 7). kget HK (KRange g 0 0x2000000000).
  kget HK (KRange (AMHB.sub (AMHB.add p n) (AMHB.mul 8 (AMHB.add p8 g))) 1 8). kget HK (KRange z 0 1).
  kget HK (KZero (SA p8 AMHB.SH) g).
  kget HK (KWord (SA (AMHB.add p8 g) AMHB.SH) 1 (AMHB.sub (AMHB.sub (AMHB.add p n) (AMHB.mul 8 (AMHB.add p8 g))) (AMHB.mul 8 z))).
  kget HK (KRange (AMHB.sub (AMHB.sub (AMHB.add p n) (AMHB.mul 8 (AMHB.add p8 g))) (AMHB.mul 8 z)) 0 7).
  kget HK (KRange (AMHB.sub p (AMHB.mul 64 h)) 0 1048576). kget HK (KRange (AMHB.sub (AMHB.mul 64 he) (AMHB.add p n)) 0 1048576).
  kget HK (KWr (SA (AMHB.mul 8 h) AMHB.SH) (AMHB.mul 8 (AMHB.sub he h))).
  kget HK (KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA p 0) n).
  match goal with
  | H1 : kentry_ok _ _ _ (KRange p8 _ _), H2 : kentry_ok _ _ _ (KRange h _ _), H3 : kentry_ok _ _ _ (KRange he _ _),
    H4 : kentry_ok _ _ _ (KRange p _ _), H5 : kentry_ok _ _ _ (KRange (AMHB.add p n) _ _),
    H6 : kentry_ok _ _ _ (KRange (AMHB.sub p (AMHB.mul 8 p8)) _ _), H7 : kentry_ok _ _ _ (KRange g _ _),
    H8 : kentry_ok _ _ _ (KRange (AMHB.sub (AMHB.add p n) _) 1 8), H8z : kentry_ok _ _ _ (KRange z _ _),
    H9 : kentry_ok _ _ _ (KZero _ _), H9w : kentry_ok _ _ _ (KWord _ 1 _), H9r : kentry_ok _ _ _ (KRange (AMHB.sub (AMHB.sub _ _) _) 0 7),
    H10 : kentry_ok _ _ _ (KRange (AMHB.sub p (AMHB.mul 64 h)) _ _), H11 : kentry_ok _ _ _ (KRange (AMHB.sub (AMHB.mul 64 he) _) _ _),
    H12 : kentry_ok _ _ _ (KWr _ _), H13 : kentry_ok _ _ _ (KDisj _ _ _ _) |- _ =>
    rename H1 into F11; rename H2 into F12; rename H3 into F13; rename H4 into F8; rename H5 into F9; rename H6 into F1;
    rename H7 into F2; rename H8 into F3; rename H8z into FZ; rename H9 into F4; rename H9w into FW; rename H9r into F14;
    rename H10 into F5; rename H11 into F6; rename H12 into F7; rename H13 into F10
  end.
  cbn [kentry_ok] in F11, F12, F13, F8, F2, FZ. fold P8 H HE P G Zz in F11, F12, F13, F8, F2, FZ.
  cbn [kentry_ok AMHB.add AMHB.sub AMHB.mul edenot] in F9, F1, F3, F5, F6, F14.
  zden F9. zden F1. zden F3. zden F5. zden F6. zden F14.
  fold P N P8 G H HE Zz in F9, F1, F3, F5, F6, F14.
  change (8 mod 2^64) with 8 in F1, F3, F14. change (64 mod 2^64) with 64 in F5, F6.
  rewrite (Z.mod_small (8 * P8)) in F1 by lia. rewrite (Z.mod_small (64 * H)) in F5 by lia. rewrite (Z.mod_small (64 * HE)) in F6 by lia.
  rewrite (Z.mod_small (P + N)) in F9 by lia. rewrite (Z.mod_small (P + N)) in F3 by lia. rewrite (Z.mod_small (P + N)) in F6 by lia.
  rewrite (Z.mod_small (P + N)) in F14 by lia. rewrite (Z.mod_small (8 * Zz)) in F14 by lia.
  rewrite (Z.mod_small (P8 + G)) in F3 by lia. rewrite (Z.mod_small (P8 + G)) in F14 by lia.
  rewrite (Z.mod_small (8 * (P8 + G))) in F3 by lia. rewrite (Z.mod_small (8 * (P8 + G))) in F14 by lia.
  assert (A1 : 0 <= P - 8 * P8 <= 7) by (apply modr; lia).
  assert (A3 : 1 <= P + N - 8 * (P8 + G) <= 8) by (apply modr; lia).
  assert (A14 : 0 <= P + N - 8 * (P8 + G) - 8 * Zz <= 7).
  { rewrite (Z.mod_small (P + N - 8 * (P8 + G))) in F14 by lia. apply modr; lia. }
  assert (A5 : 0 <= P - 64 * H <= 1048576) by (apply modr; lia).
  assert (A6 : 0 <= 64 * HE - (P + N) <= 1048576) by (apply modr; lia).
  assert (HSH : forall x, 0 <= x -> shad (64 * x) = 8 * x + ASHOFF).
  { intros x Hx. rewrite shad_div. replace (64 * x) with ((8 * x) * 8) by lia. rewrite Z.div_mul by lia. lia. }
  split.
  { cbn [kentry_ok] in F10. unfold estart, elenZ in F10. cbn [a_base a_off edenot] in F10. fold P N in F10. zden F10.
    rewrite ?(Z.mod_small 0 (2^64)), ?(Z.mod_small 0x100000001000 (2^64)) in F10 by lia.
    unfold app_blk, KLOW, KHIGH, KEND. lia. }
  split.
  { (* [comment removed for export] *)
    split; [lia|]. split; [lia|]. intros G' HG0 HG1 HG2.
    assert (G'lo : P8 <= G') by lia. assert (G'hi : G' <= P8 + G) by lia.
    destruct (Z.eq_dec G' (P8 + G)) as [EG|NG].
    - subst G'. pose proof (kword1_overlay E M _ _ FW) as W1.
      unfold estart in W1. cbn [a_base a_off AMHB.add edenot] in W1. zden W1. fold P8 G in W1. rewrite (Z.mod_small (P8 + G)) in W1 by lia.
      unfold AMHB.SH in W1. specialize (W1 ltac:(lia)).
      cbn [AMHB.sub AMHB.add AMHB.mul edenot] in W1. zden W1. fold P N P8 G Zz in W1. change (8 mod 2^64) with 8 in W1.
      rewrite (Z.mod_small (P + N)), (Z.mod_small (P8 + G)), (Z.mod_small (8 * (P8 + G))), (Z.mod_small (8 * Zz)) in W1 by lia.
      rewrite (Z.mod_small (P + N - 8 * (P8 + G))) in W1 by lia. rewrite (Z.mod_small (P + N - 8 * (P8 + G) - 8 * Zz)) in W1 by lia.
      exists (Z_to_bv 8 (P + N - 8 * (P8 + G) - 8 * Zz)). split.
      + unfold wa. replace (ASHOFF + (P8 + G)) with (P8 + G + 2147450880) by (unfold ASHOFF; lia). exact W1.
      + unfold gran_ok. rewrite sval_small by lia.
        replace (Z.min (8 * (P8 + G) + 8) (P + N) - 8 * (P8 + G)) with (P + N - 8 * (P8 + G)) by lia.
        destruct (Z.eq_dec Zz 0) as [Z0|Z1]; [right; lia | left; lia].
    - exists (Z_to_bv 8 0). split; [|left; reflexivity].
      destruct F4 as [_ Z4]. unfold elenZ, estart in Z4. cbn [a_base a_off] in Z4. fold P8 G in Z4.
      unfold wa. replace (ASHOFF + G') with (P8 + AMHB.SH + (G' - P8)) by (unfold ASHOFF, AMHB.SH; lia). apply Z4. lia. }
  split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold KEND; lia|].
  split; [rewrite Z.mul_comm; apply Z_mod_mult|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
  assert (E1 : u (edenot E (AMHB.mul 8 h)) = 8 * H).
  { cbn [AMHB.mul edenot]. rewrite u_mul64, u_lit64a. fold H. rewrite (Z.mod_small 8) by lia. apply Z.mod_small. lia. }
  assert (E2 : u (edenot E (AMHB.mul 8 (AMHB.sub he h))) = 8 * (HE - H)).
  { cbn [AMHB.mul AMHB.sub edenot]. rewrite u_mul64, u_sub64, u_lit64a. fold H HE. rewrite (Z.mod_small 8) by lia.
    rewrite (Z.mod_small (HE - H)) by lia. apply Z.mod_small. lia. }
  split.
  { pose proof (SLB.kn_wr_at bsegs E M _ _ _ F7) as W. rewrite E1, E2 in W. rewrite !HSH by lia.
    replace (8 * HE + ASHOFF - (8 * H + ASHOFF)) with (8 * (HE - H)) by lia. unfold ASHOFF, AMHB.SH in *. exact W. }
  split; [rewrite E1, HSH by lia; unfold ASHOFF, AMHB.SH; lia|].
  split; [rewrite E2, !HSH by lia; lia|].
  lia.
Qed.

(* [comment removed for export] *)
Lemma opnd_ok : forall E M p8 n8 h stk,
  know_ok bsegs E M (AMHB.opnd p8 n8 h stk) -> u (edenot E n8) <= 62 ->
  u (edenot E (AMHB.mul 8 p8)) = 8 * u (edenot E p8) /\ u (edenot E (AMHB.mul 8 n8)) = 8 * u (edenot E n8)
  /\ app_blk (8 * u (edenot E p8)) (8 * u (edenot E p8) + 8 * u (edenot E n8))
  /\ unpoisoned M (8 * u (edenot E p8)) (8 * u (edenot E p8) + 8 * u (edenot E n8))
  /\ 8 * u (edenot E (AMHB.mul 8 h)) <= 8 * u (edenot E p8)
  /\ 8 * u (edenot E p8) + 8 * u (edenot E n8) <= 8 * u (edenot E (AMHB.mul 8 h)) + 576
  /\ 8 * u (edenot E (AMHB.mul 8 h)) + 576 <= KEND
  /\ (8 * u (edenot E (AMHB.mul 8 h))) mod 64 = 0 /\ (8 * u (edenot E (AMHB.mul 8 h)) + 576) mod 64 = 0
  /\ wr_at bsegs M (shad (8 * u (edenot E (AMHB.mul 8 h)))) (shad (8 * u (edenot E (AMHB.mul 8 h)) + 576) - shad (8 * u (edenot E (AMHB.mul 8 h))))
  /\ shad (8 * u (edenot E (AMHB.mul 8 h))) = u (edenot E (AMHB.mul 8 h)) + AMHB.SH
  /\ shad (8 * u (edenot E (AMHB.mul 8 h)) + 576) - shad (8 * u (edenot E (AMHB.mul 8 h))) = 72
  /\ 0xce204 <= u (edenot E p8) <= 0xfffffefffff.
Proof.
  intros E M p8 n8 h stk HK HN.
  set (P8 := u (edenot E p8)). set (N8 := u (edenot E n8)). set (r := u (edenot E (AMHB.mul 8 h))).
  assert (RP8 := ur (edenot E p8)). assert (RN8 := ur (edenot E n8)). assert (Rr := ur (edenot E (AMHB.mul 8 h))). fold P8 N8 r in RP8, RN8, Rr.
  kget HK (KRange p8 0xce204 0xfffffefffff). kget HK (KZero (SA p8 AMHB.SH) n8).
  kget HK (KRange (AMHB.add (AMHB.mul 8 p8) (AMHB.mul 8 n8)) 0x671000 0x7fffff800000).
  kget HK (KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA (AMHB.mul 8 p8) 0) (AMHB.mul 8 n8)).
  kget HK (KRange (AMHB.sub p8 (AMHB.mul 8 h)) 4 72). kget HK (KRange (AMHB.sub (AMHB.add (AMHB.mul 8 h) (ELit 72)) (AMHB.add p8 n8)) 0 68).
  kget HK (KWr (SA (AMHB.mul 8 h) AMHB.SH) (ELit 72)).
  match goal with
  | H1 : kentry_ok _ _ _ (KRange p8 _ _), H2 : kentry_ok _ _ _ (KZero _ _), H3 : kentry_ok _ _ _ (KRange (AMHB.add _ _) _ _),
    H4 : kentry_ok _ _ _ (KDisj _ _ _ _), H5 : kentry_ok _ _ _ (KRange (AMHB.sub p8 _) _ _),
    H6 : kentry_ok _ _ _ (KRange (AMHB.sub (AMHB.add (AMHB.mul 8 h) _) _) _ _), H7 : kentry_ok _ _ _ (KWr _ _) |- _ =>
    rename H1 into F1; rename H2 into F2; rename H3 into F3; rename H4 into F4; rename H5 into F5; rename H6 into F6; rename H7 into F7
  end.
  cbn [kentry_ok] in F1. fold P8 in F1.
  assert (E8P : u (edenot E (AMHB.mul 8 p8)) = 8 * P8).
  { cbn [AMHB.mul edenot]. rewrite u_mul64, u_lit64a. fold P8. rewrite (Z.mod_small 8) by lia. apply Z.mod_small. lia. }
  assert (E8N : u (edenot E (AMHB.mul 8 n8)) = 8 * N8).
  { cbn [AMHB.mul edenot]. rewrite u_mul64, u_lit64a. fold N8. rewrite (Z.mod_small 8) by lia. apply Z.mod_small. lia. }
  cbn [kentry_ok] in F3, F5, F6. cbn [AMHB.add AMHB.sub edenot] in F3, F5, F6.
  rewrite u_add64 in F3. change (u (edenot E (AMHB.mul 8 p8))) with (u (edenot E (AMHB.mul 8 p8))) in F3.
  cbn [AMHB.mul] in E8P, E8N. rewrite E8P, E8N in F3. rewrite (Z.mod_small (8 * P8 + 8 * N8)) in F3 by lia.
  rewrite u_sub64 in F5. fold P8 in F5. change (u (mul_div M_MUL (Z_to_bv 64 8) (edenot E h))) with r in F5.
  rewrite u_sub64, u_add64, u_add64, u_lit64a in F6. fold P8 N8 in F6. change (u (mul_div M_MUL (Z_to_bv 64 8) (edenot E h))) with r in F6.
  rewrite (Z.mod_small 72) in F6 by lia. rewrite (Z.mod_small (r + 72)) in F6 by lia. rewrite (Z.mod_small (P8 + N8)) in F6 by lia.
  assert (A5 : 4 <= P8 - r <= 72) by (apply modr; lia).
  assert (A6 : 0 <= r + 72 - (P8 + N8) <= 68) by (apply modr; lia).
  assert (HSH : shad (8 * r) = r + AMHB.SH) by (rewrite shad_div; unfold ASHOFF, AMHB.SH; rewrite Z.mul_comm, Z.div_mul by lia; lia).
  assert (HSH2 : shad (8 * r + 576) = r + 72 + AMHB.SH).
  { rewrite shad_div; unfold ASHOFF, AMHB.SH. replace (8 * r + 576) with ((r + 72) * 8) by lia. rewrite Z.div_mul by lia. lia. }
  split; [exact E8P|]. split; [exact E8N|].
  split.
  { cbn [kentry_ok] in F4. unfold estart, elenZ in F4. cbn [a_base a_off] in F4. rewrite E8P, E8N in F4.
    cbn [edenot] in F4. rewrite !SLB.u64 in F4 by lia. unfold app_blk, KLOW, KHIGH, KEND. lia. }
  split.
  { destruct (Z.eq_dec N8 0) as [N0|N0].
    - rewrite N0. rewrite Z.mul_0_r, Z.add_0_r. apply unpoisoned_nil. lia.
    - apply (unpoisoned_of_zero M (8 * P8) (8 * P8 + 8 * N8) (ASHOFF + P8)); [lia | lia | lia | |].
      + f_equal. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
      + intros i Hi. destruct F2 as [_ Z2]. unfold elenZ, estart in Z2. cbn [a_base a_off] in Z2. fold P8 N8 in Z2.
        unfold wa. replace (ASHOFF + P8 + i) with (P8 + AMHB.SH + i) by (unfold ASHOFF, AMHB.SH; lia). apply Z2.
        assert (Q1 : (8 * P8 + 8 * N8 + 7) / 8 = P8 + N8) by (clear; Z.div_mod_to_equations; lia).
        assert (Q2 : 8 * P8 / 8 = P8) by (clear; Z.div_mod_to_equations; lia).
        rewrite Q1, Q2 in Hi. lia. }
  split; [lia|]. split; [lia|]. split; [unfold KEND; lia|].
  assert (R8 : r mod 8 = 0).
  { unfold r. cbn [AMHB.mul edenot]. rewrite u_mul64, u_lit64a. rewrite (Z.mod_small 8) by lia.
    rewrite Z.mod_mod_divide; [| exists (2^61); reflexivity]. rewrite Z.mul_comm. apply Z_mod_mult. }
  assert (R8' : exists k, r = 8 * k) by (exists (r / 8); Z.div_mod_to_equations; lia). destruct R8' as [k Hk].
  split; [rewrite Hk; replace (8 * (8 * k)) with (k * 64) by lia; apply Z_mod_mult|].
  split; [rewrite Hk; replace (8 * (8 * k) + 576) with ((k + 9) * 64) by lia; apply Z_mod_mult|].
  split.
  { pose proof (SLB.kn_wr_at bsegs E M _ _ _ F7) as W. fold r in W. cbn [edenot] in W. rewrite ?SLB.u64 in W by lia. rewrite HSH, HSH2.
    replace (r + 72 + AMHB.SH - (r + AMHB.SH)) with 72 by lia. exact W. }
  split; [exact HSH|]. split; [rewrite HSH, HSH2; lia|]. lia.
Qed.

End Br.

(* [comment removed for export] *)
Section Bridge.
Context {rc : runConstT}.
Variable AI : AMallocIface.
Variables (L : alayout) (RNGh : ExecF.footprint) (st : astate) (LB : list ablock).
Variable GP : nat -> list word -> (word -> option byte) -> Prop.
Local Notation hmH := (AHMB.hmH AI L RNGh st LB).
Local Notation hmA := (AHMB.hmA AI LB).
Local Notation hmC := (AHMB.hmC AI LB).
Local Notation hmR := AHMB.hmR.

Lemma ra_lit : forall (x : word) rpc, 0 <= rpc < 2^64 -> rpc <= u x <= rpc -> x = Z_to_bv 64 rpc.
Proof. intros x rpc H1 H2. apply bv_eq. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia). lia. Qed.

(* [comment removed for export] *)
Lemma msag_lib : forall c rpc, 0 <= c < 256 -> 0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  SLib.summ_libH bsegs GP hmH hmA hmC hmR (AMHB.MSAG c rpc).
Proof.
  intros c rpc Hc Hr0 Hr2 E M rom R F fc HRom HAG HWC HHM HRF HR HK _ HZ.
  unfold AHMB.hmR in HRom. subst rom. destruct HHM as [HH MI].
  cbn [AMHB.MSAG SP.SUMR SP.sm_pre SP.sm_post SP.sm_A SP.sm_W SP.sm_G SP.sm_PS t_pc t_regs t_know AMHB.MSG_pre AMHB.MSG_post TM] in *.
  rewrite (regs_ok_canon E (AMHB.MSG_pre_regs c) R HRF HR).
  unfold AMHB.MSG_pre_kn in HK.
  pose proof HK as HK0. apply Forall_app in HK0 as [_ HKa]. apply Forall_app in HKa as [_ HKb]. apply Forall_app in HKb as [_ HKO].
  kget HK (KRange (AMHB.V 0) rpc rpc). kget HK (KRange (AMHB.V 1) (0x7ffe00000000 + 2208) 0x800000000000).
  kget HK (KWr (SA AMHB.vSP (-2208)) (ELit 2208)). kget HK (KUnk (SA AMHB.vSP (-2208)) (ELit 2208)).
  kget HK (KRange (AMHB.V 17) 0 0x10000000000). kget HK (KWr (SA (AMHB.V 16) 0) (AMHB.V 17)). kget HK (KUnk (SA (AMHB.V 16) 0) (AMHB.V 17)).
  kget HK (KDisj (SA AMHB.vSP (-2208)) (ELit 2208) (SA (AMHB.V 16) 0) (AMHB.V 17)).
  match goal with
  | K0 : kentry_ok _ _ _ (KRange (AMHB.V 0) _ _), K1 : kentry_ok _ _ _ (KRange (AMHB.V 1) _ _),
    K2 : kentry_ok _ _ _ (KWr (SA AMHB.vSP _) _), K3 : kentry_ok _ _ _ (KUnk (SA AMHB.vSP _) _),
    K4 : kentry_ok _ _ _ (KRange (AMHB.V 17) _ _), K5 : kentry_ok _ _ _ (KWr (SA (AMHB.V 16) 0) _),
    K6 : kentry_ok _ _ _ (KUnk (SA (AMHB.V 16) 0) _), K7 : kentry_ok _ _ _ (KDisj _ _ _ _) |- _ =>
    rename K0 into KRA; rename K1 into KSP; rename K2 into KSW; rename K3 into KSU; rename K4 into KN; rename K5 into KDW;
    rename K6 into KDU; rename K7 into KDJ
  end.
  cbn [kentry_ok AMHB.V edenot] in KRA, KSP, KN.
  set (sp := u (ev E 1)) in *. set (D := u (ev E 16)) in *. set (N := u (ev E 17)) in *.
  pose proof (ur (ev E 1)) as Rsp. pose proof (ur (ev E 16)) as RD. pose proof (ur (ev E 17)) as RN. fold sp D N in Rsp, RD, RN.
  destruct (opnd2_ok E M _ _ _ _ _ _ HKO ltac:(cbn [AMHB.V edenot]; fold N; lia))
    as (APP & UNP & HL1 & HL2 & HL3 & HL4 & HL5 & HL6 & WRS & EH1 & EH2 & PB1 & PB2).
  cbn [AMHB.V edenot] in APP, UNP, HL1, HL2, HL3, HL4, HL5, HL6, WRS, EH1, EH2, PB1, PB2. fold D N in APP, UNP, HL1, HL2, PB1, PB2.
  set (H := u (ev E 20)) in *. set (HE := u (ev E 21)) in *.
  (* [comment removed for export] *)
  pose proof (SLB.kn_stk bsegs E M _ _ _ KSW KSU) as STK. cbn [AMHB.vSP AMHB.V edenot] in STK. fold sp in STK.
  rewrite SLB.u64 in STK by lia. replace (sp + -2208 + 2208) with sp in STK by lia. replace (sp + -2208) with (sp - 2208) in STK by lia.
  (* [comment removed for export] *)
  destruct (SLB.kn_rw_CB bsegs E M _ _ _ KDW KDU) as (junk & DST). cbn [AMHB.V edenot] in DST. fold D N in DST. rewrite Z.add_0_r in DST.
  cbn [kentry_ok] in KDJ. unfold estart, elenZ in KDJ. cbn [a_base a_off AMHB.vSP AMHB.V edenot] in KDJ. fold sp D N in KDJ.
  rewrite SLB.u64 in KDJ by lia.
  (* [comment removed for export] *)
  destruct (AI_rtcells AI L RNGh st LB M HH) as (_ & GOT & RIC & REAL & SHB & _ & INI & LAY & _).
  (* [comment removed for export] *)
  assert (RW : forall w lo len, In w AMHB.MSG_A -> fst (SX.awin_den E w) <= lo -> lo + len <= snd (SX.awin_den E w) -> 0 <= len ->
                 ExecF.rng (SX.fp_of (Some AMHB.MSG_A) E) lo len).
  { intros w lo len Hw H1 H2 H3. pose proof (SLib.rng_fp_of AMHB.MSG_A E w HAG Hw) as R0. eapply ExecF.rng_sub; [exact R0 | lia | lia]. }
  assert (RIMG : ExecF.rng (SX.fp_of (Some AMHB.MSG_A) E) 0x10000 0x661000).
  { apply (RW AMHB.IMGW); [cbn; tauto | cbn [SX.awin_den AMHB.IMGW edenot fst snd]; rewrite !SLB.u64 by lia; lia .. | lia]. }
  assert (RSTK : ExecF.rng (SX.fp_of (Some AMHB.MSG_A) E) (sp - 2208) (sp - (sp - 2208))).
  { apply (RW (AMHB.vSP, -2208, ELit 2208)); [cbn; tauto | cbn [SX.awin_den edenot AMHB.vSP AMHB.V fst snd]; fold sp; rewrite ?SLB.u64 by lia; lia .. | lia]. }
  assert (RDST : ExecF.rng (SX.fp_of (Some AMHB.MSG_A) E) D N).
  { apply (RW (AMHB.V 16, 0, AMHB.V 17)); [cbn; tauto | cbn [SX.awin_den edenot AMHB.V fst snd]; fold D N; lia .. | lia]. }
  assert (RSH : ExecF.rng (SX.fp_of (Some AMHB.MSG_A) E) (shad (64 * H)) (shad (64 * HE) - shad (64 * H))).
  { apply (RW (AMHB.hullw (AMHB.V 20) (AMHB.V 21))); [cbn; tauto | cbn [SX.awin_den AMHB.hullw fst snd]; unfold AMHB.SH in *; lia .. | ].
    rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  pose proof (asan_memset_spec (SX.fp_of (Some AMHB.MSG_A) E) (ev E 0) (ev E 1) (ev E 2) (ev E 3) (ev E 22) (ev E 23) (ev E 24) (ev E 4) (ev E 5)
                (ev E 16) (Z_to_bv 64 c) (ev E 17) (ev E 25) (ev E 26) (ev E 27) (ev E 28) (ev E 29)
                (ev E 6) (ev E 7) (ev E 8) (ev E 9) (ev E 10) (ev E 11) (ev E 12) (ev E 13) (ev E 14) (ev E 15)
                (ev E 30) (ev E 31) (ev E 32) (ev E 33) F fc M (sp - 2208) junk (64 * H) (64 * HE)) as RUN.
  fold sp D N in RUN.
  specialize (RUN MI STK ltac:(lia) ltac:(unfold KHIGH; lia) GOT RIC SHB INI LAY REAL DST ltac:(lia) APP UNP ltac:(lia)).
  specialize (RUN ltac:(unfold KEND in *; lia) WRS RIMG RSTK RDST RSH).
  destruct RUN as (ms' & Hrun & Hpost).
  pose proof (PIosRegs.msteps_wrel bsegs _ _ (ExecF.mstepsF_msteps bsegs _ _ _ Hrun)) as HW.
  destruct Hpost as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Hms' & MU & WM & MI' & STK' & DST').
  rewrite Hms' in HW. cbn [ms_mem MS] in HW.
  exists ms'. split; [exact Hrun|].
  set (E' := SLB.env_ext E 34 [t0; t1; t2; a1'; a2'; a3; a4; a5; a6; a7; t3; t4; t5; t6]).
  assert (EQ : forall v, (v < 34)%nat -> ev E' v = ev E v) by (intros v Hv; apply SLB.env_ext_lt; exact Hv).
  exists (AMHB.MSG_post c rpc), E', m',
    (mkR (ev E 0) (ev E 1) (ev E 2) (ev E 3) t0 t1 t2 (ev E 4) (ev E 5) (ev E 16) a1' a2' a3 a4 a5 a6 a7 (ev E 6) (ev E 7) (ev E 8)
         (ev E 9) (ev E 10) (ev E 11) (ev E 12) (ev E 13) (ev E 14) (ev E 15) t3 t4 t5 t6), F, fc.
  split; [left; reflexivity|].
  split.
  { rewrite Hms'. cbn [AMHB.MSG_post TM t_pc]. f_equal. rewrite (ra_lit (ev E 0) rpc Hr0 KRA). apply ret_pc_even; assumption. }
  split; [exact HZ|]. split; [apply rfull_mkR|].
  split; [apply regs_ok_mkR; reflexivity|].
  split.
  { constructor; [|constructor].
    assert (E16 : ev E' 16 = ev E 16) by (apply EQ; lia). assert (E17 : ev E' 17 = ev E 17) by (apply EQ; lia).
    destruct DST' as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
    rewrite SLB.u64 in B by lia. rewrite (Z.mod_small c 256) in B by lia.
    assert (DEF : forall i, 0 <= i < N -> m' (Z_to_bv 64 (D + i)) = Some (Z_to_bv 8 c)).
    { intros i Hi. destruct B as (B1 & B2 & HB). specialize (HB (Z.to_nat i)). rewrite repeat_length in HB.
      specialize (HB ltac:(fold N; lia)). rewrite Z2Nat.id in HB by lia. unfold mrd, wa in HB. fold D in HB.
      pose proof (SLB.kn_defined bsegs E M (AMHB.V 16) 0 (AMHB.V 17) KDU i) as D0. cbn [AMHB.V edenot] in D0. fold D N in D0.
      rewrite Z.add_0_r in D0.
      pose proof (SC.wrel_grows bsegs _ _ HW _ (D0 Hi)) as D1. unfold wa in D1.
      destruct (m' (Z_to_bv 64 (D + i))) as [x|]; [|contradiction].
      rewrite HB. rewrite nth_error_repeat by lia. reflexivity. }
    destruct (Z.eqb c 0) eqn:Hc0.
    - apply Z.eqb_eq in Hc0. subst c. cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off AMHB.V edenot]. rewrite ?E16, ?E17.
      fold D N. split; [unfold flat, estart, elenZ; cbn [a_base a_off AMHB.V edenot]; rewrite ?E16, ?E17; fold D N; lia|].
      intros i Hi. rewrite Z.add_0_r. exact (DEF i Hi).
    - cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off AMHB.V edenot]. rewrite ?E16, ?E17.
      fold D N. split; [unfold flat, estart, elenZ; cbn [a_base a_off AMHB.V edenot]; rewrite ?E16, ?E17; fold D N; lia|].
      intros i Hi. rewrite Z.add_0_r. exact (DEF i Hi). }
  split; [constructor|].
  split; [apply SLB.gagree_ext; cbn [AMHB.MSAG SP.SUMR SP.sm_G]; lia|].
  split; [reflexivity|].
  assert (EQW : map (SP.win_den E) AMHB.MSG_W = [(sp - 2208, sp); (D, D + N)]).
  { cbn [map AMHB.MSG_W SP.win_den edenot AMHB.vSP AMHB.V]. fold sp D N. rewrite !SLB.u64 by lia.
    replace (sp + -2208) with (sp - 2208) by lia. replace (sp - 2208 + 2208) with sp by lia. rewrite Z.add_0_r. reflexivity. }
  split.
  { split; [|exact MI'].
    apply (AI_frame AI L RNGh st LB M m' [(sp - 2208, sp); (D, D + N)] HH MU WM).
    rewrite <- EQW. unfold SP.wins_client in HWC. apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (w & <- & Hw).
    exact (proj1 (Forall_forall _ _) HWC w Hw). }
  cbn [SP.frame_ok AMHB.MSAG SP.SUMR SP.sm_PS SP.sm_W]. apply SLB.frame_of_munch. rewrite EQW. exact MU.
Qed.

Theorem msag_ok : forall c rpc, 0 <= c < 256 -> 0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  SP.summ_okH bsegs GP hmH hmA hmC hmR (AMHB.MSAG c rpc).
Proof. intros c rpc H0 H1 H2. apply SLib.summ_of_libH. exact (msag_lib c rpc H0 H1 H2). Qed.
(* [comment removed for export] *)
Lemma msagp_lib : forall c rpc, 0 <= c < 256 -> 0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  SLib.summ_libH bsegs GP hmH hmA hmC hmR (AMHB.MSAGP c rpc).
Proof.
  intros c rpc Hc Hr0 Hr2 E M rom R F fc HRom HAG HWC HHM HRF HR HK _ HZ.
  unfold AHMB.hmR in HRom. subst rom. destruct HHM as [HH MI].
  cbn [AMHB.MSAGP SP.SUMR SP.sm_pre SP.sm_post SP.sm_A SP.sm_W SP.sm_G SP.sm_PS t_pc t_regs t_know AMHB.MSGP_pre AMHB.MSGP_post TM] in *.
  rewrite (regs_ok_canon E (AMHB.MSGP_pre_regs c) R HRF HR).
  unfold AMHB.MSGP_pre_kn in HK.
  pose proof HK as HK0. apply Forall_app in HK0 as [_ HKa]. apply Forall_app in HKa as [_ HKb]. apply Forall_app in HKb as [_ HKO].
  kget HK (KRange (AMHB.V 0) rpc rpc). kget HK (KRange (AMHB.V 1) (0x7ffe00000000 + 2208) 0x800000000000).
  kget HK (KWr (SA AMHB.vSP (-2208)) (ELit 2208)). kget HK (KUnk (SA AMHB.vSP (-2208)) (ELit 2208)).
  kget HK (KRange (AMHB.V 17) 0 0x10000000000). kget HK (KWr (SA (AMHB.V 16) 0) (AMHB.V 17)). kget HK (KUnk (SA (AMHB.V 16) 0) (AMHB.V 17)).
  kget HK (KDisj (SA AMHB.vSP (-2208)) (ELit 2208) (SA (AMHB.V 16) 0) (AMHB.V 17)).
  match goal with
  | K0 : kentry_ok _ _ _ (KRange (AMHB.V 0) _ _), K1 : kentry_ok _ _ _ (KRange (AMHB.V 1) _ _),
    K2 : kentry_ok _ _ _ (KWr (SA AMHB.vSP _) _), K3 : kentry_ok _ _ _ (KUnk (SA AMHB.vSP _) _),
    K4 : kentry_ok _ _ _ (KRange (AMHB.V 17) _ _), K5 : kentry_ok _ _ _ (KWr (SA (AMHB.V 16) 0) _),
    K6 : kentry_ok _ _ _ (KUnk (SA (AMHB.V 16) 0) _), K7 : kentry_ok _ _ _ (KDisj _ _ _ _) |- _ =>
    rename K0 into KRA; rename K1 into KSP; rename K2 into KSW; rename K3 into KSU; rename K4 into KN; rename K5 into KDW;
    rename K6 into KDU; rename K7 into KDJ
  end.
  cbn [kentry_ok AMHB.V edenot] in KRA, KSP, KN.
  set (sp := u (ev E 1)) in *. set (D := u (ev E 16)) in *. set (N := u (ev E 17)) in *.
  pose proof (ur (ev E 1)) as Rsp. pose proof (ur (ev E 16)) as RD. pose proof (ur (ev E 17)) as RN. fold sp D N in Rsp, RD, RN.
  destruct (opnd2p_ok E M _ _ _ _ _ _ _ HKO ltac:(cbn [AMHB.V edenot]; fold N; lia))
    as (APP & UNP & HL1 & HL2 & HL3 & HL4 & HL5 & HL6 & WRS & EH1 & EH2 & PB1 & PB2).
  cbn [AMHB.V edenot] in APP, UNP, HL1, HL2, HL3, HL4, HL5, HL6, WRS, EH1, EH2, PB1, PB2. fold D N in APP, UNP, HL1, HL2, PB1, PB2.
  set (H := u (ev E 20)) in *. set (HE := u (ev E 21)) in *.
  (* [comment removed for export] *)
  pose proof (SLB.kn_stk bsegs E M _ _ _ KSW KSU) as STK. cbn [AMHB.vSP AMHB.V edenot] in STK. fold sp in STK.
  rewrite SLB.u64 in STK by lia. replace (sp + -2208 + 2208) with sp in STK by lia. replace (sp + -2208) with (sp - 2208) in STK by lia.
  (* [comment removed for export] *)
  destruct (SLB.kn_rw_CB bsegs E M _ _ _ KDW KDU) as (junk & DST). cbn [AMHB.V edenot] in DST. fold D N in DST. rewrite Z.add_0_r in DST.
  cbn [kentry_ok] in KDJ. unfold estart, elenZ in KDJ. cbn [a_base a_off AMHB.vSP AMHB.V edenot] in KDJ. fold sp D N in KDJ.
  rewrite SLB.u64 in KDJ by lia.
  (* [comment removed for export] *)
  destruct (AI_rtcells AI L RNGh st LB M HH) as (_ & GOT & RIC & REAL & SHB & _ & INI & LAY & _).
  (* [comment removed for export] *)
  assert (RW : forall w lo len, In w AMHB.MSG_A -> fst (SX.awin_den E w) <= lo -> lo + len <= snd (SX.awin_den E w) -> 0 <= len ->
                 ExecF.rng (SX.fp_of (Some AMHB.MSG_A) E) lo len).
  { intros w lo len Hw H1 H2 H3. pose proof (SLib.rng_fp_of AMHB.MSG_A E w HAG Hw) as R0. eapply ExecF.rng_sub; [exact R0 | lia | lia]. }
  assert (RIMG : ExecF.rng (SX.fp_of (Some AMHB.MSG_A) E) 0x10000 0x661000).
  { apply (RW AMHB.IMGW); [cbn; tauto | cbn [SX.awin_den AMHB.IMGW edenot fst snd]; rewrite !SLB.u64 by lia; lia .. | lia]. }
  assert (RSTK : ExecF.rng (SX.fp_of (Some AMHB.MSG_A) E) (sp - 2208) (sp - (sp - 2208))).
  { apply (RW (AMHB.vSP, -2208, ELit 2208)); [cbn; tauto | cbn [SX.awin_den edenot AMHB.vSP AMHB.V fst snd]; fold sp; rewrite ?SLB.u64 by lia; lia .. | lia]. }
  assert (RDST : ExecF.rng (SX.fp_of (Some AMHB.MSG_A) E) D N).
  { apply (RW (AMHB.V 16, 0, AMHB.V 17)); [cbn; tauto | cbn [SX.awin_den edenot AMHB.V fst snd]; fold D N; lia .. | lia]. }
  assert (RSH : ExecF.rng (SX.fp_of (Some AMHB.MSG_A) E) (shad (64 * H)) (shad (64 * HE) - shad (64 * H))).
  { apply (RW (AMHB.hullw (AMHB.V 20) (AMHB.V 21))); [cbn; tauto | cbn [SX.awin_den AMHB.hullw fst snd]; unfold AMHB.SH in *; lia .. | ].
    rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  pose proof (asan_memset_spec (SX.fp_of (Some AMHB.MSG_A) E) (ev E 0) (ev E 1) (ev E 2) (ev E 3) (ev E 23) (ev E 24) (ev E 25) (ev E 4) (ev E 5)
                (ev E 16) (Z_to_bv 64 c) (ev E 17) (ev E 26) (ev E 27) (ev E 28) (ev E 29) (ev E 30)
                (ev E 6) (ev E 7) (ev E 8) (ev E 9) (ev E 10) (ev E 11) (ev E 12) (ev E 13) (ev E 14) (ev E 15)
                (ev E 31) (ev E 32) (ev E 33) (ev E 34) F fc M (sp - 2208) junk (64 * H) (64 * HE)) as RUN.
  fold sp D N in RUN.
  specialize (RUN MI STK ltac:(lia) ltac:(unfold KHIGH; lia) GOT RIC SHB INI LAY REAL DST ltac:(lia) APP UNP ltac:(lia)).
  specialize (RUN ltac:(unfold KEND in *; lia) WRS RIMG RSTK RDST RSH).
  destruct RUN as (ms' & Hrun & Hpost).
  pose proof (PIosRegs.msteps_wrel bsegs _ _ (ExecF.mstepsF_msteps bsegs _ _ _ Hrun)) as HW.
  destruct Hpost as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Hms' & MU & WM & MI' & STK' & DST').
  rewrite Hms' in HW. cbn [ms_mem MS] in HW.
  exists ms'. split; [exact Hrun|].
  set (E' := SLB.env_ext E 35 [t0; t1; t2; a1'; a2'; a3; a4; a5; a6; a7; t3; t4; t5; t6]).
  assert (EQ : forall v, (v < 35)%nat -> ev E' v = ev E v) by (intros v Hv; apply SLB.env_ext_lt; exact Hv).
  exists (AMHB.MSGP_post c rpc), E', m',
    (mkR (ev E 0) (ev E 1) (ev E 2) (ev E 3) t0 t1 t2 (ev E 4) (ev E 5) (ev E 16) a1' a2' a3 a4 a5 a6 a7 (ev E 6) (ev E 7) (ev E 8)
         (ev E 9) (ev E 10) (ev E 11) (ev E 12) (ev E 13) (ev E 14) (ev E 15) t3 t4 t5 t6), F, fc.
  split; [left; reflexivity|].
  split.
  { rewrite Hms'. cbn [AMHB.MSGP_post TM t_pc]. f_equal. rewrite (ra_lit (ev E 0) rpc Hr0 KRA). apply ret_pc_even; assumption. }
  split; [exact HZ|]. split; [apply rfull_mkR|].
  split; [apply regs_ok_mkR; reflexivity|].
  split.
  { constructor; [|constructor].
    assert (E16 : ev E' 16 = ev E 16) by (apply EQ; lia). assert (E17 : ev E' 17 = ev E 17) by (apply EQ; lia).
    destruct DST' as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
    rewrite SLB.u64 in B by lia. rewrite (Z.mod_small c 256) in B by lia.
    assert (DEF : forall i, 0 <= i < N -> m' (Z_to_bv 64 (D + i)) = Some (Z_to_bv 8 c)).
    { intros i Hi. destruct B as (B1 & B2 & HB). specialize (HB (Z.to_nat i)). rewrite repeat_length in HB.
      specialize (HB ltac:(fold N; lia)). rewrite Z2Nat.id in HB by lia. unfold mrd, wa in HB. fold D in HB.
      pose proof (SLB.kn_defined bsegs E M (AMHB.V 16) 0 (AMHB.V 17) KDU i) as D0. cbn [AMHB.V edenot] in D0. fold D N in D0.
      rewrite Z.add_0_r in D0.
      pose proof (SC.wrel_grows bsegs _ _ HW _ (D0 Hi)) as D1. unfold wa in D1.
      destruct (m' (Z_to_bv 64 (D + i))) as [x|]; [|contradiction].
      rewrite HB. rewrite nth_error_repeat by lia. reflexivity. }
    destruct (Z.eqb c 0) eqn:Hc0.
    - apply Z.eqb_eq in Hc0. subst c. cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off AMHB.V edenot]. rewrite ?E16, ?E17.
      fold D N. split; [unfold flat, estart, elenZ; cbn [a_base a_off AMHB.V edenot]; rewrite ?E16, ?E17; fold D N; lia|].
      intros i Hi. rewrite Z.add_0_r. exact (DEF i Hi).
    - cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off AMHB.V edenot]. rewrite ?E16, ?E17.
      fold D N. split; [unfold flat, estart, elenZ; cbn [a_base a_off AMHB.V edenot]; rewrite ?E16, ?E17; fold D N; lia|].
      intros i Hi. rewrite Z.add_0_r. exact (DEF i Hi). }
  split; [constructor|].
  split; [apply SLB.gagree_ext; cbn [AMHB.MSAGP SP.SUMR SP.sm_G]; lia|].
  split; [reflexivity|].
  assert (EQW : map (SP.win_den E) AMHB.MSG_W = [(sp - 2208, sp); (D, D + N)]).
  { cbn [map AMHB.MSG_W SP.win_den edenot AMHB.vSP AMHB.V]. fold sp D N. rewrite !SLB.u64 by lia.
    replace (sp + -2208) with (sp - 2208) by lia. replace (sp - 2208 + 2208) with sp by lia. rewrite Z.add_0_r. reflexivity. }
  split.
  { split; [|exact MI'].
    apply (AI_frame AI L RNGh st LB M m' [(sp - 2208, sp); (D, D + N)] HH MU WM).
    rewrite <- EQW. unfold SP.wins_client in HWC. apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (w & <- & Hw).
    exact (proj1 (Forall_forall _ _) HWC w Hw). }
  cbn [SP.frame_ok AMHB.MSAGP SP.SUMR SP.sm_PS SP.sm_W]. apply SLB.frame_of_munch. rewrite EQW. exact MU.
Qed.

Theorem msagp_ok : forall c rpc, 0 <= c < 256 -> 0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  SP.summ_okH bsegs GP hmH hmA hmC hmR (AMHB.MSAGP c rpc).
Proof. intros c rpc H0 H1 H2. apply SLib.summ_of_libH. exact (msagp_lib c rpc H0 H1 H2). Qed.

(* [comment removed for export] *)
Lemma mcag_lib : forall rpc, 0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  SLib.summ_libH bsegs GP hmH hmA hmC hmR (AMHB.MCAG rpc).
Proof.
  intros rpc Hr0 Hr2 E M rom R F fc HRom HAG HWC HHM HRF HR HK _ HZ.
  unfold AHMB.hmR in HRom. subst rom. destruct HHM as [HH MI].
  cbn [AMHB.MCAG SP.SUMR SP.sm_pre SP.sm_post SP.sm_A SP.sm_W SP.sm_G SP.sm_PS t_pc t_regs t_know AMHB.MCG_pre AMHB.MCG_post TM] in *.
  rewrite (regs_ok_canon E AMHB.MG_pre_regs R HRF HR).
  unfold AMHB.MCG_pre_kn in HK.
  pose proof HK as HK0. apply Forall_app in HK0 as [_ HKa]. apply Forall_app in HKa as [_ HKb]. apply Forall_app in HKb as [_ HKc].
  apply Forall_app in HKc as [HKOD HKOS].
  kget HK (KRange (AMHB.V 0) rpc rpc). kget HK (KRange (AMHB.V 1) (0x7ffe00000000 + 2224) 0x800000000000).
  kget HK (KWr (SA AMHB.vSP (-2224)) (ELit 2224)). kget HK (KUnk (SA AMHB.vSP (-2224)) (ELit 2224)).
  kget HK (KRange (AMHB.V 18) 0 0x10000000000). kget HK (KUnk (SA (AMHB.V 17) 0) (AMHB.V 18)).
  kget HK (KWr (SA (AMHB.V 16) 0) (AMHB.V 18)). kget HK (KUnk (SA (AMHB.V 16) 0) (AMHB.V 18)).
  kget HK (KDisj (SA (AMHB.V 17) 0) (AMHB.V 18) (SA (AMHB.V 16) 0) (AMHB.V 18)).
  kget HK (KDisj (SA AMHB.vSP (-2224)) (ELit 2224) (SA (AMHB.V 16) 0) (AMHB.V 18)).
  kget HK (KDisj (SA AMHB.vSP (-2224)) (ELit 2224) (SA (AMHB.V 17) 0) (AMHB.V 18)).
  match goal with
  | K0 : kentry_ok _ _ _ (KRange (AMHB.V 0) _ _), K1 : kentry_ok _ _ _ (KRange (AMHB.V 1) _ _),
    K2 : kentry_ok _ _ _ (KWr (SA AMHB.vSP _) _), K3 : kentry_ok _ _ _ (KUnk (SA AMHB.vSP _) _),
    K4 : kentry_ok _ _ _ (KRange (AMHB.V 18) _ _), K5 : kentry_ok _ _ _ (KUnk (SA (AMHB.V 17) 0) _),
    K6 : kentry_ok _ _ _ (KWr (SA (AMHB.V 16) 0) _), K7 : kentry_ok _ _ _ (KUnk (SA (AMHB.V 16) 0) _),
    K8 : kentry_ok _ _ _ (KDisj (SA (AMHB.V 17) 0) _ _ _), K9 : kentry_ok _ _ _ (KDisj (SA AMHB.vSP _) _ (SA (AMHB.V 16) 0) _),
    K10 : kentry_ok _ _ _ (KDisj (SA AMHB.vSP _) _ (SA (AMHB.V 17) 0) _) |- _ =>
    rename K0 into KRA; rename K1 into KSP; rename K2 into KSW; rename K3 into KSU; rename K4 into KN; rename K5 into KSRC;
    rename K6 into KDW; rename K7 into KDU; rename K8 into KDJ; rename K9 into KDJD; rename K10 into KDJS
  end.
  cbn [kentry_ok AMHB.V edenot] in KRA, KSP, KN.
  set (sp := u (ev E 1)) in *. set (D := u (ev E 16)) in *. set (S := u (ev E 17)) in *. set (N := u (ev E 18)) in *.
  pose proof (ur (ev E 1)) as Rsp. pose proof (ur (ev E 16)) as RD. pose proof (ur (ev E 17)) as RS. pose proof (ur (ev E 18)) as RN.
  fold sp D S N in Rsp, RD, RS, RN.
  destruct (opnd2_ok E M _ _ _ _ _ _ HKOD ltac:(cbn [AMHB.V edenot]; fold N; lia))
    as (APPD & UNPD & HD1 & HD2 & HD3 & HD4 & HD5 & HD6 & WRSD & EHD1 & EHD2 & PBD1 & PBD2).
  destruct (opnd2_ok E M _ _ _ _ _ _ HKOS ltac:(cbn [AMHB.V edenot]; fold N; lia))
    as (APPS & UNPS & HS1 & HS2 & HS3 & HS4 & HS5 & HS6 & WRSS & EHS1 & EHS2 & PBS1 & PBS2).
  cbn [AMHB.V edenot] in APPD, UNPD, HD1, HD2, HD3, HD4, HD5, HD6, WRSD, EHD1, EHD2, PBD1, PBD2.
  cbn [AMHB.V edenot] in APPS, UNPS, HS1, HS2, HS3, HS4, HS5, HS6, WRSS, EHS1, EHS2, PBS1, PBS2.
  fold D S N in APPD, UNPD, HD1, HD2, PBD1, PBD2, APPS, UNPS, HS1, HS2, PBS1, PBS2.
  set (HD := u (ev E 21)) in *. set (HDE := u (ev E 22)) in *. set (HS := u (ev E 25)) in *. set (HSE := u (ev E 26)) in *.
  (* [comment removed for export] *)
  pose proof (SLB.kn_stk bsegs E M _ _ _ KSW KSU) as STK. cbn [AMHB.vSP AMHB.V edenot] in STK. fold sp in STK.
  rewrite SLB.u64 in STK by lia. replace (sp + -2224 + 2224) with sp in STK by lia. replace (sp + -2224) with (sp - 2224) in STK by lia.
  (* [comment removed for export] *)
  destruct (SLB.kn_bytes_of_unk bsegs E M _ _ _ KSRC) as (src & SRCB & SRCL). cbn [AMHB.V edenot] in SRCB, SRCL. fold S N in SRCB, SRCL.
  rewrite Z.add_0_r in SRCB.
  destruct (SLB.kn_rw_CB bsegs E M _ _ _ KDW KDU) as (junk & DST). cbn [AMHB.V edenot] in DST. fold D N in DST. rewrite Z.add_0_r in DST.
  cbn [kentry_ok] in KDJ, KDJD, KDJS. unfold estart, elenZ in KDJ, KDJD, KDJS. cbn [a_base a_off AMHB.vSP AMHB.V edenot] in KDJ, KDJD, KDJS.
  fold sp D S N in KDJ, KDJD, KDJS. rewrite SLB.u64 in KDJD by lia. rewrite SLB.u64 in KDJS by lia.
  (* [comment removed for export] *)
  destruct (AI_rtcells AI L RNGh st LB M HH) as (_ & GOT & RIC & REAL & SHB & _ & INI & LAY & _).
  (* [comment removed for export] *)
  assert (RW : forall w lo len, In w AMHB.MCG_A -> fst (SX.awin_den E w) <= lo -> lo + len <= snd (SX.awin_den E w) -> 0 <= len ->
                 ExecF.rng (SX.fp_of (Some AMHB.MCG_A) E) lo len).
  { intros w lo len Hw H1 H2 H3. pose proof (SLib.rng_fp_of AMHB.MCG_A E w HAG Hw) as R0. eapply ExecF.rng_sub; [exact R0 | lia | lia]. }
  assert (RIMG : ExecF.rng (SX.fp_of (Some AMHB.MCG_A) E) 0x10000 0x661000).
  { apply (RW AMHB.IMGW); [cbn; tauto | cbn [SX.awin_den AMHB.IMGW edenot fst snd]; rewrite !SLB.u64 by lia; lia .. | lia]. }
  assert (RSTK : ExecF.rng (SX.fp_of (Some AMHB.MCG_A) E) (sp - 2224) (sp - (sp - 2224))).
  { apply (RW (AMHB.vSP, -2224, ELit 2224)); [cbn; tauto | cbn [SX.awin_den edenot AMHB.vSP AMHB.V fst snd]; fold sp; rewrite ?SLB.u64 by lia; lia .. | lia]. }
  assert (RSRC : ExecF.rng (SX.fp_of (Some AMHB.MCG_A) E) S N).
  { apply (RW (AMHB.V 17, 0, AMHB.V 18)); [cbn; tauto | cbn [SX.awin_den edenot AMHB.V fst snd]; fold S N; lia .. | lia]. }
  assert (RDST : ExecF.rng (SX.fp_of (Some AMHB.MCG_A) E) D N).
  { apply (RW (AMHB.V 16, 0, AMHB.V 18)); [cbn; tauto | cbn [SX.awin_den edenot AMHB.V fst snd]; fold D N; lia .. | lia]. }
  assert (RSHD : ExecF.rng (SX.fp_of (Some AMHB.MCG_A) E) (shad (64 * HD)) (shad (64 * HDE) - shad (64 * HD))).
  { apply (RW (AMHB.hullw (AMHB.V 21) (AMHB.V 22))); [cbn; tauto | cbn [SX.awin_den AMHB.hullw fst snd]; unfold AMHB.SH in *; lia .. | ].
    rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
  assert (RSHS : ExecF.rng (SX.fp_of (Some AMHB.MCG_A) E) (shad (64 * HS)) (shad (64 * HSE) - shad (64 * HS))).
  { apply (RW (AMHB.hullw (AMHB.V 25) (AMHB.V 26))); [cbn; tauto | cbn [SX.awin_den AMHB.hullw fst snd]; unfold AMHB.SH in *; lia .. | ].
    rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  pose proof (asan_memcpy_proof (SX.fp_of (Some AMHB.MCG_A) E) (ev E 0) (ev E 1) (ev E 2) (ev E 3) (ev E 27) (ev E 28) (ev E 29) (ev E 4) (ev E 5)
                (ev E 16) (ev E 17) (ev E 18) (ev E 30) (ev E 31) (ev E 32) (ev E 33) (ev E 34)
                (ev E 6) (ev E 7) (ev E 8) (ev E 9) (ev E 10) (ev E 11) (ev E 12) (ev E 13) (ev E 14) (ev E 15)
                (ev E 35) (ev E 36) (ev E 37) (ev E 38) F fc M (sp - 2224) src junk (64 * HS) (64 * HSE) (64 * HD) (64 * HDE)) as RUN.
  cbv zeta in RUN. fold sp D S N in RUN.
  specialize (RUN MI STK ltac:(unfold AMEMCPY_STACK; lia) ltac:(unfold KHIGH; lia) GOT RIC SHB INI LAY REAL SRCB SRCL DST).
  specialize (RUN ltac:(clear - KDJ; lia) ltac:(unfold AMEMCPY_STACK; clear - KDJS; lia) ltac:(clear - KDJD; lia)
                   APPS APPD UNPS UNPD ltac:(clear - KN; lia)).
  specialize (RUN ltac:(unfold KEND in *; clear - HS1 HS2 HS3 HS4 HS5 HS6; lia) ltac:(unfold KEND in *; clear - HD1 HD2 HD3 HD4 HD5 HD6; lia)
                   WRSS WRSD RIMG RSTK RSRC RDST RSHS RSHD).
  destruct RUN as (ms' & Hrun & Hpost).
  pose proof (PIosRegs.msteps_wrel bsegs _ _ (ExecF.mstepsF_msteps bsegs _ _ _ Hrun)) as HW.
  destruct Hpost as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Hms' & MU & WM & MI' & STK' & DST' & SRC').
  rewrite Hms' in HW. cbn [ms_mem MS] in HW.
  exists ms'. split; [exact Hrun|].
  set (E' := SLB.env_ext E 39 [t0; t1; t2; a1'; a2'; a3; a4; a5; a6; a7; t3; t4; t5; t6]).
  assert (EQ : forall v, (v < 39)%nat -> ev E' v = ev E v) by (intros v Hv; apply SLB.env_ext_lt; exact Hv).
  exists (AMHB.MCG_post rpc), E', m',
    (mkR (ev E 0) (ev E 1) (ev E 2) (ev E 3) t0 t1 t2 (ev E 4) (ev E 5) (ev E 16) a1' a2' a3 a4 a5 a6 a7 (ev E 6) (ev E 7) (ev E 8)
         (ev E 9) (ev E 10) (ev E 11) (ev E 12) (ev E 13) (ev E 14) (ev E 15) t3 t4 t5 t6), F, fc.
  split; [left; reflexivity|].
  split.
  { rewrite Hms'. cbn [AMHB.MCG_post TM t_pc]. f_equal. rewrite (ra_lit (ev E 0) rpc Hr0 KRA). apply ret_pc_even; assumption. }
  split; [exact HZ|]. split; [apply rfull_mkR|].
  split; [apply regs_ok_mkR; reflexivity|].
  split.
  { constructor; [|constructor].
    assert (E16 : ev E' 16 = ev E 16) by (apply EQ; lia). assert (E18 : ev E' 18 = ev E 18) by (apply EQ; lia).
    cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off AMHB.V edenot]. rewrite ?E16, ?E18. fold D N.
    split; [unfold flat, estart, elenZ; cbn [a_base a_off AMHB.V edenot]; rewrite ?E16, ?E18; fold D N; lia|].
    intros i Hi. rewrite Z.add_0_r.
    pose proof (SLB.kn_defined bsegs E M (AMHB.V 16) 0 (AMHB.V 18) KDU i) as D0. cbn [AMHB.V edenot] in D0. fold D N in D0.
    rewrite Z.add_0_r in D0. exact (SC.wrel_grows bsegs _ _ HW _ (D0 Hi)). }
  split; [constructor|].
  split; [apply SLB.gagree_ext; cbn [AMHB.MCAG SP.SUMR SP.sm_G]; lia|].
  split; [reflexivity|].
  assert (EQW : map (SP.win_den E) AMHB.MCG_W = [(sp - 2224, sp); (D, D + N)]).
  { cbn [map AMHB.MCG_W SP.win_den edenot AMHB.vSP AMHB.V]. fold sp D N. rewrite !SLB.u64 by lia.
    replace (sp + -2224) with (sp - 2224) by lia. replace (sp - 2224 + 2224) with sp by lia. rewrite Z.add_0_r. reflexivity. }
  split.
  { split; [|exact MI'].
    apply (AI_frame AI L RNGh st LB M m' [(sp - 2224, sp); (D, D + N)] HH MU WM).
    rewrite <- EQW. unfold SP.wins_client in HWC. apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (w & <- & Hw).
    exact (proj1 (Forall_forall _ _) HWC w Hw). }
  cbn [SP.frame_ok AMHB.MCAG SP.SUMR SP.sm_PS SP.sm_W]. apply SLB.frame_of_munch. rewrite EQW. exact MU.
Qed.

Theorem mcag_ok : forall rpc, 0 <= rpc < 2^64 -> rpc mod 2 = 0 -> SP.summ_okH bsegs GP hmH hmA hmC hmR (AMHB.MCAG rpc).
Proof. intros rpc H1 H2. apply SLib.summ_of_libH. exact (mcag_lib rpc H1 H2). Qed.

(* [comment removed for export] *)
Lemma msah_lib : forall c rpc, 0 <= c < 256 -> 0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  SLib.summ_libH bsegs GP hmH hmA hmC hmR (AMHB.MSAH c rpc).
Proof.
  intros c rpc Hc Hr0 Hr2 E M rom R F fc HRom HAG HWC HHM HRF HR HK _ HZ.
  unfold AHMB.hmR in HRom. subst rom. destruct HHM as [HH MI].
  cbn [AMHB.MSAH SP.SUMR SP.sm_pre SP.sm_post SP.sm_A SP.sm_W SP.sm_G SP.sm_PS t_pc t_regs t_know AMHB.MS_pre AMHB.MS_post TM] in *.
  rewrite (regs_ok_canon E (AMHB.MS_pre_regs c) R HRF HR).
  unfold AMHB.MS_pre_kn in HK.
  pose proof HK as HK0. apply Forall_app in HK0 as [_ HKO].
  kget HK (KRange (AMHB.V 0) rpc rpc). kget HK (KRange (AMHB.sub (AMHB.V 16) (AMHB.mul 8 (AMHB.V 18))) 0 0).
  kget HK (KRange (AMHB.sub (AMHB.V 17) (AMHB.mul 8 (AMHB.V 19))) 0 0). kget HK (KRange (AMHB.V 19) 0 62).
  kget HK (KRange (AMHB.V 1) (0x7ffe00000000 + 2208) 0x800000000000).
  kget HK (KWr (SA AMHB.vSP (-2208)) (ELit 2208)). kget HK (KUnk (SA AMHB.vSP (-2208)) (ELit 2208)).
  kget HK (KWr (SA (AMHB.V 16) 0) (AMHB.V 17)). kget HK (KUnk (SA (AMHB.V 16) 0) (AMHB.V 17)).
  kget HK (KDisj (SA AMHB.vSP (- 2208)) (ELit 2208) (SA (AMHB.mul 8 (AMHB.V 18)) 0) (AMHB.mul 8 (AMHB.V 19))).
  match goal with
  | K0 : kentry_ok _ _ _ (KRange (AMHB.V 0) _ _), K1 : kentry_ok _ _ _ (KRange (AMHB.sub (AMHB.V 16) _) _ _),
    K2 : kentry_ok _ _ _ (KRange (AMHB.sub (AMHB.V 17) _) _ _), K3 : kentry_ok _ _ _ (KRange (AMHB.V 19) _ _),
    K4 : kentry_ok _ _ _ (KRange (AMHB.V 1) _ _),
    K5 : kentry_ok _ _ _ (KWr (SA AMHB.vSP _) _), K6 : kentry_ok _ _ _ (KUnk (SA AMHB.vSP _) _),
    K7 : kentry_ok _ _ _ (KWr (SA (AMHB.V 16) 0) _), K8 : kentry_ok _ _ _ (KUnk (SA (AMHB.V 16) 0) _),
    K9 : kentry_ok _ _ _ (KDisj (SA AMHB.vSP _) _ _ _) |- _ =>
    rename K0 into KRA; rename K1 into KD8; rename K2 into KN8; rename K3 into KN; rename K4 into KSP; rename K5 into KSW;
    rename K6 into KSU; rename K7 into KDW; rename K8 into KDU; rename K9 into KDJ
  end.
  cbn [kentry_ok AMHB.V edenot] in KRA, KSP, KN.
  destruct (opnd_ok E M _ _ _ _ HKO ltac:(cbn [AMHB.V edenot]; lia))
    as (E8P & E8N & APP & UNP & HL1 & HL2 & HL3 & HL5 & HL6 & WRS & EH1 & EH2 & PB).
  cbn [AMHB.V edenot] in E8P, E8N, APP, UNP, HL1, HL2, HL3, HL5, HL6, WRS, EH1, EH2, PB.
  set (sp := u (ev E 1)) in *. set (D := u (ev E 16)) in *. set (N := u (ev E 17)) in *.
  set (D8 := u (ev E 18)) in *. set (N8 := u (ev E 19)) in *. set (r := u (edenot E (AMHB.mul 8 (AMHB.V 20)))) in *.
  pose proof (ur (ev E 1)) as Rsp. pose proof (ur (ev E 16)) as RD. pose proof (ur (ev E 17)) as RN. fold sp D N in Rsp, RD, RN.
  cbn [kentry_ok AMHB.sub AMHB.mul AMHB.V edenot] in KD8, KN8. zden KD8. zden KN8. fold D N D8 N8 in KD8, KN8.
  change (8 mod 2^64) with 8 in KD8, KN8. rewrite (Z.mod_small (8 * D8)) in KD8 by lia. rewrite (Z.mod_small (8 * N8)) in KN8 by lia.
  assert (HD : D = 8 * D8) by (pose proof (modr (D - 8 * D8) 0 0 ltac:(lia) ltac:(lia) KD8); lia).
  assert (HN : N = 8 * N8) by (pose proof (modr (N - 8 * N8) 0 0 ltac:(lia) ltac:(lia) KN8); lia).
  rewrite <- HD in APP, UNP, HL1, HL2. rewrite <- HN in APP, UNP, HL2.
  (* [comment removed for export] *)
  pose proof (SLB.kn_stk bsegs E M _ _ _ KSW KSU) as STK. cbn [AMHB.vSP AMHB.V edenot] in STK. fold sp in STK.
  rewrite SLB.u64 in STK by lia. replace (sp + -2208 + 2208) with sp in STK by lia. replace (sp + -2208) with (sp - 2208) in STK by lia.
  (* [comment removed for export] *)
  destruct (SLB.kn_rw_CB bsegs E M _ _ _ KDW KDU) as (junk & DST). cbn [AMHB.V edenot] in DST. fold D N in DST. rewrite Z.add_0_r in DST.
  cbn [kentry_ok] in KDJ. unfold estart, elenZ in KDJ. cbn [a_base a_off AMHB.vSP AMHB.V] in KDJ. rewrite E8P, E8N in KDJ.
  unfold AMHB.vSP, AMHB.V in KDJ. cbn [edenot] in KDJ. fold sp D8 N8 in KDJ. rewrite ?SLB.u64 in KDJ by lia.
  (* [comment removed for export] *)
  destruct (AI_rtcells AI L RNGh st LB M HH) as (_ & GOT & RIC & REAL & SHB & _ & INI & LAY & _).
  (* [comment removed for export] *)
  assert (RW : forall w lo len, In w AMHB.MS_A -> fst (SX.awin_den E w) <= lo -> lo + len <= snd (SX.awin_den E w) -> 0 <= len ->
                 ExecF.rng (SX.fp_of (Some AMHB.MS_A) E) lo len).
  { intros w lo len Hw H1 H2 H3. pose proof (SLib.rng_fp_of AMHB.MS_A E w HAG Hw) as R0. eapply ExecF.rng_sub; [exact R0 | lia | lia]. }
  assert (RIMG : ExecF.rng (SX.fp_of (Some AMHB.MS_A) E) 0x10000 0x661000).
  { apply (RW AMHB.IMGW); [cbn; tauto | cbn [SX.awin_den AMHB.IMGW edenot fst snd]; rewrite !SLB.u64 by lia; lia .. | lia]. }
  assert (RSTK : ExecF.rng (SX.fp_of (Some AMHB.MS_A) E) (sp - 2208) (sp - (sp - 2208))).
  { apply (RW (AMHB.vSP, -2208, ELit 2208)); [cbn; tauto | cbn [SX.awin_den edenot AMHB.vSP AMHB.V fst snd]; fold sp; rewrite ?SLB.u64 by lia; lia .. | lia]. }
  assert (RDST : ExecF.rng (SX.fp_of (Some AMHB.MS_A) E) D N).
  { apply (RW (AMHB.V 16, 0, AMHB.V 17)); [cbn; tauto | cbn [SX.awin_den edenot AMHB.V fst snd]; fold D N; lia .. | lia]. }
  assert (RSH : ExecF.rng (SX.fp_of (Some AMHB.MS_A) E) (shad (8 * r)) (shad (8 * r + 576) - shad (8 * r))).
  { apply (RW (AMHB.mul 8 (AMHB.V 20), AMHB.SH, ELit 72)); [cbn; tauto | cbn [SX.awin_den fst snd]; fold r; rewrite ?EH2, ?EH1;
      cbn [edenot]; rewrite ?SLB.u64 by lia; unfold AMHB.SH in *; lia .. | lia]. }
  (* [comment removed for export] *)
  pose proof (asan_memset_spec (SX.fp_of (Some AMHB.MS_A) E) (ev E 0) (ev E 1) (ev E 2) (ev E 3) (ev E 21) (ev E 22) (ev E 23) (ev E 4) (ev E 5)
                (ev E 16) (Z_to_bv 64 c) (ev E 17) (ev E 24) (ev E 25) (ev E 26) (ev E 27) (ev E 28)
                (ev E 6) (ev E 7) (ev E 8) (ev E 9) (ev E 10) (ev E 11) (ev E 12) (ev E 13) (ev E 14) (ev E 15)
                (ev E 29) (ev E 30) (ev E 31) (ev E 32) F fc M (sp - 2208) junk (8 * r) (8 * r + 576)) as RUN.
  fold sp D N in RUN.
  specialize (RUN MI STK ltac:(lia) ltac:(unfold KHIGH; lia) GOT RIC SHB INI LAY REAL DST ltac:(lia) APP UNP ltac:(lia)).
  specialize (RUN ltac:(unfold KEND in *; lia) WRS RIMG RSTK RDST RSH).
  destruct RUN as (ms' & Hrun & Hpost).
  pose proof (PIosRegs.msteps_wrel bsegs _ _ (ExecF.mstepsF_msteps bsegs _ _ _ Hrun)) as HW.
  destruct Hpost as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Hms' & MU & WM & MI' & STK' & DST').
  rewrite Hms' in HW. cbn [ms_mem MS] in HW.
  exists ms'. split; [exact Hrun|].
  set (E' := SLB.env_ext E 33 [t0; t1; t2; a1'; a2'; a3; a4; a5; a6; a7; t3; t4; t5; t6]).
  assert (EQ : forall v, (v < 33)%nat -> ev E' v = ev E v) by (intros v Hv; apply SLB.env_ext_lt; exact Hv).
  exists (AMHB.MS_post c rpc), E', m',
    (mkR (ev E 0) (ev E 1) (ev E 2) (ev E 3) t0 t1 t2 (ev E 4) (ev E 5) (ev E 16) a1' a2' a3 a4 a5 a6 a7 (ev E 6) (ev E 7) (ev E 8)
         (ev E 9) (ev E 10) (ev E 11) (ev E 12) (ev E 13) (ev E 14) (ev E 15) t3 t4 t5 t6), F, fc.
  split; [left; reflexivity|].
  split.
  { rewrite Hms'. cbn [AMHB.MS_post TM t_pc]. f_equal. rewrite (ra_lit (ev E 0) rpc Hr0 KRA). apply ret_pc_even; assumption. }
  split; [exact HZ|]. split; [apply rfull_mkR|].
  split; [apply regs_ok_mkR; reflexivity|].
  split.
  { constructor; [|constructor].
    assert (E16 : ev E' 16 = ev E 16) by (apply EQ; lia). assert (E17 : ev E' 17 = ev E 17) by (apply EQ; lia).
    destruct DST' as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
    rewrite SLB.u64 in B by lia. rewrite (Z.mod_small c 256) in B by lia.
    assert (DEF : forall i, 0 <= i < N -> m' (Z_to_bv 64 (D + i)) = Some (Z_to_bv 8 c)).
    { intros i Hi. destruct B as (B1 & B2 & HB). specialize (HB (Z.to_nat i)). rewrite repeat_length in HB.
      specialize (HB ltac:(fold N; lia)). rewrite Z2Nat.id in HB by lia. unfold mrd, wa in HB. fold D in HB.
      pose proof (SLB.kn_defined bsegs E M (AMHB.V 16) 0 (AMHB.V 17) KDU i) as D0. cbn [AMHB.V edenot] in D0. fold D N in D0.
      rewrite Z.add_0_r in D0.
      pose proof (SC.wrel_grows bsegs _ _ HW _ (D0 Hi)) as D1. unfold wa in D1.
      destruct (m' (Z_to_bv 64 (D + i))) as [x|]; [|contradiction].
      rewrite HB. rewrite nth_error_repeat by lia. reflexivity. }
    destruct (Z.eqb c 0) eqn:Hc0.
    - apply Z.eqb_eq in Hc0. subst c. cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off AMHB.V edenot]. rewrite ?E16, ?E17.
      fold D N. split; [unfold flat, estart, elenZ; cbn [a_base a_off AMHB.V edenot]; rewrite ?E16, ?E17; fold D N; lia|].
      intros i Hi. rewrite Z.add_0_r. exact (DEF i Hi).
    - cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off AMHB.V edenot]. rewrite ?E16, ?E17.
      fold D N. split; [unfold flat, estart, elenZ; cbn [a_base a_off AMHB.V edenot]; rewrite ?E16, ?E17; fold D N; lia|].
      intros i Hi. rewrite Z.add_0_r. exact (DEF i Hi). }
  split; [constructor|].
  split; [apply SLB.gagree_ext; cbn [AMHB.MSAH SP.SUMR SP.sm_G]; lia|].
  split; [reflexivity|].
  assert (EQW : map (SP.win_den E) AMHB.MS_W = [(sp - 2208, sp); (D, D + N)]).
  { cbn [map AMHB.MS_W SP.win_den edenot AMHB.vSP AMHB.V]. fold sp D N. rewrite !SLB.u64 by lia.
    replace (sp + -2208) with (sp - 2208) by lia. replace (sp - 2208 + 2208) with sp by lia. rewrite Z.add_0_r. reflexivity. }
  split.
  { split; [|exact MI'].
    apply (AI_frame AI L RNGh st LB M m' [(sp - 2208, sp); (D, D + N)] HH MU WM).
    rewrite <- EQW. unfold SP.wins_client in HWC. apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (w & <- & Hw).
    exact (proj1 (Forall_forall _ _) HWC w Hw). }
  cbn [SP.frame_ok AMHB.MSAH SP.SUMR SP.sm_PS SP.sm_W]. apply SLB.frame_of_munch. rewrite EQW. exact MU.
Qed.

Theorem msah_ok : forall c rpc, 0 <= c < 256 -> 0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  SP.summ_okH bsegs GP hmH hmA hmC hmR (AMHB.MSAH c rpc).
Proof. intros c rpc H0 H1 H2. apply SLib.summ_of_libH. exact (msah_lib c rpc H0 H1 H2). Qed.

(* [comment removed for export] *)
Lemma mcah_lib : forall rpc, 0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  SLib.summ_libH bsegs GP hmH hmA hmC hmR (AMHB.MCAH rpc).
Proof.
  intros rpc Hr0 Hr2 E M rom R F fc HRom HAG HWC HHM HRF HR HK _ HZ.
  unfold AHMB.hmR in HRom. subst rom. destruct HHM as [HH MI].
  cbn [AMHB.MCAH SP.SUMR SP.sm_pre SP.sm_post SP.sm_A SP.sm_W SP.sm_G SP.sm_PS t_pc t_regs t_know AMHB.MC_pre AMHB.MC_post TM] in *.
  rewrite (regs_ok_canon E AMHB.MC_pre_regs R HRF HR).
  unfold AMHB.MC_pre_kn in HK.
  pose proof HK as HK0. apply Forall_app in HK0 as [_ HKa]. apply Forall_app in HKa as [HKOS HKOD].
  kget HK (KRange (AMHB.V 0) rpc rpc). kget HK (KRange (AMHB.sub (AMHB.V 16) (AMHB.mul 8 (AMHB.V 19))) 0 0).
  kget HK (KRange (AMHB.sub (AMHB.V 17) (AMHB.mul 8 (AMHB.V 20))) 0 0). kget HK (KRange (AMHB.sub (AMHB.V 18) (AMHB.mul 8 (AMHB.V 21))) 0 0).
  kget HK (KRange (AMHB.V 21) 0 62). kget HK (KRange (AMHB.V 1) (0x7ffe00000000 + 2224) 0x800000000000).
  kget HK (KWr (SA AMHB.vSP (-2224)) (ELit 2224)). kget HK (KUnk (SA AMHB.vSP (-2224)) (ELit 2224)).
  kget HK (KUnk (SA (AMHB.V 17) 0) (AMHB.V 18)). kget HK (KWr (SA (AMHB.V 16) 0) (AMHB.V 18)).
  kget HK (KDisj (SA (AMHB.V 17) 0) (AMHB.V 18) (SA (AMHB.V 16) 0) (AMHB.V 18)). kget HK (KUnk (SA (AMHB.V 16) 0) (AMHB.V 18)).
  kget HK (KDisj (SA AMHB.vSP (- 2224)) (ELit 2224) (SA (AMHB.mul 8 (AMHB.V 19)) 0) (AMHB.mul 8 (AMHB.V 21))).
  kget HK (KDisj (SA AMHB.vSP (- 2224)) (ELit 2224) (SA (AMHB.mul 8 (AMHB.V 20)) 0) (AMHB.mul 8 (AMHB.V 21))).
  match goal with
  | K0 : kentry_ok _ _ _ (KRange (AMHB.V 0) _ _), K1 : kentry_ok _ _ _ (KRange (AMHB.sub (AMHB.V 16) _) _ _),
    K2 : kentry_ok _ _ _ (KRange (AMHB.sub (AMHB.V 17) _) _ _), K2' : kentry_ok _ _ _ (KRange (AMHB.sub (AMHB.V 18) _) _ _),
    K3 : kentry_ok _ _ _ (KRange (AMHB.V 21) _ _), K4 : kentry_ok _ _ _ (KRange (AMHB.V 1) _ _),
    K5 : kentry_ok _ _ _ (KWr (SA AMHB.vSP _) _), K6 : kentry_ok _ _ _ (KUnk (SA AMHB.vSP _) _),
    K7 : kentry_ok _ _ _ (KUnk (SA (AMHB.V 17) 0) _), K8 : kentry_ok _ _ _ (KWr (SA (AMHB.V 16) 0) _),
    K9 : kentry_ok _ _ _ (KDisj (SA (AMHB.V 17) 0) _ _ _), K10 : kentry_ok _ _ _ (KUnk (SA (AMHB.V 16) 0) _),
    K11 : kentry_ok _ _ _ (KDisj (SA AMHB.vSP _) _ (SA (AMHB.mul 8 (AMHB.V 19)) 0) _),
    K12 : kentry_ok _ _ _ (KDisj (SA AMHB.vSP _) _ (SA (AMHB.mul 8 (AMHB.V 20)) 0) _) |- _ =>
    rename K0 into KRA; rename K1 into KD8; rename K2 into KS8; rename K2' into KN8; rename K3 into KN; rename K4 into KSP;
    rename K5 into KSW; rename K6 into KSU; rename K7 into KSRC; rename K8 into KDW; rename K9 into KDJ; rename K10 into KDU;
    rename K11 into KDJD; rename K12 into KDJS
  end.
  cbn [kentry_ok AMHB.V edenot] in KRA, KSP, KN.
  destruct (opnd_ok E M _ _ _ _ HKOD ltac:(cbn [AMHB.V edenot]; lia))
    as (E8D & E8N & APPD & UNPD & HD1 & HD2 & HD3 & HD5 & HD6 & WRSD & EHD1 & EHD2 & PBD).
  destruct (opnd_ok E M _ _ _ _ HKOS ltac:(cbn [AMHB.V edenot]; lia))
    as (E8S & _ & APPS & UNPS & HS1 & HS2 & HS3 & HS5 & HS6 & WRSS & EHS1 & EHS2 & PBS).
  cbn [AMHB.V edenot] in E8D, E8N, APPD, UNPD, HD1, HD2, HD3, HD5, HD6, WRSD, EHD1, EHD2, PBD.
  cbn [AMHB.V edenot] in E8S, APPS, UNPS, HS1, HS2, HS3, HS5, HS6, WRSS, EHS1, EHS2, PBS.
  set (sp := u (ev E 1)) in *. set (D := u (ev E 16)) in *. set (S := u (ev E 17)) in *. set (N := u (ev E 18)) in *.
  set (D8 := u (ev E 19)) in *. set (S8 := u (ev E 20)) in *. set (N8 := u (ev E 21)) in *.
  set (rd := u (edenot E (AMHB.mul 8 (AMHB.V 23)))) in *. set (rs := u (edenot E (AMHB.mul 8 (AMHB.V 22)))) in *.
  pose proof (ur (ev E 1)) as Rsp. pose proof (ur (ev E 16)) as RD. pose proof (ur (ev E 17)) as RS. pose proof (ur (ev E 18)) as RN.
  fold sp D S N in Rsp, RD, RS, RN.
  cbn [kentry_ok AMHB.sub AMHB.mul AMHB.V edenot] in KD8, KS8, KN8. zden KD8. zden KS8. zden KN8. fold D S N D8 S8 N8 in KD8, KS8, KN8.
  change (8 mod 2^64) with 8 in KD8, KS8, KN8.
  rewrite (Z.mod_small (8 * D8)) in KD8 by lia. rewrite (Z.mod_small (8 * S8)) in KS8 by lia. rewrite (Z.mod_small (8 * N8)) in KN8 by lia.
  assert (HD : D = 8 * D8) by (pose proof (modr (D - 8 * D8) 0 0 ltac:(lia) ltac:(lia) KD8); lia).
  assert (HS : S = 8 * S8) by (pose proof (modr (S - 8 * S8) 0 0 ltac:(lia) ltac:(lia) KS8); lia).
  assert (HN : N = 8 * N8) by (pose proof (modr (N - 8 * N8) 0 0 ltac:(lia) ltac:(lia) KN8); lia).
  rewrite <- HD in APPD, UNPD, HD1, HD2. rewrite <- HN in APPD, UNPD, HD2.
  rewrite <- HS in APPS, UNPS, HS1, HS2. rewrite <- HN in APPS, UNPS, HS2.
  (* [comment removed for export] *)
  pose proof (SLB.kn_stk bsegs E M _ _ _ KSW KSU) as STK. cbn [AMHB.vSP AMHB.V edenot] in STK. fold sp in STK.
  rewrite SLB.u64 in STK by lia. replace (sp + -2224 + 2224) with sp in STK by lia. replace (sp + -2224) with (sp - 2224) in STK by lia.
  (* [comment removed for export] *)
  destruct (SLB.kn_bytes_of_unk bsegs E M _ _ _ KSRC) as (src & SRCB & SRCL). cbn [AMHB.V edenot] in SRCB, SRCL. fold S N in SRCB, SRCL.
  rewrite Z.add_0_r in SRCB.
  destruct (SLB.kn_rw_CB bsegs E M _ _ _ KDW KDU) as (junk & DST). cbn [AMHB.V edenot] in DST. fold D N in DST. rewrite Z.add_0_r in DST.
  cbn [kentry_ok] in KDJ, KDJD, KDJS. unfold estart, elenZ in KDJ, KDJD, KDJS. cbn [a_base a_off] in KDJ, KDJD, KDJS.
  rewrite E8D, E8N in KDJD. rewrite E8S, E8N in KDJS.
  unfold AMHB.vSP, AMHB.V in KDJ, KDJD, KDJS. cbn [edenot] in KDJ, KDJD, KDJS. fold sp D S N D8 S8 N8 in KDJ, KDJD, KDJS.
  rewrite ?SLB.u64 in KDJD by lia. rewrite ?SLB.u64 in KDJS by lia.
  (* [comment removed for export] *)
  destruct (AI_rtcells AI L RNGh st LB M HH) as (_ & GOT & RIC & REAL & SHB & _ & INI & LAY & _).
  (* [comment removed for export] *)
  assert (RW : forall w lo len, In w AMHB.MC_A -> fst (SX.awin_den E w) <= lo -> lo + len <= snd (SX.awin_den E w) -> 0 <= len ->
                 ExecF.rng (SX.fp_of (Some AMHB.MC_A) E) lo len).
  { intros w lo len Hw H1 H2 H3. pose proof (SLib.rng_fp_of AMHB.MC_A E w HAG Hw) as R0. eapply ExecF.rng_sub; [exact R0 | lia | lia]. }
  assert (RIMG : ExecF.rng (SX.fp_of (Some AMHB.MC_A) E) 0x10000 0x661000).
  { apply (RW AMHB.IMGW); [cbn; tauto | cbn [SX.awin_den AMHB.IMGW edenot fst snd]; rewrite !SLB.u64 by lia; lia .. | lia]. }
  assert (RSTK : ExecF.rng (SX.fp_of (Some AMHB.MC_A) E) (sp - 2224) (sp - (sp - 2224))).
  { apply (RW (AMHB.vSP, -2224, ELit 2224)); [cbn; tauto | cbn [SX.awin_den edenot AMHB.vSP AMHB.V fst snd]; fold sp; rewrite ?SLB.u64 by lia; lia .. | lia]. }
  assert (RSRC : ExecF.rng (SX.fp_of (Some AMHB.MC_A) E) S N).
  { apply (RW (AMHB.V 17, 0, AMHB.V 18)); [cbn; tauto | cbn [SX.awin_den edenot AMHB.V fst snd]; fold S N; lia .. | lia]. }
  assert (RDST : ExecF.rng (SX.fp_of (Some AMHB.MC_A) E) D N).
  { apply (RW (AMHB.V 16, 0, AMHB.V 18)); [cbn; tauto | cbn [SX.awin_den edenot AMHB.V fst snd]; fold D N; lia .. | lia]. }
  assert (RSHD : ExecF.rng (SX.fp_of (Some AMHB.MC_A) E) (shad (8 * rd)) (shad (8 * rd + 576) - shad (8 * rd))).
  { apply (RW (AMHB.mul 8 (AMHB.V 23), AMHB.SH, ELit 72)); [cbn; tauto | cbn [SX.awin_den fst snd]; fold rd; rewrite ?EHD2, ?EHD1;
      cbn [edenot]; rewrite ?SLB.u64 by lia; unfold AMHB.SH in *; lia .. | lia]. }
  assert (RSHS : ExecF.rng (SX.fp_of (Some AMHB.MC_A) E) (shad (8 * rs)) (shad (8 * rs + 576) - shad (8 * rs))).
  { apply (RW (AMHB.mul 8 (AMHB.V 22), AMHB.SH, ELit 72)); [cbn; tauto | cbn [SX.awin_den fst snd]; fold rs; rewrite ?EHS2, ?EHS1;
      cbn [edenot]; rewrite ?SLB.u64 by lia; unfold AMHB.SH in *; lia .. | lia]. }
  (* [comment removed for export] *)
  pose proof (asan_memcpy_proof (SX.fp_of (Some AMHB.MC_A) E) (ev E 0) (ev E 1) (ev E 2) (ev E 3) (ev E 24) (ev E 25) (ev E 26) (ev E 4) (ev E 5)
                (ev E 16) (ev E 17) (ev E 18) (ev E 27) (ev E 28) (ev E 29) (ev E 30) (ev E 31)
                (ev E 6) (ev E 7) (ev E 8) (ev E 9) (ev E 10) (ev E 11) (ev E 12) (ev E 13) (ev E 14) (ev E 15)
                (ev E 32) (ev E 33) (ev E 34) (ev E 35) F fc M (sp - 2224) src junk (8 * rs) (8 * rs + 576) (8 * rd) (8 * rd + 576)) as RUN.
  cbv zeta in RUN. fold sp D S N in RUN.
  specialize (RUN MI STK ltac:(unfold AMEMCPY_STACK; lia) ltac:(unfold KHIGH; lia) GOT RIC SHB INI LAY REAL SRCB SRCL DST).
  specialize (RUN ltac:(clear - KDJ; lia) ltac:(unfold AMEMCPY_STACK; clear - KDJS HS HN; lia) ltac:(clear - KDJD HD HN; lia)
                   APPS APPD UNPS UNPD ltac:(clear - KN HN; lia)).
  pose proof (ur (edenot E (AMHB.mul 8 (AMHB.V 22)))) as Rrs. pose proof (ur (edenot E (AMHB.mul 8 (AMHB.V 23)))) as Rrd. fold rs rd in Rrs, Rrd.
  assert (Z0s : 0 <= 8 * rs) by (clear - Rrs; lia). assert (Z0d : 0 <= 8 * rd) by (clear - Rrd; lia).
  specialize (RUN (conj HS1 (conj HS2 (conj HS5 (conj HS6 (conj Z0s HS3))))) (conj HD1 (conj HD2 (conj HD5 (conj HD6 (conj Z0d HD3)))))
                   WRSS WRSD RIMG RSTK RSRC RDST RSHS RSHD).
  destruct RUN as (ms' & Hrun & Hpost).
  pose proof (PIosRegs.msteps_wrel bsegs _ _ (ExecF.mstepsF_msteps bsegs _ _ _ Hrun)) as HW.
  destruct Hpost as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Hms' & MU & WM & MI' & STK' & DST' & SRC').
  rewrite Hms' in HW. cbn [ms_mem MS] in HW.
  exists ms'. split; [exact Hrun|].
  set (E' := SLB.env_ext E 36 [t0; t1; t2; a1'; a2'; a3; a4; a5; a6; a7; t3; t4; t5; t6]).
  assert (EQ : forall v, (v < 36)%nat -> ev E' v = ev E v) by (intros v Hv; apply SLB.env_ext_lt; exact Hv).
  exists (AMHB.MC_post rpc), E', m',
    (mkR (ev E 0) (ev E 1) (ev E 2) (ev E 3) t0 t1 t2 (ev E 4) (ev E 5) (ev E 16) a1' a2' a3 a4 a5 a6 a7 (ev E 6) (ev E 7) (ev E 8)
         (ev E 9) (ev E 10) (ev E 11) (ev E 12) (ev E 13) (ev E 14) (ev E 15) t3 t4 t5 t6), F, fc.
  split; [left; reflexivity|].
  split.
  { rewrite Hms'. cbn [AMHB.MC_post TM t_pc]. f_equal. rewrite (ra_lit (ev E 0) rpc Hr0 KRA). apply ret_pc_even; assumption. }
  split; [exact HZ|]. split; [apply rfull_mkR|].
  split; [apply regs_ok_mkR; reflexivity|].
  split.
  { constructor; [|constructor].
    assert (E16 : ev E' 16 = ev E 16) by (apply EQ; lia). assert (E18 : ev E' 18 = ev E 18) by (apply EQ; lia).
    cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off AMHB.V edenot]. rewrite ?E16, ?E18. fold D N.
    split; [unfold flat, estart, elenZ; cbn [a_base a_off AMHB.V edenot]; rewrite ?E16, ?E18; fold D N; lia|].
    intros i Hi. rewrite Z.add_0_r.
    pose proof (SLB.kn_defined bsegs E M (AMHB.V 16) 0 (AMHB.V 18) KDU i) as D0. cbn [AMHB.V edenot] in D0. fold D N in D0.
    rewrite Z.add_0_r in D0. exact (SC.wrel_grows bsegs _ _ HW _ (D0 Hi)). }
  split; [constructor|].
  split; [apply SLB.gagree_ext; cbn [AMHB.MCAH SP.SUMR SP.sm_G]; lia|].
  split; [reflexivity|].
  assert (EQW : map (SP.win_den E) AMHB.MC_W = [(sp - 2224, sp); (D, D + N)]).
  { cbn [map AMHB.MC_W SP.win_den edenot AMHB.vSP AMHB.V]. fold sp D N. rewrite !SLB.u64 by lia.
    replace (sp + -2224) with (sp - 2224) by lia. replace (sp - 2224 + 2224) with sp by lia. rewrite Z.add_0_r. reflexivity. }
  split.
  { split; [|exact MI'].
    apply (AI_frame AI L RNGh st LB M m' [(sp - 2224, sp); (D, D + N)] HH MU WM).
    rewrite <- EQW. unfold SP.wins_client in HWC. apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (w & <- & Hw).
    exact (proj1 (Forall_forall _ _) HWC w Hw). }
  cbn [SP.frame_ok AMHB.MCAH SP.SUMR SP.sm_PS SP.sm_W]. apply SLB.frame_of_munch. rewrite EQW. exact MU.
Qed.

Theorem mcah_ok : forall rpc, 0 <= rpc < 2^64 -> rpc mod 2 = 0 -> SP.summ_okH bsegs GP hmH hmA hmC hmR (AMHB.MCAH rpc).
Proof. intros rpc H1 H2. apply SLib.summ_of_libH. exact (mcah_lib rpc H1 H2). Qed.
End Bridge.
End ABRB.
Print Assumptions ABRB.msag_ok.
Print Assumptions ABRB.msagp_ok.
Print Assumptions ABRB.mcag_ok.
Print Assumptions ABRB.msah_ok.
Print Assumptions ABRB.mcah_ok.
